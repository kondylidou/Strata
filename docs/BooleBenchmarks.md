# Boole Benchmark Targets

This document defines five target benchmarks drawn from
[dalek-lite](https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/main/curve25519-dalek)
— a Verus-verified Rust implementation of Curve25519/Ed25519 cryptography.
Each benchmark is a real exec function with `requires`/`ensures` annotations.
The goal is to run these through the Verus → Boole pipeline and verify the
postconditions with cvc5.

The five benchmarks give full coverage of the repo's major subsystems:

| # | Benchmark | Subsystem | Source file |
|---|-----------|-----------|-------------|
| 1 | `FieldElement51::mul` | Field arithmetic (GF(2²⁵⁵ − 19)) | `backend/serial/u64/field.rs` |
| 2 | `EdwardsPoint::add` | Edwards group law | `edwards.rs` |
| 3 | `MontgomeryPoint::differential_add_and_double` | Montgomery ladder (X25519 core) | `montgomery.rs` |
| 4 | `Scalar::invert` | Scalar arithmetic (group order) | `scalar.rs` |
| 5 | `RistrettoPoint::compress` | Protocol encoding (Ristretto) | `ristretto.rs` |

Benchmark 1 verifies the arithmetic primitive shared by all higher layers.
Benchmarks 2 and 3 verify the group law on the two distinct curve models in
the codebase (extended Edwards and Montgomery/projective). Benchmark 4 covers
scalar arithmetic over the group order — a structurally independent subsystem
needed for signatures and key generation. Benchmark 5 verifies a full
protocol operation that composes the lower layers. Together they exercise every
major subsystem in the repo and demonstrate that Boole can reason across the
full stack.

---

## Benchmark 1 — `FieldElement51::mul`

**Source:** `curve25519-dalek/src/backend/serial/u64/field.rs`

### The function

```rust
fn mul(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)
    requires
        fe51_limbs_bounded(self, 54) && fe51_limbs_bounded(_rhs, 54),
    ensures
        fe51_as_canonical_nat(&output)
            == field_mul(fe51_as_canonical_nat(self),
                         fe51_as_canonical_nat(_rhs)),
        fe51_limbs_bounded(&output, 52),
```

`FieldElement51` is a 5-limb radix-2^51 representation of a field element:

```rust
pub struct FieldElement51 {
    pub(crate) limbs: [u64; 5],
}
// value = limbs[0] + 2^51·limbs[1] + 2^102·limbs[2] + 2^153·limbs[3] + 2^204·limbs[4]
```

Note: the single `limbs: [u64; 5]` field is a fixed-size array. The Boole seed
below flattens it into five named integer fields (`limb0`…`limb4`), sidestepping
the array-indexing gap at the cost of a manual modeling step.

The body performs 25 cross-limb multiplications using 128-bit intermediate
accumulators (`u128`), followed by carry reduction with `× 19` — exploiting
the identity 2^255 ≡ 19 (mod p) to fold the overflow back into the low limbs.

### Cryptographic importance

`FieldElement51::mul` is the arithmetic hot path underlying every Curve25519
operation. X25519 key exchange, Ed25519 signing, Ed25519 verification, and
Ristretto group operations all reduce to repeated calls to `mul`. Verifying
`mul` correct means verifying the arithmetic foundation that every higher-level
protocol proof depends on. The postcondition
`fe51_as_canonical_nat(&output) == field_mul(...)` states that the 25-multiply
carry-chain correctly computes multiplication modulo p = 2^255 − 19.

### Boole gaps required

| Gap | Description | Status |
|-----|-------------|--------|
| **Struct/record types** (Gap #13) | `FieldElement51` is a struct; field access (`fe.limb0`), struct literal construction, and quantification over limbs are all required. | Active — [`struct_field_access.lean`](../StrataTest/Languages/Boole/FeatureRequests/struct_field_access.lean) |
| **Native `nat`** (Gap #8) | `fe51_as_canonical_nat` maps a struct to a mathematical integer; the postcondition requires `nat`/`int` arithmetic. | Active — [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) |
| **`u128` as `int`** | The body uses 128-bit carry accumulators. Model each as `int` (bounded within [0, 2^128)); the postcondition is stated purely in `nat` so no new language feature is needed — this is a modeling choice only. | — |

No recursion, no loop invariants, no sequences. The postcondition is a
bounded-integer arithmetic claim that cvc5 can discharge directly.

### Boole seed sketch

```boole
type FieldElement51 := {
  limb0: int, limb1: int, limb2: int, limb3: int, limb4: int
};

function fe_bounded(fe: FieldElement51, b: int) : bool;
axiom (∀ fe: FieldElement51, b: int .
  fe_bounded(fe, b) <==>
    fe.limb0 < b && fe.limb1 < b && fe.limb2 < b &&
    fe.limb3 < b && fe.limb4 < b);

function fe_as_nat(fe: FieldElement51) : int;
axiom (∀ fe: FieldElement51 .
  fe_as_nat(fe) ==
    fe.limb0 + 2^51  * fe.limb1 + 2^102 * fe.limb2 +
    2^153 * fe.limb3 + 2^204 * fe.limb4);

function field_mul(a: int, b: int) : int;
axiom (∀ a: int, b: int . field_mul(a, b) == (a * b) mod (2^255 - 19));

procedure fe_mul(a: FieldElement51, b: FieldElement51)
    returns (r: FieldElement51)
spec {
  requires fe_bounded(a, 2^54) && fe_bounded(b, 2^54);
  ensures  fe_as_nat(r) mod (2^255 - 19)
        == field_mul(fe_as_nat(a) mod (2^255 - 19),
                     fe_as_nat(b) mod (2^255 - 19));
  ensures  fe_bounded(r, 2^52);
}
{ /* 25 cross-limb multiplications + carry reduction with ×19 */ };
```

---

## Benchmark 2 — `EdwardsPoint::add`

**Source:** `curve25519-dalek/src/edwards.rs`

### The function

```rust
fn add(self, other: &'b EdwardsPoint) -> (result: EdwardsPoint)
    requires
        is_well_formed_edwards_point(*self) && is_well_formed_edwards_point(*other),
    ensures
        is_well_formed_edwards_point(result),
        ({
            let (x1, y1) = edwards_point_as_affine(*self);
            let (x2, y2) = edwards_point_as_affine(*other);
            edwards_point_as_affine(result) == edwards_add(x1, y1, x2, y2)
        }),
```

`EdwardsPoint` is an extended homogeneous coordinate representation
(X, Y, Z, T) with T = XY/Z (the Segre relation):

```rust
pub struct EdwardsPoint {
    pub(crate) X: FieldElement,
    pub(crate) Y: FieldElement,
    pub(crate) Z: FieldElement,
    pub(crate) T: FieldElement,
}
// affine: (x, y) = (X/Z, Y/Z), with T = xy·Z
```

The body converts `other` to a `ProjectiveNielsPoint` (Niels coordinates
`(Y+X, Y-X, Z, 2dT)`) and delegates to the `CompletedPoint`-returning
addition in `backend/serial/curve_models`. The completed-point result is then
converted back to extended coordinates via `as_extended`.

The core computation is the unified twisted Edwards addition formula:

```
PP = (Y1+X1)·(Y2+X2),   MM = (Y1−X1)·(Y2−X2)
TT2d = T1·T2·2d,        ZZ2 = Z1·Z2·2
X3 = PP−MM,  Y3 = PP+MM,  Z3 = ZZ2+TT2d,  T3 = ZZ2−TT2d
```

### Cryptographic importance

Point addition is the fundamental group operation of elliptic curve
cryptography. Every scalar multiplication (X25519 key exchange, Ed25519
signing, Ed25519 verification) reduces to iterated point additions. The
postcondition `edwards_point_as_affine(result) == edwards_add(x1, y1, x2, y2)`
is an exact statement that the extended-coordinate formula — with its
intermediate Niels and completed-point representations — faithfully computes
the affine group law of the twisted Edwards curve. This is the missing middle
layer: without it, field correctness (Benchmark 1) and encoding correctness
(Benchmark 5) are disconnected.

### Boole gaps required

This benchmark requires exactly the same two gaps as Benchmark 1 and adds
none:

| Gap | Description | Status |
|-----|-------------|--------|
| **Struct/record types** (Gap #13) | `EdwardsPoint` has four `FieldElement51` fields; same fix as Benchmark 1. | Active — [`struct_field_access.lean`](../StrataTest/Languages/Boole/FeatureRequests/struct_field_access.lean) |
| **Native `nat`** (Gap #8) | `edwards_point_as_affine` lifts coordinates to `nat`; same fix as Benchmark 1. | Active — [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) |

The spec function `edwards_add` can be axiomatized with the affine twisted
Edwards formula. The body is a sequence of `FieldElement51` ops (add, sub,
mul) on four coordinates — no recursion, no loops, no ghost variables.

### Boole seed sketch

```boole
type EdwardsPoint := {
  X: FieldElement51, Y: FieldElement51,
  Z: FieldElement51, T: FieldElement51
};

// Affine point — struct to avoid needing pair/tuple types (covered by Gap #13)
type AffinePoint := { x: int, y: int };

// Affine projection: (X/Z, Y/Z)
function edwards_point_as_affine(p: EdwardsPoint) : AffinePoint;

// Uninterpreted field ops used in the group-law axiom
function field_add(a: int, b: int) : int;
function field_sub(a: int, b: int) : int;
function field_mul(a: int, b: int) : int;
function field_div(a: int, b: int) : int;
const D : int;  // twisted Edwards curve constant d = -121665/121666 mod p

// Twisted Edwards group law
function edwards_add(x1: int, y1: int, x2: int, y2: int) : AffinePoint;
axiom (∀ x1, y1, x2, y2 .
  edwards_add(x1, y1, x2, y2).x ==
    field_div(field_add(field_mul(x1, y2), field_mul(y1, x2)),
              field_add(1, field_mul(D, field_mul(field_mul(x1, x2),
                                                  field_mul(y1, y2))))) &&
  edwards_add(x1, y1, x2, y2).y ==
    field_div(field_sub(field_mul(y1, y2), field_mul(x1, x2)),
              field_sub(1, field_mul(D, field_mul(field_mul(x1, x2),
                                                  field_mul(y1, y2))))));

function is_well_formed_edwards_point(p: EdwardsPoint) : bool;

procedure edwards_add_exec(p: EdwardsPoint, q: EdwardsPoint)
    returns (r: EdwardsPoint)
spec {
  requires is_well_formed_edwards_point(p) && is_well_formed_edwards_point(q);
  ensures  is_well_formed_edwards_point(r);
  ensures  edwards_point_as_affine(r) ==
           edwards_add(edwards_point_as_affine(p).x,
                       edwards_point_as_affine(p).y,
                       edwards_point_as_affine(q).x,
                       edwards_point_as_affine(q).y);
}
{ /* Niels-coordinate extended addition: PP, MM, TT2d, ZZ2, completed → extended */ };
```

---

## Benchmark 3 — `MontgomeryPoint::differential_add_and_double`

**Source:** `curve25519-dalek/src/montgomery.rs`

### The function

```rust
fn differential_add_and_double(
    P: &mut ProjectivePoint,
    Q: &mut ProjectivePoint,
    affine_PmQ: &FieldElement,
)
    requires
        fe51_limbs_bounded(&old(P).U, 52),
        fe51_limbs_bounded(&old(P).W, 52),
        fe51_limbs_bounded(&old(Q).U, 52),
        fe51_limbs_bounded(&old(Q).W, 52),
        fe51_limbs_bounded(affine_PmQ, 51),
        is_valid_u_coordinate(fe51_as_canonical_nat(affine_PmQ)),
    ensures
        fe51_limbs_bounded(&P.U, 52) && fe51_limbs_bounded(&P.W, 52),
        fe51_limbs_bounded(&Q.U, 52) && fe51_limbs_bounded(&Q.W, 52),
        (fe51_as_canonical_nat(affine_PmQ) == 0
            && projective_u_coordinate(*old(P)) == 0
            && projective_u_coordinate(*old(Q)) == 0) ==>
            (projective_u_coordinate(*P) == 0
             && projective_u_coordinate(*Q) == 0),
        // Case 1: P=[k]B, Q=[k+1]B => P'=[2k]B, Q'=[2k+1]B
        // Case 2: P=[k+1]B, Q=[k]B => P'=[2k+2]B, Q'=[2k+1]B
```

`MontgomeryPoint` holds a u-coordinate as a `FieldElement51`. The ladder
operates on a pair of projective representatives:

```rust
pub struct ProjectivePoint {
    pub U: FieldElement,
    pub W: FieldElement,
}
// affine u-coordinate: U/W  (with W=0 representing the point at infinity)
```

The body computes one full Montgomery ladder step: it simultaneously doubles
P and performs a differential addition of P and Q using the known difference
`affine_PmQ = u(P−Q)`. The formulas require only 4 field multiplications and
4 squarings — the efficiency that makes X25519 fast in practice.

### Cryptographic importance

`differential_add_and_double` is the inner loop body of X25519 key exchange.
Every call to `MontgomeryPoint::mul_clamped` (the Diffie-Hellman function)
iterates this step 255 times over the bits of the scalar. The annotated
postcondition in dalek-lite currently states limb-bound preservation and the
degenerate-zero case; the full ladder correctness (Cases 1 and 2 — that P and Q
remain consecutive scalar multiples after the step) is cited in comments rather
than as machine-checked ensures clauses. Verifying the full invariant through
Boole would therefore also require extending the Verus spec with those ensures
clauses. Regardless, `differential_add_and_double` is the core of the
Montgomery curve subsystem and is distinct from the Edwards curve model of
Benchmark 2 in both coordinate representation and addition formulas.

### Boole gaps required

The gaps required are:

| Gap | Description | Status |
|-----|-------------|--------|
| **Struct/record types** (Gap #13) | `ProjectivePoint` has two `FieldElement51` fields (U, W). Same fix as Benchmark 1. | Active |
| **Native `nat`** (Gap #8) | `projective_u_coordinate` and `fe51_as_canonical_nat` lift fields to `nat`. Same fix as Benchmark 1. | Active |
| **Mutable reference parameters** | `P` and `Q` are `&mut ProjectivePoint` — the function modifies both in place. Boole must model in/out variables or explicit pre/post state for mutation. | Active — not yet tracked in `BooleFeatureRequests.md` |
| **`old()` in postconditions** | The ensures clauses reference `*old(P)` and `*old(Q)` to name the pre-call state. Boole needs syntax for pre-state values. | Active — not yet tracked in `BooleFeatureRequests.md`; related to mutable reference parameters above |

For the Boole seed, `&mut P` / `&mut Q` are modelled as explicit input/output
pairs: `P_in`, `Q_in` as inputs and `P_out`, `Q_out` as returned values,
eliminating the mutation model entirely.

### Boole seed sketch

```boole
type ProjectivePoint := { U: FieldElement51, W: FieldElement51 };

function projective_u_coordinate(p: ProjectivePoint) : int;

function is_valid_u_coordinate(u: int) : bool;

procedure montgomery_ladder_step(
    P: ProjectivePoint, Q: ProjectivePoint, u_diff: FieldElement51)
    returns (P_out: ProjectivePoint, Q_out: ProjectivePoint)
spec {
  requires fe_bounded(P.U, 2^52) && fe_bounded(P.W, 2^52) &&
           fe_bounded(Q.U, 2^52) && fe_bounded(Q.W, 2^52) &&
           fe_bounded(u_diff, 2^51) &&
           is_valid_u_coordinate(fe_as_nat(u_diff));
  ensures  fe_bounded(P_out.U, 2^52) && fe_bounded(P_out.W, 2^52) &&
           fe_bounded(Q_out.U, 2^52) && fe_bounded(Q_out.W, 2^52);
  ensures  (fe_as_nat(u_diff) == 0 &&
            projective_u_coordinate(P) == 0 &&
            projective_u_coordinate(Q) == 0) ==>
           (projective_u_coordinate(P_out) == 0 &&
            projective_u_coordinate(Q_out) == 0);
  // ladder step correctness: Cases 1 and 2 axiomatized
}
{ /* Montgomery differential add-and-double field arithmetic */ };
```

---

## Benchmark 4 — `Scalar::invert`

**Source:** `curve25519-dalek/src/scalar.rs`

### The function

```rust
pub fn invert(&self) -> (result: Scalar)
    requires
        is_canonical_scalar(self),
    ensures
        scalar_as_nat(self) > 0 ==>
            group_canonical(scalar_as_nat(&result) * scalar_as_nat(self)) == 1,
        is_canonical_scalar(&result),
```

`Scalar` stores a little-endian 256-bit integer in a byte array:

```rust
pub struct Scalar {
    pub bytes: [u8; 32],
}
// value = bytes[0] + 2^8·bytes[1] + ... + 2^248·bytes[31]
// invariant: value < ℓ = 2^252 + 27742317777372353535851937790883648493
```

The body unpacks `self` into an `UnpackedScalar` (a type alias for `Scalar52`,
five 52-bit limbs), calls `UnpackedScalar::invert()` — an addition-chain
implementation of Fermat's little theorem (s^(ℓ−2) mod ℓ) — then packs the
result back to bytes.

### Cryptographic importance

Scalar inversion is required for Ed25519 signature verification (computing
`s⁻¹ mod ℓ` to recover the challenge) and for certain zero-knowledge proof
protocols. The postcondition `group_canonical(result * self) == 1` is the
multiplicative inverse property modulo the group order ℓ — a different
modulus and a different algebraic structure from the field arithmetic in
Benchmark 1. This is the only benchmark that covers scalar arithmetic: the
`Scalar` subsystem operates entirely in ℤ/ℓℤ, independent of field or curve
operations.

### Boole gaps required

The Boole seed below models `Scalar` as an abstract integer `{ val: int }`,
sidestepping both Gap #13 and the array gap — the same modeling strategy as
B1's limb flattening. In a mechanical pipeline translation the Rust source
`Scalar { bytes: [u8; 32] }` would surface two new gaps:

| Gap | Description | Status |
|-----|-------------|--------|
| **Fixed-size array types** | `Scalar` holds `bytes: [u8; 32]` — a fixed-size byte array. A mechanical translation needs a model for `[T; N]` to express `scalar_as_nat`. The seed avoids this by treating `Scalar` as an opaque integer. | New gap for faithful pipeline translation |
| **`scalar_as_nat` / byte-array lifting** | Maps `[u8; 32]` to a `nat` via positional byte weights. The seed axiomatizes `scalar_as_nat(s) == s.val` directly, bypassing the byte decomposition. A full translation needs the byte-weight unfolding. | New gap for faithful pipeline translation |

No loops, no ghost variables. The postcondition is a single modular arithmetic
claim that cvc5 can discharge once `group_canonical` and `scalar_as_nat` are
axiomatized.

### Boole seed sketch

```boole
// Model Scalar as an integer in [0, L)
type Scalar := { val: int };

const L : int = 7237005577332262213973186563042994240857116359379907606001950938285454250989;

function scalar_as_nat(s: Scalar) : int;
axiom (∀ s: Scalar . scalar_as_nat(s) == s.val);

function group_canonical(n: int) : int;
axiom (∀ n: int . group_canonical(n) == n mod L);

function is_canonical_scalar(s: Scalar) : bool;
axiom (∀ s: Scalar . is_canonical_scalar(s) <==>
  scalar_as_nat(s) >= 0 && scalar_as_nat(s) < L);

procedure scalar_invert(s: Scalar) returns (r: Scalar)
spec {
  requires is_canonical_scalar(s);
  ensures  is_canonical_scalar(r);
  ensures  scalar_as_nat(s) > 0 ==>
           group_canonical(scalar_as_nat(r) * scalar_as_nat(s)) == 1;
}
{ /* Fermat: s^(L−2) mod L via Scalar52 addition chain */ };
```

---

## Benchmark 5 — `RistrettoPoint::compress`

**Source:** `curve25519-dalek/src/ristretto.rs`

### The function

```rust
pub fn compress(&self) -> (result: CompressedRistretto)
    requires
        is_well_formed_edwards_point(self.0),
    ensures
        result.0 == spec_ristretto_compress(*self),
```

`RistrettoPoint` wraps an `EdwardsPoint` in extended homogeneous coordinates
(X, Y, Z, T) where each coordinate is a `FieldElement51`:

```rust
pub struct RistrettoPoint(pub EdwardsPoint);
// EdwardsPoint has fields X, Y, Z, T : FieldElement51
// invariant: Z·T == X·Y  (Segre relation)
```

The pure spec that the postcondition refers to is:

```rust
pub open spec fn ristretto_compress_extended(x: nat, y: nat, z: nat, t: nat) -> [u8; 32] {
    let u1      = field_mul(field_add(z, y), field_sub(z, y));  // (Z+Y)(Z-Y)
    let u2      = field_mul(x, y);                               // X·Y
    let invsqrt = nat_invsqrt(field_mul(u1, field_square(u2)));  // 1/√(u1·u2²)
    let i1      = field_mul(invsqrt, u1);
    let i2      = field_mul(invsqrt, u2);
    let z_inv   = field_mul(i1, field_mul(i2, t));               // 1/Z (affine normalisation)
    let rotate  = is_negative(field_mul(t, z_inv));              // coset representative selection
    // ... conditional rotation, sign normalisation, final encoding as bytes
    u8_32_from_nat(s_final)
}

pub open spec fn spec_ristretto_compress(point: RistrettoPoint) -> [u8; 32] {
    let (x, y, z, t) = edwards_point_as_nat(point.0);
    ristretto_compress_extended(x, y, z, t)
}
```

The body (~300 lines with ghost proofs) calls field `add`, `sub`, `mul`,
`square`, `invsqrt`, `is_negative`, `conditional_assign`, `conditional_negate`,
and `as_bytes` — all ultimately composed of `FieldElement51` operations.

### Cryptographic importance

Ristretto is the prime-order group abstraction used in modern cryptographic
protocols including the Signal Protocol, Tor's onion-service handshake, and
many zero-knowledge proof systems. It eliminates the cofactor-8 problem of
Curve25519 by defining equivalence classes on the underlying Edwards curve and
selecting a canonical representative via the compression formula.

The postcondition `result.0 == spec_ristretto_compress(*self)` states that the
exec implementation faithfully computes the Ristretto encoding specified in the
[RISTRETTO draft RFC](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448).
This is a full functional-correctness theorem linking imperative Rust code to a
mathematical group-theoretic specification.

### Boole gaps required

This benchmark shares all gaps from Benchmarks 1–4 and adds the following:

| Gap | Description | Status |
|-----|-------------|--------|
| **Struct/record types** (Gap #13) | `EdwardsPoint` has four `FieldElement51` fields (X, Y, Z, T). Same fix as Benchmark 1. | Active |
| **Native `nat`** (Gap #8) | Field element values must be lifted to `nat` for the spec. Same fix as Benchmark 1. | Active |
| **Pair/tuple return types** | `invsqrt()` returns `(bool, FieldElement51)` — a two-element struct or tuple. The ignore-first pattern `let (_, invsqrt) = ...` requires destructuring. | Active — not yet tracked in `BooleFeatureRequests.md`; related to Gap #14 (`Option<T>` in spec functions) |
| **Ghost variables** | The body uses `let ghost x_nat = fe51_as_canonical_nat(&self.0.X)` throughout to name intermediate values in proof assertions. Boole needs a `ghost` variable annotation. | Active — not yet tracked in `BooleFeatureRequests.md` |
| **Field op axioms** | `add`, `sub`, `square`, `invsqrt`, `is_negative`, `conditional_assign`, `conditional_negate`, `as_bytes` must each be declared as Boole spec functions with mathematical postconditions. Once Benchmark 1 is complete, `mul` is already available; the remaining ops follow the same pattern. | — |

**Note on scope:** For the Boole seed, the ghost proof steps (`proof { ... }` blocks)
can be dropped — the postcondition only needs to hold, not be proved
step-by-step. The Boole seed reduces to the exec body with field ops treated as
axiomatized black boxes, and cvc5 verifies the final postcondition.

### Boole seed sketch

```boole
type FieldElement51 := {
  limb0: int, limb1: int, limb2: int, limb3: int, limb4: int
};

type EdwardsPoint := { X: FieldElement51, Y: FieldElement51,
                       Z: FieldElement51, T: FieldElement51 };

type RistrettoPoint := { inner: EdwardsPoint };

// Bytes32: abstract 32-byte type; faithful translation would need [u8; 32]
type Bytes32;
type CompressedRistretto := { bytes: Bytes32 };

// Field prime (used in connecting axioms)
const P : int = 57896044618658097711785492504343953926634992332820282019728792003956564819949;

// Field op axioms (mathematical postconditions; bodies are trusted stubs)
function fe_add(a: FieldElement51, b: FieldElement51) : FieldElement51;
function fe_sub(a: FieldElement51, b: FieldElement51) : FieldElement51;
function fe_mul(a: FieldElement51, b: FieldElement51) : FieldElement51;
function fe_square(a: FieldElement51) : FieldElement51;
// invsqrt returns (was_square: bool, result: FieldElement51)
type InvsqrtResult := { ok: bool, val: FieldElement51 };
function fe_invsqrt(a: FieldElement51) : InvsqrtResult;
function fe_is_negative(a: FieldElement51) : bool;
function fe_conditional_negate(a: FieldElement51, neg: bool) : FieldElement51;
function fe_as_bytes(a: FieldElement51) : Bytes32;

// Connecting axioms: field ops respect the canonical-nat spec
function fe_as_nat(fe: FieldElement51) : int;
function field_mul(a: int, b: int) : int;
axiom (∀ a, b . fe_as_nat(fe_mul(a, b)) mod P
             == field_mul(fe_as_nat(a) mod P, fe_as_nat(b) mod P));
// ... analogous axioms for add, sub, square, invsqrt

function spec_ristretto_compress(p: RistrettoPoint) : Bytes32;
function is_well_formed_edwards_point(p: EdwardsPoint) : bool;

procedure ristretto_compress(p: RistrettoPoint) returns (r: CompressedRistretto)
spec {
  requires is_well_formed_edwards_point(p.inner);
  ensures  r.bytes == spec_ristretto_compress(p);
}
{
  // body mirrors the Rust exec, using axiomatized field ops
  let u1      := fe_mul(fe_add(p.inner.Z, p.inner.Y),
                        fe_sub(p.inner.Z, p.inner.Y));
  let u2      := fe_mul(p.inner.X, p.inner.Y);
  let inv_res := fe_invsqrt(fe_mul(u1, fe_square(u2)));
  let i1      := fe_mul(inv_res.val, u1);
  let i2      := fe_mul(inv_res.val, u2);
  let z_inv   := fe_mul(i1, fe_mul(i2, p.inner.T));
  // ... conditional rotation, sign normalisation → s : FieldElement51
  r := CompressedRistretto { bytes: fe_as_bytes(s) };  // s from rotation step
};
```

---

## Gap summary

| Gap | B1 | B2 | B3 | B4 | B5 | Notes |
|-----|:--:|:--:|:--:|:--:|:--:|----|
| Struct/record types (Gap #13) | ✓ | ✓ | ✓ | — | ✓ | Single fix unblocks B1, B2, B3, B5 |
| Native `nat` (Gap #8) | ✓ | ✓ | ✓ | — | ✓ | Single fix unblocks B1, B2, B3, B5 |
| `u128` as `int` modeling | ✓ | — | — | — | — | Modeling choice, not a language feature |
| Mutable reference parameters | — | — | ✓ | — | — | `&mut P`, `&mut Q` in B3; modeled as in/out pairs in Boole seed |
| `old()` in postconditions | — | — | ✓ | — | — | Pre-state references in B3 ensures; eliminated by in/out pair model |
| Fixed-size array types `[T; N]` | — | — | — | ✓ | — | `Scalar.bytes: [u8; 32]`; distinct from struct field access |
| `scalar_as_nat` / byte-array lifting | — | — | — | ✓ | — | Extends Gap #8 to byte-array representations |
| Pair/tuple return types | — | — | — | — | ✓ | `invsqrt()` returns `(bool, FieldElement51)` |
| Ghost variables | — | — | — | — | ✓ | Intermediate proof assertions in B5 body |
| Field op axiom stubs | — | — | — | — | ✓ | `add`, `sub`, `square`, `invsqrt`, etc.; follow B1 `mul` pattern |

**Implementation status:** As of writing, none of the gaps required by these
benchmarks are implemented. The Boole features that are implemented
(extensional equality, early return, bitvectors, mutual recursion over
datatypes, nested loop lowering) are not required by any of the five
benchmarks.

**Critical path:** Gap #13 and Gap #8 unblock B1, B2, B3, and B5 (with B5 also
needing tuple and ghost support). B4 (`Scalar::invert`) is blocked by the
fixed-size array gap, which is independent of the struct gap. B2
(`EdwardsPoint::add`) and B3 (`differential_add_and_double`) add no new
language gaps beyond B1 once the `&mut`/`old()` pair is modeled out of
existence in the Boole seed.

**Untracked gaps:** The mutable reference parameters, `old()`, ghost
variables, and pair/tuple return type gaps are not yet tracked in
[`BooleFeatureRequests.md`](BooleFeatureRequests.md). The remaining gaps
(#8, #13, and those attributed to Gap #14) are tracked there.
