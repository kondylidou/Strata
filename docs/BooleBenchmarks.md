# Boole Benchmark Targets

This document defines three target benchmarks drawn from
[dalek-lite](https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/main/curve25519-dalek)
— a Verus-verified Rust implementation of Curve25519/Ed25519 cryptography.
Each benchmark is a real exec function with `requires`/`ensures` annotations.
The goal is to run these through the Verus → Boole pipeline and verify the
postconditions with cvc5.

The three benchmarks cover the three core mathematical layers of the protocol:

| # | Benchmark | Layer | Source file |
|---|-----------|-------|-------------|
| 1 | `FieldElement51::mul` | Field arithmetic (GF(2²⁵⁵ − 19)) | `backend/serial/u64/field.rs` |
| 2 | `EdwardsPoint::add` | Group law (twisted Edwards curve) | `edwards.rs` |
| 3 | `RistrettoPoint::compress` | Protocol-level encoding (Ristretto group) | `ristretto.rs` |

Benchmark 1 verifies the arithmetic primitive. Benchmark 2 verifies that the
extended-coordinate addition formula correctly implements the elliptic curve
group law — the layer every scalar multiplication and signature operation
depends on. Benchmark 3 verifies a protocol operation composed from the
lower layers. Together they demonstrate that Boole can reason from low-level
field ops through the group law up to cryptographic protocol correctness.

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
(Benchmark 3) are disconnected.

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

// Affine projection: (X/Z, Y/Z)
function edwards_point_as_affine(p: EdwardsPoint) : (int, int);

// Twisted Edwards group law (curve constant d baked in)
function edwards_add(x1: int, y1: int, x2: int, y2: int) : (int, int);
axiom (∀ x1, y1, x2, y2 .
  edwards_add(x1, y1, x2, y2).0 ==
    field_div(field_add(field_mul(x1, y2), field_mul(y1, x2)),
              field_add(1, field_mul(D, field_mul(field_mul(x1, x2),
                                                  field_mul(y1, y2))))) &&
  edwards_add(x1, y1, x2, y2).1 ==
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
           edwards_add(edwards_point_as_affine(p).0,
                       edwards_point_as_affine(p).1,
                       edwards_point_as_affine(q).0,
                       edwards_point_as_affine(q).1);
}
{ /* Niels-coordinate extended addition: PP, MM, TT2d, ZZ2, completed → extended */ };
```

---

## Benchmark 3 — `RistrettoPoint::compress`

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

This benchmark shares all gaps from Benchmarks 1 and 2 and adds the following:

| Gap | Description | Status |
|-----|-------------|--------|
| **Struct/record types** (Gap #13) | `EdwardsPoint` has four `FieldElement51` fields (X, Y, Z, T). Same fix as Benchmark 1. | Active |
| **Native `nat`** (Gap #8) | Field element values must be lifted to `nat` for the spec. Same fix as Benchmark 1. | Active |
| **Pair/tuple return types** | `invsqrt()` returns `(bool, FieldElement51)` — a two-element struct or tuple. The ignore-first pattern `let (_, invsqrt) = ...` requires destructuring. | Active — related to missing model types (Gap #9) |
| **Ghost variables** | The body uses `let ghost x_nat = fe51_as_canonical_nat(&self.0.X)` throughout to name intermediate values in proof assertions. Boole needs a `ghost` variable annotation. | Active |
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

type CompressedRistretto := { bytes: Bytes32 };

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

// Connecting axiom: all field ops respect the canonical-nat spec
axiom (∀ a, b . fe_as_nat(fe_mul(a, b)) mod P
             == field_mul(fe_as_nat(a) mod P, fe_as_nat(b) mod P));
// ... analogous axioms for add, sub, square, invsqrt

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
  // ... rotation, sign-normalisation, s.as_bytes()
  r := CompressedRistretto { bytes: fe_as_bytes(s) };
};
```

---

## Gap summary

| Gap | Benchmark 1 | Benchmark 2 | Benchmark 3 | Notes |
|-----|:-----------:|:-----------:|:-----------:|-------|
| Struct/record types (Gap #13) | required | required | required | Single fix unblocks all three |
| Native `nat` (Gap #8) | required | required | required | Single fix unblocks all three |
| `u128` as `int` modeling | required | — | — | Modeling choice, not a language feature |
| Pair/tuple return types | — | — | required | For `invsqrt` return value |
| Ghost variables | — | — | required | For intermediate proof assertions in body |
| Field op axiom stubs | — | — | required | `add`, `sub`, `square`, `invsqrt`, etc. — follows same pattern as `mul` axiom in Benchmark 1 |

**Critical path:** closing Gap #13 (struct/record types) and Gap #8 (native `nat`)
unblocks all three benchmarks. These are the same two gaps already tracked in
[`BooleFeatureRequests.md`](BooleFeatureRequests.md). Benchmark 2 (`EdwardsPoint::add`)
is notable in that it adds no new language gaps beyond Benchmark 1 — it is purely
a more complex postcondition over the same two fixed features. All remaining items
for Benchmark 3 are one-off stubs or modeling decisions, not new language features.
