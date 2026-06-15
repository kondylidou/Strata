# Boole Benchmark Targets

Benchmarks B1–B5 come from [dalek-lite](https://github.com/Beneficial-AI-Foundation/dalek-lite) — a Verus-verified Rust implementation of Curve25519/Ed25519. Each is a real exec function with `requires`/`ensures`; the goal is to run through the Verus → Boole pipeline and discharge postconditions with cvc5.

---

## Why these benchmarks

B1–B5 cover the full stack of three widely deployed cryptographic systems: X25519 key exchange, Ed25519 signatures, and Ristretto255.

- `FieldElement51::mul` — arithmetic foundation; every curve operation reduces to repeated calls to it.
- `from_bytes_mod_order_wide` — reduces a 64-byte hash to a canonical EdDSA signing scalar; absent canonicality caused malleability vulnerabilities in OpenSSL and tinyssh (RFC 8032 §5.1.7); the uniform-output property prevents key leakage via biased nonces.
- `CompressedEdwardsY::decompress` / `RistrettoPoint::compress` — serialization at every Ed25519 verification and Ristretto255 proof.
- `MontgomeryPoint::mul_clamped` — core of X25519, used in TLS 1.3, Signal, WireGuard, and SSH.

## Overview

| # | Function | Protocol / Layer | Source | Total lines | Exec lines |
|---|----------|-----------------|--------|:-----------:|:----------:|
| 1 | `FieldElement51::mul` | Field arithmetic — GF(2²⁵⁵ − 19) | `field.rs` | 149 | ~50 |
| 2 | `Scalar::from_bytes_mod_order_wide` | Scalar arithmetic — ℤ/ℓℤ | `scalar.rs` | 49 | 13 |
| 3 | `CompressedEdwardsY::decompress` | Ed25519 — point decompression | `edwards.rs` | 76 | ~36 |
| 4 | `RistrettoPoint::compress` | Ristretto / ZK — group encoding | `ristretto.rs` | 309 | ~35 |
| 5 | `MontgomeryPoint::mul_clamped` | X25519 — key exchange | `montgomery.rs` | 45 (+400†) | 3 (+400†) |

† `mul_clamped` delegates to `mul_bits_be` (the Montgomery ladder), which is ~400 lines with a loop invariant.

---

## Benchmark 1 — `FieldElement51::mul`

**149 lines** (field.rs:486–634) · ~50 exec statements

```rust
fn mul(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)
    requires fe51_limbs_bounded(self, 54) && fe51_limbs_bounded(_rhs, 54),
    ensures
        fe51_as_canonical_nat(&output)
            == field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)),
        fe51_limbs_bounded(&output, 52),
```

- Foundation of all Curve25519 arithmetic; every higher-level operation reduces to `mul`.
- Postcondition: bounded-integer claim over 5-limb radix-2⁵¹ representation.

---

## Benchmark 2 — `Scalar::from_bytes_mod_order_wide`

**49 lines** (scalar.rs:300–348) · 2 exec statements

```rust
pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (result: Scalar)
    ensures
        scalar_as_canonical(&result) == group_canonical(bytes_seq_as_nat(input@)),
        is_canonical_scalar(&result),
        is_uniform_bytes(input) ==> is_uniform_scalar(&result),
```

- Reduces a 64-byte SHA-512 hash to a canonical EdDSA signing scalar `r`.
- First postcondition: correctness — output equals input reduced mod ℓ (the function computes the right value).
- Second postcondition: canonicality — output is the unique representative in [0, ℓ) with high bit clear; absent this, two distinct byte strings can represent the same scalar, enabling signature malleability (CVE in OpenSSL and tinyssh, RFC 8032 §5.1.7).
- Third postcondition: uniformity — uniform 512-bit input produces a statistically uniform scalar; a biased nonce leaks the private key (cf. ECDSA PS3 attack).

---

## Benchmark 3 — `CompressedEdwardsY::decompress`

**76 lines** (edwards.rs:279–354) · ~36 exec statements

```rust
pub fn decompress(&self) -> (result: Option<EdwardsPoint>)
    ensures
        is_valid_edwards_y_coordinate(field_element_from_bytes(&self.0)) <==> result.is_some(),
        result.is_some() ==> (
            edwards_y_nat(result.unwrap()) == field_element_from_bytes(&self.0)
            && edwards_z_nat(result.unwrap()) == 1
            && is_well_formed_edwards_point(result.unwrap())
            && (field_square(field_element_from_bytes(&self.0)) != 1
                    ==> edwards_x_sign_bit(result.unwrap()) == (self.0[31] >> 7))
        ),
```

- The decompression step in every Ed25519 verification (SSH, TLS 1.3, code signing).
- Four postconditions: success iff y is on the curve, correct Y, Z=1, sign bit match — fully characterising valid decompression.

---

## Benchmark 4 — `RistrettoPoint::compress`

**309 lines** (ristretto.rs:1104–1412) · ~35 exec statements

```rust
pub fn compress(&self) -> (result: CompressedRistretto)
    requires is_well_formed_edwards_point(self.0),
    ensures  result.0 == spec_ristretto_compress(*self),
```

where `spec_ristretto_compress` expands to:

```
u1 = (Z+Y)(Z−Y),  u2 = X·Y,  invsqrt = 1/√(u1·u2²)
→ rotation by coset representative selection
→ sign normalisation
→ serialize to 32 bytes
```

- Ristretto255 eliminates Curve25519's cofactor-8 problem; used in `bulletproofs` (Bulletproofs, Pedersen commitments). Called on every serialised group element.
- Postcondition links the implementation to the [Ristretto RFC (RFC 9496)](https://datatracker.ietf.org/doc/html/rfc9496) spec.
- Builds on B1: once `mul` is axiomatized, remaining field ops follow the same pattern.

---

## Benchmark 5 — `MontgomeryPoint::mul_clamped`

**45 lines** (montgomery.rs:408–452) · 3 exec statements + delegates to `mul_bits_be` (Montgomery ladder, ~400 lines)

```rust
pub fn mul_clamped(self, bytes: [u8; 32]) -> (result: Self)
    requires is_valid_montgomery_point(self),
    ensures ({
        let P = canonical_montgomery_lift(montgomery_point_as_nat(self));
        let clamped_bytes = spec_clamp_integer(bytes);
        let n = u8_32_as_nat(&clamped_bytes);
        let R = montgomery_scalar_mul(P, n);
        montgomery_point_as_nat(result) == u_coordinate(R)
    }),
```

- Core scalar multiplication of X25519 (TLS 1.3, Signal, WireGuard, SSH).
- Postcondition: output u-coordinate equals `[n]P` on the Montgomery curve.

---

## Gap status

Legend: ○ open · ✓ done · → pr open

Language feature implementations are tracked in
[`BooleFeatureRequests.md`](BooleFeatureRequests.md).
This table tracks benchmark-specific gaps. A full benchmark seed is added to
[`StrataBoole/StrataBooleTest/`](../StrataBoole/StrataBooleTest/)
only once all gaps for that benchmark are closed. Until then, gap-specific small
seeds live in
[`StrataBoole/StrataBooleTest/FeatureRequests/`](../StrataBoole/StrataBooleTest/FeatureRequests/).

**Shared by all five benchmarks:**

| Gap | Status | Notes |
|-----|--------|-------|
| #13 Struct/record field access | ○ open | Boole has no record types with named field access; see [`struct_field_access.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/struct_field_access.lean) |
| #10 Native `nat` support | ○ open | `nat` must be declared abstract with manual coercion axioms; see [`nat_int_boundary.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/nat_int_boundary.lean) |
| #11 Recursive spec functions over sequences | ✓ done (#1167) | `decreases <int expr>` implemented. Int-recursive functions are pure UFs in SMT — manual axioms still needed for `u8_64_as_group_canonical` (B2, B5), `seq_as_nat_52` (B1), `field_element_from_bytes` (B3, B4). `reconstruct` in [`seq_slicing.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/seq_slicing.lean) now active. |

**Additional gaps per benchmark:**

| B | Gap | Status | Notes |
|---|-----|--------|-------|
| 1 | `u128` intermediate products | ✓ resolved | Modelled as `int`; no separate feature needed. See [`b1_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b1_minimal.lean) |
| 1 | #13 `FieldElement51.limbs: [u64; 5]` | ✓ resolved | Encoded as `Sequence bv64` with length-5 invariant in specs. See [`b1_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b1_minimal.lean) |
| 1 | `lemma_mul_boundary` proof | → pr open | Support lemmas from §7a translated to Boole; bitvector/LA sub-lemmas proved. Only NL product-bound lemmas remain trusted. See [`b1_boundary_proved.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b1_boundary_proved.lean) |
| 1 | full proof closure (`b1_full`) | ○ blocked | The zero-dalek-admit B1 (49 procedures, ~1330 lines; only vstd library lemmas stubbed) ships `#exit`-guarded: `#strata` elaboration stack-overflows on programs this size, independent of `maxRecDepth`/OS stack — needs elaborator-side chunking. See [`b1_full.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b1_full.lean) |
| 2 | #15 `[u8; 64]` byte arrays | ✓ resolved (B2 usage) | Wide input as `Sequence bv8`; fixed-size arrays (`[u64;5]`, `[u8;32]`) as type synonyms with the length invariant on the constructor's `requires` (a global `∀ length == N` axiom over a total datatype is unsound — see [`b2_minimal_unsound_len.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b2_minimal_unsound_len.lean)); `Sequence.of_bv8[…]` literals for initializers. See [`b2_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b2_minimal.lean) |
| 5 | #15 `[u8; 32]` byte arrays | ✓ resolved | `MontgomeryPoint`/`Scalar` lower to `Sequence bv8` type synonyms with the length-32 invariant on the constructor's `requires` (same wrapper-datatype model as B2); `Sequence.of_bv8[…]` literals for `spec_clamp_integer`. The `clamp_integer` bit-vector proof verifies. See [`b5_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b5_minimal.lean) |
| 2 | `reduce()` spec function | ✓ done | Axiom pattern verified in [`scalar_reduce.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/scalar_reduce.lean); `u8_64_as_group_canonical` can now use recursive form (#1167 merged); manual axioms unchanged |
| 2 | `is_uniform_scalar` axiom | ✓ resolved | Abstract `is_uniform_bytes`/`is_uniform_scalar` uninterpreted predicates + the trusted uniform-reduction lemma, GUARDED by `canonical(result) == bytes_as_nat(input) mod group_order` (a stubbed procedure in [`b2_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b2_minimal.lean); a guarded quantified axiom in [`b2_minimal_playground_pow2.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b2_minimal_playground_pow2.lean)) |
| 3 | #14 `Option<EdwardsPoint>` return | ✓ resolved | Modeled as the two-constructor datatype `Option_option`, with the tester (`..isOption_option_Some`) and selector (`..Option_option_Some_0`) used directly in spec clauses. See [`b3_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b3_minimal.lean) |
| 3 | `field_square` / `sqrt_ratio_i` axioms | ✓ resolved (minimal variant) | The field-operation pipelines are the trusted `Decompress_step_1`/`Decompress_step_2` stubs with dalek-lite specs; the decompress body and its proof verify against them. Proving the pipelines themselves remains future work. See [`b3_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b3_minimal.lean) |
| 4 | Pair / tuple return type | ✓ resolved | `invsqrt()`'s `(Choice, FieldElement)` and `edwards_point_as_nat`'s 4-tuple lower to nested binary `Tuple2` pairs with `Tuple2.._0`/`.._1` projection chains. See [`b4_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b4_minimal.lean) |
| 4 | Field op axioms | ✓ resolved | `fe_add`/`fe_sub`/`fe_mul`/`square`/`invsqrt`/`is_negative`/`as_bytes` and the `conditional_*` wrappers are trusted external-body procedures with dalek-lite specs verbatim; the `compress` body verifies against them. cvc5 519/791 (0 fail). See [`b4_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b4_minimal.lean) |
| 5 | Inline `let`-block postcondition | ✓ done | Implemented; see [`embedded_postcondition.lean`](../StrataBoole/StrataBooleTest/embedded_postcondition.lean) |
| 5 | Operator trait-method dispatch | ○ open | `b5_minimal` type-checks and reaches cvc5 (**241/329**, 1 enc err, 87 ⌛); `clamp_integer` verifies. The lone encoding error is `mul_clamped`'s `&self * &s` call lowering to the abstract trait method `Ops_Arith_Mul_mul` (vacuous `obeys_mul_spec ==> ret == mul_spec` ensures) instead of the resolved impl `Impl__13_mul`, which carries the real Montgomery ensures (`montgomery_point_as_nat(result) == u_coordinate(montgomery_scalar_mul(…))`) but is never called. VLIR already records the `resolved_method`; the call and trait spec-refs must dispatch to it. A translator fix, not a proof. See [`b5_minimal.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/b5_minimal.lean) |
| 5 | Montgomery ladder invariant | ○ open | The ladder (`mul_bits_be`) and the `*` operator are trusted as `assume(false)` axioms in the seed, their `ensures` reproduced verbatim — sound for the `mul_clamped` target, which needs only the ladder's postcondition, not its proof. Proving the ladder itself (the constant-difference loop invariant + Costello-Smith 2017 eq. 4 differential-addition axioms) stays future work; loop structure in [`montgomery_loop_invariant.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/montgomery_loop_invariant.lean) |

