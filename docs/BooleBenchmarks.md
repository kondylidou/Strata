# Boole Benchmark Targets

Benchmarks B1–B5 come from [dalek-lite](https://github.com/Beneficial-AI-Foundation/dalek-lite) — a Verus-verified Rust implementation of Curve25519/Ed25519. Each is a real exec function with `requires`/`ensures`; the goal is to run through the Verus → Boole pipeline and discharge postconditions with cvc5.

B6 comes from [RustCrypto/hashes](https://github.com/RustCrypto/hashes) — plain (non-Verus) Rust. The spec is written by us in Boole directly, exercising the pipeline on a widely deployed symmetric primitive.

---

## Why these benchmarks

B1–B5 are the core operations of three widely deployed cryptographic systems: X25519 key exchange, Ed25519 signatures, and Ristretto255 (the prime-order group used in zero-knowledge proof frameworks).

- Field multiplication (`FieldElement51::mul`) is the arithmetic foundation of Curve25519 — every higher-level operation, from key exchange to signature verification, ultimately reduces to repeated calls to it.
- Scalar reduction (`from_bytes_mod_order_wide`) reduces a 64-byte hash output to a canonical scalar, enforcing the security property whose absence caused signature malleability vulnerabilities in several widely-used libraries including OpenSSL and tinyssh (RFC 8032 §5.1.7); it additionally guarantees that a uniformly random input produces a uniformly random scalar — the property required for secure nonce generation in EdDSA.
- Point decompression (`CompressedEdwardsY::decompress`) and Ristretto compression (`RistrettoPoint::compress`) are the serialization steps that happen at every Ed25519 signature verification and every Ristretto255-based proof respectively.
- `MontgomeryPoint::mul_clamped` is the core scalar multiplication step of X25519 — the key exchange used in TLS 1.3, Signal, WireGuard, and SSH.

B6 (`compress_u32`) adds a symmetric-primitive target: SHA-256 underpins HMAC-SHA-256, TLS 1.3 key derivation, and Bitcoin's double-SHA-256 proof-of-work, making it one of the most widely deployed hash primitives in existence.

## Overview

| # | Function | Protocol / Layer | Source | Total lines | Exec lines |
|---|----------|-----------------|--------|:-----------:|:----------:|
| 1 | `FieldElement51::mul` | Field arithmetic — GF(2²⁵⁵ − 19) | `field.rs` | 149 | ~50 |
| 2 | `Scalar::from_bytes_mod_order_wide` | Scalar arithmetic — ℤ/ℓℤ | `scalar.rs` | 49 | 13 |
| 3 | `CompressedEdwardsY::decompress` | Ed25519 — point decompression | `edwards.rs` | 76 | ~36 |
| 4 | `RistrettoPoint::compress` | Ristretto / ZK — group encoding | `ristretto.rs` | 309 | ~35 |
| 5 | `MontgomeryPoint::mul_clamped` | X25519 — key exchange | `montgomery.rs` | 45 (+400†) | 3 (+400†) |
| 6 | `compress_u32` | SHA-256 block compression | `sha256/soft/compact.rs` | ~55 | ~45 |

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

- Every Curve25519 operation — X25519, Ed25519, Ristretto — reduces to repeated calls to `mul`.
- Proving `mul` correct verifies the arithmetic foundation every higher-level proof depends on.
- The postcondition is a bounded-integer arithmetic claim.

---

## Benchmark 2 — `Scalar::from_bytes_mod_order_wide`

**49 lines** (scalar.rs:300–348) · 13 exec statements

```rust
pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (result: Scalar)
    ensures
        scalar_as_canonical(&result) == group_canonical(bytes_seq_as_nat(input@)),
        is_canonical_scalar(&result),
        is_uniform_bytes(input) ==> is_uniform_scalar(&result),
```

- Takes a 64-byte input — the size of a SHA-512 hash output — and reduces it mod ℓ to a canonical scalar. This is the function used in EdDSA nonce generation: `H(k || M)` (a 64-byte hash) is passed through this function to produce the signing scalar `r`.
- The first two postconditions enforce canonical encoding, whose absence caused signature malleability vulnerabilities in several widely-used libraries including OpenSSL and tinyssh (RFC 8032 §5.1.7).
- The third postcondition is a probabilistic security property: if the input is uniformly distributed (as a hash output is), the output scalar is also uniformly distributed. This is the property required for **nonce secrecy** — a biased nonce in EdDSA directly leaks the private key (as in the ECDSA PlayStation 3 attack).

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

- Ed25519 signature verification begins by decompressing the public key and signature point from their 32-byte encodings — this is that step.
- The postcondition has four conditions: success iff the y-coordinate is valid on the curve, correct Y, Z=1, and sign bit matching — together they fully characterise what a valid decompression means.
- Used in every SSH connection, TLS 1.3 handshake, and code-signing check that uses Ed25519.

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

- Ristretto255 is the prime-order group abstraction over Curve25519 (cofactor 8); it eliminates the cofactor problem that would otherwise allow forged proofs. The `dalek-cryptography/bulletproofs` crate builds Bulletproofs and Pedersen commitments over it. `compress` is called every time a group element is serialised.
- The postcondition is a functional-correctness theorem linking imperative Rust to the [Ristretto RFC (RFC 9496)](https://datatracker.ietf.org/doc/html/rfc9496) mathematical spec.
- Builds directly on Benchmark 1: once `mul` is axiomatized, all remaining field ops follow the same pattern.

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

- This is the core scalar multiplication step of X25519, the key exchange used in TLS 1.3, Signal, WireGuard, and SSH.
- The postcondition states functional correctness of this step: the output u-coordinate equals `[n]P` on the Montgomery curve.
- Verifying this in Boole would give a mechanically checked proof that the arithmetic core of X25519 is correct.

---

## Benchmark 6 — `compress_u32`

**~55 lines** (sha256/soft/compact.rs) · ~45 exec statements · source: [RustCrypto/hashes](https://github.com/RustCrypto/hashes/blob/master/sha2/src/sha256/soft/compact.rs)

```rust
fn compress_u32(state: &mut [u32; 8], mut block: [u32; 16]) { ... }
```

The spec we write in Boole:

```
ensures *state == sha256_compress_spec(initial_state, block)
```

where `sha256_compress_spec` is the FIPS 180-4 round function unrolled over 64 iterations, using the SHA-256 constants `K32`.

- SHA-256 underpins HMAC-SHA-256, TLS 1.3 key derivation, and Bitcoin's double-SHA-256 proof-of-work; `compress_u32` is among the most widely deployed hash primitives in existence.
- Unlike B1–B5 (Verus-annotated), the spec is written by us in Boole directly. The 64-round loop with in-place message schedule and eight chained `u32` state variables exercises `bv32` arithmetic, `rotate_right`, array indexing, loop invariants, and wrapping addition.
- New language feature required: `rotate_right` (`bvrotr` in SMT-LIB).

---

## Gap status

Legend: ○ open · ✓ done

Language feature implementations are tracked in
[`BooleFeatureRequests.md`](BooleFeatureRequests.md).
This table tracks benchmark-specific gaps. A full benchmark seed is added to
[`StrataTest/Languages/Boole/Benchmarks/`](../StrataTest/Languages/Boole/Benchmarks/)
only once all gaps for that benchmark are closed. Until then, gap-specific small
seeds live in
[`StrataTest/Languages/Boole/FeatureRequests/`](../StrataTest/Languages/Boole/FeatureRequests/).

**Shared by all six benchmarks:**

| Gap | FR# | Status | Gap seed |
|-----|-----|--------|----------|
| Struct/record field access | #13 | ○ open | [`struct_field_access.lean`](../StrataTest/Languages/Boole/FeatureRequests/struct_field_access.lean) |
| Native `nat` support | #10 | ○ open | [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) |
| Recursive spec functions over sequences | #11 | ○ open | [`seq_slicing.lean`](../StrataTest/Languages/Boole/FeatureRequests/seq_slicing.lean) — basic ops (`Sequence.skip`, `Sequence.subrange`, `Sequence.take`, etc.) are implemented; remaining gap is recursive spec functions that walk a sequence element by element: `bytes_seq_as_nat` (needed by B2 and B5), `seq_as_nat_52` (B1), and `field_element_from_bytes` (B3, B4); these need int-based termination proofs (blocked on `@[cases]`-free recursion over `int`) |

**Additional gaps per benchmark:**

| # | Gap | FR# | Status | Notes |
|---|-----|-----|--------|-------|
| 1 | `u128` as `int` | — | ○ open | 25 cross-limb products; no new language feature needed once struct access lands — model `u64`/`u128` limbs as `int` |
| 2 | `[u8; 64]` byte arrays | — | ○ open | Model as `Map int bv8`; pattern demonstrated in [`bitvector_ops.lean`](../StrataTest/Languages/Boole/bitvector_ops.lean) |
| 2 | `reduce()` spec function | — | ✓ done | Axiom seed [`scalar_reduce.lean`](../StrataTest/Languages/Boole/FeatureRequests/scalar_reduce.lean) verifies with abstract `ByteArray32`/`Scalar` types; `bytes_seq_as_nat` stays abstract — spelling it out recursively requires int-based termination over sequences (open gap) |
| 2 | `is_uniform_scalar` axiom | — | ○ open | Probabilistic postcondition; needs abstract `is_uniform_bytes` / `is_uniform_scalar` predicates as Boole axioms |
| 3 | `Option<EdwardsPoint>` return | — | ○ open | Encoding pattern demonstrated in [`option_matches.lean`](../StrataTest/Languages/Boole/FeatureRequests/option_matches.lean) and [`datatypes_and_selectors.lean`](../StrataTest/Languages/Boole/FeatureRequests/datatypes_and_selectors.lean) |
| 3 | `field_square` / `sqrt_ratio_i` axioms | — | ○ open | Needed for the full decompress body |
| 4 | Pair return type | — | ○ open | `invsqrt()` returns `(bool, FieldElement51)`; needs tuple/pair type support |
| 4 | Field op axioms | — | ○ open | `add`, `sub`, `square`, `invsqrt`, `conditional_negate`, `as_bytes` — each needs a Boole axiom |
| 5 | Inline `let`-block postcondition | — | ✓ done | Implemented; see [`embedded_postcondition.lean`](../StrataTest/Languages/Boole/embedded_postcondition.lean) and BooleFeatureRequests.md |
| 5 | Montgomery ladder invariant | — | ○ open | Requires group-law axioms (Costello-Smith 2017, eq. 4); [`montgomery_loop_invariant.lean`](../StrataTest/Languages/Boole/FeatureRequests/montgomery_loop_invariant.lean) covers the relational loop pattern |
| 6 | `rotate_right` / `bvrotr` | — | ○ open | `u32::rotate_right(n)` used 6× in the round function; needs `Bv{N}.RotR` Core op and Boole syntax |
| 6 | `[u32; N]` arrays as `Map int bv32` | — | ○ open | Same pattern as `[u8; 64]` in B2; modular index arithmetic `i % 16` also needed |
| 6 | 64-round loop invariant | — | ○ open | State and message-schedule invariant across all 64 rounds; blocked on loop invariant support |
| 6 | SHA-256 round spec axiom | — | ○ open | `sha256_compress_spec` needs to be declared as a Boole axiom linking the imperative loop to the FIPS 180-4 spec |

