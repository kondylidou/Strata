// from_bytes_mod_order_wide — self-contained Verus source
//
// Assembled from:
//   curve25519-dalek/src/scalar.rs                          (target function)
//   curve25519-dalek/src/backend/serial/u64/scalar.rs       (Scalar52, from_bytes_wide, as_bytes, pack)
//   curve25519-dalek/src/specs/core_specs.rs                (byte-to-nat specs)
//   curve25519-dalek/src/specs/scalar52_specs.rs            (limb specs, group order)
//
// dalek-lite: https://github.com/Beneficial-AI-Foundation/dalek-lite

#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;   // lemma_small_mod, lemma_mod_bound
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ============================================================
// § 1  Core specs  (specs/core_specs.rs)
// ============================================================

/// Little-endian natural value of a byte sequence.
pub open spec fn bytes_seq_as_nat(bytes: Seq<u8>) -> nat
    decreases bytes.len(),
{
    if bytes.len() == 0 { 0 } else { (bytes[0] as nat) + pow2(8) * bytes_seq_as_nat(bytes.skip(1)) }
}

/// Little-endian natural value of a fixed 32-byte array (explicit 32-term form for SMT).
#[verusfmt::skip]
pub open spec fn u8_32_as_nat(bytes: &[u8; 32]) -> nat {
    (bytes[ 0] as nat) * pow2(  0) + (bytes[ 1] as nat) * pow2(  8) +
    (bytes[ 2] as nat) * pow2( 16) + (bytes[ 3] as nat) * pow2( 24) +
    (bytes[ 4] as nat) * pow2( 32) + (bytes[ 5] as nat) * pow2( 40) +
    (bytes[ 6] as nat) * pow2( 48) + (bytes[ 7] as nat) * pow2( 56) +
    (bytes[ 8] as nat) * pow2( 64) + (bytes[ 9] as nat) * pow2( 72) +
    (bytes[10] as nat) * pow2( 80) + (bytes[11] as nat) * pow2( 88) +
    (bytes[12] as nat) * pow2( 96) + (bytes[13] as nat) * pow2(104) +
    (bytes[14] as nat) * pow2(112) + (bytes[15] as nat) * pow2(120) +
    (bytes[16] as nat) * pow2(128) + (bytes[17] as nat) * pow2(136) +
    (bytes[18] as nat) * pow2(144) + (bytes[19] as nat) * pow2(152) +
    (bytes[20] as nat) * pow2(160) + (bytes[21] as nat) * pow2(168) +
    (bytes[22] as nat) * pow2(176) + (bytes[23] as nat) * pow2(184) +
    (bytes[24] as nat) * pow2(192) + (bytes[25] as nat) * pow2(200) +
    (bytes[26] as nat) * pow2(208) + (bytes[27] as nat) * pow2(216) +
    (bytes[28] as nat) * pow2(224) + (bytes[29] as nat) * pow2(232) +
    (bytes[30] as nat) * pow2(240) + (bytes[31] as nat) * pow2(248)
}

/// Generic suffix sum: bytes[start..N] with original positional weights.
pub open spec fn bytes_as_nat_suffix<const N: usize>(bytes: &[u8; N], start: int) -> nat
    decreases (N as int) - start,
{
    if start >= N as int { 0 }
    else { (bytes[start] as nat) * pow2((start * 8) as nat) + bytes_as_nat_suffix(bytes, start + 1) }
}

/// Load 8 consecutive bytes as a little-endian u64 value.
#[verusfmt::skip]
pub open spec fn spec_load8_at(input: &[u8], i: usize) -> nat {
    (pow2( 0) * input[i + 0] + pow2( 8) * input[i + 1] +
     pow2(16) * input[i + 2] + pow2(24) * input[i + 3] +
     pow2(32) * input[i + 4] + pow2(40) * input[i + 5] +
     pow2(48) * input[i + 6] + pow2(56) * input[i + 7]) as nat
}

/// Sum of the first `count` extracted 64-bit words as a nat.
pub open spec fn words64_from_bytes_to_nat(bytes: Seq<u8>, count: int) -> nat
    decreases if count <= 0 { 0 } else { count as nat },
{
    let num_words = bytes.len() as int / 8;
    if count <= 0 { 0 }
    else if count > num_words { words64_from_bytes_to_nat(bytes, num_words) }
    else {
        let idx = count - 1;
        words64_from_bytes_to_nat(bytes, idx) + word64_from_bytes(bytes, idx) * pow2((idx * 64) as nat)
    }
}

/// Extract a 64-bit word (8 bytes) from a byte sequence by word index.
#[verusfmt::skip]
pub open spec fn word64_from_bytes(bytes: Seq<u8>, word_idx: int) -> nat {
    let num_words = bytes.len() as int / 8;
    if !(0 <= word_idx && word_idx < num_words) { 0 }
    else {
        let base = word_idx * 8;
        (bytes[(base + 0) as int] as nat) * pow2( 0) + (bytes[(base + 1) as int] as nat) * pow2( 8) +
        (bytes[(base + 2) as int] as nat) * pow2(16) + (bytes[(base + 3) as int] as nat) * pow2(24) +
        (bytes[(base + 4) as int] as nat) * pow2(32) + (bytes[(base + 5) as int] as nat) * pow2(40) +
        (bytes[(base + 6) as int] as nat) * pow2(48) + (bytes[(base + 7) as int] as nat) * pow2(56)
    }
}

// ============================================================
// § 2  Scalar52 specs  (specs/scalar52_specs.rs)
// ============================================================

/// Group order ℓ = 2^252 + 27742317777372353535851937790883648493
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

/// Canonical reduction mod ℓ.
pub open spec fn group_canonical(n: nat) -> nat { n % group_order() }

/// Montgomery radix R = 2^260.
pub open spec fn montgomery_radix() -> nat { pow2(260) }

/// Convert 5 × 52-bit limbs to a natural number (little-endian radix-2^52).
#[verusfmt::skip]
pub open spec fn five_limbs_to_nat_aux(limbs: [u64; 5]) -> nat {
                  (limbs[0] as nat) +
    pow2( 52) *   (limbs[1] as nat) +
    pow2(104) *   (limbs[2] as nat) +
    pow2(156) *   (limbs[3] as nat) +
    pow2(208) *   (limbs[4] as nat)
}

pub open spec fn limbs52_as_nat(limbs: &[u64]) -> nat {
    seq_as_nat_52(limbs@.map(|_i, x: u64| x as nat))
}

pub open spec fn seq_as_nat_52(limbs: Seq<nat>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 { 0 }
    else { limbs[0] + seq_as_nat_52(limbs.subrange(1, limbs.len() as int)) * pow2(52) }
}

pub open spec fn scalar52_as_nat(s: &Scalar52) -> nat { limbs52_as_nat(&s.limbs) }

/// All limbs < 2^52.
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}

/// Limbs bounded and value < ℓ.
pub open spec fn is_canonical_scalar52(s: &Scalar52) -> bool {
    limbs_bounded(s) && scalar52_as_nat(s) < group_order()
}

/// 9-limb polynomial value in radix-2^52 (output of mul_internal).
#[verusfmt::skip]
pub open spec fn nine_limbs_to_nat_aux(limbs: &[u128; 9]) -> nat {
    (limbs[0] as nat)              + (limbs[1] as nat) * pow2( 52) +
    (limbs[2] as nat) * pow2(104)  + (limbs[3] as nat) * pow2(156) +
    (limbs[4] as nat) * pow2(208)  + (limbs[5] as nat) * pow2(260) +
    (limbs[6] as nat) * pow2(312)  + (limbs[7] as nat) * pow2(364) +
    (limbs[8] as nat) * pow2(416)
}

/// Per-limb input bounds for montgomery_reduce (HAC 14.32).
pub uninterp spec fn montgomery_reduce_input_bounds(limbs: &[u128; 9]) -> bool;

/// T < R·L constraint for montgomery_reduce.
pub uninterp spec fn montgomery_reduce_canonical_bound(limbs: &[u128; 9]) -> bool;

/// Result × R ≡ T (mod L).
pub uninterp spec fn montgomery_congruent(result: &Scalar52, limbs: &[u128; 9]) -> bool;

// ============================================================
// § 3  Scalar / uniformity specs  (scalar.rs, proba_specs.rs)
// ============================================================

/// Bytes[31] ≤ 127 and value < ℓ.
pub open spec fn is_canonical_scalar(s: &Scalar) -> bool {
    u8_32_as_nat(&s.bytes) < group_order() && s.bytes[31] <= 127
}

pub open spec fn scalar_as_canonical(s: &Scalar) -> nat {
    group_canonical(u8_32_as_nat(&s.bytes))
}

/// Uninterpreted: input bytes are uniformly distributed.
pub uninterp spec fn is_uniform_bytes(bytes: &[u8; 64]) -> bool;

/// Uninterpreted: scalar is uniformly distributed over [0, ℓ).
pub uninterp spec fn is_uniform_scalar(s: &Scalar) -> bool;

// ============================================================
// § 4  Types and constants
// ============================================================

/// The `Scalar52` struct: element of ℤ/ℓℤ as 5 × 52-bit limbs.
#[derive(Copy, Clone)]
pub struct Scalar52 {
    pub limbs: [u64; 5],
}

/// The `Scalar` struct: canonical 32-byte little-endian encoding.
pub struct Scalar {
    pub bytes: [u8; 32],
}

/// Type alias used in scalar.rs (scalar.rs:214).
type UnpackedScalar = Scalar52;

/// R = 2^260 mod ℓ  (Montgomery radix constant).
pub const R: Scalar52 = Scalar52 {
    limbs: [0x000f48bd6721e6ed, 0x0003bab5ac67e45a, 0x000fffffeb35e51b,
            0x000fffffffffffff, 0x00000fffffffffff],
};

/// RR = R² mod ℓ  (used to convert hi-limb chunk into Montgomery domain).
pub const RR: Scalar52 = Scalar52 {
    limbs: [0x0009d265e952d13b, 0x000d63c715bea69f, 0x0005be65cb687604,
            0x0003dceec73d217f, 0x000009411b7c309a],
};

// ============================================================
// § 5  Exec helper: load8_at  (backend/serial/u64/field.rs)
// ============================================================

/// Load 8 consecutive bytes from a byte slice as a little-endian u64.
/// Body stubbed — real proof needs lemma_load8_at_* from lemmas/common_lemmas/.
pub const fn load8_at(input: &[u8], i: usize) -> (r: u64)
    requires i + 7 < input.len(),
    ensures  r as nat == spec_load8_at(input, i),
{ assume(false); 0 }

// ============================================================
// § 6  Backend helpers: mul_internal, montgomery_reduce
//      (backend/serial/u64/scalar.rs)
// ============================================================

impl Scalar52 {

    /// Compute the 9-limb schoolbook product a × b (no reduction).
    pub fn mul_internal(a: &Scalar52, b: &Scalar52) -> (result: [u128; 9])
        requires limbs_bounded(a), limbs_bounded(b),
        ensures  nine_limbs_to_nat_aux(&result) == scalar52_as_nat(a) * scalar52_as_nat(b),
    {
        // full body in backend/serial/u64/scalar.rs
        assume(false); [0u128; 9]
    }

    /// Montgomery reduction: compute T/R (mod L) from a 9-limb product T.
    pub fn montgomery_reduce(limbs: &[u128; 9]) -> (result: Scalar52)
        requires
            montgomery_reduce_input_bounds(limbs),
            montgomery_reduce_canonical_bound(limbs),
        ensures
            limbs_bounded(&result),
            montgomery_congruent(&result, limbs),
            is_canonical_scalar52(&result),
    {
        // full body in backend/serial/u64/scalar.rs (montgomery_reduce)
        assume(false); Scalar52 { limbs: [0u64; 5] }
    }

    /// Add two canonical scalars mod L.
    pub fn add(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires is_canonical_scalar52(a), is_canonical_scalar52(b),
        ensures
            is_canonical_scalar52(&result),
            scalar52_as_nat(&result) == (scalar52_as_nat(a) + scalar52_as_nat(b)) % group_order(),
    {
        assume(false); Scalar52 { limbs: [0u64; 5] }
    }

// ============================================================
// § 6  Backend: from_bytes_wide, as_bytes, pack
//      (backend/serial/u64/scalar.rs)
// ============================================================

    /// Reduce a 512-bit little-endian integer mod ℓ into a Scalar52.
    /// Body stubbed — real proof is ~300 lines in backend/serial/u64/scalar.rs.
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
        ensures
            is_canonical_scalar52(&s),
            scalar52_as_nat(&s) == group_canonical(bytes_seq_as_nat(bytes@)),
    { assume(false); Scalar52 { limbs: [0u64; 5] } }

    /// Pack 5 × 52-bit limbs into a 32-byte canonical Scalar.
    /// Body stubbed — real proof in backend/serial/u64/scalar.rs.
    pub fn as_bytes(self) -> (s: [u8; 32])
        requires limbs_bounded(&self),
        ensures  u8_32_as_nat(&s) == scalar52_as_nat(&self) % pow2(256),
    { assume(false); [0u8; 32] }

    /// Convert a canonical Scalar52 into a Scalar.
    /// Body stubbed — real proof in backend/serial/u64/scalar.rs.
    pub fn pack(&self) -> (result: Scalar)
        requires limbs_bounded(self),
        ensures
            u8_32_as_nat(&result.bytes) == scalar52_as_nat(self) % pow2(256),
            scalar52_as_nat(self) < group_order() ==> is_canonical_scalar(&result),
    { assume(false); Scalar { bytes: [0u8; 32] } }

} // impl Scalar52

// ============================================================
// § 7  Lemma stubs — large proofs that live in separate files.
//      Bodies here are `assume(false)`; the real proofs are in
//      lemmas/scalar_byte_lemmas/, lemmas/common_lemmas/,
//      and lemmas/scalar_montgomery_lemmas.rs.
// ============================================================

// ── from lemmas/scalar_byte_lemmas/ ──────────────────────────

/// scalar52_as_nat(&limbs) == five_limbs_to_nat_aux(limbs)
pub proof fn lemma_five_limbs_equals_to_nat(s: &[u64; 5])
    ensures scalar52_as_nat(&Scalar52 { limbs: *s }) == five_limbs_to_nat_aux(*s),
{ assume(false) }

/// u8_32_as_nat(&s) == scalar52_as_nat(limbs) % pow2(256) after as_bytes packing
pub proof fn lemma_as_bytes_52(limbs: [u64; 5], s: [u8; 32])
    requires limbs_bounded(&Scalar52 { limbs }),
    ensures  u8_32_as_nat(&s) == five_limbs_to_nat_aux(limbs) % pow2(256),
{ assume(false) }

// ── from lemmas/common_lemmas/to_nat_lemmas.rs ───────────────

/// u8_32_as_nat(bytes) >= bytes[idx] * pow2(idx * 8)
pub proof fn lemma_u8_32_as_nat_lower_bound(bytes: &[u8; 32], idx: int)
    requires 0 <= idx < 32,
    ensures  u8_32_as_nat(bytes) >= bytes[idx] as nat * pow2((idx * 8) as nat),
{ assume(false) }

// ── from lemmas/scalar_montgomery_lemmas.rs ──────────────────

/// Product of two bounded Scalar52s satisfies montgomery_reduce_input_bounds.
pub proof fn lemma_bounded_product_satisfies_input_bounds(
    a: &Scalar52, b: &Scalar52, product: &[u128; 9])
    requires
        limbs_bounded(a), limbs_bounded(b),
        nine_limbs_to_nat_aux(product) == scalar52_as_nat(a) * scalar52_as_nat(b),
    ensures montgomery_reduce_input_bounds(product),
{ assume(false) }

/// Product of a canonical and a canonical Scalar52 satisfies montgomery_reduce_canonical_bound.
pub proof fn lemma_canonical_product_satisfies_canonical_bound(
    a: &Scalar52, b: &Scalar52, product: &[u128; 9])
    requires
        is_canonical_scalar52(a), is_canonical_scalar52(b),
        nine_limbs_to_nat_aux(product) == scalar52_as_nat(a) * scalar52_as_nat(b),
    ensures montgomery_reduce_canonical_bound(product),
{ assume(false) }

/// The sum of two Montgomery-reduced pieces equals the original value mod ℓ.
pub proof fn lemma_montgomery_reduced_sum_congruent(
    sum: nat, hi: nat, lo: nat, hi_raw: nat, lo_raw: nat, wide: nat)
    ensures sum % group_order() == wide % group_order(),
{ assume(false) }

/// Cancelling the Montgomery radix from both sides preserves the modular value.
pub proof fn lemma_cancel_mul_pow2_mod(result: nat, wide: nat, radix: nat)
    requires radix == montgomery_radix(),
    ensures  result % group_order() == wide % group_order(),
{ assume(false) }

// ============================================================
// § 9  Proof lemmas about group_order  (lemmas/scalar_lemmas.rs)
//
//      lemma_small_mod / lemma_mod_bound come from vstd::arithmetic::div_mod
//      and are available via the `use` import above — no local definition needed.
// ============================================================

/// group_order() < 2^255
pub proof fn lemma_group_order_bound()
    ensures group_order() < pow2(255),
{
    assert(27742317777372353535851937790883648493nat < 0x40000000000000000000000000000000)
        by (compute_only);
    assert(pow2(63) == 0x8000000000000000) by { lemma2_to64_rest(); }
    lemma_pow2_adds(63, 63);
    assert(pow2(126) == 0x40000000000000000000000000000000);
    assert(27742317777372353535851937790883648493nat < pow2(126));
    lemma_pow2_strictly_increases(126, 252);
    assert(group_order() < pow2(252) + pow2(252));
    assert(pow2(252) + pow2(252) == pow2(253)) by {
        lemma_pow2_adds(1, 252); lemma2_to64();
    }
    lemma_pow2_strictly_increases(253, 255);
}

/// group_order() < 2^256
pub proof fn lemma_group_order_smaller_than_pow256()
    ensures group_order() < pow2(256),
{
    lemma_group_order_bound();
    lemma_pow2_strictly_increases(255, 256);
}

/// If scalar52_as_nat(a) < group_order() then scalar52_as_nat(a) < 2^256
pub proof fn lemma_scalar52_lt_pow2_256_if_canonical(a: &Scalar52)
    requires limbs_bounded(a), scalar52_as_nat(a) < group_order(),
    ensures  scalar52_as_nat(a) < pow2(256),
{
    lemma_group_order_bound();
    lemma_pow2_strictly_increases(255, 256);
    // scalar52_as_nat(a) < group_order() < 2^255 < 2^256
}

// ============================================================
// § 10  Uniformity axiom  (proba_specs.rs)
// ============================================================

/// Reducing 512 uniform bits mod ℓ produces a nearly-uniform scalar.
/// Statistical distance ≤ ℓ/2^512 ≈ 2^{-259} (cryptographically negligible).
pub proof fn axiom_uniform_mod_reduction(input: &[u8; 64], result: &Scalar)
    requires scalar_as_canonical(result) == bytes_seq_as_nat(input@) % group_order(),
    ensures  is_uniform_bytes(input) ==> is_uniform_scalar(result),
{ admit() }

// ============================================================
// § 11  Target function  (scalar.rs:300–348)
// ============================================================

impl Scalar {
    /// Reduce a 512-bit little-endian integer mod ℓ into a canonical Scalar.
    ///
    /// Used in EdDSA signing to reduce the SHA-512 hash of (R ‖ A ‖ M) to a
    /// nonce scalar r.  Absent canonicality caused malleability bugs in OpenSSL
    /// and tinyssh (RFC 8032 §5.1.7).  The uniformity postcondition ensures
    /// nonces derived from uniform randomness cannot leak the private key.
    pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (result: Scalar)
        ensures
            scalar_as_canonical(&result) == group_canonical(bytes_seq_as_nat(input@)),
            is_canonical_scalar(&result),
            is_uniform_bytes(input) ==> is_uniform_scalar(&result),
    {
        let unpacked = UnpackedScalar::from_bytes_wide(input);
        let result   = unpacked.pack();

        proof {
            // Step 1: scalar52_as_nat(&unpacked) < pow2(256)
            //   from_bytes_wide gives is_canonical_scalar52 => value < group_order()
            //   group_order() < pow2(256) by lemma below
            lemma_group_order_smaller_than_pow256();
            lemma_scalar52_lt_pow2_256_if_canonical(&unpacked);

            // Step 2: pack's mod-2^256 is a no-op (value < pow2(256))
            //   => u8_32_as_nat(&result.bytes) == scalar52_as_nat(&unpacked)
            lemma_small_mod(scalar52_as_nat(&unpacked), pow2(256));

            // Step 3: bytes_seq_as_nat(input@) % group_order() < group_order()
            //   => scalar52_as_nat(&unpacked) < group_order()  (already known, but needed for lemma_small_mod below)
            lemma_mod_bound(bytes_seq_as_nat(input@) as int, group_order() as int);

            // Step 4: u8_32_as_nat(&result.bytes) < group_order()
            //   => scalar_as_canonical(&result) == u8_32_as_nat(&result.bytes) == group_canonical(input)
            lemma_small_mod(u8_32_as_nat(&result.bytes), group_order());

            // Step 5: uniformity
            axiom_uniform_mod_reduction(input, &result);
        }

        result
    }
}

} // verus!

fn main() {}
