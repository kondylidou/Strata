/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Benchmark B5 — `MontgomeryPoint::mul_clamped` (VARIANT: minimal)

Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
Pinned commit: 3f3443e
File:   curve25519-dalek/src/montgomery.rs (`mul_clamped`, `mul_bits_be`, the
        `Mul` operator); scalar.rs (`clamp_integer`, the `Scalar` type); specs
        from specs/{montgomery,scalar,field,field_u64,core}_specs.rs;
        backend/serial/u64/constants.rs (`MONTGOMERY_A`).

Core scalar multiplication of X25519 — the Diffie-Hellman function used in
TLS 1.3, Signal, WireGuard and SSH. A `MontgomeryPoint` holds the affine
u-coordinate u₀(P) of a point P on the Montgomery form of Curve25519.
`mul_clamped` *clamps* the 32 input bytes — clear the low 3 bits, clear bit 255,
set bit 254 — to a scalar n ∈ 2^254 + 8·{0, …, 2^251 − 1}, then returns the
u-coordinate of [n]P. Clamping is what every Curve25519 protocol actually uses:
it forces the scalar into the prime-order coset and pins its bit-length. The
function builds an (intentionally unreduced) `Scalar` from the clamped bytes and
delegates to the `*` operator, which drives the Montgomery ladder `mul_bits_be`
(Costello-Smith 2017, Algorithm 8). The verified body is `Impl__14_mul_clamped`:
it chains `clamp_integer`'s `ensures` (`clamped == spec_clamp_integer(bytes)`)
with the `*` operator's `ensures` to discharge the encoding equality
`montgomery_point_as_nat(result) == u_coordinate(montgomery_scalar_mul(P, n))`,
where n is the *clamped* integer value (NOT reduced mod the group order).

Translation notes:
  - `[u8; 32]` / `[u64; 5]` fixed arrays become type synonyms over `Sequence`
    (`montgomeryPoint`, `scalar`, `fieldElement51`) with the length invariant on
    the constructors' `requires`.
  - `enum MontgomeryAffine { Infinity, Finite { u, v } }` becomes the
    two-constructor datatype `montgomeryAffine`; the `match (P, Q)` in
    `montgomery_add` builds a `Tuple2` pair and projects with `Tuple2.._0/_1`.
  - A tuple's `IsVariant` test (the `(P, Q)` match arms) is a parser artifact —
    a tuple is single-constructor, so its variant test lowers to the constant
    `true` (hence the `true && …ismontgomeryAffine_Infinity…` guards in
    `montgomery_add`). B5 is the only Dalek target with a tuple variant test.
  - `field_sqrt` is `choose`-defined (`choose|y| y < p && field_mul(y,y) ==
    field_canonical(a)`); it lowers to Boole's native choose-function
    declaration `function … := choose y :: …` (Strata #1365).
  - `<&MontgomeryPoint as Mul<&Scalar>>::Output` — a trait associated-type
    projection — resolves to the concrete impl return type `montgomeryPoint`
    (Verus already types the `Mul` impl's `mul` as returning `MontgomeryPoint`);
    the translator pairs each abstract trait-method decl with its impl and
    rewrites the projection at the single type-lowering chokepoint.
  - The `&self * &s` operator call dispatches to the resolved impl `Impl__13_mul`
    (Verus records the resolution in VLIR's `resolved_method = impl&%13::mul`;
    the translator routes the call there rather than to the abstract trait
    method `Ops_Arith_Mul_mul`), so the call site sees the impl's real Montgomery
    `ensures` and `mul_clamped`'s correctness postcondition closes against it.
  - Verus spec-mode `+ − *` is mathematical `int`/`nat` (never wraps): the field
    and byte-decomposition specs emit `nat.add`/`nat.sub`/`nat.mul` (and `int`
    with `as_int` on bv leaves), not wrapping `bv`. `clamp_integer`'s
    `by (bit_vector)` masks keep their `[bitvector_query]` proofs.

Trust boundary (3 `assume false` stubs + 1 uninterpreted spec fn):
  - `Impl__11_mul_bits_be` — the ~400-line Montgomery ladder (constant-time
    differential add-and-double with a loop invariant and the Costello-Smith
    differential-addition correctness axioms). `requires`/`ensures` reproduced
    verbatim, body `assume(false)`, postcondition trusted as an axiom — far too
    heavy to reproduce at "reasonable scale", exactly the case the B5 spec flags.
  - `Impl__13_mul` — the `&MontgomeryPoint * &Scalar` operator `mul_clamped`
    dispatches to (whose real body reverses the scalar into a big-endian bit
    slice and calls the ladder). Stubbed `assume(false)`, but its `ensures` is
    the real Montgomery postcondition, which `mul_clamped`'s proof consumes.
    (The abstract trait global `Ops_Arith_Mul_mul` is still emitted but
    unreferenced — the callee-stubbing pattern B2 uses for `from_bytes_wide`.)
  - `spec_mod_inverse` — left uninterpreted (`field_inv` names it, but no
    reachable proof constrains an inverse's value).
  The `clamp_integer` procedure is kept faithful and carries a real proof (a
  handful of `by (bit_vector)` facts); the three `clone` procedures are identity.
  Every field/Montgomery spec function (`field_*`, `montgomery_*`, `is_square`,
  `field_sqrt`, …) is reproduced verbatim and faithful, but *inert*: because the
  `*` operator is stubbed, the verifier never unfolds the curve arithmetic.

Operator dispatch (resolved): the `&self * &s` call dispatches to the resolved
impl `Impl__13_mul` (VLIR `resolved_method = impl&%13::mul`), so `mul_clamped`'s
correctness postcondition `Impl__14_mul_clamped_ensures` now *verifies* — it
closes against the impl's real Montgomery `ensures`
(`montgomery_point_as_nat(result) == u_coordinate(montgomery_scalar_mul(…,
scalar_as_nat(scalar)))`). Previously the call lowered to the *abstract*
`Ops_Arith_Mul_mul`, whose `obeys_mul_spec ==> ret == mul_spec` ensures is
vacuous (`obeys_mul_spec()` is `false`), and the postcondition could not close.
The abstract operator procedure is still emitted but unreferenced; its own
generic ensures VC is the lone encoding error below (an `Unimplemented encoding
for type var` over `Self_`/`Rhs`), removable by pruning the orphaned global.

Results (cvc5, 3s solver cap): 239 of 329 VCs pass, 89 timeouts, 1 encoding
error. The headline is `Impl__14_mul_clamped_ensures` — the correctness
postcondition — now passing (it could not close before the dispatch fix),
alongside `clamp_integer`'s bit-vector proof and the byte/scalar bookkeeping.
The lone encoding error is the orphaned abstract `Ops_Arith_Mul_mul`'s generic
ensures (`Unimplemented encoding for type var`), no longer on the correctness
path. The 89 timeouts are the definition-level guard class shared with B1–B4
(the 32-term `u8_32_as_nat` `Sequence.select` bounds, the `nat.sub`/`nat.mod`
guards in `p` / `field_canonical` / `field_sub` / `field_neg` and their
call-site echoes, plus the new `Impl__13_mul` precondition check) — all
cap-sensitive, not faithfulness gaps.

Status: this file uses the `as_int` cast syntax from pr/casts-boole, the native
`command_choosefndef` (#1365), the `toCoreMonoType` type-argument-order fix, and
the `resolved_method` operator dispatch that routes the `*` call to
`Impl__13_mul`. The un-merged branch has none of these, so the `#exit` below
keeps the file inert until they land.
-/

#exit

open Strata

set_option maxRecDepth 100000

private def b5_minimal_program : StrataDDM.Program :=
#strata
program Boole;

 type nat;
 function nat.toInt (n : nat) : int;
 function nat.fromIntAux (x : int) : nat;
 function nat.fromInt (x : int) : nat requires 0 <= x;
   {
  nat.fromIntAux(x)
}
 axiom [nat_nonneg]: forall n : nat :: 0 <= nat.toInt(n);
 axiom [nat_fromInt_toInt]: forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x;
 axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;
 function nat.add (a : nat, b : nat) : nat {
  nat.fromInt(nat.toInt(a) + nat.toInt(b))
}
 function nat.sub (a : nat, b : nat) : nat requires nat.toInt(b) <= nat.toInt(a);
   {
  nat.fromInt(nat.toInt(a) - nat.toInt(b))
}
 function nat.mul (a : nat, b : nat) : nat {
  nat.fromInt(nat.toInt(a) * nat.toInt(b))
}
 function nat.div (a : nat, b : nat) : nat requires nat.toInt(b) != 0;
   {
  nat.fromInt(nat.toInt(a) div nat.toInt(b))
}
 function nat.mod (a : nat, b : nat) : nat requires nat.toInt(b) != 0;
   {
  nat.fromInt(nat.toInt(a) mod nat.toInt(b))
}
 function nat.lt (a : nat, b : nat) : bool {
  nat.toInt(a) < nat.toInt(b)
}
 function nat.le (a : nat, b : nat) : bool {
  nat.toInt(a) <= nat.toInt(b)
}
 function nat.gt (a : nat, b : nat) : bool {
  nat.toInt(a) > nat.toInt(b)
}
 function nat.ge (a : nat, b : nat) : bool {
  nat.toInt(a) >= nat.toInt(b)
}
 datatype Tuple2 (T0 : Type, T1 : Type) {
  Tuple2_ctor_2(_0 : T0, _1 : T1)
};
 type fieldElement51 := Sequence bv64;
 function fieldElement51_ctor (limbs : Sequence bv64) : Sequence bv64 requires Sequence.length(limbs) == 5;
   {
  limbs
}
 function fieldElement51..limbs (limbs : Sequence bv64) : Sequence bv64 {
  limbs
}
 type scalar := Sequence bv8;
 function scalar_ctor (bytes : Sequence bv8) : Sequence bv8 requires Sequence.length(bytes) == 32;
   {
  bytes
}
 function scalar..bytes (bytes : Sequence bv8) : Sequence bv8 {
  bytes
}
 datatype projectivePoint {
  projectivePoint_ctor(U : fieldElement51, W : fieldElement51)
};
 datatype montgomeryAffine {
  montgomeryAffine_Infinity(),
  montgomeryAffine_Finite(montgomeryAffine_Finite_u : nat, montgomeryAffine_Finite_v : nat)
};
 type montgomeryPoint := Sequence bv8;
 function montgomeryPoint_ctor (_0 : Sequence bv8) : Sequence bv8 requires Sequence.length(_0) == 32;
   {
  _0
}
 function montgomeryPoint.._0 (_0 : Sequence bv8) : Sequence bv8 {
  _0
}
 function Std_specs_Ops_mul_req<Self_, Rhs> (self : Self_, rhs : Rhs) : bool;
 function Std_specs_Ops_obeys_mul_spec () : bool;
 function Std_specs_Ops_mul_spec<Self_, Rhs> (self : Self_, rhs : Rhs) : montgomeryPoint;
 procedure Ops_Arith_Mul_mul<Self_, Rhs> (self : Self_, rhs : Rhs) returns (ret : montgomeryPoint)
spec {
  requires Std_specs_Ops_mul_req(self, rhs);
  ensures Std_specs_Ops_obeys_mul_spec ==> ret == Std_specs_Ops_mul_spec(self, rhs);
  } {
  assume false;
};
 function spec_mod_inverse (a : nat, m : nat) : nat;
 function Arithmetic_Power2_pow2 (e : nat) : nat;
 function p () : nat {
  nat.sub(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19))
}
 function field_canonical (n : nat) : nat {
  nat.mod(n, p)
}
 function u64_5_as_nat (limbs : Sequence bv64) : nat {
  nat.add(nat.add(nat.add(nat.add(nat.fromInt(as_uint(Sequence.select(limbs, 0))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(51)), nat.fromInt(as_uint(Sequence.select(limbs, 1))))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(102)), nat.fromInt(as_uint(Sequence.select(limbs, 2))))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(153)), nat.fromInt(as_uint(Sequence.select(limbs, 3))))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(204)), nat.fromInt(as_uint(Sequence.select(limbs, 4)))))
}
 function u64_5_as_field_canonical (limbs : Sequence bv64) : nat {
  field_canonical(u64_5_as_nat(limbs))
}
 function u8_32_as_nat (bytes : Sequence bv8) : nat {
  nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 0))), Arithmetic_Power2_pow2(nat.fromInt(0))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 1))), Arithmetic_Power2_pow2(nat.fromInt(8)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 2))), Arithmetic_Power2_pow2(nat.fromInt(16)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 3))), Arithmetic_Power2_pow2(nat.fromInt(24)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 4))), Arithmetic_Power2_pow2(nat.fromInt(32)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 5))), Arithmetic_Power2_pow2(nat.fromInt(40)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 6))), Arithmetic_Power2_pow2(nat.fromInt(48)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 7))), Arithmetic_Power2_pow2(nat.fromInt(56)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 8))), Arithmetic_Power2_pow2(nat.fromInt(64)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 9))), Arithmetic_Power2_pow2(nat.fromInt(72)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 10))), Arithmetic_Power2_pow2(nat.fromInt(80)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 11))), Arithmetic_Power2_pow2(nat.fromInt(88)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 12))), Arithmetic_Power2_pow2(nat.fromInt(96)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 13))), Arithmetic_Power2_pow2(nat.fromInt(104)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 14))), Arithmetic_Power2_pow2(nat.fromInt(112)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 15))), Arithmetic_Power2_pow2(nat.fromInt(120)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 16))), Arithmetic_Power2_pow2(nat.fromInt(128)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 17))), Arithmetic_Power2_pow2(nat.fromInt(136)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 18))), Arithmetic_Power2_pow2(nat.fromInt(144)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 19))), Arithmetic_Power2_pow2(nat.fromInt(152)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 20))), Arithmetic_Power2_pow2(nat.fromInt(160)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 21))), Arithmetic_Power2_pow2(nat.fromInt(168)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 22))), Arithmetic_Power2_pow2(nat.fromInt(176)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 23))), Arithmetic_Power2_pow2(nat.fromInt(184)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 24))), Arithmetic_Power2_pow2(nat.fromInt(192)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 25))), Arithmetic_Power2_pow2(nat.fromInt(200)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 26))), Arithmetic_Power2_pow2(nat.fromInt(208)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 27))), Arithmetic_Power2_pow2(nat.fromInt(216)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 28))), Arithmetic_Power2_pow2(nat.fromInt(224)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 29))), Arithmetic_Power2_pow2(nat.fromInt(232)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 30))), Arithmetic_Power2_pow2(nat.fromInt(240)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 31))), Arithmetic_Power2_pow2(nat.fromInt(248))))
}
 rec function bits_be_as_nat (bits : Sequence bool, len : int) : nat
decreases len
  {
  if len <= 0 then nat.fromInt(0) else nat.add(if Sequence.select(bits, len - 1) then nat.fromInt(1) else nat.fromInt(0), nat.mul(nat.fromInt(2), bits_be_as_nat(bits, len - 1)))
};
 function fe51_as_nat (fe : fieldElement51) : nat {
  u64_5_as_nat(fieldElement51..limbs(fe))
}
 function fe51_as_canonical_nat (fe : fieldElement51) : nat {
  u64_5_as_field_canonical(fieldElement51..limbs(fe))
}
 function field_element_from_bytes (bytes : Sequence bv8) : nat {
  field_canonical(nat.mod(u8_32_as_nat(bytes), Arithmetic_Power2_pow2(nat.fromInt(255))))
}
 function field_add (a : nat, b : nat) : nat {
  field_canonical(nat.add(a, b))
}
 function field_sub (a : nat, b : nat) : nat {
  field_canonical(nat.sub(nat.add(field_canonical(a), p), field_canonical(b)))
}
 function field_mul (a : nat, b : nat) : nat {
  field_canonical(nat.mul(a, b))
}
 function field_neg (a : nat) : nat {
  field_canonical(nat.sub(p, field_canonical(a)))
}
 function field_square (a : nat) : nat {
  field_canonical(nat.mul(a, a))
}
 function field_inv (a : nat) : nat {
  if nat.toInt(nat.mod(a, p)) == 0 then nat.fromInt(0) else spec_mod_inverse(a, p)
}
 function is_square (a : nat) : bool {
  ∃ y : nat :: nat.toInt(field_mul(y, y)) == nat.toInt(field_canonical(a))
}
 function field_sqrt (a : nat) : nat :=
  choose y : nat :: nat.lt(y, p) && nat.toInt(field_mul(y, y)) == nat.toInt(field_canonical(a));
 function mONTGOMERY_A () : fieldElement51 {
  fieldElement51_ctor(Sequence.of_bv64[bv{64}(486662), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)])
}
 function montgomery_point_as_nat (point : montgomeryPoint) : nat {
  field_element_from_bytes(montgomeryPoint.._0(point))
}
 function montgomery_rhs (u : nat) : nat {
  field_add(field_add(field_mul(field_mul(u, u), u), field_mul(fe51_as_canonical_nat(mONTGOMERY_A), field_mul(u, u))), u)
}
 function is_valid_u_coordinate (u : nat) : bool {
  is_square(montgomery_rhs(u))
}
 function is_valid_montgomery_point (point : montgomeryPoint) : bool {
  is_valid_u_coordinate(montgomery_point_as_nat(point))
}
 function canonical_sqrt (r : nat) : nat {
  if nat.toInt(nat.mod(field_sqrt(r), nat.fromInt(2))) == 0 then field_sqrt(r) else field_neg(field_sqrt(r))
}
 function canonical_montgomery_lift (u : nat) : montgomeryAffine {
  montgomeryAffine_Finite(nat.mod(u, p), canonical_sqrt(montgomery_rhs(u)))
}
 function montgomery_neg (P : montgomeryAffine) : montgomeryAffine {
  if montgomeryAffine..ismontgomeryAffine_Infinity(P) then montgomeryAffine_Infinity else montgomeryAffine_Finite(montgomeryAffine..montgomeryAffine_Finite_u(P), field_neg(montgomeryAffine..montgomeryAffine_Finite_v(P)))
}
 function montgomery_add (P : montgomeryAffine, Q : montgomeryAffine) : montgomeryAffine {
  if true && montgomeryAffine..ismontgomeryAffine_Infinity(Tuple2.._0(Tuple2_ctor_2(P, Q))) then Q else if true && montgomeryAffine..ismontgomeryAffine_Infinity(Tuple2.._1(Tuple2_ctor_2(P, Q))) then P else if nat.toInt(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q)))) == nat.toInt(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._1(Tuple2_ctor_2(P, Q)))) && nat.toInt(field_add(montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q))), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._1(Tuple2_ctor_2(P, Q))))) == 0 then montgomeryAffine_Infinity else if nat.toInt(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q)))) == nat.toInt(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._1(Tuple2_ctor_2(P, Q)))) && nat.toInt(montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q)))) == nat.toInt(montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._1(Tuple2_ctor_2(P, Q)))) then montgomeryAffine_Finite(field_sub(field_sub(field_square(field_mul(field_add(field_add(field_mul(nat.fromInt(3), field_square(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))), field_mul(field_mul(nat.fromInt(2), fe51_as_canonical_nat(mONTGOMERY_A)), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))), nat.fromInt(1)), field_inv(field_mul(nat.fromInt(2), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q))))))), fe51_as_canonical_nat(mONTGOMERY_A)), field_mul(nat.fromInt(2), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))), field_sub(field_mul(field_mul(field_add(field_add(field_mul(nat.fromInt(3), field_square(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))), field_mul(field_mul(nat.fromInt(2), fe51_as_canonical_nat(mONTGOMERY_A)), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))), nat.fromInt(1)), field_inv(field_mul(nat.fromInt(2), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q)))))), field_sub(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))), field_sub(field_sub(field_square(field_mul(field_add(field_add(field_mul(nat.fromInt(3), field_square(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))), field_mul(field_mul(nat.fromInt(2), fe51_as_canonical_nat(mONTGOMERY_A)), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))), nat.fromInt(1)), field_inv(field_mul(nat.fromInt(2), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q))))))), fe51_as_canonical_nat(mONTGOMERY_A)), field_mul(nat.fromInt(2), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))))), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q))))) else montgomeryAffine_Finite(field_sub(field_sub(field_sub(field_square(field_mul(field_sub(montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._1(Tuple2_ctor_2(P, Q))), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q)))), field_inv(field_sub(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._1(Tuple2_ctor_2(P, Q))), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))))), fe51_as_canonical_nat(mONTGOMERY_A)), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q)))), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._1(Tuple2_ctor_2(P, Q)))), field_sub(field_mul(field_mul(field_sub(montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._1(Tuple2_ctor_2(P, Q))), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q)))), field_inv(field_sub(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._1(Tuple2_ctor_2(P, Q))), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q)))))), field_sub(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))), field_sub(field_sub(field_sub(field_square(field_mul(field_sub(montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._1(Tuple2_ctor_2(P, Q))), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q)))), field_inv(field_sub(montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._1(Tuple2_ctor_2(P, Q))), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q))))))), fe51_as_canonical_nat(mONTGOMERY_A)), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._0(Tuple2_ctor_2(P, Q)))), montgomeryAffine..montgomeryAffine_Finite_u(Tuple2.._1(Tuple2_ctor_2(P, Q)))))), montgomeryAffine..montgomeryAffine_Finite_v(Tuple2.._0(Tuple2_ctor_2(P, Q)))))
}
 function u_coordinate (point : montgomeryAffine) : nat {
  if montgomeryAffine..ismontgomeryAffine_Infinity(point) then nat.fromInt(0) else montgomeryAffine..montgomeryAffine_Finite_u(point)
}
 rec function montgomery_scalar_mul (P : montgomeryAffine, n : nat) : montgomeryAffine
decreases nat.toInt(n)
  {
  if nat.toInt(n) == 0 then montgomeryAffine_Infinity else montgomery_add(P, montgomery_scalar_mul(P, nat.sub(n, nat.fromInt(1))))
};
 function scalar_as_nat (s : scalar) : nat {
  u8_32_as_nat(scalar..bytes(s))
}
 function is_clamped_integer (bytes : Sequence bv8) : bool {
  Sequence.select(bytes, 0) & bv{8}(7) == bv{8}(0) && Sequence.select(bytes, 31) & bv{8}(128) == bv{8}(0) && Sequence.select(bytes, 31) & bv{8}(64) == bv{8}(64) && Sequence.select(bytes, 31) <= bv{8}(127)
}
 function spec_clamp_integer (bytes : Sequence bv8) : Sequence bv8 {
  Sequence.of_bv8[Sequence.select(bytes, 0) & bv{8}(248), Sequence.select(bytes, 1), Sequence.select(bytes, 2), Sequence.select(bytes, 3), Sequence.select(bytes, 4), Sequence.select(bytes, 5), Sequence.select(bytes, 6), Sequence.select(bytes, 7), Sequence.select(bytes, 8), Sequence.select(bytes, 9), Sequence.select(bytes, 10), Sequence.select(bytes, 11), Sequence.select(bytes, 12), Sequence.select(bytes, 13), Sequence.select(bytes, 14), Sequence.select(bytes, 15), Sequence.select(bytes, 16), Sequence.select(bytes, 17), Sequence.select(bytes, 18), Sequence.select(bytes, 19), Sequence.select(bytes, 20), Sequence.select(bytes, 21), Sequence.select(bytes, 22), Sequence.select(bytes, 23), Sequence.select(bytes, 24), Sequence.select(bytes, 25), Sequence.select(bytes, 26), Sequence.select(bytes, 27), Sequence.select(bytes, 28), Sequence.select(bytes, 29), Sequence.select(bytes, 30), Sequence.select(bytes, 31) & bv{8}(127) | bv{8}(64)]
}
 procedure Impl__2_clone (self : fieldElement51) returns (_pct_return : fieldElement51)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__2_clone;
};
 procedure Impl__5_clone (self : montgomeryPoint) returns (_pct_return : montgomeryPoint)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__5_clone;
};
 procedure Impl__10_clone (self : scalar) returns (_pct_return : scalar)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__10_clone;
};
 procedure Impl__13_mul (self : montgomeryPoint, scalar : scalar) returns (result : montgomeryPoint)
spec {
  requires Std_specs_Ops_mul_req(self, scalar);
  ensures Std_specs_Ops_obeys_mul_spec ==> result == Std_specs_Ops_mul_spec(self, scalar);
  ensures nat.toInt(montgomery_point_as_nat(result)) == nat.toInt(u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(montgomery_point_as_nat(self)), scalar_as_nat(scalar))));
  } {
  assume false;
  result := montgomeryPoint_ctor(Sequence.of_bv8[bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0)]);
  exit Impl__13_mul;
};
 procedure clamp_integer (bytes : Sequence bv8) returns (result : (Sequence bv8))
spec {
  ensures is_clamped_integer(result);
  ensures result == spec_clamp_integer(bytes);
  ensures ∀ i : int :: 1 <= i && i < 31 ==> Sequence.select(result, i) == Sequence.select(bytes, i);
  ensures Sequence.select(result, 0) & bv{8}(248) == Sequence.select(bytes, 0) & bv{8}(248);
  ensures Sequence.select(result, 31) & bv{8}(63) == Sequence.select(bytes, 31) & bv{8}(63);
  ensures Sequence.length(result) == 32;
  } {
  var r0 : bv8;
  var r31 : bv8;
  var b0 : bv8;
  var b31 : bv8;
  assume Sequence.length(bytes) == 32;
  result := bytes;
  result := Sequence.update(result, 0, Sequence.select(result, 0) & bv{8}(248));
  result := Sequence.update(result, 31, Sequence.select(result, 31) & bv{8}(127));
  result := Sequence.update(result, 31, Sequence.select(result, 31) | bv{8}(64));
  r0 := Sequence.select(result, 0);
  r31 := Sequence.select(result, 31);
  b0 := Sequence.select(bytes, 0);
  b31 := Sequence.select(bytes, 31);
  assert r0 == b0 & bv{8}(248);
  assert [bitvector_query]: r0 == b0 & bv{8}(248) ==> r0 & bv{8}(7) == bv{8}(0);
  assert r31 == b31 & bv{8}(127) | bv{8}(64);
  assert [bitvector_query]: r31 == b31 & bv{8}(127) | bv{8}(64) ==> r31 & bv{8}(128) == bv{8}(0);
  assert r31 == b31 & bv{8}(127) | bv{8}(64);
  assert [bitvector_query]: r31 == b31 & bv{8}(127) | bv{8}(64) ==> r31 & bv{8}(64) == bv{8}(64);
  assert r31 == b31 & bv{8}(127) | bv{8}(64);
  assert [bitvector_query]: r31 == b31 & bv{8}(127) | bv{8}(64) ==> r31 <= bv{8}(127);
  assert r0 == b0 & bv{8}(248);
  assert [bitvector_query]: r0 == b0 & bv{8}(248) ==> r0 & bv{8}(248) == b0 & bv{8}(248);
  assert r31 == b31 & bv{8}(127) | bv{8}(64);
  assert [bitvector_query]: r31 == b31 & bv{8}(127) | bv{8}(64) ==> r31 & bv{8}(63) == b31 & bv{8}(63);
  result := result;
  exit clamp_integer;
};
 procedure Impl__11_mul_bits_be (self : montgomeryPoint, bits : Sequence bool) returns (result : montgomeryPoint)
spec {
  requires Sequence.length(bits) <= 255;
  requires is_valid_montgomery_point(self);
  ensures nat.toInt(montgomery_point_as_nat(result)) == nat.toInt(u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(montgomery_point_as_nat(self)), bits_be_as_nat(bits, Sequence.length(bits)))));
  } {
  assume false;
  result := montgomeryPoint_ctor(Sequence.of_bv8[bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0)]);
  exit Impl__11_mul_bits_be;
};
 procedure Impl__14_mul_clamped (self : montgomeryPoint, bytes : Sequence bv8) returns (result : montgomeryPoint)
spec {
  requires is_valid_montgomery_point(self);
  ensures nat.toInt(montgomery_point_as_nat(result)) == nat.toInt(u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(montgomery_point_as_nat(self)), u8_32_as_nat(spec_clamp_integer(bytes)))));
  } {
  var tmp1 : montgomeryPoint;
  var clamped : (Sequence bv8);
  var s : scalar;
  assume Sequence.length(bytes) == 32;
  call clamped := clamp_integer(bytes);
  
  s := scalar_ctor(clamped);
  call tmp1 := Impl__13_mul(self, s);
  
  result := tmp1;
  assert clamped == spec_clamp_integer(bytes);
  assume clamped == spec_clamp_integer(bytes);
  assert nat.toInt(scalar_as_nat(s)) == nat.toInt(u8_32_as_nat(spec_clamp_integer(bytes)));
  assume nat.toInt(scalar_as_nat(s)) == nat.toInt(u8_32_as_nat(spec_clamp_integer(bytes)));
  assert nat.toInt(montgomery_point_as_nat(result)) == nat.toInt(u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(montgomery_point_as_nat(self)), u8_32_as_nat(spec_clamp_integer(bytes)))));
  assume nat.toInt(montgomery_point_as_nat(result)) == nat.toInt(u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(montgomery_point_as_nat(self)), u8_32_as_nat(spec_clamp_integer(bytes)))));
  result := result;
  exit Impl__14_mul_clamped;
};
#end

-- cvc5 via Strata.Boole.verify (3s cap): 239 of 329 VCs pass, 89 timeouts; mul_clamped postcondition verifies
-- #eval Strata.Boole.verify "cvc5" b5_minimal_program (options := .quiet)
