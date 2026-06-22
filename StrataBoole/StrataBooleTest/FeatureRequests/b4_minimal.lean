/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Benchmark B4 — `RistrettoPoint::compress` (VARIANT: minimal)

Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
File:   curve25519-dalek/src/ristretto.rs (`compress`); specs from
        specs/ristretto_specs.rs, specs/field_specs.rs, specs/edwards_specs.rs

Ristretto255 point compression: the canonical 32-byte encoding of a
prime-order group element built over Edwards Curve25519. From the underlying
point (X:Y:Z:T) it computes u1 = (Z+Y)(Z−Y), u2 = X·Y, invsqrt = 1/√(u1·u2²),
selects the unique coset representative (a sign-normalising rotation by the
constant √(−1) and a final |·| on s), and serialises s to 32 little-endian
bytes. This is the encoding Bulletproofs and Pedersen commitments put on the
wire. The verified body is `Impl__14_compress`: the field-operation pipeline
threaded through the `ristretto_compress_extended` spec to discharge the
encoding equality `result.0 == spec_ristretto_compress(*self)`.

Translation notes:
  - `[u64; 5]` / `[u8; 32]` fixed arrays become type synonyms over `Sequence`
    with the length invariant on the constructors' `requires`.
  - The 4-tuple `(nat, nat, nat, nat)` of `edwards_point_as_nat` becomes
    nested binary pairs `Tuple2 nat (Tuple2 nat (Tuple2 nat nat))`, projected
    with `Tuple2.._0` / `Tuple2.._1` chains.
  - `Option<EdwardsPoint>` is the two-constructor datatype `Option_option`;
    `subtle::Choice` is a single-field datatype with an uninterpreted
    `choice_is_true` observer.
  - `u8_32_from_nat` is `choose`-defined in the source
    (`choose|b| u8_32_as_nat(&b) == n % pow2(256)`); it lowers to Boole's
    native choose-function declaration `function … := choose b :: …`
    (Strata #1365).
  - Verus spec-mode `+ − *` is mathematical `int` (never wraps), so e.g.
    `fe1.limbs[i] + fe2.limbs[i] < bound` emits int arithmetic
    (`… as_int + … as_int < bound as_int`) — faithful to the unbounded sum,
    not a wrapping `bv +`. The `by (bit_vector)` limb-bound lemmas keep their
    `[bitvector_query]` proofs (which discharge cleanly over the int form).

Trust boundary (17 `assume false` stubs):
  - The field-operation external bodies `fe_add` / `fe_sub` / `fe_mul` /
    `square` / `invsqrt` / `is_negative` / `as_bytes` and the
    `conditional_assign` / `conditional_negate` wrappers — `requires`/
    `ensures` reproduced verbatim from dalek-lite (their correctness is the
    subject of benchmark B1 and siblings).
  - The admitted algebra lemmas `lemma_square_matches_field_square`,
    `lemma_one_field_element_value`, `lemma_invsqrt_matches_spec`,
    `lemma_canonical_bytes_equal` (admitted in dalek-lite as well).
  - vstd arithmetic lemmas `lemma_small_mod`, `lemma_mod_bound`,
    `lemma2_to64`, `lemma_pow2_strictly_increases`.
  The structural lemmas (limb-bound weakening, sum-of-limbs bound, constant
  limb bounds, 2^255 > 19) carry real proof bodies.

Results: cvc5 discharges 519 of 655 VCs, 0 failures. The compress proof chain
— the spec-equality cascade, including the choose-defined `u8_32_from_nat` and
the `by (bit_vector)` limb bounds — passes. The 136 timeouts are the
definition-level guard class shared with B1–B3 (the 32-term `u8_32_as_nat`
`Sequence.select` bounds, the let-expanded `nat_invsqrt` nat.sub/mod/div
guards, `p`/`field_canonical` guards, and their call-site echoes), amplified
by the faithful int-domain limb arithmetic.

Status: this file uses the `as_int` cast syntax from pr/casts-boole, the
native `command_choosefndef` (#1365), and the `toCoreMonoType`
type-argument-order fix. The un-merged branch has none of these, so the
`#exit` below keeps the file inert until they land.
-/

#exit

open Strata

set_option maxRecDepth 100000

private def b4_minimal_program : StrataDDM.Program :=
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
 datatype edwardsPoint {
  edwardsPoint_ctor(X : fieldElement51, Y : fieldElement51, Z : fieldElement51, T : fieldElement51)
};
 datatype ristrettoPoint {
  ristrettoPoint_ctor(_0 : edwardsPoint)
};
 type compressedRistretto := Sequence bv8;
 function compressedRistretto_ctor (_0 : Sequence bv8) : Sequence bv8 requires Sequence.length(_0) == 32;
   {
  _0
}
 function compressedRistretto.._0 (_0 : Sequence bv8) : Sequence bv8 {
  _0
}
 datatype choice {
  choice_ctor(_0 : bv8)
};
 function Arithmetic_Power_pow (b : int, e : nat) : int;
 function Arithmetic_Power2_pow2 (e : nat) : nat;
 function choice_is_true (c : choice) : bool;
 function is_on_edwards_curve_projective (x : nat, y : nat, z : nat) : bool;
 function sum_of_limbs_bounded (fe1 : fieldElement51, fe2 : fieldElement51, bound : bv64) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> as_uint(Sequence.select(fieldElement51..limbs(fe1), i)) + as_uint(Sequence.select(fieldElement51..limbs(fe2), i)) < as_uint(bound)
}
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
 function fe51_as_canonical_nat (fe : fieldElement51) : nat {
  u64_5_as_field_canonical(fieldElement51..limbs(fe))
}
 function field_add (a : nat, b : nat) : nat {
  field_canonical(nat.add(a, b))
}
 function u64_5_bounded (limbs : Sequence bv64, bit_limit : bv64) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(limbs, i) < bv{64}(1) << bit_limit
}
 function fe51_limbs_bounded (fe : fieldElement51, bit_limit : bv64) : bool {
  u64_5_bounded(fieldElement51..limbs(fe), bit_limit)
}
 procedure Impl__13_fe_add (self : fieldElement51, rhs : fieldElement51) returns (output : fieldElement51)
spec {
  requires sum_of_limbs_bounded(self, rhs, bv{64}(18446744073709551615));
  ensures nat.toInt(fe51_as_canonical_nat(output)) == nat.toInt(field_add(fe51_as_canonical_nat(self), fe51_as_canonical_nat(rhs)));
  ensures fe51_limbs_bounded(self, bv{64}(51)) && fe51_limbs_bounded(rhs, bv{64}(51)) ==> fe51_limbs_bounded(output, bv{64}(52));
  ensures fe51_limbs_bounded(self, bv{64}(52)) && fe51_limbs_bounded(rhs, bv{64}(52)) ==> fe51_limbs_bounded(output, bv{64}(53));
  } {
  assume false;
};
 function field_sub (a : nat, b : nat) : nat {
  field_canonical(nat.sub(nat.add(field_canonical(a), p), field_canonical(b)))
}
 procedure Impl__13_fe_sub (self : fieldElement51, rhs : fieldElement51) returns (output : fieldElement51)
spec {
  requires fe51_limbs_bounded(self, bv{64}(54));
  requires fe51_limbs_bounded(rhs, bv{64}(54));
  ensures nat.toInt(fe51_as_canonical_nat(output)) == nat.toInt(field_sub(fe51_as_canonical_nat(self), fe51_as_canonical_nat(rhs)));
  ensures fe51_limbs_bounded(output, bv{64}(52));
  ensures fe51_limbs_bounded(output, bv{64}(54));
  } {
  assume false;
};
 function field_mul (a : nat, b : nat) : nat {
  field_canonical(nat.mul(a, b))
}
 procedure Impl__13_fe_mul (self : fieldElement51, rhs : fieldElement51) returns (output : fieldElement51)
spec {
  requires fe51_limbs_bounded(self, bv{64}(54));
  requires fe51_limbs_bounded(rhs, bv{64}(54));
  ensures nat.toInt(fe51_as_canonical_nat(output)) == nat.toInt(field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(rhs)));
  ensures fe51_limbs_bounded(output, bv{64}(52));
  ensures fe51_limbs_bounded(output, bv{64}(54));
  } {
  assume false;
};
 procedure Impl__13_square (self : fieldElement51) returns (r : fieldElement51)
spec {
  requires fe51_limbs_bounded(self, bv{64}(54));
  ensures fe51_limbs_bounded(r, bv{64}(52));
  ensures fe51_limbs_bounded(r, bv{64}(54));
  ensures nat.toInt(fe51_as_canonical_nat(r)) == nat.toInt(field_canonical(nat.fromInt(Arithmetic_Power_pow(nat.toInt(u64_5_as_nat(fieldElement51..limbs(self))), nat.fromInt(2)))));
  } {
  assume false;
};
 function is_sqrt_ratio (u : nat, v : nat, r : nat) : bool {
  nat.toInt(field_canonical(nat.mul(nat.mul(r, r), v))) == nat.toInt(field_canonical(u))
}
 function fe51_is_sqrt_ratio (u : fieldElement51, v : fieldElement51, r : fieldElement51) : bool {
  is_sqrt_ratio(fe51_as_canonical_nat(u), fe51_as_canonical_nat(v), fe51_as_canonical_nat(r))
}
 function Impl__3_oNE () : fieldElement51 {
  fieldElement51_ctor(Sequence.of_bv64[bv{64}(1), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)])
}
 function sQRT_M1 () : fieldElement51 {
  fieldElement51_ctor(Sequence.of_bv64[bv{64}(1718705420411056), bv{64}(234908883556509), bv{64}(2233514472574048), bv{64}(2117202627021982), bv{64}(765476049583133)])
}
 function sqrt_m1 () : nat {
  fe51_as_canonical_nat(sQRT_M1)
}
 function is_sqrt_ratio_times_i (u : nat, v : nat, r : nat) : bool {
  nat.toInt(field_canonical(nat.mul(nat.mul(r, r), v))) == nat.toInt(field_mul(sqrt_m1, u))
}
 function fe51_is_sqrt_ratio_times_i (u : fieldElement51, v : fieldElement51, r : fieldElement51) : bool {
  is_sqrt_ratio_times_i(fe51_as_canonical_nat(u), fe51_as_canonical_nat(v), fe51_as_canonical_nat(r))
}
 procedure Impl__13_invsqrt (self : fieldElement51) returns (result : (Tuple2 choice fieldElement51))
spec {
  requires fe51_limbs_bounded(self, bv{64}(54));
  ensures nat.toInt(fe51_as_canonical_nat(self)) == 0 ==> !(choice_is_true(Tuple2.._0(result))) && nat.toInt(fe51_as_canonical_nat(Tuple2.._1(result))) == 0;
  ensures choice_is_true(Tuple2.._0(result)) ==> fe51_is_sqrt_ratio(Impl__3_oNE, self, Tuple2.._1(result));
  ensures !(choice_is_true(Tuple2.._0(result))) && !(nat.toInt(fe51_as_canonical_nat(self)) == 0) ==> fe51_is_sqrt_ratio_times_i(Impl__3_oNE, self, Tuple2.._1(result));
  ensures fe51_limbs_bounded(Tuple2.._1(result), bv{64}(52));
  ensures nat.toInt(nat.mod(fe51_as_canonical_nat(Tuple2.._1(result)), nat.fromInt(2))) == 0;
  } {
  assume false;
};
 function is_negative (a : nat) : bool {
  nat.toInt(nat.mod(field_canonical(a), nat.fromInt(2))) == 1
}
 procedure Impl__13_is_negative (self : fieldElement51) returns (result : choice)
spec {
  ensures choice_is_true(result) == is_negative(fe51_as_canonical_nat(self));
  } {
  assume false;
};
 function u8_32_as_nat (bytes : Sequence bv8) : nat {
  nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 0))), Arithmetic_Power2_pow2(nat.fromInt(0))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 1))), Arithmetic_Power2_pow2(nat.fromInt(8)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 2))), Arithmetic_Power2_pow2(nat.fromInt(16)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 3))), Arithmetic_Power2_pow2(nat.fromInt(24)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 4))), Arithmetic_Power2_pow2(nat.fromInt(32)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 5))), Arithmetic_Power2_pow2(nat.fromInt(40)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 6))), Arithmetic_Power2_pow2(nat.fromInt(48)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 7))), Arithmetic_Power2_pow2(nat.fromInt(56)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 8))), Arithmetic_Power2_pow2(nat.fromInt(64)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 9))), Arithmetic_Power2_pow2(nat.fromInt(72)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 10))), Arithmetic_Power2_pow2(nat.fromInt(80)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 11))), Arithmetic_Power2_pow2(nat.fromInt(88)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 12))), Arithmetic_Power2_pow2(nat.fromInt(96)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 13))), Arithmetic_Power2_pow2(nat.fromInt(104)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 14))), Arithmetic_Power2_pow2(nat.fromInt(112)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 15))), Arithmetic_Power2_pow2(nat.fromInt(120)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 16))), Arithmetic_Power2_pow2(nat.fromInt(128)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 17))), Arithmetic_Power2_pow2(nat.fromInt(136)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 18))), Arithmetic_Power2_pow2(nat.fromInt(144)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 19))), Arithmetic_Power2_pow2(nat.fromInt(152)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 20))), Arithmetic_Power2_pow2(nat.fromInt(160)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 21))), Arithmetic_Power2_pow2(nat.fromInt(168)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 22))), Arithmetic_Power2_pow2(nat.fromInt(176)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 23))), Arithmetic_Power2_pow2(nat.fromInt(184)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 24))), Arithmetic_Power2_pow2(nat.fromInt(192)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 25))), Arithmetic_Power2_pow2(nat.fromInt(200)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 26))), Arithmetic_Power2_pow2(nat.fromInt(208)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 27))), Arithmetic_Power2_pow2(nat.fromInt(216)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 28))), Arithmetic_Power2_pow2(nat.fromInt(224)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 29))), Arithmetic_Power2_pow2(nat.fromInt(232)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 30))), Arithmetic_Power2_pow2(nat.fromInt(240)))), nat.mul(nat.fromInt(as_uint(Sequence.select(bytes, 31))), Arithmetic_Power2_pow2(nat.fromInt(248))))
}
 procedure Impl__13_as_bytes (self : fieldElement51) returns (r : (Sequence bv8))
spec {
  ensures nat.toInt(u8_32_as_nat(r)) == nat.toInt(fe51_as_canonical_nat(self));
  ensures Sequence.length(r) == 32;
  } {
  assume false;
};
 procedure conditional_assign_field_element (a : fieldElement51, b : fieldElement51, choice : choice) returns (a_out : fieldElement51)
spec {
  requires fe51_limbs_bounded(a, bv{64}(52));
  requires fe51_limbs_bounded(b, bv{64}(52));
  ensures !(choice_is_true(choice)) ==> a_out == a;
  ensures choice_is_true(choice) ==> a_out == b;
  ensures fe51_limbs_bounded(a_out, bv{64}(52));
  } {
  assume false;
};
 function field_neg (a : nat) : nat {
  field_canonical(nat.sub(p, field_canonical(a)))
}
 procedure conditional_negate_field_element (a : fieldElement51, choice : choice) returns (a_out : fieldElement51)
spec {
  requires fe51_limbs_bounded(a, bv{64}(54));
  ensures fe51_limbs_bounded(a_out, bv{64}(54));
  ensures choice_is_true(choice) ==> fe51_limbs_bounded(a_out, bv{64}(52));
  ensures !(choice_is_true(choice)) ==> a_out == a;
  ensures nat.toInt(fe51_as_canonical_nat(a_out)) == if choice_is_true(choice) then nat.toInt(field_neg(fe51_as_canonical_nat(a))) else nat.toInt(fe51_as_canonical_nat(a));
  } {
  assume false;
};
 function fe51_as_nat (fe : fieldElement51) : nat {
  u64_5_as_nat(fieldElement51..limbs(fe))
}
 function field_square (a : nat) : nat {
  field_canonical(nat.mul(a, a))
}
 function nat_invsqrt (a : nat) : nat {
  if nat.toInt(nat.mod(a, p)) == 0 then nat.fromInt(0) else if is_negative(if nat.toInt(field_mul(a, field_square(field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))))) == nat.toInt(field_neg(nat.fromInt(1))) || nat.toInt(field_mul(a, field_square(field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))))) == nat.toInt(field_neg(sqrt_m1)) then field_mul(sqrt_m1, field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))) else field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))) then field_neg(if nat.toInt(field_mul(a, field_square(field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))))) == nat.toInt(field_neg(nat.fromInt(1))) || nat.toInt(field_mul(a, field_square(field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))))) == nat.toInt(field_neg(sqrt_m1)) then field_mul(sqrt_m1, field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))) else field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))) else if nat.toInt(field_mul(a, field_square(field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))))) == nat.toInt(field_neg(nat.fromInt(1))) || nat.toInt(field_mul(a, field_square(field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))))) == nat.toInt(field_neg(sqrt_m1)) then field_mul(sqrt_m1, field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))) else field_mul(field_mul(field_square(a), a), nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(field_mul(field_square(field_mul(field_square(a), a)), a)), nat.div(nat.fromInt(nat.toInt(p) - 5), nat.fromInt(8)))), p))
}
 function u8_32_from_nat (n : nat) : Sequence bv8 :=
  choose b : (Sequence bv8) :: Sequence.length(b) == 32 && nat.toInt(u8_32_as_nat(b)) == nat.toInt(nat.mod(n, Arithmetic_Power2_pow2(nat.fromInt(256))));
 function iNVSQRT_A_MINUS_D () : fieldElement51 {
  fieldElement51_ctor(Sequence.of_bv64[bv{64}(278908739862762), bv{64}(821645201101625), bv{64}(8113234426968), bv{64}(1777959178193151), bv{64}(2118520810568447)])
}
 function edwards_x (point : edwardsPoint) : fieldElement51 {
  edwardsPoint..X(point)
}
 function edwards_y (point : edwardsPoint) : fieldElement51 {
  edwardsPoint..Y(point)
}
 function edwards_z (point : edwardsPoint) : fieldElement51 {
  edwardsPoint..Z(point)
}
 function edwards_t (point : edwardsPoint) : fieldElement51 {
  edwardsPoint..T(point)
}
 function edwards_point_as_nat (point : edwardsPoint) : Tuple2 nat (Tuple2 nat (Tuple2 nat nat)) {
  Tuple2_ctor_2(fe51_as_canonical_nat(edwards_x(point)), Tuple2_ctor_2(fe51_as_canonical_nat(edwards_y(point)), Tuple2_ctor_2(fe51_as_canonical_nat(edwards_z(point)), fe51_as_canonical_nat(edwards_t(point)))))
}
 function is_valid_extended_edwards_point (x : nat, y : nat, z : nat, t : nat) : bool {
  !(nat.toInt(field_canonical(z)) == 0) && is_on_edwards_curve_projective(x, y, z) && nat.toInt(field_mul(x, y)) == nat.toInt(field_mul(z, t))
}
 function is_valid_edwards_point (point : edwardsPoint) : bool {
  is_valid_extended_edwards_point(fe51_as_canonical_nat(edwards_x(point)), fe51_as_canonical_nat(edwards_y(point)), fe51_as_canonical_nat(edwards_z(point)), fe51_as_canonical_nat(edwards_t(point)))
}
 function edwards_point_limbs_bounded (point : edwardsPoint) : bool {
  fe51_limbs_bounded(edwards_x(point), bv{64}(52)) && fe51_limbs_bounded(edwards_y(point), bv{64}(52)) && fe51_limbs_bounded(edwards_z(point), bv{64}(52)) && fe51_limbs_bounded(edwards_t(point), bv{64}(52))
}
 function is_well_formed_edwards_point (point : edwardsPoint) : bool {
  is_valid_edwards_point(point) && edwards_point_limbs_bounded(point) && sum_of_limbs_bounded(edwards_y(point), edwards_x(point), bv{64}(18446744073709551615))
}
 function ristretto_compress_extended (x : nat, y : nat, z : nat, t : nat) : Sequence bv8 {
  u8_32_from_nat(if is_negative(field_mul(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), fe51_as_canonical_nat(iNVSQRT_A_MINUS_D)) else field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), field_sub(z, if is_negative(field_mul(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(y, sqrt_m1) else x, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_neg(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(x, sqrt_m1) else y) else if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(x, sqrt_m1) else y))) then field_neg(field_mul(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), fe51_as_canonical_nat(iNVSQRT_A_MINUS_D)) else field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), field_sub(z, if is_negative(field_mul(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(y, sqrt_m1) else x, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_neg(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(x, sqrt_m1) else y) else if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(x, sqrt_m1) else y))) else field_mul(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), fe51_as_canonical_nat(iNVSQRT_A_MINUS_D)) else field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), field_sub(z, if is_negative(field_mul(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(y, sqrt_m1) else x, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_neg(if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(x, sqrt_m1) else y) else if is_negative(field_mul(t, field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(field_add(z, y), field_sub(z, y))), field_mul(field_mul(nat_invsqrt(field_mul(field_mul(field_add(z, y), field_sub(z, y)), field_square(field_mul(x, y)))), field_mul(x, y)), t)))) then field_mul(x, sqrt_m1) else y)))
}
 function spec_ristretto_compress (point : ristrettoPoint) : Sequence bv8 {
  ristretto_compress_extended(Tuple2.._0(edwards_point_as_nat(ristrettoPoint.._0(point))), Tuple2.._0(Tuple2.._1(edwards_point_as_nat(ristrettoPoint.._0(point)))), Tuple2.._0(Tuple2.._1(Tuple2.._1(edwards_point_as_nat(ristrettoPoint.._0(point))))), Tuple2.._1(Tuple2.._1(Tuple2.._1(edwards_point_as_nat(ristrettoPoint.._0(point))))))
}
 procedure Impl__2_clone (self : fieldElement51) returns (_pct_return : fieldElement51)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__2_clone;
};
 procedure Impl__6_clone (self : edwardsPoint) returns (_pct_return : edwardsPoint)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__6_clone;
};
 procedure Impl__9_clone (self : ristrettoPoint) returns (_pct_return : ristrettoPoint)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__9_clone;
};
 procedure Impl__12_clone (self : choice) returns (_pct_return : choice)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__12_clone;
};
 procedure Impl__14_compress (self : ristrettoPoint) returns (result : compressedRistretto)
spec {
  requires is_well_formed_edwards_point(ristrettoPoint.._0(self));
  ensures compressedRistretto.._0(result) == spec_ristretto_compress(self);
  } {
  var verus_tmp_x_nat : nat;
  var verus_tmp_y_nat : nat;
  var verus_tmp_z_nat : nat;
  var verus_tmp_t_nat : nat;
  var tmp5 : nat;
  var tmp6 : nat;
  var verus_tmp_u1_u2_sq_nat : nat;
  var tmp8 : (Tuple2 choice fieldElement51);
  var verus_tmp_invsqrt_nat : nat;
  var verus_tmp_i1_nat : nat;
  var verus_tmp_i2_nat : nat;
  var verus_tmp_z_inv_nat : nat;
  var tmp10 : fieldElement51;
  var tmp11 : fieldElement51;
  var tmp12 : fieldElement51;
  var verus_tmp_ed_nat : nat;
  var verus_tmp_rotate_bool : bool;
  var verus_tmp_old_den_inv : fieldElement51;
  var verus_tmp_x_rot : nat;
  var verus_tmp_y_rot : nat;
  var verus_tmp_den_inv_rot : nat;
  var tmp16 : bool;
  var tmp17 : bool;
  var tmp18 : bool;
  var verus_tmp_y_final : nat;
  var verus_tmp_s_pre_nat : nat;
  var verus_tmp_s_final_nat : nat;
  var tmp26 : nat;
  var chosen : (Sequence bv8);
  var spec_u1 : nat;
  var spec_u2 : nat;
  var spec_invsqrt : nat;
  var spec_i1 : nat;
  var spec_i2 : nat;
  var spec_z_inv : nat;
  var verus_tmp : nat;
  var x_nat : nat;
  var verus_tmp_ren1 : nat;
  var y_nat : nat;
  var verus_tmp_ren2 : nat;
  var z_nat : nat;
  var verus_tmp_ren3 : nat;
  var t_nat : nat;
  var X : fieldElement51;
  var Y : fieldElement51;
  var Z : fieldElement51;
  var T : fieldElement51;
  var z_plus_y : fieldElement51;
  var z_minus_y : fieldElement51;
  var u1 : fieldElement51;
  var u2 : fieldElement51;
  var u2_sq : fieldElement51;
  var u1_u2_sq : fieldElement51;
  var verus_tmp_ren4 : nat;
  var u1_u2_sq_nat : nat;
  var tmp_ren0 : (Tuple2 choice fieldElement51);
  var invsqrt : fieldElement51;
  var verus_tmp_ren5 : nat;
  var invsqrt_nat : nat;
  var i1 : fieldElement51;
  var i2 : fieldElement51;
  var i2_t : fieldElement51;
  var z_inv : fieldElement51;
  var den_inv : fieldElement51;
  var verus_tmp_ren6 : nat;
  var i1_nat : nat;
  var verus_tmp_ren7 : nat;
  var i2_nat : nat;
  var verus_tmp_ren8 : nat;
  var z_inv_nat : nat;
  var iX : fieldElement51;
  var iY : fieldElement51;
  var enchanted_denominator : fieldElement51;
  var verus_tmp_ren9 : nat;
  var ed_nat : nat;
  var t_z_inv : fieldElement51;
  var rotate : choice;
  var verus_tmp_ren10 : bool;
  var rotate_bool : bool;
  var verus_tmp_ren11 : fieldElement51;
  var old_den_inv : fieldElement51;
  var verus_tmp_ren12 : nat;
  var x_rot : nat;
  var verus_tmp_ren13 : nat;
  var y_rot : nat;
  var verus_tmp_ren14 : nat;
  var den_inv_rot : nat;
  var x_z_inv : fieldElement51;
  var x_z_inv_neg : choice;
  var verus_tmp_ren15 : nat;
  var y_final : nat;
  var z_minus_y_final : fieldElement51;
  var s : fieldElement51;
  var verus_tmp_ren16 : nat;
  var s_pre_nat : nat;
  var s_is_negative : choice;
  var verus_tmp_ren17 : nat;
  var s_final_nat : nat;
  var s_bytes : (Sequence bv8);
  call lemma_unfold_edwards(ristrettoPoint.._0(self));
  verus_tmp := fe51_as_canonical_nat(edwardsPoint..X(ristrettoPoint.._0(self)));
  verus_tmp_x_nat := verus_tmp;
  x_nat := verus_tmp_x_nat;
  verus_tmp_ren1 := fe51_as_canonical_nat(edwardsPoint..Y(ristrettoPoint.._0(self)));
  verus_tmp_y_nat := verus_tmp_ren1;
  y_nat := verus_tmp_y_nat;
  verus_tmp_ren2 := fe51_as_canonical_nat(edwardsPoint..Z(ristrettoPoint.._0(self)));
  verus_tmp_z_nat := verus_tmp_ren2;
  z_nat := verus_tmp_z_nat;
  verus_tmp_ren3 := fe51_as_canonical_nat(edwardsPoint..T(ristrettoPoint.._0(self)));
  verus_tmp_t_nat := verus_tmp_ren3;
  t_nat := verus_tmp_t_nat;
  call lemma_sum_of_limbs_bounded_from_fe51_bounded(edwardsPoint..Z(ristrettoPoint.._0(self)), edwardsPoint..Y(ristrettoPoint.._0(self)), as_bv64(52));
  assert sum_of_limbs_bounded(edwardsPoint..Z(ristrettoPoint.._0(self)), edwardsPoint..Y(ristrettoPoint.._0(self)), bv{64}(18446744073709551615));
  assume sum_of_limbs_bounded(edwardsPoint..Z(ristrettoPoint.._0(self)), edwardsPoint..Y(ristrettoPoint.._0(self)), bv{64}(18446744073709551615));
  call lemma_sqrt_m1_limbs_bounded();
  assert fe51_limbs_bounded(sQRT_M1, bv{64}(54));
  assume fe51_limbs_bounded(sQRT_M1, bv{64}(54));
  call lemma_invsqrt_a_minus_d_limbs_bounded();
  assert fe51_limbs_bounded(iNVSQRT_A_MINUS_D, bv{64}(54));
  assume fe51_limbs_bounded(iNVSQRT_A_MINUS_D, bv{64}(54));
  X := edwardsPoint..X(ristrettoPoint.._0(self));
  Y := edwardsPoint..Y(ristrettoPoint.._0(self));
  Z := edwardsPoint..Z(ristrettoPoint.._0(self));
  T := edwardsPoint..T(ristrettoPoint.._0(self));
  call lemma_fe51_limbs_bounded_weaken(Z, as_bv64(52), as_bv64(54));
  call lemma_fe51_limbs_bounded_weaken(Y, as_bv64(52), as_bv64(54));
  call lemma_fe51_limbs_bounded_weaken(X, as_bv64(52), as_bv64(54));
  call lemma_fe51_limbs_bounded_weaken(T, as_bv64(52), as_bv64(54));
  assert fe51_limbs_bounded(Z, bv{64}(54)) && fe51_limbs_bounded(Y, bv{64}(54)) && fe51_limbs_bounded(X, bv{64}(54)) && fe51_limbs_bounded(T, bv{64}(54));
  assume fe51_limbs_bounded(Z, bv{64}(54)) && fe51_limbs_bounded(Y, bv{64}(54)) && fe51_limbs_bounded(X, bv{64}(54)) && fe51_limbs_bounded(T, bv{64}(54));
  call z_plus_y := Impl__13_fe_add(Z, Y);
  
  call z_minus_y := Impl__13_fe_sub(Z, Y);
  
  call lemma_fe51_limbs_bounded_weaken(z_plus_y, as_bv64(53), as_bv64(54));
  assert fe51_limbs_bounded(z_plus_y, bv{64}(54));
  assume fe51_limbs_bounded(z_plus_y, bv{64}(54));
  call u1 := Impl__13_fe_mul(z_plus_y, z_minus_y);
  
  call u2 := Impl__13_fe_mul(X, Y);
  
  assert nat.toInt(fe51_as_canonical_nat(u1)) == nat.toInt(field_mul(field_add(z_nat, y_nat), field_sub(z_nat, y_nat)));
  assume nat.toInt(fe51_as_canonical_nat(u1)) == nat.toInt(field_mul(field_add(z_nat, y_nat), field_sub(z_nat, y_nat)));
  call u2_sq := Impl__13_square(u2);
  
  tmp5 := fe51_as_nat(u2);
  tmp6 := fe51_as_nat(u2_sq);
  call lemma_square_matches_field_square(tmp5, tmp6);
  assert nat.toInt(fe51_as_canonical_nat(u2_sq)) == nat.toInt(field_square(fe51_as_canonical_nat(u2)));
  assume nat.toInt(fe51_as_canonical_nat(u2_sq)) == nat.toInt(field_square(fe51_as_canonical_nat(u2)));
  call u1_u2_sq := Impl__13_fe_mul(u1, u2_sq);
  
  verus_tmp_ren4 := fe51_as_canonical_nat(u1_u2_sq);
  verus_tmp_u1_u2_sq_nat := verus_tmp_ren4;
  u1_u2_sq_nat := verus_tmp_u1_u2_sq_nat;
  assert nat.toInt(u1_u2_sq_nat) == nat.toInt(field_mul(fe51_as_canonical_nat(u1), field_square(fe51_as_canonical_nat(u2))));
  assume nat.toInt(u1_u2_sq_nat) == nat.toInt(field_mul(fe51_as_canonical_nat(u1), field_square(fe51_as_canonical_nat(u2))));
  call tmp8 := Impl__13_invsqrt(u1_u2_sq);
  
  tmp_ren0 := tmp8;
  invsqrt := Tuple2.._1(tmp_ren0);
  verus_tmp_ren5 := fe51_as_canonical_nat(invsqrt);
  verus_tmp_invsqrt_nat := verus_tmp_ren5;
  invsqrt_nat := verus_tmp_invsqrt_nat;
  call lemma_canonical_nat_lt_p(invsqrt);
  assert nat.lt(invsqrt_nat, p);
  assume nat.lt(invsqrt_nat, p);
  call lemma_canonical_nat_lt_p(u1_u2_sq);
  assert nat.lt(u1_u2_sq_nat, p);
  assume nat.lt(u1_u2_sq_nat, p);
  if (nat.toInt(u1_u2_sq_nat) == 0) {
    
  } else {
    call lemma_one_field_element_value(u1_u2_sq_nat, invsqrt_nat);
    assert is_sqrt_ratio(nat.fromInt(1), u1_u2_sq_nat, invsqrt_nat) || is_sqrt_ratio_times_i(nat.fromInt(1), u1_u2_sq_nat, invsqrt_nat);
    assume is_sqrt_ratio(nat.fromInt(1), u1_u2_sq_nat, invsqrt_nat) || is_sqrt_ratio_times_i(nat.fromInt(1), u1_u2_sq_nat, invsqrt_nat);
  }
  call lemma_invsqrt_matches_spec(invsqrt_nat, u1_u2_sq_nat);
  assert nat.toInt(invsqrt_nat) == nat.toInt(nat_invsqrt(u1_u2_sq_nat));
  assume nat.toInt(invsqrt_nat) == nat.toInt(nat_invsqrt(u1_u2_sq_nat));
  call lemma_fe51_limbs_bounded_weaken(invsqrt, as_bv64(52), as_bv64(54));
  assert fe51_limbs_bounded(invsqrt, bv{64}(54));
  assume fe51_limbs_bounded(invsqrt, bv{64}(54));
  call i1 := Impl__13_fe_mul(invsqrt, u1);
  
  call i2 := Impl__13_fe_mul(invsqrt, u2);
  
  call i2_t := Impl__13_fe_mul(i2, T);
  
  call z_inv := Impl__13_fe_mul(i1, i2_t);
  
  den_inv := i2;
  verus_tmp_ren6 := fe51_as_canonical_nat(i1);
  verus_tmp_i1_nat := verus_tmp_ren6;
  i1_nat := verus_tmp_i1_nat;
  verus_tmp_ren7 := fe51_as_canonical_nat(i2);
  verus_tmp_i2_nat := verus_tmp_ren7;
  i2_nat := verus_tmp_i2_nat;
  verus_tmp_ren8 := fe51_as_canonical_nat(z_inv);
  verus_tmp_z_inv_nat := verus_tmp_ren8;
  z_inv_nat := verus_tmp_z_inv_nat;
  assert nat.toInt(z_inv_nat) == nat.toInt(field_mul(i1_nat, field_mul(i2_nat, t_nat)));
  assume nat.toInt(z_inv_nat) == nat.toInt(field_mul(i1_nat, field_mul(i2_nat, t_nat)));
  tmp10 := sQRT_M1;
  call iX := Impl__13_fe_mul(X, tmp10);
  
  tmp11 := sQRT_M1;
  call iY := Impl__13_fe_mul(Y, tmp11);
  
  tmp12 := iNVSQRT_A_MINUS_D;
  call enchanted_denominator := Impl__13_fe_mul(i1, tmp12);
  
  verus_tmp_ren9 := fe51_as_canonical_nat(enchanted_denominator);
  verus_tmp_ed_nat := verus_tmp_ren9;
  ed_nat := verus_tmp_ed_nat;
  assert nat.toInt(ed_nat) == nat.toInt(field_mul(i1_nat, fe51_as_canonical_nat(iNVSQRT_A_MINUS_D)));
  assume nat.toInt(ed_nat) == nat.toInt(field_mul(i1_nat, fe51_as_canonical_nat(iNVSQRT_A_MINUS_D)));
  call t_z_inv := Impl__13_fe_mul(T, z_inv);
  
  call rotate := Impl__13_is_negative(t_z_inv);
  
  verus_tmp_ren10 := is_negative(field_mul(t_nat, z_inv_nat));
  verus_tmp_rotate_bool := verus_tmp_ren10;
  rotate_bool := verus_tmp_rotate_bool;
  assert choice_is_true(rotate) == rotate_bool;
  assume choice_is_true(rotate) == rotate_bool;
  verus_tmp_ren11 := den_inv;
  verus_tmp_old_den_inv := verus_tmp_ren11;
  old_den_inv := verus_tmp_old_den_inv;
  call X := conditional_assign_field_element(X, iY, rotate);
  
  call Y := conditional_assign_field_element(Y, iX, rotate);
  
  call den_inv := conditional_assign_field_element(den_inv, enchanted_denominator, rotate);
  
  verus_tmp_ren12 := fe51_as_canonical_nat(X);
  verus_tmp_x_rot := verus_tmp_ren12;
  x_rot := verus_tmp_x_rot;
  verus_tmp_ren13 := fe51_as_canonical_nat(Y);
  verus_tmp_y_rot := verus_tmp_ren13;
  y_rot := verus_tmp_y_rot;
  verus_tmp_ren14 := fe51_as_canonical_nat(den_inv);
  verus_tmp_den_inv_rot := verus_tmp_ren14;
  den_inv_rot := verus_tmp_den_inv_rot;
  if (choice_is_true(rotate)) {
    
  } else {
    assert den_inv == old_den_inv;
    assume den_inv == old_den_inv;
  }
  assert nat.toInt(den_inv_rot) == if rotate_bool then nat.toInt(ed_nat) else nat.toInt(i2_nat);
  assume nat.toInt(den_inv_rot) == if rotate_bool then nat.toInt(ed_nat) else nat.toInt(i2_nat);
  tmp16 := fe51_limbs_bounded(X, bv{64}(52));
  assert tmp16;
  assume tmp16;
  tmp17 := fe51_limbs_bounded(Y, bv{64}(52));
  assert tmp17;
  assume tmp17;
  tmp18 := fe51_limbs_bounded(den_inv, bv{64}(52));
  assert tmp18;
  assume tmp18;
  call x_z_inv := Impl__13_fe_mul(X, z_inv);
  
  call x_z_inv_neg := Impl__13_is_negative(x_z_inv);
  
  assert choice_is_true(x_z_inv_neg) == is_negative(field_mul(x_rot, z_inv_nat));
  assume choice_is_true(x_z_inv_neg) == is_negative(field_mul(x_rot, z_inv_nat));
  call lemma_fe51_limbs_bounded_weaken(Y, as_bv64(52), as_bv64(54));
  assert fe51_limbs_bounded(Y, bv{64}(54));
  assume fe51_limbs_bounded(Y, bv{64}(54));
  call Y := conditional_negate_field_element(Y, x_z_inv_neg);
  
  verus_tmp_ren15 := fe51_as_canonical_nat(Y);
  verus_tmp_y_final := verus_tmp_ren15;
  y_final := verus_tmp_y_final;
  assert nat.toInt(y_final) == if is_negative(field_mul(x_rot, z_inv_nat)) then nat.toInt(field_neg(y_rot)) else nat.toInt(y_rot);
  assume nat.toInt(y_final) == if is_negative(field_mul(x_rot, z_inv_nat)) then nat.toInt(field_neg(y_rot)) else nat.toInt(y_rot);
  call lemma_fe51_limbs_bounded_weaken(den_inv, as_bv64(52), as_bv64(54));
  assert fe51_limbs_bounded(den_inv, bv{64}(54));
  assume fe51_limbs_bounded(den_inv, bv{64}(54));
  call z_minus_y_final := Impl__13_fe_sub(Z, Y);
  
  call s := Impl__13_fe_mul(den_inv, z_minus_y_final);
  
  verus_tmp_ren16 := fe51_as_canonical_nat(s);
  verus_tmp_s_pre_nat := verus_tmp_ren16;
  s_pre_nat := verus_tmp_s_pre_nat;
  assert nat.toInt(fe51_as_canonical_nat(z_minus_y_final)) == nat.toInt(field_sub(z_nat, y_final));
  assume nat.toInt(fe51_as_canonical_nat(z_minus_y_final)) == nat.toInt(field_sub(z_nat, y_final));
  assert nat.toInt(s_pre_nat) == nat.toInt(field_mul(den_inv_rot, field_sub(z_nat, y_final)));
  assume nat.toInt(s_pre_nat) == nat.toInt(field_mul(den_inv_rot, field_sub(z_nat, y_final)));
  call s_is_negative := Impl__13_is_negative(s);
  
  assert choice_is_true(s_is_negative) == is_negative(s_pre_nat);
  assume choice_is_true(s_is_negative) == is_negative(s_pre_nat);
  call lemma_fe51_limbs_bounded_weaken(s, as_bv64(52), as_bv64(54));
  assert fe51_limbs_bounded(s, bv{64}(54));
  assume fe51_limbs_bounded(s, bv{64}(54));
  call s := conditional_negate_field_element(s, s_is_negative);
  
  verus_tmp_ren17 := fe51_as_canonical_nat(s);
  verus_tmp_s_final_nat := verus_tmp_ren17;
  s_final_nat := verus_tmp_s_final_nat;
  assert nat.toInt(s_final_nat) == if is_negative(s_pre_nat) then nat.toInt(field_neg(s_pre_nat)) else nat.toInt(s_pre_nat);
  assume nat.toInt(s_final_nat) == if is_negative(s_pre_nat) then nat.toInt(field_neg(s_pre_nat)) else nat.toInt(s_pre_nat);
  call s_bytes := Impl__13_as_bytes(s);
  
  assert nat.toInt(u8_32_as_nat(s_bytes)) == nat.toInt(s_final_nat);
  assume nat.toInt(u8_32_as_nat(s_bytes)) == nat.toInt(s_final_nat);
  call lemma_canonical_nat_lt_p(s);
  call pow255_gt_19();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(255), nat.fromInt(256));
  assert nat.lt(s_final_nat, Arithmetic_Power2_pow2(nat.fromInt(256)));
  assume nat.lt(s_final_nat, Arithmetic_Power2_pow2(nat.fromInt(256)));
  tmp26 := Arithmetic_Power2_pow2(nat.fromInt(256));
  call Arithmetic_Div_mod_lemma_small_mod(s_final_nat, tmp26);
  assert nat.toInt(nat.mod(s_final_nat, Arithmetic_Power2_pow2(nat.fromInt(256)))) == nat.toInt(s_final_nat);
  assume nat.toInt(nat.mod(s_final_nat, Arithmetic_Power2_pow2(nat.fromInt(256)))) == nat.toInt(s_final_nat);
  chosen := u8_32_from_nat(s_final_nat);
  call lemma_canonical_bytes_equal(s_bytes, chosen);
  assert s_bytes == u8_32_from_nat(s_final_nat);
  assume s_bytes == u8_32_from_nat(s_final_nat);
  spec_u1 := field_mul(field_add(z_nat, y_nat), field_sub(z_nat, y_nat));
  spec_u2 := field_mul(x_nat, y_nat);
  spec_invsqrt := nat_invsqrt(field_mul(spec_u1, field_square(spec_u2)));
  spec_i1 := field_mul(spec_invsqrt, spec_u1);
  spec_i2 := field_mul(spec_invsqrt, spec_u2);
  spec_z_inv := field_mul(spec_i1, field_mul(spec_i2, t_nat));
  assert nat.toInt(invsqrt_nat) == nat.toInt(spec_invsqrt);
  assume nat.toInt(invsqrt_nat) == nat.toInt(spec_invsqrt);
  assert nat.toInt(i1_nat) == nat.toInt(spec_i1);
  assume nat.toInt(i1_nat) == nat.toInt(spec_i1);
  assert nat.toInt(i2_nat) == nat.toInt(spec_i2);
  assume nat.toInt(i2_nat) == nat.toInt(spec_i2);
  assert nat.toInt(z_inv_nat) == nat.toInt(spec_z_inv);
  assume nat.toInt(z_inv_nat) == nat.toInt(spec_z_inv);
  assert rotate_bool == is_negative(field_mul(t_nat, spec_z_inv));
  assume rotate_bool == is_negative(field_mul(t_nat, spec_z_inv));
  assert nat.toInt(x_rot) == if rotate_bool then nat.toInt(field_mul(y_nat, sqrt_m1)) else nat.toInt(x_nat);
  assume nat.toInt(x_rot) == if rotate_bool then nat.toInt(field_mul(y_nat, sqrt_m1)) else nat.toInt(x_nat);
  assert nat.toInt(y_rot) == if rotate_bool then nat.toInt(field_mul(x_nat, sqrt_m1)) else nat.toInt(y_nat);
  assume nat.toInt(y_rot) == if rotate_bool then nat.toInt(field_mul(x_nat, sqrt_m1)) else nat.toInt(y_nat);
  assert nat.toInt(den_inv_rot) == if rotate_bool then nat.toInt(field_mul(spec_i1, fe51_as_canonical_nat(iNVSQRT_A_MINUS_D))) else nat.toInt(spec_i2);
  assume nat.toInt(den_inv_rot) == if rotate_bool then nat.toInt(field_mul(spec_i1, fe51_as_canonical_nat(iNVSQRT_A_MINUS_D))) else nat.toInt(spec_i2);
  assert nat.toInt(y_final) == if is_negative(field_mul(x_rot, spec_z_inv)) then nat.toInt(field_neg(y_rot)) else nat.toInt(y_rot);
  assume nat.toInt(y_final) == if is_negative(field_mul(x_rot, spec_z_inv)) then nat.toInt(field_neg(y_rot)) else nat.toInt(y_rot);
  assert nat.toInt(s_pre_nat) == nat.toInt(field_mul(den_inv_rot, field_sub(z_nat, y_final)));
  assume nat.toInt(s_pre_nat) == nat.toInt(field_mul(den_inv_rot, field_sub(z_nat, y_final)));
  assert nat.toInt(s_final_nat) == if is_negative(s_pre_nat) then nat.toInt(field_neg(s_pre_nat)) else nat.toInt(s_pre_nat);
  assume nat.toInt(s_final_nat) == if is_negative(s_pre_nat) then nat.toInt(field_neg(s_pre_nat)) else nat.toInt(s_pre_nat);
  assert s_bytes == ristretto_compress_extended(x_nat, y_nat, z_nat, t_nat);
  assume s_bytes == ristretto_compress_extended(x_nat, y_nat, z_nat, t_nat);
  result := compressedRistretto_ctor(s_bytes);
  exit Impl__14_compress;
};
 procedure Arithmetic_Div_mod_lemma_small_mod (x : nat, m : nat) returns ()
spec {
  requires nat.lt(x, m);
  requires nat.lt(nat.fromInt(0), m);
  ensures nat.toInt(nat.mod(x, m)) == nat.toInt(x);
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_mod_bound (x : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures 0 <= x mod m && x mod m < m;
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma_pow2_strictly_increases (e1 : nat, e2 : nat) returns ()
spec {
  requires nat.lt(e1, e2);
  ensures nat.lt(Arithmetic_Power2_pow2(e1), Arithmetic_Power2_pow2(e2));
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma2_to64 () returns ()
spec {
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(0))) == 1;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(1))) == 2;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(2))) == 4;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(3))) == 8;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(4))) == 16;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(5))) == 32;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(6))) == 64;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(7))) == 128;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(8))) == 256;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(9))) == 512;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(10))) == 1024;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(11))) == 2048;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(12))) == 4096;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(13))) == 8192;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(14))) == 16384;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(15))) == 32768;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(16))) == 65536;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(17))) == 131072;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(18))) == 262144;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(19))) == 524288;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(20))) == 1048576;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(21))) == 2097152;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(22))) == 4194304;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(23))) == 8388608;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(24))) == 16777216;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(25))) == 33554432;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(26))) == 67108864;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(27))) == 134217728;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(28))) == 268435456;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(29))) == 536870912;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(30))) == 1073741824;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(31))) == 2147483648;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(32))) == 4294967296;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(64))) == 18446744073709551616;
  } {
  assume false;
};
 procedure lemma_unfold_edwards (point : edwardsPoint) returns ()
spec {
  ensures edwards_x(point) == edwardsPoint..X(point);
  ensures edwards_y(point) == edwardsPoint..Y(point);
  ensures edwards_z(point) == edwardsPoint..Z(point);
  ensures edwards_t(point) == edwardsPoint..T(point);
  } {
  exit lemma_unfold_edwards;
};
 procedure pow255_gt_19 () returns ()
spec {
  ensures nat.gt(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19));
  } {
  call Arithmetic_Power2_lemma2_to64();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(5), nat.fromInt(255));
  exit pow255_gt_19;
};
 procedure lemma_fe51_limbs_bounded_weaken (fe : fieldElement51, a : bv64, b : bv64) returns ()
spec {
  requires fe51_limbs_bounded(fe, a);
  requires a < b;
  requires b <= bv{64}(63);
  ensures fe51_limbs_bounded(fe, b);
  } {
  var i : int;
  assume 0 <= i && i < 5;
  assert Sequence.select(fieldElement51..limbs(fe), i) < bv{64}(1) << a;
  assume Sequence.select(fieldElement51..limbs(fe), i) < bv{64}(1) << a;
  assert a < b;
  assert b <= bv{64}(63);
  assert [bitvector_query]: a < b && b <= bv{64}(63) ==> bv{64}(1) << a < bv{64}(1) << b;
  assert Sequence.select(fieldElement51..limbs(fe), i) < bv{64}(1) << b;
  assume ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(fieldElement51..limbs(fe), i) < bv{64}(1) << b;
  exit lemma_fe51_limbs_bounded_weaken;
};
 procedure lemma_sum_of_limbs_bounded_from_fe51_bounded (a : fieldElement51, b : fieldElement51, n : bv64) returns ()
spec {
  requires fe51_limbs_bounded(a, n);
  requires fe51_limbs_bounded(b, n);
  requires n <= bv{64}(62);
  ensures sum_of_limbs_bounded(a, b, bv{64}(18446744073709551615));
  } {
  var i : int;
  assume 0 <= i && i < 5;
  assert Sequence.select(fieldElement51..limbs(a), i) < bv{64}(1) << n;
  assume Sequence.select(fieldElement51..limbs(a), i) < bv{64}(1) << n;
  assert Sequence.select(fieldElement51..limbs(b), i) < bv{64}(1) << n;
  assume Sequence.select(fieldElement51..limbs(b), i) < bv{64}(1) << n;
  assert n <= bv{64}(62);
  assert [bitvector_query]: n <= bv{64}(62) ==> as_uint(bv{64}(1) << n) + as_uint(bv{64}(1) << n) < 18446744073709551615;
  assert as_uint(Sequence.select(fieldElement51..limbs(a), i)) + as_uint(Sequence.select(fieldElement51..limbs(b), i)) < 18446744073709551615;
  assume ∀ i : int :: 0 <= i && i < 5 ==> as_uint(Sequence.select(fieldElement51..limbs(a), i)) + as_uint(Sequence.select(fieldElement51..limbs(b), i)) < 18446744073709551615;
  exit lemma_sum_of_limbs_bounded_from_fe51_bounded;
};
 procedure lemma_sqrt_m1_limbs_bounded () returns ()
spec {
  ensures fe51_limbs_bounded(sQRT_M1, bv{64}(54));
  } {
  assert [compute]: Sequence.select(fieldElement51..limbs(sQRT_M1), 0) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(sQRT_M1), 1) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(sQRT_M1), 2) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(sQRT_M1), 3) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(sQRT_M1), 4) < bv{64}(1) << bv{64}(54);
  exit lemma_sqrt_m1_limbs_bounded;
};
 procedure lemma_invsqrt_a_minus_d_limbs_bounded () returns ()
spec {
  ensures fe51_limbs_bounded(iNVSQRT_A_MINUS_D, bv{64}(54));
  } {
  assert [compute]: Sequence.select(fieldElement51..limbs(iNVSQRT_A_MINUS_D), 0) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(iNVSQRT_A_MINUS_D), 1) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(iNVSQRT_A_MINUS_D), 2) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(iNVSQRT_A_MINUS_D), 3) < bv{64}(1) << bv{64}(54);
  assert [compute]: Sequence.select(fieldElement51..limbs(iNVSQRT_A_MINUS_D), 4) < bv{64}(1) << bv{64}(54);
  exit lemma_invsqrt_a_minus_d_limbs_bounded;
};
 procedure lemma_canonical_nat_lt_p (x : fieldElement51) returns ()
spec {
  ensures nat.lt(fe51_as_canonical_nat(x), p);
  } {
  var tmp1 : nat;
  var tmp2 : nat;
  call pow255_gt_19();
  assert nat.gt(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19));
  assume nat.gt(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19));
  tmp1 := fe51_as_nat(x);
  tmp2 := p;
  call Arithmetic_Div_mod_lemma_mod_bound(nat.toInt(tmp1), nat.toInt(tmp2));
  exit lemma_canonical_nat_lt_p;
};
 procedure lemma_square_matches_field_square (y_raw : nat, y2_raw : nat) returns ()
spec {
  requires nat.toInt(nat.mod(y2_raw, p)) == nat.toInt(nat.mod(nat.fromInt(Arithmetic_Power_pow(nat.toInt(y_raw), nat.fromInt(2))), p));
  ensures nat.toInt(nat.mod(y2_raw, p)) == nat.toInt(field_square(nat.mod(y_raw, p)));
  } {
  assume false;
  exit lemma_square_matches_field_square;
};
 procedure lemma_one_field_element_value (v : nat, r : nat) returns ()
spec {
  requires nat.lt(v, p);
  requires nat.lt(r, p);
  requires !(nat.toInt(v) == 0);
  ensures is_sqrt_ratio(nat.fromInt(1), v, r) || is_sqrt_ratio_times_i(nat.fromInt(1), v, r);
  } {
  assume false;
  exit lemma_one_field_element_value;
};
 procedure lemma_invsqrt_matches_spec (big_i_nat : nat, v_u2_sqr_nat : nat) returns ()
spec {
  requires nat.toInt(nat.mod(big_i_nat, nat.fromInt(2))) == 0;
  requires nat.toInt(v_u2_sqr_nat) == 0 ==> nat.toInt(big_i_nat) == 0;
  requires !(nat.toInt(v_u2_sqr_nat) == 0) ==> is_sqrt_ratio(nat.fromInt(1), v_u2_sqr_nat, big_i_nat) || is_sqrt_ratio_times_i(nat.fromInt(1), v_u2_sqr_nat, big_i_nat);
  requires nat.lt(big_i_nat, p);
  requires nat.lt(v_u2_sqr_nat, p);
  ensures nat.toInt(big_i_nat) == nat.toInt(nat_invsqrt(v_u2_sqr_nat));
  } {
  assume false;
  exit lemma_invsqrt_matches_spec;
};
 procedure lemma_canonical_bytes_equal (bytes1 : Sequence bv8, bytes2 : Sequence bv8) returns ()
spec {
  requires nat.toInt(u8_32_as_nat(bytes1)) == nat.toInt(u8_32_as_nat(bytes2));
  ensures ∀ i : int :: 0 <= i && i < 32 ==> Sequence.select(bytes1, i) == Sequence.select(bytes2, i);
  } {
  assume false;
  exit lemma_canonical_bytes_equal;
};
#end

-- The inline `#eval` is Lean-compilation-bound on this large program and does
-- not reach cvc5 within a practical timeout; the figure below is from a
-- dedicated run (cvc5 invoked directly on the exported VCs).
-- cvc5 via Strata.Boole.verify: 519 of 655 VCs pass, 136 timeouts, 0 failures
-- #eval Strata.Boole.verify "cvc5" b4_minimal_program (options := .quiet)
