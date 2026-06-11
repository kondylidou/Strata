/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Benchmark B3 — `CompressedEdwardsY::decompress` (VARIANT: minimal)

Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
File:   curve25519-dalek/src/edwards.rs (`decompress`, `step_1`, `step_2`)

Edwards point decompression for Ed25519: decode the y-coordinate from 32
bytes, recover x = sqrt((y² − 1)/(d·y² + 1)) when it exists, and assemble
the extended-coordinates point. This runs in every Ed25519 signature
verification. The verified body is `Impl__11_decompress`: the branch on the
validity check plus the proof chaining `lemma_decompress_valid_branch` and
limb-bound weakening into the well-formedness postconditions.

Translation notes:
  - The `(Choice, FieldElement, FieldElement, FieldElement)` return of
    `step_1` becomes nested binary pairs
    (`Tuple2 choice (Tuple2 fieldElement51 …)`), projected with
    `Tuple2.._0` / `Tuple2.._1` chains.
  - `Option<EdwardsPoint>` becomes the two-constructor datatype
    `Option_option`.
  - `FieldElement51` and `CompressedEdwardsY` are type synonyms
    over `Sequence` with the length invariant on the constructors'
    `requires`.
  - `subtle::Choice` is a single-field datatype with an uninterpreted
    `choice_is_true` observer.

Trust boundary (8 `assume false` stubs):
  - `Decompress_step_1` / `Decompress_step_2` — the field-operation
    pipelines (from_bytes, square, sqrt_ratio_i, conditional negate);
    specs taken verbatim from dalek-lite.
  - `lemma_decompress_valid_branch` — the curve argument (~70 lines),
    admitted in dalek-lite as well.
  - `Impl__10_from` / `choice_into` — the `subtle::Choice` observers
    (`external_body` upstream).
  - Three vstd arithmetic lemmas (`lemma_mod_bound`, `lemma2_to64`,
    `lemma_pow2_strictly_increases`), proved in vstd upstream.

Results: cvc5 discharges 430 of 509 VCs; the 79 timeouts are
definition-level obligations (`Sequence.select` bounds inside the 32-term
`u8_32_as_nat`, pow2 value facts), not the decompress proof itself.

Status: this file uses the `as_int` cast syntax from pr/casts-boole, which
this branch does not have yet; the `#exit` below keeps it inert until then.
The cvc5 run additionally needs the `toCoreMonoType` type-argument-order
fix (provided to pr/casts-boole as a patch).
-/

#exit

open Strata

set_option maxRecDepth 100000

private def b3_minimal_program : StrataDDM.Program :=
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
 function int_pow2 (e : int) : int;
 axiom [int_pow2_zero]: int_pow2(0) == 1;
 axiom [int_pow2_succ]: forall e : int :: 0 <= e ==> int_pow2(e + 1) == 2 * int_pow2(e);
 axiom [int_pow2_pos]: forall e : int :: 0 <= e ==> 1 <= int_pow2(e);
 datatype Tuple2 (T0 : Type, T1 : Type) {
  Tuple2_ctor_2(_0 : T0, _1 : T1)
};
 type compressedEdwardsY := Sequence bv8;
 function compressedEdwardsY_ctor (_0 : Sequence bv8) : Sequence bv8 requires Sequence.length(_0) == 32;
   {
  _0
}
 function compressedEdwardsY.._0 (_0 : Sequence bv8) : Sequence bv8 {
  _0
}
 datatype Option_option (V : Type) {
  Option_option_None(),
  Option_option_Some(Option_option_Some_0 : V)
};
 datatype choice {
  choice_ctor(v : bv8)
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
 function Arithmetic_Power2_pow2 (e : nat) : nat;
 function choice_is_true (c : choice) : bool;
 procedure Impl__10_from (u : bv8) returns (c : choice)
spec {
  ensures (u == bv{8}(1)) == choice_is_true(c);
  } {
  assume false;
};
 procedure choice_into (c : choice) returns (b : bool)
spec {
  ensures b == choice_is_true(c);
  } {
  assume false;
};
 function u8_32_as_nat (bytes : Sequence bv8) : nat {
  nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.mul(nat.fromInt(Sequence.select(bytes, 0) as_int), Arithmetic_Power2_pow2(nat.fromInt(0))), nat.mul(nat.fromInt(Sequence.select(bytes, 1) as_int), Arithmetic_Power2_pow2(nat.fromInt(8)))), nat.mul(nat.fromInt(Sequence.select(bytes, 2) as_int), Arithmetic_Power2_pow2(nat.fromInt(16)))), nat.mul(nat.fromInt(Sequence.select(bytes, 3) as_int), Arithmetic_Power2_pow2(nat.fromInt(24)))), nat.mul(nat.fromInt(Sequence.select(bytes, 4) as_int), Arithmetic_Power2_pow2(nat.fromInt(32)))), nat.mul(nat.fromInt(Sequence.select(bytes, 5) as_int), Arithmetic_Power2_pow2(nat.fromInt(40)))), nat.mul(nat.fromInt(Sequence.select(bytes, 6) as_int), Arithmetic_Power2_pow2(nat.fromInt(48)))), nat.mul(nat.fromInt(Sequence.select(bytes, 7) as_int), Arithmetic_Power2_pow2(nat.fromInt(56)))), nat.mul(nat.fromInt(Sequence.select(bytes, 8) as_int), Arithmetic_Power2_pow2(nat.fromInt(64)))), nat.mul(nat.fromInt(Sequence.select(bytes, 9) as_int), Arithmetic_Power2_pow2(nat.fromInt(72)))), nat.mul(nat.fromInt(Sequence.select(bytes, 10) as_int), Arithmetic_Power2_pow2(nat.fromInt(80)))), nat.mul(nat.fromInt(Sequence.select(bytes, 11) as_int), Arithmetic_Power2_pow2(nat.fromInt(88)))), nat.mul(nat.fromInt(Sequence.select(bytes, 12) as_int), Arithmetic_Power2_pow2(nat.fromInt(96)))), nat.mul(nat.fromInt(Sequence.select(bytes, 13) as_int), Arithmetic_Power2_pow2(nat.fromInt(104)))), nat.mul(nat.fromInt(Sequence.select(bytes, 14) as_int), Arithmetic_Power2_pow2(nat.fromInt(112)))), nat.mul(nat.fromInt(Sequence.select(bytes, 15) as_int), Arithmetic_Power2_pow2(nat.fromInt(120)))), nat.mul(nat.fromInt(Sequence.select(bytes, 16) as_int), Arithmetic_Power2_pow2(nat.fromInt(128)))), nat.mul(nat.fromInt(Sequence.select(bytes, 17) as_int), Arithmetic_Power2_pow2(nat.fromInt(136)))), nat.mul(nat.fromInt(Sequence.select(bytes, 18) as_int), Arithmetic_Power2_pow2(nat.fromInt(144)))), nat.mul(nat.fromInt(Sequence.select(bytes, 19) as_int), Arithmetic_Power2_pow2(nat.fromInt(152)))), nat.mul(nat.fromInt(Sequence.select(bytes, 20) as_int), Arithmetic_Power2_pow2(nat.fromInt(160)))), nat.mul(nat.fromInt(Sequence.select(bytes, 21) as_int), Arithmetic_Power2_pow2(nat.fromInt(168)))), nat.mul(nat.fromInt(Sequence.select(bytes, 22) as_int), Arithmetic_Power2_pow2(nat.fromInt(176)))), nat.mul(nat.fromInt(Sequence.select(bytes, 23) as_int), Arithmetic_Power2_pow2(nat.fromInt(184)))), nat.mul(nat.fromInt(Sequence.select(bytes, 24) as_int), Arithmetic_Power2_pow2(nat.fromInt(192)))), nat.mul(nat.fromInt(Sequence.select(bytes, 25) as_int), Arithmetic_Power2_pow2(nat.fromInt(200)))), nat.mul(nat.fromInt(Sequence.select(bytes, 26) as_int), Arithmetic_Power2_pow2(nat.fromInt(208)))), nat.mul(nat.fromInt(Sequence.select(bytes, 27) as_int), Arithmetic_Power2_pow2(nat.fromInt(216)))), nat.mul(nat.fromInt(Sequence.select(bytes, 28) as_int), Arithmetic_Power2_pow2(nat.fromInt(224)))), nat.mul(nat.fromInt(Sequence.select(bytes, 29) as_int), Arithmetic_Power2_pow2(nat.fromInt(232)))), nat.mul(nat.fromInt(Sequence.select(bytes, 30) as_int), Arithmetic_Power2_pow2(nat.fromInt(240)))), nat.mul(nat.fromInt(Sequence.select(bytes, 31) as_int), Arithmetic_Power2_pow2(nat.fromInt(248))))
}
 function p () : nat {
  nat.sub(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19))
}
 function field_canonical (n : nat) : nat {
  nat.mod(n, p)
}
 function u64_5_as_nat (limbs : Sequence bv64) : nat {
  nat.add(nat.add(nat.add(nat.add(nat.fromInt(Sequence.select(limbs, 0) as_int), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(51)), nat.fromInt(Sequence.select(limbs, 1) as_int))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(102)), nat.fromInt(Sequence.select(limbs, 2) as_int))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(153)), nat.fromInt(Sequence.select(limbs, 3) as_int))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(204)), nat.fromInt(Sequence.select(limbs, 4) as_int)))
}
 function u64_5_as_field_canonical (limbs : Sequence bv64) : nat {
  field_canonical(u64_5_as_nat(limbs))
}
 function u64_5_bounded (limbs : Sequence bv64, bit_limit : bv64) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(limbs, i) < bv{64}(1) << bit_limit
}
 function fe51_limbs_bounded (fe : fieldElement51, bit_limit : bv64) : bool {
  u64_5_bounded(fieldElement51..limbs(fe), bit_limit)
}
 function sum_of_limbs_bounded (fe1 : fieldElement51, fe2 : fieldElement51, bound : bv64) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(fieldElement51..limbs(fe1), i) + Sequence.select(fieldElement51..limbs(fe2), i) < bound
}
 function fe51_as_nat (fe : fieldElement51) : nat {
  u64_5_as_nat(fieldElement51..limbs(fe))
}
 function fe51_as_canonical_nat (fe : fieldElement51) : nat {
  u64_5_as_field_canonical(fieldElement51..limbs(fe))
}
 function field_element_from_bytes (bytes : Sequence bv8) : nat {
  field_canonical(nat.mod(u8_32_as_nat(bytes), Arithmetic_Power2_pow2(nat.fromInt(255))))
}
 function fe51_as_canonical_nat_sign_bit (fe : fieldElement51) : bv8 {
  nat.toInt(nat.mod(fe51_as_canonical_nat(fe), nat.fromInt(2))) as_bv8
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
 function eDWARDS_D () : fieldElement51 {
  fieldElement51_ctor(Sequence.of_bv64[bv{64}(929955233495203), bv{64}(466365720129213), bv{64}(1662059464998953), bv{64}(2033849074728123), bv{64}(1442794654840575)])
}
 function is_on_edwards_curve (x : nat, y : nat) : bool {
  nat.toInt(field_sub(field_square(y), field_square(x))) == nat.toInt(field_add(nat.fromInt(1), field_mul(fe51_as_canonical_nat(eDWARDS_D), field_mul(field_square(x), field_square(y)))))
}
 function is_on_edwards_curve_projective (x : nat, y : nat, z : nat) : bool {
  nat.toInt(field_mul(field_sub(field_square(y), field_square(x)), field_square(z))) == nat.toInt(field_add(field_square(field_square(z)), field_mul(fe51_as_canonical_nat(eDWARDS_D), field_mul(field_square(x), field_square(y)))))
}
 function is_valid_edwards_y_coordinate (y : nat) : bool {
  if nat.toInt(nat.mod(field_sub(field_square(y), nat.fromInt(1)), p)) == 0 then true else if nat.toInt(nat.mod(field_add(field_mul(fe51_as_canonical_nat(eDWARDS_D), field_square(y)), nat.fromInt(1)), p)) == 0 then false else ∃ r : nat :: nat.lt(r, p) && (nat.toInt(field_mul(field_square(r), field_add(field_mul(fe51_as_canonical_nat(eDWARDS_D), field_square(y)), nat.fromInt(1)))) == nat.toInt(nat.mod(field_sub(field_square(y), nat.fromInt(1)), p)) || nat.toInt(field_mul(field_square(r), field_add(field_mul(fe51_as_canonical_nat(eDWARDS_D), field_square(y)), nat.fromInt(1)))) == nat.toInt(field_neg(field_sub(field_square(y), nat.fromInt(1)))))
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
 function edwards_y_nat (point : edwardsPoint) : nat {
  fe51_as_canonical_nat(edwards_y(point))
}
 function edwards_z_nat (point : edwardsPoint) : nat {
  fe51_as_canonical_nat(edwards_z(point))
}
 function edwards_x_sign_bit (point : edwardsPoint) : bv8 {
  fe51_as_canonical_nat_sign_bit(edwards_x(point))
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
 procedure Impl__9_clone (self : choice) returns (_pct_return : choice)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__9_clone;
};
 procedure Decompress_step_1 (repr : compressedEdwardsY) returns (result : (Tuple2 choice (Tuple2 fieldElement51 (Tuple2 fieldElement51 fieldElement51))))
spec {
  ensures nat.toInt(fe51_as_canonical_nat(Tuple2.._0(Tuple2.._1(Tuple2.._1(result))))) == nat.toInt(field_element_from_bytes(compressedEdwardsY.._0(repr))) && nat.toInt(fe51_as_canonical_nat(Tuple2.._1(Tuple2.._1(Tuple2.._1(result))))) == 1 && choice_is_true(Tuple2.._0(result)) == is_valid_edwards_y_coordinate(fe51_as_canonical_nat(Tuple2.._0(Tuple2.._1(Tuple2.._1(result))))) && (choice_is_true(Tuple2.._0(result)) ==> is_on_edwards_curve(fe51_as_canonical_nat(Tuple2.._0(Tuple2.._1(result))), fe51_as_canonical_nat(Tuple2.._0(Tuple2.._1(Tuple2.._1(result)))))) && fe51_limbs_bounded(Tuple2.._0(Tuple2.._1(result)), bv{64}(52)) && fe51_limbs_bounded(Tuple2.._0(Tuple2.._1(Tuple2.._1(result))), bv{64}(51)) && fe51_limbs_bounded(Tuple2.._1(Tuple2.._1(Tuple2.._1(result))), bv{64}(51)) && nat.toInt(nat.mod(fe51_as_canonical_nat(Tuple2.._0(Tuple2.._1(result))), nat.fromInt(2))) == 0;
  } {
  assume false;
};
 procedure Decompress_step_2 (repr : compressedEdwardsY, X : fieldElement51, Y : fieldElement51, Z : fieldElement51) returns (result : edwardsPoint)
spec {
  requires fe51_limbs_bounded(X, bv{64}(52));
  requires fe51_limbs_bounded(Y, bv{64}(51));
  requires fe51_limbs_bounded(Z, bv{64}(51));
  requires is_on_edwards_curve(fe51_as_canonical_nat(X), fe51_as_canonical_nat(Y));
  requires nat.toInt(fe51_as_canonical_nat(Z)) == 1;
  ensures nat.toInt(fe51_as_canonical_nat(edwardsPoint..X(result))) == if Sequence.select(compressedEdwardsY.._0(repr), 31) >> bv{8}(7) == bv{8}(1) then nat.toInt(field_neg(fe51_as_canonical_nat(X))) else nat.toInt(fe51_as_canonical_nat(X));
  ensures edwardsPoint..Y(result) == Y && edwardsPoint..Z(result) == Z && nat.toInt(fe51_as_canonical_nat(edwardsPoint..T(result))) == nat.toInt(field_mul(fe51_as_canonical_nat(edwardsPoint..X(result)), fe51_as_canonical_nat(edwardsPoint..Y(result))));
  ensures fe51_limbs_bounded(edwardsPoint..X(result), bv{64}(52));
  ensures fe51_limbs_bounded(edwardsPoint..T(result), bv{64}(52));
  } {
  assume false;
};
 procedure Impl__11_decompress (self : compressedEdwardsY) returns (result : (Option_option edwardsPoint))
spec {
  ensures is_valid_edwards_y_coordinate(field_element_from_bytes(compressedEdwardsY.._0(self))) == Option_option..isOption_option_Some(result);
  ensures Option_option..isOption_option_Some(result) ==> nat.toInt(edwards_y_nat(Option_option..Option_option_Some_0(result))) == nat.toInt(field_element_from_bytes(compressedEdwardsY.._0(self))) && nat.toInt(edwards_z_nat(Option_option..Option_option_Some_0(result))) == 1 && is_well_formed_edwards_point(Option_option..Option_option_Some_0(result)) && (!(nat.toInt(field_square(field_element_from_bytes(compressedEdwardsY.._0(self)))) == 1) ==> edwards_x_sign_bit(Option_option..Option_option_Some_0(result)) == Sequence.select(compressedEdwardsY.._0(self), 31) >> bv{8}(7));
  } {
  var tmp1 : (Tuple2 choice (Tuple2 fieldElement51 (Tuple2 fieldElement51 fieldElement51)));
  var tmp4 : bool;
  var tmp9 : nat;
  var tmp10 : nat;
  var tmp12 : bool;
  var tmp13 : bool;
  var tmp16 : bool;
  var tmp19 : bool;
  var x_orig : nat;
  var point : edwardsPoint;
  var tmp20 : (Option_option edwardsPoint);
  var tmp_ren0 : (Tuple2 choice (Tuple2 fieldElement51 (Tuple2 fieldElement51 fieldElement51)));
  var is_valid_y_coord : choice;
  var X : fieldElement51;
  var Y : fieldElement51;
  var Z : fieldElement51;
  call tmp1 := Decompress_step_1(self);
  
  tmp_ren0 := tmp1;
  is_valid_y_coord := Tuple2.._0(tmp_ren0);
  X := Tuple2.._0(Tuple2.._1(tmp_ren0));
  Y := Tuple2.._0(Tuple2.._1(Tuple2.._1(tmp_ren0)));
  Z := Tuple2.._1(Tuple2.._1(Tuple2.._1(tmp_ren0)));
  assert choice_is_true(is_valid_y_coord) ==> is_valid_edwards_y_coordinate(field_element_from_bytes(compressedEdwardsY.._0(self)));
  assume choice_is_true(is_valid_y_coord) ==> is_valid_edwards_y_coordinate(field_element_from_bytes(compressedEdwardsY.._0(self)));
  assert choice_is_true(is_valid_y_coord) ==> is_on_edwards_curve(fe51_as_canonical_nat(X), fe51_as_canonical_nat(Y));
  assume choice_is_true(is_valid_y_coord) ==> is_on_edwards_curve(fe51_as_canonical_nat(X), fe51_as_canonical_nat(Y));
  call tmp4 := choice_into(is_valid_y_coord);
  
  if (tmp4) {
    call point := Decompress_step_2(self, X, Y, Z);
    
    result := Option_option_Some(point);
    call lemma_unfold_edwards(point);
    x_orig := fe51_as_canonical_nat(X);
    assert edwardsPoint..Y(point) == Y;
    assume edwardsPoint..Y(point) == Y;
    assert edwardsPoint..Z(point) == Z;
    assume edwardsPoint..Z(point) == Z;
    assert nat.toInt(fe51_as_canonical_nat(edwardsPoint..Y(point))) == nat.toInt(field_element_from_bytes(compressedEdwardsY.._0(self)));
    assume nat.toInt(fe51_as_canonical_nat(edwardsPoint..Y(point))) == nat.toInt(field_element_from_bytes(compressedEdwardsY.._0(self)));
    assert nat.toInt(fe51_as_canonical_nat(edwardsPoint..Z(point))) == 1;
    assume nat.toInt(fe51_as_canonical_nat(edwardsPoint..Z(point))) == 1;
    call pow255_gt_19();
    tmp9 := fe51_as_nat(X);
    tmp10 := p;
    call Arithmetic_Div_mod_lemma_mod_bound(nat.toInt(tmp9), nat.toInt(tmp10));
    assert nat.lt(x_orig, p);
    assume nat.lt(x_orig, p);
    call lemma_decompress_valid_branch(compressedEdwardsY.._0(self), x_orig, point);
    tmp12 := fe51_limbs_bounded(edwardsPoint..Y(point), bv{64}(51));
    assert tmp12;
    assume tmp12;
    tmp13 := fe51_limbs_bounded(edwardsPoint..Z(point), bv{64}(51));
    assert tmp13;
    assume tmp13;
    assert [compute]: bv{64}(1) << bv{64}(51) < bv{64}(1) << bv{64}(52);
    call lemma_fe51_limbs_bounded_weaken(edwardsPoint..Y(point), 51 as_bv64, 52 as_bv64);
    call lemma_fe51_limbs_bounded_weaken(edwardsPoint..Z(point), 51 as_bv64, 52 as_bv64);
    tmp16 := edwards_point_limbs_bounded(point);
    assert tmp16;
    assume tmp16;
    call lemma_sum_of_limbs_bounded_from_fe51_bounded(edwardsPoint..Y(point), edwardsPoint..X(point), 52 as_bv64);
    tmp19 := is_well_formed_edwards_point(point);
    assert tmp19;
    assume tmp19;
    tmp20 := result;
  } else {
    tmp20 := Option_option_None;
  }
  result := tmp20;
  exit Impl__11_decompress;
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
 procedure p_gt_2 () returns ()
spec {
  ensures nat.gt(p, nat.fromInt(2));
  ensures nat.gt(nat.sub(p, nat.fromInt(2)), nat.fromInt(0));
  } {
  call Arithmetic_Power2_lemma2_to64();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(5), nat.fromInt(255));
  exit p_gt_2;
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
  assert [bitvector_query]: n <= bv{64}(62) ==> (bv{64}(1) << n) + (bv{64}(1) << n) < bv{64}(18446744073709551615);
  assert Sequence.select(fieldElement51..limbs(a), i) + Sequence.select(fieldElement51..limbs(b), i) < bv{64}(18446744073709551615);
  assume ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(fieldElement51..limbs(a), i) + Sequence.select(fieldElement51..limbs(b), i) < bv{64}(18446744073709551615);
  exit lemma_sum_of_limbs_bounded_from_fe51_bounded;
};
 procedure lemma_decompress_valid_branch (repr_bytes : Sequence bv8, x_orig : nat, point : edwardsPoint) returns ()
spec {
  requires nat.toInt(fe51_as_canonical_nat(edwardsPoint..Y(point))) == nat.toInt(field_element_from_bytes(repr_bytes));
  requires is_on_edwards_curve(x_orig, fe51_as_canonical_nat(edwardsPoint..Y(point)));
  requires nat.toInt(nat.mod(x_orig, nat.fromInt(2))) == 0;
  requires nat.lt(x_orig, p);
  requires nat.toInt(fe51_as_canonical_nat(edwardsPoint..X(point))) == if Sequence.select(repr_bytes, 31) >> bv{8}(7) == bv{8}(1) then nat.toInt(field_neg(x_orig)) else nat.toInt(x_orig);
  requires nat.toInt(fe51_as_canonical_nat(edwardsPoint..Z(point))) == 1;
  requires nat.toInt(fe51_as_canonical_nat(edwardsPoint..T(point))) == nat.toInt(field_mul(fe51_as_canonical_nat(edwardsPoint..X(point)), fe51_as_canonical_nat(edwardsPoint..Y(point))));
  ensures is_valid_edwards_point(point);
  ensures nat.toInt(fe51_as_canonical_nat(edwardsPoint..Y(point))) == nat.toInt(field_element_from_bytes(repr_bytes));
  ensures !(nat.toInt(field_square(field_element_from_bytes(repr_bytes))) == 1) ==> fe51_as_canonical_nat_sign_bit(edwardsPoint..X(point)) == Sequence.select(repr_bytes, 31) >> bv{8}(7);
  } {
  assume false;
  exit lemma_decompress_valid_branch;
};
#end

-- cvc5 via Strata.Boole.verify: 430 of 509 VCs pass, 79 timeouts
-- #eval Strata.Boole.verify "cvc5" b3_minimal_program (options := .quiet)
