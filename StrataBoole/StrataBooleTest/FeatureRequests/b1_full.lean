/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Benchmark B1 — `FieldElement51::mul` (VARIANT: full proof)

Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
File:   curve25519-dalek/src/backend/serial/u64/field.rs (lines 486–634)

The complete B1. Unlike `b1_minimal.lean` (both main lemmas trusted) and
`b1_boundary_proved.lean` (boundary lemma proved, value lemma trusted), this
variant carries the full dalek-lite proof closure: `lemma_mul_boundary`,
`lemma_mul_value`, and every supporting lemma have their real proof bodies.
The only `assume false` stubs are 22 vstd arithmetic and bit-manipulation
library lemmas (mul, div_mod, power2, bits), which are proved in vstd
upstream. 49 procedures, ~1330 lines of Boole.

Status: `#strata` elaboration of a program this size overflows the
interpreter stack ("Stack overflow detected"), independent of `maxRecDepth`
and the OS stack limit; the fix is elaborator-side (chunked elaboration or
an iterative AST walk in StrataDDM). The `#exit` below keeps the file inert
until then — remove it to attempt elaboration. Verification has not been
attempted; `b1_minimal.lean`'s nonlinear wall is expected to apply.
-/

#exit

open Strata

set_option maxRecDepth 100000

private def b1_full_program : StrataDDM.Program :=
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
 type fieldElement51 := Sequence bv64;
 function fieldElement51_ctor (limbs : Sequence bv64) : Sequence bv64 requires Sequence.length(limbs) == 5;
   {
  limbs
}
 function fieldElement51..limbs (limbs : Sequence bv64) : Sequence bv64 {
  limbs
}
 function Arithmetic_Power2_pow2 (e : nat) : nat;
 function Bits_low_bits_mask (n : nat) : nat;
 function u64_5_as_nat (limbs : Sequence bv64) : nat {
  nat.add(nat.add(nat.add(nat.add(nat.fromInt(Sequence.select(limbs, 0) as_int), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(51)), nat.fromInt(Sequence.select(limbs, 1) as_int))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(102)), nat.fromInt(Sequence.select(limbs, 2) as_int))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(153)), nat.fromInt(Sequence.select(limbs, 3) as_int))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(204)), nat.fromInt(Sequence.select(limbs, 4) as_int)))
}
 function p () : nat {
  nat.sub(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19))
}
 function field_canonical (n : nat) : nat {
  nat.mod(n, p)
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
 function fe51_as_canonical_nat (fe : fieldElement51) : nat {
  u64_5_as_field_canonical(fieldElement51..limbs(fe))
}
 function field_mul (a : nat, b : nat) : nat {
  field_canonical(nat.mul(a, b))
}
 function lOW_51_BIT_MASK () : bv64 {
  bv{64}(2251799813685247)
}
 function mask51 () : bv64 {
  bv{64}(2251799813685247)
}
 function mul_c0_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  (Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 1) as_int) + Sequence.select(a, 3) as_int * (19 * Sequence.select(b, 2) as_int) + Sequence.select(a, 2) as_int * (19 * Sequence.select(b, 3) as_int) + Sequence.select(a, 1) as_int * (19 * Sequence.select(b, 4) as_int)) mod 340282366920938463463374607431768211456
}
 function mul_c1_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  (Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 2) as_int) + Sequence.select(a, 3) as_int * (19 * Sequence.select(b, 3) as_int) + Sequence.select(a, 2) as_int * (19 * Sequence.select(b, 4) as_int)) mod 340282366920938463463374607431768211456
}
 function mul_c2_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  (Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 3) as_int) + Sequence.select(a, 3) as_int * (19 * Sequence.select(b, 4) as_int)) mod 340282366920938463463374607431768211456
}
 function mul_c3_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  (Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 4) as_int)) mod 340282366920938463463374607431768211456
}
 function mul_c4_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  (Sequence.select(a, 4) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 4) as_int) mod 340282366920938463463374607431768211456
}
 function mul_c0_val (a : Sequence bv64, b : Sequence bv64) : int {
  mul_c0_0_val(a, b)
}
 function mul_c1_val (a : Sequence bv64, b : Sequence bv64) : int {
  (mul_c1_0_val(a, b) + mul_c0_val(a, b) div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456
}
 function mul_c2_val (a : Sequence bv64, b : Sequence bv64) : int {
  (mul_c2_0_val(a, b) + mul_c1_val(a, b) div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456
}
 function mul_c3_val (a : Sequence bv64, b : Sequence bv64) : int {
  (mul_c3_0_val(a, b) + mul_c2_val(a, b) div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456
}
 function mul_c4_val (a : Sequence bv64, b : Sequence bv64) : int {
  (mul_c4_0_val(a, b) + mul_c3_val(a, b) div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456
}
 function mul_return (a : Sequence bv64, b : Sequence bv64) : Sequence bv64 {
  Sequence.of_bv64[((mul_c0_val(a, b) as_bv64 & mask51) as_int + mul_c4_val(a, b) div 2251799813685248 mod 18446744073709551616 * 19) as_bv64 & mask51, ((mul_c1_val(a, b) as_bv64 & mask51) as_int + (((mul_c0_val(a, b) as_bv64 & mask51) as_int + mul_c4_val(a, b) div 2251799813685248 mod 18446744073709551616 * 19) as_bv64 >> bv{64}(51)) as_int) as_bv64, mul_c2_val(a, b) as_bv64 & mask51, mul_c3_val(a, b) as_bv64 & mask51, mul_c4_val(a, b) as_bv64 & mask51]
}
 function mul_term_product_bounds_spec (a : Sequence bv64, b : Sequence bv64, bound : bv64) : bool {
  ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> Sequence.select(a, i) as_int * Sequence.select(b, j) as_int < bound as_int * bound as_int && ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> Sequence.select(a, i) as_int * (19 * Sequence.select(b, j) as_int mod 340282366920938463463374607431768211456) < 19 * (bound as_int * bound as_int)
}
 function mul_ci_0_val_boundaries (a : Sequence bv64, b : Sequence bv64, bound : bv64) : bool {
  mul_c0_0_val(a, b) < 77 * (bound as_int * bound as_int) && mul_c1_0_val(a, b) < 59 * (bound as_int * bound as_int) && mul_c2_0_val(a, b) < 41 * (bound as_int * bound as_int) && mul_c3_0_val(a, b) < 23 * (bound as_int * bound as_int) && mul_c4_0_val(a, b) < 5 * (bound as_int * bound as_int)
}
 function mul_ci_val_boundaries (a : Sequence bv64, b : Sequence bv64) : bool {
  mul_c0_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c1_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c2_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c3_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c4_val(a, b) div 2251799813685248 <= 18446744073709551615
}
 function mul_out_val_boundaries (a : Sequence bv64, b : Sequence bv64) : bool {
  mul_c0_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c1_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c2_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c3_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c4_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && (mul_c4_val(a, b) div 2251799813685248) as_bv64 < bv{64}(724618875532318195) && (mul_c0_val(a, b) as_bv64 & mask51) as_int + mul_c4_val(a, b) div 2251799813685248 mod 18446744073709551616 * 19 < 18446744073709551615 && (mul_c1_val(a, b) as_bv64 & mask51) as_int + (((mul_c0_val(a, b) as_bv64 & mask51) as_int + mul_c4_val(a, b) div 2251799813685248 mod 18446744073709551616 * 19) as_bv64 >> bv{64}(51)) as_int < ((bv{64}(1) << bv{64}(52)) as_int) as_int && (((mul_c0_val(a, b) as_bv64 & mask51) as_int + mul_c4_val(a, b) div 2251799813685248 mod 18446744073709551616 * 19) as_bv64 & mask51) as_int < ((bv{64}(1) << bv{64}(51)) as_int) as_int
}
 function mul_boundary_spec (a : Sequence bv64, b : Sequence bv64) : bool {
  bv{64}(19) * (bv{64}(1) << bv{64}(54)) <= bv{64}(18446744073709551615) && 77 * ((bv{64}(1) << bv{64}(54)) as_int * (bv{64}(1) << bv{64}(54)) as_int) <= 340282366920938463463374607431768211455 && mul_term_product_bounds_spec(a, b, bv{64}(1) << bv{64}(54)) && mul_ci_0_val_boundaries(a, b, bv{64}(1) << bv{64}(54)) && mul_ci_val_boundaries(a, b) && mul_out_val_boundaries(a, b) && Sequence.select(mul_return(a, b), 0) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 1) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 2) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 3) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 4) < bv{64}(1) << bv{64}(52) && bv{64}(1) << bv{64}(52) < bv{64}(1) << bv{64}(54)
}
 procedure Impl__2_clone (self : fieldElement51) returns (_pct_return : fieldElement51)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__2_clone;
};
 procedure m (x : bv64, y : bv64) returns (r : int)
spec {
  ensures r == x as_int * y as_int;
  ensures r <= 340282366920938463463374607431768211455;
  } {
  call Arithmetic_Mul_lemma_mul_upper_bound(x as_int, 18446744073709551615, y as_int, 18446744073709551615);
  assert [compute]: 18446744073709551615 * 18446744073709551615 <= 340282366920938463463374607431768211455;
  assert 0 <= x as_int * y as_int && x as_int * y as_int <= 340282366920938463463374607431768211455;
  assume 0 <= x as_int * y as_int && x as_int * y as_int <= 340282366920938463463374607431768211455;
  r := x as_int * y as_int mod 340282366920938463463374607431768211456;
  exit m;
};
 procedure Impl__3_mul (self : fieldElement51, _rhs : fieldElement51) returns (output : fieldElement51)
spec {
  requires fe51_limbs_bounded(self, bv{64}(54));
  requires fe51_limbs_bounded(_rhs, bv{64}(54));
  ensures nat.toInt(fe51_as_canonical_nat(output)) == nat.toInt(field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)));
  ensures fe51_limbs_bounded(output, bv{64}(52));
  ensures fe51_limbs_bounded(output, bv{64}(54));
  } {
  var tmp8 : int;
  var tmp10 : int;
  var tmp13 : int;
  var tmp16 : int;
  var tmp19 : int;
  var tmp24 : int;
  var tmp28 : int;
  var tmp31 : int;
  var tmp34 : int;
  var tmp37 : int;
  var tmp42 : int;
  var tmp46 : int;
  var tmp51 : int;
  var tmp54 : int;
  var tmp57 : int;
  var tmp62 : int;
  var tmp66 : int;
  var tmp71 : int;
  var tmp76 : int;
  var tmp79 : int;
  var tmp84 : int;
  var tmp88 : int;
  var tmp93 : int;
  var tmp98 : int;
  var tmp103 : int;
  var tmp128 : nat;
  var tmp129 : nat;
  var tmp130 : nat;
  var tmp131 : bool;
  var tmp132 : bool;
  var a : (Sequence bv64);
  var b : (Sequence bv64);
  var b1_19 : bv64;
  var b2_19 : bv64;
  var b3_19 : bv64;
  var b4_19 : bv64;
  var c0 : int;
  var c1 : int;
  var c2 : int;
  var c3 : int;
  var c4 : int;
  var out_ : (Sequence bv64);
  var carry : bv64;
  a := fieldElement51..limbs(self);
  b := fieldElement51..limbs(_rhs);
  call lemma_mul_boundary(a, b);
  assert 0 <= Sequence.select(b, 1) as_int * 19 && Sequence.select(b, 1) as_int * 19 <= 18446744073709551615;
  assume 0 <= Sequence.select(b, 1) as_int * 19 && Sequence.select(b, 1) as_int * 19 <= 18446744073709551615;
  b1_19 := Sequence.select(b, 1) * bv{64}(19);
  assert 0 <= Sequence.select(b, 2) as_int * 19 && Sequence.select(b, 2) as_int * 19 <= 18446744073709551615;
  assume 0 <= Sequence.select(b, 2) as_int * 19 && Sequence.select(b, 2) as_int * 19 <= 18446744073709551615;
  b2_19 := Sequence.select(b, 2) * bv{64}(19);
  assert 0 <= Sequence.select(b, 3) as_int * 19 && Sequence.select(b, 3) as_int * 19 <= 18446744073709551615;
  assume 0 <= Sequence.select(b, 3) as_int * 19 && Sequence.select(b, 3) as_int * 19 <= 18446744073709551615;
  b3_19 := Sequence.select(b, 3) * bv{64}(19);
  assert 0 <= Sequence.select(b, 4) as_int * 19 && Sequence.select(b, 4) as_int * 19 <= 18446744073709551615;
  assume 0 <= Sequence.select(b, 4) as_int * 19 && Sequence.select(b, 4) as_int * 19 <= 18446744073709551615;
  b4_19 := Sequence.select(b, 4) * bv{64}(19);
  call tmp8 := m(Sequence.select(a, 0), Sequence.select(b, 0));
  
  call tmp10 := m(Sequence.select(a, 4), b1_19);
  
  assert 0 <= tmp8 + tmp10 && tmp8 + tmp10 <= 340282366920938463463374607431768211455;
  assume 0 <= tmp8 + tmp10 && tmp8 + tmp10 <= 340282366920938463463374607431768211455;
  call tmp13 := m(Sequence.select(a, 3), b2_19);
  
  assert 0 <= (tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13 && (tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13 <= 340282366920938463463374607431768211455;
  assume 0 <= (tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13 && (tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13 <= 340282366920938463463374607431768211455;
  call tmp16 := m(Sequence.select(a, 2), b3_19);
  
  assert 0 <= ((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16 && ((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16 <= 340282366920938463463374607431768211455;
  assume 0 <= ((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16 && ((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16 <= 340282366920938463463374607431768211455;
  call tmp19 := m(Sequence.select(a, 1), b4_19);
  
  assert 0 <= (((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16) mod 340282366920938463463374607431768211456 + tmp19 && (((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16) mod 340282366920938463463374607431768211456 + tmp19 <= 340282366920938463463374607431768211455;
  assume 0 <= (((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16) mod 340282366920938463463374607431768211456 + tmp19 && (((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16) mod 340282366920938463463374607431768211456 + tmp19 <= 340282366920938463463374607431768211455;
  c0 := ((((tmp8 + tmp10) mod 340282366920938463463374607431768211456 + tmp13) mod 340282366920938463463374607431768211456 + tmp16) mod 340282366920938463463374607431768211456 + tmp19) mod 340282366920938463463374607431768211456;
  call tmp24 := m(Sequence.select(a, 1), Sequence.select(b, 0));
  
  call tmp28 := m(Sequence.select(a, 0), Sequence.select(b, 1));
  
  assert 0 <= tmp24 + tmp28 && tmp24 + tmp28 <= 340282366920938463463374607431768211455;
  assume 0 <= tmp24 + tmp28 && tmp24 + tmp28 <= 340282366920938463463374607431768211455;
  call tmp31 := m(Sequence.select(a, 4), b2_19);
  
  assert 0 <= (tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31 && (tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31 <= 340282366920938463463374607431768211455;
  assume 0 <= (tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31 && (tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31 <= 340282366920938463463374607431768211455;
  call tmp34 := m(Sequence.select(a, 3), b3_19);
  
  assert 0 <= ((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34 && ((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34 <= 340282366920938463463374607431768211455;
  assume 0 <= ((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34 && ((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34 <= 340282366920938463463374607431768211455;
  call tmp37 := m(Sequence.select(a, 2), b4_19);
  
  assert 0 <= (((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34) mod 340282366920938463463374607431768211456 + tmp37 && (((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34) mod 340282366920938463463374607431768211456 + tmp37 <= 340282366920938463463374607431768211455;
  assume 0 <= (((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34) mod 340282366920938463463374607431768211456 + tmp37 && (((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34) mod 340282366920938463463374607431768211456 + tmp37 <= 340282366920938463463374607431768211455;
  c1 := ((((tmp24 + tmp28) mod 340282366920938463463374607431768211456 + tmp31) mod 340282366920938463463374607431768211456 + tmp34) mod 340282366920938463463374607431768211456 + tmp37) mod 340282366920938463463374607431768211456;
  call tmp42 := m(Sequence.select(a, 2), Sequence.select(b, 0));
  
  call tmp46 := m(Sequence.select(a, 1), Sequence.select(b, 1));
  
  assert 0 <= tmp42 + tmp46 && tmp42 + tmp46 <= 340282366920938463463374607431768211455;
  assume 0 <= tmp42 + tmp46 && tmp42 + tmp46 <= 340282366920938463463374607431768211455;
  call tmp51 := m(Sequence.select(a, 0), Sequence.select(b, 2));
  
  assert 0 <= (tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51 && (tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51 <= 340282366920938463463374607431768211455;
  assume 0 <= (tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51 && (tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51 <= 340282366920938463463374607431768211455;
  call tmp54 := m(Sequence.select(a, 4), b3_19);
  
  assert 0 <= ((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54 && ((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54 <= 340282366920938463463374607431768211455;
  assume 0 <= ((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54 && ((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54 <= 340282366920938463463374607431768211455;
  call tmp57 := m(Sequence.select(a, 3), b4_19);
  
  assert 0 <= (((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54) mod 340282366920938463463374607431768211456 + tmp57 && (((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54) mod 340282366920938463463374607431768211456 + tmp57 <= 340282366920938463463374607431768211455;
  assume 0 <= (((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54) mod 340282366920938463463374607431768211456 + tmp57 && (((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54) mod 340282366920938463463374607431768211456 + tmp57 <= 340282366920938463463374607431768211455;
  c2 := ((((tmp42 + tmp46) mod 340282366920938463463374607431768211456 + tmp51) mod 340282366920938463463374607431768211456 + tmp54) mod 340282366920938463463374607431768211456 + tmp57) mod 340282366920938463463374607431768211456;
  call tmp62 := m(Sequence.select(a, 3), Sequence.select(b, 0));
  
  call tmp66 := m(Sequence.select(a, 2), Sequence.select(b, 1));
  
  assert 0 <= tmp62 + tmp66 && tmp62 + tmp66 <= 340282366920938463463374607431768211455;
  assume 0 <= tmp62 + tmp66 && tmp62 + tmp66 <= 340282366920938463463374607431768211455;
  call tmp71 := m(Sequence.select(a, 1), Sequence.select(b, 2));
  
  assert 0 <= (tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71 && (tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71 <= 340282366920938463463374607431768211455;
  assume 0 <= (tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71 && (tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71 <= 340282366920938463463374607431768211455;
  call tmp76 := m(Sequence.select(a, 0), Sequence.select(b, 3));
  
  assert 0 <= ((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76 && ((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76 <= 340282366920938463463374607431768211455;
  assume 0 <= ((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76 && ((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76 <= 340282366920938463463374607431768211455;
  call tmp79 := m(Sequence.select(a, 4), b4_19);
  
  assert 0 <= (((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76) mod 340282366920938463463374607431768211456 + tmp79 && (((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76) mod 340282366920938463463374607431768211456 + tmp79 <= 340282366920938463463374607431768211455;
  assume 0 <= (((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76) mod 340282366920938463463374607431768211456 + tmp79 && (((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76) mod 340282366920938463463374607431768211456 + tmp79 <= 340282366920938463463374607431768211455;
  c3 := ((((tmp62 + tmp66) mod 340282366920938463463374607431768211456 + tmp71) mod 340282366920938463463374607431768211456 + tmp76) mod 340282366920938463463374607431768211456 + tmp79) mod 340282366920938463463374607431768211456;
  call tmp84 := m(Sequence.select(a, 4), Sequence.select(b, 0));
  
  call tmp88 := m(Sequence.select(a, 3), Sequence.select(b, 1));
  
  assert 0 <= tmp84 + tmp88 && tmp84 + tmp88 <= 340282366920938463463374607431768211455;
  assume 0 <= tmp84 + tmp88 && tmp84 + tmp88 <= 340282366920938463463374607431768211455;
  call tmp93 := m(Sequence.select(a, 2), Sequence.select(b, 2));
  
  assert 0 <= (tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93 && (tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93 <= 340282366920938463463374607431768211455;
  assume 0 <= (tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93 && (tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93 <= 340282366920938463463374607431768211455;
  call tmp98 := m(Sequence.select(a, 1), Sequence.select(b, 3));
  
  assert 0 <= ((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98 && ((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98 <= 340282366920938463463374607431768211455;
  assume 0 <= ((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98 && ((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98 <= 340282366920938463463374607431768211455;
  call tmp103 := m(Sequence.select(a, 0), Sequence.select(b, 4));
  
  assert 0 <= (((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98) mod 340282366920938463463374607431768211456 + tmp103 && (((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98) mod 340282366920938463463374607431768211456 + tmp103 <= 340282366920938463463374607431768211455;
  assume 0 <= (((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98) mod 340282366920938463463374607431768211456 + tmp103 && (((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98) mod 340282366920938463463374607431768211456 + tmp103 <= 340282366920938463463374607431768211455;
  c4 := ((((tmp84 + tmp88) mod 340282366920938463463374607431768211456 + tmp93) mod 340282366920938463463374607431768211456 + tmp98) mod 340282366920938463463374607431768211456 + tmp103) mod 340282366920938463463374607431768211456;
  out_ := Sequence.of_bv64[bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)];
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= c1 + c0 div 2251799813685248 mod 18446744073709551616 && c1 + c0 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= c1 + c0 div 2251799813685248 mod 18446744073709551616 && c1 + c0 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c1 := (c1 + c0 div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456;
  out_ := Sequence.update(out_, 0, c0 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= c2 + c1 div 2251799813685248 mod 18446744073709551616 && c2 + c1 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= c2 + c1 div 2251799813685248 mod 18446744073709551616 && c2 + c1 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c2 := (c2 + c1 div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456;
  out_ := Sequence.update(out_, 1, c1 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= c3 + c2 div 2251799813685248 mod 18446744073709551616 && c3 + c2 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= c3 + c2 div 2251799813685248 mod 18446744073709551616 && c3 + c2 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c3 := (c3 + c2 div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456;
  out_ := Sequence.update(out_, 2, c2 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= c4 + c3 div 2251799813685248 mod 18446744073709551616 && c4 + c3 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= c4 + c3 div 2251799813685248 mod 18446744073709551616 && c4 + c3 div 2251799813685248 mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c4 := (c4 + c3 div 2251799813685248 mod 18446744073709551616) mod 340282366920938463463374607431768211456;
  out_ := Sequence.update(out_, 3, c3 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  carry := (c4 div 2251799813685248) as_bv64;
  out_ := Sequence.update(out_, 4, c4 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= carry as_int * 19 && carry as_int * 19 <= 18446744073709551615;
  assume 0 <= carry as_int * 19 && carry as_int * 19 <= 18446744073709551615;
  assert 0 <= Sequence.select(out_, 0) as_int + carry as_int * 19 mod 18446744073709551616 && Sequence.select(out_, 0) as_int + carry as_int * 19 mod 18446744073709551616 <= 18446744073709551615;
  assume 0 <= Sequence.select(out_, 0) as_int + carry as_int * 19 mod 18446744073709551616 && Sequence.select(out_, 0) as_int + carry as_int * 19 mod 18446744073709551616 <= 18446744073709551615;
  out_ := Sequence.update(out_, 0, Sequence.select(out_, 0) + carry * bv{64}(19));
  assert 0 <= 51 && 51 < 64;
  assume 0 <= 51 && 51 < 64;
  assert 0 <= Sequence.select(out_, 1) as_int + (Sequence.select(out_, 0) >> bv{64}(51)) as_int && Sequence.select(out_, 1) as_int + (Sequence.select(out_, 0) >> bv{64}(51)) as_int <= 18446744073709551615;
  assume 0 <= Sequence.select(out_, 1) as_int + (Sequence.select(out_, 0) >> bv{64}(51)) as_int && Sequence.select(out_, 1) as_int + (Sequence.select(out_, 0) >> bv{64}(51)) as_int <= 18446744073709551615;
  out_ := Sequence.update(out_, 1, Sequence.select(out_, 1) + (Sequence.select(out_, 0) >> bv{64}(51)));
  out_ := Sequence.update(out_, 0, Sequence.select(out_, 0) & lOW_51_BIT_MASK);
  call lemma_mul_value(a, b);
  assert out_ == mul_return(a, b);
  assume out_ == mul_return(a, b);
  assert nat.toInt(nat.mod(u64_5_as_nat(out_), p)) == nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p));
  assume nat.toInt(nat.mod(u64_5_as_nat(out_), p)) == nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p));
  call pow255_gt_19();
  tmp128 := u64_5_as_nat(a);
  tmp129 := u64_5_as_nat(b);
  tmp130 := p;
  call Arithmetic_Div_mod_lemma_mul_mod_noop_general(nat.toInt(tmp128), nat.toInt(tmp129), nat.toInt(tmp130));
  assert nat.toInt(fe51_as_canonical_nat(fieldElement51_ctor(out_))) == nat.toInt(field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)));
  assume nat.toInt(fe51_as_canonical_nat(fieldElement51_ctor(out_))) == nat.toInt(field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)));
  assert [compute]: bv{64}(1) << bv{64}(52) <= bv{64}(1) << bv{64}(54);
  tmp131 := fe51_limbs_bounded(fieldElement51_ctor(out_), bv{64}(52));
  assert tmp131;
  assume tmp131;
  tmp132 := fe51_limbs_bounded(fieldElement51_ctor(out_), bv{64}(54));
  assert tmp132;
  assume tmp132;
  output := fieldElement51_ctor(out_);
  exit Impl__3_mul;
};
 procedure Arithmetic_Div_mod_lemma_fundamental_div_mod (x : int, d : int) returns ()
spec {
  requires !(d == 0);
  ensures x == d * (x div d) + x mod d;
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_mod_twice (x : int, m : int) returns ()
spec {
  requires m > 0;
  ensures x mod m mod m == x mod m;
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_mod_multiples_basic (x : int, m : int) returns ()
spec {
  requires m > 0;
  ensures x * m mod m == 0;
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_add_mod_noop (x : int, y : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures (x mod m + y mod m) mod m == (x + y) mod m;
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_sub_mod_noop (x : int, y : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures (x mod m - y mod m) mod m == (x - y) mod m;
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_mul_mod_noop_general (x : int, y : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures x mod m * y mod m == x * y mod m;
  ensures x * (y mod m) mod m == x * y mod m;
  ensures x mod m * (y mod m) mod m == x * y mod m;
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_nonzero (x : int, y : int) returns ()
spec {
  ensures !(x * y == 0) == (!(x == 0) && !(y == 0));
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_is_associative (x : int, y : int, z : int) returns ()
spec {
  ensures x * (y * z) == x * y * z;
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_is_commutative (x : int, y : int) returns ()
spec {
  ensures x * y == y * x;
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_strict_inequality (x : int, y : int, z : int) returns ()
spec {
  requires x < y;
  requires z > 0;
  ensures x * z < y * z;
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_upper_bound (x : int, xbound : int, y : int, ybound : int) returns ()
spec {
  requires x <= xbound;
  requires y <= ybound;
  requires 0 <= x;
  requires 0 <= y;
  ensures x * y <= xbound * ybound;
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_is_distributive_add (x : int, y : int, z : int) returns ()
spec {
  ensures x * (y + z) == x * y + x * z;
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_is_distributive_sub (x : int, y : int, z : int) returns ()
spec {
  ensures x * (y - z) == x * y - x * z;
  } {
  assume false;
};
 procedure Arithmetic_Mul_lemma_mul_is_distributive_sub_other_way (x : int, y : int, z : int) returns ()
spec {
  ensures (y - z) * x == y * x - z * x;
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma_pow2_pos (e : nat) returns ()
spec {
  ensures nat.gt(Arithmetic_Power2_pow2(e), nat.fromInt(0));
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma_pow2_adds (e1 : nat, e2 : nat) returns ()
spec {
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.add(e1, e2))) == nat.toInt(Arithmetic_Power2_pow2(e1)) * nat.toInt(Arithmetic_Power2_pow2(e2));
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
 procedure Arithmetic_Power2_lemma2_to64_rest () returns ()
spec {
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(33))) == 8589934592;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(34))) == 17179869184;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(35))) == 34359738368;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(36))) == 68719476736;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(37))) == 137438953472;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(38))) == 274877906944;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(39))) == 549755813888;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(40))) == 1099511627776;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(41))) == 2199023255552;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(42))) == 4398046511104;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(43))) == 8796093022208;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(44))) == 17592186044416;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(45))) == 35184372088832;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(46))) == 70368744177664;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(47))) == 140737488355328;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(48))) == 281474976710656;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(49))) == 562949953421312;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(50))) == 1125899906842624;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) == 2251799813685248;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(52))) == 4503599627370496;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(53))) == 9007199254740992;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(54))) == 18014398509481984;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(55))) == 36028797018963968;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(56))) == 72057594037927936;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(57))) == 144115188075855872;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(58))) == 288230376151711744;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(59))) == 576460752303423488;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(60))) == 1152921504606846976;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(61))) == 2305843009213693952;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(62))) == 4611686018427387904;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
  ensures nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(64))) == 18446744073709551616;
  } {
  assume false;
};
 procedure Bits_lemma_u128_shr_is_div (x : int, shift : int) returns ()
spec {
  requires 0 <= shift && shift < 128;
  ensures x div int_pow2(shift) == x div nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(shift)));
  } {
  assume false;
};
 procedure Bits_lemma_u64_shr_is_div (x : bv64, shift : bv64) returns ()
spec {
  requires bv{64}(0) <= shift && shift < bv{64}(64);
  ensures ((x >> shift) as_int) as_int == x as_int div nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(shift as_int)));
  } {
  assume false;
};
 procedure Bits_lemma_u64_low_bits_mask_is_mod (x : bv64, n : nat) returns ()
spec {
  requires nat.toInt(n) < 64;
  ensures ((x & nat.toInt(Bits_low_bits_mask(n)) as_bv64) as_int) as_int == x as_int mod (nat.toInt(Arithmetic_Power2_pow2(n)) mod 18446744073709551616);
  } {
  assume false;
};
 procedure pow255_gt_19 () returns ()
spec {
  ensures nat.gt(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19));
  } {
  call Arithmetic_Power2_lemma2_to64();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(5), nat.fromInt(255));
  exit pow255_gt_19;
};
 procedure lemma_mul_lt (a1 : nat, b1 : nat, a2 : nat, b2 : nat) returns ()
spec {
  requires nat.lt(a1, b1);
  requires nat.lt(a2, b2);
  ensures nat.lt(nat.mul(a1, a2), nat.mul(b1, b2));
  } {
  if (nat.toInt(a2) == 0) {
    call Arithmetic_Mul_lemma_mul_nonzero(nat.toInt(b1), nat.toInt(b2));
    assert nat.gt(nat.mul(b1, b2), nat.fromInt(0));
    assume nat.gt(nat.mul(b1, b2), nat.fromInt(0));
  } else {
    call Arithmetic_Mul_lemma_mul_strict_inequality(nat.toInt(a1), nat.toInt(b1), nat.toInt(a2));
    call Arithmetic_Mul_lemma_mul_strict_inequality(nat.toInt(a2), nat.toInt(b2), nat.toInt(b1));
  }
  exit lemma_mul_lt;
};
 procedure lemma_m (x : bv64, y : bv64, bx : bv64, b_y : bv64) returns ()
spec {
  requires x < bx;
  requires y < b_y;
  ensures x as_int * y as_int < bx as_int * b_y as_int;
  } {
  call lemma_mul_lt(nat.fromInt(x as_int), nat.fromInt(bx as_int), nat.fromInt(y as_int), nat.fromInt(b_y as_int));
  exit lemma_m;
};
 procedure lemma_mul_term_product_bounds (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires bv{64}(19) * bound <= bv{64}(18446744073709551615);
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bound;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bound;
  ensures mul_term_product_bounds_spec(a, b, bound);
  } {
  var i : int;
  var j : int;
  var bound19 : bv64;
  bound19 := bv{64}(19) * bound;
  call Arithmetic_Mul_lemma_mul_is_associative(19, bound as_int, bound as_int);
  assert bound * (bv{64}(19) * bound) == bv{64}(19) * (bound * bound);
  assume bound * (bv{64}(19) * bound) == bv{64}(19) * (bound * bound);
  assume 0 <= i && i < 5 && (0 <= j && j < 5);
  call lemma_m(Sequence.select(a, i), Sequence.select(b, j), bound, bound);
  call lemma_m(Sequence.select(a, i), bv{64}(19) * Sequence.select(b, j), bound, bound19);
  assert Sequence.select(a, i) as_int * Sequence.select(b, j) as_int < bound as_int * bound as_int && Sequence.select(a, i) as_int * (19 * Sequence.select(b, j) as_int mod 340282366920938463463374607431768211456) < 19 * (bound as_int * bound as_int);
  assume ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> Sequence.select(a, i) as_int * Sequence.select(b, j) as_int < bound as_int * bound as_int && Sequence.select(a, i) as_int * (19 * Sequence.select(b, j) as_int mod 340282366920938463463374607431768211456) < 19 * (bound as_int * bound as_int);
  exit lemma_mul_term_product_bounds;
};
 procedure lemma_mul_c_i_0_bounded (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires bv{64}(19) * bound <= bv{64}(18446744073709551615);
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bound;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bound;
  ensures mul_ci_0_val_boundaries(a, b, bound);
  } {
  call lemma_mul_term_product_bounds(a, b, bound);
  exit lemma_mul_c_i_0_bounded;
};
 procedure lemma_shr_51_le (a : int, b : int) returns ()
spec {
  requires a <= b;
  ensures a div 2251799813685248 <= b div 2251799813685248;
  } {
  assert a <= b;
  assert [bitvector_query]: a <= b ==> a div 2251799813685248 <= b div 2251799813685248;
  exit lemma_shr_51_le;
};
 procedure lemma_shr_51_fits_u64 (a : int) returns ()
spec {
  requires a <= 18446744073709551615 * 2251799813685248;
  ensures a div 2251799813685248 <= 18446744073709551615;
  } {
  assert [compute]: 18446744073709551615 * 2251799813685248 div 2251799813685248 == 18446744073709551615;
  call lemma_shr_51_le(a, 18446744073709551615 * 2251799813685248);
  exit lemma_shr_51_fits_u64;
};
 procedure lemma_mul_c_i_shift_bounded (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires bv{64}(19) * bound <= bv{64}(18446744073709551615);
  requires 77 * (bound as_int * bound as_int) + 18446744073709551615 <= 18446744073709551615 * 2251799813685248;
  requires mul_ci_0_val_boundaries(a, b, bound);
  ensures mul_ci_val_boundaries(a, b);
  } {
  var tmp1 : int;
  var tmp2 : int;
  var tmp3 : int;
  var tmp4 : int;
  var tmp5 : int;
  tmp1 := mul_c0_val(a, b);
  call lemma_shr_51_fits_u64(tmp1);
  tmp2 := mul_c1_val(a, b);
  call lemma_shr_51_fits_u64(tmp2);
  tmp3 := mul_c2_val(a, b);
  call lemma_shr_51_fits_u64(tmp3);
  tmp4 := mul_c3_val(a, b);
  call lemma_shr_51_fits_u64(tmp4);
  tmp5 := mul_c4_val(a, b);
  call lemma_shr_51_fits_u64(tmp5);
  exit lemma_mul_c_i_shift_bounded;
};
 procedure lemma_masked_lt_51 (v : bv64) returns ()
spec {
  ensures v & mask51 < bv{64}(1) << bv{64}(51);
  } {
  assert [compute]: v & bv{64}(2251799813685247) < bv{64}(1) << bv{64}(51);
  assert [bitvector_query]: v & bv{64}(2251799813685247) < bv{64}(2251799813685248);
  exit lemma_masked_lt_51;
};
 procedure lemma_mul_boundary (a : Sequence bv64, b : Sequence bv64) returns ()
spec {
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bv{64}(1) << bv{64}(54);
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bv{64}(1) << bv{64}(54);
  ensures mul_boundary_spec(a, b);
  } {
  var c0 : int;
  var c1 : int;
  var c2 : int;
  var c3 : int;
  var c4 : int;
  var out0 : bv64;
  var out1 : bv64;
  var carry : bv64;
  var out0_1 : bv64;
  var pow2_5933 : bv64;
  var bound : bv64;
  var bound19 : bv64;
  var bound_sq : int;
  bound := bv{64}(1) << bv{64}(54);
  bound19 := bv{64}(19) * bound;
  bound_sq := 1 * 324518553658426726783156020576256;
  assert [compute]: (bv{64}(1) << bv{64}(54)) as_int mod 340282366920938463463374607431768211456 * ((bv{64}(1) << bv{64}(54)) as_int mod 340282366920938463463374607431768211456) == 1 * 324518553658426726783156020576256;
  assert bound as_int * bound as_int == bound_sq;
  assume bound as_int * bound as_int == bound_sq;
  assert [compute]: (bv{64}(1) << bv{64}(54)) as_int * (19 * (bv{64}(1) << bv{64}(54)) as_int mod 18446744073709551616) == 19 * (1 * 324518553658426726783156020576256);
  assert bound as_int * bound19 as_int == 19 * bound_sq;
  assume bound as_int * bound19 as_int == 19 * bound_sq;
  assert [compute]: bv{64}(19) * (bv{64}(1) << bv{64}(54)) <= bv{64}(18446744073709551615);
  assert bv{64}(19) * bound <= bv{64}(18446744073709551615);
  assume bv{64}(19) * bound <= bv{64}(18446744073709551615);
  call lemma_mul_term_product_bounds(a, b, bound);
  assert mul_term_product_bounds_spec(a, b, bound);
  assume mul_term_product_bounds_spec(a, b, bound);
  call lemma_mul_c_i_0_bounded(a, b, bound);
  assert mul_ci_0_val_boundaries(a, b, bound);
  assume mul_ci_0_val_boundaries(a, b, bound);
  assert [compute]: 77 * (1 * 324518553658426726783156020576256) + 18446744073709551615 <= 18446744073709551615 * 2251799813685248;
  assert 77 * bound_sq + 18446744073709551615 <= 18446744073709551615 * 2251799813685248;
  assume 77 * bound_sq + 18446744073709551615 <= 18446744073709551615 * 2251799813685248;
  call lemma_mul_c_i_shift_bounded(a, b, bound);
  assert mul_ci_val_boundaries(a, b);
  assume mul_ci_val_boundaries(a, b);
  c0 := mul_c0_val(a, b);
  c1 := mul_c1_val(a, b);
  c2 := mul_c2_val(a, b);
  c3 := mul_c3_val(a, b);
  c4 := mul_c4_val(a, b);
  out0 := c0 as_bv64 & mask51;
  out1 := c1 as_bv64 & mask51;
  carry := (c4 div 2251799813685248) as_bv64;
  out0_1 := out0 + carry * bv{64}(19);
  call lemma_masked_lt_51(c0 as_bv64);
  call lemma_masked_lt_51(c1 as_bv64);
  call lemma_masked_lt_51(c2 as_bv64);
  call lemma_masked_lt_51(c3 as_bv64);
  call lemma_masked_lt_51(c4 as_bv64);
  assert out0 < bv{64}(1) << bv{64}(51) && out1 < bv{64}(1) << bv{64}(51) && c2 as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && c3 as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && c4 as_bv64 & mask51 < bv{64}(1) << bv{64}(51);
  assume out0 < bv{64}(1) << bv{64}(51) && out1 < bv{64}(1) << bv{64}(51) && c2 as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && c3 as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && c4 as_bv64 & mask51 < bv{64}(1) << bv{64}(51);
  pow2_5933 := bv{64}(724618875532318195);
  call lemma_shr_51_le(c4, (5 * bound_sq + 18446744073709551615) mod 340282366920938463463374607431768211456);
  assert c4 div 2251799813685248 <= (5 * bound_sq + 18446744073709551615) mod 340282366920938463463374607431768211456 div 2251799813685248;
  assume c4 div 2251799813685248 <= (5 * bound_sq + 18446744073709551615) mod 340282366920938463463374607431768211456 div 2251799813685248;
  assert [compute]: (5 * (1 * 324518553658426726783156020576256) + 18446744073709551615) mod 340282366920938463463374607431768211456 div 2251799813685248 < 724618875532318195;
  assert carry < pow2_5933;
  assume carry < pow2_5933;
  assert [compute]: (bv{64}(1) << bv{64}(51)) + bv{64}(19) * bv{64}(724618875532318195) <= bv{64}(18446744073709551615);
  assert out0 + carry * bv{64}(19) < bv{64}(18446744073709551615);
  assume out0 + carry * bv{64}(19) < bv{64}(18446744073709551615);
  call lemma_shr_51_le(out0_1 as_int, 18446744073709551615);
  assert out0_1 as_int div 2251799813685248 <= 18446744073709551615 div 2251799813685248;
  assume out0_1 as_int div 2251799813685248 <= 18446744073709551615 div 2251799813685248;
  assert [compute]: 18446744073709551615 div 2251799813685248 < ((bv{64}(1) << bv{64}(13)) as_int) as_int;
  assert [compute]: (bv{64}(1) << bv{64}(51)) + (bv{64}(1) << bv{64}(13)) < bv{64}(1) << bv{64}(52);
  assert out1 + (out0_1 >> bv{64}(51)) < bv{64}(1) << bv{64}(52);
  assume out1 + (out0_1 >> bv{64}(51)) < bv{64}(1) << bv{64}(52);
  call lemma_masked_lt_51(out0_1);
  assert out0_1 & mask51 < bv{64}(1) << bv{64}(51);
  assume out0_1 & mask51 < bv{64}(1) << bv{64}(51);
  assert mul_out_val_boundaries(a, b);
  assume mul_out_val_boundaries(a, b);
  assert [compute]: bv{64}(1) << bv{64}(51) < bv{64}(1) << bv{64}(52) && bv{64}(1) << bv{64}(52) < bv{64}(1) << bv{64}(54);
  exit lemma_mul_boundary;
};
 procedure lemma_mul_distributive_3_terms (n : int, x1 : int, x2 : int, x3 : int) returns ()
spec {
  ensures n * (x1 + x2 + x3) == (x1 + x2 + x3) * n && (x1 + x2 + x3) * n == n * x1 + n * x2 + n * x3;
  } {
  call Arithmetic_Mul_lemma_mul_is_commutative(n, x1 + x2 + x3);
  assert n * (x1 + x2 + x3) == (x1 + x2 + x3) * n;
  assume n * (x1 + x2 + x3) == (x1 + x2 + x3) * n;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(n, x1 + x2, x3);
  assert n * (x1 + x2 + x3) == n * (x1 + x2) + n * x3;
  assume n * (x1 + x2 + x3) == n * (x1 + x2) + n * x3;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(n, x1, x2);
  assert n * (x1 + x2) == n * x1 + n * x2;
  assume n * (x1 + x2) == n * x1 + n * x2;
  exit lemma_mul_distributive_3_terms;
};
 procedure lemma_mul_distributive_4_terms (n : int, x1 : int, x2 : int, x3 : int, x4 : int) returns ()
spec {
  ensures n * (x1 + x2 + x3 + x4) == (x1 + x2 + x3 + x4) * n && (x1 + x2 + x3 + x4) * n == n * x1 + n * x2 + n * x3 + n * x4;
  } {
  call Arithmetic_Mul_lemma_mul_is_commutative(n, x1 + x2 + x3 + x4);
  assert n * (x1 + x2 + x3 + x4) == (x1 + x2 + x3 + x4) * n;
  assume n * (x1 + x2 + x3 + x4) == (x1 + x2 + x3 + x4) * n;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(n, x1 + x2 + x3, x4);
  assert n * (x1 + x2 + x3 + x4) == n * (x1 + x2 + x3) + n * x4;
  assume n * (x1 + x2 + x3 + x4) == n * (x1 + x2 + x3) + n * x4;
  call lemma_mul_distributive_3_terms(n, x1, x2, x3);
  assert n * (x1 + x2 + x3) == n * x1 + n * x2 + n * x3;
  assume n * (x1 + x2 + x3) == n * x1 + n * x2 + n * x3;
  exit lemma_mul_distributive_4_terms;
};
 procedure lemma_mul_distributive_5_terms (n : int, x1 : int, x2 : int, x3 : int, x4 : int, x5 : int) returns ()
spec {
  ensures n * (x1 + x2 + x3 + x4 + x5) == (x1 + x2 + x3 + x4 + x5) * n && (x1 + x2 + x3 + x4 + x5) * n == n * x1 + n * x2 + n * x3 + n * x4 + n * x5;
  } {
  call Arithmetic_Mul_lemma_mul_is_commutative(n, x1 + x2 + x3 + x4 + x5);
  assert n * (x1 + x2 + x3 + x4 + x5) == (x1 + x2 + x3 + x4 + x5) * n;
  assume n * (x1 + x2 + x3 + x4 + x5) == (x1 + x2 + x3 + x4 + x5) * n;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(n, x1 + x2 + x3 + x4, x5);
  assert n * (x1 + x2 + x3 + x4 + x5) == n * (x1 + x2 + x3 + x4) + n * x5;
  assume n * (x1 + x2 + x3 + x4 + x5) == n * (x1 + x2 + x3 + x4) + n * x5;
  call lemma_mul_distributive_4_terms(n, x1, x2, x3, x4);
  assert n * (x1 + x2 + x3 + x4) == n * x1 + n * x2 + n * x3 + n * x4;
  assume n * (x1 + x2 + x3 + x4) == n * x1 + n * x2 + n * x3 + n * x4;
  exit lemma_mul_distributive_5_terms;
};
 procedure lemma_mul_quad_prod (a1 : int, b1 : int, a2 : int, b2 : int) returns ()
spec {
  ensures a1 * b1 * (a2 * b2) == a1 * a2 * (b1 * b2);
  } {
  call Arithmetic_Mul_lemma_mul_is_associative(a1 * b1, a2, b2);
  call Arithmetic_Mul_lemma_mul_is_associative(a2, a1, b1);
  call Arithmetic_Mul_lemma_mul_is_associative(a2 * a1, b1, b2);
  exit lemma_mul_quad_prod;
};
 procedure lemma_mul_w0_and_reorder (w0 : int, v0 : int, s1 : int, v1 : int, s2 : int, v2 : int, s3 : int, v3 : int, s4 : int, v4 : int) returns ()
spec {
  ensures w0 * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) == s4 * (w0 * v4) + s3 * (w0 * v3) + s2 * (w0 * v2) + s1 * (w0 * v1) + w0 * v0;
  } {
  call lemma_mul_distributive_5_terms(w0, v0, s1 * v1, s2 * v2, s3 * v3, s4 * v4);
  call Arithmetic_Mul_lemma_mul_is_associative(w0, v1, s1);
  call Arithmetic_Mul_lemma_mul_is_associative(w0, v2, s2);
  call Arithmetic_Mul_lemma_mul_is_associative(w0, v3, s3);
  call Arithmetic_Mul_lemma_mul_is_associative(w0, v4, s4);
  exit lemma_mul_w0_and_reorder;
};
 procedure lemma_mul_si_vi_and_reorder (si : int, vi : int, v0 : int, s1 : int, v1 : int, s2 : int, v2 : int, s3 : int, v3 : int, s4 : int, v4 : int) returns ()
spec {
  ensures si * vi * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) == si * (vi * v0) + si * s1 * (vi * v1) + si * s2 * (vi * v2) + si * s3 * (vi * v3) + si * s4 * (vi * v4);
  } {
  call lemma_mul_distributive_5_terms(si * vi, v0, s1 * v1, s2 * v2, s3 * v3, s4 * v4);
  assert si * vi * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) == si * vi * v0 + si * vi * (s1 * v1) + si * vi * (s2 * v2) + si * vi * (s3 * v3) + si * vi * (s4 * v4);
  assume si * vi * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) == si * vi * v0 + si * vi * (s1 * v1) + si * vi * (s2 * v2) + si * vi * (s3 * v3) + si * vi * (s4 * v4);
  call Arithmetic_Mul_lemma_mul_is_associative(si, vi, v0);
  call lemma_mul_quad_prod(si, vi, s1, v1);
  call lemma_mul_quad_prod(si, vi, s2, v2);
  call lemma_mul_quad_prod(si, vi, s3, v3);
  call lemma_mul_quad_prod(si, vi, s4, v4);
  exit lemma_mul_si_vi_and_reorder;
};
 procedure lemma_mod_sum_factor (a : int, b : int, m : int) returns ()
spec {
  requires m > 0;
  ensures (a * m + b) mod m == b mod m;
  } {
  call Arithmetic_Div_mod_lemma_add_mod_noop(a * m, b, m);
  call Arithmetic_Div_mod_lemma_mod_multiples_basic(a, m);
  call Arithmetic_Div_mod_lemma_mod_twice(b, m);
  exit lemma_mod_sum_factor;
};
 procedure lemma_mod_diff_factor (a : int, b : int, m : int) returns ()
spec {
  requires m > 0;
  ensures (b - a * m) mod m == b mod m;
  } {
  call Arithmetic_Div_mod_lemma_sub_mod_noop(b, a * m, m);
  call Arithmetic_Div_mod_lemma_mod_multiples_basic(a, m);
  call Arithmetic_Div_mod_lemma_mod_twice(b, m);
  exit lemma_mod_diff_factor;
};
 procedure l51_bit_mask_lt () returns ()
spec {
  ensures mask51 as_int == nat.toInt(Bits_low_bits_mask(nat.fromInt(51)));
  ensures mask51 < bv{64}(1) << bv{64}(51);
  } {
  call Arithmetic_Power2_lemma2_to64_rest();
  assert [compute]: mask51 < bv{64}(1) << bv{64}(51);
  exit l51_bit_mask_lt;
};
 procedure lemma_u64_div_and_mod_51 (ai : bv64, bi : bv64, v : bv64) returns ()
spec {
  requires ai == v >> bv{64}(51);
  requires bi == v & mask51;
  ensures ai as_int == v as_int div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  ensures bi as_int == v as_int mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  ensures v as_int == ai as_int * nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) + bi as_int;
  } {
  var tmp1 : nat;
  var tmp2 : nat;
  call l51_bit_mask_lt();
  call Arithmetic_Power2_lemma_pow2_pos(nat.fromInt(51));
  call Arithmetic_Power2_lemma2_to64_rest();
  assert nat.lt(nat.fromInt(0), Arithmetic_Power2_pow2(nat.fromInt(51))) && nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) <= 18446744073709551615;
  assume nat.lt(nat.fromInt(0), Arithmetic_Power2_pow2(nat.fromInt(51))) && nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) <= 18446744073709551615;
  call Bits_lemma_u64_shr_is_div(v, 51 as_bv64);
  assert ai as_int == v as_int div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  assume ai as_int == v as_int div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  call Bits_lemma_u64_low_bits_mask_is_mod(v, nat.fromInt(51));
  assert bi as_int == v as_int mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  assume bi as_int == v as_int mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  tmp1 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Div_mod_lemma_fundamental_div_mod(v as_int, nat.toInt(tmp1));
  assert v as_int == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (v as_int div nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51)))) + v as_int mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51)));
  assume v as_int == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (v as_int div nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51)))) + v as_int mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51)));
  tmp2 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Mul_lemma_mul_is_commutative(ai as_int, nat.toInt(tmp2));
  exit lemma_u64_div_and_mod_51;
};
 procedure lemma_cast_then_mod_51 (x : int) returns ()
spec {
  ensures x mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616) == x mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456);
  } {
  call Arithmetic_Power2_lemma2_to64_rest();
  assert [bitvector_query]: x mod 18446744073709551616 mod 2251799813685248 == x mod 2251799813685248;
  exit lemma_cast_then_mod_51;
};
 procedure lemma_mul_sub (ci : int, cj : int, cj_0 : int, k : nat) returns ()
spec {
  ensures nat.toInt(Arithmetic_Power2_pow2(k)) * (ci - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (cj - cj_0)) == nat.toInt(Arithmetic_Power2_pow2(k)) * ci - nat.toInt(Arithmetic_Power2_pow2(nat.add(k, nat.fromInt(51)))) * cj + nat.toInt(Arithmetic_Power2_pow2(nat.add(k, nat.fromInt(51)))) * cj_0;
  } {
  var tmp1 : nat;
  var tmp3 : nat;
  var tmp4 : nat;
  var tmp6 : nat;
  tmp1 := Arithmetic_Power2_pow2(k);
  call Arithmetic_Mul_lemma_mul_is_distributive_sub(nat.toInt(tmp1), ci, nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (cj - cj_0));
  tmp3 := Arithmetic_Power2_pow2(k);
  tmp4 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(tmp3), nat.toInt(tmp4), cj - cj_0);
  call Arithmetic_Power2_lemma_pow2_adds(k, nat.fromInt(51));
  tmp6 := Arithmetic_Power2_pow2(nat.add(k, nat.fromInt(51)));
  call Arithmetic_Mul_lemma_mul_is_distributive_sub(nat.toInt(tmp6), cj, cj_0);
  exit lemma_mul_sub;
};
 procedure lemma_u64_5_as_nat_product (a : Sequence bv64, b : Sequence bv64) returns ()
spec {
  ensures nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(8), nat.fromInt(51)))) * (Sequence.select(a, 4) as_int * Sequence.select(b, 4) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(7), nat.fromInt(51)))) * (Sequence.select(a, 3) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 3) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(6), nat.fromInt(51)))) * (Sequence.select(a, 2) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 2) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(5), nat.fromInt(51)))) * (Sequence.select(a, 1) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 1) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(4), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 0) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(3), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(2), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(1), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int) + Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int;
  ensures nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p)) == (nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(4), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 0) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(3), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 4) as_int)) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(2), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 3) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 3) as_int)) + nat.toInt(Arithmetic_Power2_pow2(nat.mul(nat.fromInt(1), nat.fromInt(51)))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 2) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 2) as_int)) + (Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 1) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 1) as_int))) mod nat.toInt(p);
  } {
  var tmp1 : nat;
  var tmp39 : nat;
  var tmp40 : nat;
  var tmp41 : nat;
  var tmp42 : nat;
  var tmp46 : nat;
  var tmp47 : nat;
  var tmp48 : nat;
  var tmp49 : nat;
  var tmp52 : nat;
  var tmp55 : nat;
  var tmp60 : nat;
  var a0 : bv64;
  var a1 : bv64;
  var a2 : bv64;
  var a3 : bv64;
  var a4 : bv64;
  var b0 : bv64;
  var b1 : bv64;
  var b2 : bv64;
  var b3 : bv64;
  var b4 : bv64;
  var s1 : nat;
  var s2 : nat;
  var s3 : nat;
  var s4 : nat;
  var s5 : nat;
  var s6 : nat;
  var s7 : nat;
  var s8 : nat;
  var c0_x19 : int;
  var c1_x19 : int;
  var c2_x19 : int;
  var c3_x19 : int;
  var c0_base : int;
  var c1_base : int;
  var c2_base : int;
  var c3_base : int;
  var c4 : int;
  var c0 : int;
  var c1 : int;
  var c2 : int;
  var c3 : int;
  var k : int;
  var sum : int;
  a0 := Sequence.select(a, 0);
  a1 := Sequence.select(a, 1);
  a2 := Sequence.select(a, 2);
  a3 := Sequence.select(a, 3);
  a4 := Sequence.select(a, 4);
  b0 := Sequence.select(b, 0);
  b1 := Sequence.select(b, 1);
  b2 := Sequence.select(b, 2);
  b3 := Sequence.select(b, 3);
  b4 := Sequence.select(b, 4);
  s1 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(1), nat.fromInt(51)));
  s2 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(2), nat.fromInt(51)));
  s3 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(3), nat.fromInt(51)));
  s4 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(4), nat.fromInt(51)));
  s5 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(5), nat.fromInt(51)));
  s6 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(6), nat.fromInt(51)));
  s7 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(7), nat.fromInt(51)));
  s8 := Arithmetic_Power2_pow2(nat.mul(nat.fromInt(8), nat.fromInt(51)));
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(51), nat.fromInt(51));
  assert nat.toInt(s1) * nat.toInt(s1) == nat.toInt(s2);
  assume nat.toInt(s1) * nat.toInt(s1) == nat.toInt(s2);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(51), nat.fromInt(102));
  assert nat.toInt(s1) * nat.toInt(s2) == nat.toInt(s2) * nat.toInt(s1) && nat.toInt(s2) * nat.toInt(s1) == nat.toInt(s3);
  assume nat.toInt(s1) * nat.toInt(s2) == nat.toInt(s2) * nat.toInt(s1) && nat.toInt(s2) * nat.toInt(s1) == nat.toInt(s3);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(51), nat.fromInt(153));
  assert nat.toInt(s1) * nat.toInt(s3) == nat.toInt(s3) * nat.toInt(s1) && nat.toInt(s3) * nat.toInt(s1) == nat.toInt(s4);
  assume nat.toInt(s1) * nat.toInt(s3) == nat.toInt(s3) * nat.toInt(s1) && nat.toInt(s3) * nat.toInt(s1) == nat.toInt(s4);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(51), nat.fromInt(204));
  assert nat.toInt(s1) * nat.toInt(s4) == nat.toInt(s4) * nat.toInt(s1) && nat.toInt(s4) * nat.toInt(s1) == nat.toInt(s5);
  assume nat.toInt(s1) * nat.toInt(s4) == nat.toInt(s4) * nat.toInt(s1) && nat.toInt(s4) * nat.toInt(s1) == nat.toInt(s5);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(102), nat.fromInt(102));
  assert nat.toInt(s2) * nat.toInt(s2) == nat.toInt(s4);
  assume nat.toInt(s2) * nat.toInt(s2) == nat.toInt(s4);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(102), nat.fromInt(153));
  assert nat.toInt(s2) * nat.toInt(s3) == nat.toInt(s3) * nat.toInt(s2) && nat.toInt(s3) * nat.toInt(s2) == nat.toInt(s5);
  assume nat.toInt(s2) * nat.toInt(s3) == nat.toInt(s3) * nat.toInt(s2) && nat.toInt(s3) * nat.toInt(s2) == nat.toInt(s5);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(102), nat.fromInt(204));
  assert nat.toInt(s2) * nat.toInt(s4) == nat.toInt(s4) * nat.toInt(s2) && nat.toInt(s4) * nat.toInt(s2) == nat.toInt(s6);
  assume nat.toInt(s2) * nat.toInt(s4) == nat.toInt(s4) * nat.toInt(s2) && nat.toInt(s4) * nat.toInt(s2) == nat.toInt(s6);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(153), nat.fromInt(153));
  assert nat.toInt(s3) * nat.toInt(s3) == nat.toInt(s6);
  assume nat.toInt(s3) * nat.toInt(s3) == nat.toInt(s6);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(153), nat.fromInt(204));
  assert nat.toInt(s3) * nat.toInt(s4) == nat.toInt(s4) * nat.toInt(s3) && nat.toInt(s4) * nat.toInt(s3) == nat.toInt(s7);
  assume nat.toInt(s3) * nat.toInt(s4) == nat.toInt(s4) * nat.toInt(s3) && nat.toInt(s4) * nat.toInt(s3) == nat.toInt(s7);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(204), nat.fromInt(204));
  assert nat.toInt(s4) * nat.toInt(s4) == nat.toInt(s8);
  assume nat.toInt(s4) * nat.toInt(s4) == nat.toInt(s8);
  tmp1 := u64_5_as_nat(b);
  call lemma_mul_distributive_5_terms(nat.toInt(tmp1), a0 as_int, nat.toInt(s1) * a1 as_int, nat.toInt(s2) * a2 as_int, nat.toInt(s3) * a3 as_int, nat.toInt(s4) * a4 as_int);
  assert nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == a0 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s1) * a1 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s2) * a2 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s3) * a3 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s4) * a4 as_int * nat.toInt(u64_5_as_nat(b));
  assume nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == a0 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s1) * a1 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s2) * a2 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s3) * a3 as_int * nat.toInt(u64_5_as_nat(b)) + nat.toInt(s4) * a4 as_int * nat.toInt(u64_5_as_nat(b));
  call lemma_mul_w0_and_reorder(a0 as_int, b0 as_int, nat.toInt(s1), b1 as_int, nat.toInt(s2), b2 as_int, nat.toInt(s3), b3 as_int, nat.toInt(s4), b4 as_int);
  assert a0 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s4) * (a0 as_int * b4 as_int) + nat.toInt(s3) * (a0 as_int * b3 as_int) + nat.toInt(s2) * (a0 as_int * b2 as_int) + nat.toInt(s1) * (a0 as_int * b1 as_int) + a0 as_int * b0 as_int;
  assume a0 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s4) * (a0 as_int * b4 as_int) + nat.toInt(s3) * (a0 as_int * b3 as_int) + nat.toInt(s2) * (a0 as_int * b2 as_int) + nat.toInt(s1) * (a0 as_int * b1 as_int) + a0 as_int * b0 as_int;
  call lemma_mul_si_vi_and_reorder(nat.toInt(s1), a1 as_int, b0 as_int, nat.toInt(s1), b1 as_int, nat.toInt(s2), b2 as_int, nat.toInt(s3), b3 as_int, nat.toInt(s4), b4 as_int);
  assert nat.toInt(s1) * a1 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s5) * (a1 as_int * b4 as_int) + nat.toInt(s4) * (a1 as_int * b3 as_int) + nat.toInt(s3) * (a1 as_int * b2 as_int) + nat.toInt(s2) * (a1 as_int * b1 as_int) + nat.toInt(s1) * (a1 as_int * b0 as_int);
  assume nat.toInt(s1) * a1 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s5) * (a1 as_int * b4 as_int) + nat.toInt(s4) * (a1 as_int * b3 as_int) + nat.toInt(s3) * (a1 as_int * b2 as_int) + nat.toInt(s2) * (a1 as_int * b1 as_int) + nat.toInt(s1) * (a1 as_int * b0 as_int);
  call lemma_mul_si_vi_and_reorder(nat.toInt(s2), a2 as_int, b0 as_int, nat.toInt(s1), b1 as_int, nat.toInt(s2), b2 as_int, nat.toInt(s3), b3 as_int, nat.toInt(s4), b4 as_int);
  assert nat.toInt(s2) * a2 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s6) * (a2 as_int * b4 as_int) + nat.toInt(s5) * (a2 as_int * b3 as_int) + nat.toInt(s4) * (a2 as_int * b2 as_int) + nat.toInt(s3) * (a2 as_int * b1 as_int) + nat.toInt(s2) * (a2 as_int * b0 as_int);
  assume nat.toInt(s2) * a2 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s6) * (a2 as_int * b4 as_int) + nat.toInt(s5) * (a2 as_int * b3 as_int) + nat.toInt(s4) * (a2 as_int * b2 as_int) + nat.toInt(s3) * (a2 as_int * b1 as_int) + nat.toInt(s2) * (a2 as_int * b0 as_int);
  call lemma_mul_si_vi_and_reorder(nat.toInt(s3), a3 as_int, b0 as_int, nat.toInt(s1), b1 as_int, nat.toInt(s2), b2 as_int, nat.toInt(s3), b3 as_int, nat.toInt(s4), b4 as_int);
  assert nat.toInt(s3) * a3 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s7) * (a3 as_int * b4 as_int) + nat.toInt(s6) * (a3 as_int * b3 as_int) + nat.toInt(s5) * (a3 as_int * b2 as_int) + nat.toInt(s4) * (a3 as_int * b1 as_int) + nat.toInt(s3) * (a3 as_int * b0 as_int);
  assume nat.toInt(s3) * a3 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s7) * (a3 as_int * b4 as_int) + nat.toInt(s6) * (a3 as_int * b3 as_int) + nat.toInt(s5) * (a3 as_int * b2 as_int) + nat.toInt(s4) * (a3 as_int * b1 as_int) + nat.toInt(s3) * (a3 as_int * b0 as_int);
  call lemma_mul_si_vi_and_reorder(nat.toInt(s4), a4 as_int, b0 as_int, nat.toInt(s1), b1 as_int, nat.toInt(s2), b2 as_int, nat.toInt(s3), b3 as_int, nat.toInt(s4), b4 as_int);
  assert nat.toInt(s4) * a4 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s8) * (a4 as_int * b4 as_int) + nat.toInt(s7) * (a4 as_int * b3 as_int) + nat.toInt(s6) * (a4 as_int * b2 as_int) + nat.toInt(s5) * (a4 as_int * b1 as_int) + nat.toInt(s4) * (a4 as_int * b0 as_int);
  assume nat.toInt(s4) * a4 as_int * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s8) * (a4 as_int * b4 as_int) + nat.toInt(s7) * (a4 as_int * b3 as_int) + nat.toInt(s6) * (a4 as_int * b2 as_int) + nat.toInt(s5) * (a4 as_int * b1 as_int) + nat.toInt(s4) * (a4 as_int * b0 as_int);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s1), a0 as_int * b1 as_int, a1 as_int * b0 as_int);
  assert nat.toInt(s1) * (a0 as_int * b1 as_int) + nat.toInt(s1) * (a1 as_int * b0 as_int) == nat.toInt(s1) * (a0 as_int * b1 as_int + a1 as_int * b0 as_int);
  assume nat.toInt(s1) * (a0 as_int * b1 as_int) + nat.toInt(s1) * (a1 as_int * b0 as_int) == nat.toInt(s1) * (a0 as_int * b1 as_int + a1 as_int * b0 as_int);
  call lemma_mul_distributive_3_terms(nat.toInt(s2), a0 as_int * b2 as_int, a1 as_int * b1 as_int, a2 as_int * b0 as_int);
  assert nat.toInt(s2) * (a0 as_int * b2 as_int) + nat.toInt(s2) * (a1 as_int * b1 as_int) + nat.toInt(s2) * (a2 as_int * b0 as_int) == nat.toInt(s2) * (a0 as_int * b2 as_int + a1 as_int * b1 as_int + a2 as_int * b0 as_int);
  assume nat.toInt(s2) * (a0 as_int * b2 as_int) + nat.toInt(s2) * (a1 as_int * b1 as_int) + nat.toInt(s2) * (a2 as_int * b0 as_int) == nat.toInt(s2) * (a0 as_int * b2 as_int + a1 as_int * b1 as_int + a2 as_int * b0 as_int);
  call lemma_mul_distributive_4_terms(nat.toInt(s3), a0 as_int * b3 as_int, a1 as_int * b2 as_int, a2 as_int * b1 as_int, a3 as_int * b0 as_int);
  assert nat.toInt(s3) * (a0 as_int * b3 as_int) + nat.toInt(s3) * (a1 as_int * b2 as_int) + nat.toInt(s3) * (a2 as_int * b1 as_int) + nat.toInt(s3) * (a3 as_int * b0 as_int) == nat.toInt(s3) * (a0 as_int * b3 as_int + a1 as_int * b2 as_int + a2 as_int * b1 as_int + a3 as_int * b0 as_int);
  assume nat.toInt(s3) * (a0 as_int * b3 as_int) + nat.toInt(s3) * (a1 as_int * b2 as_int) + nat.toInt(s3) * (a2 as_int * b1 as_int) + nat.toInt(s3) * (a3 as_int * b0 as_int) == nat.toInt(s3) * (a0 as_int * b3 as_int + a1 as_int * b2 as_int + a2 as_int * b1 as_int + a3 as_int * b0 as_int);
  call lemma_mul_distributive_5_terms(nat.toInt(s4), a0 as_int * b4 as_int, a1 as_int * b3 as_int, a2 as_int * b2 as_int, a3 as_int * b1 as_int, a4 as_int * b0 as_int);
  assert nat.toInt(s4) * (a0 as_int * b4 as_int) + nat.toInt(s4) * (a1 as_int * b3 as_int) + nat.toInt(s4) * (a2 as_int * b2 as_int) + nat.toInt(s4) * (a3 as_int * b1 as_int) + nat.toInt(s4) * (a4 as_int * b0 as_int) == nat.toInt(s4) * (a0 as_int * b4 as_int + a1 as_int * b3 as_int + a2 as_int * b2 as_int + a3 as_int * b1 as_int + a4 as_int * b0 as_int);
  assume nat.toInt(s4) * (a0 as_int * b4 as_int) + nat.toInt(s4) * (a1 as_int * b3 as_int) + nat.toInt(s4) * (a2 as_int * b2 as_int) + nat.toInt(s4) * (a3 as_int * b1 as_int) + nat.toInt(s4) * (a4 as_int * b0 as_int) == nat.toInt(s4) * (a0 as_int * b4 as_int + a1 as_int * b3 as_int + a2 as_int * b2 as_int + a3 as_int * b1 as_int + a4 as_int * b0 as_int);
  call lemma_mul_distributive_4_terms(nat.toInt(s5), a1 as_int * b4 as_int, a2 as_int * b3 as_int, a3 as_int * b2 as_int, a4 as_int * b1 as_int);
  assert nat.toInt(s5) * (a1 as_int * b4 as_int) + nat.toInt(s5) * (a2 as_int * b3 as_int) + nat.toInt(s5) * (a3 as_int * b2 as_int) + nat.toInt(s5) * (a4 as_int * b1 as_int) == nat.toInt(s5) * (a1 as_int * b4 as_int + a2 as_int * b3 as_int + a3 as_int * b2 as_int + a4 as_int * b1 as_int);
  assume nat.toInt(s5) * (a1 as_int * b4 as_int) + nat.toInt(s5) * (a2 as_int * b3 as_int) + nat.toInt(s5) * (a3 as_int * b2 as_int) + nat.toInt(s5) * (a4 as_int * b1 as_int) == nat.toInt(s5) * (a1 as_int * b4 as_int + a2 as_int * b3 as_int + a3 as_int * b2 as_int + a4 as_int * b1 as_int);
  call lemma_mul_distributive_3_terms(nat.toInt(s6), a2 as_int * b4 as_int, a3 as_int * b3 as_int, a4 as_int * b2 as_int);
  assert nat.toInt(s6) * (a2 as_int * b4 as_int) + nat.toInt(s6) * (a3 as_int * b3 as_int) + nat.toInt(s6) * (a4 as_int * b2 as_int) == nat.toInt(s6) * (a2 as_int * b4 as_int + a3 as_int * b3 as_int + a4 as_int * b2 as_int);
  assume nat.toInt(s6) * (a2 as_int * b4 as_int) + nat.toInt(s6) * (a3 as_int * b3 as_int) + nat.toInt(s6) * (a4 as_int * b2 as_int) == nat.toInt(s6) * (a2 as_int * b4 as_int + a3 as_int * b3 as_int + a4 as_int * b2 as_int);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s7), a3 as_int * b4 as_int, a4 as_int * b3 as_int);
  assert nat.toInt(s7) * (a3 as_int * b4 as_int) + nat.toInt(s7) * (a4 as_int * b3 as_int) == nat.toInt(s7) * (a3 as_int * b4 as_int + a4 as_int * b3 as_int);
  assume nat.toInt(s7) * (a3 as_int * b4 as_int) + nat.toInt(s7) * (a4 as_int * b3 as_int) == nat.toInt(s7) * (a3 as_int * b4 as_int + a4 as_int * b3 as_int);
  assert nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s8) * (a4 as_int * b4 as_int) + nat.toInt(s7) * (a3 as_int * b4 as_int + a4 as_int * b3 as_int) + nat.toInt(s6) * (a2 as_int * b4 as_int + a3 as_int * b3 as_int + a4 as_int * b2 as_int) + nat.toInt(s5) * (a1 as_int * b4 as_int + a2 as_int * b3 as_int + a3 as_int * b2 as_int + a4 as_int * b1 as_int) + nat.toInt(s4) * (a0 as_int * b4 as_int + a1 as_int * b3 as_int + a2 as_int * b2 as_int + a3 as_int * b1 as_int + a4 as_int * b0 as_int) + nat.toInt(s3) * (a0 as_int * b3 as_int + a1 as_int * b2 as_int + a2 as_int * b1 as_int + a3 as_int * b0 as_int) + nat.toInt(s2) * (a0 as_int * b2 as_int + a1 as_int * b1 as_int + a2 as_int * b0 as_int) + nat.toInt(s1) * (a0 as_int * b1 as_int + a1 as_int * b0 as_int) + a0 as_int * b0 as_int;
  assume nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s8) * (a4 as_int * b4 as_int) + nat.toInt(s7) * (a3 as_int * b4 as_int + a4 as_int * b3 as_int) + nat.toInt(s6) * (a2 as_int * b4 as_int + a3 as_int * b3 as_int + a4 as_int * b2 as_int) + nat.toInt(s5) * (a1 as_int * b4 as_int + a2 as_int * b3 as_int + a3 as_int * b2 as_int + a4 as_int * b1 as_int) + nat.toInt(s4) * (a0 as_int * b4 as_int + a1 as_int * b3 as_int + a2 as_int * b2 as_int + a3 as_int * b1 as_int + a4 as_int * b0 as_int) + nat.toInt(s3) * (a0 as_int * b3 as_int + a1 as_int * b2 as_int + a2 as_int * b1 as_int + a3 as_int * b0 as_int) + nat.toInt(s2) * (a0 as_int * b2 as_int + a1 as_int * b1 as_int + a2 as_int * b0 as_int) + nat.toInt(s1) * (a0 as_int * b1 as_int + a1 as_int * b0 as_int) + a0 as_int * b0 as_int;
  call pow255_gt_19();
  assert nat.toInt(s5) == nat.toInt(p) + 19;
  assume nat.toInt(s5) == nat.toInt(p) + 19;
  c0_x19 := Sequence.select(a, 1) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 1) as_int;
  c1_x19 := Sequence.select(a, 2) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 2) as_int;
  c2_x19 := Sequence.select(a, 3) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 3) as_int;
  c3_x19 := Sequence.select(a, 4) as_int * Sequence.select(b, 4) as_int;
  c0_base := Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int;
  c1_base := Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int;
  c2_base := Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int;
  c3_base := Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int;
  c4 := Sequence.select(a, 0) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 0) as_int;
  c0 := c0_base + 19 * c0_x19;
  c1 := c1_base + 19 * c1_x19;
  c2 := c2_base + 19 * c2_x19;
  c3 := c3_base + 19 * c3_x19;
  call Arithmetic_Power2_lemma_pow2_adds(nat.mul(nat.fromInt(3), nat.fromInt(51)), nat.mul(nat.fromInt(5), nat.fromInt(51)));
  assert nat.toInt(s8) == nat.toInt(s3) * nat.toInt(s5);
  assume nat.toInt(s8) == nat.toInt(s3) * nat.toInt(s5);
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(s3), nat.toInt(s5), c3_x19);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s3), nat.toInt(s5) * c3_x19, c3_base);
  assert nat.toInt(s8) * c3_x19 + nat.toInt(s3) * c3_base == nat.toInt(s3) * (nat.toInt(s5) * c3_x19 + c3_base);
  assume nat.toInt(s8) * c3_x19 + nat.toInt(s3) * c3_base == nat.toInt(s3) * (nat.toInt(s5) * c3_x19 + c3_base);
  call Arithmetic_Power2_lemma_pow2_adds(nat.mul(nat.fromInt(2), nat.fromInt(51)), nat.mul(nat.fromInt(5), nat.fromInt(51)));
  assert nat.toInt(s7) == nat.toInt(s2) * nat.toInt(s5);
  assume nat.toInt(s7) == nat.toInt(s2) * nat.toInt(s5);
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(s2), nat.toInt(s5), c2_x19);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s2), nat.toInt(s5) * c2_x19, c2_base);
  assert nat.toInt(s7) * c2_x19 + nat.toInt(s2) * c2_base == nat.toInt(s2) * (nat.toInt(s5) * c2_x19 + c2_base);
  assume nat.toInt(s7) * c2_x19 + nat.toInt(s2) * c2_base == nat.toInt(s2) * (nat.toInt(s5) * c2_x19 + c2_base);
  call Arithmetic_Power2_lemma_pow2_adds(nat.mul(nat.fromInt(1), nat.fromInt(51)), nat.mul(nat.fromInt(5), nat.fromInt(51)));
  assert nat.toInt(s6) == nat.toInt(s1) * nat.toInt(s5);
  assume nat.toInt(s6) == nat.toInt(s1) * nat.toInt(s5);
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(s1), nat.toInt(s5), c1_x19);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s1), nat.toInt(s5) * c1_x19, c1_base);
  assert nat.toInt(s6) * c1_x19 + nat.toInt(s1) * c1_base == nat.toInt(s1) * (nat.toInt(s5) * c1_x19 + c1_base);
  assume nat.toInt(s6) * c1_x19 + nat.toInt(s1) * c1_base == nat.toInt(s1) * (nat.toInt(s5) * c1_x19 + c1_base);
  assert nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s4) * c4 + nat.toInt(s3) * (nat.toInt(s5) * c3_x19 + c3_base) + nat.toInt(s2) * (nat.toInt(s5) * c2_x19 + c2_base) + nat.toInt(s1) * (nat.toInt(s5) * c1_x19 + c1_base) + (nat.toInt(s5) * c0_x19 + c0_base);
  assume nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == nat.toInt(s4) * c4 + nat.toInt(s3) * (nat.toInt(s5) * c3_x19 + c3_base) + nat.toInt(s2) * (nat.toInt(s5) * c2_x19 + c2_base) + nat.toInt(s1) * (nat.toInt(s5) * c1_x19 + c1_base) + (nat.toInt(s5) * c0_x19 + c0_base);
  tmp39 := p;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(c3_x19, nat.toInt(tmp39), 19);
  assert nat.toInt(s5) * c3_x19 + c3_base == nat.toInt(p) * c3_x19 + c3;
  assume nat.toInt(s5) * c3_x19 + c3_base == nat.toInt(p) * c3_x19 + c3;
  tmp40 := p;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(c2_x19, nat.toInt(tmp40), 19);
  assert nat.toInt(s5) * c2_x19 + c2_base == nat.toInt(p) * c2_x19 + c2;
  assume nat.toInt(s5) * c2_x19 + c2_base == nat.toInt(p) * c2_x19 + c2;
  tmp41 := p;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(c1_x19, nat.toInt(tmp41), 19);
  assert nat.toInt(s5) * c1_x19 + c1_base == nat.toInt(p) * c1_x19 + c1;
  assume nat.toInt(s5) * c1_x19 + c1_base == nat.toInt(p) * c1_x19 + c1;
  tmp42 := p;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(c0_x19, nat.toInt(tmp42), 19);
  assert nat.toInt(s5) * c0_x19 + c0_base == nat.toInt(p) * c0_x19 + c0;
  assume nat.toInt(s5) * c0_x19 + c0_base == nat.toInt(p) * c0_x19 + c0;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s3), nat.toInt(p) * c3_x19, c3);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s2), nat.toInt(p) * c2_x19, c2);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(s1), nat.toInt(p) * c1_x19, c1);
  tmp46 := p;
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(s3), c3_x19, nat.toInt(tmp46));
  tmp47 := p;
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(s2), c2_x19, nat.toInt(tmp47));
  tmp48 := p;
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(s1), c1_x19, nat.toInt(tmp48));
  tmp49 := p;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(tmp49), nat.toInt(s3) * c3_x19, nat.toInt(s2) * c2_x19);
  tmp52 := p;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(tmp52), nat.toInt(s3) * c3_x19 + nat.toInt(s2) * c2_x19, nat.toInt(s1) * c1_x19);
  tmp55 := p;
  call Arithmetic_Mul_lemma_mul_is_distributive_add(nat.toInt(tmp55), nat.toInt(s3) * c3_x19 + nat.toInt(s2) * c2_x19 + nat.toInt(s1) * c1_x19, c0_x19);
  assert nat.toInt(s3) * (nat.toInt(p) * c3_x19) + nat.toInt(s2) * (nat.toInt(p) * c2_x19) + nat.toInt(s1) * (nat.toInt(p) * c1_x19) + nat.toInt(p) * c0_x19 == nat.toInt(p) * (nat.toInt(s3) * c3_x19 + nat.toInt(s2) * c2_x19 + nat.toInt(s1) * c1_x19 + c0_x19);
  assume nat.toInt(s3) * (nat.toInt(p) * c3_x19) + nat.toInt(s2) * (nat.toInt(p) * c2_x19) + nat.toInt(s1) * (nat.toInt(p) * c1_x19) + nat.toInt(p) * c0_x19 == nat.toInt(p) * (nat.toInt(s3) * c3_x19 + nat.toInt(s2) * c2_x19 + nat.toInt(s1) * c1_x19 + c0_x19);
  assert nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == nat.toInt(p) * (nat.toInt(s3) * c3_x19 + nat.toInt(s2) * c2_x19 + nat.toInt(s1) * c1_x19 + c0_x19) + (nat.toInt(s4) * c4 + nat.toInt(s3) * c3 + nat.toInt(s2) * c2 + nat.toInt(s1) * c1 + c0);
  assume nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == nat.toInt(p) * (nat.toInt(s3) * c3_x19 + nat.toInt(s2) * c2_x19 + nat.toInt(s1) * c1_x19 + c0_x19) + (nat.toInt(s4) * c4 + nat.toInt(s3) * c3 + nat.toInt(s2) * c2 + nat.toInt(s1) * c1 + c0);
  k := nat.toInt(s3) * c3_x19 + nat.toInt(s2) * c2_x19 + nat.toInt(s1) * c1_x19 + c0_x19;
  sum := nat.toInt(s4) * c4 + nat.toInt(s3) * c3 + nat.toInt(s2) * c2 + nat.toInt(s1) * c1 + c0;
  assert nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == k * nat.toInt(p) + sum;
  assume nat.toInt(u64_5_as_nat(a)) * nat.toInt(u64_5_as_nat(b)) == k * nat.toInt(p) + sum;
  assert k * nat.toInt(p) + sum == k * nat.toInt(p) + sum;
  assume k * nat.toInt(p) + sum == k * nat.toInt(p) + sum;
  assert nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p)) == nat.toInt(nat.mod(nat.add(nat.mul(nat.fromInt(k), p), nat.fromInt(sum)), p));
  assume nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p)) == nat.toInt(nat.mod(nat.add(nat.mul(nat.fromInt(k), p), nat.fromInt(sum)), p));
  tmp60 := p;
  call lemma_mod_sum_factor(k, sum, nat.toInt(tmp60));
  assert nat.toInt(nat.mod(nat.add(nat.mul(nat.fromInt(k), p), nat.fromInt(sum)), p)) == nat.toInt(nat.mod(nat.fromInt(sum), p));
  assume nat.toInt(nat.mod(nat.add(nat.mul(nat.fromInt(k), p), nat.fromInt(sum)), p)) == nat.toInt(nat.mod(nat.fromInt(sum), p));
  exit lemma_u64_5_as_nat_product;
};
 procedure lemma_mul_value (a : Sequence bv64, b : Sequence bv64) returns ()
spec {
  requires mul_boundary_spec(a, b);
  ensures nat.toInt(nat.mod(u64_5_as_nat(mul_return(a, b)), p)) == nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p));
  } {
  var tmp3 : nat;
  var tmp4 : nat;
  var tmp5 : nat;
  var tmp6 : nat;
  var tmp7 : nat;
  var tmp8 : nat;
  var tmp9 : nat;
  var tmp11 : nat;
  var tmp12 : nat;
  var tmp13 : nat;
  var tmp14 : nat;
  var out_hat : (Sequence bv64);
  var c0_0 : int;
  var c1_0 : int;
  var c2_0 : int;
  var c3_0 : int;
  var c4_0 : int;
  var c1 : int;
  var c2 : int;
  var c3 : int;
  var c4 : int;
  var carry : bv64;
  var out0_0 : bv64;
  var out1_0 : bv64;
  var out2 : bv64;
  var out3 : bv64;
  var out4 : bv64;
  var out0_1 : bv64;
  var out1_1 : bv64;
  var out0_2 : bv64;
  var c_arr_as_nat : int;
  var s1 : nat;
  var s4 : nat;
  var reduced_sum : int;
  call Arithmetic_Power2_lemma2_to64_rest();
  call pow255_gt_19();
  assert nat.gt(p, nat.fromInt(0));
  assume nat.gt(p, nat.fromInt(0));
  call l51_bit_mask_lt();
  assert mask51 as_int == nat.toInt(Bits_low_bits_mask(nat.fromInt(51)));
  assume mask51 as_int == nat.toInt(Bits_low_bits_mask(nat.fromInt(51)));
  out_hat := mul_return(a, b);
  c0_0 := mul_c0_0_val(a, b);
  c1_0 := mul_c1_0_val(a, b);
  c2_0 := mul_c2_0_val(a, b);
  c3_0 := mul_c3_0_val(a, b);
  c4_0 := mul_c4_0_val(a, b);
  c1 := mul_c1_val(a, b);
  c2 := mul_c2_val(a, b);
  c3 := mul_c3_val(a, b);
  c4 := mul_c4_val(a, b);
  carry := (c4 div 2251799813685248) as_bv64;
  out0_0 := c0_0 as_bv64 & mask51;
  out1_0 := c1 as_bv64 & mask51;
  out2 := c2 as_bv64 & mask51;
  out3 := c3 as_bv64 & mask51;
  out4 := c4 as_bv64 & mask51;
  out0_1 := out0_0 + carry * bv{64}(19);
  out1_1 := out1_0 + (out0_1 >> bv{64}(51));
  out0_2 := out0_1 & mask51;
  call Bits_lemma_u64_low_bits_mask_is_mod(out0_1, nat.fromInt(51));
  assert out0_2 as_int == out0_1 as_int mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  assume out0_2 as_int == out0_1 as_int mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  call Bits_lemma_u64_shr_is_div(out0_1, 51 as_bv64);
  assert ((out0_1 >> bv{64}(51)) as_int) as_int == out0_1 as_int div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  assume ((out0_1 >> bv{64}(51)) as_int) as_int == out0_1 as_int div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616);
  call lemma_u64_div_and_mod_51(out0_1 >> bv{64}(51), out0_2, out0_1);
  assert out0_2 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * out1_1 as_int == out0_1 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * out1_0 as_int;
  assume out0_2 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * out1_1 as_int == out0_1 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * out1_0 as_int;
  assert nat.toInt(u64_5_as_nat(out_hat)) == out0_1 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * out1_0 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * out2 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * out3 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * out4 as_int;
  assume nat.toInt(u64_5_as_nat(out_hat)) == out0_1 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * out1_0 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * out2 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * out3 as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * out4 as_int;
  call l51_bit_mask_lt();
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616 == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616 == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456;
  call Bits_lemma_u64_low_bits_mask_is_mod(c0_0 as_bv64, nat.fromInt(51));
  assert out0_1 as_int == c0_0 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616) + 19 * carry as_int;
  assume out0_1 as_int == c0_0 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616) + 19 * carry as_int;
  call Bits_lemma_u64_low_bits_mask_is_mod(c1 as_bv64, nat.fromInt(51));
  assert out1_0 == c1 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  assume out1_0 == c1 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  call Bits_lemma_u64_low_bits_mask_is_mod(c2 as_bv64, nat.fromInt(51));
  assert out2 == c2 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  assume out2 == c2 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  call Bits_lemma_u64_low_bits_mask_is_mod(c3 as_bv64, nat.fromInt(51));
  assert out3 == c3 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  assume out3 == c3 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  call Bits_lemma_u64_low_bits_mask_is_mod(c4 as_bv64, nat.fromInt(51));
  assert out4 == c4 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  assume out4 == c4 as_bv64 mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) as_bv64;
  assert nat.toInt(u64_5_as_nat(out_hat)) == c0_0 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616));
  assume nat.toInt(u64_5_as_nat(out_hat)) == c0_0 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 mod 18446744073709551616 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 18446744073709551616));
  call lemma_cast_then_mod_51(c0_0);
  call lemma_cast_then_mod_51(c1);
  call lemma_cast_then_mod_51(c2);
  call lemma_cast_then_mod_51(c3);
  call lemma_cast_then_mod_51(c4);
  assert nat.toInt(u64_5_as_nat(out_hat)) == c0_0 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456));
  assume nat.toInt(u64_5_as_nat(out_hat)) == c0_0 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 mod (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456));
  tmp3 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Div_mod_lemma_fundamental_div_mod(c0_0, nat.toInt(tmp3));
  tmp4 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Div_mod_lemma_fundamental_div_mod(c1, nat.toInt(tmp4));
  tmp5 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Div_mod_lemma_fundamental_div_mod(c2, nat.toInt(tmp5));
  tmp6 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Div_mod_lemma_fundamental_div_mod(c3, nat.toInt(tmp6));
  tmp7 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Div_mod_lemma_fundamental_div_mod(c4, nat.toInt(tmp7));
  assert nat.toInt(u64_5_as_nat(out_hat)) == c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c0_0 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c2 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c3 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c4 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)));
  assume nat.toInt(u64_5_as_nat(out_hat)) == c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c0_0 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c2 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c3 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c4 div (nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) mod 340282366920938463463374607431768211456)));
  call Bits_lemma_u128_shr_is_div(c0_0, 51);
  call Bits_lemma_u128_shr_is_div(c1, 51);
  call Bits_lemma_u128_shr_is_div(c2, 51);
  call Bits_lemma_u128_shr_is_div(c3, 51);
  call Bits_lemma_u128_shr_is_div(c4, 51);
  assert nat.toInt(u64_5_as_nat(out_hat)) == c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - c1_0) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c2 - c2_0)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c3 - c3_0)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c4 - c4_0)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * carry as_int);
  assume nat.toInt(u64_5_as_nat(out_hat)) == c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - c1_0) + 19 * carry as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c2 - c2_0)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c3 - c3_0)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c4 - c4_0)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * carry as_int);
  tmp8 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Mul_lemma_mul_is_distributive_sub(nat.toInt(tmp8), c1, c1_0);
  assert c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - c1_0) == c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0;
  assume c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - c1_0) == c0_0 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0;
  call lemma_mul_sub(c1, c2, c2_0, nat.fromInt(51));
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c2 - c2_0)) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c2 - c2_0)) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0;
  call lemma_mul_sub(c2, c3, c3_0, nat.fromInt(102));
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c3 - c3_0)) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c3 - c3_0)) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0;
  call lemma_mul_sub(c3, c4, c4_0, nat.fromInt(153));
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c4 - c4_0)) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * (c4 - c4_0)) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0;
  tmp9 := Arithmetic_Power2_pow2(nat.fromInt(204));
  call Arithmetic_Mul_lemma_mul_is_distributive_sub(nat.toInt(tmp9), c4, nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * carry as_int);
  tmp11 := Arithmetic_Power2_pow2(nat.fromInt(204));
  tmp12 := Arithmetic_Power2_pow2(nat.fromInt(51));
  call Arithmetic_Mul_lemma_mul_is_associative(nat.toInt(tmp11), nat.toInt(tmp12), carry as_int);
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(204), nat.fromInt(51));
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * carry as_int) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(255))) * carry as_int;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * (c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * carry as_int) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4 - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(255))) * carry as_int;
  call pow255_gt_19();
  tmp13 := Arithmetic_Power2_pow2(nat.fromInt(255));
  call Arithmetic_Mul_lemma_mul_is_distributive_sub_other_way(carry as_int, nat.toInt(tmp13), 19);
  assert c0_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0 + 19 * carry as_int - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(255))) * carry as_int == c0_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0 - nat.toInt(p) * carry as_int;
  assume c0_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0 + 19 * carry as_int - nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(255))) * carry as_int == c0_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0 - nat.toInt(p) * carry as_int;
  assert nat.toInt(u64_5_as_nat(out_hat)) == c0_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0 - nat.toInt(p) * carry as_int;
  assume nat.toInt(u64_5_as_nat(out_hat)) == c0_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0 - nat.toInt(p) * carry as_int;
  c_arr_as_nat := c0_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) * c1_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * c2_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * c3_0 + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(204))) * c4_0;
  tmp14 := p;
  call lemma_mod_diff_factor(carry as_int, c_arr_as_nat, nat.toInt(tmp14));
  assert nat.toInt(nat.mod(u64_5_as_nat(out_hat), p)) == nat.toInt(nat.mod(nat.fromInt(c_arr_as_nat), p));
  assume nat.toInt(nat.mod(u64_5_as_nat(out_hat), p)) == nat.toInt(nat.mod(nat.fromInt(c_arr_as_nat), p));
  call lemma_u64_5_as_nat_product(a, b);
  s1 := Arithmetic_Power2_pow2(nat.fromInt(51));
  s4 := Arithmetic_Power2_pow2(nat.fromInt(204));
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 4) as_int, Sequence.select(b, 1) as_int, 19);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 3) as_int, Sequence.select(b, 2) as_int, 19);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 2) as_int, Sequence.select(b, 3) as_int, 19);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 1) as_int, Sequence.select(b, 4) as_int, 19);
  call lemma_mul_distributive_4_terms(19, Sequence.select(a, 4) as_int * Sequence.select(b, 1) as_int, Sequence.select(a, 3) as_int * Sequence.select(b, 2) as_int, Sequence.select(a, 2) as_int * Sequence.select(b, 3) as_int, Sequence.select(a, 1) as_int * Sequence.select(b, 4) as_int);
  assert c0_0 == Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 4) as_int);
  assume c0_0 == Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 4) as_int);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 4) as_int, Sequence.select(b, 2) as_int, 19);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 3) as_int, Sequence.select(b, 3) as_int, 19);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 2) as_int, Sequence.select(b, 4) as_int, 19);
  call lemma_mul_distributive_3_terms(19, Sequence.select(a, 4) as_int * Sequence.select(b, 2) as_int, Sequence.select(a, 3) as_int * Sequence.select(b, 3) as_int, Sequence.select(a, 2) as_int * Sequence.select(b, 4) as_int);
  assert c1_0 == Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 4) as_int);
  assume c1_0 == Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 4) as_int);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 4) as_int, Sequence.select(b, 3) as_int, 19);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 3) as_int, Sequence.select(b, 4) as_int, 19);
  call Arithmetic_Mul_lemma_mul_is_distributive_add(19, Sequence.select(a, 4) as_int * Sequence.select(b, 3) as_int, Sequence.select(a, 3) as_int * Sequence.select(b, 4) as_int);
  assert c2_0 == Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 4) as_int);
  assume c2_0 == Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 4) as_int);
  call Arithmetic_Mul_lemma_mul_is_associative(Sequence.select(a, 4) as_int, Sequence.select(b, 4) as_int, 19);
  assert c3_0 == Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 4) as_int);
  assume c3_0 == Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 4) as_int);
  reduced_sum := nat.toInt(s4) * (Sequence.select(a, 0) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 0) as_int) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(153))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 4) as_int * Sequence.select(b, 4) as_int)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(102))) * (Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 3) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 3) as_int)) + nat.toInt(s1) * (Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 2) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 2) as_int)) + (Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int + 19 * (Sequence.select(a, 1) as_int * Sequence.select(b, 4) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 4) as_int * Sequence.select(b, 1) as_int));
  assert c_arr_as_nat == reduced_sum;
  assume c_arr_as_nat == reduced_sum;
  assert nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p)) == nat.toInt(nat.mod(nat.fromInt(reduced_sum), p));
  assume nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p)) == nat.toInt(nat.mod(nat.fromInt(reduced_sum), p));
  assert nat.toInt(nat.mod(nat.fromInt(c_arr_as_nat), p)) == nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p));
  assume nat.toInt(nat.mod(nat.fromInt(c_arr_as_nat), p)) == nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p));
  exit lemma_mul_value;
};
#end

-- Blocked on #strata elaboration (stack overflow on programs this size);
-- see the module docstring.
-- #eval Strata.Boole.verify "cvc5" b1_full_program (options := .quiet)
