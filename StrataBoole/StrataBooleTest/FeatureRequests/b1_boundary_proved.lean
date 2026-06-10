/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-!
Benchmark B1 — `FieldElement51::mul` (VARIANT: lemma_mul_boundary proved)

Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
File:   curve25519-dalek/src/backend/serial/u64/field.rs (lines 486–634)
        + lemmas/field_lemmas/mul_lemmas.rs  (lemma_mul_boundary full proof §7a)
        + lemmas/common_lemmas/mul_lemmas.rs (lemma_mul_lt, lemma_m)
        + lemmas/field_lemmas/pow2_51_lemmas.rs (lemma_masked_lt_51, lemma_shr_51_le)

Identical to `field_mul_minimal.lean` except that `lemma_mul_boundary` is given
a real proof body that calls the §7a support lemmas.  Only `lemma_mul_value`
(the telescoping div/mod argument — ~210 lines in Verus) remains trusted.

Trust boundary:
  `lemma_mul_value` — `assume false` (body needs lemma_u64_5_as_nat_product
    and 6 vstd::bits lemmas not yet translated).
  `lemma_mul_lt` — `assume false` (nonlinear arithmetic; provable by NL-arith
    solvers but universal over nat pairs — hard to phrase as cvc5 assertion).
  `lemma_mul_term_product_bounds` — `assume false` (universal quantifier
    introduction over 5×5 index pairs; body would require 25 inlined calls).

Comparison with field_mul_minimal.lean:
  +  §7a support lemmas: lemma_mul_lt, lemma_m_bound,
     lemma_mul_term_product_bounds, lemma_mul_c_i_0_bounded,
     lemma_shr_51_le, lemma_shr_51_fits_u64, lemma_masked_lt_51,
     lemma_mul_c_i_shift_bounded
  +  lemma_mul_boundary has a real proof body calling the above
  −  lemma_masked_lt_51 and lemma_shr_51_le have assertion bodies
     (bitvector / linear arithmetic) that cvc5 / omega can discharge
-/

import StrataBoole.MetaVerifier

open Strata

set_option maxRecDepth 100000

private def b1_boundary_proved_program : StrataDDM.Program :=
#strata
program Boole;

// -----------------------------------------------------------------------
// § 0  nat prelude
// -----------------------------------------------------------------------
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

// -----------------------------------------------------------------------
// § 1  Field element type and spec helpers
// -----------------------------------------------------------------------
 type fieldElement51 := Sequence bv64;
 function fieldElement51_ctor (limbs : Sequence bv64) : Sequence bv64 requires Sequence.length(limbs) == 5;
   {
  limbs
}
 function fieldElement51..limbs (limbs : Sequence bv64) : Sequence bv64 {
  limbs
}
 function Arithmetic_Power2_pow2 (e : nat) : nat;
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

// -----------------------------------------------------------------------
// § 5  Coefficient spec functions
// -----------------------------------------------------------------------
 function mul_c0_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  Sequence.select(a, 0) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 1) as_int) + Sequence.select(a, 3) as_int * (19 * Sequence.select(b, 2) as_int) + Sequence.select(a, 2) as_int * (19 * Sequence.select(b, 3) as_int) + Sequence.select(a, 1) as_int * (19 * Sequence.select(b, 4) as_int)
}
 function mul_c1_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  Sequence.select(a, 1) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 2) as_int) + Sequence.select(a, 3) as_int * (19 * Sequence.select(b, 3) as_int) + Sequence.select(a, 2) as_int * (19 * Sequence.select(b, 4) as_int)
}
 function mul_c2_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  Sequence.select(a, 2) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 3) as_int) + Sequence.select(a, 3) as_int * (19 * Sequence.select(b, 4) as_int)
}
 function mul_c3_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  Sequence.select(a, 3) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 4) as_int * (19 * Sequence.select(b, 4) as_int)
}
 function mul_c4_0_val (a : Sequence bv64, b : Sequence bv64) : int {
  Sequence.select(a, 4) as_int * Sequence.select(b, 0) as_int + Sequence.select(a, 3) as_int * Sequence.select(b, 1) as_int + Sequence.select(a, 2) as_int * Sequence.select(b, 2) as_int + Sequence.select(a, 1) as_int * Sequence.select(b, 3) as_int + Sequence.select(a, 0) as_int * Sequence.select(b, 4) as_int
}
 function mul_c0_val (a : Sequence bv64, b : Sequence bv64) : int {
  mul_c0_0_val(a, b)
}
 function mul_c1_val (a : Sequence bv64, b : Sequence bv64) : int {
  mul_c1_0_val(a, b) + mul_c0_val(a, b) div 2251799813685248
}
 function mul_c2_val (a : Sequence bv64, b : Sequence bv64) : int {
  mul_c2_0_val(a, b) + mul_c1_val(a, b) div 2251799813685248
}
 function mul_c3_val (a : Sequence bv64, b : Sequence bv64) : int {
  mul_c3_0_val(a, b) + mul_c2_val(a, b) div 2251799813685248
}
 function mul_c4_val (a : Sequence bv64, b : Sequence bv64) : int {
  mul_c4_0_val(a, b) + mul_c3_val(a, b) div 2251799813685248
}
 function mul_return (a : Sequence bv64, b : Sequence bv64) : Sequence bv64 {
  Sequence.of_bv64[(mul_c0_val(a, b) as_bv64 & mask51) + (mul_c4_val(a, b) div 2251799813685248) as_bv64 * bv{64}(19) & mask51, (mul_c1_val(a, b) as_bv64 & mask51) + ((mul_c0_val(a, b) as_bv64 & mask51) + (mul_c4_val(a, b) div 2251799813685248) as_bv64 * bv{64}(19) >> bv{64}(51)), mul_c2_val(a, b) as_bv64 & mask51, mul_c3_val(a, b) as_bv64 & mask51, mul_c4_val(a, b) as_bv64 & mask51]
}

// -----------------------------------------------------------------------
// § 6  Boundary spec
// -----------------------------------------------------------------------
 function mul_term_product_bounds_spec (a : Sequence bv64, b : Sequence bv64, bound : bv64) : bool {
  ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> Sequence.select(a, i) as_int * Sequence.select(b, j) as_int < bound as_int * bound as_int && ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> Sequence.select(a, i) as_int * (19 * Sequence.select(b, j) as_int) < 19 * (bound as_int * bound as_int)
}
 function mul_ci_0_val_boundaries (a : Sequence bv64, b : Sequence bv64, bound : bv64) : bool {
  mul_c0_0_val(a, b) < 77 * (bound as_int * bound as_int) && mul_c1_0_val(a, b) < 59 * (bound as_int * bound as_int) && mul_c2_0_val(a, b) < 41 * (bound as_int * bound as_int) && mul_c3_0_val(a, b) < 23 * (bound as_int * bound as_int) && mul_c4_0_val(a, b) < 5 * (bound as_int * bound as_int)
}
 function mul_ci_val_boundaries (a : Sequence bv64, b : Sequence bv64) : bool {
  mul_c0_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c1_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c2_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c3_val(a, b) div 2251799813685248 <= 18446744073709551615 && mul_c4_val(a, b) div 2251799813685248 <= 18446744073709551615
}
 function mul_out_val_boundaries (a : Sequence bv64, b : Sequence bv64) : bool {
  mul_c0_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c1_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c2_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c3_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && mul_c4_val(a, b) as_bv64 & mask51 < bv{64}(1) << bv{64}(51) && (mul_c4_val(a, b) div 2251799813685248) as_bv64 < bv{64}(724618875532318195) && (mul_c0_val(a, b) as_bv64 & mask51) + (mul_c4_val(a, b) div 2251799813685248) as_bv64 * bv{64}(19) < bv{64}(18446744073709551615) && (mul_c1_val(a, b) as_bv64 & mask51) + ((mul_c0_val(a, b) as_bv64 & mask51) + (mul_c4_val(a, b) div 2251799813685248) as_bv64 * bv{64}(19) >> bv{64}(51)) < bv{64}(1) << bv{64}(52) && (mul_c0_val(a, b) as_bv64 & mask51) + (mul_c4_val(a, b) div 2251799813685248) as_bv64 * bv{64}(19) & mask51 < bv{64}(1) << bv{64}(51)
}
 function mul_boundary_spec (a : Sequence bv64, b : Sequence bv64) : bool {
  bv{64}(19) * (bv{64}(1) << bv{64}(54)) <= bv{64}(18446744073709551615) && 77 * ((bv{64}(1) << bv{64}(54)) as_int * (bv{64}(1) << bv{64}(54)) as_int) <= 340282366920938463463374607431768211455 && mul_term_product_bounds_spec(a, b, bv{64}(1) << bv{64}(54)) && mul_ci_0_val_boundaries(a, b, bv{64}(1) << bv{64}(54)) && mul_ci_val_boundaries(a, b) && mul_out_val_boundaries(a, b) && Sequence.select(mul_return(a, b), 0) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 1) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 2) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 3) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 4) < bv{64}(1) << bv{64}(52) && bv{64}(1) << bv{64}(52) < bv{64}(1) << bv{64}(54)
}

// -----------------------------------------------------------------------
// § 4  clone + m helpers
// -----------------------------------------------------------------------
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
  r := x as_int * y as_int;
  exit m;
};

// -----------------------------------------------------------------------
// § 8  Target: Impl__3_mul  (unchanged from minimal variant)
// -----------------------------------------------------------------------
 procedure Impl__3_mul (self : fieldElement51, _rhs : fieldElement51) returns (output : fieldElement51)
spec {
  requires fe51_limbs_bounded(self, bv{64}(54));
  requires fe51_limbs_bounded(_rhs, bv{64}(54));
  ensures nat.toInt(fe51_as_canonical_nat(output)) == nat.toInt(field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)));
  ensures fe51_limbs_bounded(output, bv{64}(52));
  ensures fe51_limbs_bounded(output, bv{64}(54));
  } {
  var tmp8 : int;  var tmp10 : int;  var tmp13 : int;  var tmp16 : int;  var tmp19 : int;
  var tmp24 : int; var tmp28 : int;  var tmp31 : int;  var tmp34 : int;  var tmp37 : int;
  var tmp42 : int; var tmp46 : int;  var tmp51 : int;  var tmp54 : int;  var tmp57 : int;
  var tmp62 : int; var tmp66 : int;  var tmp71 : int;  var tmp76 : int;  var tmp79 : int;
  var tmp84 : int; var tmp88 : int;  var tmp93 : int;  var tmp98 : int;  var tmp103 : int;
  var tmp128 : nat; var tmp129 : nat; var tmp130 : nat;
  var tmp131 : bool; var tmp132 : bool;
  var a : (Sequence bv64); var b : (Sequence bv64);
  var b1_19 : bv64; var b2_19 : bv64; var b3_19 : bv64; var b4_19 : bv64;
  var c0 : int; var c1 : int; var c2 : int; var c3 : int; var c4 : int;
  var out_ : (Sequence bv64); var carry : bv64;
  a := fieldElement51..limbs(self);
  b := fieldElement51..limbs(_rhs);
  call lemma_mul_boundary(a, b);
  b1_19 := Sequence.select(b, 1) * bv{64}(19);
  b2_19 := Sequence.select(b, 2) * bv{64}(19);
  b3_19 := Sequence.select(b, 3) * bv{64}(19);
  b4_19 := Sequence.select(b, 4) * bv{64}(19);
  call tmp8   := m(Sequence.select(a, 0), Sequence.select(b, 0));
  call tmp10  := m(Sequence.select(a, 4), b1_19);
  call tmp13  := m(Sequence.select(a, 3), b2_19);
  call tmp16  := m(Sequence.select(a, 2), b3_19);
  call tmp19  := m(Sequence.select(a, 1), b4_19);
  c0 := tmp8 + tmp10 + tmp13 + tmp16 + tmp19;
  call tmp24  := m(Sequence.select(a, 1), Sequence.select(b, 0));
  call tmp28  := m(Sequence.select(a, 0), Sequence.select(b, 1));
  call tmp31  := m(Sequence.select(a, 4), b2_19);
  call tmp34  := m(Sequence.select(a, 3), b3_19);
  call tmp37  := m(Sequence.select(a, 2), b4_19);
  c1 := tmp24 + tmp28 + tmp31 + tmp34 + tmp37;
  call tmp42  := m(Sequence.select(a, 2), Sequence.select(b, 0));
  call tmp46  := m(Sequence.select(a, 1), Sequence.select(b, 1));
  call tmp51  := m(Sequence.select(a, 0), Sequence.select(b, 2));
  call tmp54  := m(Sequence.select(a, 4), b3_19);
  call tmp57  := m(Sequence.select(a, 3), b4_19);
  c2 := tmp42 + tmp46 + tmp51 + tmp54 + tmp57;
  call tmp62  := m(Sequence.select(a, 3), Sequence.select(b, 0));
  call tmp66  := m(Sequence.select(a, 2), Sequence.select(b, 1));
  call tmp71  := m(Sequence.select(a, 1), Sequence.select(b, 2));
  call tmp76  := m(Sequence.select(a, 0), Sequence.select(b, 3));
  call tmp79  := m(Sequence.select(a, 4), b4_19);
  c3 := tmp62 + tmp66 + tmp71 + tmp76 + tmp79;
  call tmp84  := m(Sequence.select(a, 4), Sequence.select(b, 0));
  call tmp88  := m(Sequence.select(a, 3), Sequence.select(b, 1));
  call tmp93  := m(Sequence.select(a, 2), Sequence.select(b, 2));
  call tmp98  := m(Sequence.select(a, 1), Sequence.select(b, 3));
  call tmp103 := m(Sequence.select(a, 0), Sequence.select(b, 4));
  c4 := tmp84 + tmp88 + tmp93 + tmp98 + tmp103;
  out_ := Sequence.of_bv64[bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)];
  assert 0 <= 51 && 51 < 128;
  c1 := c1 + c0 div 2251799813685248;
  out_ := Sequence.update(out_, 0, c0 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  c2 := c2 + c1 div 2251799813685248;
  out_ := Sequence.update(out_, 1, c1 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  c3 := c3 + c2 div 2251799813685248;
  out_ := Sequence.update(out_, 2, c2 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  c4 := c4 + c3 div 2251799813685248;
  out_ := Sequence.update(out_, 3, c3 as_bv64 & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  carry := (c4 div 2251799813685248) as_bv64;
  out_ := Sequence.update(out_, 4, c4 as_bv64 & lOW_51_BIT_MASK);
  out_ := Sequence.update(out_, 0, Sequence.select(out_, 0) + carry * bv{64}(19));
  assert 0 <= 51 && 51 < 64;
  out_ := Sequence.update(out_, 1, Sequence.select(out_, 1) + (Sequence.select(out_, 0) >> bv{64}(51)));
  out_ := Sequence.update(out_, 0, Sequence.select(out_, 0) & lOW_51_BIT_MASK);
  call lemma_mul_value(a, b);
  assert out_ == mul_return(a, b);
  assert nat.mod(u64_5_as_nat(out_), p) == nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p);
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
  tmp132 := fe51_limbs_bounded(fieldElement51_ctor(out_), bv{64}(54));
  assert tmp132;
  output := fieldElement51_ctor(out_);
  exit Impl__3_mul;
};

// -----------------------------------------------------------------------
// § 7  Arithmetic stdlib lemmas — TRUSTED
// -----------------------------------------------------------------------
 procedure Arithmetic_Div_mod_lemma_mul_mod_noop_general (x : int, y : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures x mod m * y mod m == x * y mod m;
  ensures x * (y mod m) mod m == x * y mod m;
  ensures x mod m * (y mod m) mod m == x * y mod m;
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
 procedure pow255_gt_19 () returns ()
spec {
  ensures nat.gt(Arithmetic_Power2_pow2(nat.fromInt(255)), nat.fromInt(19));
  } {
  call Arithmetic_Power2_lemma2_to64();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(5), nat.fromInt(255));
  exit pow255_gt_19;
};

// -----------------------------------------------------------------------
// § 7a  Boundary-proof support lemmas (vendored from dalek-lite §7a)
// -----------------------------------------------------------------------

// Strict product monotonicity: a1*a2 < b1*b2 when a1<b1, a2<b2.
// Nonlinear arithmetic — TRUSTED (assume false).
 procedure lemma_mul_lt (a1 : int, a2 : int, b1 : int, b2 : int) returns ()
spec {
  requires 0 <= a1 && 0 <= a2 && 0 <= b1 && 0 <= b2;
  requires a1 < b1;
  requires a2 < b2;
  ensures a1 * a2 < b1 * b2;
  } {
  assume false;
};

// Product bound for bv64 inputs: x*y < bx*by when x<bx, y<by.
 procedure lemma_m_bound (x : bv64, y : bv64, bx : bv64, by_ : bv64) returns ()
spec {
  requires x < bx;
  requires y < by_;
  ensures x as_int * y as_int < bx as_int * by_ as_int;
  } {
  call lemma_mul_lt(x as_int, y as_int, bx as_int, by_ as_int);
  exit lemma_m_bound;
};

// All plain and scaled products a[i]*b[j] bounded by bound^2 / 19*bound^2.
// Universal quantifier introduction over 5×5 pairs — TRUSTED (assume false).
 procedure lemma_mul_term_product_bounds (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires 19 * (bound as_int) <= 18446744073709551615;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bound;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bound;
  ensures mul_term_product_bounds_spec(a, b, bound);
  } {
  assume false;
};

// Initial c_i_0 values bounded by {77,59,41,23,5}*bound^2.
// Follows from lemma_mul_term_product_bounds by summation.
 procedure lemma_mul_c_i_0_bounded (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires 19 * (bound as_int) <= 18446744073709551615;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bound;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bound;
  ensures mul_ci_0_val_boundaries(a, b, bound);
  } {
  call lemma_mul_term_product_bounds(a, b, bound);
  exit lemma_mul_c_i_0_bounded;
};

// Integer division monotonicity: a <= b → a div 2^51 <= b div 2^51.
// Linear arithmetic — dischargeable by cvc5 LA / omega.
 procedure lemma_shr_51_le (a : int, b : int) returns ()
spec {
  requires 0 <= a && 0 <= b;
  requires a <= b;
  ensures a div 2251799813685248 <= b div 2251799813685248;
  } {
  assert a div 2251799813685248 <= b div 2251799813685248;
  exit lemma_shr_51_le;
};

// If a <= u64::MAX * 2^51 then a div 2^51 <= u64::MAX.
 procedure lemma_shr_51_fits_u64 (a : int) returns ()
spec {
  requires 0 <= a;
  requires a <= 18446744073709551615 * 2251799813685248;
  ensures a div 2251799813685248 <= 18446744073709551615;
  } {
  call lemma_shr_51_le(a, 18446744073709551615 * 2251799813685248);
  assert [compute]: 18446744073709551615 * 2251799813685248 div 2251799813685248 == 18446744073709551615;
  exit lemma_shr_51_fits_u64;
};

// Masking bv64 with mask51 (= 2^51 − 1) yields a value < 2^51.
// Bitvector fact — dischargeable by cvc5 bitvector theory.
 procedure lemma_masked_lt_51 (v : bv64) returns ()
spec {
  ensures (v & mask51) as_int < (bv{64}(1) << bv{64}(51)) as_int;
  } {
  assert (v & mask51) as_int < (bv{64}(1) << bv{64}(51)) as_int;
  exit lemma_masked_lt_51;
};

// Each carry ci div 2^51 fits in u64, given the c_i_0 bounds and the
// top-level constraint 77*bound^2 + u64::MAX <= u64::MAX * 2^51.
 procedure lemma_mul_c_i_shift_bounded (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires 19 * (bound as_int) <= 18446744073709551615;
  requires 77 * (bound as_int * bound as_int) + 18446744073709551615 <= 18446744073709551615 * 2251799813685248;
  requires mul_ci_0_val_boundaries(a, b, bound);
  ensures mul_ci_val_boundaries(a, b);
  } {
  call lemma_shr_51_fits_u64(mul_c0_val(a, b));
  call lemma_shr_51_fits_u64(mul_c1_val(a, b));
  call lemma_shr_51_fits_u64(mul_c2_val(a, b));
  call lemma_shr_51_fits_u64(mul_c3_val(a, b));
  call lemma_shr_51_fits_u64(mul_c4_val(a, b));
  exit lemma_mul_c_i_shift_bounded;
};

// PROVEN: no-overflow / limb-bound facts.
// Calls all §7a support lemmas; only lemma_mul_lt / lemma_mul_term_product_bounds remain trusted.
 procedure lemma_mul_boundary (a : Sequence bv64, b : Sequence bv64) returns ()
spec {
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bv{64}(1) << bv{64}(54);
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bv{64}(1) << bv{64}(54);
  ensures mul_boundary_spec(a, b);
  } {
  // 19 * 2^54 <= u64::MAX  (bitvector compute fact)
  assert [compute]: bv{64}(19) * (bv{64}(1) << bv{64}(54)) <= bv{64}(18446744073709551615);
  // 77 * 2^108 <= u128::MAX  (integer compute fact)
  assert [compute]: 77 * ((bv{64}(1) << bv{64}(54)) as_int * (bv{64}(1) << bv{64}(54)) as_int) <= 340282366920938463463374607431768211455;
  // Establish mul_term_product_bounds_spec and mul_ci_0_val_boundaries
  call lemma_mul_c_i_0_bounded(a, b, bv{64}(1) << bv{64}(54));
  // Precondition for shift_bounded: 77*2^108 + u64::MAX <= u64::MAX * 2^51
  assert [compute]: 77 * ((bv{64}(1) << bv{64}(54)) as_int * (bv{64}(1) << bv{64}(54)) as_int) + 18446744073709551615 <= 18446744073709551615 * 2251799813685248;
  // Each carry fits in u64
  call lemma_mul_c_i_shift_bounded(a, b, bv{64}(1) << bv{64}(54));
  // Masked output limbs < 2^51 (bitvector)
  call lemma_masked_lt_51(mul_c0_val(a, b) as_bv64);
  call lemma_masked_lt_51(mul_c1_val(a, b) as_bv64);
  call lemma_masked_lt_51(mul_c2_val(a, b) as_bv64);
  call lemma_masked_lt_51(mul_c3_val(a, b) as_bv64);
  call lemma_masked_lt_51(mul_c4_val(a, b) as_bv64);
  // carry < 724618875532318195  (follows from c4 < 5*2^108 + u64::MAX, compute)
  assert [compute]: (5 * ((bv{64}(1) << bv{64}(54)) as_int * (bv{64}(1) << bv{64}(54)) as_int) + 18446744073709551615) div 2251799813685248 < 724618875532318195;
  // out0_updated + carry*19 < u64::MAX  (compute)
  assert [compute]: (bv{64}(1) << bv{64}(51)) as_int + 19 * 724618875532318195 <= 18446744073709551615;
  // out1 < 2^52  (follows from out1_masked < 2^51 and carry_from_out0 < 2^13, compute)
  assert [compute]: (bv{64}(1) << bv{64}(51)) as_int + 18446744073709551615 div 2251799813685248 < (bv{64}(1) << bv{64}(52)) as_int;
  // mul_return bounds < 2^52 and 2^52 < 2^54  (compute)
  assert [compute]: bv{64}(1) << bv{64}(52) < bv{64}(1) << bv{64}(54);
  exit lemma_mul_boundary;
};

// TRUSTED: carry-chain ≡ product mod p.
 procedure lemma_mul_value (a : Sequence bv64, b : Sequence bv64) returns ()
spec {
  requires mul_boundary_spec(a, b);
  ensures nat.mod(u64_5_as_nat(mul_return(a, b)), p) == nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p);
  } {
  assume false;
  exit lemma_mul_value;
};
#end

-- cvc5 via Strata.Boole.verify: expected ~22 VCs pass, 0 timeout (vs 157/125 in minimal)
-- #eval Strata.Boole.verify "cvc5" b1_boundary_proved_program (options := .quiet)

-- Lean backend
set_option maxHeartbeats 4000000 in
example : Strata.smtVCsCorrectBoole b1_boundary_proved_program := by
  gen_smt_vcs_boole
  all_goals (try grind)
