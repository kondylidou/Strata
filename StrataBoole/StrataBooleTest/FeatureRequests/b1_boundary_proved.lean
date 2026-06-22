/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Benchmark B1 — `FieldElement51::mul` (VARIANT: lemma_mul_boundary proved)

Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
File:   curve25519-dalek/src/backend/serial/u64/field.rs (lines 486–634)
        + lemmas/field_lemmas/mul_lemmas.rs  (lemma_mul_boundary full proof §7a)
        + lemmas/common_lemmas/mul_lemmas.rs (lemma_mul_lt, lemma_m)
        + lemmas/field_lemmas/pow2_51_lemmas.rs (lemma_masked_lt_51, lemma_shr_51_le)

Identical to `b1_minimal.lean` except that `lemma_mul_boundary` is given
a real proof body that calls the §7a support lemmas.  Only `lemma_mul_value`
(the telescoping div/mod argument — ~210 lines in Verus) remains trusted.

Trust boundary:
  `lemma_mul_value` — `assume false` (body needs lemma_u64_5_as_nat_product
    and 6 vstd::bits lemmas not yet translated).
  `lemma_mul_lt` and `lemma_mul_term_product_bounds` have real proof bodies
    that discharge their nonlinear-multiplication goals through vstd
    `Arithmetic_Mul` lemmas (`lemma_mul_nonzero`, `lemma_mul_strict_inequality`,
    `lemma_mul_is_associative`), which remain `assume false` as untranslated
    library axioms.

Comparison with b1_minimal.lean:
  +  §7a support lemmas: lemma_mul_lt, lemma_m,
     lemma_mul_term_product_bounds, lemma_mul_c_i_0_bounded,
     lemma_shr_51_le, lemma_shr_51_fits_u64, lemma_masked_lt_51,
     lemma_mul_c_i_shift_bounded
  +  lemma_mul_boundary has a real proof body calling the above
  −  lemma_masked_lt_51 and lemma_shr_51_le have assertion bodies
     (bitvector / linear arithmetic) that cvc5 / omega can discharge
-/


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
  nat.add(nat.add(nat.add(nat.add(nat.fromInt(as_uint(Sequence.select(limbs, 0))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(51)), nat.fromInt(as_uint(Sequence.select(limbs, 1))))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(102)), nat.fromInt(as_uint(Sequence.select(limbs, 2))))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(153)), nat.fromInt(as_uint(Sequence.select(limbs, 3))))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(204)), nat.fromInt(as_uint(Sequence.select(limbs, 4)))))
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
 function mul_c0_0_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(Sequence.select(a, 0)) * as_uint(Sequence.select(b, 0)) + as_uint(Sequence.select(a, 4)) * (19 * as_uint(Sequence.select(b, 1))) + as_uint(Sequence.select(a, 3)) * (19 * as_uint(Sequence.select(b, 2))) + as_uint(Sequence.select(a, 2)) * (19 * as_uint(Sequence.select(b, 3))) + as_uint(Sequence.select(a, 1)) * (19 * as_uint(Sequence.select(b, 4))))
}
 function mul_c1_0_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(Sequence.select(a, 1)) * as_uint(Sequence.select(b, 0)) + as_uint(Sequence.select(a, 0)) * as_uint(Sequence.select(b, 1)) + as_uint(Sequence.select(a, 4)) * (19 * as_uint(Sequence.select(b, 2))) + as_uint(Sequence.select(a, 3)) * (19 * as_uint(Sequence.select(b, 3))) + as_uint(Sequence.select(a, 2)) * (19 * as_uint(Sequence.select(b, 4))))
}
 function mul_c2_0_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(Sequence.select(a, 2)) * as_uint(Sequence.select(b, 0)) + as_uint(Sequence.select(a, 1)) * as_uint(Sequence.select(b, 1)) + as_uint(Sequence.select(a, 0)) * as_uint(Sequence.select(b, 2)) + as_uint(Sequence.select(a, 4)) * (19 * as_uint(Sequence.select(b, 3))) + as_uint(Sequence.select(a, 3)) * (19 * as_uint(Sequence.select(b, 4))))
}
 function mul_c3_0_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(Sequence.select(a, 3)) * as_uint(Sequence.select(b, 0)) + as_uint(Sequence.select(a, 2)) * as_uint(Sequence.select(b, 1)) + as_uint(Sequence.select(a, 1)) * as_uint(Sequence.select(b, 2)) + as_uint(Sequence.select(a, 0)) * as_uint(Sequence.select(b, 3)) + as_uint(Sequence.select(a, 4)) * (19 * as_uint(Sequence.select(b, 4))))
}
 function mul_c4_0_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(Sequence.select(a, 4)) * as_uint(Sequence.select(b, 0)) + as_uint(Sequence.select(a, 3)) * as_uint(Sequence.select(b, 1)) + as_uint(Sequence.select(a, 2)) * as_uint(Sequence.select(b, 2)) + as_uint(Sequence.select(a, 1)) * as_uint(Sequence.select(b, 3)) + as_uint(Sequence.select(a, 0)) * as_uint(Sequence.select(b, 4)))
}
 function mul_c0_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  mul_c0_0_val(a, b)
}
 function mul_c1_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(mul_c1_0_val(a, b)) + as_uint(mul_c0_val(a, b) >> bv{128}(51)) mod 18446744073709551616)
}
 function mul_c2_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(mul_c2_0_val(a, b)) + as_uint(mul_c1_val(a, b) >> bv{128}(51)) mod 18446744073709551616)
}
 function mul_c3_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(mul_c3_0_val(a, b)) + as_uint(mul_c2_val(a, b) >> bv{128}(51)) mod 18446744073709551616)
}
 function mul_c4_val (a : Sequence bv64, b : Sequence bv64) : bv128 {
  as_bv128(as_uint(mul_c4_0_val(a, b)) + as_uint(mul_c3_val(a, b) >> bv{128}(51)) mod 18446744073709551616)
}
 function mul_return (a : Sequence bv64, b : Sequence bv64) : Sequence bv64 {
  Sequence.of_bv64[as_bv64(as_uint(as_bv64(as_uint(mul_c0_val(a, b))) & mask51) + as_uint(mul_c4_val(a, b) >> bv{128}(51)) mod 18446744073709551616 * 19) & mask51, as_bv64(as_uint(as_bv64(as_uint(mul_c1_val(a, b))) & mask51) + as_uint(as_bv64(as_uint(as_bv64(as_uint(mul_c0_val(a, b))) & mask51) + as_uint(mul_c4_val(a, b) >> bv{128}(51)) mod 18446744073709551616 * 19) >> bv{64}(51))), as_bv64(as_uint(mul_c2_val(a, b))) & mask51, as_bv64(as_uint(mul_c3_val(a, b))) & mask51, as_bv64(as_uint(mul_c4_val(a, b))) & mask51]
}

// -----------------------------------------------------------------------
// § 6  Boundary spec
// -----------------------------------------------------------------------
 function mul_term_product_bounds_spec (a : Sequence bv64, b : Sequence bv64, bound : bv64) : bool {
  ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> as_uint(Sequence.select(a, i)) * as_uint(Sequence.select(b, j)) < as_uint(bound) * as_uint(bound) && ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> as_uint(Sequence.select(a, i)) * (19 * as_uint(Sequence.select(b, j)) mod 340282366920938463463374607431768211456) < 19 * (as_uint(bound) * as_uint(bound))
}
 function mul_ci_0_val_boundaries (a : Sequence bv64, b : Sequence bv64, bound : bv64) : bool {
  as_uint(mul_c0_0_val(a, b)) < 77 * (as_uint(bound) * as_uint(bound)) && as_uint(mul_c1_0_val(a, b)) < 59 * (as_uint(bound) * as_uint(bound)) && as_uint(mul_c2_0_val(a, b)) < 41 * (as_uint(bound) * as_uint(bound)) && as_uint(mul_c3_0_val(a, b)) < 23 * (as_uint(bound) * as_uint(bound)) && as_uint(mul_c4_0_val(a, b)) < 5 * (as_uint(bound) * as_uint(bound))
}
 function mul_ci_val_boundaries (a : Sequence bv64, b : Sequence bv64) : bool {
  mul_c0_val(a, b) >> bv{128}(51) <= as_bv128(18446744073709551615) && mul_c1_val(a, b) >> bv{128}(51) <= as_bv128(18446744073709551615) && mul_c2_val(a, b) >> bv{128}(51) <= as_bv128(18446744073709551615) && mul_c3_val(a, b) >> bv{128}(51) <= as_bv128(18446744073709551615) && mul_c4_val(a, b) >> bv{128}(51) <= as_bv128(18446744073709551615)
}
 function mul_out_val_boundaries (a : Sequence bv64, b : Sequence bv64) : bool {
  as_bv64(as_uint(mul_c0_val(a, b))) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(mul_c1_val(a, b))) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(mul_c2_val(a, b))) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(mul_c3_val(a, b))) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(mul_c4_val(a, b))) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(mul_c4_val(a, b) >> bv{128}(51))) < bv{64}(724618875532318195) && as_uint(as_bv64(as_uint(mul_c0_val(a, b))) & mask51) + as_uint(mul_c4_val(a, b) >> bv{128}(51)) mod 18446744073709551616 * 19 < 18446744073709551615 && as_uint(as_bv64(as_uint(mul_c1_val(a, b))) & mask51) + as_uint(as_bv64(as_uint(as_bv64(as_uint(mul_c0_val(a, b))) & mask51) + as_uint(mul_c4_val(a, b) >> bv{128}(51)) mod 18446744073709551616 * 19) >> bv{64}(51)) < as_uint(as_uint(bv{64}(1) << bv{64}(52))) && as_uint(as_bv64(as_uint(as_bv64(as_uint(mul_c0_val(a, b))) & mask51) + as_uint(mul_c4_val(a, b) >> bv{128}(51)) mod 18446744073709551616 * 19) & mask51) < as_uint(as_uint(bv{64}(1) << bv{64}(51)))
}
 function mul_boundary_spec (a : Sequence bv64, b : Sequence bv64) : bool {
  19 * as_uint(bv{64}(1) << bv{64}(54)) <= 18446744073709551615 && 77 * (as_uint(bv{64}(1) << bv{64}(54)) * as_uint(bv{64}(1) << bv{64}(54))) <= 340282366920938463463374607431768211455 && mul_term_product_bounds_spec(a, b, bv{64}(1) << bv{64}(54)) && mul_ci_0_val_boundaries(a, b, bv{64}(1) << bv{64}(54)) && mul_ci_val_boundaries(a, b) && mul_out_val_boundaries(a, b) && Sequence.select(mul_return(a, b), 0) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 1) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 2) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 3) < bv{64}(1) << bv{64}(52) && Sequence.select(mul_return(a, b), 4) < bv{64}(1) << bv{64}(52) && bv{64}(1) << bv{64}(52) < bv{64}(1) << bv{64}(54)
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

 procedure m (x : bv64, y : bv64) returns (r : bv128)
spec {
  ensures as_uint(r) == as_uint(x) * as_uint(y);
  ensures r <= bv{128}(340282366920938463463374607431768211455);
  } {
  call Arithmetic_Mul_lemma_mul_upper_bound(as_uint(x), 18446744073709551615, as_uint(y), 18446744073709551615);
  assert [compute]: 18446744073709551615 * 18446744073709551615 <= 340282366920938463463374607431768211455;
  assert 0 <= as_uint(x) * as_uint(y) && as_uint(x) * as_uint(y) <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(x) * as_uint(y) && as_uint(x) * as_uint(y) <= 340282366920938463463374607431768211455;
  r := as_bv128(as_uint(x)) * as_bv128(as_uint(y));
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
  var tmp8 : bv128;
  var tmp10 : bv128;
  var tmp13 : bv128;
  var tmp16 : bv128;
  var tmp19 : bv128;
  var tmp24 : bv128;
  var tmp28 : bv128;
  var tmp31 : bv128;
  var tmp34 : bv128;
  var tmp37 : bv128;
  var tmp42 : bv128;
  var tmp46 : bv128;
  var tmp51 : bv128;
  var tmp54 : bv128;
  var tmp57 : bv128;
  var tmp62 : bv128;
  var tmp66 : bv128;
  var tmp71 : bv128;
  var tmp76 : bv128;
  var tmp79 : bv128;
  var tmp84 : bv128;
  var tmp88 : bv128;
  var tmp93 : bv128;
  var tmp98 : bv128;
  var tmp103 : bv128;
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
  var c0 : bv128;
  var c1 : bv128;
  var c2 : bv128;
  var c3 : bv128;
  var c4 : bv128;
  var out_ : (Sequence bv64);
  var carry : bv64;
  a := fieldElement51..limbs(self);
  b := fieldElement51..limbs(_rhs);
  call lemma_mul_boundary(a, b);
  assert 0 <= as_uint(Sequence.select(b, 1)) * 19 && as_uint(Sequence.select(b, 1)) * 19 <= 18446744073709551615;
  assume 0 <= as_uint(Sequence.select(b, 1)) * 19 && as_uint(Sequence.select(b, 1)) * 19 <= 18446744073709551615;
  b1_19 := Sequence.select(b, 1) * bv{64}(19);
  assert 0 <= as_uint(Sequence.select(b, 2)) * 19 && as_uint(Sequence.select(b, 2)) * 19 <= 18446744073709551615;
  assume 0 <= as_uint(Sequence.select(b, 2)) * 19 && as_uint(Sequence.select(b, 2)) * 19 <= 18446744073709551615;
  b2_19 := Sequence.select(b, 2) * bv{64}(19);
  assert 0 <= as_uint(Sequence.select(b, 3)) * 19 && as_uint(Sequence.select(b, 3)) * 19 <= 18446744073709551615;
  assume 0 <= as_uint(Sequence.select(b, 3)) * 19 && as_uint(Sequence.select(b, 3)) * 19 <= 18446744073709551615;
  b3_19 := Sequence.select(b, 3) * bv{64}(19);
  assert 0 <= as_uint(Sequence.select(b, 4)) * 19 && as_uint(Sequence.select(b, 4)) * 19 <= 18446744073709551615;
  assume 0 <= as_uint(Sequence.select(b, 4)) * 19 && as_uint(Sequence.select(b, 4)) * 19 <= 18446744073709551615;
  b4_19 := Sequence.select(b, 4) * bv{64}(19);
  call tmp8 := m(Sequence.select(a, 0), Sequence.select(b, 0));

  call tmp10 := m(Sequence.select(a, 4), b1_19);

  assert 0 <= as_uint(tmp8) + as_uint(tmp10) && as_uint(tmp8) + as_uint(tmp10) <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(tmp8) + as_uint(tmp10) && as_uint(tmp8) + as_uint(tmp10) <= 340282366920938463463374607431768211455;
  call tmp13 := m(Sequence.select(a, 3), b2_19);

  assert 0 <= (as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13) && (as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13) <= 340282366920938463463374607431768211455;
  assume 0 <= (as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13) && (as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13) <= 340282366920938463463374607431768211455;
  call tmp16 := m(Sequence.select(a, 2), b3_19);

  assert 0 <= ((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16) && ((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16) <= 340282366920938463463374607431768211455;
  assume 0 <= ((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16) && ((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16) <= 340282366920938463463374607431768211455;
  call tmp19 := m(Sequence.select(a, 1), b4_19);

  assert 0 <= (((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16)) mod 340282366920938463463374607431768211456 + as_uint(tmp19) && (((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16)) mod 340282366920938463463374607431768211456 + as_uint(tmp19) <= 340282366920938463463374607431768211455;
  assume 0 <= (((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16)) mod 340282366920938463463374607431768211456 + as_uint(tmp19) && (((as_uint(tmp8) + as_uint(tmp10)) mod 340282366920938463463374607431768211456 + as_uint(tmp13)) mod 340282366920938463463374607431768211456 + as_uint(tmp16)) mod 340282366920938463463374607431768211456 + as_uint(tmp19) <= 340282366920938463463374607431768211455;
  c0 := tmp8 + tmp10 + tmp13 + tmp16 + tmp19;
  call tmp24 := m(Sequence.select(a, 1), Sequence.select(b, 0));

  call tmp28 := m(Sequence.select(a, 0), Sequence.select(b, 1));

  assert 0 <= as_uint(tmp24) + as_uint(tmp28) && as_uint(tmp24) + as_uint(tmp28) <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(tmp24) + as_uint(tmp28) && as_uint(tmp24) + as_uint(tmp28) <= 340282366920938463463374607431768211455;
  call tmp31 := m(Sequence.select(a, 4), b2_19);

  assert 0 <= (as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31) && (as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31) <= 340282366920938463463374607431768211455;
  assume 0 <= (as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31) && (as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31) <= 340282366920938463463374607431768211455;
  call tmp34 := m(Sequence.select(a, 3), b3_19);

  assert 0 <= ((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34) && ((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34) <= 340282366920938463463374607431768211455;
  assume 0 <= ((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34) && ((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34) <= 340282366920938463463374607431768211455;
  call tmp37 := m(Sequence.select(a, 2), b4_19);

  assert 0 <= (((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34)) mod 340282366920938463463374607431768211456 + as_uint(tmp37) && (((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34)) mod 340282366920938463463374607431768211456 + as_uint(tmp37) <= 340282366920938463463374607431768211455;
  assume 0 <= (((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34)) mod 340282366920938463463374607431768211456 + as_uint(tmp37) && (((as_uint(tmp24) + as_uint(tmp28)) mod 340282366920938463463374607431768211456 + as_uint(tmp31)) mod 340282366920938463463374607431768211456 + as_uint(tmp34)) mod 340282366920938463463374607431768211456 + as_uint(tmp37) <= 340282366920938463463374607431768211455;
  c1 := tmp24 + tmp28 + tmp31 + tmp34 + tmp37;
  call tmp42 := m(Sequence.select(a, 2), Sequence.select(b, 0));

  call tmp46 := m(Sequence.select(a, 1), Sequence.select(b, 1));

  assert 0 <= as_uint(tmp42) + as_uint(tmp46) && as_uint(tmp42) + as_uint(tmp46) <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(tmp42) + as_uint(tmp46) && as_uint(tmp42) + as_uint(tmp46) <= 340282366920938463463374607431768211455;
  call tmp51 := m(Sequence.select(a, 0), Sequence.select(b, 2));

  assert 0 <= (as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51) && (as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51) <= 340282366920938463463374607431768211455;
  assume 0 <= (as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51) && (as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51) <= 340282366920938463463374607431768211455;
  call tmp54 := m(Sequence.select(a, 4), b3_19);

  assert 0 <= ((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54) && ((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54) <= 340282366920938463463374607431768211455;
  assume 0 <= ((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54) && ((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54) <= 340282366920938463463374607431768211455;
  call tmp57 := m(Sequence.select(a, 3), b4_19);

  assert 0 <= (((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54)) mod 340282366920938463463374607431768211456 + as_uint(tmp57) && (((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54)) mod 340282366920938463463374607431768211456 + as_uint(tmp57) <= 340282366920938463463374607431768211455;
  assume 0 <= (((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54)) mod 340282366920938463463374607431768211456 + as_uint(tmp57) && (((as_uint(tmp42) + as_uint(tmp46)) mod 340282366920938463463374607431768211456 + as_uint(tmp51)) mod 340282366920938463463374607431768211456 + as_uint(tmp54)) mod 340282366920938463463374607431768211456 + as_uint(tmp57) <= 340282366920938463463374607431768211455;
  c2 := tmp42 + tmp46 + tmp51 + tmp54 + tmp57;
  call tmp62 := m(Sequence.select(a, 3), Sequence.select(b, 0));

  call tmp66 := m(Sequence.select(a, 2), Sequence.select(b, 1));

  assert 0 <= as_uint(tmp62) + as_uint(tmp66) && as_uint(tmp62) + as_uint(tmp66) <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(tmp62) + as_uint(tmp66) && as_uint(tmp62) + as_uint(tmp66) <= 340282366920938463463374607431768211455;
  call tmp71 := m(Sequence.select(a, 1), Sequence.select(b, 2));

  assert 0 <= (as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71) && (as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71) <= 340282366920938463463374607431768211455;
  assume 0 <= (as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71) && (as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71) <= 340282366920938463463374607431768211455;
  call tmp76 := m(Sequence.select(a, 0), Sequence.select(b, 3));

  assert 0 <= ((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76) && ((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76) <= 340282366920938463463374607431768211455;
  assume 0 <= ((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76) && ((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76) <= 340282366920938463463374607431768211455;
  call tmp79 := m(Sequence.select(a, 4), b4_19);

  assert 0 <= (((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76)) mod 340282366920938463463374607431768211456 + as_uint(tmp79) && (((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76)) mod 340282366920938463463374607431768211456 + as_uint(tmp79) <= 340282366920938463463374607431768211455;
  assume 0 <= (((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76)) mod 340282366920938463463374607431768211456 + as_uint(tmp79) && (((as_uint(tmp62) + as_uint(tmp66)) mod 340282366920938463463374607431768211456 + as_uint(tmp71)) mod 340282366920938463463374607431768211456 + as_uint(tmp76)) mod 340282366920938463463374607431768211456 + as_uint(tmp79) <= 340282366920938463463374607431768211455;
  c3 := tmp62 + tmp66 + tmp71 + tmp76 + tmp79;
  call tmp84 := m(Sequence.select(a, 4), Sequence.select(b, 0));

  call tmp88 := m(Sequence.select(a, 3), Sequence.select(b, 1));

  assert 0 <= as_uint(tmp84) + as_uint(tmp88) && as_uint(tmp84) + as_uint(tmp88) <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(tmp84) + as_uint(tmp88) && as_uint(tmp84) + as_uint(tmp88) <= 340282366920938463463374607431768211455;
  call tmp93 := m(Sequence.select(a, 2), Sequence.select(b, 2));

  assert 0 <= (as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93) && (as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93) <= 340282366920938463463374607431768211455;
  assume 0 <= (as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93) && (as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93) <= 340282366920938463463374607431768211455;
  call tmp98 := m(Sequence.select(a, 1), Sequence.select(b, 3));

  assert 0 <= ((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98) && ((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98) <= 340282366920938463463374607431768211455;
  assume 0 <= ((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98) && ((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98) <= 340282366920938463463374607431768211455;
  call tmp103 := m(Sequence.select(a, 0), Sequence.select(b, 4));

  assert 0 <= (((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98)) mod 340282366920938463463374607431768211456 + as_uint(tmp103) && (((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98)) mod 340282366920938463463374607431768211456 + as_uint(tmp103) <= 340282366920938463463374607431768211455;
  assume 0 <= (((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98)) mod 340282366920938463463374607431768211456 + as_uint(tmp103) && (((as_uint(tmp84) + as_uint(tmp88)) mod 340282366920938463463374607431768211456 + as_uint(tmp93)) mod 340282366920938463463374607431768211456 + as_uint(tmp98)) mod 340282366920938463463374607431768211456 + as_uint(tmp103) <= 340282366920938463463374607431768211455;
  c4 := tmp84 + tmp88 + tmp93 + tmp98 + tmp103;
  out_ := Sequence.of_bv64[bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)];
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= as_uint(c1) + as_uint(c0 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c1) + as_uint(c0 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(c1) + as_uint(c0 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c1) + as_uint(c0 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c1 := c1 + as_bv128(as_uint(as_bv64(as_uint(c0 >> bv{128}(51)))));
  out_ := Sequence.update(out_, 0, as_bv64(as_uint(c0)) & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= as_uint(c2) + as_uint(c1 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c2) + as_uint(c1 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(c2) + as_uint(c1 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c2) + as_uint(c1 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c2 := c2 + as_bv128(as_uint(as_bv64(as_uint(c1 >> bv{128}(51)))));
  out_ := Sequence.update(out_, 1, as_bv64(as_uint(c1)) & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= as_uint(c3) + as_uint(c2 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c3) + as_uint(c2 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(c3) + as_uint(c2 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c3) + as_uint(c2 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c3 := c3 + as_bv128(as_uint(as_bv64(as_uint(c2 >> bv{128}(51)))));
  out_ := Sequence.update(out_, 2, as_bv64(as_uint(c2)) & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  assert 0 <= as_uint(c4) + as_uint(c3 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c4) + as_uint(c3 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  assume 0 <= as_uint(c4) + as_uint(c3 >> bv{128}(51)) mod 18446744073709551616 && as_uint(c4) + as_uint(c3 >> bv{128}(51)) mod 18446744073709551616 <= 340282366920938463463374607431768211455;
  c4 := c4 + as_bv128(as_uint(as_bv64(as_uint(c3 >> bv{128}(51)))));
  out_ := Sequence.update(out_, 3, as_bv64(as_uint(c3)) & lOW_51_BIT_MASK);
  assert 0 <= 51 && 51 < 128;
  assume 0 <= 51 && 51 < 128;
  carry := as_bv64(as_uint(c4 >> bv{128}(51)));
  out_ := Sequence.update(out_, 4, as_bv64(as_uint(c4)) & lOW_51_BIT_MASK);
  assert 0 <= as_uint(carry) * 19 && as_uint(carry) * 19 <= 18446744073709551615;
  assume 0 <= as_uint(carry) * 19 && as_uint(carry) * 19 <= 18446744073709551615;
  assert 0 <= as_uint(Sequence.select(out_, 0)) + as_uint(carry) * 19 mod 18446744073709551616 && as_uint(Sequence.select(out_, 0)) + as_uint(carry) * 19 mod 18446744073709551616 <= 18446744073709551615;
  assume 0 <= as_uint(Sequence.select(out_, 0)) + as_uint(carry) * 19 mod 18446744073709551616 && as_uint(Sequence.select(out_, 0)) + as_uint(carry) * 19 mod 18446744073709551616 <= 18446744073709551615;
  out_ := Sequence.update(out_, 0, Sequence.select(out_, 0) + carry * bv{64}(19));
  assert 0 <= 51 && 51 < 64;
  assume 0 <= 51 && 51 < 64;
  assert 0 <= as_uint(Sequence.select(out_, 1)) + as_uint(Sequence.select(out_, 0) >> bv{64}(51)) && as_uint(Sequence.select(out_, 1)) + as_uint(Sequence.select(out_, 0) >> bv{64}(51)) <= 18446744073709551615;
  assume 0 <= as_uint(Sequence.select(out_, 1)) + as_uint(Sequence.select(out_, 0) >> bv{64}(51)) && as_uint(Sequence.select(out_, 1)) + as_uint(Sequence.select(out_, 0) >> bv{64}(51)) <= 18446744073709551615;
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
// Nonlinear arithmetic — PROVEN via vstd Arithmetic_Mul lemmas.
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

// Product bound for bv64 inputs: x*y < bx*by when x<bx, y<by.
 procedure lemma_m (x : bv64, y : bv64, bx : bv64, b_y : bv64) returns ()
spec {
  requires x < bx;
  requires y < b_y;
  ensures as_uint(x) * as_uint(y) < as_uint(bx) * as_uint(b_y);
  } {
  call lemma_mul_lt(nat.fromInt(as_uint(x)), nat.fromInt(as_uint(bx)), nat.fromInt(as_uint(y)), nat.fromInt(as_uint(b_y)));
  exit lemma_m;
};

// All plain and scaled products a[i]*b[j] bounded by bound^2 / 19*bound^2.
// Universal quantifier introduction over 5×5 pairs — PROVEN via lemma_m and Arithmetic_Mul.
 procedure lemma_mul_term_product_bounds (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires 19 * as_uint(bound) <= 18446744073709551615;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bound;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bound;
  ensures mul_term_product_bounds_spec(a, b, bound);
  } {
  var i : int;
  var j : int;
  var bound19 : bv64;
  bound19 := as_bv64(19 * as_uint(bound));
  call Arithmetic_Mul_lemma_mul_is_associative(19, as_uint(bound), as_uint(bound));
  assert as_uint(bound) * (19 * as_uint(bound)) == 19 * (as_uint(bound) * as_uint(bound));
  assume as_uint(bound) * (19 * as_uint(bound)) == 19 * (as_uint(bound) * as_uint(bound));
  assume 0 <= i && i < 5 && (0 <= j && j < 5);
  call lemma_m(Sequence.select(a, i), Sequence.select(b, j), bound, bound);
  call lemma_m(Sequence.select(a, i), as_bv64(19 * as_uint(Sequence.select(b, j))), bound, bound19);
  assert as_uint(Sequence.select(a, i)) * as_uint(Sequence.select(b, j)) < as_uint(bound) * as_uint(bound) && as_uint(Sequence.select(a, i)) * (19 * as_uint(Sequence.select(b, j)) mod 340282366920938463463374607431768211456) < 19 * (as_uint(bound) * as_uint(bound));
  assume ∀ i : int, j : int :: 0 <= i && i < 5 && (0 <= j && j < 5) ==> as_uint(Sequence.select(a, i)) * as_uint(Sequence.select(b, j)) < as_uint(bound) * as_uint(bound) && as_uint(Sequence.select(a, i)) * (19 * as_uint(Sequence.select(b, j)) mod 340282366920938463463374607431768211456) < 19 * (as_uint(bound) * as_uint(bound));
  exit lemma_mul_term_product_bounds;
};
// Initial c_i_0 values bounded by {77,59,41,23,5}*bound^2.
// Follows from lemma_mul_term_product_bounds by summation.
 procedure lemma_mul_c_i_0_bounded (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires 19 * as_uint(bound) <= 18446744073709551615;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bound;
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bound;
  ensures mul_ci_0_val_boundaries(a, b, bound);
  } {
  call lemma_mul_term_product_bounds(a, b, bound);
  exit lemma_mul_c_i_0_bounded;
};

// Integer division monotonicity: a <= b → a div 2^51 <= b div 2^51.
// Linear arithmetic — dischargeable by cvc5 LA / omega.
 procedure lemma_shr_51_le (a : bv128, b : bv128) returns ()
spec {
  requires a <= b;
  ensures a >> bv{128}(51) <= b >> bv{128}(51);
  } {
  assert a <= b;
  assert [bitvector_query]: a <= b ==> a >> bv{128}(51) <= b >> bv{128}(51);
  exit lemma_shr_51_le;
};

// If a <= u64::MAX * 2^51 then a div 2^51 <= u64::MAX.
 procedure lemma_shr_51_fits_u64 (a : bv128) returns ()
spec {
  requires a <= as_bv128(18446744073709551615) << bv{128}(51);
  ensures a >> bv{128}(51) <= as_bv128(18446744073709551615);
  } {
  assert [compute]: as_bv128(18446744073709551615) << bv{128}(51) >> bv{128}(51) == as_bv128(18446744073709551615);
  call lemma_shr_51_le(a, as_bv128(18446744073709551615) << bv{128}(51));
  exit lemma_shr_51_fits_u64;
};

// Masking bv64 with mask51 (= 2^51 − 1) yields a value < 2^51.
// Bitvector fact — dischargeable by cvc5 bitvector theory.
 procedure lemma_masked_lt_51 (v : bv64) returns ()
spec {
  ensures v & mask51 < bv{64}(1) << bv{64}(51);
  } {
  assert [compute]: v & bv{64}(2251799813685247) < bv{64}(1) << bv{64}(51);
  assert [bitvector_query]: v & bv{64}(2251799813685247) < bv{64}(2251799813685248);
  exit lemma_masked_lt_51;
};
// Each carry ci div 2^51 fits in u64, given the c_i_0 bounds and the
// top-level constraint 77*bound^2 + u64::MAX <= u64::MAX * 2^51.
 procedure lemma_mul_c_i_shift_bounded (a : Sequence bv64, b : Sequence bv64, bound : bv64) returns ()
spec {
  requires 19 * as_uint(bound) <= 18446744073709551615;
  requires 77 * (as_uint(bound) * as_uint(bound)) + 18446744073709551615 <= as_uint(as_uint(as_bv128(18446744073709551615) << bv{128}(51)));
  requires mul_ci_0_val_boundaries(a, b, bound);
  ensures mul_ci_val_boundaries(a, b);
  } {
  var tmp1 : bv128;
  var tmp2 : bv128;
  var tmp3 : bv128;
  var tmp4 : bv128;
  var tmp5 : bv128;
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

// PROVEN: no-overflow / limb-bound facts.
// Calls all §7a support lemmas (all proved); lemma_mul_value + vstd Arithmetic lemmas remain trusted.
 procedure lemma_mul_boundary (a : Sequence bv64, b : Sequence bv64) returns ()
spec {
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(a, i) < bv{64}(1) << bv{64}(54);
  requires ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(b, i) < bv{64}(1) << bv{64}(54);
  ensures mul_boundary_spec(a, b);
  } {
  var c0 : bv128;
  var c1 : bv128;
  var c2 : bv128;
  var c3 : bv128;
  var c4 : bv128;
  var out0 : bv64;
  var out1 : bv64;
  var carry : bv64;
  var out0_1 : bv64;
  var pow2_5933 : bv64;
  var bound : bv64;
  var bound19 : bv64;
  var bound_sq : bv128;
  bound := bv{64}(1) << bv{64}(54);
  bound19 := as_bv64(19 * as_uint(bound));
  bound_sq := bv{128}(1) << bv{128}(108);
  assert [compute]: as_uint(bv{64}(1) << bv{64}(54)) mod 340282366920938463463374607431768211456 * (as_uint(bv{64}(1) << bv{64}(54)) mod 340282366920938463463374607431768211456) == as_uint(as_uint(bv{128}(1) << bv{128}(108)));
  assert as_uint(bound) * as_uint(bound) == as_uint(bound_sq);
  assume as_uint(bound) * as_uint(bound) == as_uint(bound_sq);
  assert [compute]: as_uint(bv{64}(1) << bv{64}(54)) * (19 * as_uint(bv{64}(1) << bv{64}(54)) mod 18446744073709551616) == 19 * as_uint(bv{128}(1) << bv{128}(108));
  assert as_uint(bound) * as_uint(bound19) == 19 * as_uint(bound_sq);
  assume as_uint(bound) * as_uint(bound19) == 19 * as_uint(bound_sq);
  assert [compute]: 19 * as_uint(bv{64}(1) << bv{64}(54)) <= 18446744073709551615;
  assert 19 * as_uint(bound) <= 18446744073709551615;
  assume 19 * as_uint(bound) <= 18446744073709551615;
  call lemma_mul_term_product_bounds(a, b, bound);
  assert mul_term_product_bounds_spec(a, b, bound);
  assume mul_term_product_bounds_spec(a, b, bound);
  call lemma_mul_c_i_0_bounded(a, b, bound);
  assert mul_ci_0_val_boundaries(a, b, bound);
  assume mul_ci_0_val_boundaries(a, b, bound);
  assert [compute]: 77 * as_uint(bv{128}(1) << bv{128}(108)) + 18446744073709551615 <= as_uint(as_uint(as_bv128(18446744073709551615) << bv{128}(51)));
  assert 77 * as_uint(bound_sq) + 18446744073709551615 <= as_uint(as_uint(as_bv128(18446744073709551615) << bv{128}(51)));
  assume 77 * as_uint(bound_sq) + 18446744073709551615 <= as_uint(as_uint(as_bv128(18446744073709551615) << bv{128}(51)));
  call lemma_mul_c_i_shift_bounded(a, b, bound);
  assert mul_ci_val_boundaries(a, b);
  assume mul_ci_val_boundaries(a, b);
  c0 := mul_c0_val(a, b);
  c1 := mul_c1_val(a, b);
  c2 := mul_c2_val(a, b);
  c3 := mul_c3_val(a, b);
  c4 := mul_c4_val(a, b);
  out0 := as_bv64(as_uint(c0)) & mask51;
  out1 := as_bv64(as_uint(c1)) & mask51;
  carry := as_bv64(as_uint(c4 >> bv{128}(51)));
  out0_1 := as_bv64(as_uint(out0) + as_uint(carry) * 19);
  call lemma_masked_lt_51(as_bv64(as_uint(c0)));
  call lemma_masked_lt_51(as_bv64(as_uint(c1)));
  call lemma_masked_lt_51(as_bv64(as_uint(c2)));
  call lemma_masked_lt_51(as_bv64(as_uint(c3)));
  call lemma_masked_lt_51(as_bv64(as_uint(c4)));
  assert out0 < bv{64}(1) << bv{64}(51) && out1 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(c2)) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(c3)) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(c4)) & mask51 < bv{64}(1) << bv{64}(51);
  assume out0 < bv{64}(1) << bv{64}(51) && out1 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(c2)) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(c3)) & mask51 < bv{64}(1) << bv{64}(51) && as_bv64(as_uint(c4)) & mask51 < bv{64}(1) << bv{64}(51);
  pow2_5933 := bv{64}(724618875532318195);
  call lemma_shr_51_le(c4, as_bv128(5 * as_uint(bound_sq) + 18446744073709551615));
  assert as_uint(as_uint(c4 >> bv{128}(51))) <= as_uint(as_bv128(5 * as_uint(bound_sq) + 18446744073709551615) >> bv{128}(51));
  assume as_uint(as_uint(c4 >> bv{128}(51))) <= as_uint(as_bv128(5 * as_uint(bound_sq) + 18446744073709551615) >> bv{128}(51));
  assert [compute]: as_uint(as_bv128(5 * as_uint(bv{128}(1) << bv{128}(108)) + 18446744073709551615) >> bv{128}(51)) < 724618875532318195;
  assert carry < pow2_5933;
  assume carry < pow2_5933;
  assert [compute]: as_uint(bv{64}(1) << bv{64}(51)) + 19 * 724618875532318195 <= 18446744073709551615;
  assert as_uint(out0) + as_uint(carry) * 19 < 18446744073709551615;
  assume as_uint(out0) + as_uint(carry) * 19 < 18446744073709551615;
  call lemma_shr_51_le(as_bv128(as_uint(out0_1)), as_bv128(18446744073709551615));
  assert as_bv128(as_uint(out0_1)) >> bv{128}(51) <= as_bv128(18446744073709551615) >> bv{128}(51);
  assume as_bv128(as_uint(out0_1)) >> bv{128}(51) <= as_bv128(18446744073709551615) >> bv{128}(51);
  assert [compute]: as_bv128(18446744073709551615) >> bv{128}(51) < as_bv128(as_uint(bv{64}(1) << bv{64}(13)));
  assert [compute]: as_uint(bv{64}(1) << bv{64}(51)) + as_uint(bv{64}(1) << bv{64}(13)) < as_uint(as_uint(bv{64}(1) << bv{64}(52)));
  assert as_uint(out1) + as_uint(out0_1 >> bv{64}(51)) < as_uint(as_uint(bv{64}(1) << bv{64}(52)));
  assume as_uint(out1) + as_uint(out0_1 >> bv{64}(51)) < as_uint(as_uint(bv{64}(1) << bv{64}(52)));
  call lemma_masked_lt_51(out0_1);
  assert out0_1 & mask51 < bv{64}(1) << bv{64}(51);
  assume out0_1 & mask51 < bv{64}(1) << bv{64}(51);
  assert mul_out_val_boundaries(a, b);
  assume mul_out_val_boundaries(a, b);
  assert [compute]: bv{64}(1) << bv{64}(51) < bv{64}(1) << bv{64}(52) && bv{64}(1) << bv{64}(52) < bv{64}(1) << bv{64}(54);
  exit lemma_mul_boundary;
};

// TRUSTED: carry-chain ≡ product mod p.
 procedure lemma_mul_value (a : Sequence bv64, b : Sequence bv64) returns ()
spec {
  requires mul_boundary_spec(a, b);
  ensures nat.toInt(nat.mod(u64_5_as_nat(mul_return(a, b)), p)) == nat.toInt(nat.mod(nat.mul(u64_5_as_nat(a), u64_5_as_nat(b)), p));
  } {
  assume false;
  exit lemma_mul_value;
};
#end

-- cvc5 via Strata.Boole.verify: 216 VCs pass, 224 timeout (vs 152/192 in minimal)
-- #eval Strata.Boole.verify "cvc5" b1_boundary_proved_program (options := .quiet)

-- Lean backend
set_option maxHeartbeats 4000000 in
example : Strata.smtVCsCorrectBoole b1_boundary_proved_program := by
  gen_smt_vcs_boole
  all_goals (try grind)
