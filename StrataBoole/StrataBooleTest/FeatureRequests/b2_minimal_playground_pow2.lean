/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Benchmark B2 — `Scalar::from_bytes_mod_order_wide` (VARIANT: abstract array
types, arithmetic facts as axioms)

Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
File:   curve25519-dalek/src/backend/serial/u64/scalar.rs
        (`from_bytes_mod_order_wide`, `pack`)

Same benchmark and trust boundary as `b2_minimal.lean`, with two differences.

Array encoding: `[u64; 5]` and `[u8; 32]` are modeled as abstract types
`array5` / `array32` with uninterpreted `get`, `toSeq`, `ofSeq` and axioms
relating them (`get(v, i) == Sequence.select(toSeq(v), i)`,
`Sequence.length(toSeq(v)) == N`). The types have no constructor, so the
axioms are consistent: interpreting `array5` as the length-5 sequences gives
a model. The `toSeq`/`ofSeq` round-trip axiom is omitted, and `ofSeq`
requires its input to have length N.

Arithmetic facts: instead of calling vstd lemmas inside procedure bodies,
the pow2 values (`pow2(0)`..`pow2(64)` and the large constants `pow2(126)`,
`pow2(252)`..`pow2(256)`), the pow2 algebra, the nat/int coercion laws, and
the uniform-reduction lemma are stated as global axioms. The
uniform-reduction axiom keeps the same guard as in `b2_minimal.lean`
(`canonical(result) == bytes_as_nat(input) mod group_order`).

Results: cvc5 reports 2 timeout VCs (`b2_minimal.lean`, the bv128 variant,
leaves 39); grind closes 16 of 25 goals. The quantified axioms make grind's
queries harder, so the closing theorem below is left commented.

Status: this file uses the `as_uint` cast syntax from pr/casts-boole, which
this branch does not have yet; the `#exit` below keeps it inert until then.
-/

#exit

open Strata

private def b2_minimal_playground_pow2_program : StrataDDM.Program :=
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
 function bv64_to_nat_u (x : bv64) : nat;
 const Seq_map_empty_0:Sequence nat;
 axiom Sequence.length(Seq_map_empty_0) == 0;
 function Seq_map_closure_0 (_i : int, x : bv64) : nat {
  bv64_to_nat_u(x)
}
 rec function Seq_map_rec_0 (s : Sequence bv64, n : int) : Sequence nat
requires 0 <= n && n <= Sequence.length(s);
decreases n
  {
  if n <= 0 then Seq_map_empty_0 else Sequence.build(Seq_map_rec_0(s, n - 1), Seq_map_closure_0(n - 1, Sequence.select(s, n - 1)))
};

 type array5;
 function array5.get (v : array5, i : int) : bv64;
 function array5.len (v : array5) : int { 5 }
 function array5.ofSeqAux (s : Sequence bv64) : array5;
 function array5.ofSeq (s : Sequence bv64) : array5
  requires Sequence.length(s) == 5;
   {
    array5.ofSeqAux(s)
  }
 function array5.toSeq (v : array5) : Sequence bv64;
 axiom [array5_toSeq_get]: forall v : array5, i : int :: 0 <= i && i < 5 ==> array5.get(v, i) == Sequence.select(array5.toSeq(v), i);
//  axiom [array5_ofSeq_toSeq]: forall s : Sequence bv64 :: Sequence.length(s) == 5 ==> array5.toSeq(array5.ofSeq(s)) == s;
 axiom [array5_ofSeq_get]: forall s : Sequence bv64, i : int :: 0 <= i && i < 5 ==> array5.get(array5.ofSeq(s), i) == Sequence.select(s, i);
 axiom [array5_toSeq_len]: forall v : array5 :: Sequence.length(array5.toSeq(v)) == 5;

 type array32;
 function array32.get (v : array32, i : int) : bv8;
 function array32.len (v : array32) : int { 32 }
 function array32.ofSeqAux (s : Sequence bv8) : array32;
 function array32.ofSeq (s : Sequence bv8) : array32
  requires Sequence.length(s) == 32;
   {
    array32.ofSeqAux(s)
  }
 function array32.toSeq (v : array32) : Sequence bv8;
 axiom [array32_toSeq_get]: forall v : array32, i : int :: 0 <= i && i < 32 ==> array32.get(v, i) == Sequence.select(array32.toSeq(v), i);
 axiom [array32_ofSeq_get]: forall s : Sequence bv8, i : int :: 0 <= i && i < 32 ==> array32.get(array32.ofSeq(s), i) == Sequence.select(s, i);
 axiom [array32_toSeq_len]: forall v : array32 :: Sequence.length(array32.toSeq(v)) == 32;

 type scalar52 := array5;
 type scalar := array32;

 function Array_spec_array_as_slice<T> (ar : Sequence T) : Sequence T;
 function Arithmetic_Power2_pow2 (e : nat) : nat;
 axiom [pow2_adds]: forall e1 : nat, e2 : nat :: Arithmetic_Power2_pow2(nat.add(e1, e2)) == nat.mul(Arithmetic_Power2_pow2(e1), Arithmetic_Power2_pow2(e2));
 axiom [pow2_strictly_increases]: forall e1 : nat, e2 : nat :: nat.lt(e1, e2) ==> nat.lt(Arithmetic_Power2_pow2(e1), Arithmetic_Power2_pow2(e2));
 function is_uniform_bytes (bytes : Sequence bv8) : bool;
 function is_uniform_scalar (s : scalar) : bool;
 rec function bytes_seq_as_nat (bytes : Sequence bv8) : nat
decreases Sequence.length(bytes)
  {
  if Sequence.length(bytes) == 0 then nat.fromInt(0) else nat.fromInt(as_uint(Sequence.select(bytes, 0)) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(8))) * nat.toInt(bytes_seq_as_nat(Sequence.subrange(bytes, 1, Sequence.length(bytes)))))
};
 rec function u8_32_as_nat (bytes : Sequence bv8) : nat
decreases Sequence.length(bytes)
  {
  if Sequence.length(bytes) == 0 then nat.fromInt(0) else nat.add(nat.fromInt(as_uint(Sequence.select(bytes, 0))), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(8)), u8_32_as_nat(Sequence.subrange(bytes, 1, Sequence.length(bytes)))))
};
 function group_order () : nat {
  nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), nat.fromInt(27742317777372353535851937790883648493))
}
 function group_canonical (n : nat) : nat {
  nat.fromInt(nat.toInt(n) mod nat.toInt(group_order))
}
 rec function seq_as_nat_52 (limbs : Sequence nat) : nat
decreases Sequence.length(limbs)
  {
  if Sequence.length(limbs) == 0 then nat.fromInt(0) else nat.add(Sequence.select(limbs, 0), nat.mul(seq_as_nat_52(Sequence.subrange(limbs, 1, Sequence.length(limbs))), Arithmetic_Power2_pow2(nat.fromInt(52))))
};
 function limbs52_as_nat (limbs : Sequence bv64) : nat {
  seq_as_nat_52(Seq_map_rec_0(limbs, Sequence.length(limbs)))
}
 function scalar52_as_nat (s : scalar52) : nat {
  limbs52_as_nat(Array_spec_array_as_slice(array5.toSeq(s)))
}
 function limbs_bounded (s : scalar52) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> array5.get(s, i) < bv{64}(1) << bv{64}(52)
}
 function is_canonical_scalar52 (s : scalar52) : bool {
  limbs_bounded(s) && nat.lt(scalar52_as_nat(s), group_order)
}
 function is_canonical_scalar (s : scalar) : bool {
  nat.lt(u8_32_as_nat(array32.toSeq(s)), group_order) && array32.get(s, 31) <= bv{8}(127)
}
 function scalar_as_canonical (s : scalar) : nat {
  group_canonical(u8_32_as_nat(array32.toSeq(s)))
}
 procedure Impl__3_from_bytes_wide (bytes : Sequence bv8) returns (s : scalar52)
spec {
  ensures is_canonical_scalar52(s);
  ensures scalar52_as_nat(s) == group_canonical(bytes_seq_as_nat(bytes));
  } {
  assume false;
  s := array5.ofSeq(Sequence.of_bv64[bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)]);
  exit Impl__3_from_bytes_wide;
};
 procedure Impl__3_pack (self : scalar52) returns (result : scalar)
spec {
  requires limbs_bounded(self);
  ensures nat.toInt(u8_32_as_nat(array32.toSeq(result))) == nat.toInt(scalar52_as_nat(self)) mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(256)));
  ensures nat.lt(scalar52_as_nat(self), group_order) ==> is_canonical_scalar(result);
  } {
  assume false;
  result := array32.ofSeq(Sequence.of_bv8[bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0)]);
  exit Impl__3_pack;
};
 procedure Impl__4_from_bytes_mod_order_wide (input : Sequence bv8) returns (result : scalar)
spec {
  ensures scalar_as_canonical(result) == group_canonical(bytes_seq_as_nat(input));
  ensures is_canonical_scalar(result);
  ensures is_uniform_bytes(input) ==> is_uniform_scalar(result);
  } {
  var tmp1 : nat;
  var tmp2 : nat;
  var tmp3 : nat;
  var tmp4 : nat;
  var tmp5 : nat;
  var tmp6 : nat;
  var unpacked : scalar52;
  call unpacked := Impl__3_from_bytes_wide(input);

  call result := Impl__3_pack(unpacked);

  call lemma_group_order_smaller_than_pow256();
  call lemma_scalar52_lt_pow2_256_if_canonical(unpacked);
  tmp1 := scalar52_as_nat(unpacked);
  tmp2 := Arithmetic_Power2_pow2(nat.fromInt(256));
  call Arithmetic_Div_mod_lemma_small_mod(tmp1, tmp2);
  tmp3 := bytes_seq_as_nat(input);
  tmp4 := group_order;
  call Arithmetic_Div_mod_lemma_mod_bound(nat.toInt(tmp3), nat.toInt(tmp4));
  tmp5 := u8_32_as_nat(array32.toSeq(result));
  tmp6 := group_order;
  call Arithmetic_Div_mod_lemma_small_mod(tmp5, tmp6);
  result := result;
  exit Impl__4_from_bytes_mod_order_wide;
};
 procedure Arithmetic_Div_mod_lemma_small_mod (x : nat, m : nat) returns ()
spec {
  requires nat.lt(x, m);
  requires 0 < nat.toInt(m);
  ensures nat.toInt(x) mod nat.toInt(m) == nat.toInt(x);
  } {
};
 procedure Arithmetic_Div_mod_lemma_mod_bound (x : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures 0 <= x mod m && x mod m < m;
  } {
};
 axiom [Arithmetic_Power2_lemma2_to64_0]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(0))) == 1;
 axiom [Arithmetic_Power2_lemma2_to64_1]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(1))) == 2;
 axiom [Arithmetic_Power2_lemma2_to64_2]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(2))) == 4;
 axiom [Arithmetic_Power2_lemma2_to64_3]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(3))) == 8;
 axiom [Arithmetic_Power2_lemma2_to64_4]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(4))) == 16;
 axiom [Arithmetic_Power2_lemma2_to64_5]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(5))) == 32;
 axiom [Arithmetic_Power2_lemma2_to64_6]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(6))) == 64;
 axiom [Arithmetic_Power2_lemma2_to64_7]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(7))) == 128;
 axiom [Arithmetic_Power2_lemma2_to64_8]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(8))) == 256;
 axiom [Arithmetic_Power2_lemma2_to64_9]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(9))) == 512;
 axiom [Arithmetic_Power2_lemma2_to64_10]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(10))) == 1024;
 axiom [Arithmetic_Power2_lemma2_to64_11]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(11))) == 2048;
 axiom [Arithmetic_Power2_lemma2_to64_12]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(12))) == 4096;
 axiom [Arithmetic_Power2_lemma2_to64_13]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(13))) == 8192;
 axiom [Arithmetic_Power2_lemma2_to64_14]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(14))) == 16384;
 axiom [Arithmetic_Power2_lemma2_to64_15]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(15))) == 32768;
 axiom [Arithmetic_Power2_lemma2_to64_16]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(16))) == 65536;
 axiom [Arithmetic_Power2_lemma2_to64_17]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(17))) == 131072;
 axiom [Arithmetic_Power2_lemma2_to64_18]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(18))) == 262144;
 axiom [Arithmetic_Power2_lemma2_to64_19]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(19))) == 524288;
 axiom [Arithmetic_Power2_lemma2_to64_20]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(20))) == 1048576;
 axiom [Arithmetic_Power2_lemma2_to64_21]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(21))) == 2097152;
 axiom [Arithmetic_Power2_lemma2_to64_22]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(22))) == 4194304;
 axiom [Arithmetic_Power2_lemma2_to64_23]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(23))) == 8388608;
 axiom [Arithmetic_Power2_lemma2_to64_24]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(24))) == 16777216;
 axiom [Arithmetic_Power2_lemma2_to64_25]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(25))) == 33554432;
 axiom [Arithmetic_Power2_lemma2_to64_26]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(26))) == 67108864;
 axiom [Arithmetic_Power2_lemma2_to64_27]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(27))) == 134217728;
 axiom [Arithmetic_Power2_lemma2_to64_28]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(28))) == 268435456;
 axiom [Arithmetic_Power2_lemma2_to64_29]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(29))) == 536870912;
 axiom [Arithmetic_Power2_lemma2_to64_30]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(30))) == 1073741824;
 axiom [Arithmetic_Power2_lemma2_to64_31]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(31))) == 2147483648;
 axiom [Arithmetic_Power2_lemma2_to64_32]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(32))) == 4294967296;
 axiom [Arithmetic_Power2_lemma2_to64_33]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(64))) == 18446744073709551616;
 axiom [Arithmetic_Power2_lemma2_to64_rest_0]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(33))) == 8589934592;
 axiom [Arithmetic_Power2_lemma2_to64_rest_1]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(34))) == 17179869184;
 axiom [Arithmetic_Power2_lemma2_to64_rest_2]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(35))) == 34359738368;
 axiom [Arithmetic_Power2_lemma2_to64_rest_3]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(36))) == 68719476736;
 axiom [Arithmetic_Power2_lemma2_to64_rest_4]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(37))) == 137438953472;
 axiom [Arithmetic_Power2_lemma2_to64_rest_5]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(38))) == 274877906944;
 axiom [Arithmetic_Power2_lemma2_to64_rest_6]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(39))) == 549755813888;
 axiom [Arithmetic_Power2_lemma2_to64_rest_7]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(40))) == 1099511627776;
 axiom [Arithmetic_Power2_lemma2_to64_rest_8]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(41))) == 2199023255552;
 axiom [Arithmetic_Power2_lemma2_to64_rest_9]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(42))) == 4398046511104;
 axiom [Arithmetic_Power2_lemma2_to64_rest_10]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(43))) == 8796093022208;
 axiom [Arithmetic_Power2_lemma2_to64_rest_11]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(44))) == 17592186044416;
 axiom [Arithmetic_Power2_lemma2_to64_rest_12]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(45))) == 35184372088832;
 axiom [Arithmetic_Power2_lemma2_to64_rest_13]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(46))) == 70368744177664;
 axiom [Arithmetic_Power2_lemma2_to64_rest_14]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(47))) == 140737488355328;
 axiom [Arithmetic_Power2_lemma2_to64_rest_15]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(48))) == 281474976710656;
 axiom [Arithmetic_Power2_lemma2_to64_rest_16]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(49))) == 562949953421312;
 axiom [Arithmetic_Power2_lemma2_to64_rest_17]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(50))) == 1125899906842624;
 axiom [Arithmetic_Power2_lemma2_to64_rest_18]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) == 2251799813685248;
 axiom [Arithmetic_Power2_lemma2_to64_rest_19]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(52))) == 4503599627370496;
 axiom [Arithmetic_Power2_lemma2_to64_rest_20]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(53))) == 9007199254740992;
 axiom [Arithmetic_Power2_lemma2_to64_rest_21]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(54))) == 18014398509481984;
 axiom [Arithmetic_Power2_lemma2_to64_rest_22]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(55))) == 36028797018963968;
 axiom [Arithmetic_Power2_lemma2_to64_rest_23]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(56))) == 72057594037927936;
 axiom [Arithmetic_Power2_lemma2_to64_rest_24]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(57))) == 144115188075855872;
 axiom [Arithmetic_Power2_lemma2_to64_rest_25]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(58))) == 288230376151711744;
 axiom [Arithmetic_Power2_lemma2_to64_rest_26]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(59))) == 576460752303423488;
 axiom [Arithmetic_Power2_lemma2_to64_rest_27]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(60))) == 1152921504606846976;
 axiom [Arithmetic_Power2_lemma2_to64_rest_28]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(61))) == 2305843009213693952;
 axiom [Arithmetic_Power2_lemma2_to64_rest_29]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(62))) == 4611686018427387904;
 axiom [Arithmetic_Power2_lemma2_to64_rest_30]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
 axiom [Arithmetic_Power2_lemma2_to64_rest_31]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(64))) == 18446744073709551616;
 axiom [pow2_126]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(126))) == 85070591730234615865843651857942052864;
 axiom [pow2_252]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(252))) == 7237005577332262213973186563042994240829374041602535252466099000494570602496;
 axiom [pow2_253]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(253))) == 14474011154664524427946373126085988481658748083205070504932198000989141204992;
 axiom [pow2_255]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(255))) == 57896044618658097711785492504343953926634992332820282019728792003956564819968;
 axiom [pow2_256]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(256))) == 115792089237316195423570985008687907853269984665640564039457584007913129639936;
 procedure lemma_group_order_bound () returns ()
spec {
  ensures nat.lt(group_order, Arithmetic_Power2_pow2(nat.fromInt(255)));
  } {
  assume 27742317777372353535851937790883648493 < 85070591730234615865843651857942052864;
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(126))) == 85070591730234615865843651857942052864;
  assert 27742317777372353535851937790883648493 < nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(126)));
  assert nat.lt(group_order, nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), Arithmetic_Power2_pow2(nat.fromInt(252))));
  assert nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), Arithmetic_Power2_pow2(nat.fromInt(252))) == Arithmetic_Power2_pow2(nat.fromInt(253));
  assume nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), Arithmetic_Power2_pow2(nat.fromInt(252))) == Arithmetic_Power2_pow2(nat.fromInt(253));
  exit lemma_group_order_bound;
};
 procedure lemma_group_order_smaller_than_pow256 () returns ()
spec {
  ensures nat.lt(group_order, Arithmetic_Power2_pow2(nat.fromInt(256)));
  } {
  call lemma_group_order_bound();
  exit lemma_group_order_smaller_than_pow256;
};
 procedure lemma_scalar52_lt_pow2_256_if_canonical (a : scalar52) returns ()
spec {
  requires limbs_bounded(a);
  requires nat.lt(scalar52_as_nat(a), group_order);
  ensures nat.lt(scalar52_as_nat(a), Arithmetic_Power2_pow2(nat.fromInt(256)));
  } {
  call lemma_group_order_bound();
  exit lemma_scalar52_lt_pow2_256_if_canonical;
};
 axiom [uniform_mod_reduction]: forall input : Sequence bv8, result : scalar ::
  nat.toInt(scalar_as_canonical(result)) == nat.toInt(bytes_seq_as_nat(input)) mod nat.toInt(group_order) ==>
  (is_uniform_bytes(input) ==> is_uniform_scalar(result));
#end

-- cvc5 via Strata.Boole.verify: 2 timeout VCs
-- #eval Strata.Boole.verify "cvc5" b2_minimal_playground_pow2_program (options := .quiet)

-- Lean backend: gen_smt_vcs_boole; grind closes 16 of 25 goals
-- set_option maxHeartbeats 4000000 in
-- theorem b2_minimal_playground_pow2_smt_vcs_correct :
--     Strata.smtVCsCorrectBoole b2_minimal_playground_pow2_program := by
--   gen_smt_vcs_boole
--   all_goals (try grind)
