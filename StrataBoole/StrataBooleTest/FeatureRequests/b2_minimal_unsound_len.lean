/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
Benchmark B2 — `Scalar::from_bytes_mod_order_wide`
(REFERENCE VARIANT — **UNSOUND**, do not treat as verified)

Same benchmark as `b2_minimal.lean`, kept to document a previous unsound version
that vacuously verifies, because the fixed-size arrays are modeled as
**total datatypes** with a **global length axiom**:

    datatype scalar52 { scalar52_ctor(limbs : Sequence bv64) ... }
    axiom [scalar52_limbs_len]: ∀ s : scalar52 :: Sequence.length(scalar52..limbs(s)) == 5;
    axiom [scalar_bytes_len]:   ∀ s : scalar   :: Sequence.length(scalar..bytes(s))   == 32;

The constructor is total — it accepts a sequence of *any* length — so
`scalar52_ctor(emptySeq)` is a well-formed `scalar52` whose `limbs` has length 0.
The axiom then forces `0 == 5`, a contradiction, from which every goal is
provable. The verifier reports "all VCs pass", but vacuously.
-/

open Strata

private def b2_minimal_unsound_len_program : StrataDDM.Program :=
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
 function bv8_to_nat_u (x : bv8) : nat;
 function bv64_to_nat_u (x : bv64) : nat;
 const Seq_map_empty_0:Sequence nat;
 axiom Sequence.length(Seq_map_empty_0) == 0;
 function Seq_map_closure_0 (_i : int, x : bv64) : nat {
  bv64_to_nat_u(x)
}
 rec function Seq_map_rec_0 (s : Sequence bv64, n : int) : Sequence nat requires 0 <= n && n <= Sequence.length(s);

decreases n
  {
  if n <= 0 then Seq_map_empty_0 else Sequence.build(Seq_map_rec_0(s, n - 1), Seq_map_closure_0(n - 1, Sequence.select(s, n - 1)))
};
 datatype scalar52 {
  scalar52_ctor(limbs : Sequence bv64)
};
 axiom [scalar52_limbs_len]: ∀ s : scalar52 :: Sequence.length(scalar52..limbs(s)) == 5;
 datatype scalar {
  scalar_ctor(bytes : Sequence bv8)
};
 axiom [scalar_bytes_len]: ∀ s : scalar :: Sequence.length(scalar..bytes(s)) == 32;
 function Array_spec_array_as_slice<T> (ar : Sequence T) : Sequence T;
 function Arithmetic_Power2_pow2 (e : nat) : nat;
 function is_uniform_bytes (bytes : Sequence bv8) : bool;
 function is_uniform_scalar (s : scalar) : bool;
 rec function bytes_seq_as_nat (bytes : Sequence bv8) : nat
decreases Sequence.length(bytes)
  {
  if Sequence.length(bytes) == 0 then nat.fromInt(0) else nat.add(bv8_to_nat_u(Sequence.select(bytes, 0)), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(8)), bytes_seq_as_nat(Sequence.subrange(bytes, 1, Sequence.length(bytes)))))
};
 function u8_32_as_nat (bytes : Sequence bv8) : nat {
  nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.add(nat.mul(bv8_to_nat_u(Sequence.select(bytes, 0)), Arithmetic_Power2_pow2(nat.fromInt(0))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 1)), Arithmetic_Power2_pow2(nat.fromInt(8)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 2)), Arithmetic_Power2_pow2(nat.fromInt(16)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 3)), Arithmetic_Power2_pow2(nat.fromInt(24)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 4)), Arithmetic_Power2_pow2(nat.fromInt(32)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 5)), Arithmetic_Power2_pow2(nat.fromInt(40)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 6)), Arithmetic_Power2_pow2(nat.fromInt(48)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 7)), Arithmetic_Power2_pow2(nat.fromInt(56)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 8)), Arithmetic_Power2_pow2(nat.fromInt(64)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 9)), Arithmetic_Power2_pow2(nat.fromInt(72)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 10)), Arithmetic_Power2_pow2(nat.fromInt(80)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 11)), Arithmetic_Power2_pow2(nat.fromInt(88)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 12)), Arithmetic_Power2_pow2(nat.fromInt(96)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 13)), Arithmetic_Power2_pow2(nat.fromInt(104)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 14)), Arithmetic_Power2_pow2(nat.fromInt(112)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 15)), Arithmetic_Power2_pow2(nat.fromInt(120)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 16)), Arithmetic_Power2_pow2(nat.fromInt(128)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 17)), Arithmetic_Power2_pow2(nat.fromInt(136)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 18)), Arithmetic_Power2_pow2(nat.fromInt(144)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 19)), Arithmetic_Power2_pow2(nat.fromInt(152)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 20)), Arithmetic_Power2_pow2(nat.fromInt(160)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 21)), Arithmetic_Power2_pow2(nat.fromInt(168)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 22)), Arithmetic_Power2_pow2(nat.fromInt(176)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 23)), Arithmetic_Power2_pow2(nat.fromInt(184)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 24)), Arithmetic_Power2_pow2(nat.fromInt(192)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 25)), Arithmetic_Power2_pow2(nat.fromInt(200)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 26)), Arithmetic_Power2_pow2(nat.fromInt(208)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 27)), Arithmetic_Power2_pow2(nat.fromInt(216)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 28)), Arithmetic_Power2_pow2(nat.fromInt(224)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 29)), Arithmetic_Power2_pow2(nat.fromInt(232)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 30)), Arithmetic_Power2_pow2(nat.fromInt(240)))), nat.mul(bv8_to_nat_u(Sequence.select(bytes, 31)), Arithmetic_Power2_pow2(nat.fromInt(248))))
}
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
  limbs52_as_nat(Array_spec_array_as_slice(scalar52..limbs(s)))
}
 function limbs_bounded (s : scalar52) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(scalar52..limbs(s), i) < bv{64}(1) << bv{64}(52)
}
 function is_canonical_scalar52 (s : scalar52) : bool {
  limbs_bounded(s) && nat.lt(scalar52_as_nat(s), group_order)
}
 function is_canonical_scalar (s : scalar) : bool {
  nat.lt(u8_32_as_nat(scalar..bytes(s)), group_order) && Sequence.select(scalar..bytes(s), 31) <= bv{8}(127)
}
 function scalar_as_canonical (s : scalar) : nat {
  group_canonical(u8_32_as_nat(scalar..bytes(s)))
}
 procedure Impl__2_clone (self : scalar52) returns (_pct_return : scalar52)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__2_clone;
};
 procedure Impl__3_from_bytes_wide (bytes : Sequence bv8) returns (s : scalar52)
spec {
  ensures is_canonical_scalar52(s);
  ensures nat.toInt(scalar52_as_nat(s)) == nat.toInt(group_canonical(bytes_seq_as_nat(bytes)));
  } {
  assume Sequence.length(bytes) == 64;
  assume false;
  s := scalar52_ctor(Sequence.of_bv64[bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)]);
  exit Impl__3_from_bytes_wide;
};
 procedure Impl__3_pack (self : scalar52) returns (result : scalar)
spec {
  requires limbs_bounded(self);
  ensures nat.toInt(u8_32_as_nat(scalar..bytes(result))) == nat.toInt(scalar52_as_nat(self)) mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(256)));
  ensures nat.lt(scalar52_as_nat(self), group_order) ==> is_canonical_scalar(result);
  } {
  assume false;
  result := scalar_ctor(Sequence.of_bv8[bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0)]);
  exit Impl__3_pack;
};
 procedure Impl__4_from_bytes_mod_order_wide (input : Sequence bv8) returns (result : scalar)
spec {
  ensures nat.toInt(scalar_as_canonical(result)) == nat.toInt(group_canonical(bytes_seq_as_nat(input)));
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
  assume Sequence.length(input) == 64;
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
  tmp5 := u8_32_as_nat(scalar..bytes(result));
  tmp6 := group_order;
  call Arithmetic_Div_mod_lemma_small_mod(tmp5, tmp6);
  call axiom_uniform_mod_reduction(input, result);
  result := result;
  exit Impl__4_from_bytes_mod_order_wide;
};
 procedure Arithmetic_Div_mod_lemma_small_mod (x : nat, m : nat) returns ()
spec {
  requires nat.lt(x, m);
  requires nat.lt(nat.fromInt(0), m);
  ensures nat.toInt(x) mod nat.toInt(m) == nat.toInt(x);
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
 procedure lemma_group_order_bound () returns ()
spec {
  ensures nat.lt(group_order, Arithmetic_Power2_pow2(nat.fromInt(255)));
  } {
  assume nat.lt(nat.fromInt(27742317777372353535851937790883648493), nat.fromInt(85070591730234615865843651857942052864));
  call Arithmetic_Power2_lemma2_to64_rest();
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(63), nat.fromInt(63));
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(126))) == 85070591730234615865843651857942052864;
  assert nat.lt(nat.fromInt(27742317777372353535851937790883648493), Arithmetic_Power2_pow2(nat.fromInt(126)));
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(126), nat.fromInt(252));
  assert nat.lt(group_order, nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), Arithmetic_Power2_pow2(nat.fromInt(252))));
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(1), nat.fromInt(252));
  call Arithmetic_Power2_lemma2_to64();
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(252))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(252))) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(253)));
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(252))) + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(252))) == nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(253)));
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(253), nat.fromInt(255));
  exit lemma_group_order_bound;
};
 procedure lemma_group_order_smaller_than_pow256 () returns ()
spec {
  ensures nat.lt(group_order, Arithmetic_Power2_pow2(nat.fromInt(256)));
  } {
  call lemma_group_order_bound();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(255), nat.fromInt(256));
  exit lemma_group_order_smaller_than_pow256;
};
 procedure lemma_scalar52_lt_pow2_256_if_canonical (a : scalar52) returns ()
spec {
  requires limbs_bounded(a);
  requires nat.lt(scalar52_as_nat(a), group_order);
  ensures nat.lt(scalar52_as_nat(a), Arithmetic_Power2_pow2(nat.fromInt(256)));
  } {
  call lemma_group_order_bound();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(255), nat.fromInt(256));
  exit lemma_scalar52_lt_pow2_256_if_canonical;
};
 procedure axiom_uniform_mod_reduction (input : Sequence bv8, result : scalar) returns ()
spec {
  requires nat.toInt(scalar_as_canonical(result)) == nat.toInt(bytes_seq_as_nat(input)) mod nat.toInt(group_order);
  ensures is_uniform_bytes(input) ==> is_uniform_scalar(result);
  } {
  assume false;
  exit axiom_uniform_mod_reduction;
};
#end

-- cvc5 reports "all VCs pass"
-- #eval Strata.Boole.verify "cvc5" b2_minimal_unsound_len_program (options := .quiet)
