import Strata.MetaVerifier

open Strata

private def sha256_compact_indexed_program : Strata.Program :=
#strata
program Boole;

 type nat;
 function int_to_nat (i : int) : nat;
 type Set (T : Type);
 function Seq_len<T> (s : Sequence T) : nat {
  int_to_nat(Sequence.length(s))
}
 function Seq_lib_insert<T> (s : Sequence T, i : int, val : T) : Sequence T {
  Sequence.append(Sequence.build(Sequence.take(s, i), val), Sequence.drop(s, i))
}
 function Seq_new<T> (len : nat, f : int -> T) : Sequence T;
 function Seq_lib_map<T, U> (s : Sequence T, f : int -> T -> U) : Sequence U;
 function Seq_lib_map_values<T, U> (s : Sequence T, f : T -> U) : Sequence U;
 function Seq_lib_filter<T> (s : Sequence T, p : T -> bool) : Sequence T;
 function Seq_lib_sort_by<T> (s : Sequence T, less : T -> T -> bool) : Sequence T;
 function Seq_lib_to_set<T> (s : Sequence T) : Set T;
 function Set_finite<T> (s : Set T) : bool;
 function bv64_to_int_u (x : bv64) : int;
 function bv8_to_bv32_u (x : bv8) : bv32;
 function k32 () : Sequence bv32 {
  Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.empty_bv32, bv{32}(1116352408)), bv{32}(1899447441)), bv{32}(3049323471)), bv{32}(3921009573)), bv{32}(961987163)), bv{32}(1508970993)), bv{32}(2453635748)), bv{32}(2870763221)), bv{32}(3624381080)), bv{32}(310598401)), bv{32}(607225278)), bv{32}(1426881987)), bv{32}(1925078388)), bv{32}(2162078206)), bv{32}(2614888103)), bv{32}(3248222580)), bv{32}(3835390401)), bv{32}(4022224774)), bv{32}(264347078)), bv{32}(604807628)), bv{32}(770255983)), bv{32}(1249150122)), bv{32}(1555081692)), bv{32}(1996064986)), bv{32}(2554220882)), bv{32}(2821834349)), bv{32}(2952996808)), bv{32}(3210313671)), bv{32}(3336571891)), bv{32}(3584528711)), bv{32}(113926993)), bv{32}(338241895)), bv{32}(666307205)), bv{32}(773529912)), bv{32}(1294757372)), bv{32}(1396182291)), bv{32}(1695183700)), bv{32}(1986661051)), bv{32}(2177026350)), bv{32}(2456956037)), bv{32}(2730485921)), bv{32}(2820302411)), bv{32}(3259730800)), bv{32}(3345764771)), bv{32}(3516065817)), bv{32}(3600352804)), bv{32}(4094571909)), bv{32}(275423344)), bv{32}(430227734)), bv{32}(506948616)), bv{32}(659060556)), bv{32}(883997877)), bv{32}(958139571)), bv{32}(1322822218)), bv{32}(1537002063)), bv{32}(1747873779)), bv{32}(1955562222)), bv{32}(2024104815)), bv{32}(2227730452)), bv{32}(2361852424)), bv{32}(2428436474)), bv{32}(2756734187)), bv{32}(3204031479)), bv{32}(3329325298))
}
 procedure rotate_right (x : bv32, n : bv32) returns (_pct_return : bv32)
spec {
  requires bv{32}(1) <= n && n < bv{32}(32);
  } {
  assert bv{32}(0) <= n && n < bv{32}(32);
  assert bv{32}(0) <= bv{32}(32) - n && bv{32}(32) - n < bv{32}(32);
  _pct_return := x >> n | (x << bv{32}(32) - n);
  exit rotate_right;
};
 procedure to_u32s (block : Sequence bv8) returns (_pct_return : (Sequence bv32))
spec {
  } {
  var j : bv64;
  var res : (Sequence bv32);
  res := Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.build(Sequence.empty_bv32, bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0)), bv{32}(0));
  for i : bv64 := bv{64}(0) to bv{64}(16) - bv{64}(1)
  {
    j := i * bv{64}(4);
    assert 0 <= 24 && 24 < 32;
    assert 0 <= 16 && 16 < 32;
    assert 0 <= 8 && 8 < 32;
    res := Sequence.update(res, bv64_to_int_u(i), bv8_to_bv32_u(Sequence.select(block, bv64_to_int_u(j))) << bv{32}(24) | (bv8_to_bv32_u(Sequence.select(block, bv64_to_int_u(j + bv{64}(1)))) << bv{32}(16)) | (bv8_to_bv32_u(Sequence.select(block, bv64_to_int_u(j + bv{64}(2)))) << bv{32}(8)) | bv8_to_bv32_u(Sequence.select(block, bv64_to_int_u(j + bv{64}(3)))));
  }

  _pct_return := res;
  exit to_u32s;
};
 procedure compress_u32 (state : Sequence bv32, block : Sequence bv32) returns (state_out : (Sequence bv32))
spec {
  } {
  var tmp15 : bv32;
  var tmp16 : bv32;
  var tmp22 : bv32;
  var tmp23 : bv32;
  var w15 : bv32;
  var s0 : bv32;
  var w2 : bv32;
  var s1 : bv32;
  var new_w : bv32;
  var tmp36 : bv32;
  var tmp37 : bv32;
  var tmp38 : bv32;
  var tmp40 : bv32;
  var tmp44 : (Sequence bv32);
  var tmp48 : bv32;
  var tmp49 : bv32;
  var tmp51 : bv32;
  var w : bv32;
  var ch : bv32;
  var t1 : bv32;
  var maj : bv32;
  var t2 : bv32;
  var a : bv32;
  var b : bv32;
  var c : bv32;
  var d : bv32;
  var e : bv32;
  var f : bv32;
  var g : bv32;
  var h : bv32;
  state_out := state;
  a := Sequence.select(state_out, bv64_to_int_u(bv{64}(0)));
  b := Sequence.select(state_out, bv64_to_int_u(bv{64}(1)));
  c := Sequence.select(state_out, bv64_to_int_u(bv{64}(2)));
  d := Sequence.select(state_out, bv64_to_int_u(bv{64}(3)));
  e := Sequence.select(state_out, bv64_to_int_u(bv{64}(4)));
  f := Sequence.select(state_out, bv64_to_int_u(bv{64}(5)));
  g := Sequence.select(state_out, bv64_to_int_u(bv{64}(6)));
  h := Sequence.select(state_out, bv64_to_int_u(bv{64}(7)));
  for i : bv64 := bv{64}(0) to bv{64}(64) - bv{64}(1)
  {
    if (i < bv{64}(16)) {
      tmp36 := Sequence.select(block, bv64_to_int_u(i));
    } else {
      assert bv{64}(16) != bv{64}(0);
      w15 := Sequence.select(block, bv64_to_int_u((i - bv{64}(15)) mod bv{64}(16)));
      call tmp15 := rotate_right(w15, bv{32}(7));

      call tmp16 := rotate_right(w15, bv{32}(18));

      assert 0 <= 3 && 3 < 32;
      s0 := tmp15 ^ tmp16 ^ (w15 >> bv{32}(3));
      assert bv{64}(16) != bv{64}(0);
      w2 := Sequence.select(block, bv64_to_int_u((i - bv{64}(2)) mod bv{64}(16)));
      call tmp22 := rotate_right(w2, bv{32}(17));

      call tmp23 := rotate_right(w2, bv{32}(19));

      assert 0 <= 10 && 10 < 32;
      s1 := tmp22 ^ tmp23 ^ (w2 >> bv{32}(10));
      assert bv{64}(16) != bv{64}(0);
      assert bv{64}(16) != bv{64}(0);
      new_w := Sequence.select(block, bv64_to_int_u((i - bv{64}(16)) mod bv{64}(16))) + s0 + Sequence.select(block, bv64_to_int_u((i - bv{64}(7)) mod bv{64}(16))) + s1;
      assert bv{64}(16) != bv{64}(0);
      block := Sequence.update(block, bv64_to_int_u(i mod bv{64}(16)), new_w);
      tmp36 := new_w;
    }
    w := tmp36;
    call tmp37 := rotate_right(e, bv{32}(6));

    call tmp38 := rotate_right(e, bv{32}(11));

    call tmp40 := rotate_right(e, bv{32}(25));

    s1 := tmp37 ^ tmp38 ^ tmp40;
    ch := e & f ^ (~e & g);
    tmp44 := k32();
    t1 := s1 + ch + Sequence.select(tmp44, bv64_to_int_u(i)) + w + h;
    call tmp48 := rotate_right(a, bv{32}(2));

    call tmp49 := rotate_right(a, bv{32}(13));

    call tmp51 := rotate_right(a, bv{32}(22));

    s0 := tmp48 ^ tmp49 ^ tmp51;
    maj := a & b ^ (a & c) ^ (b & c);
    t2 := s0 + maj;
    h := g;
    g := f;
    f := e;
    e := d + t1;
    d := c;
    c := b;
    b := a;
    a := t1 + t2;
  }

  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(0)), Sequence.select(state_out, bv64_to_int_u(bv{64}(0))) + a);
  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(1)), Sequence.select(state_out, bv64_to_int_u(bv{64}(1))) + b);
  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(2)), Sequence.select(state_out, bv64_to_int_u(bv{64}(2))) + c);
  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(3)), Sequence.select(state_out, bv64_to_int_u(bv{64}(3))) + d);
  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(4)), Sequence.select(state_out, bv64_to_int_u(bv{64}(4))) + e);
  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(5)), Sequence.select(state_out, bv64_to_int_u(bv{64}(5))) + f);
  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(6)), Sequence.select(state_out, bv64_to_int_u(bv{64}(6))) + g);
  state_out := Sequence.update(state_out, bv64_to_int_u(bv{64}(7)), Sequence.select(state_out, bv64_to_int_u(bv{64}(7))) + h);
  exit compress_u32;
};
 procedure compress (state : Sequence bv32, blocks : Sequence (Sequence bv8)) returns (state_out : (Sequence bv32))
spec {
  } {
  var tmp1 : bv64;
  var tmp2 : bv64;
  var tmp4 : (Sequence bv32);
  var k : bv64;
  state_out := state;
  k := bv{64}(0);
  while (bv64_to_int_u(k) < Sequence.length(blocks))
  decreases Sequence.length(blocks) - bv64_to_int_u(k)
  invariant bv64_to_int_u(k) <= Sequence.length(blocks)
  {
    call tmp4 := to_u32s(Sequence.select(blocks, bv64_to_int_u(k)));

    call state_out := compress_u32(state_out, tmp4);

    k := k + bv{64}(1);
  }
  exit compress;
};
 procedure main () returns ()
spec {
  } {
  exit main;
};
#end
-- TODO pending fixing
--#eval Strata.Boole.verify "cvc5" sha256_compact_indexed_program (options := .quiet)
