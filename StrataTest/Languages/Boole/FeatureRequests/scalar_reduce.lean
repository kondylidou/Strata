/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchor:
- Source: dalek-lite `curve25519-dalek/src/scalar.rs`
  `Scalar::from_bytes_mod_order_wide` (line 300–348) — reduces a 64-byte
  SHA-512 hash output modulo the group order ℓ to a canonical scalar (B2).
  The axiom pattern also covers `from_bytes_mod_order` (line 273–291, 32-byte).

Implemented:
- `ByteArray64` and `Scalar` kept abstract — no byte-array indexing or
  struct-field access needed for this seed.
- `u8_64_as_group_canonical` stays abstract; its recursive byte-accumulation
  definition requires int-based termination over sequences (open Gap #11).
- Two axioms capture what `reduce` guarantees; the procedure body verifies
  by axiom instantiation alone.

Remaining gap:
- Spelling out `u8_64_as_group_canonical` recursively requires Gap #11.
- `Scalar { bytes }` struct construction requires Gap #13.
-/

private def scalarReduceSeed : Strata.Program :=
#strata
program Boole;

type ByteArray64;
type Scalar;

function reduce(b: ByteArray64) : Scalar;
function scalar_as_canonical(s: Scalar) : int;
function u8_64_as_group_canonical(b: ByteArray64) : int;
function is_canonical_scalar(s: Scalar) : bool;

axiom (∀ b: ByteArray64 . scalar_as_canonical(reduce(b)) == u8_64_as_group_canonical(b));
axiom (∀ b: ByteArray64 . is_canonical_scalar(reduce(b)));

procedure from_bytes_mod_order_wide(bytes: ByteArray64) returns (result: Scalar)
spec {
  ensures scalar_as_canonical(result) == u8_64_as_group_canonical(bytes);
  ensures is_canonical_scalar(result);
}
{
  result := reduce(bytes);
};
#end

/-- info:
Obligation: from_bytes_mod_order_wide_ensures_2_1528
Property: assert
Result: ✅ pass

Obligation: from_bytes_mod_order_wide_ensures_3_1602
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" scalarReduceSeed (options := .quiet)

example : Strata.smtVCsCorrect scalarReduceSeed := by
  gen_smt_vcs
  all_goals (try grind)
