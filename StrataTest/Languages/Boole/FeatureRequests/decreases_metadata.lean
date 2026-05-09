/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors:
- `verus-examples:proposal-rw2022`, `rw2022_script`, `recursion`
- `vlir-tests:LoopSimpleWithSpec`

Loop-level `decreases` and function/procedure-level `decreases` annotations
all parse. Function- and procedure-level ones are silently dropped by the
Boole lowering; termination is not separately verified in the SMT path.

Remaining gap: recursive functions over `int` need int-based termination
proofs — structural recursion on `@[cases]` is the only supported form now.
-/

private def decreasesMetadataSeed : Strata.Program :=
#strata
program Boole;

procedure loop_measure_seed(n: int) returns (i: int)
spec {
  requires 0 <= n;
  ensures i == n;
}
{
  i := 0;
  while (i < n)
    decreases n - i
    invariant 0 <= i
    invariant i <= n
  {
    i := i + 1;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: loop_measure_seed_ensures_1_1174
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesMetadataSeed (options:=.quiet)

example : Strata.smtVCsCorrect decreasesMetadataSeed := by
  gen_smt_vcs
  all_goals (try grind)

-- Function- and procedure-level `decreases` are parsed and dropped.
-- `clamp` is non-recursive here; a recursive `int` function would need
-- int-based termination support (open gap).
private def decreasesFunctionSeed : Strata.Program :=
#strata
program Boole;

function clamp(n: int) : int
  decreases n;
{
  if n < 0 then 0 else n
}

procedure decreases_proc_seed(n: int) returns (r: int)
spec {
  decreases n;
  requires 0 <= n;
  ensures r == n;
}
{
  r := clamp(n);
};
#end

/-- info:
Obligation: decreases_proc_seed_ensures_1_1944
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesFunctionSeed (options := .quiet)

example : Strata.smtVCsCorrect decreasesFunctionSeed := by
  gen_smt_vcs
  all_goals (try grind)

-- `decreases` clause in a `for v := init to limit` loop.
private def decreasesForLoopSeed : Strata.Program :=
#strata
program Boole;

procedure for_decreases_seed(n: int) returns (s: int)
spec {
  requires 0 <= n;
  ensures s == n;
}
{
  s := 0;
  for i : int := 0 to n - 1
  decreases n - i
  invariant 0 <= i && i <= n
  invariant s == i
  {
    s := s + 1;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: for_decreases_seed_ensures_1_2489
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesForLoopSeed (options := .quiet)
