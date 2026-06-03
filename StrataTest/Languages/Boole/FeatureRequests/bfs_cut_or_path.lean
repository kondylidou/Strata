import Strata.MetaVerifier

namespace Strata

/-
  BFS-based Max-Flow / Min-Cut witness

  G = (V, E), vertices 0..n-1, edges given by uninterpreted function hasEdge.

  p1 : IsACut(S) — S ⊆ V, s ∈ S, t ∉ S, no edge crosses S → V\S
  p2 : IsPathValid(P) — P is a valid s→t path encoded via parent pointers
  p3 : BFS_s(t) = { P (found=true) | S (found=false) }

  If BFS_s(t) returns P → p2 accepts P  (found=true,  visited[t])
  Else BFS_s(t) returns S → p1 accepts S  (found=false, s ∈ S, t ∉ S)
-/

private def bfsCutOrPath : Strata.Program :=
#strata
program Boole;

// Graph G = (V, E): vertices 0..n-1, adjacency via uninterpreted function.
function AdjMatrix(u: int, v: int) : bool;

type IntMap := Map int int;
type BoolMap := Map int bool;
type Walk := Sequence int;

// p3: BFS_s(t)
//
// found = true  → p2: visited[t] witnesses that t is reachable from s
// found = false → p1: visited is the cut set S with s ∈ S and t ∉ S
procedure BFS(n: int, s: int, t: int)
  returns (visited: BoolMap, path: Walk)
spec {
  requires n > 0;
  requires 0 <= s && s < n;
  requires 0 <= t && t < n;
  requires s != t;

  ensures visited[s]; // s is always in S
  ensures !(visited[t]) ==> IsACut(AdjMatrix, visited);
  ensures visited[t] ==> IsPathValid(AdjMatrix,path);
}
{
  var queue : IntMap;
  var head : int;
  var tail : int;
  var i : int;
  var u : int;
  var v : int;

  // Initialize visited to false so that !visited[t] holds at BFS entry.
  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant ∀ k: int :: 0 <= k && k < i ==> !(visited[k])
  {
    visited[i] := false;
    i := i + 1;
  }

  head := 0;
  tail := 0;
  found := false;

  queue[0] := s;
  tail := 1;
  visited[s] := true;

  while (head < tail && !found)
    invariant 0 <= head && head <= tail
    invariant visited[s]
    invariant found ==> visited[t]
    invariant !found ==> !(visited[t])
  {
    u := queue[head];
    head := head + 1;

    v := 0;
    while (v < n && !found)
      invariant 0 <= v && v <= n
      invariant head <= tail
      invariant visited[s]
      invariant found ==> visited[t]
      invariant !found ==> !(visited[t])
    {
      if (AdjMatrix(u, v) && !(visited[v])) {
        visited[v] := true;
        parent[v]  := u;
        if (v == t) {
          found := true;
        } else {
          queue[tail] := v;
          tail := tail + 1;
        }
      }
      v := v + 1;
    }
  }
};

#end

#eval Strata.Boole.verify "cvc5" bfsCutOrPath (options := .quiet)

set_option maxHeartbeats 800000 in
example : Strata.smtVCsCorrect bfsCutOrPath := by
  gen_smt_vcs
  all_goals (try grind)

end Strata
