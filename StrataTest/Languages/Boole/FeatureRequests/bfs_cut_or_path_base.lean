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
function Adj(u: int, v: int) : bool;

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
  ensures !(visited[t]) ==> (∀ i:int . ∀ j:int . 0 <= i && i < n && 0 <= j && j < n && visited[i] && !(visited[j]) ==> !(Adj(i,j)));
//  ensures visited[t] ==> 2 <= Sequence.length(path) && (∀ i:int . 0 <= i && i < Sequence.length(path)-1 && Adj(Sequence.select(path,i),Sequence.select(path,i+1)));
}
{
  var queue : IntMap;
  var pos   : IntMap; // New: tracks the index of each node in the queue
  var head : int;
  var tail : int;
  var done : BoolMap;
  var i : int;
  var u : int;
  var v : int;

  // Initialize visited to false so that !visited[t] holds at BFS entry.
  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant ∀ k: int :: 0 <= k && k < i ==> !(visited[k])
    invariant ∀ k: int :: 0 <= k && k < i ==> !(done[k])
  {
    visited[i] := false;
    done[i] := false;
    i := i + 1;
  }

  head := 0;
  pos[s] := 0;     // Record that 's' is at index 0
  queue[0] := s;
  tail := 1;
  visited[s] := true;

  assert queue[0] == s && head == 0 && tail == 1 && visited[s];
  assert ((head <= 0 && 0 < tail && queue[0] == s));
  assert ∀ k: int :: 0 <= k && k < n ==> visited[k] ==> done[k] || k == t || (head <= pos[k] && pos[k] < tail && queue[pos[k]] == k);

  while (head < tail && !(visited[t]))
    invariant 0 <= head && head <= tail
    invariant visited[s]
    invariant ∀ i: int :: head <= i && i < tail ==> (0 <= queue[i] && queue[i] < n)
    invariant ∀ i: int :: head <= i && i < tail ==> visited[queue[i]]
    invariant ∀ k: int :: 0 <= k && k < n ==> done[k] ==> visited[k]
    invariant ∀ k: int :: 0 <= k && k < n ==> visited[k] ==> done[k] || k == t || (head <= pos[k] && pos[k] < tail && queue[pos[k]] == k)
    invariant !(visited[t]) ==> (∀ i:int, j:int :: 0 <= i && i < n && 0 <= j && j < n ==> (done[i] && Adj(i,j) ==> visited[j]))
  {
    u := queue[head];
    head := head + 1;


    v := 0;
    while (v < n && !(visited[t]))
      invariant 0 <= v && v <= n
      invariant 0 <= head && head <= tail
      invariant visited[s]

      // The currently processing node 'u' is valid and visited
      invariant 0 <= u && u < n
      invariant visited[u]

      invariant ∀ x: int :: head <= x && x < tail ==> 0 <= queue[x] && queue[x] < n
      invariant ∀ x: int :: head <= x && x < tail ==> visited[queue[x]]

      invariant ∀ k: int :: 0 <= k && k < n ==> visited[k] ==> (done[k] || k == u || k == t || (head <= pos[k] && pos[k] < tail && queue[pos[k]] == k))
      invariant !(visited[t]) ==> (∀ i:int, j:int :: 0 <= i && i < n && 0 <= j && j < n ==> (done[i] && Adj(i,j) ==> visited[j]))
      invariant !(visited[t]) ==> (∀ j: int :: 0 <= j && j < v ==> (Adj(u,j) ==> visited[j]))
      invariant ∀ k: int :: 0 <= k && k < n ==> (done[k]) ==> visited[k]

    {
      if (Adj(u, v) && !(visited[v])) {
        visited[v] := true;
        if (v == t) {

        } else {
          queue[tail] := v;
          pos[v] := tail; // Record that 'v' is at index 'tail'
          tail := tail + 1;
        }
      }
      v := v + 1;
    }
    done[u] := true;
  }
};

#end

-- #eval Strata.Boole.verify "cvc5" bfsCutOrPath
--   (options := { Core.VerifyOptions.quiet with mbqiEnum := true, solverTimeout := 10 })

--#eval Strata.Boole.verify "cvc5" bfsCutOrPath (options := { Core.VerifyOptions.quiet with mbqiEnum := true })

#eval Strata.Boole.verify "cvc5" bfsCutOrPath (options := .quiet)

set_option maxHeartbeats 800000 in
example : Strata.smtVCsCorrect bfsCutOrPath := by
  gen_smt_vcs
  all_goals (try grind)


end Strata
