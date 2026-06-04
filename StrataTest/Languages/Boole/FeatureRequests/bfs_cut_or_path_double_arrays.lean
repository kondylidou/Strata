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

set_option maxRecDepth 20000

private def bfsCutOrPath : Strata.Program :=
#strata
program Boole;

// Graph G = (V, E): vertices 0..n-1, adjacency via uninterpreted function.
function Adj(u: int, v: int) : bool;

type IntMap := Map int int;
type BoolMap := Map int bool;

type Walk := Sequence int;
type WalkMap := Map int IntMap;


// p3: BFS_s(t)
//
// found = true  → p2: visited[t] witnesses that t is reachable from s
// found = false → p1: visited is the cut set S with s ∈ S and t ∉ S
procedure BFS(n: int, s: int, t: int)
  returns (visited: BoolMap, path: IntMap, path_length: int)
spec {
  requires n > 0;
  requires 0 <= s && s < n;
  requires 0 <= t && t < n;
  requires s != t;

  ensures visited[s]; // s is always in S
  ensures !(visited[t]) ==> (∀ i:int . ∀ j:int . 0 <= i && i < n && 0 <= j && j < n && visited[i] && !(visited[j]) ==> !(Adj(i,j)));
  ensures visited[t] ==> 2 <= path_length && (∀ i:int . 0 <= i && i < path_length -1 ==> Adj(path[i],path[i+1]));
}
{
  var queue : IntMap;
  var pos   : IntMap;
//  var parent: IntMap;
  var head : int;
  var tail : int;
  var done : BoolMap;
  var i : int;
  var u : int;
  var v : int;

  var paths: WalkMap; // Maps a node 'k' to its specific path sequence (IntMap)
  var lengths: IntMap;    // Maps a node 'k' to the length of its sequence

  // Initialize visited to false so that !visited[t] holds at BFS entry.
  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant ∀ k: int :: 0 <= k && k < i ==> !(visited[k])
    invariant ∀ k: int :: 0 <= k && k < i ==> !(done[k])
  {
    visited[i] := false;
    done[i] := false;
    lengths[i] := 0;

    i := i + 1;
  }

  head := 0;
  pos[s] := 0;
  queue[0] := s;
  tail := 1;
  visited[s] := true;

  lengths[s] := 1;
  paths[s][0] := s;
  // Ground the 2D map initialization for the solver's base-case frame
  assert paths[s][0] == s;



  assert lengths[s] - 1 == 0; // Trivial arithmetic
  assert paths[s][lengths[s]-1] == s;

  // 1. Domain Restrictor: Mathematically prove 's' is the strictly singular visited node
  assert (∀ k: int :: 0 <= k && k < n && k != s ==> !(visited[k]));

  // 2. Base Case Grounding: Bind the map properties specifically to 's'
  assert lengths[s] == 1;
  assert paths[s][lengths[s]-1] == s;

  // 3. Pre-Loop Synthesis: Force the full quantified invariant evaluation prior to loop entry
  assert (∀ k: int :: 0 <= k && k < n && visited[k] ==> paths[k][lengths[k]-1] == k);

  while (head < tail && !(visited[t]))
    invariant 0 <= head && head <= tail
    invariant visited[s]
    invariant ∀ i: int :: head <= i && i < tail ==> (0 <= queue[i] && queue[i] < n)
    invariant ∀ i: int :: head <= i && i < tail ==> visited[queue[i]]
    invariant ∀ k: int :: 0 <= k && k < n ==> done[k] ==> visited[k]
    invariant ∀ k: int :: 0 <= k && k < n ==> visited[k] ==> done[k] || k == t || (head <= pos[k] && pos[k] < tail && queue[pos[k]] == k)
    invariant !(visited[t]) ==> (∀ i:int, j:int :: 0 <= i && i < n && 0 <= j && j < n ==> (done[i] && Adj(i,j) ==> visited[j]))
// 6
    invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> (k == s ==> lengths[k] == 1)
    invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> (k != s ==> lengths[k] >= 2)
    invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> paths[k][0] == s
    invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> paths[k][lengths[k]-1] == k
    invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==>
      (∀ idx: int :: 0 <= idx && idx < lengths[k]-1 ==> Adj(paths[k][idx], paths[k][idx+1]))


  {
    u := queue[head];
    head := head + 1;

    // Force outer loop invariant carry-over before context switch
    assert (∀ k: int :: 0 <= k && k < n && visited[k] ==> paths[k][lengths[k]-1] == k);


    v := 0;
    while (v < n && !(visited[t]))
      invariant 0 <= v && v <= n // 0
      invariant 0 <= head && head <= tail
      invariant visited[s]

      invariant 0 <= u && u < n // 3
      invariant visited[u]

      invariant ∀ x: int :: head <= x && x < tail ==> 0 <= queue[x] && queue[x] < n // 5
      invariant ∀ x: int :: head <= x && x < tail ==> visited[queue[x]]

      invariant ∀ k: int :: 0 <= k && k < n ==> visited[k] ==> (done[k] || k == u || k == t || (head <= pos[k] && pos[k] < tail && queue[pos[k]] == k))
      invariant !(visited[t]) ==> (∀ i:int, j:int :: 0 <= i && i < n && 0 <= j && j < n ==> (done[i] && Adj(i,j) ==> visited[j]))
      invariant !(visited[t]) ==> (∀ j: int :: 0 <= j && j < v ==> (Adj(u,j) ==> visited[j]))
      invariant ∀ k: int :: 0 <= k && k < n ==> (done[k]) ==> visited[k]

      invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> (k == s ==> lengths[k] == 1)
      invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> (k != s ==> lengths[k] >= 2)
      invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> paths[k][0] == s
      invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==> paths[k][lengths[k]-1] == k
      invariant ∀ k: int :: 0 <= k && k < n && visited[k] ==>
      (∀ idx: int :: 0 <= idx && idx < lengths[k]-1 ==> Adj(paths[k][idx], paths[k][idx+1]))

    {
      if (Adj(u, v) && !(visited[v])) {
        // 1. UPDATE GHOST STATE FIRST
        // Crucial: Do NOT set visited[v] := true yet!
        paths[v] := paths[u];
        paths[v][lengths[u]] := v;
        lengths[v] := lengths[u] + 1;

        // 2. PROVE PROPERTIES FOR THE NEW NODE
        assert paths[v][lengths[v]-1] == v;
        assert paths[v][0] == s;

        // 3. PUSH THE FRAME FOR ALL OLD NODES
        // Because visited[v] is STILL FALSE here, this assertion only checks the
        // previously visited nodes. It forces the solver to mathematically recognize
        // that updating paths[v] didn't destroy paths[x] for any old node 'x'.
        assert (∀ x: int :: 0 <= x && x < n && visited[x] ==> paths[x][lengths[x]-1] == x);
        assert (∀ x: int :: 0 <= x && x < n && visited[x] ==> paths[x][0] == s);

        // 4. NOW PUBLISH THE NODE
        // By flipping this boolean now, 'v' enters the loop invariant's domain
        // perfectly formed, and the solver trivially unions step 2 and step 3.
        visited[v] := true;

        // 5. EXISTING ADJACENCY SYNTHESIS (Unchanged)
        assert (∀ idx: int :: 0 <= idx && idx < lengths[u]-1 ==> Adj(paths[v][idx], paths[v][idx+1]));

        assert paths[v][lengths[v]-2] == u;
        assert paths[v][lengths[v]-1] == v;
        assert Adj(paths[v][lengths[v]-2], paths[v][lengths[v]-1]);

        // 1. Point-wise Map Equivalence: Ground the prefix elements
        assert (∀ idx: int :: 0 <= idx && idx < lengths[u] ==> paths[v][idx] == paths[u][idx]);

        // 2. Transitive Adjacency Pull: Verify the old path explicitly
        assert (∀ idx: int :: 0 <= idx && idx < lengths[u]-1 ==> Adj(paths[u][idx], paths[u][idx+1]));

        // 3. Unified Synthesis: Merge evaluated frames
        assert (∀ idx: int :: 0 <= idx && idx < lengths[v]-1 ==> Adj(paths[v][idx], paths[v][idx+1]));

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

   if (visited[t]) {
    path := paths[t];
    path_length := lengths[t];
  } else {
    path_length := 0; // Ensures initialized return on all paths
  }

};

#end

-- #eval Strata.Boole.verify "cvc5" bfsCutOrPath (options := { Core.VerifyOptions.quiet with mbqiEnum := true, solverTimeout := 10 })

-- #eval Strata.Boole.verify "cvc5" bfsCutOrPath (options := { Core.VerifyOptions.quiet with mbqiEnum := true })

#eval Strata.Boole.verify "cvc5" bfsCutOrPath
  (options := { Core.VerifyOptions.quiet with
    mbqiEnum := true,
    mbqiEnumChoiceGrammar := false,
    solverTimeout := 60 })

set_option maxHeartbeats 800000 in
example : Strata.smtVCsCorrect bfsCutOrPath := by
  gen_smt_vcs
  all_goals (try grind)


end Strata
