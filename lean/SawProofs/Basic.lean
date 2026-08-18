/-
Fixed-length self-avoiding walks in grid boxes.

Machine-checked ground truth for the OEIS families A188148–A188155 (2D),
A187164–A187170 (3D), A188785–A188789 (4D).  Convention (Hardin/OEIS):
a "k-step walk" is a sequence of k distinct pairwise-adjacent cells,
i.e. k - 1 edges, with each direction counted separately.

This file is deliberately mathlib-free: it defines the count as a computable
function and certifies concrete values against OEIS data via `native_decide`.
The eventual-polynomiality theorem (docs/proof.md) will be formalized on top
of these definitions in a later phase, with mathlib.
-/

namespace SawProofs

/-- A cell of the `d`-dimensional box, as a list of `d` coordinates. -/
abbrev Cell := List Int

/-- The lattice neighbors of `p`: one step ±1 along a single axis. -/
def neighbors : Cell → List Cell
  | [] => []
  | x :: xs =>
    ((x + 1) :: xs) :: ((x - 1) :: xs) :: (neighbors xs).map (x :: ·)

/-- Membership of a cell in the box `{0, …, n-1}^d`. -/
def inBox (n : Nat) (p : Cell) : Bool :=
  p.all fun x => 0 ≤ x && x < (n : Int)

/-- Number of walks of `m` further edges from `pos`, avoiding `visited`
    (which already contains `pos`), staying in the box of side `n`. -/
def countFrom (n : Nat) : Nat → List Cell → Cell → Nat
  | 0, _, _ => 1
  | m + 1, visited, pos =>
    (neighbors pos).foldl
      (fun acc q =>
        if inBox n q && !(visited.contains q) then
          acc + countFrom n m (q :: visited) q
        else acc)
      0

/-- All cells of the box `{0, …, n-1}^d`. -/
def allCells : Nat → Nat → List Cell
  | 0, _ => [[]]
  | d + 1, n =>
    (List.range n).flatMap fun x => (allCells d n).map (Int.ofNat x :: ·)

/-- Total number of `k`-step self-avoiding walks (k cells, k−1 edges) in the
    `d`-dimensional box of side `n`, summed over all starting cells;
    each direction counted separately.  Matches Hardin's OEIS convention. -/
def sawCount (d n k : Nat) : Nat :=
  (allCells d n).foldl (fun acc c => acc + countFrom n (k - 1) [c] c) 0

/-! ### Certified values against OEIS data

Spot checks tying the Lean definition to the published sequences.  The full
per-entry certification (every published term) is phase 2.
-/

-- A188148 (2D, 3-step): a(2) = 8, a(3) = 44, a(4) = 104
theorem A188148_a2 : sawCount 2 2 3 = 8 := by native_decide
theorem A188148_a3 : sawCount 2 3 3 = 44 := by native_decide
theorem A188148_a4 : sawCount 2 4 3 = 104 := by native_decide

-- A188148 conjectured polynomial at n = 10: 12·100 − 24·10 + 8 = 968
theorem A188148_a10 : sawCount 2 10 3 = 12 * 10 ^ 2 - 24 * 10 + 8 := by
  native_decide

-- A188150 (2D, 5-step): a(3) = 104, a(4) = 432
theorem A188150_a3 : sawCount 2 3 5 = 104 := by native_decide
theorem A188150_a4 : sawCount 2 4 5 = 432 := by native_decide

-- A187164 (3D, 3-step): a(2) = 48, a(3) = 342
theorem A187164_a2 : sawCount 3 2 3 = 48 := by native_decide
theorem A187164_a3 : sawCount 3 3 3 = 342 := by native_decide

-- A188785 (4D, 2-step): a(2) = 64, a(3) = 432
theorem A188785_a2 : sawCount 4 2 2 = 64 := by native_decide
theorem A188785_a3 : sawCount 4 3 2 = 432 := by native_decide

end SawProofs
