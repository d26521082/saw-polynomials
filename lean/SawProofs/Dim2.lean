import Mathlib

/-!
# Eventual polynomiality of fixed-length SAW counts in 2D boxes

Formalization of the 2D case of the meta-theorem in `docs/proof.md`:
for `m = k - 1` and `n ≥ 2m + 1`, the number `A m n` of walks of `m` edges
in the `n × n` grid, summed over all starting cells (Hardin's OEIS
convention: "k-step walk" = k distinct cells = m edges, directions counted
separately), equals `(n-2m)^2 * W2 m + (n-2m) * W1 m + W0 m` where the `W`s
are finite window sums.  Together with `native_decide` evaluations of the
`W`s and of the finitely many sub-threshold values, this yields end-to-end
machine-checked proofs of OEIS A188148–A188155.

Proof chain:
  `countFrom_congr` (locality) → `countFrom_shift` (translation invariance)
  → `count_eq_wcount` (window reduction) → `census` (single-axis census)
  → `A_eq_poly` (2D polynomial form) → `A1881xx` (the eight entries).
-/

namespace SawProofs
namespace D2

abbrev Cell := Int × Int

/-- Axis-aligned box with inclusive bounds. -/
structure Box where
  x1 : Int
  x2 : Int
  y1 : Int
  y2 : Int

def inB (B : Box) (p : Cell) : Prop :=
  B.x1 ≤ p.1 ∧ p.1 ≤ B.x2 ∧ B.y1 ≤ p.2 ∧ p.2 ≤ B.y2

instance (B : Box) (p : Cell) : Decidable (inB B p) := by
  unfold inB; infer_instance

/-- Lattice neighbors. -/
def nbrs (p : Cell) : List Cell :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- Number of walks of `m` further edges from `pos` (already recorded in
`vis`), self-avoiding, staying inside `B`. -/
def countFrom (B : Box) : Nat → List Cell → Cell → Nat
  | 0, _, _ => 1
  | m + 1, vis, pos =>
    (nbrs pos).foldl
      (fun acc q =>
        if inB B q ∧ q ∉ vis then acc + countFrom B m (q :: vis) q else acc)
      0

/-- `L∞`-proximity: every coordinate differs by at most `m`. -/
def near (m : Nat) (p q : Cell) : Prop :=
  (p.1 - q.1).natAbs ≤ m ∧ (p.2 - q.2).natAbs ≤ m

theorem near_mono {m m' : Nat} (h : m ≤ m') {p q : Cell} (hn : near m p q) :
    near m' p q := by
  unfold near at *; omega

theorem near_step {m : Nat} {p q r : Cell} (h1 : near 1 p q)
    (h2 : near m q r) : near (m + 1) p r := by
  unfold near at *; omega

theorem near_nbrs {p q : Cell} (h : q ∈ nbrs p) : near 1 p q := by
  simp only [nbrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> subst h <;> unfold near <;> simp <;> omega

/-! ## Locality -/

/-- If two boxes agree on the `L∞`-ball of radius `m` around `pos`, walks of
`m` edges from `pos` cannot tell them apart. -/
theorem countFrom_congr (B B' : Box) :
    ∀ (m : Nat) (vis : List Cell) (pos : Cell),
      (∀ q, near m pos q → (inB B q ↔ inB B' q)) →
      countFrom B m vis pos = countFrom B' m vis pos := by
  intro m
  induction m with
  | zero => intro vis pos _; rfl
  | succ m ih =>
    intro vis pos h
    have step : ∀ (acc : Nat) (q : Cell), q ∈ nbrs pos →
        (if inB B q ∧ q ∉ vis then acc + countFrom B m (q :: vis) q else acc)
          = (if inB B' q ∧ q ∉ vis then acc + countFrom B' m (q :: vis) q
             else acc) := by
      intro acc q hq
      have h1 : near 1 pos q := near_nbrs hq
      have hiff : inB B q ↔ inB B' q := h q (near_mono (by omega) h1)
      have hrec : countFrom B m (q :: vis) q = countFrom B' m (q :: vis) q :=
        ih (q :: vis) q (fun r hr => h r (near_step h1 hr))
      exact if_congr (and_congr_left' hiff) (by rw [hrec]) rfl
    have main : ∀ (l : List Cell), (∀ q ∈ l, q ∈ nbrs pos) → ∀ acc : Nat,
        l.foldl (fun acc q =>
          if inB B q ∧ q ∉ vis then acc + countFrom B m (q :: vis) q
          else acc) acc
        = l.foldl (fun acc q =>
          if inB B' q ∧ q ∉ vis then acc + countFrom B' m (q :: vis) q
          else acc) acc := by
      intro l
      induction l with
      | nil => intro _ acc; rfl
      | cons a t iht =>
        intro hl acc
        simp only [List.foldl_cons]
        rw [step acc a (hl a (by simp))]
        exact iht (fun q hq => hl q (by simp [hq])) _
    simp only [countFrom]
    exact main (nbrs pos) (fun q hq => hq) 0

/-! ## Translation invariance -/

def shift (v : Cell) (p : Cell) : Cell := (p.1 + v.1, p.2 + v.2)

def shiftBox (v : Cell) (B : Box) : Box :=
  ⟨B.x1 + v.1, B.x2 + v.1, B.y1 + v.2, B.y2 + v.2⟩

theorem shift_injective (v : Cell) : Function.Injective (shift v) := by
  intro a b hab
  unfold shift at hab
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  simp at h1 h2
  exact Prod.ext h1 h2

theorem nbrs_shift (v p : Cell) :
    nbrs (shift v p) = (nbrs p).map (shift v) := by
  simp only [nbrs, shift, List.map_cons, List.map_nil, List.cons.injEq,
    Prod.mk.injEq, and_true, true_and]
  omega

theorem inB_shift (v : Cell) (B : Box) (q : Cell) :
    inB (shiftBox v B) (shift v q) ↔ inB B q := by
  obtain ⟨qx, qy⟩ := q
  obtain ⟨a, b, c, d⟩ := B
  unfold inB shiftBox shift
  dsimp only
  omega

theorem countFrom_shift (v : Cell) (B : Box) :
    ∀ (m : Nat) (vis : List Cell) (pos : Cell),
      countFrom (shiftBox v B) m (vis.map (shift v)) (shift v pos)
        = countFrom B m vis pos := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro vis pos
    simp only [countFrom, nbrs_shift, List.foldl_map]
    congr 1
    funext acc q
    have hcond : (inB (shiftBox v B) (shift v q) ∧
        shift v q ∉ vis.map (shift v)) ↔ (inB B q ∧ q ∉ vis) := by
      rw [inB_shift]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hm => h2 (List.mem_map.mpr ⟨q, hm, rfl⟩)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hm => ?_⟩
        obtain ⟨r, hr, hre⟩ := List.mem_map.mp hm
        exact h2 (shift_injective v hre ▸ hr)
    refine if_congr hcond ?_ rfl
    have : (shift v q :: vis.map (shift v)) = (q :: vis).map (shift v) := rfl
    rw [this, ih]

/-! ## Window reduction -/

/-- The `n × n` grid `{0, …, n-1}²` as a box. -/
def boxN (n : Nat) : Box := ⟨0, (n : Int) - 1, 0, (n : Int) - 1⟩

/-- Clipped pair of a coordinate: distances to the two faces, capped at `m`. -/
def clip (m n x : Nat) : Nat × Nat := (min x m, min (n - 1 - x) m)

/-- The standard window box for a clipped profile, with the start cell at
the origin. -/
def profBox (px py : Nat × Nat) : Box :=
  ⟨-(px.1 : Int), (px.2 : Int), -(py.1 : Int), (py.2 : Int)⟩

/-- Walk count from the canonical cell of a window. -/
def wcount (m : Nat) (px py : Nat × Nat) : Nat :=
  countFrom (profBox px py) m [((0 : Int), (0 : Int))] (0, 0)

theorem count_eq_wcount (m n x y : Nat) (hx : x < n) (hy : y < n) :
    countFrom (boxN n) m [((x : Int), (y : Int))] ((x : Int), (y : Int))
      = wcount m (clip m n x) (clip m n y) := by
  have h1 : countFrom (boxN n) m [((x : Int), (y : Int))] ((x : Int), (y : Int))
      = countFrom (shiftBox ((x : Int), (y : Int))
          (profBox (clip m n x) (clip m n y))) m
          [((x : Int), (y : Int))] ((x : Int), (y : Int)) := by
    apply countFrom_congr
    intro q hq
    obtain ⟨qx, qy⟩ := q
    unfold near at hq
    unfold inB boxN shiftBox profBox clip
    dsimp only at hq ⊢
    push_cast [Nat.cast_min] at hq ⊢
    omega
  have h2 : countFrom (shiftBox ((x : Int), (y : Int))
        (profBox (clip m n x) (clip m n y))) m
        [((x : Int), (y : Int))] ((x : Int), (y : Int))
      = wcount m (clip m n x) (clip m n y) := by
    have := countFrom_shift ((x : Int), (y : Int))
      (profBox (clip m n x) (clip m n y)) m [((0 : Int), (0 : Int))] (0, 0)
    have e1 : shift ((x : Int), (y : Int)) ((0 : Int), (0 : Int))
        = ((x : Int), (y : Int)) := by unfold shift; simp
    have e2 : ([((0 : Int), (0 : Int))].map (shift ((x : Int), (y : Int))))
        = [((x : Int), (y : Int))] := by simp [shift]
    rw [e1, e2] at this
    rw [this]
    rfl
  rw [h1, h2]

/-! ## The total count -/

/-- Total number of walks of `m` edges in the `n × n` grid, summed over all
starting cells.  This is the OEIS count for `(m+1)`-step walks. -/
def A (m n : Nat) : Nat :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    countFrom (boxN n) m [((x : Int), (y : Int))] ((x : Int), (y : Int))

/-! ## Single-axis census -/

theorem census_base (g : Nat × Nat → Nat) (m : Nat) :
    ∑ x ∈ Finset.range (2 * m + 1), g (clip m (2 * m + 1) x)
      = g (m, m) + ∑ i ∈ Finset.range m, (g (i, m) + g (m, i)) := by
  rw [Finset.sum_add_distrib]
  have hsplit : ∑ x ∈ Finset.range (2 * m + 1), g (clip m (2 * m + 1) x)
      = (∑ x ∈ Finset.Ico 0 (m + 1), g (clip m (2 * m + 1) x))
        + ∑ x ∈ Finset.Ico (m + 1) (2 * m + 1), g (clip m (2 * m + 1) x) := by
    rw [Finset.sum_Ico_consecutive _ (by omega) (by omega),
      Finset.range_eq_Ico]
  have e1 : ∑ x ∈ Finset.Ico 0 (m + 1), g (clip m (2 * m + 1) x)
      = (∑ i ∈ Finset.range m, g (i, m)) + g (m, m) := by
    have : Finset.Ico 0 (m + 1) = Finset.range (m + 1) := by
      rw [Finset.range_eq_Ico]
    rw [this, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      have hx' : x < m := Finset.mem_range.mp hx
      have : clip m (2 * m + 1) x = (x, m) := by
        unfold clip
        have h1 : min x m = x := by omega
        have h2 : min (2 * m + 1 - 1 - x) m = m := by omega
        rw [h1, h2]
      rw [this]
    · have : clip m (2 * m + 1) m = (m, m) := by
        unfold clip
        have h1 : min m m = m := by omega
        have h2 : min (2 * m + 1 - 1 - m) m = m := by omega
        rw [h1, h2]
      rw [this]
  have e2 : ∑ x ∈ Finset.Ico (m + 1) (2 * m + 1), g (clip m (2 * m + 1) x)
      = ∑ i ∈ Finset.range m, g (m, i) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : 2 * m + 1 - (m + 1) = m := by omega
    rw [hlen]
    have hcong : ∀ i ∈ Finset.range m,
        g (clip m (2 * m + 1) (m + 1 + i)) = g (m, m - 1 - i) := by
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have : clip m (2 * m + 1) (m + 1 + i) = (m, m - 1 - i) := by
        unfold clip
        have h1 : min (m + 1 + i) m = m := by omega
        have h2 : min (2 * m + 1 - 1 - (m + 1 + i)) m = m - 1 - i := by omega
        rw [h1, h2]
      rw [this]
    rw [Finset.sum_congr rfl hcong]
    exact Finset.sum_range_reflect (fun i => g (m, i)) m
  omega

theorem census_step (g : Nat × Nat → Nat) (m n : Nat) (h : 2 * m + 1 ≤ n) :
    ∑ x ∈ Finset.range (n + 1), g (clip m (n + 1) x)
      = (∑ x ∈ Finset.range n, g (clip m n x)) + g (m, m) := by
  have hL : ∑ x ∈ Finset.range (n + 1), g (clip m (n + 1) x)
      = (∑ x ∈ Finset.Ico 0 (m + 1), g (clip m (n + 1) x))
        + ∑ x ∈ Finset.Ico (m + 1) (n + 1), g (clip m (n + 1) x) := by
    rw [Finset.sum_Ico_consecutive _ (by omega) (by omega),
      Finset.range_eq_Ico]
  have hR : ∑ x ∈ Finset.range n, g (clip m n x)
      = (∑ x ∈ Finset.Ico 0 m, g (clip m n x))
        + ∑ x ∈ Finset.Ico m n, g (clip m n x) := by
    rw [Finset.sum_Ico_consecutive _ (by omega) (by omega),
      Finset.range_eq_Ico]
  have e1 : ∑ x ∈ Finset.Ico 0 (m + 1), g (clip m (n + 1) x)
      = (∑ x ∈ Finset.Ico 0 m, g (clip m n x)) + g (m, m) := by
    rw [Finset.sum_Ico_succ_top (by omega)]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      have hx' : x < m := by
        have := Finset.mem_Ico.mp hx; omega
      have c1 : clip m (n + 1) x = (x, m) := by
        unfold clip
        have h1 : min x m = x := by omega
        have h2 : min (n + 1 - 1 - x) m = m := by omega
        rw [h1, h2]
      have c2 : clip m n x = (x, m) := by
        unfold clip
        have h1 : min x m = x := by omega
        have h2 : min (n - 1 - x) m = m := by omega
        rw [h1, h2]
      rw [c1, c2]
    · have : clip m (n + 1) m = (m, m) := by
        unfold clip
        have h1 : min m m = m := by omega
        have h2 : min (n + 1 - 1 - m) m = m := by omega
        rw [h1, h2]
      rw [this]
  have e2 : ∑ x ∈ Finset.Ico (m + 1) (n + 1), g (clip m (n + 1) x)
      = ∑ x ∈ Finset.Ico m n, g (clip m n x) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hlen : n + 1 - (m + 1) = n - m := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n - m := Finset.mem_range.mp hi
    have c1 : clip m (n + 1) (m + 1 + i) = (m, min (n - m - 1 - i) m) := by
      unfold clip
      have h1 : min (m + 1 + i) m = m := by omega
      have h2 : n + 1 - 1 - (m + 1 + i) = n - m - 1 - i := by omega
      rw [h1, h2]
    have c2 : clip m n (m + i) = (m, min (n - m - 1 - i) m) := by
      unfold clip
      have h1 : min (m + i) m = m := by omega
      have h2 : n - 1 - (m + i) = n - m - 1 - i := by omega
      rw [h1, h2]
    rw [c1, c2]
  omega

/-- Single-axis census: for `n ≥ 2m+1` the multiset of clipped pairs
consists of each boundary pair once and the interior pair `n - 2m` times. -/
theorem census (g : Nat × Nat → Nat) (m : Nat) :
    ∀ n, 2 * m + 1 ≤ n →
      ∑ x ∈ Finset.range n, g (clip m n x)
        = (n - 2 * m) * g (m, m)
          + ∑ i ∈ Finset.range m, (g (i, m) + g (m, i)) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge n (2 * m + 1) with hlt | hge
    · -- n + 1 = 2m + 1 exactly
      have hn : n = 2 * m := by omega
      subst hn
      have h1 : 2 * m + 1 - 2 * m = 1 := by omega
      calc ∑ x ∈ Finset.range (2 * m + 1), g (clip m (2 * m + 1) x)
          = g (m, m) + ∑ i ∈ Finset.range m, (g (i, m) + g (m, i)) :=
            census_base g m
        _ = (2 * m + 1 - 2 * m) * g (m, m)
              + ∑ i ∈ Finset.range m, (g (i, m) + g (m, i)) := by
            rw [h1, one_mul]
    · have hstep := census_step g m n hge
      have hin := ih hge
      rw [hstep, hin]
      have h2 : n + 1 - 2 * m = (n - 2 * m) + 1 := by omega
      rw [h2, Nat.succ_mul]
      ring

/-! ## The 2D polynomial theorem -/

/-- Boundary correction along the second axis. -/
def Kc (m : Nat) (p : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range m, (wcount m p (i, m) + wcount m p (m, i))

def W2 (m : Nat) : Nat := wcount m (m, m) (m, m)

def W1 (m : Nat) : Nat :=
  (∑ i ∈ Finset.range m, (wcount m (i, m) (m, m) + wcount m (m, i) (m, m)))
    + Kc m (m, m)

def W0 (m : Nat) : Nat :=
  ∑ i ∈ Finset.range m, (Kc m (i, m) + Kc m (m, i))

/-- Main theorem (2D): for `n ≥ 2m+1` the total walk count is the explicit
quadratic in `n - 2m` with window-sum coefficients. -/
theorem A_eq_poly (m n : Nat) (h : 2 * m + 1 ≤ n) :
    A m n = (n - 2 * m) ^ 2 * W2 m + (n - 2 * m) * W1 m + W0 m := by
  have hA : A m n = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
      wcount m (clip m n x) (clip m n y) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    exact count_eq_wcount m n x y (Finset.mem_range.mp hx)
      (Finset.mem_range.mp hy)
  have inner : ∀ x : Nat,
      ∑ y ∈ Finset.range n, wcount m (clip m n x) (clip m n y)
        = (n - 2 * m) * wcount m (clip m n x) (m, m) + Kc m (clip m n x) := by
    intro x
    exact census (fun p => wcount m (clip m n x) p) m n h
  have houter : A m n = ∑ x ∈ Finset.range n,
      ((n - 2 * m) * wcount m (clip m n x) (m, m) + Kc m (clip m n x)) := by
    rw [hA]
    exact Finset.sum_congr rfl fun x _ => inner x
  rw [houter, Finset.sum_add_distrib, ← Finset.mul_sum]
  have c1 := census (fun p => wcount m p (m, m)) m n h
  have c2 := census (fun p => Kc m p) m n h
  rw [c1, c2]
  unfold W2 W1 W0
  ring

/-! ## The eight OEIS entries

Each proof: for `n ≥ 2m+1` use `A_eq_poly` with the window constants
computed by `native_decide`; for the finitely many `n` between the OEIS
threshold and `2m+1`, evaluate both sides by `native_decide`.
-/

/-- **OEIS A188148**: 3-step SAWs on the `n × n` grid; `a(n) = 12n² - 24n + 8`
for `n > 1`. -/
theorem A188148 (n : Nat) (h : 2 ≤ n) :
    (A 2 n : Int) = 12 * (n : Int) ^ 2 - 24 * n + 8 := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 5 := ⟨n - 5, by omega⟩
    have hp := A_eq_poly 2 (t + 5) (by omega)
    have w2 : W2 2 = 12 := by native_decide
    have w1 : W1 2 = 72 := by native_decide
    have w0 : W0 2 = 104 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 5 - 2 * 2 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188149**: 4-step SAWs; `a(n) = 36n² - 100n + 56` for `n > 2`. -/
theorem A188149 (n : Nat) (h : 3 ≤ n) :
    (A 3 n : Int) = 36 * (n : Int) ^ 2 - 100 * n + 56 := by
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 7 := ⟨n - 7, by omega⟩
    have hp := A_eq_poly 3 (t + 7) (by omega)
    have w2 : W2 3 = 36 := by native_decide
    have w1 : W1 3 = 332 := by native_decide
    have w0 : W0 3 = 752 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 7 - 2 * 3 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188150**: 5-step SAWs; `a(n) = 100n² - 360n + 272` for `n > 3`. -/
theorem A188150 (n : Nat) (h : 4 ≤ n) :
    (A 4 n : Int) = 100 * (n : Int) ^ 2 - 360 * n + 272 := by
  rcases Nat.lt_or_ge n 9 with h9 | h9
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 9 := ⟨n - 9, by omega⟩
    have hp := A_eq_poly 4 (t + 9) (by omega)
    have w2 : W2 4 = 100 := by native_decide
    have w1 : W1 4 = 1240 := by native_decide
    have w0 : W0 4 = 3792 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 9 - 2 * 4 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188151**: 6-step SAWs; `a(n) = 284n² - 1228n + 1152` for `n > 4`. -/
theorem A188151 (n : Nat) (h : 5 ≤ n) :
    (A 5 n : Int) = 284 * (n : Int) ^ 2 - 1228 * n + 1152 := by
  rcases Nat.lt_or_ge n 11 with h11 | h11
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 11 := ⟨n - 11, by omega⟩
    have hp := A_eq_poly 5 (t + 11) (by omega)
    have w2 : W2 5 = 284 := by native_decide
    have w1 : W1 5 = 4452 := by native_decide
    have w0 : W0 5 = 17272 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 11 - 2 * 5 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188152**: 7-step SAWs; `a(n) = 780n² - 3960n + 4432` for `n > 5`. -/
theorem A188152 (n : Nat) (h : 6 ≤ n) :
    (A 6 n : Int) = 780 * (n : Int) ^ 2 - 3960 * n + 4432 := by
  rcases Nat.lt_or_ge n 13 with h13 | h13
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 13 := ⟨n - 13, by omega⟩
    have hp := A_eq_poly 6 (t + 13) (by omega)
    have w2 : W2 6 = 780 := by native_decide
    have w1 : W1 6 = 14760 := by native_decide
    have w0 : W0 6 = 69232 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 13 - 2 * 6 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188153**: 8-step SAWs; `a(n) = 2172n² - 12500n + 16096` for `n > 6`. -/
theorem A188153 (n : Nat) (h : 7 ≤ n) :
    (A 7 n : Int) = 2172 * (n : Int) ^ 2 - 12500 * n + 16096 := by
  rcases Nat.lt_or_ge n 15 with h15 | h15
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 15 := ⟨n - 15, by omega⟩
    have hp := A_eq_poly 7 (t + 15) (by omega)
    have w2 : W2 7 = 2172 := by native_decide
    have w1 : W1 7 = 48316 := by native_decide
    have w0 : W0 7 = 266808 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 15 - 2 * 7 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188154**: 9-step SAWs; `a(n) = 5916n² - 38192n + 55600` for `n > 7`. -/
theorem A188154 (n : Nat) (h : 8 ≤ n) :
    (A 8 n : Int) = 5916 * (n : Int) ^ 2 - 38192 * n + 55600 := by
  rcases Nat.lt_or_ge n 17 with h17 | h17
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 17 := ⟨n - 17, by omega⟩
    have hp := A_eq_poly 8 (t + 17) (by omega)
    have w2 : W2 8 = 5916 := by native_decide
    have w1 : W1 8 = 151120 := by native_decide
    have w0 : W0 8 = 959024 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 17 - 2 * 8 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188155**: 10-step SAWs; `a(n) = 16268n² - 115548n + 186528` for
`n > 8`. -/
theorem A188155 (n : Nat) (h : 9 ≤ n) :
    (A 9 n : Int) = 16268 * (n : Int) ^ 2 - 115548 * n + 186528 := by
  rcases Nat.lt_or_ge n 19 with h19 | h19
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 19 := ⟨n - 19, by omega⟩
    have hp := A_eq_poly 9 (t + 19) (by omega)
    have w2 : W2 9 = 16268 := by native_decide
    have w1 : W1 9 = 470100 := by native_decide
    have w0 : W0 9 = 3377496 := by native_decide
    rw [hp, w2, w1, w0]
    have ht : t + 19 - 2 * 9 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-! ## Cross-check against the independent list-based definition -/

/-- `A` agrees with published OEIS values (spot checks; the two independent
Lean definitions of the count are also cross-checked in `Basic.lean`). -/
theorem A_spot_checks :
    A 2 3 = 44 ∧ A 2 10 = 968 ∧ A 3 4 = 232 ∧ A 4 5 = 972 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end D2
end SawProofs
