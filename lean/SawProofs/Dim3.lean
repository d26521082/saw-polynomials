import SawProofs.Dim2

/-!
# The 3D case: OEIS A187164–A187170

Same blueprint as `Dim2.lean` with cells in `ℤ³`; the dimension-independent
pieces (`D2.clip`, `D2.census`) are reused.  The polynomial theorem
`A3_eq_poly` is proved from Lean's standard axioms; the seven OEIS entry
theorems add `native_decide` evaluations of the window constants and the
sub-threshold values.
-/

namespace SawProofs
namespace D3

open SawProofs.D2 (clip census)

abbrev Cell3 := Int × Int × Int

structure Box3 where
  x1 : Int
  x2 : Int
  y1 : Int
  y2 : Int
  z1 : Int
  z2 : Int

def inB (B : Box3) (p : Cell3) : Prop :=
  B.x1 ≤ p.1 ∧ p.1 ≤ B.x2 ∧ B.y1 ≤ p.2.1 ∧ p.2.1 ≤ B.y2
    ∧ B.z1 ≤ p.2.2 ∧ p.2.2 ≤ B.z2

instance (B : Box3) (p : Cell3) : Decidable (inB B p) := by
  unfold inB; infer_instance

def nbrs (p : Cell3) : List Cell3 :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2),
   (p.1, p.2.1 + 1, p.2.2), (p.1, p.2.1 - 1, p.2.2),
   (p.1, p.2.1, p.2.2 + 1), (p.1, p.2.1, p.2.2 - 1)]

def countFrom (B : Box3) : Nat → List Cell3 → Cell3 → Nat
  | 0, _, _ => 1
  | m + 1, vis, pos =>
    (nbrs pos).foldl
      (fun acc q =>
        if inB B q ∧ q ∉ vis then acc + countFrom B m (q :: vis) q else acc)
      0

def near (m : Nat) (p q : Cell3) : Prop :=
  (p.1 - q.1).natAbs ≤ m ∧ (p.2.1 - q.2.1).natAbs ≤ m
    ∧ (p.2.2 - q.2.2).natAbs ≤ m

theorem near_mono {m m' : Nat} (h : m ≤ m') {p q : Cell3} (hn : near m p q) :
    near m' p q := by
  unfold near at *; omega

theorem near_step {m : Nat} {p q r : Cell3} (h1 : near 1 p q)
    (h2 : near m q r) : near (m + 1) p r := by
  unfold near at *; omega

theorem near_nbrs {p q : Cell3} (h : q ∈ nbrs p) : near 1 p q := by
  simp only [nbrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> unfold near <;>
    simp <;> omega

theorem countFrom_congr (B B' : Box3) :
    ∀ (m : Nat) (vis : List Cell3) (pos : Cell3),
      (∀ q, near m pos q → (inB B q ↔ inB B' q)) →
      countFrom B m vis pos = countFrom B' m vis pos := by
  intro m
  induction m with
  | zero => intro vis pos _; rfl
  | succ m ih =>
    intro vis pos h
    have step : ∀ (acc : Nat) (q : Cell3), q ∈ nbrs pos →
        (if inB B q ∧ q ∉ vis then acc + countFrom B m (q :: vis) q else acc)
          = (if inB B' q ∧ q ∉ vis then acc + countFrom B' m (q :: vis) q
             else acc) := by
      intro acc q hq
      have h1 : near 1 pos q := near_nbrs hq
      have hiff : inB B q ↔ inB B' q := h q (near_mono (by omega) h1)
      have hrec : countFrom B m (q :: vis) q = countFrom B' m (q :: vis) q :=
        ih (q :: vis) q (fun r hr => h r (near_step h1 hr))
      exact if_congr (and_congr_left' hiff) (by rw [hrec]) rfl
    have main : ∀ (l : List Cell3), (∀ q ∈ l, q ∈ nbrs pos) → ∀ acc : Nat,
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

def shift (v : Cell3) (p : Cell3) : Cell3 :=
  (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2)

def shiftBox (v : Cell3) (B : Box3) : Box3 :=
  ⟨B.x1 + v.1, B.x2 + v.1, B.y1 + v.2.1, B.y2 + v.2.1,
   B.z1 + v.2.2, B.z2 + v.2.2⟩

theorem shift_injective (v : Cell3) : Function.Injective (shift v) := by
  intro a b hab
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [shift, Prod.ext_iff] at hab ⊢
  omega

theorem nbrs_shift (v p : Cell3) :
    nbrs (shift v p) = (nbrs p).map (shift v) := by
  simp only [nbrs, shift, List.map_cons, List.map_nil, List.cons.injEq,
    Prod.mk.injEq, and_true, true_and]
  omega

theorem inB_shift (v : Cell3) (B : Box3) (q : Cell3) :
    inB (shiftBox v B) (shift v q) ↔ inB B q := by
  obtain ⟨qx, qy, qz⟩ := q
  obtain ⟨a, b, c, d, e, f⟩ := B
  unfold inB shiftBox shift
  dsimp only
  omega

theorem countFrom_shift (v : Cell3) (B : Box3) :
    ∀ (m : Nat) (vis : List Cell3) (pos : Cell3),
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

def boxN (n : Nat) : Box3 :=
  ⟨0, (n : Int) - 1, 0, (n : Int) - 1, 0, (n : Int) - 1⟩

def profBox (px py pz : Nat × Nat) : Box3 :=
  ⟨-(px.1 : Int), (px.2 : Int), -(py.1 : Int), (py.2 : Int),
   -(pz.1 : Int), (pz.2 : Int)⟩

def wcount (m : Nat) (px py pz : Nat × Nat) : Nat :=
  countFrom (profBox px py pz) m [((0 : Int), (0 : Int), (0 : Int))] (0, 0, 0)

theorem count_eq_wcount (m n x y z : Nat) (hx : x < n) (hy : y < n)
    (hz : z < n) :
    countFrom (boxN n) m [((x : Int), (y : Int), (z : Int))]
        ((x : Int), (y : Int), (z : Int))
      = wcount m (clip m n x) (clip m n y) (clip m n z) := by
  have h1 : countFrom (boxN n) m [((x : Int), (y : Int), (z : Int))]
        ((x : Int), (y : Int), (z : Int))
      = countFrom (shiftBox ((x : Int), (y : Int), (z : Int))
          (profBox (clip m n x) (clip m n y) (clip m n z))) m
          [((x : Int), (y : Int), (z : Int))]
          ((x : Int), (y : Int), (z : Int)) := by
    apply countFrom_congr
    intro q hq
    obtain ⟨qx, qy, qz⟩ := q
    unfold near at hq
    unfold inB boxN shiftBox profBox SawProofs.D2.clip
    dsimp only at hq ⊢
    push_cast [Nat.cast_min] at hq ⊢
    omega
  have h2 : countFrom (shiftBox ((x : Int), (y : Int), (z : Int))
        (profBox (clip m n x) (clip m n y) (clip m n z))) m
        [((x : Int), (y : Int), (z : Int))]
        ((x : Int), (y : Int), (z : Int))
      = wcount m (clip m n x) (clip m n y) (clip m n z) := by
    have := countFrom_shift ((x : Int), (y : Int), (z : Int))
      (profBox (clip m n x) (clip m n y) (clip m n z)) m
      [((0 : Int), (0 : Int), (0 : Int))] (0, 0, 0)
    have e1 : shift ((x : Int), (y : Int), (z : Int))
        ((0 : Int), (0 : Int), (0 : Int))
        = ((x : Int), (y : Int), (z : Int)) := by unfold shift; simp
    have e2 : ([((0 : Int), (0 : Int), (0 : Int))].map
          (shift ((x : Int), (y : Int), (z : Int))))
        = [((x : Int), (y : Int), (z : Int))] := by simp [shift]
    rw [e1, e2] at this
    rw [this]
    rfl
  rw [h1, h2]

/-! ## Total count and polynomial theorem -/

/-- Total number of walks of `m` edges in the `n × n × n` grid, summed over
all starting cells: the OEIS count for `(m+1)`-step walks. -/
def A3 (m n : Nat) : Nat :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
    countFrom (boxN n) m [((x : Int), (y : Int), (z : Int))]
      ((x : Int), (y : Int), (z : Int))

def Kz (m : Nat) (p q : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range m, (wcount m p q (i, m) + wcount m p q (m, i))

def Ky1 (m : Nat) (p : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range m,
    (wcount m p (i, m) (m, m) + wcount m p (m, i) (m, m))

def Ky0 (m : Nat) (p : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range m, (Kz m p (i, m) + Kz m p (m, i))

def S2 (m : Nat) (p : Nat × Nat) : Nat := wcount m p (m, m) (m, m)

def S1 (m : Nat) (p : Nat × Nat) : Nat := Ky1 m p + Kz m p (m, m)

def S0 (m : Nat) (p : Nat × Nat) : Nat := Ky0 m p

theorem sum2 (m n : Nat) (h : 2 * m + 1 ≤ n) (p : Nat × Nat) :
    ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
        wcount m p (clip m n y) (clip m n z)
      = (n - 2 * m) ^ 2 * S2 m p + (n - 2 * m) * S1 m p + S0 m p := by
  have inner : ∀ y : Nat,
      ∑ z ∈ Finset.range n, wcount m p (clip m n y) (clip m n z)
        = (n - 2 * m) * wcount m p (clip m n y) (m, m)
          + Kz m p (clip m n y) := by
    intro y
    exact census (fun q => wcount m p (clip m n y) q) m n h
  rw [Finset.sum_congr rfl fun y _ => inner y, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [census (fun q => wcount m p q (m, m)) m n h,
    census (fun q => Kz m p q) m n h]
  unfold S2 S1 S0 Ky1 Ky0
  ring

def V3c (m : Nat) : Nat := S2 m (m, m)

def V2c (m : Nat) : Nat :=
  (∑ i ∈ Finset.range m, (S2 m (i, m) + S2 m (m, i))) + S1 m (m, m)

def V1c (m : Nat) : Nat :=
  (∑ i ∈ Finset.range m, (S1 m (i, m) + S1 m (m, i))) + S0 m (m, m)

def V0c (m : Nat) : Nat :=
  ∑ i ∈ Finset.range m, (S0 m (i, m) + S0 m (m, i))

/-- Main theorem (3D): explicit cubic in `n - 2m` for `n ≥ 2m+1`. -/
theorem A3_eq_poly (m n : Nat) (h : 2 * m + 1 ≤ n) :
    A3 m n = (n - 2 * m) ^ 3 * V3c m + (n - 2 * m) ^ 2 * V2c m
      + (n - 2 * m) * V1c m + V0c m := by
  have hA : A3 m n = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
      ∑ z ∈ Finset.range n,
        wcount m (clip m n x) (clip m n y) (clip m n z) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    exact count_eq_wcount m n x y z (Finset.mem_range.mp hx)
      (Finset.mem_range.mp hy) (Finset.mem_range.mp hz)
  rw [hA]
  rw [Finset.sum_congr rfl fun x _ => sum2 m n h (clip m n x)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rw [census (fun p => S2 m p) m n h, census (fun p => S1 m p) m n h,
    census (fun p => S0 m p) m n h]
  unfold V3c V2c V1c V0c
  ring

/-! ## The seven OEIS entries -/

/-- **OEIS A187164**: 3-step SAWs on `n × n × n`; `a(n) = 30n³ - 60n² + 24n`
for `n > 1`. -/
theorem A187164 (n : Nat) (h : 2 ≤ n) :
    (A3 2 n : Int) = 30 * (n : Int) ^ 3 - 60 * n ^ 2 + 24 * n := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 5 := ⟨n - 5, by omega⟩
    have hp := A3_eq_poly 2 (t + 5) (by omega)
    have v3 : V3c 2 = 30 := by native_decide
    have v2 : V2c 2 = 300 := by native_decide
    have v1 : V1c 2 = 984 := by native_decide
    have v0 : V0c 2 = 1056 := by native_decide
    rw [hp, v3, v2, v1, v0]
    have ht : t + 5 - 2 * 2 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A187165**: 4-step SAWs; `a(n) = 150n³ - 426n² + 312n - 48` for
`n > 2`. -/
theorem A187165 (n : Nat) (h : 3 ≤ n) :
    (A3 3 n : Int) = 150 * (n : Int) ^ 3 - 426 * n ^ 2 + 312 * n - 48 := by
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 7 := ⟨n - 7, by omega⟩
    have hp := A3_eq_poly 3 (t + 7) (by omega)
    have v3 : V3c 3 = 150 := by native_decide
    have v2 : V2c 3 = 2274 := by native_decide
    have v1 : V1c 3 = 11400 := by native_decide
    have v0 : V0c 3 = 18888 := by native_decide
    rw [hp, v3, v2, v1, v0]
    have ht : t + 7 - 2 * 3 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A187166**: 5-step SAWs; `a(n) = 726n³ - 2640n² + 2688n - 720` for
`n > 3`. -/
theorem A187166 (n : Nat) (h : 4 ≤ n) :
    (A3 4 n : Int) = 726 * (n : Int) ^ 3 - 2640 * n ^ 2 + 2688 * n - 720 := by
  rcases Nat.lt_or_ge n 9 with h9 | h9
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 9 := ⟨n - 9, by omega⟩
    have hp := A3_eq_poly 4 (t + 9) (by omega)
    have v3 : V3c 4 = 726 := by native_decide
    have v2 : V2c 4 = 14784 := by native_decide
    have v1 : V1c 4 = 99840 := by native_decide
    have v0 : V0c 4 = 223536 := by native_decide
    rw [hp, v3, v2, v1, v0]
    have ht : t + 9 - 2 * 4 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A187167**: 6-step SAWs; `a(n) = 3534n³ - 15366n² + 19536n - 7056`
for `n > 4`. -/
theorem A187167 (n : Nat) (h : 5 ≤ n) :
    (A3 5 n : Int)
      = 3534 * (n : Int) ^ 3 - 15366 * n ^ 2 + 19536 * n - 7056 := by
  rcases Nat.lt_or_ge n 11 with h11 | h11
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 11 := ⟨n - 11, by omega⟩
    have hp := A3_eq_poly 5 (t + 11) (by omega)
    have v3 : V3c 5 = 3534 := by native_decide
    have v2 : V2c 5 = 90654 := by native_decide
    have v1 : V1c 5 = 772416 := by native_decide
    have v0 : V0c 5 = 2185704 := by native_decide
    rw [hp, v3, v2, v1, v0]
    have ht : t + 11 - 2 * 5 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

set_option maxHeartbeats 0 in
/-- **OEIS A187168**: 7-step SAWs; `a(n) = 16926n³ - 85380n² + 128832n -
57312` for `n > 5`. -/
theorem A187168 (n : Nat) (h : 6 ≤ n) :
    (A3 6 n : Int)
      = 16926 * (n : Int) ^ 3 - 85380 * n ^ 2 + 128832 * n - 57312 := by
  rcases Nat.lt_or_ge n 13 with h13 | h13
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 13 := ⟨n - 13, by omega⟩
    have hp := A3_eq_poly 6 (t + 13) (by omega)
    have v3 : V3c 6 = 16926 := by native_decide
    have v2 : V2c 6 = 523956 := by native_decide
    have v1 : V1c 6 = 5391744 := by native_decide
    have v0 : V0c 6 = 18442080 := by native_decide
    rw [hp, v3, v2, v1, v0]
    have ht : t + 13 - 2 * 6 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

set_option maxHeartbeats 0 in
/-- **OEIS A187169**: 8-step SAWs; `a(n) = 81390n³ - 463074n² + 801216n -
418032` for `n > 6`. -/
theorem A187169 (n : Nat) (h : 7 ≤ n) :
    (A3 7 n : Int)
      = 81390 * (n : Int) ^ 3 - 463074 * n ^ 2 + 801216 * n - 418032 := by
  rcases Nat.lt_or_ge n 15 with h15 | h15
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 15 := ⟨n - 15, by omega⟩
    have hp := A3_eq_poly 7 (t + 15) (by omega)
    have v3 : V3c 7 = 81390 := by native_decide
    have v2 : V2c 7 = 2955306 := by native_decide
    have v1 : V1c 7 = 35692464 := by native_decide
    have v0 : V0c 7 = 143370648 := by native_decide
    rw [hp, v3, v2, v1, v0]
    have ht : t + 15 - 2 * 7 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

set_option maxHeartbeats 0 in
/-- **OEIS A187170**: 9-step SAWs; `a(n) = 387966n³ - 2452704n² + 4766544n -
2833872` for `n > 7`. -/
theorem A187170 (n : Nat) (h : 8 ≤ n) :
    (A3 8 n : Int)
      = 387966 * (n : Int) ^ 3 - 2452704 * n ^ 2 + 4766544 * n - 2833872 := by
  rcases Nat.lt_or_ge n 17 with h17 | h17
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 17 := ⟨n - 17, by omega⟩
    have hp := A3_eq_poly 8 (t + 17) (by omega)
    have v3 : V3c 8 = 387966 := by native_decide
    have v2 : V2c 8 = 16169664 := by native_decide
    have v1 : V1c 8 = 224237904 := by native_decide
    have v0 : V0c 8 = 1034647344 := by native_decide
    rw [hp, v3, v2, v1, v0]
    have ht : t + 17 - 2 * 8 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

end D3
end SawProofs
