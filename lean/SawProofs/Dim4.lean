import SawProofs.Dim2

/-!
# The 4D case: OEIS A188785–A188789

Same blueprint as `Dim2.lean`/`Dim3.lean` with cells in `ℤ⁴`; reuses
`D2.clip` and `D2.census`.  `A4_eq_poly` is proved from Lean's standard
axioms; the five OEIS entry theorems add `native_decide` evaluations.
-/

namespace SawProofs
namespace D4

open SawProofs.D2 (clip census)

abbrev Cell4 := Int × Int × Int × Int

structure Box4 where
  x1 : Int
  x2 : Int
  y1 : Int
  y2 : Int
  z1 : Int
  z2 : Int
  w1 : Int
  w2 : Int

def inB (B : Box4) (p : Cell4) : Prop :=
  B.x1 ≤ p.1 ∧ p.1 ≤ B.x2 ∧ B.y1 ≤ p.2.1 ∧ p.2.1 ≤ B.y2
    ∧ B.z1 ≤ p.2.2.1 ∧ p.2.2.1 ≤ B.z2 ∧ B.w1 ≤ p.2.2.2 ∧ p.2.2.2 ≤ B.w2

instance (B : Box4) (p : Cell4) : Decidable (inB B p) := by
  unfold inB; infer_instance

def nbrs (p : Cell4) : List Cell4 :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2),
   (p.1, p.2.1 + 1, p.2.2), (p.1, p.2.1 - 1, p.2.2),
   (p.1, p.2.1, p.2.2.1 + 1, p.2.2.2), (p.1, p.2.1, p.2.2.1 - 1, p.2.2.2),
   (p.1, p.2.1, p.2.2.1, p.2.2.2 + 1), (p.1, p.2.1, p.2.2.1, p.2.2.2 - 1)]

def countFrom (B : Box4) : Nat → List Cell4 → Cell4 → Nat
  | 0, _, _ => 1
  | m + 1, vis, pos =>
    (nbrs pos).foldl
      (fun acc q =>
        if inB B q ∧ q ∉ vis then acc + countFrom B m (q :: vis) q else acc)
      0

def near (m : Nat) (p q : Cell4) : Prop :=
  (p.1 - q.1).natAbs ≤ m ∧ (p.2.1 - q.2.1).natAbs ≤ m
    ∧ (p.2.2.1 - q.2.2.1).natAbs ≤ m ∧ (p.2.2.2 - q.2.2.2).natAbs ≤ m

theorem near_mono {m m' : Nat} (h : m ≤ m') {p q : Cell4} (hn : near m p q) :
    near m' p q := by
  unfold near at *; omega

theorem near_step {m : Nat} {p q r : Cell4} (h1 : near 1 p q)
    (h2 : near m q r) : near (m + 1) p r := by
  unfold near at *; omega

theorem near_nbrs {p q : Cell4} (h : q ∈ nbrs p) : near 1 p q := by
  simp only [nbrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst h <;> unfold near <;>
    simp <;> omega

theorem countFrom_congr (B B' : Box4) :
    ∀ (m : Nat) (vis : List Cell4) (pos : Cell4),
      (∀ q, near m pos q → (inB B q ↔ inB B' q)) →
      countFrom B m vis pos = countFrom B' m vis pos := by
  intro m
  induction m with
  | zero => intro vis pos _; rfl
  | succ m ih =>
    intro vis pos h
    have step : ∀ (acc : Nat) (q : Cell4), q ∈ nbrs pos →
        (if inB B q ∧ q ∉ vis then acc + countFrom B m (q :: vis) q else acc)
          = (if inB B' q ∧ q ∉ vis then acc + countFrom B' m (q :: vis) q
             else acc) := by
      intro acc q hq
      have h1 : near 1 pos q := near_nbrs hq
      have hiff : inB B q ↔ inB B' q := h q (near_mono (by omega) h1)
      have hrec : countFrom B m (q :: vis) q = countFrom B' m (q :: vis) q :=
        ih (q :: vis) q (fun r hr => h r (near_step h1 hr))
      exact if_congr (and_congr_left' hiff) (by rw [hrec]) rfl
    have main : ∀ (l : List Cell4), (∀ q ∈ l, q ∈ nbrs pos) → ∀ acc : Nat,
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

def shift (v : Cell4) (p : Cell4) : Cell4 :=
  (p.1 + v.1, p.2.1 + v.2.1, p.2.2.1 + v.2.2.1, p.2.2.2 + v.2.2.2)

def shiftBox (v : Cell4) (B : Box4) : Box4 :=
  ⟨B.x1 + v.1, B.x2 + v.1, B.y1 + v.2.1, B.y2 + v.2.1,
   B.z1 + v.2.2.1, B.z2 + v.2.2.1, B.w1 + v.2.2.2, B.w2 + v.2.2.2⟩

theorem shift_injective (v : Cell4) : Function.Injective (shift v) := by
  intro a b hab
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  simp only [shift, Prod.ext_iff] at hab ⊢
  omega

theorem nbrs_shift (v p : Cell4) :
    nbrs (shift v p) = (nbrs p).map (shift v) := by
  simp only [nbrs, shift, List.map_cons, List.map_nil, List.cons.injEq,
    Prod.mk.injEq, and_true, true_and]
  omega

theorem inB_shift (v : Cell4) (B : Box4) (q : Cell4) :
    inB (shiftBox v B) (shift v q) ↔ inB B q := by
  obtain ⟨qx, qy, qz, qw⟩ := q
  obtain ⟨a, b, c, d, e, f, g, k⟩ := B
  unfold inB shiftBox shift
  dsimp only
  omega

theorem countFrom_shift (v : Cell4) (B : Box4) :
    ∀ (m : Nat) (vis : List Cell4) (pos : Cell4),
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

def boxN (n : Nat) : Box4 :=
  ⟨0, (n : Int) - 1, 0, (n : Int) - 1, 0, (n : Int) - 1, 0, (n : Int) - 1⟩

def profBox (px py pz pw : Nat × Nat) : Box4 :=
  ⟨-(px.1 : Int), (px.2 : Int), -(py.1 : Int), (py.2 : Int),
   -(pz.1 : Int), (pz.2 : Int), -(pw.1 : Int), (pw.2 : Int)⟩

def wcount (m : Nat) (px py pz pw : Nat × Nat) : Nat :=
  countFrom (profBox px py pz pw) m
    [((0 : Int), (0 : Int), (0 : Int), (0 : Int))] (0, 0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem count_eq_wcount (m n x y z w : Nat) (hx : x < n) (hy : y < n)
    (hz : z < n) (hw : w < n) :
    countFrom (boxN n) m [((x : Int), (y : Int), (z : Int), (w : Int))]
        ((x : Int), (y : Int), (z : Int), (w : Int))
      = wcount m (clip m n x) (clip m n y) (clip m n z) (clip m n w) := by
  have h1 : countFrom (boxN n) m
        [((x : Int), (y : Int), (z : Int), (w : Int))]
        ((x : Int), (y : Int), (z : Int), (w : Int))
      = countFrom (shiftBox ((x : Int), (y : Int), (z : Int), (w : Int))
          (profBox (clip m n x) (clip m n y) (clip m n z) (clip m n w))) m
          [((x : Int), (y : Int), (z : Int), (w : Int))]
          ((x : Int), (y : Int), (z : Int), (w : Int)) := by
    apply countFrom_congr
    intro q hq
    obtain ⟨qx, qy, qz, qw⟩ := q
    unfold near at hq
    unfold inB boxN shiftBox profBox SawProofs.D2.clip
    dsimp only at hq ⊢
    push_cast [Nat.cast_min] at hq ⊢
    omega
  have h2 : countFrom (shiftBox ((x : Int), (y : Int), (z : Int), (w : Int))
        (profBox (clip m n x) (clip m n y) (clip m n z) (clip m n w))) m
        [((x : Int), (y : Int), (z : Int), (w : Int))]
        ((x : Int), (y : Int), (z : Int), (w : Int))
      = wcount m (clip m n x) (clip m n y) (clip m n z) (clip m n w) := by
    have := countFrom_shift ((x : Int), (y : Int), (z : Int), (w : Int))
      (profBox (clip m n x) (clip m n y) (clip m n z) (clip m n w)) m
      [((0 : Int), (0 : Int), (0 : Int), (0 : Int))] (0, 0, 0, 0)
    have e1 : shift ((x : Int), (y : Int), (z : Int), (w : Int))
        ((0 : Int), (0 : Int), (0 : Int), (0 : Int))
        = ((x : Int), (y : Int), (z : Int), (w : Int)) := by
      unfold shift; simp
    have e2 : ([((0 : Int), (0 : Int), (0 : Int), (0 : Int))].map
          (shift ((x : Int), (y : Int), (z : Int), (w : Int))))
        = [((x : Int), (y : Int), (z : Int), (w : Int))] := by simp [shift]
    rw [e1, e2] at this
    rw [this]
    rfl
  rw [h1, h2]

/-! ## Total count and polynomial theorem -/

/-- Total number of walks of `m` edges in the `n⁴` grid, summed over all
starting cells: the OEIS count for `(m+1)`-step walks. -/
def A4 (m n : Nat) : Nat :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
    ∑ w ∈ Finset.range n,
      countFrom (boxN n) m [((x : Int), (y : Int), (z : Int), (w : Int))]
        ((x : Int), (y : Int), (z : Int), (w : Int))

def L1 (m : Nat) (p q r : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range m, (wcount m p q r (i, m) + wcount m p q r (m, i))

def U2 (m : Nat) (p q : Nat × Nat) : Nat := wcount m p q (m, m) (m, m)

def U1 (m : Nat) (p q : Nat × Nat) : Nat :=
  (∑ i ∈ Finset.range m,
      (wcount m p q (i, m) (m, m) + wcount m p q (m, i) (m, m)))
    + L1 m p q (m, m)

def U0 (m : Nat) (p q : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range m, (L1 m p q (i, m) + L1 m p q (m, i))

theorem sum2 (m n : Nat) (h : 2 * m + 1 ≤ n) (p q : Nat × Nat) :
    ∑ z ∈ Finset.range n, ∑ w ∈ Finset.range n,
        wcount m p q (clip m n z) (clip m n w)
      = (n - 2 * m) ^ 2 * U2 m p q + (n - 2 * m) * U1 m p q + U0 m p q := by
  have inner : ∀ z : Nat,
      ∑ w ∈ Finset.range n, wcount m p q (clip m n z) (clip m n w)
        = (n - 2 * m) * wcount m p q (clip m n z) (m, m)
          + L1 m p q (clip m n z) := by
    intro z
    exact census (fun r => wcount m p q (clip m n z) r) m n h
  rw [Finset.sum_congr rfl fun z _ => inner z, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [census (fun r => wcount m p q r (m, m)) m n h,
    census (fun r => L1 m p q r) m n h]
  unfold U2 U1 U0
  ring

def S3 (m : Nat) (p : Nat × Nat) : Nat := U2 m p (m, m)

def S2 (m : Nat) (p : Nat × Nat) : Nat :=
  (∑ i ∈ Finset.range m, (U2 m p (i, m) + U2 m p (m, i))) + U1 m p (m, m)

def S1 (m : Nat) (p : Nat × Nat) : Nat :=
  (∑ i ∈ Finset.range m, (U1 m p (i, m) + U1 m p (m, i))) + U0 m p (m, m)

def S0 (m : Nat) (p : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range m, (U0 m p (i, m) + U0 m p (m, i))

theorem sum3 (m n : Nat) (h : 2 * m + 1 ≤ n) (p : Nat × Nat) :
    ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, ∑ w ∈ Finset.range n,
        wcount m p (clip m n y) (clip m n z) (clip m n w)
      = (n - 2 * m) ^ 3 * S3 m p + (n - 2 * m) ^ 2 * S2 m p
        + (n - 2 * m) * S1 m p + S0 m p := by
  rw [Finset.sum_congr rfl fun y _ => sum2 m n h p (clip m n y)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rw [census (fun r => U2 m p r) m n h, census (fun r => U1 m p r) m n h,
    census (fun r => U0 m p r) m n h]
  unfold S3 S2 S1 S0
  ring

def V4c (m : Nat) : Nat := S3 m (m, m)

def V3c (m : Nat) : Nat :=
  (∑ i ∈ Finset.range m, (S3 m (i, m) + S3 m (m, i))) + S2 m (m, m)

def V2c (m : Nat) : Nat :=
  (∑ i ∈ Finset.range m, (S2 m (i, m) + S2 m (m, i))) + S1 m (m, m)

def V1c (m : Nat) : Nat :=
  (∑ i ∈ Finset.range m, (S1 m (i, m) + S1 m (m, i))) + S0 m (m, m)

def V0c (m : Nat) : Nat :=
  ∑ i ∈ Finset.range m, (S0 m (i, m) + S0 m (m, i))

/-- Main theorem (4D): explicit quartic in `n - 2m` for `n ≥ 2m+1`. -/
theorem A4_eq_poly (m n : Nat) (h : 2 * m + 1 ≤ n) :
    A4 m n = (n - 2 * m) ^ 4 * V4c m + (n - 2 * m) ^ 3 * V3c m
      + (n - 2 * m) ^ 2 * V2c m + (n - 2 * m) * V1c m + V0c m := by
  have hA : A4 m n = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
      ∑ z ∈ Finset.range n, ∑ w ∈ Finset.range n,
        wcount m (clip m n x) (clip m n y) (clip m n z) (clip m n w) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro w hw
    exact count_eq_wcount m n x y z w (Finset.mem_range.mp hx)
      (Finset.mem_range.mp hy) (Finset.mem_range.mp hz)
      (Finset.mem_range.mp hw)
  rw [hA]
  rw [Finset.sum_congr rfl fun x _ => sum3 m n h (clip m n x)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [census (fun p => S3 m p) m n h, census (fun p => S2 m p) m n h,
    census (fun p => S1 m p) m n h, census (fun p => S0 m p) m n h]
  unfold V4c V3c V2c V1c V0c
  ring

/-! ## The five OEIS entries -/

/-- **OEIS A188785**: 2-step SAWs on the `n⁴` grid; `a(n) = 8n⁴ - 8n³`. -/
theorem A188785 (n : Nat) (h : 1 ≤ n) :
    (A4 1 n : Int) = 8 * (n : Int) ^ 4 - 8 * n ^ 3 := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 3 := ⟨n - 3, by omega⟩
    have hp := A4_eq_poly 1 (t + 3) (by omega)
    have v4 : V4c 1 = 8 := by native_decide
    have v3 : V3c 1 = 56 := by native_decide
    have v2 : V2c 1 = 144 := by native_decide
    have v1 : V1c 1 = 160 := by native_decide
    have v0 : V0c 1 = 64 := by native_decide
    rw [hp, v4, v3, v2, v1, v0]
    have ht : t + 3 - 2 * 1 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188786**: 3-step SAWs; `a(n) = 56n⁴ - 112n³ + 48n²` for `n > 1`. -/
theorem A188786 (n : Nat) (h : 2 ≤ n) :
    (A4 2 n : Int) = 56 * (n : Int) ^ 4 - 112 * n ^ 3 + 48 * n ^ 2 := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 5 := ⟨n - 5, by omega⟩
    have hp := A4_eq_poly 2 (t + 5) (by omega)
    have v4 : V4c 2 = 56 := by native_decide
    have v3 : V3c 2 = 784 := by native_decide
    have v2 : V2c 2 = 4080 := by native_decide
    have v1 : V1c 2 = 9344 := by native_decide
    have v0 : V0c 2 = 7936 := by native_decide
    rw [hp, v4, v3, v2, v1, v0]
    have ht : t + 5 - 2 * 2 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

/-- **OEIS A188787**: 4-step SAWs; `a(n) = 392n⁴ - 1128n³ + 912n² - 192n` for
`n > 2`. -/
theorem A188787 (n : Nat) (h : 3 ≤ n) :
    (A4 3 n : Int)
      = 392 * (n : Int) ^ 4 - 1128 * n ^ 3 + 912 * n ^ 2 - 192 * n := by
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 7 := ⟨n - 7, by omega⟩
    have hp := A4_eq_poly 3 (t + 7) (by omega)
    have v4 : V4c 3 = 392 := by native_decide
    have v3 : V3c 3 = 8280 := by native_decide
    have v2 : V2c 3 = 65280 := by native_decide
    have v1 : V1c 3 = 227616 := by native_decide
    have v0 : V0c 3 = 296064 := by native_decide
    rw [hp, v4, v3, v2, v1, v0]
    have ht : t + 7 - 2 * 3 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

set_option maxHeartbeats 0 in
/-- **OEIS A188788**: 5-step SAWs; `a(n) = 2696n⁴ - 9968n³ + 11424n² - 4416n
+ 384` for `n > 3`. -/
theorem A188788 (n : Nat) (h : 4 ≤ n) :
    (A4 4 n : Int) = 2696 * (n : Int) ^ 4 - 9968 * n ^ 3 + 11424 * n ^ 2
      - 4416 * n + 384 := by
  rcases Nat.lt_or_ge n 9 with h9 | h9
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 9 := ⟨n - 9, by omega⟩
    have hp := A4_eq_poly 4 (t + 9) (by omega)
    have v4 : V4c 4 = 2696 := by native_decide
    have v3 : V3c 4 = 76304 := by native_decide
    have v2 : V2c 4 = 807456 := by native_decide
    have v1 : V1c 4 = 3785920 := by native_decide
    have v0 : V0c 4 = 6635392 := by native_decide
    rw [hp, v4, v3, v2, v1, v0]
    have ht : t + 9 - 2 * 4 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

set_option maxHeartbeats 0 in
/-- **OEIS A188789**: 6-step SAWs; `a(n) = 18584n⁴ - 82552n³ + 119616n² -
64320n + 9984` for `n > 4`. -/
theorem A188789 (n : Nat) (h : 5 ≤ n) :
    (A4 5 n : Int) = 18584 * (n : Int) ^ 4 - 82552 * n ^ 3 + 119616 * n ^ 2
      - 64320 * n + 9984 := by
  rcases Nat.lt_or_ge n 11 with h11 | h11
  · interval_cases n <;> native_decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 11 := ⟨n - 11, by omega⟩
    have hp := A4_eq_poly 5 (t + 11) (by omega)
    have v4 : V4c 5 = 18584 := by native_decide
    have v3 : V3c 5 = 660808 := by native_decide
    have v2 : V2c 5 = 8793456 := by native_decide
    have v1 : V1c 5 = 51898400 := by native_decide
    have v0 : V0c 5 = 114616384 := by native_decide
    rw [hp, v4, v3, v2, v1, v0]
    have ht : t + 11 - 2 * 5 = t + 1 := by omega
    rw [ht]
    push_cast
    ring

end D4
end SawProofs
