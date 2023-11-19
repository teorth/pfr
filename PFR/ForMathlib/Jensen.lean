import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Finset.Option
import Mathlib.Tactic.FieldSimp

/-!
# Equality case of Jensen's inequality

-/

open BigOperators Option Finset

variable {𝕜 : Type*} {E : Type*} {β : Type*} {ι : Type*}
  [LinearOrderedField 𝕜] [AddCommGroup E] [OrderedAddCommGroup β] [Module 𝕜 E]
  [Module 𝕜 β] [OrderedSMul 𝕜 β] [Fintype ι] {s : Set E} {f : E → β} {t : Finset ι}

/-- A version of Jensen's inequality in which one element plays a distinguished role. -/
theorem ConvexOn.map_add_sum_le {v : 𝕜} {w : ι → 𝕜}
    {p : ι → E} (q : E) (hf : ConvexOn 𝕜 s f) (h₀' : 0 ≤ v) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i in t, w i = 1) (hmem' : q ∈ s) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (v • q + ∑ i in t, w i • p i) ≤ v • f q + ∑ i in t, w i • f (p i) := by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have : f (∑ j in insertNone t, W j • P j) ≤ ∑ j in insertNone t, W j • f (P j) := by
    apply hf.map_sum_le
    · rintro (_|i) hi
      · exact h₀'
      · apply h₀
        simpa using hi
    · simpa using h₁
    · rintro (_|i) hi
      · exact hmem'
      · apply hmem
        simpa using hi
  simpa using this

/-- A form of the equality case of Jensen's equality.  For a strictly convex function `f` and
positive weights `w`, if an indexed family of points contains two which are not equal, then we have
strict inequality in Jensen's inequality: `f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i)`.

See also `StrictConvexOn.map_sum_eq_iff`. -/
theorem StrictConvexOn.map_sum_lt {w : ι → 𝕜} {p : ι → E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) {j1 j2 : ι}
    (hj1 : j1 ∈ t) (hj2 : j2 ∈ t) (hjp : p j1 ≠ p j2) :
    f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) := by
  classical
  let t' : Finset ι := (t.erase j1).erase j2
  have ht'' : t' ⊆ t := by intro; simp
  have hj2' : j2 ∉ t' := by simp
  have hj1' : j1 ∉ insert j2 t' := by
    simp only [Finset.mem_erase, Finset.mem_insert]
    tauto
  have hj12 : j2 ∈ Finset.erase t j1 := by
    simp only [Finset.mem_erase]
    tauto
  have ht' : t = insert j1 (insert j2 t'):= by
    rw [Finset.insert_erase hj12, Finset.insert_erase hj1]
  rw [ht'] at h₁ ⊢
  simp only [Finset.sum_insert hj1', Finset.sum_insert hj2'] at h₁ ⊢
  have := h₀ j1 hj1
  have := h₀ j2 hj2
  let c := w j1 + w j2
  have h1 : w j1 / c + w j2 / c = 1 := by field_simp
  have h2 : c * (w j1 / c) = w j1 := by field_simp; ring
  have h3 : c * (w j2 / c) = w j2 := by field_simp; ring
  calc f (w j1 • p j1 + (w j2 • p j2 + ∑ x in t', w x • p x))
      = f ((w j1 • p j1 + w j2 • p j2) + ∑ x in t', w x • p x) := by abel_nf
    _ = f ((c • ((w j1 / c) • p j1 + (w j2 / c) • p j2)) + ∑ x in t', w x • p x) := by
      rw [smul_add, ← mul_smul, ← mul_smul, h2, h3]
    _ ≤ c • f ((w j1 / c) • p j1 + (w j2 / c) • p j2) + ∑ x in t', w x • f (p x) := by
      -- apply the usual Jensen's inequality wrt the weighted average of the two distinguished
      -- points and all the other points
      apply hf.convexOn.map_add_sum_le
      · positivity
      · intro i hi
        refine (h₀ _ (ht'' hi)).le
      · rw [← h₁]
        abel_nf
      · refine hf.1 (hmem _ hj1) (hmem _ hj2) ?_ ?_ h1 <;> positivity
      · intro i hi
        refine (hmem i (ht'' hi))
    _ < c • ((w j1 / c) • f (p j1) + (w j2 / c) • f (p j2)) + ∑ x in t', w x • f (p x) := by
      -- then apply the definition of strict convexity for the two distinguished points
      gcongr
      refine hf.2 (hmem _ hj1) (hmem _ hj2) hjp ?_ ?_ h1 <;> positivity
    _ = (w j1 • f (p j1) + w j2 • f (p j2)) + ∑ x in t', w x • f (p x) := by
      rw [smul_add, ← mul_smul, ← mul_smul, h2, h3]
    _ = w j1 • f (p j1) + (w j2 • f (p j2) + ∑ x in t', w x • f (p x)) := by abel_nf

/-- A form of the equality case of Jensen's equality.  For a strictly convex function `f` and
positive weights `w`, if `f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)`, then the points `p`
are all equal.

See also `StrictConvexOn.map_sum_eq_iff`. -/
theorem StrictConvexOn.eq_of_map_sum_eq {w : ι → 𝕜} {p : ι → E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)) {j1 j2 : ι} (hj1 : j1 ∈ t)
    (hj2 : j2 ∈ t) :
    p j1 = p j2 := by
  revert j2 j1
  contrapose! h_eq
  apply ne_of_lt
  obtain ⟨j1, j2, hj1, hj2, hjp⟩ := h_eq
  exact hf.map_sum_lt h₀ h₁ hmem hj1 hj2 hjp

/-- Canonical form of the equality case of Jensen's equality.  For a strictly convex function `f`
and positive weights `w`, we have `f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)` if and only if
the points `p` are all equal (and in fact all equal to their center of mass wrt `w`). -/
theorem StrictConvexOn.map_sum_eq_iff {w : ι → 𝕜} {p : ι → E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i in t, w i • p i := by
  constructor
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H : ∀ j ∈ t, p j = p i₀ := by
      intro j hj
      apply hf.eq_of_map_sum_eq h₀ h₁ hmem h_eq hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1:𝕜) • p i₀ := by simp
      _ = (∑ j in t, w j) • p i₀ := by rw [h₁]
      _ = ∑ j in t, (w j • p i₀) := by rw [Finset.sum_smul]
      _ = ∑ j in t, (w j • p j) := by congr! 2 with j hj; rw [← H _ hj]
  · intro h
    have H : ∀ j ∈ t, w j • f (p j) = w j • f (∑ i in t, w i • p i) := by
      intro j hj
      simp [h j hj]
    rw [Finset.sum_congr rfl H, ← Finset.sum_smul, h₁, one_smul]

/-- Canonical form of the equality case of Jensen's equality.  For a strictly concave function `f`
and positive weights `w`, we have `f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)` if and only if
the points `p` are all equal (and in fact all equal to their center of mass wrt `w`). -/
theorem StrictConcaveOn.map_sum_eq_iff {w : ι → 𝕜} {p : ι → E} (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i in t, w i • p i := by
  simpa using hf.neg.map_sum_eq_iff h₀ h₁ hmem

/-- the equality case of Jensen's inequality -/
theorem StrictConvexOn.map_sum_eq_iff' [Fintype ι] {w : ι → 𝕜} {p : ι → E}
    (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ i, w i = 1) (hmem : ∀ i, p i ∈ s) :
    f (∑ i, w i • p i) = ∑ i, w i • f (p i) ↔ ∀ j, w j = 0 ∨ p j = ∑ i, w i • p i := by
  let t := Finset.filter (fun i ↦ 0 < w i) Finset.univ
  have H : ∀ i, i ∉ t → w i = 0 := by
    intro i hi
    exact le_antisymm (by simpa using hi) (h₀ i)
  have ht₁ : ∀ i ∈ t, 0 < w i := by intro i hi; simpa using hi
  have ht₂ : ∑ i in t, w i = 1 := (Finset.sum_subset (by simp) (fun x _ ↦ H x)).trans h₁
  have H1 : ∑ i in t, w i • p i = ∑ i : ι, w i • p i := by
    apply Finset.sum_subset (by simp)
    intro i _ hi
    simp [H _ hi]
  have H2 : ∑ i in t, w i • f (p i) = ∑ i : ι, w i • f (p i) := by
    apply Finset.sum_subset (by simp)
    intro i _ hi
    simp [H _ hi]
  convert hf.map_sum_eq_iff ht₁ ht₂ (fun i _ ↦ hmem i) using 2 with i
  · simp [H1]
  · simp [H2]
  · obtain hi | hi := eq_or_lt_of_le (h₀ i)
    · simp [← hi]
    · simp [hi.ne', hi, H1]

/-- the equality case of Jensen's inequality -/
theorem StrictConcaveOn.map_sum_eq_iff' [Fintype ι] {w : ι → 𝕜} {p : ι → E}
    (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ i, w i = 1) (hmem : ∀ i, p i ∈ s) :
    f (∑ i, w i • p i) = ∑ i, w i • f (p i) ↔ ∀ j, w j = 0 ∨ p j = ∑ i, w i • p i := by
  simpa using hf.neg.map_sum_eq_iff' h₀ h₁ hmem
