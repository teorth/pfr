import Mathlib
-- to do: be more specific on which part of Mathlib is being imported

open Real

/-! The purpose of this file is to record basic analytic properties of the function h(x) = - x * log x on the unit interval, for use in the theory of Shannon entropy.  Thanks to Heather Macbeth for optimizations. -/

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))

-- the entropy function.  Note that h 0 = 0 thanks to Lean notational conventions. May want to change the name of h and/or localize it to a namespace
noncomputable def h := (fun x : ℝ ↦ - x * log x)

/-- h is nonnegative -/
lemma h_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ h x := by
  unfold h
  rw [neg_mul_comm]
  apply mul_nonneg h1
  simp
  exact log_nonpos h1 h2

/-- h 0 = 0 -/
@[simp]
lemma h_zero : h 0 = 0 := by unfold h; simp

/-- h 1 = 0 -/
@[simp]
lemma h_one : h 1 = 0 := by unfold h; simp

/-- a sublemma needed to get an upper bound for h. -/
lemma log_le {x:ℝ} (hx: 0 ≤ x) : log x ≤ x / rexp 1 := by
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx
  . rw [<-sub_le_sub_iff_right 1]
    convert (log_le_sub_one_of_pos (show 0 < (x * (Real.exp 1)⁻¹) by positivity)) using 1
    rw [log_mul]
    . simp; ring
    all_goals positivity
  simp [<-hx]

/-- an upper bound for h that can help prove continuity at 0. -/
lemma h_le {x : ℝ} (hx : 0 ≤ x) : h x ≤ 2 * (sqrt x) / rexp 1 := by
  unfold h
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx
  . rw [neg_mul_comm, <- log_inv, <- sq_sqrt (show 0 ≤ x⁻¹ by positivity), log_pow, <-mul_assoc, <- le_div_iff']
    convert log_le (show 0 ≤ sqrt x⁻¹ by positivity) using 1
    field_simp
    nth_rewrite 3 [<- sq_sqrt (show 0 ≤ x by positivity)]
    ring
    positivity
  simp [<-hx]

/-- To prove continuity of h we will need a version of the squeeze test. -/
lemma squeeze [TopologicalSpace α] [TopologicalSpace β] [LinearOrder β] [OrderTopology β] {f g h : α → β} {x : α} (hfg : f x = g x) (hgh : g x = h x) (lower : ∀ y : α, f y ≤ g y) (upper : ∀ y : α, g y ≤ h y) (f_cont : ContinuousAt f x) (h_cont : ContinuousAt h x) : ContinuousAt g x := by
  rw [continuousAt_iff_lower_upperSemicontinuousAt] at f_cont h_cont ⊢
  dsimp [LowerSemicontinuousAt, UpperSemicontinuousAt] at f_cont h_cont ⊢
  rw [hfg] at f_cont
  rw [<-hgh] at h_cont
  constructor
  . intro a ha
    apply Filter.Eventually.mono (f_cont.1 a ha)
    intro x hx
    exact lt_of_lt_of_le hx (lower x)
  intro a ha
  apply Filter.Eventually.mono (h_cont.2 a ha)
  intro x hx
  exact LE.le.trans_lt (upper x) hx

/-- actually we need the squeeze test restricted to a subdomain. -/
lemma squeezeWithin [TopologicalSpace α] [TopologicalSpace β] [LinearOrder β] [OrderTopology β] {f g h : α → β} {s : Set α} {x : α} (hx : x ∈ s) (hfg : f x = g x) (hgh : g x = h x) (lower : ∀ y ∈ s, f y ≤ g y) (upper : ∀ y ∈ s, g y ≤ h y) (f_cont : ContinuousWithinAt f s x) (h_cont : ContinuousWithinAt h s x) : ContinuousWithinAt g s x := by
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx] at f_cont h_cont ⊢
  set f' := Set.restrict s f
  set g' := Set.restrict s g
  set h' := Set.restrict s h
  set x' : s := ⟨ x, hx ⟩
  apply squeeze (show f' x' = g' x' by simpa) (show g' x' = h' x' by simpa) _ _ f_cont h_cont
  . intro y; simp [lower y]
  intro y; simp [upper y]

/-- Finally, the continuity of h. -/
lemma h_cont : ContinuousOn h (Set.Icc 0 1) := by
  dsimp [ContinuousOn]
  intro x hx
  simp at hx; rcases hx with ⟨ hx1, hx2 ⟩
  rw [le_iff_lt_or_eq] at hx1
  rcases hx1 with hx1 | hx1
  . refine (continuous_id.neg.continuousAt.mul (continuousAt_log ?_)).continuousWithinAt
    linarith
-- the tricky case : continuity at zero!
  rw [<- hx1]
  let f := fun _ : ℝ ↦ (0:ℝ)
  let g := fun x : ℝ ↦ (2 * sqrt x) / rexp 1
  have f_cont : ContinuousWithinAt f (Set.Icc 0 1) 0 := by
    apply continuousWithinAt_const
  have g_cont : ContinuousWithinAt g (Set.Icc 0 1) 0 := by
    apply Continuous.continuousWithinAt
    continuity
  apply squeezeWithin _ _ _ _ _ f_cont g_cont
  . simp
  . simp [h]
  . simp [h]
  . intro y hy
    exact h_nonneg hy.1 hy.2
  intro y hy
  exact h_le hy.1

/-- The derivative of h. -/
lemma h_deriv {x : ℝ} (hx: 0 < x) : HasDerivAt h (- log x + (- 1)) x := by
  convert hasDerivAt_id x |>.neg.mul (hasDerivAt_log ?_) using 1
  · field_simp
  · positivity

-- how to get differentiability from `HasDerivAt`
example : DifferentiableOn ℝ h (Set.Ioo 0 1) :=
  fun _ hx ↦ (h_deriv hx.1).differentiableAt.differentiableWithinAt

-- how to get the `deriv` from `HasDerivAt`
example {x : ℝ} (hx: 0 < x) : deriv h x = - log x + (- 1) := (h_deriv hx).deriv

/-- The concavity of h. -/
lemma h_concave : ConcaveOn ℝ (Set.Icc 0 1) h := by
  apply AntitoneOn.concaveOn_of_deriv
  . apply convex_Icc
  . exact h_cont
  . rw [interior_Icc]
    intro x hx
    exact (h_deriv hx.1).differentiableAt.differentiableWithinAt
  rw [interior_Icc]
  refine ((strictMonoOn_log.monotoneOn.mono ?_).neg.add_const (-1)).congr ?_
  · intro x hx
    exact hx.1
  · intro x hx
    rw [(h_deriv hx.1).deriv]

open BigOperators

lemma h_jensen [Fintype S] {w : S → ℝ} {p : S → ℝ} (h0 : ∀ s ∈ Finset.univ, 0 ≤ w s) (h1 : ∑ s in Finset.univ, w s = 1) (hmem : ∀ s ∈ Finset.univ, p s ∈ (Set.Icc 0 1)) : ∑ s in Finset.univ, (w s) * h (p s) ≤ h ( ∑ s in Finset.univ, (w s) * (p s)) := by
  convert ConcaveOn.le_map_sum h_concave h0 h1 hmem
