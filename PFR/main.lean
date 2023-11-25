import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement
import PFR.f2_vec
import PFR.entropy_pfr
import PFR.Tactic.RPowSimp


/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/-!
# Polynomial Freiman-Ruzsa conjecture

Here we prove the polynomial Freiman-Ruzsa conjecture.

-/

open Pointwise ProbabilityTheory MeasureTheory Real
universe u

namespace ProbabilityTheory

lemma PFR_conjecture_pos_aux {G : Type*} [AddCommGroup G] [Fintype G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K := by
  have card_AA_pos : (0 : ℝ) < Nat.card (A + A) := by
    have : Nonempty (A + A) := Set.nonempty_coe_sort.mpr (Set.Nonempty.add h₀A h₀A)
    have : Finite (A + A) := by exact Subtype.finite
    simp [Nat.cast_pos, Nat.card_pos_iff]
  have KA_pos : 0 < K ∧ (0 : ℝ) < Nat.card A := by
    have I : ¬ ((Nat.card A : ℝ) < 0) := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hA)
  exact ⟨KA_pos.2, card_AA_pos, KA_pos.1⟩


/-- A uniform distribution on a set with doubling constant `K` has entropy at most `log K` -/
theorem rdist_le_of_isUniform_of_card_add_le
    {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U₀ : Ω → G}
    (U₀unif : IsUniform A U₀) (U₀meas : Measurable U₀) : d[U₀ # U₀] ≤ log K := by
  obtain ⟨A_pos, AA_pos, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  rcases independent_copies_two U₀meas U₀meas with ⟨Ω, mΩ, U, U', hP, hU, hU', UU'_indep, idU, idU'⟩
  have Uunif : IsUniform A U := U₀unif.of_identDistrib idU.symm trivial
  have U'unif : IsUniform A U' := U₀unif.of_identDistrib idU'.symm trivial
  have IU : d[U # U'] ≤ log K := by
    have I : H[U + U'] ≤ log (Nat.card (A + A)) := by
      apply entropy_le_log_card_of_mem (hU.add hU')
      filter_upwards [Uunif.ae_mem, U'unif.ae_mem] with ω h1 h2
      exact Set.add_mem_add h1 h2
    have J : log (Nat.card (A + A)) ≤ log K + log (Nat.card A) := by
      apply (log_le_log' AA_pos hA).trans (le_of_eq _)
      rw [log_mul K_pos.ne' A_pos.ne']
    have : H[U + U'] = H[U - U'] := by congr; simp
    rw [UU'_indep.rdist_eq hU hU', Uunif.entropy_eq, U'unif.entropy_eq, ← this]
    linarith
  rwa [idU.rdist_eq idU'] at IU


/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$. -/
lemma prob_ge_exp_neg_entropy' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype S] (X : Ω → S) :
    ∃ s : S, rexp (- H[X ; μ]) ≤ μ.real (X ⁻¹' {s}) := by sorry

open scoped BigOperators

open Set Fintype

lemma goo (s : Finset α) : ∑ i in s, 1 = s.card := by
  simp only [Finset.sum_const, smul_eq_mul, mul_one]


section

variable {β β' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

theorem IndepFun.measure_inter_preimage_eq_mul {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) :=
  indepFun_iff_measure_inter_preimage_eq_mul.1 h _ _ hs ht

theorem IndepFun.measureReal_inter_preimage_eq_mul {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.real (f ⁻¹' s ∩ g ⁻¹' t) = μ.real (f ⁻¹' s) * μ.real (g ⁻¹' t) := by
  rw [measureReal_def, h.measure_inter_preimage_eq_mul hs ht, ENNReal.toReal_mul]; rfl

end

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V` with probability `# (A ∩ B) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub_zero {G : Type*} [AddCommGroup G] [Fintype G]
    {A B : Set G}
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U V : Ω → G}
    (Uunif : IsUniform A U) (Umeas : Measurable U) (Vunif : IsUniform B V) (Vmeas : Measurable V)
    (hindep : IndepFun U V) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {0})
      = Nat.card (A ∩ B : Set G) / (Nat.card A * Nat.card B) := by
  have : (U - V) ⁻¹' {0} = ⋃ (g : G), (U ⁻¹' {g} ∩ V⁻¹' {g}) := by
    ext ω; simp [sub_eq_zero, eq_comm]
  rw [this, measureReal_iUnion_fintype _ (fun i ↦ (Umeas trivial).inter (Vmeas trivial))
    (fun i ↦ measure_ne_top _ _)]; swap
  · intro g g' hgg'
    apply Set.disjoint_iff_inter_eq_empty.2
    ext a
    simp (config := {contextual := True}) [hgg']
  let W : Finset G := (A ∩ B).toFinite.toFinset
  calc
    ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p} ∩ V ⁻¹' {p})
      = ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply sum_congr _ _ (fun g ↦ ?_)
        rw [hindep.measureReal_inter_preimage_eq_mul trivial trivial]
    _ = ∑ p in W, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply (Finset.sum_finset_eq_sum _).symm
        intro i hi
        simp only [Finite.mem_toFinset, mem_inter_iff, not_and_or] at hi
        rcases hi with h'i|h'i
        · simp [Uunif.measureReal_preimage_of_nmem h'i]
        · simp [Vunif.measureReal_preimage_of_nmem h'i]
    _ = ∑ p in W, (1 / Nat.card A : ℝ) * (1 / Nat.card B) := by
        apply Finset.sum_congr rfl (fun i hi ↦ ?_)
        replace hi : i ∈ A ∩ B := by simpa using hi
        rw [Uunif.measureReal_preimage_of_mem (by trivial) hi.1,
            Vunif.measureReal_preimage_of_mem (by trivial) hi.2]
    _ = (W.card : ℝ) / (Nat.card A * Nat.card B) := by simp [div_eq_inv_mul]; ring
    _ = Nat.card (A ∩ B : Set G) / (Nat.card A * Nat.card B) := by
        congr; exact (Nat.card_eq_toFinset_card _).symm

lemma Nat.card_congr_equiv {α β : Type*} (A : Set α) (e : α ≃ β) : Nat.card A = Nat.card (e '' A) :=
    Nat.card_congr (e.image A)

@[to_additive]
lemma Nat.card_mul_singleton {G : Type*} [Group G] (A : Set G) (x : G) :
    Nat.card (A * ({x} : Set G)) = Nat.card A := by
  have : (Equiv.mulRight x) '' A = A * {x} := by simp
  rw [← this, ← Nat.card_congr_equiv]

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V + x` with probability `# (A ∩ (B + x)) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub {G : Type*} [AddCommGroup G] [Fintype G]
    {A B : Set G}
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U V : Ω → G}
    (Uunif : IsUniform A U) (Umeas : Measurable U) (Vunif : IsUniform B V) (Vmeas : Measurable V)
    (hindep : IndepFun U V) (x : G) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {x})
      = Nat.card (A ∩ (B + {x}) : Set G) / (Nat.card A * Nat.card B) := by
  let W := fun ω ↦ V ω + x
  have Wunif : IsUniform (B + {x}) W := sorry
  have Wmeas : Measurable W := Vmeas.add_const _
  have UWindep : IndepFun U W := by
    have : Measurable (fun g ↦ g + x) := measurable_id'
    exact hindep.comp measurable_id this
  have : (U - V) ⁻¹' {x} = (U - W) ⁻¹' {0} := by
    ext ω
    simp only [mem_preimage, Pi.add_apply, mem_singleton_iff, Pi.sub_apply, ← sub_eq_zero (b := x)]
    abel_nf
  rw [this, Uunif.measureReal_preimage_sub_zero Umeas Wunif Wmeas UWindep]
  congr 3
  exact Nat.card_add_singleton _ _

open Pointwise

section Rusza_set
variable {α : Type*} [CommGroup α]

/-- **Ruzsa's covering lemma**. Version for sets. For finsets,
see `Finset.exists_subset_mul_div`. -/
@[to_additive "**Ruzsa's covering lemma**. Version for sets. For finsets,
see `Finset.exists_subset_add_sub`."]
theorem Set.exists_subset_mul_div {s : Set α} (hs : s.Finite) {t : Set α} (h't : t.Finite)
    (ht : t.Nonempty) :
    ∃ (u : Set α), Nat.card u * Nat.card t ≤ Nat.card (s * t) ∧ s ⊆ u * t / t ∧ u.Finite := by
  classical
  let t' := h't.toFinset
  have : t'.Nonempty := by simpa using ht
  rcases Finset.exists_subset_mul_div hs.toFinset this with ⟨u, u_card, hu⟩
  refine ⟨u, ?_, by simpa [← Finset.coe_subset] using hu, u.finite_toSet⟩
  have : Nat.card t = t'.card := Nat.card_eq_toFinset_card _
  simp [this]
  apply u_card.trans (le_of_eq _)
  rw [← Nat.card_eq_finset_card]
  congr with x
  simp [← Finset.mem_coe, Finset.coe_mul]

end Rusza_set

/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup $H$
such that $A$ can be covered by at most $K^{13/2} #A^{1/2} / #H^{1/2}$ cosets of $H$. -/
theorem PFR_conjecture_aux {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (13/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ (11/2) * Nat.card A ∧ A ⊆ c + H := by
  classical
  obtain ⟨A_pos, AA_pos, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  rcases exists_isUniform_measureSpace A h₀A with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, UAmem⟩
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le h₀A hA UAunif UAmeas
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas⟩
  rcases entropic_PFR_conjecture p with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm (by trivial)
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm (by trivial)
  -- main step: entropic PFR shows that the entropy of `VA - VH` is small
  have I : log K * (-11/2) + log (Nat.card A) * (-1/2) + log (Nat.card (H : Set G)) * (-1/2)
      ≤ - H[VA - VH] := by
    have : d[VA # VH] ≤ 11/2 * log K := by rw [idVA.rdist_eq idVH]; linarith
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    have : H[VA] = log (Nat.card A) := VAunif.entropy_eq
    have : H[VH] = log (Nat.card (H : Set G)) := VHunif.entropy_eq
    linarith
  have IHA : Nat.card H ≤ K ^ (11/2) * Nat.card A := sorry
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _
  have H_pos : (0 : ℝ) < Nat.card (H : Set G) := by
    have : (H : Set G).Nonempty := AddSubgroup.coe_nonempty H
    have : 0 < Nat.card (H : Set G) := Nat.card_pos
    positivity
  -- massage the previous inequality to get that `A ∩ (H + {x₀})` is large
  have J : K ^ (-11/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (1/2) ≤
      Nat.card (A ∩ (H + {x₀}) : Set G) := by
    rw [VAunif.measureReal_preimage_sub VAmeas VHunif VHmeas Vindep] at h₀
    have := (Real.exp_monotone I).trans h₀
    rw [le_div_iff (by positivity)] at this
    convert this using 1
    rw [exp_add, exp_add, ← rpow_def_of_pos K_pos, ← rpow_def_of_pos A_pos, ← rpow_def_of_pos H_pos]
    rpow_ring
    norm_num
  have Hne : Set.Nonempty (A ∩ (H + {x₀} : Set G)) := by
    by_contra h'
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, card_of_isEmpty, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h'] at this
  /- use Rusza covering lemma to cover `A` by few translates of `A ∩ ((H + {x₀}) - A ∩ ((H + {x₀}`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #((A ∩ (H + {x₀})))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  rcases Set.exists_subset_add_sub (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne with
    ⟨u, hu, Au, u_fin⟩
  have Iu : Nat.card u ≤ K ^ (13/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := by
    have : (0 : ℝ) ≤ Nat.card u := by simp
    have Z1 := mul_le_mul_of_nonneg_left J this
    have Z2 : (Nat.card u * Nat.card (A ∩ (H + {x₀}) : Set G) : ℝ)
      ≤ Nat.card (A + A ∩ (↑H + {x₀})) := by norm_cast
    have Z3 : (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ) ≤ K * Nat.card A := by
      apply le_trans _ hA
      simp only [Nat.cast_le]
      apply Nat.card_mono (toFinite _)
      apply add_subset_add_left (inter_subset_left _ _)
    have : 0 ≤ K ^ (11/2) * Nat.card A ^ (-1/2) * Nat.card (H : Set G) ^ (-1/2) := by positivity
    have T := mul_le_mul_of_nonneg_left ((Z1.trans Z2).trans Z3) this
    convert T using 1 <;> rpow_ring <;> norm_num
  have A_subset_uH : A ⊆ u + H := by
    apply Au.trans
    rw [add_sub_assoc]
    apply add_subset_add_left
    apply (sub_subset_sub (inter_subset_right _ _) (inter_subset_right _ _)).trans
    rintro - ⟨-, -, ⟨y, xy, hy, hxy, rfl⟩, ⟨z, xz, hz, hxz, rfl⟩, rfl⟩
    simp at hxy hxz
    simpa [hxy, hxz, -sub_eq_add] using H.sub_mem hy hz
  exact ⟨H, u, Iu, IHA, A_subset_uH⟩

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{12}$ cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry
