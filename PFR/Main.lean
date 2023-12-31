import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.OrderOfElement
import PFR.Mathlib.GroupTheory.Subgroup.Pointwise
import PFR.Tactic.RPowSimp
import PFR.EntropyPFR

/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/-!
# Polynomial Freiman-Ruzsa conjecture

Here we prove the polynomial Freiman-Ruzsa conjecture.
-/

open ProbabilityTheory MeasureTheory Real Set Fintype Function
open scoped BigOperators Pointwise

universe u

namespace ProbabilityTheory
variable {G Ω : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] {A B : Finset G}
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U V : Ω → G}

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V` with probability `# (A ∩ B) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub_zero (Uunif : IsUniform A U) (Umeas : Measurable U)
    (Vunif : IsUniform B V) (Vmeas : Measurable V) (hindep : IndepFun U V) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {0})
      = Nat.card (A ∩ B : Set G) / (Nat.card A * Nat.card B) := by
  have : (U - V) ⁻¹' {0} = ⋃ (g : G), (U ⁻¹' {g} ∩ V⁻¹' {g}) := by
    ext ω; simp [sub_eq_zero, eq_comm]
  rw [this, measureReal_iUnion_fintype _
    (fun i ↦ (Umeas $ measurableSet_discrete _).inter $ Vmeas $ measurableSet_discrete _)]; swap
  · intro g g' hgg'
    apply Set.disjoint_iff_inter_eq_empty.2
    ext a
    simp (config := {contextual := True}) [hgg']
  classical
  let W : Finset G := A ∩ B
  calc
    ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p} ∩ V ⁻¹' {p})
      = ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply sum_congr _ _ (fun g ↦ ?_)
        rw [hindep.measureReal_inter_preimage_eq_mul (measurableSet_discrete _) $
          measurableSet_discrete _]
    _ = ∑ p in W, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply (Finset.sum_subset W.subset_univ _).symm
        intro i _ hi
        replace hi : i ∉ A ∨ i ∉ B := by simp at hi; tauto
        rcases hi with h'i|h'i
        · simp [Uunif.measureReal_preimage_of_nmem h'i]
        · simp [Vunif.measureReal_preimage_of_nmem h'i]
    _ = ∑ p in W, (1 / Nat.card A : ℝ) * (1 / Nat.card B) := by
        apply Finset.sum_congr rfl (fun i hi ↦ ?_)
        replace hi : i ∈ A ∧ i ∈ B := by simpa using hi
        rw [Uunif.measureReal_preimage_of_mem (by trivial) hi.1,
            Vunif.measureReal_preimage_of_mem (by trivial) hi.2]
    _ = (W.card : ℝ) / (Nat.card A * Nat.card B) := by simp [div_eq_inv_mul]; ring
    _ = Nat.card (A ∩ B : Set G) / (Nat.card A * Nat.card B) := by
        congr
        rw [← Finset.coe_inter, Nat.card_eq_fintype_card, Fintype.card_ofFinset]
        simp

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V + x` with probability `# (A ∩ (B + x)) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub (Uunif : IsUniform A U) (Umeas : Measurable U)
    (Vunif : IsUniform B V) (Vmeas : Measurable V) (hindep : IndepFun U V) (x : G) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {x})
      = Nat.card (A ∩ (B + {x}) : Set G) / (Nat.card A * Nat.card B) := by
  classical
  let W := fun ω ↦ V ω + x
  have Wunif : IsUniform (B + {x} : Set G) W := by
    convert Vunif.comp (add_left_injective x)
    simp
  have Wmeas : Measurable W := Vmeas.add_const _
  have UWindep : IndepFun U W := by
    have : Measurable (fun g ↦ g + x) := measurable_add_const x
    exact hindep.comp measurable_id this
  have : (U - V) ⁻¹' {x} = (U - W) ⁻¹' {0} := by
    ext ω
    simp only [mem_preimage, Pi.add_apply, mem_singleton_iff, Pi.sub_apply, ← sub_eq_zero (b := x)]
    abel_nf
  have h : (B:Set G)+{x} = (B+{x}:Finset G) := by simp
  rw [h] at Wunif
  rw [this, Uunif.measureReal_preimage_sub_zero Umeas Wunif Wmeas UWindep]
  congr 3
  . rw [add_singleton]; simp
  convert Finset.card_vadd_finset (AddOpposite.op x) B
  . simp
  simp

end ProbabilityTheory


/-- Record positivity results that are useful in the proof of PFR. -/
lemma PFR_conjecture_pos_aux {G : Type*} [AddCommGroup G] {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A - A) ≤ K * Nat.card A) :
    (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A - A) ∧ 0 < K := by
  have card_AA_pos : (0 : ℝ) < Nat.card (A - A) := by
    have : Nonempty (A - A) := Set.nonempty_coe_sort.mpr (Set.Nonempty.sub h₀A h₀A)
    have : Finite (A - A) := finite_coe_iff.mpr (Finite.image2 _ (Set.toFinite A) (Set.toFinite A))
    simp [Nat.cast_pos, Nat.card_pos_iff]
  have KA_pos : 0 < K ∧ (0 : ℝ) < Nat.card A := by
    have I : ¬ ((Nat.card A : ℝ) < 0) := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hA)
  exact ⟨KA_pos.2, card_AA_pos, KA_pos.1⟩

lemma PFR_conjecture_pos_aux' {G : Type*} [AddCommGroup G] {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K := by
  have card_AA_pos : (0 : ℝ) < Nat.card (A + A) := by
    have : Nonempty (A + A) := Set.nonempty_coe_sort.mpr (Set.Nonempty.add h₀A h₀A)
    have : Finite (A + A) := finite_coe_iff.mpr (Finite.image2 _ (Set.toFinite A) (Set.toFinite A))
    simp [Nat.cast_pos, Nat.card_pos_iff]
  have KA_pos : 0 < K ∧ (0 : ℝ) < Nat.card A := by
    have I : ¬ ((Nat.card A : ℝ) < 0) := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hA)
  exact ⟨KA_pos.2, card_AA_pos, KA_pos.1⟩

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  [MeasurableSingletonClass G] {A : Set G} [Finite A] {K : ℝ} [Countable G]

/-- A uniform distribution on a set with doubling constant `K` has self Rusza distance
at most `log K`. -/
theorem rdist_le_of_isUniform_of_card_add_le (h₀A : A.Nonempty) (hA : Nat.card (A - A) ≤ K * Nat.card A)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U₀ : Ω → G}
    (U₀unif : IsUniform A U₀) (U₀meas : Measurable U₀) : d[U₀ # U₀] ≤ log K := by
  obtain ⟨A_pos, AA_pos, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A - A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  rcases independent_copies_two U₀meas U₀meas with ⟨Ω, mΩ, U, U', hP, hU, hU', UU'_indep, idU, idU'⟩
  have Uunif : IsUniform A U := U₀unif.of_identDistrib idU.symm $ measurableSet_discrete _
  have U'unif : IsUniform A U' := U₀unif.of_identDistrib idU'.symm $ measurableSet_discrete _
  have IU : d[U # U'] ≤ log K := by
    have I : H[U - U'] ≤ log (Nat.card (A - A)) := by
      convert entropy_le_log_card_of_mem (A := (A-A).toFinite.toFinset) ?_ ?_ with x
      . simp
        exact Iff.rfl
      . measurability
      filter_upwards [Uunif.ae_mem, U'unif.ae_mem] with ω h1 h2
      simp
      exact Set.sub_mem_sub h1 h2
    have J : log (Nat.card (A - A)) ≤ log K + log (Nat.card A) := by
      apply (log_le_log AA_pos hA).trans (le_of_eq _)
      rw [log_mul K_pos.ne' A_pos.ne']
--    have : H[U + U'] = H[U - U'] := by congr; simp
    rw [UU'_indep.rdist_eq hU hU', IsUniform.entropy_eq' Uunif hU, IsUniform.entropy_eq' U'unif hU']
    linarith
  rwa [idU.rdist_eq idU'] at IU

variable [ElementaryAddCommGroup G 2] [Fintype G]

/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup $H$
such that $A$ can be covered by at most $K^{13/2} |A|^{1/2} / |H|^{1/2}$ cosets of $H$, and $H$ has
the same cardinality as $A$ up to a multiplicative factor $K^11$. -/
lemma PFR_conjecture_aux (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (13/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ 11 * Nat.card A ∧ Nat.card A ≤ K ^ 11 * Nat.card H ∧ A ⊆ c + H := by
  classical
  let _mG : MeasurableSpace G := ⊤
  have hadd_sub : A + A = A - A := by
    rw [← Set.image2_add, ← Set.image2_sub]
    congr! 1 with a _ b _
    rw [(show a+b=a-b by simp)]
    rfl
  rw [hadd_sub] at hA
  have : MeasurableSingletonClass G := ⟨λ _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A - A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  let A' := A.toFinite.toFinset
  have h₀A' : Finset.Nonempty A' := by
    simp [Finset.Nonempty]
    exact h₀A
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' h₀A' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -, -⟩
  rw [hAA'] at UAunif
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le h₀A hA UAunif UAmeas
  rw [← hadd_sub] at hA
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas, 1/9, (by norm_num), (by norm_num)⟩
  -- entropic PFR gives a subgroup `H` which is close to `A` for the Rusza distance
  rcases entropic_PFR_conjecture p (by norm_num) with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm $ measurableSet_discrete _
  have VA'unif := VAunif
  rw [← hAA'] at VA'unif
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm $ measurableSet_discrete _
  let H' := (H:Set G).toFinite.toFinset
  have hHH' : H' = (H:Set G) := Finite.coe_toFinset (toFinite (H:Set G))
  have VH'unif := VHunif
  rw [← hHH'] at VH'unif

  have : d[VA # VH] ≤ 11/2 * log K := by rw [idVA.rdist_eq idVH]; linarith
  have H_pos : (0 : ℝ) < Nat.card (H : Set G) := by
    have : 0 < Nat.card (H : Set G) := Nat.card_pos
    positivity
  have VA_ent : H[VA] = log (Nat.card A) := IsUniform.entropy_eq' VAunif VAmeas
  have VH_ent : H[VH] = log (Nat.card (H : Set G)) := IsUniform.entropy_eq' VHunif VHmeas
  have Icard : |log (Nat.card A) - log (Nat.card (H : Set G))| ≤ 11 * log K := by
    rw [← VA_ent, ← VH_ent]
    apply (diff_ent_le_rdist VAmeas VHmeas).trans
    linarith
  have IAH : Nat.card A ≤ K ^ 11 * Nat.card (H : Set G) := by
    have : log (Nat.card A) ≤ log K * 11 + log (Nat.card (H : Set G)) := by
      linarith [(le_abs_self _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log A_pos).symm
    · rw [exp_add, exp_log H_pos, ← rpow_def_of_pos K_pos]
  have IHA : Nat.card (H : Set G) ≤ K ^ 11 * Nat.card A := by
    have : log (Nat.card (H : Set G)) ≤ log K * 11 + log (Nat.card A) := by
      linarith [(neg_le_abs_self _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log H_pos).symm
    · rw [exp_add, exp_log A_pos, ← rpow_def_of_pos K_pos]
  -- entropic PFR shows that the entropy of `VA - VH` is small
  have I : log K * (-11/2) + log (Nat.card A) * (-1/2) + log (Nat.card (H : Set G)) * (-1/2)
      ≤ - H[VA - VH] := by
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    have : H[VA] = log (Nat.card A) := IsUniform.entropy_eq' VAunif VAmeas
    have : H[VH] = log (Nat.card (H : Set G)) := IsUniform.entropy_eq' VHunif VHmeas
    linarith
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
  -- massage the previous inequality to get that `A ∩ (H + {x₀})` is large
  have J : K ^ (-11/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (1/2) ≤
      Nat.card (A ∩ (H + {x₀}) : Set G) := by
    rw [VA'unif.measureReal_preimage_sub VAmeas VH'unif VHmeas Vindep] at h₀
    have := (Real.exp_monotone I).trans h₀
    have hAA'_card : Nat.card A' = Nat.card A := congrArg Nat.card (congrArg Subtype hAA')
    have hHH'_card : Nat.card H' = Nat.card (H : Set G) := congrArg Nat.card (congrArg Subtype hHH')
    rw [hAA'_card, hHH'_card, le_div_iff] at this
    convert this using 1
    . rw [exp_add, exp_add, ← rpow_def_of_pos K_pos, ← rpow_def_of_pos A_pos, ← rpow_def_of_pos H_pos]
      rpow_ring
      norm_num
    . rw [hAA', hHH']
    positivity

  have Hne : Set.Nonempty (A ∩ (H + {x₀} : Set G)) := by
    by_contra h'
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, card_of_isEmpty, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h'] at this
  /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  rcases Set.exists_subset_add_sub (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne with
    ⟨u, hu, Au, -⟩
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
    rw [add_sub_assoc] at Au
    refine Au.trans $ add_subset_add_left $
      (sub_subset_sub (inter_subset_right ..) (inter_subset_right ..)).trans ?_
    rw [add_sub_add_comm, singleton_sub_singleton, sub_self]
    simp
  exact ⟨H, u, Iu, IHA, IAH, A_subset_uH⟩


/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{12}$ cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' h₀A hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (13/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card (H : Set G) ≤ K ^ 11 * Nat.card A ∧ Nat.card A ≤ K ^ 11 * Nat.card (H : Set G)
      ∧ A ⊆ c + H :=
    PFR_conjecture_aux h₀A hA
  have H_pos : (0 : ℝ) < Nat.card (H : Set G) := by
    have : 0 < Nat.card (H : Set G) := Nat.card_pos; positivity
  rcases le_or_lt (Nat.card (H : Set G)) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ (13/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := hc
    _ ≤ K ^ (13/2) * (K ^ 11 * Nat.card (H : Set G)) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := by
      gcongr
    _ = K ^ 12 := by rpow_ring; norm_num
    _ < 2 * K ^ 12 := by linarith [show 0 < K ^ 12 by positivity]
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / 2 < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : AddSubgroup G, Nat.card (H' : Set G) ≤ Nat.card A
          ∧ Nat.card A < 2 * Nat.card (H' : Set G) ∧ H' ≤ H := by
      have A_pos' : 0 < Nat.card A := mod_cast A_pos
      exact ElementaryAddCommGroup.exists_subgroup_subset_card_le Nat.prime_two H h.le A_pos'.ne'
    have : (Nat.card A / 2 : ℝ) < Nat.card (H' : Set G) := by
      rw [div_lt_iff zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < Nat.card (H' : Set G) := by
      have : 0 < Nat.card (H' : Set G) := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ := AddSubgroup.exists_left_transversal_of_le H'H
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast card_add_le
    _ ≤ (K ^ (13/2) * (Nat.card A) ^ (1 / 2) * (Nat.card (H : Set G) ^ (-1 / 2)))
          * (Nat.card (H : Set G) / Nat.card (H' : Set G)) := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ (13/2) * (Nat.card A) ^ (1 / 2) * (Nat.card (H : Set G) ^ (-1 / 2)))
          * (Nat.card (H : Set G) / (Nat.card A / 2)) := by
        gcongr
    _ = 2 * K ^ (13/2) * (Nat.card A) ^ (-1/2) * (Nat.card (H : Set G)) ^ (1/2) := by
        have : (0 : ℝ) < Nat.card H := H_pos
        field_simp
        rpow_ring
        norm_num
    _ ≤ 2 * K ^ (13/2) * (Nat.card A) ^ (-1/2) * (K ^ 11 * Nat.card A) ^ (1/2) := by
        gcongr
    _ = 2 * K ^ 12 := by
        rpow_ring
        norm_num

/-- Corollary of `PFR_conjecture` in which the ambient group is not required to be finite (but) then
$H$ and $c$ are finite. -/
theorem PFR_conjecture' {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  let G' := AddSubgroup.closure A
  let G'fin : Fintype G' := by
    exact Finite.fintype (ElementaryAddCommGroup.finite_closure Afin)
  have G'Elem : ElementaryAddCommGroup G' 2 := ElementaryAddCommGroup.subgroup _
  let ι : G'→+ G := G'.subtype
  have ι_inj : Injective ι := AddSubgroup.subtype_injective G'
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι := by simpa using AddSubgroup.subset_closure
  have cardA' : Nat.card A' = Nat.card A := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
         Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
  rcases PFR_conjecture (h₀A.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  refine ⟨AddSubgroup.map ι H', ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · erw [Nat.card_image_of_injective ι_inj, ← cardA']
    exact hH'
  · erw [← image_add]
    exact ⟨⟨x, AddSubgroup.subset_closure hx⟩, hH'₂ hx, rfl⟩
