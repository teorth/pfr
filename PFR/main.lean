import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement
import PFR.ForMathlib.Set
import PFR.ForMathlib.MonoidHom
import PFR.f2_vec
import PFR.entropy_pfr
import PFR.Tactic.RPowSimp


/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/-!
# Polynomial Freiman-Ruzsa conjecture

Here we prove the polynomial Freiman-Ruzsa conjecture.
-/

open Pointwise ProbabilityTheory MeasureTheory Real Set Fintype Function

open scoped BigOperators

universe u

namespace ProbabilityTheory
variable {G Ω : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] {A B : Set G}
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
  let W : Finset G := (A ∩ B).toFinite.toFinset
  calc
    ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p} ∩ V ⁻¹' {p})
      = ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply sum_congr _ _ (fun g ↦ ?_)
        rw [hindep.measureReal_inter_preimage_eq_mul (measurableSet_discrete _) $
          measurableSet_discrete _]
    _ = ∑ p in W, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply (Finset.sum_subset W.subset_univ _).symm
        intro i _ hi
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

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V + x` with probability `# (A ∩ (B + x)) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub (Uunif : IsUniform A U) (Umeas : Measurable U)
    (Vunif : IsUniform B V) (Vmeas : Measurable V) (hindep : IndepFun U V) (x : G) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {x})
      = Nat.card (A ∩ (B + {x}) : Set G) / (Nat.card A * Nat.card B) := by
  let W := fun ω ↦ V ω + x
  have Wunif : IsUniform (B + {x}) W := by
    have : B + {x} = (Equiv.addRight x) '' B := by simp
    rw [this]
    exact Vunif.comp (Equiv.injective _)
  have Wmeas : Measurable W := Vmeas.add_const _
  have UWindep : IndepFun U W := by
    have : Measurable (fun g ↦ g + x) := measurable_add_const x
    exact hindep.comp measurable_id this
  have : (U - V) ⁻¹' {x} = (U - W) ⁻¹' {0} := by
    ext ω
    simp only [mem_preimage, Pi.add_apply, mem_singleton_iff, Pi.sub_apply, ← sub_eq_zero (b := x)]
    abel_nf
  rw [this, Uunif.measureReal_preimage_sub_zero Umeas Wunif Wmeas UWindep]
  congr 3
  exact Nat.card_add_singleton _ _

end ProbabilityTheory


/-- Record positivity results that are useful in the proof of PFR. -/
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

variable {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G]
  [MeasurableSingletonClass G] {A : Set G} {K : ℝ}

/-- A uniform distribution on a set with doubling constant `K` has self Rusza distance
at most `log K`. -/
theorem rdist_le_of_isUniform_of_card_add_le (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U₀ : Ω → G}
    (U₀unif : IsUniform A U₀) (U₀meas : Measurable U₀) : d[U₀ # U₀] ≤ log K := by
  obtain ⟨A_pos, AA_pos, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  rcases independent_copies_two U₀meas U₀meas with ⟨Ω, mΩ, U, U', hP, hU, hU', UU'_indep, idU, idU'⟩
  have Uunif : IsUniform A U := U₀unif.of_identDistrib idU.symm $ measurableSet_discrete _
  have U'unif : IsUniform A U' := U₀unif.of_identDistrib idU'.symm $ measurableSet_discrete _
  have IU : d[U # U'] ≤ log K := by
    have I : H[U + U'] ≤ log (Nat.card (A + A)) := by
      apply entropy_le_log_card_of_mem (hU.add hU')
      filter_upwards [Uunif.ae_mem, U'unif.ae_mem] with ω h1 h2
      exact Set.add_mem_add h1 h2
    have J : log (Nat.card (A + A)) ≤ log K + log (Nat.card A) := by
      apply (log_le_log' AA_pos hA).trans (le_of_eq _)
      rw [log_mul K_pos.ne' A_pos.ne']
    have : H[U + U'] = H[U - U'] := by congr; simp
    rw [UU'_indep.rdist_eq hU hU', Uunif.entropy_eq hU, U'unif.entropy_eq hU', ← this]
    linarith
  rwa [idU.rdist_eq idU'] at IU


/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup $H$
such that $A$ can be covered by at most $K^{13/2} |A|^{1/2} / |H|^{1/2}$ cosets of $H$, and $H$ has
the same cardinality as $A$ up to a multiplicative factor $K^11$. -/
lemma PFR_conjecture_aux (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (13/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ 11 * Nat.card A ∧ Nat.card A ≤ K ^ 11 * Nat.card H ∧ A ⊆ c + H := by
  classical
  let mG : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨λ _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  rcases exists_isUniform_measureSpace A h₀A with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -⟩
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le h₀A hA UAunif UAmeas
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas⟩
  -- entropic PFR gives a subgroup `H` which is close to `A` for the Rusza distance
  rcases entropic_PFR_conjecture p with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm $ measurableSet_discrete _
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm $ measurableSet_discrete _
  have : d[VA # VH] ≤ 11/2 * log K := by rw [idVA.rdist_eq idVH]; linarith
  have H_pos : (0 : ℝ) < Nat.card (H : Set G) := by
    have : 0 < Nat.card (H : Set G) := Nat.card_pos
    positivity
  have Icard : |log (Nat.card A) - log (Nat.card (H : Set G))| ≤ 11 * log K := by
    rw [← VAunif.entropy_eq VAmeas, ← VHunif.entropy_eq VHmeas]
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
    have : H[VA] = log (Nat.card A) := VAunif.entropy_eq VAmeas
    have : H[VH] = log (Nat.card (H : Set G)) := VHunif.entropy_eq VHmeas
    linarith
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
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
    apply Au.trans
    rw [add_sub_assoc]
    apply add_subset_add_left
    apply (sub_subset_sub (inter_subset_right _ _) (inter_subset_right _ _)).trans
    rintro - ⟨-, -, ⟨y, xy, hy, hxy, rfl⟩, ⟨z, xz, hz, hxz, rfl⟩, rfl⟩
    simp only [mem_singleton_iff] at hxy hxz
    simpa [hxy, hxz, -ElementaryAddCommGroup.sub_eq_add] using H.sub_mem hy hz
  exact ⟨H, u, Iu, IHA, IAH, A_subset_uH⟩


/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{12}$ cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
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
      have A_pos' : 0 < Nat.card A := by exact_mod_cast A_pos
      exact ElementaryAddCommGroup.exists_subgroup_subset_card_le H h.le A_pos'.ne'
    have : (Nat.card A / 2 : ℝ) < Nat.card (H' : Set G) := by
      rw [div_lt_iff zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < Nat.card (H' : Set G) := by
      have : 0 < Nat.card (H' : Set G) := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ : ∃ (u : Set G), u + (H' : Set G) = H
        ∧ Nat.card u * Nat.card (H' : Set G) = Nat.card (H : Set G) :=
      AddSubgroup.exists_add_eq_addSubgroup_of_le H'H
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := by norm_cast; exact Nat.card_add_le _ _
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
  have cardA' : Nat.card A' = Nat.card A := ι_inj.nat_card_preimage Afin A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', preimage_add_preimage ι_inj A_rg A_rg,
         ι_inj.nat_card_preimage (Afin.add Afin) (add_subset_range A_rg A_rg)]
  rcases PFR_conjecture (h₀A.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  use AddSubgroup.map ι H', ι '' c', ?_, ?_, ?_, ?_
  · intro x hx
    erw [← image_add]
    exact ⟨⟨x, AddSubgroup.subset_closure hx⟩, hH'₂ hx, rfl⟩
  · exact toFinite (ι '' c')
  · exact toFinite (ι '' H')
  · rwa [nat_card_image_of_injective ι_inj (toFinite c')]
  · erw [nat_card_image_of_injective ι_inj, ← cardA']
    exacts [hH', toFinite (H' : Set G')]
