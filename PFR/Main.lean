import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.GroupTheory.Complement
import PFR.EntropyPFR
import PFR.Tactic.RPowSimp

/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/-!
# Polynomial Freiman-Ruzsa conjecture

Here we prove the polynomial Freiman-Ruzsa conjecture.
-/

open ProbabilityTheory MeasureTheory Real Set Fintype Function
open scoped Pointwise

universe u

namespace ProbabilityTheory
variable {G Ω : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] {A B : Finset G}
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U V : Ω → G}

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V` with probability `#(A ∩ B) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub_zero [DecidableEq G] (Uunif : IsUniform A U)
    (Umeas : Measurable U) (Vunif : IsUniform B V) (Vmeas : Measurable V) (h_indep : IndepFun U V) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {0})
      = (A ∩ B).card / (A.card * B.card) := by
  have : (U - V) ⁻¹' {0} = ⋃ (g : G), (U ⁻¹' {g} ∩ V⁻¹' {g}) := by
    ext ω; simp [sub_eq_zero, eq_comm]
  rw [this, measureReal_iUnion_fintype _
    (fun i ↦ (Umeas .of_discrete).inter $ Vmeas .of_discrete)]; swap
  · intro g g' hgg'
    apply Set.disjoint_iff_inter_eq_empty.2
    ext a
    simp (config := {contextual := True}) [hgg']
  let W : Finset G := A ∩ B
  calc
    ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p} ∩ V ⁻¹' {p})
      = ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply sum_congr _ _ (fun g ↦ ?_)
        rw [h_indep.measureReal_inter_preimage_eq_mul .of_discrete .of_discrete]
    _ = ∑ p ∈ W, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply (Finset.sum_subset W.subset_univ _).symm
        intro i _ hi
        obtain hi | hi : i ∉ A ∨ i ∉ B := by simpa [or_iff_not_imp_left, W] using hi
        · simp [Uunif.measureReal_preimage_of_nmem hi]
        · simp [Vunif.measureReal_preimage_of_nmem hi]
    _ = ∑ p ∈ W, (1 / A.card : ℝ) * (1 / B.card) := by
        congr! 1 with i hi
        replace hi : i ∈ A ∧ i ∈ B := by simpa [W] using hi
        rw [Uunif.measureReal_preimage_of_mem (by trivial) hi.1,
            Vunif.measureReal_preimage_of_mem (by trivial) hi.2]
    _ = (W.card : ℝ) / (A.card * B.card) := by simp [div_eq_inv_mul]; ring

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V + x` with probability `# (A ∩ (B + x)) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub [DecidableEq G] (Uunif : IsUniform A U)
    (Umeas : Measurable U) (Vunif : IsUniform B V) (Vmeas : Measurable V) (h_indep : IndepFun U V)
    (x : G) : (ℙ : Measure Ω).real ((U - V) ⁻¹' {x}) = (A ∩ (B + {x})).card / (A.card * B.card) := by
  classical
  let W := fun ω ↦ V ω + x
  have Wunif : IsUniform (B + {x} : Set G) W := by
    convert Vunif.comp (add_left_injective x)
    simp
  have Wmeas : Measurable W := Vmeas.add_const _
  have UWindep : IndepFun U W := by
    have : Measurable (fun g ↦ g + x) := measurable_add_const x
    exact h_indep.comp measurable_id this
  have : (U - V) ⁻¹' {x} = (U - W) ⁻¹' {0} := by
    ext ω
    simp [W, ← sub_eq_zero (b := x)]
    abel_nf
  have h : (B : Set G)+{x} = (B+{x}:Finset G) := by simp
  rw [h] at Wunif
  simp [this, Uunif.measureReal_preimage_sub_zero Umeas Wunif Wmeas UWindep]

end ProbabilityTheory


/-- Record positivity results that are useful in the proof of PFR. -/
lemma PFR_conjecture_pos_aux {G : Type*} [AddCommGroup G] {A : Set G} (hA : A.Finite) {K : ℝ}
    (hA₀ : A.Nonempty) (hAK : (A - A).ncard ≤ K * A.ncard) :
    (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A - A).ncard ∧ 0 < K := by
  have card_AA_pos : (0 : ℝ) < (A - A).ncard := by simpa [Set.ncard_pos (hA.sub hA)]
  have KA_pos : 0 < K ∧ (0 : ℝ) < A.ncard := by
    have I : ¬ (A.ncard : ℝ) < 0 := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hAK)
  exact ⟨KA_pos.2, card_AA_pos, KA_pos.1⟩

lemma PFR_conjecture_pos_aux' {G : Type*} [AddCommGroup G] {A : Set G} (hA : A.Finite) {K : ℝ}
    (hA₀ : A.Nonempty) (hAK : (A + A).ncard ≤ K * A.ncard) :
    (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A + A).ncard ∧ 0 < K := by
  have card_AA_pos : (0 : ℝ) < (A + A).ncard := by simpa [Set.ncard_pos (hA.add hA)]
  have KA_pos : 0 < K ∧ (0 : ℝ) < A.ncard := by
    have I : ¬ (A.ncard : ℝ) < 0 := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hAK)
  exact ⟨KA_pos.2, card_AA_pos, KA_pos.1⟩

variable {G : Type*} [AddCommGroup G] {A : Set G} {K : ℝ} [Countable G]

/-- A uniform distribution on a set with doubling constant `K` has self Rusza distance
at most `log K`. -/
theorem rdist_le_of_isUniform_of_card_add_le [A_fin : Finite A] [MeasurableSpace G]
    [MeasurableSingletonClass G]
    (hA₀ : A.Nonempty) (hA : (A - A).ncard ≤ K * A.ncard)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U₀ : Ω → G}
    (U₀unif : IsUniform A U₀) (U₀meas : Measurable U₀) : d[U₀ # U₀] ≤ log K := by
  obtain ⟨A_pos, AA_pos, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A - A).ncard ∧ 0 < K :=
    PFR_conjecture_pos_aux A.toFinite hA₀ hA
  rcases independent_copies_two U₀meas U₀meas with ⟨Ω, mΩ, U, U', hP, hU, hU', UU'_indep, idU, idU'⟩
  have Uunif : IsUniform A U := U₀unif.of_identDistrib idU.symm .of_discrete
  have U'unif : IsUniform A U' := U₀unif.of_identDistrib idU'.symm .of_discrete
  have IU : d[U # U'] ≤ log K := by
    have I : H[U - U'] ≤ log (A - A).ncard := by
      apply entropy_le_log_card_of_mem_finite (Set.Finite.sub A_fin A_fin) (hU.sub hU')
      filter_upwards [Uunif.ae_mem, U'unif.ae_mem] with ω h1 h2
      exact Set.sub_mem_sub h1 h2
    have J : log (A - A).ncard ≤ log K + log A.ncard := by
      rw [← log_mul K_pos.ne' A_pos.ne']; gcongr
    rw [UU'_indep.rdist_eq hU hU', Uunif.entropy_eq' A_fin hU, U'unif.entropy_eq' A_fin hU']
    linarith
  rwa [idU.rdist_congr idU'] at IU

variable [Module (ZMod 2) G] [Fintype G]

lemma sumset_eq_sub {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] (A : Set G) :
    A + A = A - A := by
  rw [← Set.image2_add, ← Set.image2_sub]
  congr! 1 with a _ b _
  show a + b = a - b
  simp [ZModModule.sub_eq_add]

/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if `A` is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup `H`
such that `A` can be covered by at most `K^(13/2) |A|^(1/2) / |H|^(1/2)` cosets of `H`, and `H` has
the same cardinality as `A` up to a multiplicative factor `K^11`. -/
lemma PFR_conjecture_aux (hA₀ : A.Nonempty) (hA : (A + A).ncard ≤ K * A.ncard) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)
      ∧ (H : Set G).ncard ≤ K ^ 11 * A.ncard ∧ A.ncard ≤ K ^ 11 * (H : Set G).ncard ∧ A ⊆ c + H := by
  classical
  have A_fin : Finite A := by infer_instance
  let _mG : MeasurableSpace G := ⊤
  rw [sumset_eq_sub] at hA
  have : MeasurableSingletonClass G := ⟨λ _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A - A).ncard ∧ 0 < K :=
    PFR_conjecture_pos_aux A.toFinite hA₀ hA
  let A' := A.toFinite.toFinset
  have hA₀' : Finset.Nonempty A' := by simpa [Finset.Nonempty, A'] using hA₀
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' hA₀' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -, -⟩
  rw [hAA'] at UAunif
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le hA₀ hA UAunif UAmeas
  rw [← sumset_eq_sub] at hA
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas, 1/9, (by norm_num), (by norm_num)⟩
  -- entropic PFR gives a subgroup `H` which is close to `A` for the Rusza distance
  rcases entropic_PFR_conjecture p (by norm_num) with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  have H_fin : (H : Set G).Finite := (H : Set G).toFinite
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm .of_discrete
  have VA'unif := VAunif
  rw [← hAA'] at VA'unif
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm .of_discrete
  let H' := (H : Set G).toFinite.toFinset
  have hHH' : H' = (H : Set G) := (toFinite (H : Set G)).coe_toFinset
  have VH'unif := VHunif
  rw [← hHH'] at VH'unif

  have : d[VA # VH] ≤ 11/2 * log K := by rw [idVA.rdist_congr idVH]; linarith
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos
    positivity
  have VA_ent : H[VA] = log A.ncard := VAunif.entropy_eq' A_fin VAmeas
  have VH_ent : H[VH] = log (H : Set G).ncard := VHunif.entropy_eq' H_fin VHmeas
  have Icard : |log A.ncard - log (H : Set G).ncard| ≤ 11 * log K := by
    rw [← VA_ent, ← VH_ent]
    apply (diff_ent_le_rdist VAmeas VHmeas).trans
    linarith
  have IAH : A.ncard ≤ K ^ 11 * (H : Set G).ncard := by
    have : log A.ncard ≤ log K * 11 + log (H : Set G).ncard := by
      linarith [(le_abs_self _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log A_pos).symm
    · rw [exp_add, exp_log H_pos, ← rpow_def_of_pos K_pos]
  have IHA : (H : Set G).ncard ≤ K ^ 11 * A.ncard := by
    have : log (H : Set G).ncard ≤ log K * 11 + log A.ncard := by
      linarith [(neg_le_abs _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log H_pos).symm
    · rw [exp_add, exp_log A_pos, ← rpow_def_of_pos K_pos]
  -- entropic PFR shows that the entropy of `VA - VH` is small
  have I : log K * (-11/2) + log A.ncard * (-1/2) + log (H : Set G).ncard * (-1/2)
      ≤ - H[VA - VH] := by
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    linarith
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
  -- massage the previous inequality to get that `A ∩ (H + {x₀})` is large
  have J : K ^ (-11/2 : ℝ) * A.ncard ^ (1/2) * (H : Set G).ncard ^ (1/2 : ℝ) ≤
      (A ∩ (H + {x₀}) : Set G).ncard := by
    rw [VA'unif.measureReal_preimage_sub VAmeas VH'unif VHmeas Vindep] at h₀
    have := (Real.exp_monotone I).trans h₀
    have hAA'_card : A'.card  = A.ncard := by simp [← hAA']
    have hHH'_card : H'.card = (H : Set G).ncard := by simp [← hHH']
    rw [hAA'_card, hHH'_card, le_div_iff₀ (by positivity)] at this
    convert this using 1
    · rw [exp_add, exp_add, ← rpow_def_of_pos K_pos, ← rpow_def_of_pos A_pos,
        ← rpow_def_of_pos H_pos]
      rpow_ring
      norm_num
    · simp [← Set.ncard_coe_finset, hAA', hHH', -add_singleton]

  have Hne : (A ∩ (H + {x₀} : Set G)).Nonempty := by
    by_contra h'
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, card_of_isEmpty, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h'] at this
  /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  have Z3 :
      ((A + A ∩ (↑H + {x₀})).ncard : ℝ) ≤ (K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) *
        (H : Set G).ncard ^ (-1/2 : ℝ)) * (A ∩ (↑H + {x₀})).ncard := by
    calc
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ)
      _ ≤ (A + A).ncard := by
        gcongr; exact Nat.card_mono (toFinite _) <| add_subset_add_left inter_subset_left
      _ ≤ K * A.ncard := hA
      _ = (K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
          (K ^ (-11/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (1/2 : ℝ)) := by
        rpow_ring; norm_num
      _ ≤ (K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
        (A ∩ (↑H + {x₀})).ncard := by gcongr
  obtain ⟨u, huA, hucard, hAu, -⟩ :=
    Set.ruzsa_covering_add (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne (by convert Z3)
  have A_subset_uH : A ⊆ u + H := by
    refine hAu.trans $ add_subset_add_left $
      (sub_subset_sub (inter_subset_right ..) (inter_subset_right ..)).trans ?_
    rw [add_sub_add_comm, singleton_sub_singleton, sub_self]
    simp
  exact ⟨H, u, hucard, IHA, IAH, A_subset_uH⟩

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if `A` is a subset of an elementary abelian
2-group of doubling constant at most `K`, then `A` can be covered by at most `2 * K ^ 12` cosets of
a subgroup of cardinality at most `|A|`. -/
theorem PFR_conjecture (hA₀ : A.Nonempty) (hA : (A + A).ncard ≤ K * A.ncard) :
     ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c < 2 * K ^ 12 ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A + A).ncard ∧ 0 < K :=
    PFR_conjecture_pos_aux' A.toFinite hA₀ hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ (13/2) * A.ncard ^ (1/2) * (H : Set G).ncard ^ (-1/2)
      ∧ (H : Set G).ncard ≤ K ^ 11 * A.ncard ∧ A.ncard ≤ K ^ 11 * (H : Set G).ncard
      ∧ A ⊆ c + H :=
    PFR_conjecture_aux hA₀ hA
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos; positivity
  rcases le_or_gt ((H : Set G).ncard) A.ncard with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ) := hc
    _ ≤ K ^ (13/2 : ℝ) * (K ^ 11 * (H : Set G).ncard) ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ) := by gcongr
    _ = K ^ 12 := by rpow_ring; norm_num
    _ < 2 * K ^ 12 := by linarith [show 0 < K ^ 12 by positivity]
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / 2 < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : Submodule (ZMod 2) G, Nat.card H' ≤ A.ncard
          ∧ A.ncard < 2 * Nat.card H' ∧ H' ≤ H := by
      have A_pos' : 0 < A.ncard := mod_cast A_pos
      exact ZModModule.exists_submodule_subset_card_le Nat.prime_two H h.le A_pos'.ne'
    have : (A.ncard / 2 : ℝ) < Nat.card H' := by
      rw [div_lt_iff₀ zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < Nat.card H' := by
      have : 0 < Nat.card H' := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ :=
      H'.toAddSubgroup.exists_left_transversal_of_le (H := H.toAddSubgroup) H'H
    dsimp at HH'u
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast natCard_add_le
    _ ≤ (K ^ (13/2 : ℝ) * A.ncard ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard / Nat.card H') := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ (13/2) * A.ncard ^ (1 / 2) * ((H : Set G).ncard ^ (-1 / 2)))
          * ((H : Set G).ncard / (A.ncard / 2)) := by
        gcongr
    _ = 2 * K ^ (13/2) * A.ncard ^ (-1/2) * (H : Set G).ncard ^ (1/2) := by
        field_simp
        rpow_ring
        norm_num
    _ ≤ 2 * K ^ (13/2) * A.ncard ^ (-1/2) * (K ^ 11 * A.ncard) ^ (1/2) := by
        gcongr
    _ = 2 * K ^ 12 := by
        rpow_ring
        norm_num

/-- Corollary of `PFR_conjecture` in which the ambient group is not required to be finite (but) then
`H` and `c` are finite. -/
theorem PFR_conjecture' {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} {K : ℝ} (hA₀ : A.Nonempty) (Afin : A.Finite)
    (hA : (A + A).ncard ≤ K * A.ncard) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := by
  let G' := Submodule.span (ZMod 2) A
  let G'fin : Fintype G' := (Afin.submoduleSpan _).fintype
  let ι : G'→ₗ[ZMod 2] G := G'.subtype
  have ι_inj : Injective ι := G'.toAddSubgroup.subtype_injective
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι := by simp [G', ι]
  have cardA' : Nat.card A' = A.ncard := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
         Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
  rcases PFR_conjecture (hA₀.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  refine ⟨H'.map ι , ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · simpa [Set.ncard_image_of_injective _ ι_inj, ← cardA']
  · erw [← image_add]
    exact ⟨⟨x, Submodule.subset_span hx⟩, hH'₂ hx, rfl⟩
