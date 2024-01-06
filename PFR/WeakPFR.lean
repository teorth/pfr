import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Quotient
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.FreeModule.PID
import PFR.Mathlib.Data.Set.Pointwise.SMul
import PFR.EntropyPFR
import PFR.ForMathlib.Entropy.RuzsaSetDist
import PFR.Mathlib.GroupTheory.Torsion

/-!
# Weak PFR over the integers

Here we use the entropic form of PFR to deduce a weak form of PFR over the integers.

## Main statement

* `weak_PFR_int` : Let $A\subseteq \mathbb{Z}^d$ and $\lvert A+A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-44}\lvert A\rvert$ and $\dim A' \leq 60\log K$.

-/

section AddCommGroup
variable {G : Type*} [AddCommGroup G] {A B : Set G}

open Set
open scoped Pointwise

def IsShift (A B : Set G) : Prop := ∃ x : G, A = x +ᵥ B

lemma IsShift.sub_self_congr : IsShift A B → A - A = B - B := by
  rintro ⟨x, rfl⟩; simp [vadd_sub_vadd_comm, singleton_zero]

lemma IsShift.card_congr : IsShift A B → Nat.card A = Nat.card B := by rintro ⟨x, rfl⟩; simp

/-- The property of two sets A, B of a group G not being contained in cosets of the same proper
subgroup -/
def NotInCoset (A B : Set G) : Prop := AddSubgroup.closure ((A - A) ∪ (B - B)) = ⊤

/-- Without loss of generality, one can move (up to translation and embedding) any pair A, B of non-empty sets into a subgroup where they are not in a coset. -/
lemma wlog_notInCoset (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (G' : AddSubgroup G) (A' B' : Set G'), IsShift A A' ∧ IsShift B B' ∧ NotInCoset A' B' := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  set G' := AddSubgroup.closure ((A - A) ∪ (B - B))
  set A' : Set G' := (↑) ⁻¹' ((-x) +ᵥ A)
  set B' : Set G' := (↑) ⁻¹' ((-y) +ᵥ B)
  have hxA : -x +ᵥ A ⊆ range ((↑) : G' → G)
  · simp only [← singleton_add', ← neg_singleton, neg_add_eq_sub, SetLike.coe_sort_coe,
      Subtype.range_coe_subtype, SetLike.mem_coe]
    exact (sub_subset_sub_left $ singleton_subset_iff.2 hx).trans $ (subset_union_left ..).trans
      AddSubgroup.subset_closure
  have hyB : -y +ᵥ B ⊆ range ((↑) : G' → G)
  · simp only [← singleton_add', ← neg_singleton, neg_add_eq_sub, SetLike.coe_sort_coe,
      Subtype.range_coe_subtype, SetLike.mem_coe]
    exact (sub_subset_sub_left $ singleton_subset_iff.2 hy).trans $ (subset_union_right ..).trans
      AddSubgroup.subset_closure
  have hA : IsShift A A' := ⟨x, by rw [Set.image_preimage_eq_of_subset hxA, vadd_neg_vadd]⟩
  have hB : IsShift B B' := ⟨y, by rw [Set.image_preimage_eq_of_subset hyB, vadd_neg_vadd]⟩
  refine ⟨G', A', B', hA, hB, ?_⟩
  unfold NotInCoset
  convert AddSubgroup.closure_preimage_eq_top ((A - A) ∪ (B - B))
  simp_rw [preimage_union, hA.sub_self_congr, hB.sub_self_congr]
  rw [preimage_sub, preimage_sub]
  simp [preimage_image_preimage]
  all_goals apply_rules [Subtype.coe_injective, (image_preimage_subset ..).trans, hxA, hyB]

end AddCommGroup

section Torsion

open Real ProbabilityTheory MeasureTheory

variable {G : Type u} [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [Countable G] {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G)
  (μ : Measure Ω := by volume_tac) (μ': Measure Ω' := by volume_tac)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If $G$ is torsion-free and $X,Y$ are $G$-valued random variables then $d[X;2Y]\leq 5d[X;Y]$.  -/
lemma torsion_free_doubling [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) (hG : AddMonoid.IsTorsionFree G) :
    d[X ; μ # (Y + Y) ; μ'] ≤ 5 * d[X; μ # Y ; μ'] := by
  obtain ⟨A, mA, μA, X', Y'₁, Y'₂, hμA, h_indep, hX'_meas, hY'₁_meas, hY'₂_meas, hX'_ident,
    hY'₁_ident, hY'₂_ident, _, _, _⟩ := independent_copies3_nondep_finiteRange hX hY hY μ μ' μ'
  have h_meas (i : Fin 3) : Measurable (![X', Y'₁, Y'₂] i) := by fin_cases i <;> assumption
  haveI : NoZeroSMulDivisors ℕ G := hG.noZeroNsmulDivisors
  have : H[⟨X', ⟨Y'₁ - Y'₂, X' - 2 • Y'₁⟩⟩ ; μA] = H[X ; μ] + 2 * H[Y ; μ'] := calc
    H[⟨X', ⟨Y'₁ - Y'₂, X' - 2 • Y'₁⟩⟩ ; μA] = H[⟨X', ⟨Y'₁, Y'₂⟩⟩ ; μA] := by
      let f : G × G × G → G × G × G := fun ⟨x, y₁, y₂⟩ ↦ (x, y₁ - y₂, x - 2 • y₁)
      show H[f ∘ ⟨X', ⟨Y'₁, Y'₂⟩⟩ ; μA] = _
      refine entropy_comp_of_injective μA ?_ f ?_
      · exact Measurable.prod hX'_meas <| Measurable.prod hY'₁_meas hY'₂_meas
      · exact fun ⟨_, _, _⟩ _ h ↦ by simp at h; obtain ⟨_, _, _⟩ := h; simp_all [smul_right_inj]
    _ = H[X ; μ] + 2 * H[Y ; μ'] := by
      have : IndepFun X' (prod Y'₁ Y'₂) μA := Indep.symm <|
        h_indep.indepFun_prod_mk h_meas 1 2 0 (by decide) (by decide)
      rw [this.entropy_pair_eq_add hX'_meas (by exact Measurable.prod hY'₁_meas hY'₂_meas),
        IndepFun.entropy_pair_eq_add hY'₁_meas hY'₂_meas (h_indep.indepFun (show 1 ≠ 2 by decide)),
        hX'_ident.entropy_eq, hY'₁_ident.entropy_eq, hY'₂_ident.entropy_eq, two_mul]
  have : H[⟨X', X' - 2 • Y'₁⟩ ; μA] = H[X ; μ] + H[Y ; μ'] := calc
    H[⟨X', X' - 2 • Y'₁⟩ ; μA] = H[⟨X', Y'₁⟩ ; μA] := by
      let f : G × G → G × G := fun ⟨x, y₁⟩ ↦ (x, x - 2 • y₁)
      show H[f ∘ ⟨X', Y'₁⟩ ; μA] = _
      apply entropy_comp_of_injective μA (by exact Measurable.prod hX'_meas hY'₁_meas) f
      exact fun ⟨_, _⟩ _ h ↦ by simp at h; obtain ⟨_, _⟩ := h; simp_all [smul_right_inj]
    _ = H[X ; μ] + H[Y ; μ'] := by
      rw [IndepFun.entropy_pair_eq_add hX'_meas hY'₁_meas (h_indep.indepFun (show 0 ≠ 1 by decide)),
        hX'_ident.entropy_eq, hY'₁_ident.entropy_eq]
  let f : G × G → G × G := fun ⟨x, y⟩ ↦ (x, y - x)
  have hf : f.Injective := fun ⟨_, _⟩ _ h ↦ by simp at h; obtain ⟨_, _⟩ := h; simp_all
  have : H[⟨Y'₁ - Y'₂, X' - 2 • Y'₁⟩ ; μA] ≤ H[Y'₁ - Y'₂ ; μA] + H[X' - Y'₁ - Y'₂ ; μA] := calc
    H[⟨Y'₁ - Y'₂, X' - 2 • Y'₁⟩ ; μA] = H[f ∘ ⟨Y'₁ - Y'₂, X' - Y'₁ - Y'₂⟩ ; μA] := by
      show _ = H[⟨Y'₁ - Y'₂, X' - Y'₁ - Y'₂ - (Y'₁ - Y'₂)⟩ ; μA]
      rw [sub_sub_sub_cancel_right, ← sub_add_eq_sub_sub, two_nsmul]
    _ = H[⟨Y'₁ - Y'₂, X' - Y'₁ - Y'₂⟩ ; μA] := by
      refine entropy_comp_of_injective μA (Measurable.prod ?_ ?_) f hf
      · exact Measurable.sub hY'₁_meas hY'₂_meas
      · exact Measurable.sub (Measurable.sub hX'_meas hY'₁_meas) hY'₂_meas
    _ ≤ H[Y'₁ - Y'₂ ; μA] + H[X' - Y'₁ - Y'₂ ; μA] :=
      entropy_pair_le_add (hY'₁_meas.sub' hY'₂_meas) (hX'_meas.sub' hY'₁_meas |>.sub' hY'₂_meas) μA
  have : H[⟨X', ⟨Y'₁ - Y'₂, X' - 2 • Y'₁⟩⟩ ; μA] + H[X' - 2 • Y'₁ ; μA] ≤
      H[⟨X', X' - 2 • Y'₁⟩ ; μA] + H[⟨Y'₁ - Y'₂, X' - 2 • Y'₁⟩ ; μA] := by
    haveI : FiniteRange (Y'₁ - Y'₂) := FiniteRange.sub Y'₁ Y'₂
    haveI : FiniteRange (2 • Y'₁) := by show FiniteRange ((fun x ↦ 2 • x) ∘ Y'₁); infer_instance
    apply entropy_triple_add_entropy_le μA hX'_meas (Measurable.sub hY'₁_meas hY'₂_meas)
    exact Measurable.sub' hX'_meas <| Measurable.const_smul hY'₁_meas 2
  have : H[⟨Y'₁, ⟨Y'₂, X' - Y'₁ - Y'₂⟩⟩ ; μA] = H[X ; μ] + 2 * H[Y ; μ'] := calc
    H[⟨Y'₁, ⟨Y'₂, X' - Y'₁ - Y'₂⟩⟩ ; μA] = H[⟨Y'₁, ⟨Y'₂, X'⟩⟩ ; μA] := by
      let f : G × G × G → G × G × G := fun ⟨y₁, y₂, x⟩ ↦ (y₁, y₂, x - y₁ - y₂)
      show H[f ∘ ⟨Y'₁, ⟨Y'₂, X'⟩⟩ ; μA] = H[⟨Y'₁, ⟨Y'₂, X'⟩⟩ ; μA]
      refine entropy_comp_of_injective μA ?_ f ?_
      · exact Measurable.prod hY'₁_meas <| Measurable.prod hY'₂_meas hX'_meas
      · exact fun ⟨_, _, _⟩ _ h ↦ by simp at h; obtain ⟨_, _, _⟩ := h; simp_all
    _ = H[X ; μ] + 2 * H[Y ; μ'] := by
      have : IndepFun Y'₁ (prod Y'₂ X') μA := Indep.symm <|
        h_indep.indepFun_prod_mk h_meas 2 0 1 (by decide) (by decide)
      rw [this.entropy_pair_eq_add hY'₁_meas (by exact Measurable.prod hY'₂_meas hX'_meas),
        IndepFun.entropy_pair_eq_add hY'₂_meas hX'_meas (h_indep.indepFun (show 2 ≠ 0 by decide)),
        hX'_ident.entropy_eq, hY'₁_ident.entropy_eq, hY'₂_ident.entropy_eq]
      group
  have : H[⟨Y'₁, X' - Y'₁ - Y'₂⟩ ; μA] = H[Y ; μ'] + H[X' - Y'₂ ; μA] := calc
    H[⟨Y'₁, X' - Y'₁ - Y'₂⟩ ; μA] = H[f ∘ ⟨Y'₁, X' - Y'₂⟩ ; μA] := by rw [sub_right_comm] ; rfl
    _ = H[⟨Y'₁, X' - Y'₂⟩ ; μA] := entropy_comp_of_injective μA
      (by exact Measurable.prod hY'₁_meas <| Measurable.sub hX'_meas hY'₂_meas) f hf
    _ = H[Y ; μ'] + H[X' - Y'₂ ; μA] := by
      haveI : FiniteRange (X' - Y'₂) := FiniteRange.sub X' Y'₂
      convert IndepFun.entropy_pair_eq_add hY'₁_meas (hX'_meas.sub hY'₂_meas)
        <| h_indep.indepFun_sub_right h_meas 1 0 2 (by decide) (by decide)
      exact hY'₁_ident.entropy_eq.symm
  have : H[⟨Y'₂, X' - Y'₁ - Y'₂⟩ ; μA] = H[Y ; μ'] + H[X' - Y'₁ ; μA] := calc
    H[⟨Y'₂, X' - Y'₁ - Y'₂⟩ ; μA] = H[f ∘ ⟨Y'₂, X' - Y'₁⟩ ; μA] := rfl
    _ = H[⟨Y'₂, X' - Y'₁⟩ ; μA] := entropy_comp_of_injective μA
      (by exact Measurable.prod hY'₂_meas <| Measurable.sub hX'_meas hY'₁_meas) f hf
    _ = H[Y ; μ'] + H[X' - Y'₁ ; μA] := by
      haveI : FiniteRange (X' - Y'₁) := FiniteRange.sub X' Y'₁
      convert IndepFun.entropy_pair_eq_add hY'₂_meas (hX'_meas.sub hY'₁_meas)
        <| h_indep.indepFun_sub_right h_meas 2 0 1 (by decide) (by decide)
      exact hY'₂_ident.entropy_eq.symm
  have : H[⟨Y'₁, ⟨Y'₂, X' - Y'₁ - Y'₂⟩⟩ ; μA] + H[X' - Y'₁ - Y'₂ ; μA] ≤
      H[⟨Y'₁, X' - Y'₁ - Y'₂⟩ ; μA] + H[⟨Y'₂, X' - Y'₁ - Y'₂⟩ ; μA] := by
    apply entropy_triple_add_entropy_le μA hY'₁_meas hY'₂_meas
    exact Measurable.sub (Measurable.sub hX'_meas hY'₁_meas) hY'₂_meas
  have : H[X' - Y'₁ - Y'₂ ; μA] ≤ 2 * d[X ; μ # Y ; μ'] + H[Y ; μ'] := calc
    H[X' - Y'₁ - Y'₂ ; μA] ≤ H[X' - Y'₁ ; μA] + H[X' - Y'₂ ; μA] - H[X ; μ] := by linarith
    _ = 2 * d[X ; μ # Y ; μ'] + H[Y ; μ'] := by
      nth_rw 1 [two_mul, ← hX'_ident.rdist_eq hY'₁_ident, ← hX'_ident.rdist_eq hY'₂_ident]
      have h1 : d[X' ; μA # Y'₁ ; μA] = H[X' - Y'₁ ; μA] - H[X' ; μA] / 2 - H[Y'₁ ; μA] / 2 :=
        (h_indep.indepFun (show 0 ≠ 1 by decide)).rdist_eq hX'_meas hY'₁_meas
      have h2 : d[X' ; μA # Y'₂ ; μA] = H[X' - Y'₂ ; μA] - H[X' ; μA] / 2 - H[Y'₂ ; μA] / 2 :=
        (h_indep.indepFun (show 0 ≠ 2 by decide)).rdist_eq hX'_meas hY'₂_meas
      rw [h1, h2, hY'₁_ident.entropy_eq, hY'₂_ident.entropy_eq, hX'_ident.entropy_eq]
      group
  have : d[X ; μ # 2 • Y ; μ'] ≤
      d[Y'₁ ; μA # Y'₂ ; μA] + (H[Y ; μ'] - H[X ; μ]) / 2 + 2 * d[X ; μ # Y ; μ'] := calc
    d[X ; μ # 2 • Y ; μ'] = H[X' - 2 • Y'₁ ; μA] - H[X ; μ] / 2 - H[2 • Y ; μ'] / 2 := by
      have h2Y_ident : IdentDistrib (2 • Y'₁) (2 • Y) (μ := μA) (ν := μ') := by
        convert hY'₁_ident.comp <| measurable_discrete <| fun g ↦ 2 • g
      have h2Y_indep : IndepFun X' (2 • Y'₁) (μ := μA) := by
        convert (h_indep.indepFun (show 0 ≠ 1 by decide)).comp measurable_id
          (measurable_const_smul 2)
      rw [← hX'_ident.rdist_eq h2Y_ident,
        h2Y_indep.rdist_eq hX'_meas <| Measurable.const_smul hY'₁_meas 2,
        hX'_ident.entropy_eq, h2Y_ident.entropy_eq]
    _ ≤ H[Y'₁ - Y'₂ ; μA] + 2 * d[X ; μ # Y ; μ'] - H[X ; μ] / 2 - H[2 • Y ; μ'] / 2 := by linarith
    _ = d[Y'₁ ; μA # Y'₂ ; μA] + (H[Y ; μ'] - H[X ; μ]) / 2 + 2 * d[X ; μ # Y ; μ'] := by
      have H2Y : H[2 • Y ; μ'] = H[Y ; μ'] := by
        let f (g : G) := 2 • g
        exact entropy_comp_of_injective μ' hY f (fun _ _ ↦ by simp [smul_right_inj])
      have : d[Y'₁ ; μA # Y'₂ ; μA] = H[Y'₁ - Y'₂ ; μA] - H[Y'₁ ; μA] / 2 - H[Y'₂ ; μA] / 2 :=
        (h_indep.indepFun (show 1 ≠ 2 by decide)).rdist_eq hY'₁_meas hY'₂_meas
      rw [this, hY'₁_ident.entropy_eq, hY'₂_ident.entropy_eq, H2Y]
      group
  have : d[Y'₁ ; μA # Y'₂ ; μA] ≤ 2 * d[X ; μ # Y ; μ'] := by
    rw [two_mul]
    convert rdist_triangle hY'₁_meas hX'_meas hY'₂_meas (μ := μA) (μ' := μA) (μ'' := μA)
    · exact rdist_symm.trans (hY'₁_ident.rdist_eq hX'_ident).symm
    · exact (hX'_ident.rdist_eq hY'₂_ident).symm
  rw [← two_nsmul]
  linarith [abs_le.mp <| diff_ent_le_rdist hX hY (μ := μ) (μ' := μ')]

/-- If $G$ is a torsion-free group and $X,Y$ are $G$-valued random variables and
$\phi : G\to \mathbb{F}_2^d$ is a homomorphism then
\[\mathbb{H}(\phi(X))\leq 10d[X;Y].\] -/
lemma torsion_dist_shrinking {H : Type u} [FiniteRange X] [FiniteRange Y] (hX : Measurable X)
  (hY : Measurable Y) [AddCommGroup H] [ElementaryAddCommGroup H 2]
  [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]
  (hG : AddMonoid.IsTorsionFree G) (φ : G →+ H) :
  H[φ ∘ X ; μ] ≤ 10 * d[X; μ # Y ; μ'] := by
  have :=
    calc d[φ ∘ X ; μ # φ ∘ (Y + Y); μ'] ≤ d[X; μ # (Y + Y) ; μ'] := rdist_of_hom_le φ hX (Measurable.add hY hY)
    _ ≤ 5 * d[X; μ # Y ; μ'] := torsion_free_doubling X Y μ μ' hX hY hG
  have eq_zero : φ ∘ (Y + Y) = fun _ ↦ 0 := by ext x ; simp only [Function.comp_apply, Pi.add_apply,
    map_add, ElementaryAddCommGroup.add_self]
  rwa [eq_zero, rdist_zero_eq_half_ent, div_le_iff zero_lt_two, mul_assoc, mul_comm _ 2, ←mul_assoc,
    show (5*2 : ℝ) = 10 by norm_num] at this

end Torsion

section F2_projection

open Real ProbabilityTheory MeasureTheory

variable {G : Type u} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
 {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- Let $G=\mathbb{F}_2^n$ and $X,Y$ be $G$-valued random variables such that
\[\mathbb{H}(X)+\mathbb{H}(Y)> 44d[X;Y].\]
There is a non-trivial subgroup $H\leq G$ such that
\[\log \lvert H\rvert <\mathbb{H}(X)+\mathbb{H}(Y)\] and
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))< \frac{\mathbb{H}(X)+\mathbb{H}(Y)}{2}\]
where $\psi : G\to G/H$ is the natural projection homomorphism.
-/
proof_wanted app_ent_PFR (hent : H[ X; μ] + H[Y; μ'] > 44 * d[X;μ # Y;μ']) : ∃ H : AddSubgroup G, log (Nat.card H) < H[X; μ] + H[Y;μ'] ∧ H[ (QuotientAddGroup.mk' H) ∘ X; μ ] + H[ (QuotientAddGroup.mk' H) ∘ Y; μ' ] < (H[ X; μ] + H[Y; μ'])/2

/-- If $G=\mathbb{F}_2^d$ and $X,Y$ are $G$-valued random variables then there is a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq 2(\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi : G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 44 d[\psi(X);\psi(Y)].\] -/
lemma PFR_projection :
    ∃ H : AddSubgroup G, log (Nat.card H) ≤ 2 * (H[X; μ] + H[Y ; μ']) ∧
      H[(QuotientAddGroup.mk' H) ∘ X; μ ] + H[ (QuotientAddGroup.mk' H) ∘ Y; μ' ] ≤
        44 * d[(QuotientAddGroup.mk' H) ∘ X;μ # (QuotientAddGroup.mk' H) ∘ Y;μ'] := by sorry

end F2_projection

open MeasureTheory ProbabilityTheory Real

lemma four_logs {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    log ((a*b)/(c*d)) = log a + log b - log c - log d := by
  rw [log_div, log_mul, log_mul, sub_sub] <;> positivity

/-- Let $\phi : G\to H$ be a homomorphism and $A,B\subseteq G$ be finite subsets. If $x,y\in H$ then let $A_x=A\cap \phi^{-1}(x)$ and $B_y=B\cap \phi^{-1}(y)$. There exist $x,y\in H$ such that $A_x,B_y$ are both non-empty and
\[d[\phi(U_A);\phi(U_B)]\log \frac{\lvert A\rvert\lvert B\rvert}{\lvert A_x\rvert\lvert B_y\rvert}\leq (\mathbb{H}(\phi(U_A))+\mathbb{H}(\phi(U_B)))(d(U_A,U_B)-d(U_{A_x},U_{B_y}).\] -/
lemma single_fibres {G H Ω Ω' : Type u} [AddCommGroup G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [AddCommGroup H] [Countable H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (φ : G →+ H) {A B : Set G} [Finite A] [Finite B] (hA : A.Nonempty)
    (hB : B.Nonempty) [MeasureSpace Ω] [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [IsProbabilityMeasure  (ℙ : Measure Ω')] {UA : Ω → G} {UB : Ω' → G} (hUA' : Measurable UA)
    (hUB' : Measurable UB) (hUA : IsUniform A UA) (hUB : IsUniform B UB) :
    ∃ (x y : H) (Ax By : Set G), Ax = A ∩ φ⁻¹' {x} ∧ By = B ∩ φ⁻¹' {y} ∧ Ax.Nonempty ∧ By.Nonempty ∧
      d[φ ∘ UA # φ ∘ UB] * log (Nat.card A * Nat.card B / (Nat.card Ax * Nat.card By))
        ≤ (H[φ ∘ UA] + H[φ ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := by sorry

section dim

open Classical

variable {G : Type*} [AddCommGroup G]

/- If G ≅ ℤᵈ then there is a subgroup H of G such that A lies in a coset of H. This is helpful to
  give the equivalent definition of `dimension`. Here this is stated in greated generality since the
  proof carries over automatically-/
lemma exists_coset_cover (A : Set G) :
    ∃ (d : ℕ), ∃ (S : Submodule ℤ G) (v : G),
      FiniteDimensional.finrank ℤ S = d ∧ ∀ a ∈ A, a - v ∈ S := by
  existsi FiniteDimensional.finrank ℤ (⊤ : Submodule ℤ G), ⊤, 0
  refine ⟨rfl, fun a _ ↦ trivial⟩

noncomputable def dimension (A : Set G) : ℕ := Nat.find (exists_coset_cover A)

lemma dimension_le_of_coset_cover (A : Set G) (S : Submodule ℤ G) (v : G)
    (hA : ∀ a ∈ A, a - v ∈ S) : dimension A ≤ FiniteDimensional.finrank ℤ S := by
  apply Nat.find_le
  existsi S , v
  exact ⟨rfl, hA⟩

lemma dimension_le_rank [Module.Finite ℤ G] (A : Set G) :
    dimension A ≤ FiniteDimensional.finrank ℤ G := by
  obtain ⟨S, v, hs, _⟩ := Nat.find_spec (exists_coset_cover A)
  rw [dimension, ←hs]
  apply Submodule.finrank_le S

end dim

variable {G : Type u} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

open Real MeasureTheory ProbabilityTheory Pointwise

/-- Move to Mathlib? `Finsupp.mapRange` of a surjective function is surjective. -/
lemma Finsupp.mapRange_surjective {α : Type u_1} {M : Type u_5} {N : Type u_7} [Zero M] [Zero N] (f : M → N) (hf : f 0 = 0)
  (hs : Function.Surjective f) : Function.Surjective (Finsupp.mapRange (α := α) f hf) := by
  classical
  let g (n : N) : M := if n = 0 then 0 else Function.surjInv hs n
  have : Function.RightInverse g f := by
    intro n
    by_cases h : n = 0
    . simp [h,hf]
    simp [h, Function.surjInv_eq hs n]
  have hg : g 0 = 0 := by simp
  have hfg : (f ∘ g) 0 = 0 := by simp [hf, hg]
  intro F
  use Finsupp.mapRange g hg F
  rw [← Finsupp.mapRange_comp (h :=hfg)]
  convert Finsupp.mapRange_id F
  convert Function.RightInverse.id this

/-- A free Z-module is torsion-free. Move to Mathlib? -/
lemma torsion_free : AddMonoid.IsTorsionFree G := by
    rintro x hx hn
    rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hn
    rcases hn with ⟨ n, hn, hn' ⟩
    apply_fun Module.Free.repr ℤ G at hn'
    simp_rw [map_nsmul, map_zero, smul_eq_zero, AddEquivClass.map_eq_zero_iff, hx, or_false] at hn'
    linarith

/-- If G is a rank n free Z-module, then G/2G is a finite elementary 2-group of cardinality 2^n.  Code is slow, needs to be golfed -/
lemma weak_PFR_quotient_prelim :
  let H := G ⧸ (AddMonoidHom.range (zsmulAddGroupHom 2))
  ElementaryAddCommGroup H 2 ∧ Finite H ∧ Nat.card H = 2^(FiniteDimensional.finrank ℤ G) := by
  set ψ : G →+ G := zsmulAddGroupHom 2
  set G₂ := AddMonoidHom.range ψ
  set H := G ⧸ G₂
  set φ : G →+ H := QuotientAddGroup.mk' G₂
  have hH_elem : ElementaryAddCommGroup H 2 := by
    apply ElementaryAddCommGroup.quotient_group (by decide)
    intro x; rw [AddMonoidHom.mem_range]
    use x
    rw [zsmulAddGroupHom_apply]
    norm_cast
  let B := Module.Free.ChooseBasisIndex ℤ G
  let bG : Basis B ℤ G := Module.Free.chooseBasis ℤ G
  have hB_fin : Fintype B := by infer_instance
  have hB_card : Nat.card B = FiniteDimensional.finrank ℤ G := by
    rw [FiniteDimensional.finrank_eq_card_basis bG, Nat.card_eq_fintype_card]
  have hH_module : Module (ZMod 2) H := by infer_instance
  let mod : (B →₀ ℤ) →+ (B →₀ ZMod 2) := Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod 2))
  let f : G →+ (B →₀ ℤ) := bG.repr
  have hker : G₂ ≤ AddMonoidHom.ker (AddMonoidHom.comp mod f) := by
    intro x hx
    simp_rw [AddMonoidHom.mem_range, zsmulAddGroupHom_apply, AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Int.coe_castAddHom] at hx ⊢
    rcases hx with ⟨ y, rfl⟩
    ext b
    simp_rw [map_zsmul, Finsupp.mapRange_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Int.cast_mul, Int.int_cast_ofNat, Finsupp.coe_zero, Pi.zero_apply, mul_eq_zero]
    left
    exact ZMod.nat_cast_self 2
  let g : H →+ (B →₀ ZMod 2) := QuotientAddGroup.lift G₂ (AddMonoidHom.comp mod f) hker
  have hsur : Function.Surjective g := by
    have h1 : Function.Surjective mod := Finsupp.mapRange_surjective (Int.castAddHom (ZMod 2)) (map_zero _) ZMod.int_cast_surjective
    have h2 := h1.comp bG.repr.surjective
    have h3 : mod ∘ bG.repr = g ∘ (QuotientAddGroup.mk' G₂) := by
      ext x b
      simp only [Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Int.coe_castAddHom,
        Finsupp.mapRange_apply, QuotientAddGroup.coe_mk', QuotientAddGroup.lift_mk,
        AddMonoidHom.coe_comp, AddMonoidHom.coe_coe]
    rw [h3] at h2
    apply Function.Surjective.of_comp h2
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rcases QuotientAddGroup.mk'_surjective G₂ x with ⟨y, rfl⟩
    simp_rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Int.coe_castAddHom,FunLike.ext_iff,Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply,ZMod.int_cast_zmod_eq_zero_iff_dvd] at hx
    replace hx := fun x ↦ Int.mul_ediv_cancel' (hx x)
    let z (b : B) := ((Module.Free.chooseBasis ℤ G).repr y) b / 2
    let z' := (Finsupp.equivFunOnFinite).symm z
    change ∀ b : B, 2 * z' b = (f y) b at hx
    let x' := bG.repr.symm z'
    simp_rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
    use x'
    change 2 • (bG.repr.symm.toLinearMap.toAddMonoidHom z') = y
    rw [← AddMonoidHom.map_zsmul bG.repr.symm.toLinearMap.toAddMonoidHom z' (2 : ℤ)]
    rw [← LinearEquiv.symm_apply_apply bG.repr y]
    change bG.repr.symm (2 • z') = bG.repr.symm (f y)
    congr
    ext b
    rw [Finsupp.smul_apply, ← hx b, smul_eq_mul]
  rcases Function.bijective_iff_has_inverse.mp ⟨ hinj, hsur ⟩ with ⟨ g', hg' ⟩

  have bH : Basis B (ZMod 2) H := by
    constructor
    exact {
      toFun := g
      invFun := g'
      left_inv := hg'.1
      right_inv := hg'.2
      map_add' := AddMonoidHom.map_add _
      map_smul' := by
        intro r x
        rcases ZMod.int_cast_surjective r with ⟨ n, rfl ⟩
        change g ((n : ZMod 2) • x) = (n : ZMod 2) • g x
        rw [intCast_smul, intCast_smul]
        exact AddMonoidHom.map_zsmul g x n
    }
  have hH_fin : Fintype H := Module.fintypeOfFintype bH
  have hH_card : Nat.card H = 2^(FiniteDimensional.finrank ℤ G) := by
    rw [Nat.card_eq_fintype_card, Module.card_fintype bH, ← Nat.card_eq_fintype_card (α := B), hB_card]
    congr
  exact ⟨ hH_elem, Finite.of_fintype H, hH_card ⟩

open QuotientAddGroup

/-- A version of the third isomorphism theorem : if G₂ ≤ G and H' is a subgroup of G⧸G₂, then there is a canonical isomorphism between H⧸H' and G⧸N, where N is the preimage of H' in G. A bit clunky; may be a better way to do this -/
lemma third_iso {G : Type u} [AddCommGroup G] {G₂ : AddSubgroup G} (H' : AddSubgroup (G ⧸ G₂)) :
  let H := G ⧸ G₂
  let φ : G →+ H := mk' G₂
  let N := AddSubgroup.comap φ H'
  ∃ e : H ⧸ H' ≃+ G ⧸ N, ∀ x : G, e (mk' H' (φ x))= mk' N x := by
  set H := G ⧸ G₂
  let φ : G →+ H := mk' G₂
  let N := AddSubgroup.comap φ H'
  have h1 : G₂ ≤ N := by
    intro x hx
    rw [← eq_zero_iff] at hx
    simp [hx, AddSubgroup.zero_mem H']
  set H'' := AddSubgroup.map (mk' G₂) N
  have h2 : H' = H'' := by
    change H' = AddSubgroup.map (mk' G₂) N
    rw [AddSubgroup.map_comap_eq, AddMonoidHom.range_top_of_surjective _ (mk'_surjective G₂)]
    simp
  let e1 : H ⧸ H'' ≃+ G ⧸ N := quotientQuotientEquivQuotient _ _ h1
  let e2 := quotientAddEquivOfEq h2
  set e := e2.trans e1
  use e
  intro x
  convert (quotientQuotientEquivQuotientAux_mk_mk _ _ h1 x) using 1

lemma single {Ω : Type u} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} {z : Ω} (hA : μ.real A = 1) (hz : μ.real {z} > 0) :
    z ∈ A := by
  contrapose! hz
  have : Disjoint {z} A := by simp [hz]
  replace this := measureReal_union (μ := μ) this (measurableSet_discrete _)
  simp [hA] at this
  have h := measureReal_mono (μ := μ) (show insert z A ⊆ Set.univ by simp)
  simp [this] at h
  assumption

/-- Given two non-empty finite subsets A, B of a rank n free Z-module G, there exists a subgroup N and points x, y in G/N such that the fibers Ax, By of A, B over x, y respectively are non-empty, one has the inequality
$$ \log \frac{|A| |B|}{|A_x| |B_y|} ≤ 44 (d[U_A; U_B] - d[U_{A_x}; U_{B_y}])$$
and one has the dimension bound
$$ n \log 2 ≤ \log |G/N| + 40 d[U_A; U_B].$$
 -/
lemma weak_PFR_asymm_prelim {A B : Set G} [Finite A] [Finite B] (hA : A.Nonempty) (hB : B.Nonempty)
    {Ω Ω' : Type u} [hΩ : MeasureSpace Ω] [hΩ' : MeasureSpace Ω'] {UA : Ω → G} {UB : Ω' → G} [hpΩ : IsProbabilityMeasure (ℙ : Measure Ω)] [hpΩ' : IsProbabilityMeasure (ℙ : Measure Ω')] (hUA : IsUniform A UA) (hUB : IsUniform B UB) (hUA_mes : Measurable UA) (hUB_mes : Measurable UB) [hUA_f : FiniteRange UA] [hUB_f : FiniteRange UB] :
    ∃ (N : AddSubgroup G) (x y : G ⧸ N) (Ax By : Set G) (Ωx Ωy : Type u) (hΩx : MeasureSpace Ωx)
    (hΩy : MeasureSpace Ωy) (UAx : Ωx → G) (UBy : Ωy → G), Ax.Nonempty ∧ By.Nonempty ∧ Set.Finite Ax ∧ Set.Finite By ∧ Ax = {z : G | z ∈ A ∧ QuotientAddGroup.mk' N z = x } ∧ By = {z : G | z ∈ B ∧ QuotientAddGroup.mk' N z = y } ∧ IsProbabilityMeasure (ℙ : Measure Ωx) ∧IsProbabilityMeasure (ℙ : Measure Ωy)  ∧ IsUniform Ax UAx ∧ IsUniform By UBy ∧ Measurable UAx ∧ Measurable UBy ∧ FiniteRange UAx ∧ FiniteRange UBy ∧ (log 2) * FiniteDimensional.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) + 40 * dᵤ[ A # B ] ∧ log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By) ≤ 44 * (dᵤ[ A # B ] - dᵤ[ Ax # By ]) := by
  have := hA.to_subtype
  have := hB.to_subtype
  obtain ⟨ h_elem, h_finite, h_card ⟩ := weak_PFR_quotient_prelim (G := G)
  set ψ : G →+ G := zsmulAddGroupHom 2
  set G₂ := AddMonoidHom.range ψ
  set H := G ⧸ G₂
  let φ : G →+ H := QuotientAddGroup.mk' G₂
  let _mH : MeasurableSpace H := ⊤
  have _msH : MeasurableSingletonClass H := ⟨λ _ ↦ trivial⟩
  have h_fintype : Fintype H := Fintype.ofFinite H
  have h_torsionfree := torsion_free (G := G)

  obtain ⟨ Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, hUA_fin ⟩ := exists_isUniform_measureSpace' A
  obtain ⟨ Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, hUB_fin ⟩ := exists_isUniform_measureSpace' B

  rcases (PFR_projection (φ.toFun ∘ UA) (φ.toFun ∘ UB) ℙ ℙ) with ⟨H', ⟨ hH1, hH2 ⟩ ⟩
  let N := AddSubgroup.comap φ H'
  set φ' := QuotientAddGroup.mk' N
  have _cGN : Countable (G ⧸ N) := Function.Surjective.countable (QuotientAddGroup.mk'_surjective N)
  have _msGN : MeasurableSingletonClass (G ⧸ N) := by
    constructor
    intro x
    exact MeasurableSpace.map_def.mpr (measurableSet_discrete _)

  rcases third_iso H' with ⟨ e : H ⧸ H' ≃+ G ⧸ N, he ⟩
  rcases single_fibres φ' hA hB hUA_mes hUB_mes hUA_unif hUB_unif with
    ⟨x, y, Ax, By, hAx, hBy, hnAx, hnBy, hcard_ineq⟩
  have := hnAx.to_subtype
  have := hnBy.to_subtype
  have Axf : Finite Ax := by rw [hAx]; infer_instance
  have Byf : Finite By := by rw [hBy]; infer_instance

  have h1 := torsion_dist_shrinking UA UB ℙ ℙ hUA_mes hUB_mes h_torsionfree φ
  have h2 := torsion_dist_shrinking UB UA ℙ ℙ hUB_mes hUA_mes h_torsionfree φ
  rw [rdist_symm] at h2
  rw [<- rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes] at h1 h2
  -- using explicit .toFun casts as this saves a lot of heartbeats
  change H[φ.toFun ∘ UA] ≤ 10 * dᵤ[A # B] at h1
  change H[φ.toFun ∘ UB] ≤ 10 * dᵤ[A # B] at h2
  replace hH1 : log (Nat.card H') ≤ 40  * dᵤ[A # B] := by
    apply hH1.trans
    linarith
  replace h_card : log 2 * FiniteDimensional.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) + 40 * dᵤ[A # B] := by
    rw [mul_comm, ← log_rpow (by norm_num)]
    norm_cast
    classical
    rwa [← h_card, ← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← AddSubgroup.index_mul_card H', AddSubgroup.index_eq_card, Nat.cast_mul, log_mul, add_le_add_iff_left, ← Nat.card_eq_fintype_card]
    all_goals norm_cast; exact Fintype.card_ne_zero


  use N, x, y, Ax, By
  refine ⟨ hnAx, hnBy, Ax.toFinite, By.toFinite, hAx, hBy, h_card, ?_ ⟩

  replace hH2 : H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] ≤ 44 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] := by
    set X := ((mk' H').toFun ∘ φ.toFun) ∘ UA
    set Y := ((mk' H').toFun ∘ φ.toFun) ∘ UB
    have hX : Measurable X := Measurable.comp (measurable_discrete _) hUA_mes
    have hY : Measurable Y := Measurable.comp (measurable_discrete _) hUB_mes
    change H[X] + H[Y] ≤ 44 * d[X # Y] at hH2

    have ha : φ'.toFun ∘ UA = e.toFun ∘ X := by ext x; exact (he (UA x)).symm
    have hb : φ'.toFun ∘ UB = e.toFun ∘ Y := by ext x; exact (he (UB x)).symm
    have he_inj : Function.Injective e.toFun := AddEquiv.injective e
    rw [ha, hb, entropy_comp_of_injective _ hX _ he_inj, entropy_comp_of_injective _ hY _ he_inj]
    have : d[e.toFun ∘ X # e.toFun ∘ Y] = d[X # Y] :=  rdist_of_inj hX hY e.toAddMonoidHom he_inj
    rwa [this]

  set X : Ω → G ⧸ N := φ'.toFun ∘ UA
  set Y : Ω' → G ⧸ N := φ'.toFun ∘ UB
  have hX : Measurable X := Measurable.comp (measurable_discrete _) hUA_mes
  have hY : Measurable Y := Measurable.comp (measurable_discrete _) hUB_mes
  rcases le_iff_lt_or_eq.mp (rdist_nonneg (μ := ℙ) (μ' := ℙ) hX hY) with h | h
  swap
  . rw [← h] at hH2
    have hH2A : H[X] ≥ 0 := entropy_nonneg _ _
    have hH2B : H[Y] ≥ 0 := entropy_nonneg _ _
    have hH2A' : H[X] ≤ 0 := by linarith only [hH2, hH2A, hH2B]
    have hH2B' : H[Y] ≤ 0 := by linarith only [hH2, hH2A, hH2B]

    rcases const_of_nonpos_entropy (μ := ℙ) hX hH2A' with ⟨ x', hx ⟩
    rcases const_of_nonpos_entropy (μ := ℙ) hY hH2B' with ⟨ y', hy ⟩

    have hAAx {z : G} (hz : z ∈ A) : φ'.toFun z = x' := by
      change (ℙ).real (UA⁻¹' (φ'⁻¹' {x'})) = 1 at hx
      rw [← MeasureTheory.map_measureReal_apply hUA_mes (measurableSet_discrete _)] at hx
      set Af := A.toFinite.toFinset
      have hUAf : IsUniform Af UA := by
        convert hUA_unif; simp only [Set.Finite.coe_toFinset]
      have hnAf : 0 < Nat.card Af := by simp only [Set.Finite.mem_toFinset, Nat.card_pos]
      have hzf : z ∈ Af := by simp [Set.Finite.mem_toFinset, hz]
      have : (Measure.map UA ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUAf hUA_mes hzf]
        positivity
      have _ : IsProbabilityMeasure ((ℙ).map UA) := by
        exact MeasureTheory.isProbabilityMeasure_map (Measurable.aemeasurable hUA_mes)
      replace this := single ((ℙ).map UA) hx this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this

    have hxx : Ax = A := by
      have h : hnAx.some ∈ Ax := hnAx.some_mem
      simp [hAx] at h ⊢
      have := hAAx h.1
      simp [h.2] at this
      intro z hz
      simp [this]
      convert hAAx hz

    have hBBy {z : G} (hz : z ∈ B) : φ'.toFun z = y' := by
      change (ℙ).real (UB⁻¹' (φ'⁻¹' {y'})) = 1 at hy
      rw [← MeasureTheory.map_measureReal_apply hUB_mes (measurableSet_discrete _)] at hy
      set Bf := B.toFinite.toFinset
      have hUBf : IsUniform Bf UB := by convert hUB_unif; simp only [Set.Finite.coe_toFinset]
      have hnBf : 0 < Nat.card Bf := by simp only [Set.Finite.mem_toFinset, Nat.card_pos]
      have hzf : z ∈ Bf := by simp [Set.Finite.mem_toFinset, hz]
      have : (Measure.map UB ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUBf hUB_mes hzf]
        positivity
      have _ : IsProbabilityMeasure ((ℙ).map UB) := by
        exact MeasureTheory.isProbabilityMeasure_map (Measurable.aemeasurable hUB_mes)
      replace this := single ((ℙ).map UB) hy this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this

    have hyy : By = B := by
      have h : hnBy.some ∈ By := hnBy.some_mem
      simp [hBy] at h ⊢
      have := hBBy h.1
      simp [h.2] at this
      intro z hz
      simp [this]
      convert hBBy hz

    simp [hxx, hyy]

  have := calc d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By))
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * log ((Nat.card A) * (Nat.card B) / ((Nat.card Ax) * (Nat.card By))) := by
      congr
      convert (four_logs ?_ ?_ ?_ ?_).symm
      all_goals norm_cast; exact Nat.card_pos
    _ ≤ (H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := hcard_ineq
    _ ≤ (44 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := by
      apply mul_le_mul_of_nonneg_right hH2
      have := rdist_le_avg_ent (Measurable.comp (measurable_discrete φ'.toFun) hUA_mes) (Measurable.comp (measurable_discrete φ'.toFun) hUB_mes)
      replace this : 0 < H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] := by linarith
      rw [← mul_le_mul_left this]
      apply le_trans _ hcard_ineq
      rw [mul_zero]
      change 0 ≤ d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * log ((Nat.card A) * (Nat.card B) / ((Nat.card Ax) * (Nat.card By)))
      rw [← mul_zero d[φ'.toFun ∘ UA # φ'.toFun ∘ UB], mul_le_mul_left h]
      apply Real.log_nonneg
      rw [one_le_div]
      gcongr
      . apply Nat.card_mono
        . exact Set.toFinite A
        rw [hAx]; exact Set.inter_subset_left _ _
      apply Nat.card_mono
      . exact Set.toFinite B
      rw [hBy]; exact Set.inter_subset_left _ _
      norm_cast
      exact mul_pos Nat.card_pos Nat.card_pos
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (44 * (d[UA # UB] - dᵤ[Ax # By])) := by ring
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (44 * (dᵤ[A # B] - dᵤ[Ax # By])) := by rw [<- rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes]
  exact (mul_le_mul_left h).mp this

/-- Separating out the conclusion of `weak_PFR_asymm` for convenience of induction arguments.-/
def WeakPFRAsymmConclusion (A B : Set G) : Prop := ∃ A' B' : Set G, A' ⊆ A ∧ B' ⊆ B ∧ Nonempty A' ∧ Nonempty B' ∧ log (((Nat.card A) * (Nat.card B)) / ((Nat.card A') * (Nat.card B'))) ≤ 44 * dᵤ[A # B] ∧ max (dimension A') (dimension B') ≤ (40 / log 2) * dᵤ[A # B]

/-- In fact one has equality here, but this is tricker to prove and not needed for the argument. -/
lemma dimension_of_shift {G : Type u} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] {H : AddSubgroup G} [Module.Free ℤ H] [Module.Finite ℤ H] (A : Set H) (x : G) : dimension ((fun a : H ↦ (a : G) + x) '' A) ≤ dimension A := by
  classical
  rcases Nat.find_spec (exists_coset_cover A) with ⟨ S, v, hrank, hshift ⟩
  change FiniteDimensional.finrank ℤ S = dimension A at hrank
  rw [← hrank]
  convert dimension_le_of_coset_cover _ (Submodule.map H.subtype.toIntLinearMap S) (x+v) ?_
  . apply LinearEquiv.finrank_eq
    exact Submodule.equivMapOfInjective _ (by simpa using Subtype.val_injective) _
  intro a ha
  rw [Set.mem_image] at ha
  rcases ha with ⟨ b, ⟨ hb, hb'⟩ ⟩
  rw [Submodule.mem_map]
  use b - v, hshift b hb
  simp [← hb']
  abel

lemma conclusion_transfers {A B : Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] (G': AddSubgroup G) [Module.Finite ℤ G'] [Module.Free ℤ G'] (A' B' : Set G') (hA: IsShift A A') (hB: IsShift B B') [Finite A'] [Finite B'] [Nonempty A'] [Nonempty B'] : WeakPFRAsymmConclusion A' B' → WeakPFRAsymmConclusion A B := by
  intro this
  rcases this with ⟨ A'', B'', hA'', hB'', hA''_non, hB''_non, hcard_ineq, hdim_ineq ⟩
  rcases hA with ⟨ x, hA ⟩
  set f : G' → G := fun a ↦ (a : G) + x
  have hf : Function.Injective f := by
    intro y z hyz
    simp at hyz
    exact hyz
  have hA' : A = f '' A' := by
    simp_rw [hA, ← Set.image_vadd, Set.image_image, vadd_eq_add, add_comm]; rfl
  rcases hB with ⟨ y, hB ⟩
  set g : G' → G := fun a ↦ (a : G) + y
  have hg : Function.Injective g := by
    intro y z hyz
    simp at hyz
    exact hyz
  have hB' : B = g '' B' := by
    simp_rw [hB, ← Set.image_vadd, Set.image_image, vadd_eq_add, add_comm]; rfl
  use f '' A'', g '' B''
  have : dᵤ[A # B] = dᵤ[A' # B'] := by
    rw [<-rdist_set_of_inj _ _ (φ := G'.subtype) Subtype.val_injective, <-rdist_set_add_const (G'.subtype '' A') (G'.subtype '' B') x y]
    congr
    simp
    sorry
    sorry

  refine ⟨ ?_, ?_, (by infer_instance), (by infer_instance), ?_, ?_ ⟩
  . simp [hA', hf, hA'']
  . simp [hB', hg, hB'']
  . convert hcard_ineq using 2
    . congr 3
      . rw [hA', Nat.card_image_of_injective hf]
      . rw [hB', Nat.card_image_of_injective hg]
      . rw [Nat.card_image_of_injective hf]
      rw [Nat.card_image_of_injective hg]
  convert LE.le.trans _ hdim_ineq using 2
  norm_cast
  apply max_le_max
  . exact dimension_of_shift A'' x
  exact dimension_of_shift B'' y


/-- If $A,B\subseteq \mathbb{Z}^d$ are finite non-empty sets then there exist non-empty $A'\subseteq A$ and $B'\subseteq B$ such that
\[\log\frac{\lvert A\rvert\lvert B\rvert}{\lvert A'\rvert\lvert B'\rvert}\leq 44d[U_A;U_B]\]
such that $\max(\dim A',\dim B')\leq \frac{40}{\log 2} d[U_A;U_B]$. -/
lemma weak_PFR_asymm (A B : Set G) [Finite A] [Finite B] (hA : A.Nonempty) (hB : B.Nonempty) : WeakPFRAsymmConclusion A B  := by
  let P : ℕ → Prop := fun M ↦ (∀ (G : Type u) (hG_comm : AddCommGroup G) (_hG_free : Module.Free ℤ G) (_hG_fin : Module.Finite ℤ G) (_hG_count : Countable G) (hG_mes : MeasurableSpace G) (_hG_sing: MeasurableSingletonClass G) (A B: Set G) (_hA_fin: Finite A) (_hB_fin: Finite B) (_hA_non: Nonempty A) (_hB_non: Nonempty B) (_hM : (Nat.card A) + (Nat.card B) ≤ M), WeakPFRAsymmConclusion A B)
  suffices : ∀ M, (∀ M', M' < M → P M') → P M
  . set M := (Nat.card A) + (Nat.card B)
    have hM : (Nat.card A) + (Nat.card B) ≤ M := Nat.le_refl _
    convert (Nat.strong_induction_on (p := P) M this) G ‹_› ‹_› ‹_› ‹_› _ ‹_› A B ‹_› ‹_› ‹_› ‹_› hM
  intro M h_induct
  -- wlog we can assume A, B are not in cosets of a smaller subgroup
  suffices : ∀ (G : Type u) (hG_comm : AddCommGroup G) (_hG_free : Module.Free ℤ G) (_hG_fin : Module.Finite ℤ G) (_hG_count : Countable G) (hG_mes : MeasurableSpace G) (_hG_sing: MeasurableSingletonClass G) (A B: Set G) (_hA_fin: Finite A) (_hB_fin: Finite B) (_hA_non: Nonempty A) (_hB_non: Nonempty B) (_hM : (Nat.card A) + (Nat.card B) ≤ M) (_hnot: NotInCoset A B), WeakPFRAsymmConclusion A B
  . intro G hG_comm hG_free hG_fin hG_count hG_mes hG_sing A B hA_fin hB_fin hA_non hB_non hM

    obtain ⟨ G', A', B', hAA', hBB', hnot' ⟩ := wlog_notInCoset hA hB
    have hG'_fin : Module.Finite ℤ G' :=
      Module.Finite.iff_fg (N := AddSubgroup.toIntSubmodule G').2 (IsNoetherian.noetherian _)

    have hG'_free : Module.Free ℤ G' := by
      rcases Submodule.nonempty_basis_of_pid (Module.Free.chooseBasis ℤ G) (AddSubgroup.toIntSubmodule G') with ⟨ n, ⟨ b ⟩ ⟩
      exact Module.Free.of_basis b
    rw [hAA'.card_congr, hBB'.card_congr] at hM
    obtain ⟨ hA'_fin, hA'_non, hA'_card ⟩ := hA.card_congr
    obtain ⟨ hB'_fin, hB'_non, hB'_card ⟩ := card_of_shift hB
    rw [<-hA'_card, <-hB'_card] at hM
    replace this := this G' _ hG'_free hG'_fin (by infer_instance) (by infer_instance) (by infer_instance) A' B' hA'_fin hB'_fin hA'_non hB'_non hM hnot'
    exact conclusion_transfers G' A' B' hA hB this
  intro G hG_comm hG_free hG_fin hG_count hG_mes hG_sing A B hA_fin hB_fin hA_non hB_non hM hnot
  rcases weak_PFR_asymm_prelim A B with ⟨ N, x, y, Ax, By, hAx_non, hBy_non, hAx_fin, hBy_fin, hAx, hBy, hdim, hcard⟩
  have hAxA : Ax ⊆ A := by rw [hAx]; simp
  have hByB : By ⊆ B := by rw [hBy]; simp
  have hA_pos : (0 : ℝ) < Nat.card A := Nat.cast_pos.mpr Nat.card_pos
  have hB_pos : (0 : ℝ) < Nat.card B := Nat.cast_pos.mpr Nat.card_pos

  rcases lt_or_ge (Nat.card Ax + Nat.card By) (Nat.card A + Nat.card B) with h | h
  . replace h := h_induct (Nat.card Ax + Nat.card By) (h.trans_le hM) G hG_comm hG_free hG_fin hG_count hG_mes hG_sing Ax By (Set.finite_coe_iff.mpr hAx_fin) (Set.finite_coe_iff.mpr hBy_fin) hAx_non hBy_non (Eq.le rfl)
    rcases h with ⟨ A', B', hA', hB', hA'_non, hB'_non, hcard_ineq, hdim_ineq ⟩
    use A', B'
    have hAx_fin' := Set.finite_coe_iff.mpr hAx_fin
    have hBy_fin' := Set.finite_coe_iff.mpr hBy_fin
    have hA'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hAx_fin hA')
    have hB'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hBy_fin hB')
    have hAx_pos : (0 : ℝ) < Nat.card Ax := Nat.cast_pos.mpr Nat.card_pos
    have hBy_pos : (0 : ℝ) < Nat.card By := Nat.cast_pos.mpr Nat.card_pos
    have hA'_pos : (0 : ℝ) < Nat.card A' := Nat.cast_pos.mpr Nat.card_pos
    have hB'_pos : (0 : ℝ) < Nat.card B' := Nat.cast_pos.mpr Nat.card_pos
    have hAxA_le : (Nat.card Ax : ℝ) ≤ (Nat.card A : ℝ) := Nat.cast_le.mpr (Nat.card_mono A.toFinite hAxA)
    have hByB_le : (Nat.card By : ℝ) ≤ (Nat.card B : ℝ) := Nat.cast_le.mpr (Nat.card_mono B.toFinite hByB)

    refine ⟨ hA'.trans hAxA, hB'.trans hByB, hA'_non, hB'_non, ?_, ?_ ⟩
    . rw [four_logs hA_pos hB_pos hA'_pos hB'_pos]
      rw [four_logs hAx_pos hBy_pos hA'_pos hB'_pos] at hcard_ineq
      linarith only [hcard, hcard_ineq]
    apply hdim_ineq.trans
    gcongr
    linarith only [Real.log_le_log hAx_pos hAxA_le, Real.log_le_log hBy_pos hByB_le, hcard]
  use A, B
  refine ⟨ Eq.subset rfl, Eq.subset rfl, hA_non, hB_non, ?_, ?_ ⟩
  . apply LE.le.trans _ <| mul_nonneg (by norm_num) <| rdist_set_nonneg A B
    rw [div_self (by positivity)]
    simp
  have hAx_eq : Ax = A := by
    apply Set.Finite.eq_of_subset_of_card_le A.toFinite hAxA
    linarith only [h, Nat.card_mono B.toFinite hByB]
  have hBy_eq : By = B := by
    apply Set.Finite.eq_of_subset_of_card_le B.toFinite hByB
    linarith only [h, Nat.card_mono A.toFinite hAxA]
  have hN : N = ⊤ := by
    have : (A-A) ∪ (B-B) ⊆ N := by
      rw [← hAx_eq, ← hBy_eq, hAx, hBy]
      intro z hz
      simp [Set.mem_sub] at hz
      convert (QuotientAddGroup.eq_zero_iff z).mp ?_
      . infer_instance
      rcases hz with ⟨ a, ⟨ -, ha⟩, a', ⟨-, ha'⟩, haa' ⟩ | ⟨ b, ⟨ -, hb⟩, b', ⟨ -,hb'⟩, hbb' ⟩
      . rw [← haa']; simp [ha, ha']
      rw [← hbb']; simp [hb, hb']
    rw [← AddSubgroup.closure_le, hnot] at this
    exact top_le_iff.mp this
  have : Nat.card (G ⧸ N) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    . rw [hN]
      exact  QuotientAddGroup.subsingleton_quotient_top
    infer_instance
  simp [this] at hdim
  rw [← le_div_iff' (by positivity)] at hdim
  convert LE.le.trans ?_ hdim using 1
  . field_simp
  simp
  exact ⟨ dimension_le_rank A, dimension_le_rank B ⟩

/-- If $A\subseteq \mathbb{Z}^d$ is a finite non-empty set with $d[U_A;U_A]\leq \log K$ then there exists a non-empty $A'\subseteq A$ such that
$\lvert A'\rvert\geq K^{-22}\lvert A\rvert$
and $\dim A'\leq \frac{40}{\log 2} \log K$. -/
lemma weak_PFR {A : Set G} [Finite A] [Nonempty A]  {K : ℝ} (hK: 0 < K) (hdist: dᵤ[A # A] ≤ log K): ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-22 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ (40 / log 2) * log K := by
  rcases weak_PFR_asymm A A with ⟨A', A'', hA', hA'', hA'nonempty, hA''nonempty, hcard, hdim⟩

  have : ∃ B : Set G, B ⊆ A ∧ (Nat.card B) ≥ (Nat.card A') ∧ (Nat.card B) ≥ (Nat.card A'') ∧ (dimension B) ≤
max (dimension A') (dimension A'') := by
    rcases lt_or_ge (Nat.card A') (Nat.card A'') with h | h
    . use A''
      exact ⟨hA'', by linarith, by linarith, le_max_right _ _⟩
    use A'
    exact ⟨hA', by linarith, by linarith, le_max_left _ _⟩

  rcases this with ⟨B, hB, hBcard, hBcard', hBdim⟩
  use B
  have hApos : Nat.card A > 0 := by
    rw [gt_iff_lt, Nat.card_pos_iff]
    exact ⟨ (by infer_instance), (by infer_instance) ⟩
  have hA'pos : Nat.card A' > 0 := by
    rw [gt_iff_lt, Nat.card_pos_iff]
    refine ⟨ (by infer_instance), Finite.Set.subset _ hA' ⟩
  have hA''pos : Nat.card A'' > 0 := by
    rw [gt_iff_lt, Nat.card_pos_iff]
    refine ⟨ (by infer_instance), Finite.Set.subset _ hA'' ⟩
  have hBpos : Nat.card B > 0 := by linarith

  refine ⟨hB, ?_, ?_⟩
  . have := calc 2 * log ((Nat.card A) / (Nat.card B))
      _ = log ( ((Nat.card A) * (Nat.card A)) / ((Nat.card B) * (Nat.card B)) ) := by
        convert (log_pow (((Nat.card A) : ℝ)/(Nat.card B)) 2).symm
        field_simp
        rw [← pow_two, ← pow_two]
      _ ≤ log ( ((Nat.card A) * (Nat.card A)) / ((Nat.card A') * (Nat.card A'')) ) := by
        apply log_le_log
        . positivity
        gcongr
      _ ≤ 44 * dᵤ[A # A] := hcard
      _ ≤ 44 * log K := mul_le_mul_of_nonneg_left hdist (by linarith)
      _ = 2 * (22 * log K) := by ring
      _ = 2 * log (K^22) := by
        congr
        convert (log_pow K 22).symm
    rw [mul_le_mul_left (by norm_num), log_le_log_iff (by positivity) (by positivity), div_le_iff (by positivity), ← mul_inv_le_iff (by positivity), ← ge_iff_le, mul_comm] at this
    convert this using 2
    convert zpow_neg K 22 using 1
    norm_cast
  calc ((dimension B) : ℝ)
    _ ≤ (((max (dimension A') (dimension A'')) : ℕ) : ℝ) := by norm_cast
    _ ≤ (40 / log 2) * d[A # A] := hdim
    _ ≤ (40 / log 2) * log K := mul_le_mul_of_nonneg_left hdist (by positivity)


/-- Let $A\subseteq \mathbb{Z}^d$ and $\lvert A-A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-22}\lvert A\rvert$ and $\dim A' \leq \frac{40}{\log 2} \log K$.-/
theorem weak_PFR_int {A : Set G} [Finite A] [Nonempty A] {K : ℝ} (hK: 0 < K) (hA: Nat.card (A-A) ≤ K * Nat.card A) : ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-22 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ (40 / log 2) * log K := by
  apply weak_PFR hK ((rdist_set_le A A).trans _)
  suffices log (Nat.card (A-A)) ≤ log K + log (Nat.card A) by linarith
  rw [<-log_mul (by positivity) _]
  . apply log_le_log _ hA
    norm_cast
    have : Nonempty (A-A) := by
      have : Set.Nonempty A := Set.nonempty_coe_sort.mp ‹_›
      exact Set.Nonempty.coe_sort (Set.Nonempty.sub this this)
    apply Nat.card_pos
  norm_cast
  apply ne_of_gt Nat.card_pos
