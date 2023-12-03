import PFR.Main

open Pointwise

variable {G G' : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [AddCommGroup G'] [ElementaryAddCommGroup G' 2] [Fintype G']

/-- Let $H_0$ be a subgroup of $G$.  Then every homomorphism $\phi: H_0 \to G'$ can be extended to a homomorphism $\tilde \phi: G \to G'$. -/
lemma hahn_banach (H₀ : AddSubgroup G) (φ : H₀ →+ G') : ∃ (φ' : G →+ G'), ∀ x : H₀, φ x = φ' x := by
  haveI : ElementaryAddCommGroup H₀ 2 := ElementaryAddCommGroup.subgroup _
  let ι := ElementaryAddCommGroup.linearMap H₀.subtype
  have hι : Function.Injective ι :=
    show Function.Injective H₀.subtype from AddSubgroup.subtype_injective H₀
  have : LinearMap.ker ι = ⊥ := by exact LinearMap.ker_eq_bot.mpr hι
  obtain ⟨g,hg⟩ := LinearMap.exists_leftInverse_of_injective ι this
  use φ.comp g.toAddMonoidHom
  intro x
  show φ x = φ ((g.comp ι) x)
  rw [hg]
  rfl

/-- Let $H$ be a subgroup of $G \times G'$.  Then there exists a subgroup $H_0$ of $G$, a subgroup $H_1$ of $G'$, and a homomorphism $\phi: G \to G'$ such that
$$ H := \{ (x, \phi(x) + y): x \in H_0, y \in H_1 \}.$$
In particular, $|H| = |H_0| |H_1|$. -/
lemma goursat (H : AddSubgroup (G × G')): ∃ (H₀ : AddSubgroup G) (H₁ : AddSubgroup G') (φ : G →+ G'),
    (∀ x : G × G', x ∈ H ↔ (x.1 ∈ H₀ ∧ x.2 - φ x.1 ∈ H₁)) ∧
    (Nat.card H) = (Nat.card H₀) * (Nat.card H₁) := by
  let π₁ := AddMonoidHom.fst G G'
  let π₂ := AddMonoidHom.snd G G'
  let p₁ := AddMonoidHom.addSubgroupMap π₁ H
  let p₂ := AddMonoidHom.addSubgroupMap π₂ (H ⊓ π₁.ker)
  let H₀ := AddSubgroup.map π₁ H
  let H₁ := AddSubgroup.map π₂ (H ⊓ π₁.ker)
  have : ElementaryAddCommGroup H 2 := ElementaryAddCommGroup.subgroup H
  have : ElementaryAddCommGroup H₀ 2 := ElementaryAddCommGroup.subgroup H₀
  let p₁' := ElementaryAddCommGroup.linearMap p₁
  obtain ⟨ φ', hφ' ⟩ := LinearMap.exists_rightInverse_of_surjective p₁'
    (LinearMap.range_eq_top.mpr (AddMonoidHom.addSubgroupMap_surjective π₁ H))
  obtain ⟨ φ, hφ ⟩ := hahn_banach H₀ ((π₂.restrict H).comp φ'.toAddMonoidHom)

  let bij (x : H) : G × G' := (x.val.1, x.val.2 - φ x.val.1)
  let bij_inv (x : H₀ × H₁) : G × G' := (x.1.val, φ x.1.val + x.2.val)
  have h_bij' : ∀ x : G × G', x ∈ H ↔ (x.1 ∈ H₀ ∧ x.2 - φ x.1 ∈ H₁) := by
    intro x
    constructor

    intro hx
    let x₁ : H₀ := ⟨ x.1, AddSubgroup.mem_map_of_mem π₁ hx ⟩
    let x₂ : H := { val := x, property := hx } - (φ' x₁)
    have h_ker : x₂.val ∈ π₁.ker := by
      show π₁ x - p₁'.comp φ' x₁ = 0
      rw [sub_eq_zero, hφ', show LinearMap.id x₁ = π₁ x from rfl]
    constructor
    exact AddSubgroup.mem_map_of_mem (K := H) π₁ hx
    rw [← hφ x₁]
    exact AddSubgroup.mem_map_of_mem (K := H ⊓ π₁.ker) π₂ (Set.mem_inter x₂.property h_ker)

    intro hx
    let x₁ : H₀ := ⟨ x.1, hx.left ⟩
    let x₂ : H₁ := ⟨ x.2 - φ x₁, hx.right ⟩
    let xₗ : H := φ' x₁
    let xᵣ : G × G' := (0, x₂.val)
    have hxₗ : xₗ.val = (x.1, φ x₁) := by
      have hx₁ : xₗ.val.1 = x.1 := by
        rw [show xₗ.val.1 = p₁'.comp φ' x₁ from rfl, hφ', show LinearMap.id x₁ = x.1 from rfl]
      exact Prod.ext hx₁ (hφ x₁)
    have hxᵣ : xᵣ ∈ H := by
      obtain ⟨ g, hg ⟩ := Set.Nonempty.preimage (Set.singleton_nonempty x₂)
        (AddMonoidHom.addSubgroupMap_surjective π₂ (H ⊓ π₁.ker))
      have h_ker : g.val ∈ H ∧ g.val ∈ π₁.ker := AddSubgroup.mem_inf.mp g.property
      have hg₁ : g.val.1 = xᵣ.1 := (AddMonoidHom.mem_ker π₁).mp h_ker.right
      have hg₂ : g.val.2 = xᵣ.2 := by { show (p₂ g).val = x₂.val ; rw [← hg] }
      rw [← Prod.ext hg₁ hg₂]
      exact h_ker.left
    let xᵣ : H := ⟨ xᵣ, hxᵣ ⟩
    have hx : x = xₗ.val + xᵣ.val := by
      rw [hxₗ, show xᵣ = _ from rfl, Prod.mk_add_mk, add_zero, ← add_comm_sub, sub_self, zero_add]
    rw [hx]
    exact (xₗ + xᵣ).property

  have h_bij_prop (x : H) : (bij x).1 ∈ H₀ ∧ (bij x).2 ∈ H₁ := (h_bij' x.val).mp x.property
  let bij (x : H) : H₀ × H₁ := (⟨ (bij x).1, (h_bij_prop x).1 ⟩, ⟨ (bij x).2, (h_bij_prop x).2 ⟩)
  have h_bij_inv_prop (x : H₀ × H₁) : bij_inv x ∈ H := (h_bij' (bij_inv x)).mpr
    ⟨ x.1.property, by simp only [x.2.property, add_comm, add_sub_assoc, sub_self, add_zero] ⟩
  let bij_inv (x : H₀ × H₁) : H := ⟨ bij_inv x, h_bij_inv_prop x ⟩
  have h_leftinv : Function.LeftInverse bij_inv bij := fun _ ↦ by
    simp_rw [← add_comm_sub, sub_self, zero_add]
  have h_rightinv : Function.RightInverse bij_inv bij := fun _ ↦ by
    simp_rw [add_comm, add_sub_assoc, sub_self, add_zero]
  have h_bij : Function.Bijective bij :=
    Function.bijective_iff_has_inverse.mpr ⟨ bij_inv, ⟨ h_leftinv, h_rightinv ⟩ ⟩

  use H₀, H₁, φ
  constructor
  exact h_bij'
  rw [Nat.card_eq_of_bijective bij h_bij, Nat.card_prod H₀ H₁]

/-- Let $f: G \to G'$ be a function, and let $S$ denote the set
$$ S := \{ f(x+y)-f(x)-f(y): x,y \in G \}.$$
Then there exists a homomorphism $\phi: G \to G'$ such that
$$ |\{ f(x) - \phi(x)\}| \leq 4 |S|^{24}.$$ -/
theorem homomorphism_pfr (f : G → G') (S : Set G') (hS: ∀ x y : G, f (x+y) - (f x) - (f y) ∈ S): ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S)^24 ∧ ∀ x : G, (f x) - (φ x) ∈ T := by sorry
