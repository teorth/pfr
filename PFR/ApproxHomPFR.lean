import PFR.HomPFR
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The approximate homomorphism form of PFR

Here we apply PFR to show that almost homomorphisms f from a 2-group to a 2-group often coincide with a (shifted) actual homomorphisms.  Here, approximate is in the sense that f(x+y)=f(x)+f(y) is true for a positive proportion of x,y.

## Main result

* `approx_hom_pfr` : If $f: G → G'$ is a map between finite abelian elementary 2-groups such that $f(x+y)=f(x)+f(y)$ for at least $|G|/K$ values, then then there is a homomorphism $\phi: G \to G'$ and a constant $c$ such that $f(x)=\phi(x)+c$ for a substantial set of values.

-/
open Pointwise Classical

variable {G : Type*} [AddCommGroup G] (A : Finset G)

/-- If $G$ is a group, and $A$ is a finite subset of $G$, the \emph{additive energy} $E(A)$ of $A$ is the number of quadruples $(a_1,a_2,a_3,a_4) \in A^4$ such that $a_1+a_2 = a_3+a_4$. -/
notation3:max "E[" A "]" => Finset.additiveEnergy A A

lemma nat_cauchy_schwartz {B : Type*} [Fintype B] (v w : B → ℕ) :
  (Finset.univ.sum (v * w))^2 ≤ Finset.univ.sum (v^2) * Finset.univ.sum (w^2) := by
  rify
  let x : EuclideanSpace ℝ B := fun i ↦ (v i : ℝ)
  let y : EuclideanSpace ℝ B := fun i ↦ (w i : ℝ)
  have := abs_real_inner_le_norm x y
  rw [PiLp.inner_apply, ((abs_eq (mul_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
    (abs_eq_abs.mp rfl)).symm, ←sq_le_sq, mul_pow, EuclideanSpace.norm_eq,EuclideanSpace.norm_eq] at this
  rw [Real.sq_sqrt, Real.sq_sqrt] at this
  · simp only [IsROrC.norm_natCast] at this
    simp only [Real.sq_sqrt, Real.sq_sqrt, IsROrC.norm_natCast, Pi.mul_apply, Nat.cast_mul,
      Pi.pow_apply, Nat.cast_pow, ge_iff_le]
    exact this
  all_goals { apply Finset.sum_nonneg (fun i _ ↦ sq_nonneg _) }

lemma nat_cauchy_schwartz' {X : Type*} (B : Finset X) (v w : X → ℕ) :
  (B.sum (v * w))^2 ≤ B.sum (v^2) * B.sum (w^2) := by
  have := nat_cauchy_schwartz (fun b : B => v b) (fun b : B => w b)
  rwa [←(show Finset.univ.sum (fun b : B => (v * w) b) = B.sum (v * w) from Finset.sum_attach),
    ←(show Finset.univ.sum (fun b : B => (v^2 : X → ℕ) b) = B.sum (v^2) from Finset.sum_attach),
    ←(show Finset.univ.sum (fun b : B => (w^2 : X → ℕ) b) = B.sum (w^2) from Finset.sum_attach)]

/--  If $G$ is a group, $A,B$ are finite subsets of $G$, then
$$ E(A) \geq \frac{|\{ (a,a') \in A \times A: a+a' \in B \}|^2}{|B|}.$$ -/
lemma cauchy_schwarz (A B : Finset G) :
  ((A ×ˢ A).filter (fun (a : G × G) => a.fst + a.snd ∈ B)).card^2 ≤ B.card * E[A] := by
  let r : G → ℕ := fun g => ((A ×ˢ A).filter (fun (a : G × G) => a.fst + a.snd = g)).card
  let T : Finset G := (A ×ˢ A).image (fun a => a.fst + a.snd)
  -- This should be a bit easier with a little extra API for additive energy
  have counting : E[A] = T.sum (fun b => (r b)^2)
  · let S := ((A ×ˢ A) ×ˢ A ×ˢ A).filter (fun (x : (G × G) × G × G) => x.1.1 + x.2.1 = x.1.2 + x.2.2)
    have temp : ∀ x : (G × G) × G × G, x ∈ S → x.1.2 + x.2.2 ∈ T
    · intro x hx
      rw [Finset.mem_image]
      use (x.1.2, x.2.2)
      refine ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp (Finset.mem_product.mp
        (Finset.mem_filter.mp hx).left).left).right, (Finset.mem_product.mp
        (Finset.mem_product.mp (Finset.mem_filter.mp hx).left).right).right⟩, rfl⟩
    rw [(show E[A] = S.card from rfl), Finset.card_eq_sum_card_fiberwise temp]
    suffices card_fiber : ∀ (g : G), g ∈ T →
      (S.filter (fun (x : (G × G) × G × G) => x.1.2 + x.2.2 = g)).card = (r g)^2
    · rw [Finset.sum_congr rfl card_fiber]
    suffices : ∀ (g : G), g ∈ T → S.filter (fun (x : (G × G) × G × G) => x.1.2 + x.2.2 = g)
      = (((A ×ˢ A).filter (fun x => x.1 + x.2 = g)) ×ˢ ((A ×ˢ A).filter (fun x => x.1 + x.2 = g))).image
      (fun x => ((x.1.1, x.2.1), x.1.2, x.2.2))
    · intro g hg
      rw [this g hg]
      simp only [Finset.mem_product, and_imp, Prod.forall, Finset.card_product,
        Finset.filter_congr_decidable, pow_two]
      rw [Finset.card_image_of_injective]
      · simp only [Finset.mem_product, and_imp, Prod.forall, Finset.card_product]
      · intro x y h
        simp only [Prod.mk.injEq] at h
        rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
        refine ⟨⟨h.left.left, h.right.left⟩, h.left.right, h.right.right⟩
    intro g _
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [Finset.mem_image]
      use ((x.1.1, x.2.1), x.1.2, x.2.2)
      refine ⟨?_, rfl⟩
      rw [Finset.mem_product]
      rw [Finset.mem_filter] at hx ⊢
      constructor
      · simp only [Finset.mem_product]
        constructor
        · exact ⟨(Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).left).left,
          (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).right).left⟩
        · rw [(Finset.mem_filter.mp hx.left).right, hx.right]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp
          (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).left).right,
          (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).right).right⟩, hx.right⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ha.right.right⟩
      · simpa only [Finset.mem_product, Finset.mem_product, Finset.mem_product] using
          ⟨⟨ha.left.left.left, ha.right.left.left⟩, ha.left.left.right, ha.right.left.right⟩
      · rw [ha.left.right, ha.right.right]
  have rhs : ((A ×ˢ A).filter (fun (a : G × G) => a.fst + a.snd ∈ B)).card = B.sum r
  · rw [Finset.card_eq_sum_card_fiberwise (fun x hx => (Finset.mem_filter.mp hx).right)]
    apply Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.filter_filter]
    apply congr_arg _  (Finset.filter_congr (fun u _ => ⟨fun hu' => hu'.2, fun hu' => ⟨by rwa [hu'], hu'⟩⟩))
  suffices cauchy_schwarz : (B.sum r)^2 ≤ B.card * B.sum (fun b => (r b)^2)
  · rw [rhs]
    apply le_trans cauchy_schwarz _
    calc B.card * B.sum (fun b => (r b)^2) = B.card * (T ∩ B).sum (fun b => (r b)^2) := by
              suffices : B.sum (fun b => (r b)^2) = (T ∩ B).sum (fun b => (r b)^2)
              · rw [this]
              symm
              rw [Finset.sum_subset ((Finset.inter_subset_right T B))]
              intro x hx hx'
              rw [pow_two]
              have not_in : x ∉ T := fun hx'' => hx' (Finset.mem_inter_of_mem hx'' hx)
              have : ∀ y : G, y ∉ T → r y = 0
              · intro y hy
                rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
                intro t ht
                simp_rw [Finset.mem_filter] at ht hy
                simp_rw [Finset.mem_image] at hy
                apply hy ; use t
              rw [this x not_in, mul_zero]
        _ ≤ B.card * T.sum (fun b => (r b)^2) := by
              apply Nat.mul_le_mul_left
              rw [←Finset.sum_sdiff (Finset.inter_subset_left T B)]
              apply Nat.le_add_left _ _
        _ = B.card * E[A] := by rw [counting]
  have := nat_cauchy_schwartz' B r (fun _ => 1)
  have simp₁ : B.sum ((fun b => 1)^2) = B.card
  · simp only [Pi.pow_apply, one_pow, Finset.sum_const, smul_eq_mul, mul_one]
  have simp₂ : B.sum (r * fun g => 1) = B.sum r
  · simp only [Finset.mem_product, and_imp, Prod.forall, Pi.mul_apply, mul_one]
  rwa [simp₁, simp₂, mul_comm] at this


-- These are provisional values of constants, subject to change.  May also want to localize these definitions to just this file

def C₁ := 2^4
def C₂ := 1
def C₃ := 2^10
def C₄ := 4

/-- Let $G$ be an abelian group, and let $A$ be a finite non-empty set with $E(A) \geq |A|^3 / K$ for some $K \geq 1$.  Then there is a subset $A'$ of $A$ with $|A'| \geq |A| / (C_1 K^{C_2})$ and $|A'-A'| \leq C_3 K^{C_4} |A'|$ -/
lemma bsg (A : Finset G) (K : ℝ) (hK: 0 < K) (hE: E[A] ≥ (A.card)^3 / K): ∃ A' : Finset G, A' ⊆ A ∧ A'.card ≥ A.card / (C₁ * K^C₂) ∧ (A' - A').card ≤ C₃ * K^C₄ * A'.card := sorry


variable {G G' : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G']
  [ElementaryAddCommGroup G 2] [ElementaryAddCommGroup G' 2]

/-- Let $G,G'$ be finite abelian $2$-groups.
  Let $f: G \to G'$ be a function, and suppose that there are at least $|G|^2 / K$ pairs $(x,y) \in G^2$ such that
$$ f(x+y) = f(x) + f(y).$$
Then there exists a homomorphism $\phi: G \to G'$ and a constant $c \in G'$ such that $f(x) = \phi(x)+c$ for at least $|G| / 4C_1^{25} C_3^{24} K^{50C_4+48 C_2}$ values of $x \in G$. -/
theorem approx_hom_pfr (f : G → G') (K : ℝ) (hK: K > 0) (hf: Nat.card { x : G × G| f (x.1+x.2) = (f x.1) + (f x.2) } ≥ (Nat.card G)^2/ K) : ∃ (φ : G →+ G') (c : G'), Nat.card { x : G | f x = φ x + c } ≥ (Nat.card G) / (4 * C₁^25 * C₃^24 * K^(50 * C₄ + 48 * C₂)) := sorry
