import PFR.ForMathlib.CompactProb
import PFR.MoreRuzsaDist
import PFR.kullback

/-!
# The rho functional

Definition of the rho functional and basic facts

## Main definitions:

## Main results

-/

open MeasureTheory ProbabilityTheory
open scoped Pointwise
universe uG

variable {G : Type uG} [AddCommGroup G]  [Fintype G] [MeasurableSpace G]

/-- For any $G$-valued random variable $X$, we define $\rho^-(X)$ to be the infimum of $D_{KL}(X \Vert  U_A + T)$, where $U_A$ is uniform on $A$ and $T$ ranges over $G$-valued random variables independent of $U_A$. -/
noncomputable def rho_minus {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ := sInf { x:ℝ | ∃ (Ω':Type uG) (mΩ':MeasureSpace Ω') (T : Ω' → G) (U: Ω' → G), (IsUniform A U) ∧ (IndepFun T U) ∧ (x = KL[ X # T + U])}

/-- For any $G$-valued random variable $X$, we define $\rho^+(X) := \rho^-(X) + \bbH(X) - \bbH(U_A)$. -/
noncomputable def rho_plus {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ := (rho_minus X A) + H[ X ] - Real.log (Nat.card A)

/-- We have $\rho^-(X) \geq 0$. -/
lemma rho_minus_nonneg {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : rho_minus X A ≥ 0 := sorry

-- the spelling below can likely be improved.
/-- If $H$ is a finite subgroup of $G$, then $\rho^-(U_H) = \log |A| - \log \max_t |A \cap (H+t)|$. -/
lemma rho_minus_of_subgroup (H : AddSubgroup G) {Ω : Type*} [MeasureSpace Ω]
    (U : Ω → G) (hunif: IsUniform H U) (A : Finset G) : rho_minus U A = Real.log (Nat.card A) - Real.log (sSup (Set.range fun t:G ↦ Nat.card ((A:Set G) ∩ (t +ᵥ H.carrier) : Set G))) := sorry

/--  If $H$ is a finite subgroup of $G$, then $\rho^+(U_H) = \log |H| - \log \max_t |A \cap (H+t)|$. -/
lemma rho_plus_of_subgroup : 0 = 1 := sorry

/--  We define $\rho(X) := (\rho^+(X) + \rho^-(X))/2$. -/
noncomputable def rho {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ := ((rho_minus X A) + (rho_plus X A))/2

/-- We have $\rho(U_A) = 0$. -/
lemma rho_of_uniform {Ω : Type*} [MeasureSpace Ω]
    (U : Ω → G) (A : Finset G) (hunif: IsUniform A U) : rho U A = 0 := sorry

/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such that $|A \cap (H+t)| \geq 2^{-r} \sqrt{|A||H|}$, and $|H|/|A|\in[2^{-2r},2^{2r}]$. -/
lemma rho_of_subgroup : 0 = 1 := by sorry

/-- For any $s \in G$, $\rho(X+s) = \rho(X)$. -/
lemma rho_of_translate {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) (s:G) : rho (fun ω ↦ X ω + s) A = rho X A := by sorry

/-- \rho(X)$ depends continuously on the distribution of $X$. -/
lemma rho_continuous : 0 = 1 := by sorry

/-- If $X,Y$ are independent, one has
  $$ \rho^-(X+Y) \leq \rho^-(X)$$ -/
lemma rho_minus_of_sum  {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) : rho_minus (X+Y) A ≤ rho_minus X A := by sorry


/-- If $X,Y$ are independent, one has
$$ \rho^+(X+Y) \leq \rho^+(X) + \bbH[X+Y] - \bbH[X]$$ -/
lemma rho_plus_of_sum  {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) : rho_plus (X+Y) A ≤ rho_plus X A + H[X+Y] - H[X] := by sorry

/-- If $X,Y$ are independent, one has
  $$ \rho(X+Y) \leq \rho(X) + \frac{1}{2}( \bbH[X+Y] - \bbH[X] ).$$
  -/
lemma rho_of_sum {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) : rho (X+Y) A ≤ rho X A + (H[X+Y] - H[X])/2 := by sorry

-- This may not be the optimal spelling for condRho, feel free to improve
/-- We define $\rho(X|Y) := \sum_y {\bf P}(Y=y) \rho(X|Y=y)$. -/
noncomputable def condRho {Ω S : Type*} [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) : ℝ := ∑' s, (volume (Y ⁻¹' {s})).toReal * @rho G _ _ Ω ⟨ ProbabilityTheory.cond volume (Y⁻¹' {s}) ⟩ X A

noncomputable def condRho_minus {Ω S : Type*} [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) : ℝ := ∑' s, (volume (Y ⁻¹' {s})).toReal * @rho_minus G _ _ Ω ⟨ ProbabilityTheory.cond volume (Y⁻¹' {s}) ⟩ X A

noncomputable def condRho_plus {Ω S : Type*} [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) : ℝ := ∑' s, (volume (Y ⁻¹' {s})).toReal * @rho_plus G _ _ Ω ⟨ ProbabilityTheory.cond volume (Y⁻¹' {s}) ⟩ X A


/-- For any $s\in G$, $\rho(X+s|Y)=\rho(X|Y)$. -/
lemma condRho_of_translate {Ω S : Type*} [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) (s:G) : condRho (fun ω ↦ X ω + s) Y A = condRho X Y A := by sorry

/-- If $f$ is injective, then $\rho(X|f(Y))=\rho(X|Y)$. -/
lemma condRho_of_injective {Ω S T : Type*} [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) (f: S → T) (hf: Function.Injective f) : condRho X (f ∘ Y) A = condRho X Y A := by sorry

/--   $$ \rho^-(X|Z) \leq \rho^-(X) + \bbH[X] - \bbH[X|Z]$$ -/
lemma condRho_minus_le {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S] (X : Ω → G) (Z : Ω → S) (A : Finset G) : condRho_minus X Z A ≤ rho_minus X A + H[ X ] - H[ X | Z ] := by sorry

/-- $$ \rho^+(X|Z) \leq \rho^+(X)$$ -/
lemma condRho_plus_le {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S] (X : Ω → G) (Z : Ω → S) (A : Finset G) : condRho_plus X Z A ≤ rho_plus X A := by sorry

/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z] )$$ -/
lemma condRho_le {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S] (X : Ω → G) (Z : Ω → S) (A : Finset G) : condRho X Z A ≤ rho X A + (H[ X ] - H[ X | Z ]) / 2 := by sorry

variable [ElementaryAddCommGroup G 2]

/-- If $X,Y$ are independent, then
  $$ \rho(X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$
 -/
lemma rho_of_sum_le {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) : rho (X + Y) A ≤ (rho X A + rho Y A + d[ X # Y ]) / 2 := by sorry

/--   If $X,Y$ are independent, then
  $$ \rho(X | X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$ -/
lemma condRho_of_sum_le {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) : condRho X (X + Y) A ≤ (rho X A + rho Y A + d[ X # Y ]) / 2 := by sorry
