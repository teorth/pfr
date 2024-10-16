import PFR.ForMathlib.CompactProb
import PFR.MoreRuzsaDist
import PFR.kullback
import PFR.Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The rho functional

Definition of the rho functional and basic facts

## Main definitions:

## Main results

-/

open MeasureTheory ProbabilityTheory
open scoped Pointwise
universe uG

local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))

variable {G : Type uG} [AddCommGroup G]  [Fintype G] [hGm: MeasurableSpace G]

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
lemma rho_plus_of_subgroup (H : AddSubgroup G) {Ω : Type*} [MeasureSpace Ω]
    (U : Ω → G) (hunif: IsUniform H U) (A : Finset G) : rho_plus U A = Real.log (Nat.card H) - Real.log (sSup (Set.range fun t:G ↦ Nat.card ((A:Set G) ∩ (t +ᵥ H.carrier) : Set G))):= sorry

/--  We define $\rho(X) := (\rho^+(X) + \rho^-(X))/2$. -/
noncomputable def rho {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ := ((rho_minus X A) + (rho_plus X A))/2

/-- We have $\rho(U_A) = 0$. -/
lemma rho_of_uniform {Ω : Type*} [MeasureSpace Ω]
    (U : Ω → G) (A : Finset G) (hunif: IsUniform A U) : rho U A = 0 := sorry

-- for some reason I need multiple casts to `Set G` to make this compile
/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such that $|A \cap (H+t)| \geq 2^{-r} \sqrt{|A||H|}$, and $|H|/|A|\in[2^{-2r},2^{2r}]$. -/
lemma rho_of_subgroup (H: AddSubgroup G)  {Ω : Type*} [MeasureSpace Ω] (U : Ω → G) (hunif: IsUniform H U) (A : Finset G) (r:ℝ) (hr: rho U A ≤ r) : ∃ t:G, Nat.card ((A:Set G) ∩ ((t +ᵥ H.carrier)) : Set G) ≤ 2^(-r) * (Nat.card A * Nat.card H)^(1/2) ∧ Nat.card A ≤ 2^(2*r) * Nat.card H ∧ Nat.card H ≤ 2^(2*r) * Nat.card A := by sorry

/-- For any $s \in G$, $\rho(X+s) = \rho(X)$. -/
lemma rho_of_translate {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) (s:G) : rho (fun ω ↦ X ω + s) A = rho X A := by sorry

/-- \rho(X)$ depends continuously on the distribution of $X$. -/
lemma rho_continuous [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] : Continuous
      (fun (μ: ProbabilityMeasure G) ↦ @rho G _ hGm G ⟨ μ ⟩ id A) := by sorry

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
lemma condRho_of_translate {Ω S : Type*} [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) (s:G) : condRho (fun ω ↦ X ω + s) Y A = condRho X Y A := by
  simp only [condRho, rho_of_translate]

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



section phiMinimizer

noncomputable def phi {Ω: Type*} [MeasureSpace Ω] (X Y : Ω → G) (η:ℝ) (A: Finset G)  : ℝ := d[ X # Y ] + η * (rho X A + rho Y A)

/--  Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$
and define a \emph{$\phi$-minimizer} to be a pair of random variables $X,Y$ which minimizes $\phi[X;Y]$.-/
def phiMinimizes {Ω: Type uG} [MeasureSpace Ω] (X Y : Ω → G) (η:ℝ) (A: Finset G) : Prop := ∀ (Ω': Type uG) (_: MeasureSpace Ω') (X' Y' : Ω' → G), phi X Y η A ≤ phi X' Y' η A

variable (η:ℝ) (hη: η > 0) (A: Finset G)

/-- There exists a $\phi$-minimizer. -/
lemma phi_min_exists : ∃ (Ω: Type uG) (_:MeasureSpace Ω) (X Y : Ω → G), phiMinimizes X Y η A := by sorry

-- Let $(X_1, X_2)$ be a $\phi$-minimizer, and $\tilde X_1, \tilde X_2$ be independent copies of $X_1,X_2$ respectively.
variable {Ω: Type uG} [MeasureSpace Ω] (X₁ X₂ X'₁ X'₂ : Ω → G) (hmin: phiMinimizes X₁ X₂ η A) (hident₁: IdentDistrib X₁ X'₁) (hident₁: IdentDistrib X₂ X'₂) (hindep: iIndepFun (fun _ ↦ hGm) ![X₁, X₂, X'₁, X'₂])

local notation3 "I₁" => I[X₁ + X₂ : X'₁ + X₂ | X₁ + X₂ + X'₁ + X'₂]
local notation3 "I₂" => I[X₁ + X₂ : X₁ + X'₁ | X₁ + X₂ + X'₁ + X'₂]

/-- $I_1\le 2\eta d[X_1;X_2]$ -/
lemma I_one_le : I₁ ≤ 2 * η * d[ X₁ # X₂ ] := by sorry

/--   $d[X_1;X_1]+d[X_2;X_2]= 2d[X_1;X_2]+(I_2-I_1)$. -/
lemma dist_add_dist_eq : d[ X₁ # X₁ ] + d[ X₂ # X₂ ] = 2 * d[ X₁ # X₂ ] + (I₂ - I₁) := by sorry

/-- $I_2\le 2\eta d[X_1;X_2] + \frac{\eta}{1-\eta}(2\eta d[X_1;X_2]-I_1)$. -/
lemma I_two_le : I₂ ≤ 2 * η * d[ X₁ # X₂ ] + (η / (1 - η)) * (2 * η * d[ X₁ # X₂ ] - I₁) := by sorry

/--   If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])+ \eta(\rho(T_1|T_3)+\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero {Ω': Type uG} [MeasureSpace Ω'] (T₁ T₂ T₃ : Ω' → G) (hsum: T₁ + T₂ + T₃ = 0) : d[ X₁ # X₂ ] ≤ 3 * I[T₁ : T₂ | T₃] + (2 * H[T₃] - H[T₁] - H[T₂]) + η * (condRho T₁ T₃ A + condRho T₂ T₃ A - rho X₁ A - rho X₂ A) := by sorry

/--   If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2] \leq  \sum_{1 \leq i < j \leq 3} \bbI[T_i:T_j] + \frac{\eta}{3}   \sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j) + \rho(T_j|T_i) -\rho(X_1)-\rho(X_2))$$
-/
lemma dist_le_of_sum_zero' {Ω': Type uG} [MeasureSpace Ω'] (T₁ T₂ T₃ : Ω' → G) (hsum: T₁ + T₂ + T₃ = 0) : d[ X₁ # X₂ ] ≤ I[T₁ : T₂] + I[T₁ : T₃] + I[T₂ : T₃] + (η/3) * ( ( condRho T₁ T₂ A + condRho T₂ T₁ A - rho X₁ A - rho X₂ A) +
( condRho T₁ T₃ A + condRho T₃ T₁ A - rho X₁ A - rho X₂ A) + ( condRho T₂ T₃ A + condRho T₃ T₂ A - rho X₁ A - rho X₂ A) ) := sorry

/--   For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define $S:=Y_1+Y_2+Y_3+Y_4$, $T_1:=Y_1+Y_2$, $T_2:=Y_1+Y_3$. Then
  $$\rho(T_1|T_2,S)+\rho(T_2|T_1,S) - \frac{1}{2}\sum_{i} \rho(Y_i)\le \frac{1}{2}(d[Y_1;Y_2]+d[Y_3;Y_4]+d[Y_1;Y_3]+d[Y_2;Y_4]).$$
-/
lemma condRho_sum_le {Ω': Type uG} [MeasureSpace Ω'] (Y₁ Y₂ Y₃ Y₄ : Ω' → G) (hindep: iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) :
  let S := Y₁ + Y₂ + Y₃ + Y₄
  let T₁ := Y₁ + Y₂
  let T₂ := Y₁ + Y₃
  condRho T₁ T₂ A + condRho T₂ T₁ A - (rho Y₁ A + rho Y₂ A + rho Y₃ A + rho Y₄ A)/2 ≤ (d[ Y₁ # Y₂ ] + d[ Y₃ # Y₄ ] + d[ Y₁ # Y₃ ] + d[ Y₂ # Y₄ ]) / 2 := by sorry

/--   For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define $T_1:=Y_1+Y_2,T_2:=Y_1+Y_3,T_3:=Y_2+Y_3$ and $S:=Y_1+Y_2+Y_3+Y_4$. Then
  $$\sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j,S) + \rho(T_j|T_i,S) -  \frac{1}{2}\sum_{i} \rho(Y_i))\le \sum_{1\leq i < j \leq 4}d[Y_i;Y_j]$$ -/
lemma condRho_sum_le' {Ω': Type uG} [MeasureSpace Ω'] (Y₁ Y₂ Y₃ Y₄ : Ω' → G) (hindep: iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) :
  let S := Y₁ + Y₂ + Y₃ + Y₄
  let T₁ := Y₁ + Y₂
  let T₂ := Y₁ + Y₃
  let T₃ := Y₂ + Y₃
  condRho T₁ T₂ A + condRho T₂ T₁ A + condRho T₁ T₃ A + condRho T₃ T₁ A + condRho T₂ T₃ A + condRho T₃ T₂ A - 3*(rho Y₁ A + rho Y₂ A + rho Y₃ A + rho Y₄ A)/2 ≤ d[ Y₁ # Y₂ ] + d[ Y₁ # Y₃ ] + d[ Y₁ # Y₄ ] + d[ Y₂ # Y₃ ] + d[ Y₂ # Y₄ ] + d[ Y₃ # Y₄ ] := by sorry

/-- If $X_1,X_2$ is a $\phi$-minimizer, then $d[X_1;X_2] = 0$. -/
lemma dist_of_min_eq_zero (hη': η < 1/8) : d[ X₁ # X₂ ] = 0 := by sorry

end phiMinimizer

/-- For any random variables $Y_1,Y_2$, there exist a subgroup $H$ such that
  $$ 2\rho(U_H) \leq \rho(Y_1) + \rho(Y_2) + 8 d[Y_1;Y_2].$$ -/
theorem rho_PFR_conjecture (η:ℝ) (hη: η > 0) (hη': η < 1/8) {Ω: Type uG} [MeasureSpace Ω] (Y₁ Y₂: Ω → G) (A: Finset G):
    ∃ (H : AddSubgroup G) (Ω' : Type uG) (mΩ' : MeasureSpace Ω) (U : Ω → G),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ 2 * rho U A ≤ rho Y₁ A + rho Y₂ A + 8 * d[Y₁ # Y₂] := sorry


open scoped Pointwise

/-- If $|A+A| \leq K|A|$, then there exists a subgroup $H$ and $t\in G$ such that $|A \cap (H+t)| \geq K^{-4} \sqrt{|A||V|}$, and $|H|/|A|\in[K^{-8},K^8]$.
\end{corollary} -/
lemma better_PFR_conjecture_aux {A: Set G} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ 4 * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ 8 * Nat.card A ∧ Nat.card A ≤ K ^ 8 * Nat.card H ∧ A ⊆ c + H := sorry

/--  If $A \subset {\bf F}_2^n$ is finite non-empty with $|A+A| \leq K|A|$, then there exists a subgroup $H$ of ${\bf F}_2^n$ with $|H| \leq |A|$ such that $A$ can be covered by at most $2K^9$ translates of $H$. -/
lemma better_PFR_conjecture {A: Set G} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := sorry
