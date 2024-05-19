import PFR.ForMathlib.Entropy.RuzsaDist

/-!
# More results about Ruzsa distance

More facts about Ruzsa distance and related inequalities, for use in the m-torsion version of PFR.

## Main definitions

## Main results

-/

section dataProcessing

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

namespace ProbabilityTheory

universe uΩ uS uT uU uV uW

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW} [mΩ : MeasurableSpace Ω]
  [Countable S] [Countable T] [Countable U] [Countable V] [Countable W]
  [Nonempty S] [Nonempty T] [Nonempty U] [Nonempty V] [Nonempty W]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

/--
Let $X,Y$ be random variables. For any function $f, g$ on the range of $X$, we have $I[f(X) : Y] \leq I[X:Y]$.
-/
lemma mutual_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : Y ; μ] ≤ I[X : Y ; μ] := by
  have h_meas : Measurable (f ∘ X) := Measurable.comp (measurable_discrete f) hX
  rw [mutualInfo_comm h_meas hY, mutualInfo_comm hX hY,
    mutualInfo_eq_entropy_sub_condEntropy hY h_meas, mutualInfo_eq_entropy_sub_condEntropy hY hX]
  gcongr
  exact condEntropy_comp_ge μ hX hY f

/--
Let `X, Y` be random variables. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ]`.
 -/
lemma mutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) (g : T → V) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ] :=
  calc
    _ ≤ I[X : g ∘ Y ; μ] := mutual_comp_le μ hX (Measurable.comp hg hY) f
    _ = I[g ∘ Y : X ; μ] := mutualInfo_comm hX (Measurable.comp hg hY) μ
    _ ≤ I[Y : X ; μ] := mutual_comp_le μ hY hX g
    _ = I[X : Y ; μ] := mutualInfo_comm hY hX μ

/--
Let `X, Y, Z`. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ]`.
-/
lemma condMutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
  (f : S → V) (g : T → W) [FiniteRange X] [FiniteRange Y]:
    I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by sorry

end ProbabilityTheory
end dataProcessing

open Filter Function MeasureTheory Measure ProbabilityTheory
open scoped BigOperators

attribute [symm] ProbabilityTheory.IdentDistrib.symm

variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G]
  [Countable S] [Nonempty S] [MeasurableSpace S]
  [Countable T] [Nonempty T] [MeasurableSpace T]

variable {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G} [FiniteRange X] [FiniteRange Y] [FiniteRange Z]

/--   If $X,Y$ are $G$-valued, then
  $$  d[X ; -Y]  \leq 3 d[X;Y].$$ -/
lemma rdist_of_neg_le : d[X ; μ # -Y ; μ'] ≤ 3 * d[X ; μ # Y ; μ'] := by sorry


--open Classical in
/--  If $n \geq 1$ and $X, Y_1, \dots, Y_n$ are jointly independent $G$-valued random variables, then
  $$ H[X + \sum_{i=1}^n Y_i] - H[X] \leq \sum_{i=1}^n H[X+Y_i] - \bbH[X].$$
The spelling here is tentative.  Feel free to modify it to make the proof easier, or the application easier. -/
lemma kvm_ineq_I {I:Type*} {i₀: I} {s: Finset I} (hs: ¬ i₀ ∈ s) (Y: I → Ω → G) (hY: (i:I) → Measurable (Y i))
                 (hindep: iIndepFun (fun (i:I) => hG) Y μ )
                : H[ Y i₀ + ∑ i in s, Y i; μ ] - H[ Y i₀; μ ] ≤ ∑ i in s, (H[ Y i₀ + Y i; μ] - H[Y i₀; μ]) := by sorry

/--  If $n \geq 1$ and $X, Y_1, \dots, Y_n$ are jointly independent $G$-valued random variables, then
  $$ d[X; \sum_{i=1}^n Y_i] \leq 2 \sum_{i=1}^n d[X; Y_i].$$
-/
lemma kvm_ineq_II {I:Type*} {i₀: I} {s: Finset I} (hs: ¬ i₀ ∈ s) (hs': Finset.Nonempty s) (Y: I → Ω → G)
                 (hY: (i:I) → Measurable (Y i)) (hindep: iIndepFun (fun (i:I) => hG) Y μ )
                : d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ 2 * ∑ i in s, d[Y i₀; μ # Y i; μ] := by sorry

/-- If $n \geq 1$ and $X, Y_1, \dots, Y_n$ are jointly independent $G$-valued random variables, then
  $$ d[X; \sum_{i=1}^n Y_i] \leq d[X; Y_1] + \frac{1}{2}(\bbH[ \sum_{i=1}^n Y_i ] - \bbH[Y_1]).$$
-/
lemma kvm_ineq_III {I:Type*} {i₀ : I} {s: Finset I} (hs: ¬ i₀ ∈ s) (hs': Finset.Nonempty s) (Y: I → Ω → G)
                 (hY: (i:I) → Measurable (Y i)) (hindep: iIndepFun (fun (i:I) => hG) Y μ ) (i₁ : I)
                : d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ d[Y i₀; μ # Y i₁; μ] + (2:ℝ)⁻¹ * ∑ i in s, (H[Y i; μ] - H[Y i₁; μ]) := by sorry

open Classical in
/-- Let $(X_i)_{1 \leq i \leq m}$ and $(Y_j)_{1 \leq j \leq l}$ be tuples of jointly independent random variables (so the $X$'s and $Y$'s are also independent of each other), and let $f: \{1,\dots,l\} \to \{1,\dots,m\}$ be a function, then
  $$ \bbH[\sum_{j=1}^l Y_j] \leq \bbH[ \sum_{i=1}^m X_i ] + \sum_{j=1}^l (\bbH[ Y_j - X_{f(j)}] - \bbH[X_{f(j)}]).$$
-/
lemma ent_of_sum_le_ent_of_sum {I:Type*} {s t: Finset I} (hdisj: Disjoint s t) (hs: Finset.Nonempty s) (ht: Finset.Nonempty t) (X: I → Ω → G)
  (hX: (i:I) → Measurable (X i)) (hindep: iIndepFun (fun (i:I) => hG) X μ ) (f: I → I) (hf: Finset.image f t ⊆ s)
                : H[∑ i in t, X i; μ] ≤ H[∑ i in s, X i; μ] + ∑ i in t, (H[ X i - X (f i); μ] - H[X (f i); μ]) := by sorry

/-- Let $X,Y,X'$ be independent $G$-valued random variables, with $X'$ a copy of $X$, and let $a$ be an integer.  Then
$$H[X-(a+1)Y] \leq H[X-aY] + H[X-Y-X'] - H[X]$$ -/
lemma ent_of_sub_smul {Y : Ω → G} {X' : Ω → G} [FiniteRange Y] [FiniteRange X'] (hX: Measurable X) (hY: Measurable Y) (hX': Measurable X') (hindep: iIndepFun (fun _ ↦ hG) ![X, Y, X'] μ) (hident: IdentDistrib X X' μ μ) {a:ℤ} : H[X - (a+1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by sorry

/-- Let $X,Y,X'$ be independent $G$-valued random variables, with $X'$ a copy of $X$, and let $a$ be an integer.  Then
$$H[X-(a-1)Y] \leq H[X-aY] + H[X-Y-X'] - H[X]$$ -/
lemma ent_of_sub_smul' {Y : Ω → G} {X' : Ω → G} [FiniteRange Y] [FiniteRange X'] (hX: Measurable X) (hY: Measurable Y) (hX': Measurable X') (hindep: iIndepFun (fun _ ↦ hG) ![X, Y, X'] μ) (hident: IdentDistrib X X' μ μ) {a:ℤ} : H[X - (a-1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by sorry

/--  Let $X,Y$ be independent $G$-valued random variables, and let $a$ be an integer.  Then
  $$H[X-aY] - H[X] \leq 4 |a| d[X;Y].$$ -/
lemma ent_of_sub_smul_le {Y : Ω → G} [FiniteRange Y] (hX: Measurable X) (hY: Measurable Y) (hindep: IndepFun X Y μ) {a:ℤ} : H[X - a • Y; μ] - H[X; μ] ≤ 4 * |a| * d[X ; μ # Y ; μ] := by sorry

section multiDistance

open Filter Function MeasureTheory Measure ProbabilityTheory
open scoped BigOperators

variable {G : Type*}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G]

/--  Let $X_{[m]} = (X_i)_{1 \leq i \leq m}$ non-empty finite tuple of $G$-valued random variables $X_i$. Then we define
\[
  D[X_{[m]}] := \bbH[\sum_{i=1}^m \tilde X_i] - \frac{1}{m} \sum_{i=1}^m \bbH[\tilde X_i],
\]
where the $\tilde X_i$ are independent copies of the $X_i$.-/
noncomputable
def multiDist {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) : ℝ := sorry

@[inherit_doc multiDist] notation3:max "D[" X " ; " hΩ "]" => multiDist hΩ X

/-- For any such tuple, we have $D[X_{[m]}] \geq 0$. -/
lemma multiDist_nonneg : 0 = 1 := by sorry

/--  If $\phi: \{1,\dots,m\} \to \{1,\dots,m\}$ is a bijection, then $D[X_{[m]}] = D[(X_{\phi(j)})_{1 \leq j \leq m}]$. -/
lemma multiDist_of_perm : 0 = 1 := by sorry

/-- Let $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables. Then
  $$\sum_{1 \leq j,k \leq m: j \neq k} d[X_j; -X_k] \leq m(m-1) D[X_{[m]}].$$ -/
lemma multidist_ruzsa_I : 0 = 1 := by sorry

/-- Let $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables. Then
  $$\sum_{j=1}^m d[X_j;X_j] \leq 2 m D[X_{[m]}].$$ -/
lemma multidist_ruzsa_II : 0 = 1 := by sorry

/-- Let $I$ be an indexing set of size $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables. If the $X_i$ all have the same distribution, then $D[X_{[m]}] \leq m d[X_i;X_i]$ for any $1 \leq i \leq m$. -/
lemma multidist_ruzsa_III : 0 = 1 := by sorry

/-- Let $I$ be an indexing set of size $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables.  Let $W := \sum_{i \in I} X_i$. Then
  $$ d[W;-W] \leq 2 D[X_i].$$ -/
lemma multidist_ruzsa_IV : 0 = 1 := by sorry

/-- If $D[X_{[m]}]=0$, then for each $i \in I$ there is a finite subgroup $H_i \leq G$ such that $d[X_i; U_{H_i}] = 0$. -/
lemma multidist_eq_zero : 0 = 1 := by sorry

/-- If $X_{[m]} = (X_i)_{1 \leq i \leq m}$ and $Y_{[m]} = (Y_i)_{1 \leq i \leq m}$ are tuples of random variables, with the $X_i$ being $G$-valued (but the $Y_i$ need not be), then we define
  \begin{equation}\label{multi-def-cond}
  D[ X_{[m]} | Y_{[m]}] := \bbH[\sum_{i=1}^m \tilde X_i \big| (\tilde Y_j)_{1 \leq j \leq m} ] - \frac{1}{m} \sum_{i=1}^m \bbH[ \tilde X_i | \tilde Y_i]
    \end{equation}
  where $(\tilde X_i,\tilde Y_i)$, $1 \leq i \leq m$ are independent copies of $(X_i,Y_i), 1 \leq i \leq m$ (but note here that we do \emph{not} assume $X_i$ are independent of $Y_i$, or $\tilde X_i$ independent of $\tilde Y_i$). -/
noncomputable
def condMultiDist {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) (Y : (i:Fin m) → (Ω i) → G) : ℝ := sorry

@[inherit_doc multiDist] notation3:max "D[" X " | " Y " ; " hΩ "]" => condMultiDist hΩ X Y

/-- With the above notation, we have
  \begin{equation}\label{multi-def-cond-alt}
    D[ X_{[m]} | Y_{[m]} ] = \sum_{(y_i)_{1 \leq i \leq m}} \biggl(\prod_{1 \leq i \leq m} p_{Y_i}(y_i)\biggr) D[ (X_i \,|\, Y_i \mathop{=}y_i)_{1 \leq i \leq m}]
  \end{equation}
  where each $y_i$ ranges over the support of $p_{Y_i}$ for $1 \leq i \leq m$. -/
lemma condMultiDist_eq : 0 = 1 := by sorry

end multiDistance

section multiDistance_chainRule

/-- Let $\pi : G \to H$ be a homomorphism of abelian groups and let $X_{[m]}$ be a tuple of jointly independent $G$-valued random variables.  Then $D[X_{[m]}]$ is equal to
$$ D[ X_{[m]} | \pi(X_{[m]}) ]  +D[ \pi(X_{[m]}) ]  + I[ \sum_{i=1}^m X_i  : \pi(X_{[m]}) \; | \; \pi(\sum_{i=1}^m X_i) ]$$
  where $\pi(X_{[m]}) := (\pi(X_i))_{1 \leq i \leq m}$.
-/
lemma multiDist_chainRule : 0 = 1 := by sorry

/-- Let $\pi : G \to H$ be a homomorphism of abelian groups.
    Let $I$ be a finite index set and let $X_{[m]}$ be a tuple of $G$-valued random variables.
    Let $Y_{[m]}$ be another tuple of random variables (not necessarily $G$-valued).
    Suppose that the pairs $(X_i, Y_i)$ are jointly independent of one another (but $X_i$ need not be independent of $Y_i$).
    Then
$$  D[ X_{[m]} | Y_{[m]} ] =  D[ X_{[m]} \,|\, \pi(X_{[m]}), Y_{[m]}] + D[ \pi(X_{[m]}) \,|\, Y_{[m]}]$$
$$+ I[ \sum_{i=1}^m X_i : \pi(X_{[m]}) \; | \;  \pi(\sum_{i=1}^m X_i \bigr), Y_{[m]} ]. -/
lemma cond_multiDist_chainRule : 0 = 1 := by sorry

/-- Let $m$ be a positive integer.
    Suppose one has a sequence
 $$     G_m \to G_{m-1} \to \dots \to G_1 \to G_0 = \{0\}
 $$
 of homomorphisms between abelian groups $G_0,\dots,G_m$, and for each $d=0,\dots,m$, let $\pi_d : G_m \to G_d$ be the homomorphism from $G_m$ to $G_d$ arising from this sequence by composition (so for instance $\pi_m$ is the identity homomorphism and $\pi_0$ is the zero homomorphism).
    Let $X_{[m]} = (X_i)_{1 \leq i \leq m}$ be a jointly independent tuple of $G_m$-valued random variables.
    Then
 $$       D[ X_{[m]} ] =  \sum_{d=1}^m D[ \pi_d(X_{[m]}) \,|\, \pi_{d-1}(X_{[m]})] $$
 $$ + \sum_{d=1}^{m-1} I[ \sum_i X_i : \pi_d(X_{[m]}) \; \big| \; \pi_d\big(\sum_i X_i\big), \pi_{d-1}(X_{[m]}) ].
 $$
  -/
lemma iter_multiDist_chainRule : 0 = 1 := by sorry

/-- Under the preceding hypotheses,
$$ D[ X_{[m]} ] \geq  & \sum_{d=1}^m D[ \pi_d(X_{[m]})|\pi_{d-1}(X_{[m]}) ] $$
 $$+ I[ \sum_i X_i : \pi_1(X_{[m]}) \; \big| \; \pi_1\bigl(\sum_i X_i\bigr) ].$$
-/
lemma iter_multiDist_chainRule' : 0 = 1 := by sorry

/-- Let $G$ be an abelian group and let $m \geq 2$.  Suppose that $X_{i,j}$, $1 \leq i, j \leq m$, are independent $G$-valued random variables.
    Then
  $$I[ l(\sum_{i=1}^m X_{i,j}\bigr)_{j =1}^{m} : \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i = 1}^m \; \big| \; \sum_{i=1}^m \sum_{j = 1}^m  X_{i,j} ] $$
  is less than
  $$\sum_{j=1}^{m-1} \Bigl(D[(X_{i, j})_{i = 1}^m] - D[ (X_{i, j})_{i = 1}^m  \; \big| \; (X_{i,j} + \cdots + X_{i,m})_{i =1}^m ]\Bigr)$$
  $$+  D[(X_{i,m})_{i=1}^m] - D[ \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i=1}^m ],$$
  where all the multidistances here involve the indexing set $\{1,\dots, m\}$.
  -/
lemma cor_multiDist_chainRule : 0 = 1 := by sorry


end multiDistance_chainRule
