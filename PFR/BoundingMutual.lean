import PFR.MultiTauFunctional


/-!
# Bounding the mutual information


## Main definitions:


## Main results

-/

universe u
open MeasureTheory ProbabilityTheory

-- Spelling here is *very* janky.  Feel free to respell
/-- Suppose that $X_{i,j}$, $1 \leq i,j \leq m$, are jointly independent $G$-valued random variables, such that for each $j = 1,\dots,m$, the random variables $(X_{i,j})_{i = 1}^m$
coincide in distribution with some permutation of $X_{[m]}$.
  Write
$$    {\mathcal I} := \bbI[ \bigl(\sum_{i=1}^m X_{i,j}\bigr)_{j =1}^{m}
: \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i = 1}^m
\; \big| \; \sum_{i=1}^m \sum_{j = 1}^m  X_{i,j} ].
 $$
 Then ${\mathcal I} \leq 4 m^2 \eta k.$
-/
lemma mutual_information_le {G Ωₒ : Type u} [MeasureableFinGroup G] [MeasureSpace Ωₒ] (p : multiRefPackage G Ωₒ) (Ω : Type u) [hΩ: MeasureSpace Ω] (X : ∀ i, Ω → G) (hindep:
  iIndepFun (fun _ ↦ by infer_instance) X)
  (hmin : multiTauMinimizes p (fun _ ↦ Ω) (fun _ ↦ hΩ) X) (Ω' : Type*) [MeasureSpace Ω'] (X': Fin p.m × Fin p.m → Ω' → G) (hindep': iIndepFun (fun _ ↦ by infer_instance) X') (hperm:
  ∀ j, ∃ e : Fin p.m ≃ Fin p.m, IdentDistrib (fun ω ↦ (fun i ↦ X' (i, j) ω) ) (fun ω ↦ (fun i ↦ X (e i) ω))) :
  I[ fun ω ↦ ( fun j ↦ ∑ i, X' (i, j) ω) : fun ω ↦ ( fun i ↦ ∑ j, X' (i, j) ω) | fun ω ↦ ∑ i, ∑ j, X' (i, j) ω ] ≤ 4 * p.m^2 * p.η * D[ X; (fun _ ↦ hΩ)] := sorry
