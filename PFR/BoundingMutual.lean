import PFR.MultiTauFunctional


/-!
# Bounding the mutual information


## Main definitions:


## Main results

-/

universe u
open MeasureTheory ProbabilityTheory

-- Spelling here is *very* janky. Feel free to respell
/-- Suppose that $X_{i,j}$, $1 \leq i,j \leq m$, are jointly independent $G$-valued random variables, such that for each $j = 1,\dots,m$, the random variables $(X_{i,j})_{i = 1}^m$
coincide in distribution with some permutation of $X_{[m]}$.
  Write
$$ {\mathcal I} := \bbI[ \bigl(\sum_{i=1}^m X_{i,j}\bigr)_{j =1}^{m}
: \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i = 1}^m
\; \big| \; \sum_{i=1}^m \sum_{j = 1}^m X_{i,j} ].
 $$
 Then ${\mathcal I} \leq 4 m^2 \eta k.$
-/
lemma mutual_information_le {G Ωₒ : Type u} [MeasureableFinGroup G] [MeasureSpace Ωₒ]
  (p : multiRefPackage G Ωₒ) (Ω : Type u) [hΩ : MeasureSpace Ω] (X : ∀ i, Ω → G)
  (h_indep : iIndepFun X)
  (h_min : multiTauMinimizes p (fun _ ↦ Ω) (fun _ ↦ hΩ) X) (Ω' : Type*) [hΩ': MeasureSpace Ω']
  [IsProbabilityMeasure hΩ'.volume]
  (X' : Fin p.m × Fin p.m → Ω' → G) (h_indep': iIndepFun X')
  (hperm : ∀ j, ∃ e : Fin p.m ≃ Fin p.m, IdentDistrib (fun ω ↦ (fun i ↦ X' (i, j) ω))
    (fun ω ↦ (fun i ↦ X (e i) ω))) :
  I[ fun ω ↦ ( fun j ↦ ∑ i, X' (i, j) ω) : fun ω ↦ ( fun i ↦ ∑ j, X' (i, j) ω) |
    fun ω ↦ ∑ i, ∑ j, X' (i, j) ω ] ≤ 2 * p.m * (2*p.m + 1) * p.η * D[ X; (fun _ ↦ hΩ)] := by
    have hm := p.hm
    set I₀ := I[ fun ω ↦ ( fun j ↦ ∑ i, X' (i, j) ω) : fun ω ↦ ( fun i ↦ ∑ j, X' (i, j) ω) |
    fun ω ↦ ∑ i, ∑ j, X' (i, j) ω ]
    set k := D[X ; fun x ↦ hΩ]
    set one : Fin p.m := ⟨ 1, by omega ⟩
    set last : Fin p.m := ⟨ p.m-1, by omega ⟩
    set column : Fin p.m → Fin p.m → Ω' → G := fun j i ω ↦ X' (i, j) ω
    set V : Fin p.m → Ω' → G := fun i ω ↦ ∑ j, X' (i, j) ω
    set S : Fin p.m → Fin p.m → Ω' → G := fun i j ↦ ∑ k ∈ .Ici j, X' (i, k)
    set A : Fin p.m → ℝ := fun j ↦ D[ column j; fun _ ↦ hΩ']
      - D[ column j | fun i ↦ S i j; fun _ ↦ hΩ']
    set B : ℝ := D[ column last; fun _ ↦ hΩ'] - D[ fun j ω ↦ ∑ i, X' (i, j) ω; fun _ ↦ hΩ']

    have h1 : I₀ ≤ ∑ j ∈ .Iio last, A j + B := by
      sorry

    have h2 {j : Fin p.m} (hj: j ∈ Finset.Iio last)
      : A j ≤ p.η * ∑ i, d[ X' (i,j) # X' (i,j) | S i j ] := by
        sorry

    have h3 : B ≤ p.η * ∑ i, d[ X' (i, last) # V i ] := by
      sorry

    have h4 (i: Fin p.m) {j : Fin p.m} (hj: j ∈ Finset.Iio last) :
      d[ X' (i,j) # X' (i,j) | S i j ] ≤ d[ X' (i,j) # X' (i,j) ]
        + (H[S i j] - H[S i (j+one)]) / 2 := by
        sorry

    have h5 (i: Fin p.m) :
      ∑ j ∈ Finset.Iio last, d[ X' (i,j) # X' (i,j) | S i j ]
        ≤ ∑ j ∈ Finset.Iio last, d[ X' (i,j) # X' (i,j) ] + (H[V i] - H[X' (i, last)]) / 2 := by
        sorry

    have h6 (i: Fin p.m) :
      d[ X' (i, last) # V i ] ≤ d[ X' (i, last) # X' (i, last) ]
        + (H[V i] - H[X' (i, last)]) / 2 := by
        sorry

    have h7 : I₀/p.η ≤ p.m * ∑ i, d[X i # X i] + ∑ i, H[V i] - ∑ i, H[X i] := by
      sorry

    have h8 (i: Fin p.m) : H[V i] ≤ H[ ∑ j, X j] + ∑ j, d[X' (i,j) # X' (i,j)] := by
      sorry

    have h9 : ∑ i, H[V i] - ∑ i, H[X i] ≤ p.m * ∑ i, d[X i # X i] + p.m * k := by
      sorry

    have h10 : I₀/p.η ≤ 2 * p.m * ∑ i, d[X i # X i] + p.m * k := by linarith

    have h11 : ∑ i, d[X i # X i] ≤ 2 * p.m * k := by
      sorry

    sorry
