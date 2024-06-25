import PFR.MultiTauFunctional


/-!
# Bounding the mutual information


## Main definitions:


## Main results

-/

open MeasureTheory ProbabilityTheory

/-- Suppose that $X_{i,j}$, $1 \leq i,j \leq m$, are jointly independent $G$-valued random variables, such that for each $j = 1,\dots,m$, the random variables $(X_{i,j})_{i = 1}^m$ coincide in distribution with some permutation of $X_{[m]}$.
  Write
  \[
    {\mathcal I} := \bbI[ \bigl(\sum_{i=1}^m X_{i,j}\bigr)_{j =1}^{m} : \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i = 1}^m \; \big| \; \sum_{i=1}^m \sum_{j = 1}^m  X_{i,j} ].
  \]
Then
  \begin{equation}\label{I-ineq}
    {\mathcal I} \leq 4 m^2 \eta k.
  \end{equation}
-/
lemma mutual_information_le : 0 = 1 := sorry
