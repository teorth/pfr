import PFR.first_estimate
import PFR.second_estimate

/-!
# Endgame

The endgame on tau-minimizers.

Assumptions (need to be placed explicitly in the file):

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $I_1 :=  I_1 [ X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2 ]$
* $I_2 := I[ X_1+X_2 : X_1 + \tilde X_1 | X_1+X_2+\tilde X_1+\tilde X_2 ]$
* U := X_1 + X_2,
* V := \tilde X_1 + X_2
* W := X_1 + \tilde X_1
* S := X_1 + X_2 + \tilde X_1 + \tilde X_2.
-/

/--
$$ I(U : V | S) + I(V : W | S) + I(W : U | S) $$
is less than or equal to
$$ 6 \eta k - \frac{1 - 5 \eta}{1-\eta} (2 \eta k - I_1).$$
-/
lemma sum_condMutual_le : 0 = 1 := by sorry

/--
$$ \sum_{i=1}^2 \sum_{A\in\{U,V,W\}} \big(d[X^0_i;A|S] - d[X^0_i;X_i]\big)$$
is less than or equal to
$$ \leq (6 - 3\eta) k + 3(2 \eta k - I_1).$$
-/
lemma sum_dist_diff_le : 0 = 1 := by sorry

/-- $U+V+W=0$. -/
lemma sum_uvw_eq_zero : 0 = 1 := by sorry

/-- If $T_1, T_2, T_3$ are $G$-valued randomv variables with $T_1+T_2+T_3=0$ holds identically and
$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$
Then there exist random variables $T'_1, T'_2$ such that
$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X_1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2]) $$
is at most
$$\delta + \frac{\eta}{3} \biggl( \delta + \sum_{i=1}^2 \sum_{j = 1}^3 (d[X^0_i;T_j] - d[X^0_i; X_i]) \biggr).$$
-/
lemma construct_good : 0 = 1 := by sorry
