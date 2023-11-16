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

/-- I(U : V | S) + I(V : W | S) + I(W : U | S) \leq 6 \eta k - \frac{1 - 5 \eta}{1-\eta} (2 \eta k - I_1).
-/
lemma sum_condMutual_le : 0 = 1 := by sorry
