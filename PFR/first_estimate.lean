import PFR.entropy_basic

/-!
# First estimate

The first estimate on tau-minimizers.

Assumptions (need to be placed explicitly in the file):

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $I_1 :=  I_1 [ X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2 ]$

-/


/--  We have $I_1 \leq 2 \eta k$ -/
lemma first_estimate : 0 = 1 := by sorry


/--     H[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} H[X_1]+\tfrac{1}{2} H[X_2] + (2 + \eta) k - I_1.
-/
lemma ent_ofsum_le : 0 = 1 := by sorry
