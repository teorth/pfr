import Mathlib.Data.Finset.Pointwise
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite field vector spaces

Here we define the notion of a vector space over a finite field, and record basic results about it.

## Main classes

* `ElementaryAddGroup`: An elementary p-group.

-/


open Pointwise Nat

class ElementaryAddGroup (G : Type*) [AddGroup G] (p : outParam ℕ) where
  orderOf_of_ne {x : G} (hx : x ≠ 0) : addOrderOf x = p
-- may want to change this to p . x = 0 for all x

variable [AddGroup G] [ElementaryAddGroup G 2]

lemma sum_eq_diff ( x y : G ) : x + y = x - y := by sorry

lemma sum_add_sum_eq_sum ( x y z : G ) : (x + y) + (y + z) = x + z := by sorry
