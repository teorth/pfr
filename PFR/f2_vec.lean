import Mathlib.Data.Finset.Pointwise
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite field vector spaces

Here we define the notion of a vector space over a finite field, and record basic results about it.

-/


open Pointwise Nat

class ElementaryAddGroup (G : Type*) [AddGroup G] (p : outParam ℕ) where
  orderOf_of_ne {x : G} (hx : x ≠ 0) : addOrderOf x = p
-- may want to change this to p . x = 0 for all x; may also want to enforce finiteness.
