import Mathlib.Data.Set.Pointwise.Finite

open Pointwise

@[to_additive]
lemma Set.Finite.div {α : Type*} [Div α] {A B : Set α} (hA : A.Finite) (hB : B.Finite) :
    Set.Finite (A / B) := Set.Finite.image2 _ hA hB
