import Mathlib.Data.Finset.Image

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma Finset.map_sdiff (f : α ↪ β) (s : Finset α) (t : Finset α) :
    map f (s \ t) = map f s \ map f t := by aesop
