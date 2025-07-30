import Mathlib.Data.Fin.Basic

theorem Fin.cast_surjective {k l:ℕ} (h: k = l) : Function.Surjective (Fin.cast h) :=
  (rightInverse_cast h).surjective -- or `(finCongr h).surjective`

/-- For Mathlib -/
theorem Fin.cast_bijective {k l:ℕ} (h: k = l) : Function.Bijective (Fin.cast h) :=
  ⟨ cast_injective h, cast_surjective h ⟩ -- or `(finCongr h).bijective`
