import Mathlib.Data.Fin.Basic

theorem Fin.cast_bijective {k l : ℕ} (h : k = l) : Function.Bijective (Fin.cast h) := by
  subst l; simpa using Function.bijective_id

theorem Fin.cast_surjective {k l : ℕ} (h : k = l) : Function.Surjective (Fin.cast h) :=
  (Fin.cast_bijective h).surjective

theorem Fin.forall_fin_three {p : Fin 3 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 :=
  Fin.forall_fin_succ.trans <| and_congr_right fun _ => Fin.forall_fin_two
