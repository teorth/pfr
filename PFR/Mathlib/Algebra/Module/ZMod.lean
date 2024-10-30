import Mathlib.Algebra.Module.ZMod

/-- The quotient of an abelian group by a subgroup containing all multiples of `n` is a
`n`-torsion group. -/
-- See note [reducible non-instances]
abbrev QuotientAddGroup.instZModModule {n : ℕ} {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (hH : ∀ x, n • x ∈ H) : Module (ZMod n) (G ⧸ H) :=
  AddCommGroup.zmodModule <| by simpa [QuotientAddGroup.forall_mk, ← QuotientAddGroup.mk_nsmul]
