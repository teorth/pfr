import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Free

/-!
If `G` is a rank `d` free `ℤ`-module, then `G/nG` is a finite group of cardinality `n ^ d`.
-/

open Finsupp Function

variable {G : Type*} [AddCommGroup G] [Module.Free ℤ G] {n : ℕ}

variable (G n) in
/-- `modN G n` denotes the quotient of `G` by multiples of `n` -/
abbrev modN : Type _ := G ⧸ LinearMap.range (LinearMap.lsmul ℤ G n)

instance : Module (ZMod n) (modN G n) := QuotientAddGroup.zmodModule (by simp)

variable [NeZero n]

/-- Given a free module `G` over `ℤ`, construct the corresponding basis
of `G / ⟨n⟩` over `ℤ / nℤ`. -/
noncomputable def modNBasis : Basis (Module.Free.ChooseBasisIndex ℤ G) (ZMod n) (modN G n) := by
  set ψ : G →+ G := zsmulAddGroupHom n
  set nG := LinearMap.range (LinearMap.lsmul ℤ G n)
  set H := G ⧸ nG
  set φ : G →ₗ[ℤ] H := nG.mkQ
  let B := Module.Free.ChooseBasisIndex ℤ G
  let bG : Basis B ℤ G := Module.Free.chooseBasis ℤ G
  let mod : (B →₀ ℤ) →ₗ[ℤ] (B →₀ ZMod n) := mapRange.linearMap (Int.castAddHom _).toIntLinearMap
  let f : G →ₗ[ℤ] (B →₀ ℤ) := bG.repr
  have hker : nG ≤ LinearMap.ker (mod.comp f) := by
    rintro _ ⟨x, rfl⟩
    ext b
    simp [mod, f, nG, CharP.ofNat_eq_zero]
  let g : H →ₗ[ℤ] (B →₀ ZMod n) := nG.liftQ (mod.comp f) hker
  refine ⟨.ofBijective (g.toAddMonoidHom.toZModLinearMap n) ⟨?_, ?_⟩⟩
  · rw [AddMonoidHom.coe_toZModLinearMap, LinearMap.toAddMonoidHom_coe, injective_iff_map_eq_zero,
      nG.mkQ_surjective.forall]
    intro x hx
    simp only [Submodule.mkQ_apply, g] at hx
    rw [Submodule.liftQ_apply] at hx
    simp [mod, DFunLike.ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    simp
    rw [Submodule.Quotient.mk_eq_zero]
    choose c hc using hx
    refine ⟨bG.repr.symm ⟨(f x).support, c, by simp [hc, NeZero.ne]⟩, bG.repr.injective ?_⟩
    simpa [DFunLike.ext_iff, eq_comm] using hc
  · suffices mod ∘ bG.repr = g ∘ nG.mkQ by
      exact (this ▸ (mapRange_surjective _ (map_zero _) ZMod.intCast_surjective).comp
        bG.repr.surjective).of_comp
    ext x b
    simp [mod, comp_apply, mapRange.addMonoidHom_apply, Int.coe_castAddHom,
      mapRange_apply, QuotientAddGroup.coe_mk', g, f]
    rfl

variable [Module.Finite ℤ G]

instance modN.instModuleFinite : Module.Finite (ZMod n) (modN G n) := .of_basis modNBasis
instance modN.instFinite : Finite (modN G n) := Module.finite_of_finite (ZMod n)

variable (G n)
@[simp] lemma card_modN : Nat.card (modN G n) = n ^ Module.finrank ℤ G := by
  simp [Nat.card_congr modNBasis.repr.toEquiv, Nat.card_eq_fintype_card,
    Module.finrank_eq_card_chooseBasisIndex]
