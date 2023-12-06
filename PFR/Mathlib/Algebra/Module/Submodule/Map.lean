import Mathlib.Algebra.Module.Submodule.Map

namespace LinearMap

variable { M M' R : Type* } [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
  [Module R M] [Module R M']

def submoduleMap (f : M →ₗ[R] M') (S : Submodule R M) : S →ₗ[R] S.map f where
  toFun := fun x ↦ ⟨ f x, Submodule.apply_coe_mem_map f x ⟩
  map_add' x y := Subtype.eq <| f.map_add x y
  map_smul' x y := Subtype.eq <| f.map_smul x y

theorem submoduleMap_surjective (f : M →ₗ[R] M') (S : Submodule R M) :
    Function.Surjective (f.submoduleMap S) :=
  AddMonoidHom.addSubmonoidMap_surjective f.toAddMonoidHom S.toAddSubmonoid
