/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Marton's conjecture (the polynomial Freiman–Ruzsa conjecture)

This file states, in Mathlib-only terms, the headline theorems of three papers:

* `[GGMT]` W. T. Gowers, Ben Green, Freddie Manners, Terence Tao,
  *On a conjecture of Marton*, arXiv:2311.05762.
* `[GGMT2]` W. T. Gowers, Ben Green, Freddie Manners, Terence Tao,
  *Marton's conjecture in abelian groups with bounded torsion*, arXiv:2404.02244.
* `[L]` Jyun-Jie Liao, *Improved exponent for Marton's conjecture in $\mathbf{F}_2^n$*,
  arXiv:2404.09639.

Marton's conjecture, widely known as the polynomial Freiman–Ruzsa conjecture, asserts that a
subset `A` of an abelian group with small doubling, `|A + A| ≤ K * |A|`, is efficiently covered
by cosets of a subgroup no larger than `A`, with a number of cosets polynomial in `K`.

The six statements below are:

* `Marton.pfr_conjecture` — `[GGMT]`, Theorem 1.2: the conjecture in `𝔽₂ⁿ`, with `2 * K ^ 12`
  cosets.
* `Marton.pfr_conjecture_nine` — `[L]`, main theorem: the same conclusion with `2 * K ^ 9`
  cosets. This strengthens `Marton.pfr_conjecture`, which is retained because it is the
  headline theorem of a different paper.
* `Marton.torsion_pfr_conjecture` — `[GGMT2]`, Theorem 1.1: the conjecture in an arbitrary
  abelian group of torsion `m`, with `m * K ^ (256 * m ^ 3 + 1)` cosets.
* `Marton.weak_pfr_int` — `[GGMT]`, Theorem 1.3: a set of small doubling in a finitely
  generated free `ℤ`-module has a large subset of logarithmically small affine dimension.
* `Marton.homomorphism_pfr` — `[GGMT]`, Corollary 1.4: a map whose additive defects take few
  values differs from a homomorphism by a map with small range.
* `Marton.approx_hom_pfr` — `[GGMT]`, Corollary 1.5: a map that is additive on a positive
  proportion of pairs agrees with a homomorphism on a positive proportion of points.

All statements are phrased with `Nat.card`, `Set` pointwise arithmetic, `AddSubgroup`,
`vectorSpan` and `Module.finrank`, so that no definition of this project is needed in order to
read them. Torsion hypotheses are stated as `∀ x : G, m • x = 0` rather than through a
`Module (ZMod m) G` instance, so that the statements do not depend on which `ZMod`-algebra
instance path is in scope.
-/

open Pointwise

namespace Marton

/-- **Marton's conjecture in characteristic 2**, `[GGMT]`, Theorem 1.2.

If `A` is a finite non-empty subset of an abelian group `G` of exponent `2` — that is,
`2 • x = 0` for every `x : G`, so that `G` is an `𝔽₂`-vector space — and `|A + A| ≤ K * |A|`,
then `A` is covered by fewer than `2 * K ^ 12` cosets of a subgroup `H` of `G` with
`|H| ≤ |A|`.

The ambient group `G` is not required to be finite; the covering set `c` and the subgroup `H`
produced are then finite. This statement is superseded by `Marton.pfr_conjecture_nine`, and is
recorded separately because it is the headline theorem of `[GGMT]`. -/
theorem pfr_conjecture {G : Type*} [AddCommGroup G] (h2 : ∀ x : G, 2 • x = 0) {A : Set G}
    (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ} (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry

/-- **Marton's conjecture in characteristic 2 with exponent 9**, `[L]`, main theorem.

If `A` is a finite non-empty subset of an abelian group `G` of exponent `2` — that is,
`2 • x = 0` for every `x : G`, so that `G` is an `𝔽₂`-vector space — and `|A + A| ≤ K * |A|`,
then `A` is covered by fewer than `2 * K ^ 9` cosets of a subgroup `H` of `G` with
`|H| ≤ |A|`.

The ambient group `G` is not required to be finite; the covering set `c` and the subgroup `H`
produced are then finite. -/
theorem pfr_conjecture_nine {G : Type*} [AddCommGroup G] (h2 : ∀ x : G, 2 • x = 0) {A : Set G}
    (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ} (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry

/-- **Marton's conjecture in abelian groups of bounded torsion**, `[GGMT2]`, Theorem 1.1.

Let `G` be an abelian group of torsion `m ≥ 2`, meaning that `m • x = 0` for every `x : G`.
If `A` is a finite non-empty subset of `G` with `|A + A| ≤ K * |A|`, then `A` is covered by
fewer than `m * K ^ (256 * m ^ 3 + 1)` cosets of a subgroup `H` of `G` with `|H| ≤ |A|`.

The ambient group `G` is not required to be finite; the covering set `c` and the subgroup `H`
produced are then finite. -/
theorem torsion_pfr_conjecture {G : Type*} [AddCommGroup G] {m : ℕ} (hm : 2 ≤ m)
    (htorsion : ∀ x : G, m • x = 0) {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < m * K ^ (256 * m ^ 3 + 1) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry

/-- **Weak Marton's conjecture over the integers**, `[GGMT]`, Theorem 1.3.

Let `G` be a finitely generated free `ℤ`-module, that is, a copy of `ℤ ^ D`. If `A` is a
finite non-empty subset of `G` with `|A + A| ≤ K * |A|`, then `A` has a subset `A'` with
`|A'| ≥ K ^ (-34) * |A|` whose affine dimension — the rank of the `ℤ`-span of its difference
set — is at most `(80 / log 2) * log K`.

This realises the constants `C₁ = 68` and `C₂ = 80 / log 2` of `[GGMT]`, Theorem 1.3, which
is stated there for unspecified absolute constants. -/
theorem weak_pfr_int {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ A' ⊆ A, K ^ (-34 : ℝ) * Nat.card A ≤ Nat.card A' ∧
      (Module.finrank ℤ (vectorSpan ℤ A') : ℝ) ≤ (80 / Real.log 2) * Real.log K := by
  sorry

/-- **The homomorphism form of Marton's conjecture**, `[GGMT]`, Corollary 1.4.

Let `G` and `G'` be finite abelian groups of exponent `2` and let `f : G → G'` be a function
whose additive defects `f (x + y) - f x - f y` all lie in a set `S`. Then `f` differs from a
group homomorphism `φ : G →+ G'` by a function taking at most `|S| ^ 10` values. -/
theorem homomorphism_pfr {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] [Finite G] [Finite G']
    (h2 : ∀ x : G, 2 • x = 0) (h2' : ∀ y : G', 2 • y = 0) (f : G → G') (S : Set G')
    (hS : ∀ x y : G, f (x + y) - f x - f y ∈ S) :
    ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ Nat.card S ^ 10 ∧ ∀ x : G, f x - φ x ∈ T := by
  sorry

/-- **The approximate homomorphism form of Marton's conjecture**, `[GGMT]`, Corollary 1.5.

Let `G` and `G'` be finite abelian groups of exponent `2` and let `f : G → G'` be a function
such that `f (x + y) = f x + f y` for at least a proportion `K⁻¹` of the pairs
`(x, y) ∈ G × G`, written here as `|G| ^ 2 ≤ K * |{(x, y) | f (x + y) = f x + f y}|`. Then
there is a group homomorphism `φ : G →+ G'` agreeing with `f` on at least
`(|G| / (2 ^ 144 * K ^ 122) - 1) / 2` points of `G`. -/
theorem approx_hom_pfr {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] [Finite G] [Finite G']
    (h2 : ∀ x : G, 2 • x = 0) (h2' : ∀ y : G', 2 • y = 0) (f : G → G') {K : ℝ} (hK : 0 < K)
    (hf : (Nat.card G : ℝ) ^ 2 ≤ K * Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2}) :
    ∃ φ : G →+ G',
      (Nat.card G / (2 ^ 144 * K ^ 122) - 1) / 2 ≤ Nat.card {x : G | f x = φ x} := by
  sorry

end Marton
