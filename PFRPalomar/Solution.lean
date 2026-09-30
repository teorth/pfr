/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PFR.ApproxHomPFR
import PFR.HomPFR
import PFR.Main
import PFR.RhoFunctional
import PFR.TorsionEndgame
import PFR.WeakPFR

/-!
# Marton's conjecture: proofs

Proofs of the statements of `PFRPalomar.Challenge`, obtained from the corresponding results of
the `PFR` library.
-/

set_option linter.style.haveILetI false

open Pointwise Function Set

namespace Marton

private theorem pfr_conjecture_aux {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨H, c, hc, hH, hcard, hHA, hsub⟩ := PFR_conjecture hA₀ hA hAK
  exact ⟨H.toAddSubgroup, c, hc, hH, by exact_mod_cast hcard, hHA, hsub⟩

theorem pfr_conjecture {G : Type*} [AddCommGroup G] (h2 : ∀ x : G, 2 • x = 0) {A : Set G}
    (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ} (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  letI := AddCommGroup.zmodModule h2
  exact pfr_conjecture_aux hA hA₀ hAK

private theorem pfr_conjecture_nine_aux {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨H, c, hc, hH, hcard, hHA, hsub⟩ := better_PFR_conjecture hA₀ hA hAK
  exact ⟨H.toAddSubgroup, c, hc, hH, hcard, hHA, hsub⟩

theorem pfr_conjecture_nine {G : Type*} [AddCommGroup G] (h2 : ∀ x : G, 2 • x = 0) {A : Set G}
    (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ} (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  letI := AddCommGroup.zmodModule h2
  exact pfr_conjecture_nine_aux hA hA₀ hAK

theorem torsion_pfr_conjecture {G : Type*} [AddCommGroup G] {m : ℕ} (hm : 2 ≤ m)
    (htorsion : ∀ x : G, m • x = 0) {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < m * K ^ (256 * m ^ 3 + 1) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨H, c, hc, hH, hcard, hHA, hsub⟩ := torsion_PFR hm htorsion hA hA₀ hAK
  exact ⟨H, c, hc, hH, hcard, hHA, hsub⟩

theorem weak_pfr_int {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ A' ⊆ A, K ^ (-34 : ℝ) * Nat.card A ≤ Nat.card A' ∧
      (Module.finrank ℤ (vectorSpan ℤ A') : ℝ) ≤ (80 / Real.log 2) * Real.log K := by
  obtain ⟨A', hA'sub, hcard, hdim⟩ := weak_PFR_int_sumset hA hA₀ hAK
  exact ⟨A', hA'sub, hcard, by simpa [AffineSpace.finrank] using hdim⟩

private theorem homomorphism_pfr_aux {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    [Module (ZMod 2) G] [Module (ZMod 2) G'] [Finite G] [Finite G'] (f : G → G') (S : Set G')
    (hS : ∀ x y : G, f (x + y) - f x - f y ∈ S) :
    ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ Nat.card S ^ 10 ∧ ∀ x : G, f x - φ x ∈ T :=
  _root_.homomorphism_pfr f S hS

theorem homomorphism_pfr {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] [Finite G] [Finite G']
    (h2 : ∀ x : G, 2 • x = 0) (h2' : ∀ y : G', 2 • y = 0) (f : G → G') (S : Set G')
    (hS : ∀ x y : G, f (x + y) - f x - f y ∈ S) :
    ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ Nat.card S ^ 10 ∧ ∀ x : G, f x - φ x ∈ T := by
  letI := AddCommGroup.zmodModule h2
  letI := AddCommGroup.zmodModule h2'
  exact homomorphism_pfr_aux f S hS

private theorem approx_hom_pfr_aux {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    [Module (ZMod 2) G] [Module (ZMod 2) G'] [Finite G] [Finite G'] (f : G → G') {K : ℝ}
    (hK : 0 < K)
    (hf : (Nat.card G : ℝ) ^ 2 ≤ K * Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2}) :
    ∃ φ : G →+ G',
      (Nat.card G / (2 ^ 144 * K ^ 122) - 1) / 2 ≤ Nat.card {x : G | f x = φ x} := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have hGcard : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hfilter : Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2}
      = ({x : G × G | f (x.1 + x.2) = f x.1 + f x.2} : Finset (G × G)).card := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hdens : K⁻¹ ≤ Finset.dens {x : G × G | f (x.1 + x.2) = f x.1 + f x.2} := by
    rw [Finset.nnratCast_dens, Fintype.card_prod, le_div_iff₀ (by positivity)]
    rw [hfilter, Nat.card_eq_fintype_card] at hf
    push_cast
    rw [inv_mul_le_iff₀ hK]
    nlinarith
  exact _root_.approx_hom_pfr' f K hK hdens

theorem approx_hom_pfr {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] [Finite G] [Finite G']
    (h2 : ∀ x : G, 2 • x = 0) (h2' : ∀ y : G', 2 • y = 0) (f : G → G') {K : ℝ} (hK : 0 < K)
    (hf : (Nat.card G : ℝ) ^ 2 ≤ K * Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2}) :
    ∃ φ : G →+ G',
      (Nat.card G / (2 ^ 144 * K ^ 122) - 1) / 2 ≤ Nat.card {x : G | f x = φ x} := by
  letI := AddCommGroup.zmodModule h2
  letI := AddCommGroup.zmodModule h2'
  exact approx_hom_pfr_aux f hK hf

end Marton
