/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
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
  obtain ⟨H, c, hc, hH, hcard, hHA, hsub⟩ := PFR_conjecture' hA₀ hA hAK
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
  obtain ⟨H, c, hc, hH, hcard, hHA, hsub⟩ := better_PFR_conjecture' hA₀ hA hAK
  exact ⟨H.toAddSubgroup, c, hc, hH, hcard, hHA, hsub⟩

theorem pfr_conjecture_nine {G : Type*} [AddCommGroup G] (h2 : ∀ x : G, 2 • x = 0) {A : Set G}
    (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ} (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  letI := AddCommGroup.zmodModule h2
  exact pfr_conjecture_nine_aux hA hA₀ hAK

private theorem torsion_pfr_aux {G : Type*} [AddCommGroup G] {m : ℕ} [NeZero m]
    [Module (ZMod m) G] (hm : 2 ≤ m) (htorsion : ∀ x : G, m • x = 0) {A : Set G}
    (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ} (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < m * K ^ (256 * m ^ 3 + 1) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  let G' := Submodule.span (ZMod m) A
  let G'fin : Fintype G' := (hA.submoduleSpan _).fintype
  let ι : G' →ₗ[ZMod m] G := G'.subtype
  have ι_inj : Injective ι := G'.toAddSubgroup.subtype_injective
  let f : G' →+ G := (ι : G' →ₗ[ZMod m] G).toAddMonoidHom
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι := by simp [G', ι]
  have cardA' : Nat.card A' = Nat.card A := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
      Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
  have htorsion' : ∀ x : G', m • x = 0 := fun x ↦ by
    ext
    push_cast
    exact htorsion x.1
  obtain ⟨H', c', hc', hH'A, hsub⟩ := torsion_PFR hm htorsion' (hA₀.preimage' A_rg) hA'
  have hHmap : ((H'.map f : AddSubgroup G) : Set G) = ι '' (H' : Set G') := by
    rw [AddSubgroup.coe_map]; rfl
  refine ⟨H'.map f, ι '' c', toFinite _,
    by rw [hHmap]; exact (toFinite (H' : Set G')).image ι, ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · rw [show Nat.card (H'.map f : AddSubgroup G)
      = ((H'.map f : AddSubgroup G) : Set G).ncard from rfl, hHmap]
    simpa [Set.ncard_image_of_injective _ ι_inj, ← cardA'] using hH'A
  · rw [hHmap, ← image_add]
    exact ⟨⟨x, Submodule.subset_span hx⟩, hsub hx, rfl⟩

theorem torsion_pfr_conjecture {G : Type*} [AddCommGroup G] {m : ℕ} (hm : 2 ≤ m)
    (htorsion : ∀ x : G, m • x = 0) {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < m * K ^ (256 * m ^ 3 + 1) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  have hne : NeZero m := ⟨by omega⟩
  letI := AddCommGroup.zmodModule htorsion
  exact torsion_pfr_aux hm htorsion hA hA₀ hAK

theorem weak_pfr_int {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    {A : Set G} (hA : A.Finite) (hA₀ : A.Nonempty) {K : ℝ}
    (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ A' ⊆ A, K ^ (-34 : ℝ) * Nat.card A ≤ Nat.card A' ∧
      (Module.finrank ℤ (vectorSpan ℤ A') : ℝ) ≤ (80 / Real.log 2) * Real.log K := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s : Finset G, (↑s : Set G) = A := ⟨hA.toFinset, hA.coe_toFinset⟩
  have hsne : s.Nonempty := by simpa using hA₀
  have hs₀ : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.2 hsne
  have hcoe : ∀ t : Finset G, Nat.card (↑t : Set G) = t.card := fun t ↦ by simp
  rw [show ((↑s : Set G) + ↑s) = ((s + s : Finset G) : Set G) by simp, hcoe, hcoe] at hAK
  have hsum₀ : (0 : ℝ) ≤ (s + s).card := by positivity
  have hK₁ : (1 : ℝ) ≤ K := by
    have h1 : (s.card : ℝ) ≤ ((s + s).card : ℝ) := by
      exact_mod_cast Finset.card_le_card_add_left hsne
    nlinarith
  have hruzsa : ((s - s).card : ℝ) * s.card ≤ ((s + s).card : ℝ) * ((s + s).card : ℝ) := by
    exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add s s s
  have hcoesub : ((s : Set G) - (s : Set G)) = ((s - s : Finset G) : Set G) := by
    simp
  have hdiff : (Nat.card ((s : Set G) - (s : Set G)) : ℝ) ≤ K ^ 2 * Nat.card (s : Set G) := by
    rw [hcoesub, hcoe, hcoe]
    nlinarith
  obtain ⟨A', hA'sub, hcard, hdim⟩ := weak_PFR_int (K := K ^ 2) hA₀ hdiff
  refine ⟨A', hA'sub, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) hcard
    rw [← Real.rpow_natCast K 2, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ K)]
    norm_num
  · refine le_trans hdim (le_of_eq ?_)
    rw [Real.log_pow]
    push_cast
    ring

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
