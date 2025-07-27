import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import PFR.MultiTauFunctional


/-!
# Bounding the mutual information


## Main definitions:


## Main results

-/

universe u
open MeasureTheory ProbabilityTheory


/-- For Mathlib -/
theorem Fin.cast_surjective {k l:ℕ} (h: k = l) : Function.Surjective (Fin.cast h) :=
  (rightInverse_cast h).surjective -- or `(finCongr h).surjective`

/-- For Mathlib -/
theorem Fin.cast_bijective {k l:ℕ} (h: k = l) : Function.Bijective (Fin.cast h) :=
  ⟨ cast_injective h, cast_surjective h ⟩ -- or `(finCongr h).bijective`

lemma multiDist_of_cast {m m' : ℕ} (h : m' = m) {Ω : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩfin : ∀ i, IsFiniteMeasure (hΩ i).volume)
    {G: Type*} [MeasureableFinGroup G] (X : ∀ i, (Ω i) → G)  :
    D[fun i ↦ X (i.cast h); fun i ↦ hΩ (i.cast h)] = D[X ; hΩ] := by
    unfold multiDist
    congr 1
    . apply IdentDistrib.entropy_congr
      exact {
        aemeasurable_fst := by fun_prop
        aemeasurable_snd := by fun_prop
        map_eq := by
          have : (fun (x: Fin m' → G) ↦ ∑ i, x i) = (fun (x: Fin m → G) ↦ ∑ i, x i) ∘ (fun (x: Fin m' → G) ↦ x ∘ (Fin.cast h.symm)) := by
            ext x; simp; symm; apply Function.Bijective.sum_comp (Fin.cast_bijective h.symm)
          rw [this, ←MeasureTheory.Measure.map_map] <;> try fun_prop
          congr
          convert MeasureTheory.Measure.pi_map_piCongrLeft (finCongr h) (fun i ↦ Measure.map (X i) ℙ)
      }
    congr 1
    . rw [h]
    convert Finset.sum_bijective _ (Fin.cast_bijective h) ?_ ?_ using 1 <;> simp

lemma condMultiDist_of_cast {m m' : ℕ} (h : m' = m) {Ω : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i))
    {G S: Type*} [MeasureableFinGroup G] [Fintype S] (X : ∀ i, (Ω i) → G) (Y : ∀ i, (Ω i) → S) :
    D[fun i ↦ X (i.cast h) | fun i ↦ Y (i.cast h); fun i ↦ hΩ (i.cast h)] =
    D[X | Y ; hΩ] := by
      unfold condMultiDist
      let ι : (Fin m' → S) → (Fin m → S) := fun x i ↦ x (i.cast h.symm)
      have hι : Function.Bijective ι := by
        constructor
        . intro f g h'; ext i; replace h' := congrFun h' (i.cast h); simpa [ι] using h'
        intro f; use f ∘ (Fin.cast h); ext i; simp [ι]
      convert Function.Bijective.sum_comp hι _ with y _
      congr 1
      . convert Function.Bijective.prod_comp (Fin.cast_bijective h) _ with i _
        rfl
      convert multiDist_of_cast h _ _ X with i hmes i
      . simp; congr
      intros; simp; infer_instance

-- Spelling here is *very* janky. Feel free to respell
/-- Suppose that $X_{i,j}$, $1 \leq i,j \leq m$, are jointly independent $G$-valued random variables, such that for each $j = 1,\dots,m$, the random variables $(X_{i,j})_{i = 1}^m$
coincide in distribution with some permutation of $X_{[m]}$.
  Write
$$ {\mathcal I} := \bbI[ \bigl(\sum_{i=1}^m X_{i,j}\bigr)_{j =1}^{m}
: \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i = 1}^m
\; \big| \; \sum_{i=1}^m \sum_{j = 1}^m X_{i,j} ].
 $$
 Then ${\mathcal I} \leq 4 m^2 \eta k.$
-/
lemma mutual_information_le {G Ωₒ : Type u} [MeasureableFinGroup G] [MeasureSpace Ωₒ]
  {p : multiRefPackage G Ωₒ} {Ω : Type u} [hΩ : MeasureSpace Ω] [IsProbabilityMeasure hΩ.volume]
  {X : ∀ i, Ω → G} (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X)
  (h_min : multiTauMinimizes p (fun _ ↦ Ω) (fun _ ↦ hΩ) X) {Ω' : Type*} [hΩ': MeasureSpace Ω']
  [IsProbabilityMeasure hΩ'.volume]
  {X' : Fin p.m × Fin p.m → Ω' → G} (hX' : ∀ i j, Measurable (X' (i, j)))
  (h_indep': iIndepFun X')
  (hperm : ∀ j, ∃ e : Fin p.m ≃ Fin p.m, IdentDistrib (fun ω ↦ (fun i ↦ X' (i, j) ω))
    (fun ω ↦ (fun i ↦ X (e i) ω))) :
  I[ fun ω ↦ ( fun j ↦ ∑ i, X' (i, j) ω) : fun ω ↦ ( fun i ↦ ∑ j, X' (i, j) ω) |
    fun ω ↦ ∑ i, ∑ j, X' (i, j) ω ] ≤ 2 * p.m * (2*p.m + 1) * p.η * D[ X; (fun _ ↦ hΩ)] := by
    have hm := p.hm
    have hη := p.hη
    set I₀ := I[ fun ω ↦ ( fun j ↦ ∑ i, X' (i, j) ω) : fun ω ↦ ( fun i ↦ ∑ j, X' (i, j) ω) |
    fun ω ↦ ∑ i, ∑ j, X' (i, j) ω ]
    set k := D[X ; fun x ↦ hΩ]
    set one : Fin p.m := ⟨ 1, by omega ⟩
    set last : Fin p.m := ⟨ p.m-1, by omega ⟩
    set column : Fin p.m → Fin p.m → Ω' → G := fun j i ω ↦ X' (i, j) ω
    set V : Fin p.m → Ω' → G := fun i ω ↦ ∑ j, X' (i, j) ω
    set S : Fin p.m → Fin p.m → Ω' → G := fun i j ↦ ∑ k ∈ .Ici j, X' (i, k)
    set A : Fin p.m → ℝ := fun j ↦ D[ column j; fun _ ↦ hΩ']
      - D[ column j | fun i ↦ S i j; fun _ ↦ hΩ']
    set B : ℝ := D[ column last; fun _ ↦ hΩ'] - D[ fun i ω ↦ ∑ j, X' (i, j) ω; fun _ ↦ hΩ']

    have h1 : I₀ ≤ ∑ j ∈ .Iio last, A j + B := by
      -- significant dependent type hell here because `p.m` is not defeq of the form `m+1`.
      -- One might refactor the rest of the argument to do this, but I think this claim is
      -- the only place where it is a serious issue.
      set m := p.m - 1
      have hm' : m+1 = p.m := by omega
      let X'' : Fin (m+1) × Fin (m+1) → Ω' → G := fun (i,j) ↦ X' (i.cast hm', j.cast hm')
      convert cor_multiDist_chainRule _ X'' (by fun_prop) _ using 1 <;> try infer_instance
      . simp [I₀]
        let ι : (Fin (m+1) → G) → (Fin p.m → G) := fun f ↦ f ∘ (Fin.cast hm'.symm)
        have hι : Function.Injective ι := by
          intro f g h; ext i; replace h := congrFun h (i.cast hm'); simpa [ι] using h
        observe hid : Function.Injective (id: G → G)
        convert condMutualInfo_of_inj' _ _ _ _ hι hι hid using 2 <;> try infer_instance
        all_goals try fun_prop
        . ext ω j; simp [ι, X'']; symm
          apply Function.Bijective.sum_comp (Fin.cast_bijective hm') (fun i ↦ X' (i, j) ω)
        . ext ω i; simp [ι, X'']; symm
          apply Function.Bijective.sum_comp (Fin.cast_bijective hm') (fun j ↦ X' (i, j) ω)
        . ext ω
          rw [←Multiset.sum_eq_foldr, ←Finset.sum_eq_multiset_sum, ←Finset.sum_product']
          simp; apply Function.Bijective.sum_comp ⟨ _, _ ⟩ (fun x ↦ X' x ω)
          . intro ⟨ i, j ⟩ ⟨ i', j' ⟩ h; simpa using h
          intro ⟨ i, j ⟩; use ⟨ i.cast hm'.symm, j.cast hm'.symm ⟩; simp
        simp_rw [←Multiset.sum_eq_foldr, ←Finset.sum_eq_multiset_sum]
        fun_prop
      . rw [add_sub_assoc]; congr 1
        . convert Finset.sum_image (g := fun j:Fin m ↦ j.castSucc.cast hm')
            (f := A) (s := Finset.univ) _ using 2 with _ _ n _
          . ext ⟨ n, hn ⟩; simp [last]; constructor
            . intro h; use ⟨ n, by omega ⟩; simp
            rintro ⟨ ⟨ n', hn' ⟩, h ⟩; simp at h; omega
          . simp [A, X'', column, S]; congr 1
            . convert multiDist_of_cast hm' (fun _ ↦ hΩ') inferInstance _ with i
              rfl
            convert condMultiDist_of_cast hm' (fun _ ↦ hΩ') (fun i ↦ X' (i, Fin.cast hm' n.castSucc)) (fun i ↦ ∑ k ∈ Finset.Ici (Fin.cast hm' n.castSucc), X' (i, k)) using 2
            ext i ω; simp
            convert Finset.sum_map _ (finCongr hm'.symm).toEmbedding _
            ext i; simp
          simp
        simp [B, column, X'']; congr 1
        . symm; convert multiDist_of_cast hm' (fun _ ↦ hΩ') inferInstance _ with i
          rfl
        symm; convert multiDist_of_cast hm' (fun _ ↦ hΩ') inferInstance _ with i
        ext ω; simp
        apply Function.Bijective.sum_comp (Fin.cast_bijective hm') (fun j ↦ X' (Fin.cast hm' i, j) ω)
      apply ProbabilityTheory.iIndepFun.precomp _ h_indep'
      intro ⟨ i, j ⟩ ⟨ i', j' ⟩ h; simpa using h

    have h2 {j : Fin p.m} (hj: j ∈ Finset.Iio last)
      : A j ≤ p.η * (k + ∑ i, d[ X' (i,j) # X' (i,j) | S i j ]) := by
        sorry

    have h3 : B ≤ p.η * ∑ i, d[ X' (i, last) # V i ] := by
      sorry

    have h4 (i: Fin p.m) {j : Fin p.m} (hj: j ∈ Finset.Iio last) :
      d[ X' (i,j) # X' (i,j) | S i j ] ≤ d[ X' (i,j) # X' (i,j) ]
        + (H[S i j] - H[S i (j+one)]) / 2 := by
        sorry

    have h5 (i: Fin p.m) :
      ∑ j ∈ .Iio last, d[ X' (i,j) # X' (i,j) | S i j ]
        ≤ ∑ j ∈ .Iio last, d[ X' (i,j) # X' (i,j) ] + (H[V i] - H[X' (i, last)]) / 2 := calc
        _ ≤ ∑ j ∈ .Iio last, (d[ X' (i,j) # X' (i,j) ] + (H[S i j] - H[S i (j+one)]) / 2) := by
          apply Finset.sum_le_sum; intro j hj; exact h4 i hj
        _ = _ := by
          rw [Finset.sum_add_distrib, ←Finset.sum_div]; congr
          convert Finset.sum_range_sub' (fun k ↦ H[∑ j ∈ {j|j.val ≥ k}, X' (i,j)]) (p.m-1)
          . have (k:Fin p.m): S i k = ∑ j ∈ {j|j.val ≥ k.val}, X' (i,j) := by
              unfold S; congr
              ext ⟨ j, hj ⟩; obtain ⟨ k, hk ⟩ := k; simp
            simp_rw [this]
            convert Finset.sum_nbij (fun i ↦ i.val) (s := Finset.Iio last)  _ _ _ _
            . intro ⟨ _, _ ⟩; simp [last]
            . intro ⟨ _, _⟩ _ ⟨ _, _ ⟩ _; simp
            . intro _ hi; simpa [last] using hi
            intro ⟨ j, hj ⟩ hj'
            simp [last, one] at hj' ⊢
            rcongr ⟨ k, hk ⟩
            have : (j+1) % p.m = j+1 := Nat.mod_eq_of_lt (by omega)
            simp [←Fin.val_fin_le, Fin.val_add, this]
          . ext ω; simp [V]
          ext ω; simp; symm; convert Finset.sum_singleton _ last
          ext ⟨ j, hk ⟩; simp [last]; omega

    have h6 (i: Fin p.m) :
      d[ X' (i, last) # V i ] ≤ d[ X' (i, last) # X' (i, last) ]
        + (H[V i] - H[X' (i, last)]) / 2 := by
        sorry

    have h7 : I₀/p.η ≤ p.m * k + p.m * ∑ i, d[X i # X i] + ∑ i, H[V i] - ∑ i, H[X i] := by
      sorry

    have h8 (i: Fin p.m) : H[V i] ≤ H[ ∑ j, X j] + ∑ j, d[X' (i,j) # X' (i,j)] := by
      sorry

    have h9 : ∑ i, H[V i] - ∑ i, H[X i] ≤ p.m * ∑ i, d[X i # X i] + p.m * k := by
      sorry

    have h10 : I₀/p.η ≤ 2 * p.m * ∑ i, d[X i # X i] + 2 * p.m * k := by linarith

    have h11 : ∑ i, d[X i # X i] ≤ 2 * p.m * k := by
      convert multidist_ruzsa_II hm _ _ _ hX _ <;> try infer_instance

    calc
       _ ≤ p.η * (2 * p.m * ∑ i, d[X i # X i] + 2 * p.m * k) := by rwa [←div_le_iff₀' (by positivity)]
      _ ≤ p.η * (2 * p.m * (2 * p.m * k) + 2 * p.m * k) := by gcongr
      _ = _ := by ring
