import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import PFR.Mathlib.Data.Fin.Basic
import PFR.MultiTauFunctional


/-!
# Bounding the mutual information


## Main definitions:


## Main results

-/

universe u
open MeasureTheory ProbabilityTheory



lemma multiDist_of_cast {m m' : ℕ} (h : m' = m) {Ω : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩfin : ∀ i, IsFiniteMeasure (hΩ i).volume)
    {G: Type*} [MeasurableFinGroup G] (X : ∀ i, (Ω i) → G)  :
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

/-- For Mathlib? -/
lemma ProbabilityTheory.iIndepFun.sum_elim {Ω I J G:Type*} [MeasurableSpace Ω]  [hG: MeasurableSpace G] (μ: Measure Ω) {f: (x:I) → Ω → G} {g: (y:J) → Ω → G} (hf_indep: iIndepFun f μ) (hg_indep: iIndepFun g μ)
(hindep: IndepFun (fun ω x ↦ f x ω) (fun ω y ↦ g y ω) μ) : iIndepFun (Sum.elim f g) μ := by
  rw [iIndepFun_iff] at hf_indep hg_indep ⊢
  intro s E hE
  have : s.toLeft.disjSum s.toRight = s := Finset.toLeft_disjSum_toRight
  rw [←this, Finset.prod_disjSum,←hf_indep,←hg_indep]
  . simp_rw [MeasurableSpace.measurableSet_comap] at hE
    choose F hF using hE
    let S := ⋂ (i:s.toLeft), {x: I → G | x i ∈ F (Sum.inl i) (Finset.mem_toLeft.mp i.property)}
    let T := ⋂ (j:s.toRight), {y: J → G | y j ∈ F (Sum.inr j) (Finset.mem_toRight.mp j.property)}
    convert hindep.measure_inter_preimage_eq_mul S T _ _
    . ext ω; simp [S,T]; apply and_congr <;> {
        apply forall_congr'; intro i
        constructor
        . intro h hi; simp [←(hF _ hi).2, hi] at h; convert h
        intro h hi; specialize h hi; simp [←(hF _ hi).2]; convert h
      }
    . ext ω; simp [S]; apply forall_congr'; intro i
      constructor
      . intro h hi; simp [←(hF _ hi).2, hi] at h; convert h
      intro h hi; specialize h hi; simp [←(hF _ hi).2]; convert h
    . ext ω; simp [T]; apply forall_congr'; intro i
      constructor
      . intro h hi; simp [←(hF _ hi).2, hi] at h; convert h
      intro h hi; specialize h hi; simp [←(hF _ hi).2]; convert h
    all_goals {
      apply MeasurableSet.iInter; intro ⟨ i, hi ⟩
      simp only
      convert measurableSet_preimage (measurable_pi_apply i) _
      apply (hF _ _).1
    }
  . intro i hi; apply hE; exact Finset.mem_toRight.mp hi
  intro j hj; apply hE; exact Finset.mem_toLeft.mp hj


lemma condMultiDist_of_cast {m m' : ℕ} (h : m' = m) {Ω : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i))
    {G S: Type*} [MeasurableFinGroup G] [Fintype S] (X : ∀ i, (Ω i) → G) (Y : ∀ i, (Ω i) → S) :
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

set_option maxHeartbeats 300000 in
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
lemma mutual_information_le {G Ωₒ : Type u} [MeasurableFinGroup G] [MeasureSpace Ωₒ]
  {p : multiRefPackage G Ωₒ} {Ω : Type u} [hΩ : MeasureSpace Ω] [IsProbabilityMeasure hΩ.volume]
  {X : Fin p.m → Ω → G} (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X)
  (h_min : multiTauMinimizes p (fun _ ↦ Ω) (fun _ ↦ hΩ) X) {Ω' : Type u} [hΩ': MeasureSpace Ω']
  [IsProbabilityMeasure hΩ'.volume]
  {X' : Fin p.m × Fin p.m → Ω' → G} (hX' : ∀ i j, Measurable (X' (i, j)))
  (h_indep': iIndepFun X')
  (hperm : ∀ j, ∃ e : Fin p.m ≃ Fin p.m, IdentDistrib (fun ω ↦ (fun i ↦ X' (i, j) ω))
    (fun ω ↦ (fun i ↦ X (e i) ω))) :
  I[ fun ω ↦ ( fun j ↦ ∑ i, X' (i, j) ω) : fun ω ↦ ( fun i ↦ ∑ j, X' (i, j) ω) |
    fun ω ↦ ∑ i, ∑ j, X' (i, j) ω ] ≤ p.m * (4*p.m+1) * p.η * D[ X; (fun _ ↦ hΩ)] := by
    have hm := p.hm
    have _ : NeZero p.m := by rw [neZero_iff]; omega
    have hη := p.hη
    set I₀ := I[ fun ω ↦ ( fun j ↦ ∑ i, X' (i, j) ω) : fun ω ↦ ( fun i ↦ ∑ j, X' (i, j) ω) |
    fun ω ↦ ∑ i, ∑ j, X' (i, j) ω ]
    set k := D[X ; fun x ↦ hΩ]
    have hk: 0 ≤ k := multiDist_nonneg _ inferInstance _ (by fun_prop)
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

    have hD (j: Fin p.m) : D[column j ; fun x ↦ hΩ'] = k := by
      obtain ⟨ e, he ⟩ := hperm j
      calc
        _ = D[fun i ω ↦ X (e i) ω; fun x ↦ hΩ] := by
          apply multiDist_copy _ _ _ _ _
          intro i; exact IdentDistrib.comp (u := fun x ↦ x i) he (by fun_prop)
        _ = _ := by
          convert multiDist_of_perm (fun _ ↦ hΩ) _ _ e <;> try infer_instance

    have h2 {j : Fin p.m} (hj: j ∈ Finset.Iio last)
      : A j ≤ p.η * ∑ i, d[ X' (i,j) # X' (i,j) | S i j ] := by
      obtain ⟨ e, he ⟩ := hperm j
      simp only [A, hD]
      convert sub_condMultiDistance_le' inferInstance hX h_min inferInstance (X' := fun i ↦ X' (i, j)) _ _ e using 3 with i _ <;> try infer_instance
      all_goals try fun_prop
      apply condRuzsaDist'_of_copy <;> try fun_prop
      . exact IdentDistrib.comp (u := fun x ↦ x i) he (by fun_prop)
      apply IdentDistrib.refl; fun_prop

    have h3 : B ≤ p.η * ∑ i, d[ X' (i, last) # V i ] := by
      obtain ⟨ e, he ⟩ := hperm last
      simp only [B, hD, V]
      convert sub_multiDistance_le' inferInstance hX h_min inferInstance (X' := fun i ↦ V i) (by fun_prop) e using 3 with i _
      apply IdentDistrib.rdist_congr_left (by fun_prop); exact IdentDistrib.comp (u := fun x ↦ x i) he (by fun_prop)

    have h4 (i: Fin p.m) {j : Fin p.m} (hj: j ∈ Finset.Iio last) :
      d[ X' (i,j) # X' (i,j) | S i j ] ≤ d[ X' (i,j) # X' (i,j) ]
        + (H[S i j] - H[S i (j+one)]) / 2 := calc
      _ ≤ d[ X' (i,j) # X' (i,j) ] + I[ X' (i,j) : S i j ] / 2 := by
        apply condRuzsaDist_le' <;> fun_prop
      _ = d[ X' (i,j) # X' (i,j) ] + (H[S i j] - H[S i (j+one) |  X' (i,j) ]) / 2 := by
        congr
        rw [mutualInfo_comm]
        convert mutualInfo_eq_entropy_sub_condEntropy .. using 2 <;> try infer_instance
        all_goals try fun_prop
        rw [←condEntropy_add_left] <;> try fun_prop
        congr
        convert Finset.add_sum_erase (a := j) .. using 3
        . rfl
        . obtain ⟨ j, hj' ⟩ := j; ext ⟨ k, hk ⟩
          simp [last, one] at hj ⊢
          have : (j+1) % p.m = j+1 := Nat.mod_eq_of_lt (by omega)
          simp [←Fin.val_fin_le, Fin.val_add, this] at hj ⊢; omega
        simp
      _ = _ := by
        congr; apply ProbabilityTheory.IndepFun.condEntropy_eq_entropy <;> try fun_prop
        let T : Finset (Fin p.m × Fin p.m) := {q|q.2>j}
        let T' : Finset (Fin p.m × Fin p.m) := {q|q.2=j}
        let φ : (T → G) → G := fun f ↦ ∑ k : Finset.Ici (j + one), f ⟨(i, k), by
          obtain ⟨ ⟨ k, hk⟩, hk' ⟩ := k; obtain ⟨ j, hj' ⟩ := j; simp [last, one] at hj ⊢
          have : (j+1) % p.m = j+1 := Nat.mod_eq_of_lt (by omega)
          simp [T,←Fin.val_fin_le, Fin.val_add, this, one] at hj ⊢ hk'; omega⟩
        let φ' : (T' → G) → G := fun f ↦ f ⟨ (i,j), by simp [T'] ⟩
        convert iIndepFun.finsets_comp' _ h_indep' (by fun_prop) (φ := φ) (show Measurable φ by fun_prop) (show Measurable φ' by fun_prop) with ω ω <;> try simp [φ,φ']
        . unfold S
          simp; symm; convert Finset.sum_attach _ _; rfl
        rw [Finset.disjoint_left]; rintro ⟨ _, _ ⟩ h h'
        simp [T,T'] at h h'; order

    have h4a (i: Fin p.m) : ∑ j ∈ Finset.Iio last, (H[S i j] - H[S i (j + one)]) = H[V i] - H[X' (i, last)] := by
      convert Finset.sum_range_sub' (fun k ↦ H[∑ j ∈ {j|j.val ≥ k}, X' (i,j)]) (p.m-1)
      . have (k:Fin p.m): S i k = ∑ j ∈ {j|j.val ≥ k.val}, X' (i,j) := by
          unfold S; congr
          ext ⟨ j, hj ⟩; obtain ⟨ k, hk ⟩ := k; simp
        simp_rw [this]
        convert Finset.sum_nbij (fun i ↦ i.val) (s := Finset.Iio last) ..
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

    have h5 (i: Fin p.m) :
      ∑ j ∈ .Iio last, d[ X' (i,j) # X' (i,j) | S i j ]
        ≤ ∑ j ∈ .Iio last, d[ X' (i,j) # X' (i,j) ] + (H[V i] - H[X' (i, last)]) / 2 := calc
        _ ≤ ∑ j ∈ .Iio last, (d[ X' (i,j) # X' (i,j) ] + (H[S i j] - H[S i (j+one)]) / 2) := by
          apply Finset.sum_le_sum; intro j hj; exact h4 i hj
        _ = _ := by
          rw [Finset.sum_add_distrib, ←Finset.sum_div]; congr
          exact h4a i

    have h6 (i: Fin p.m) :
      d[ X' (i, last) # V i ] ≤ d[ X' (i, last) # X' (i, last) ]
        + (H[V i] - H[X' (i, last)]) / 2 := by
        have : V i = X' (i, last) + ∑ j ∈ .Iio last, X' (i,j) := by
          symm; ext ω; simp [V]; convert Finset.add_sum_erase (a := last) .. using 3
          . rfl
          . ext ⟨ j, hj ⟩; simp [last]; omega
          simp
        simp [this, ←inv_mul_eq_div]
        apply kvm_ineq_III_aux' <;> try fun_prop
        let T : Finset (Fin p.m × Fin p.m) := {q|q.2=last}
        let T' : Finset (Fin p.m × Fin p.m) := {q|q.2<last}
        let φ : (T → G) → G := fun f ↦ f ⟨(i, last), by simp [T]⟩
        let φ' : (T' → G) → G := fun f ↦ ∑ j : Finset.Iio last, f ⟨ (i,j), by obtain ⟨ j, hj ⟩ := j; simpa [T'] using hj ⟩
        convert iIndepFun.finsets_comp' _ h_indep' (by fun_prop) (φ := φ) (show Measurable φ by fun_prop) (show Measurable φ' by fun_prop) with ω ω <;> try simp [φ,φ']
        . symm; convert Finset.sum_attach _ _; rfl
        rw [Finset.disjoint_left]; rintro ⟨ _, _ ⟩ h h'
        simp [T,T'] at h h'; order

    have h7 : I₀/p.η ≤ p.m * ∑ i, d[X i # X i] + ∑ i, H[V i] - ∑ i, H[X i] := by
      rw [div_le_iff₀' hη]
      apply h1.trans
      calc
        _ ≤ ∑ j ∈ .Iio last, (p.η * (∑ i, d[ X' (i,j) # X' (i,j) | S i j ])) + p.η * ∑ i, d[ X' (i, last) # V i ] := by gcongr with j hj; exact h2 hj
        _ ≤ p.η * (∑ i, (∑ j ∈ .Iio last, d[ X' (i,j) # X' (i,j) ] + (H[V i] - H[X' (i, last)]) / 2)) +
        p.η * ∑ i, (d[ X' (i, last) # X' (i, last) ] + (H[V i] - H[X' (i, last)]) / 2) := by
          simp [←Finset.mul_sum, Finset.sum_add_distrib]; rw [Finset.sum_comm]; gcongr
          . rw [←Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _; exact h5 i
          rw [←Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _; exact h6 i
        _ = p.η * (∑ i, (∑ j ∈ .Iio last, d[ X' (i,j) # X' (i,j) ] + d[ X' (i, last) # X' (i, last) ]) + ∑ i, H[V i] - ∑ i, H[X' (i, last)]) := by
          simp_rw [Finset.sum_add_distrib, ←Finset.sum_div, Finset.sum_sub_distrib]; ring
        _ = p.η * (∑ j, (∑ i, d[ X' (i,j) # X' (i,j) ]) + ∑ i, H[V i] - ∑ i, H[X' (i, last)]) := by
          rw [Finset.sum_comm]
          rcongr i
          convert Finset.sum_erase_add _ _ _ using 3
          . ext ⟨ j, hj ⟩; simp [last]; omega
          . infer_instance
          simp
        _ = p.η * ((∑ j:Fin p.m, (∑ i, d[ X i # X i ])) + ∑ i, H[V i] - ∑ i, H[X i]) := by
          congr 2
          . congr; ext j; obtain ⟨ e, he ⟩ := hperm j
            convert Equiv.sum_comp e _ with i _
            apply IdentDistrib.rdist_congr <;> exact he.comp (u := fun x ↦ x i) (by fun_prop)
          obtain ⟨ e, he ⟩ := hperm last
          convert Equiv.sum_comp e _ with i _
          apply IdentDistrib.entropy_congr; exact he.comp (u := fun x ↦ x i) (by fun_prop)
        _ ≤ _ := by simp

    have h8 (i: Fin p.m) : H[V i] ≤ H[ ∑ j, X j] + ∑ j, d[X' (i,j) # X' (i,j)] := by
      obtain ⟨ ν, XX, XX', hν, hXX, hXX', h_indep_XX_XX', hident_X, hident_X', hfin_XX, hfin_XX'⟩ := independent_copies_finiteRange (X := fun ω i ↦ X i ω) (Y := fun ω q ↦ X' q ω)
        (by fun_prop) (by fun_prop) ℙ ℙ
      let Ω'' := (Fin p.m → G) × (Fin p.m × Fin p.m → G)
      let _ : MeasureSpace (Ω'') := ⟨ ν ⟩
      let Z : Fin p.m → Ω'' → G := fun i ω ↦ XX ω i
      let Z' : Fin p.m × Fin p.m → Ω'' → G := fun i ω ↦ XX' ω i
      -- the claim below could be abstracted into a Mathlib lemma.
      have hindep_Z : iIndepFun Z ℙ := by
        rw [iIndepFun_iff_map_fun_eq_pi_map] at h_indep ⊢ <;> try fun_prop
        convert h_indep with i
        . exact IdentDistrib.map_eq hident_X
        apply IdentDistrib.map_eq
        exact hident_X.comp (u := fun x ↦ x i) (by fun_prop)
      have hindep_Z' : iIndepFun Z' ℙ := by
        rw [iIndepFun_iff_map_fun_eq_pi_map] at h_indep' ⊢ <;> try fun_prop
        convert h_indep' with i
        . exact IdentDistrib.map_eq hident_X'
        apply IdentDistrib.map_eq
        exact hident_X'.comp (u := fun x ↦ x i) (by fun_prop)
      have hindep_all : iIndepFun (Sum.elim Z Z') ℙ := iIndepFun.sum_elim ℙ hindep_Z hindep_Z' h_indep_XX_XX'

      let s : Finset (Fin p.m ⊕ (Fin p.m × Fin p.m)) := Finset.image Sum.inl Finset.univ
      let t : Finset (Fin p.m ⊕ (Fin p.m × Fin p.m)) := Finset.image Sum.inr {q|q.1=i}
      have hdisj : Disjoint s t := by rw [Finset.disjoint_left]; simp [s,t]
      have hs: s.Nonempty := by use Sum.inl one; simp [s]
      have ht: t.Nonempty := by use Sum.inr (i,one); simp [t]
      choose e he using hperm
      let f : Fin p.m ⊕ (Fin p.m × Fin p.m) → Fin p.m ⊕ (Fin p.m × Fin p.m) := fun x ↦ match x with
      | Sum.inl i => Sum.inl i
      | Sum.inr (i,j) => Sum.inl ((e j) i)
      convert ent_of_sum_le_ent_of_sum hdisj hs ht _ _ _ hindep_all f _
      . apply IdentDistrib.entropy_congr
        convert hident_X'.symm.comp (u := fun x ↦ ∑ j:Fin p.m, x (i, j)) _ <;> try fun_prop
        ext ω; simp [Z, Z', t]
        apply Finset.sum_nbij' (Prod.snd) (fun j ↦ (i,j))
        on_goal 5 => simp; rintro a b rfl; rfl
        all_goals simp
      . apply IdentDistrib.entropy_congr
        convert hident_X.symm.comp (u := fun x ↦ ∑ j, x j) _ <;> try fun_prop
        all_goals ext ω; simp [Z, Z', s]
      . let g : Fin p.m ⊕ (Fin p.m × Fin p.m) → Fin p.m := fun x ↦ match x with
        | Sum.inl i => i
        | Sum.inr (i,j) => j
        apply Finset.sum_nbij' (fun j ↦ Sum.inr (i,j)) g <;> try simp [t,g,f]
        intro j
        have hident_1 : IdentDistrib (X' (i, j)) (Z' (i, j)) ℙ ℙ := by
          convert hident_X'.symm.comp (u := fun x ↦ x (i, j)) _; fun_prop
        have hident_2 : IdentDistrib (Z' (i, j)) (Z ((e j) i)) ℙ ℙ := by
          apply hident_1.symm.trans
          have h1 : IdentDistrib (X ((e j) i)) (Z ((e j) i)) ℙ ℙ := by
            convert hident_X.symm.comp (u := fun x ↦ x ((e j) i)) _; fun_prop
          have h2 : IdentDistrib (X' (i, j)) (X ((e j) i)) ℙ ℙ := by
            convert (he j).comp (u := fun x ↦ x i) _; fun_prop
          exact h2.trans h1
        calc
          _ = d[Z' (i, j) # Z ((e j) i)] :=
            IdentDistrib.rdist_congr hident_1 (hident_1.trans hident_2)
          _ = H[Z' (i, j) - Z ((e j) i)] - H[Z' (i,j)]/2 - H[Z ((e j) i)]/2 := by
            apply IndepFun.rdist_eq <;> try fun_prop
            symm
            apply h_indep_XX_XX'.comp (φ := fun x ↦ x ((e j) i)) (ψ := fun x ↦ x (i, j)) <;> fun_prop
          _ = H[Z' (i, j) - Z ((e j) i)] - H[Z ((e j) i)]/2 - H[Z ((e j) i)]/2 := by
            rw [IdentDistrib.entropy_congr hident_2]
          _ = _ := by ring
      . fun_prop
      . simp [Z,Z']; constructor
        . intros; infer_instance
        intro a b; infer_instance
      intro x; simp [f,t,s]; aesop

    have h9 : ∑ i, H[V i] ≤ p.m * ∑ i, d[X i # X i] + ∑ i, H[X i] + p.m * k := calc
      _ ≤ ∑ i, (H[ ∑ j, X j] + ∑ j, d[X' (i,j) # X' (i,j)]) := by
        apply Finset.sum_le_sum; intro i _; exact h8 i
      _ ≤ p.m * H[∑ j, X j] + ∑ j, ∑ i, d[X' (i, j) # X' (i, j)]  := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]; simp
      _ = (∑ i, H[X i] + p.m * k) + ∑ j:Fin p.m, ∑ i, d[X i # X i] := by
        congr
        . have : k = D[X; fun _ ↦ hΩ] := rfl
          rw [this, multiDist_indep _ _ h_indep]
          . field_simp; ring
          fun_prop
        ext j
        obtain ⟨ e, he ⟩ := hperm j
        convert Equiv.sum_comp e _ with i _
        apply IdentDistrib.rdist_congr <;> exact IdentDistrib.comp (u := fun x ↦ x i) he (by fun_prop)
      _ = _ := by simp; abel

    have h10 : I₀/p.η ≤ 2 * p.m * ∑ i, d[X i # X i] + p.m * k := by linarith

    have h11 : ∑ i, d[X i # X i] ≤ 2 * p.m * k := by
      convert multidist_ruzsa_II hm _ _ _ hX _ <;> try infer_instance

    calc
       _ ≤ p.η * (2 * p.m * ∑ i, d[X i # X i] + p.m * k) := by rwa [←div_le_iff₀' (by positivity)]
      _ ≤ p.η * (2 * p.m * (2 * p.m * k) + p.m * k) := by gcongr
      _ = _ := by ring
