import PFR.f2_vec
import PFR.first_estimate
import PFR.second_estimate

/-!
# Endgame

The endgame on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies
    of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $U := X_1 + X_2$
* $V := \tilde X_1 + X_2$
* $W := X_1 + \tilde X_1$
* $S := X_1 + X_2 + \tilde X_1 + \tilde X_2$.
* $I_1 := I[ U : V | S ]$
* $I_2 := I[ U : W | S ]$
* $I_3 := I[ V : W | S ]$ (not explicitly defined in Lean)

# Main results:

* `sum_condMutual_le` : An upper bound on the total conditional mutual information $I_1+I_2+I_3$.
* `sum_dist_diff_le`: A sum of the "costs" of $U$, $V$, $W$.
* `construct_good`: A construction of two random variables with small Ruzsa distance between them
  given some random variables with control on total cost, as well as total mutual information.
-/

open MeasureTheory ProbabilityTheory

open scoped BigOperators

variable {G : Type*} [addgroup: AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [elem: ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun (fun _i => hG) ![X₁, X₂, X₁', X₂'])

variable (h_min: tau_minimizes p X₁ X₂)

/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[ X₁ # X₂]

/-- `U := X₁ + X₂` -/
local notation3 "U" => X₁ + X₂

/-- `V := X₁' + X₂` -/
local notation3 "V" => X₁' + X₂

/-- `W := X₁' + X₁` -/
local notation3 "W" => X₁' + X₁

/-- `S := X₁ + X₂ + X₁' + X₂'` -/
local notation3 "S" => X₁ + X₂ + X₁' + X₂'

/-- `I₁ := I[ U : V | S ]`, the conditional mutual information of `U = X₁ + X₂` and `V = X₁' + X₂`
given the quadruple sum `S = X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => I[ U : V | S ]

/-- `I₂ := I[ U : W | S ]`, the conditional mutual information of `U = X₁ + X₂` and `W = X₁' + X₁`
given the quadruple sum `S = X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => I[ U : W | S ]

--(Mantas) this times out in the proof below
private lemma hmeas2 : Measurable
    (fun p : Fin 4 → G => ((p 0 + p 1, p 0 + p 2), p 0 + p 1 + p 2 + p 3)) := by
  apply Measurable.prod
  · apply Measurable.prod
    · exact (measurable_pi_apply _).add (measurable_pi_apply _)
    · exact (measurable_pi_apply _).add (measurable_pi_apply _)
  · apply Measurable.add
    · apply Measurable.add
      · exact (measurable_pi_apply _).add (measurable_pi_apply _)
      · apply measurable_pi_apply
    · apply measurable_pi_apply

/-- The quantity $I_3 = I[V:W|S]$ is equal to $I_2$. -/
lemma I₃_eq : I[ V : W | S ] = I₂ := by
  have h_indep2 : iIndepFun (fun _ ↦ hG) ![X₁', X₂, X₁, X₂'] := by
    apply ProbabilityTheory.iIndepFun.reindex (Equiv.swap (0 : Fin 4) 2)
    convert h_indep using 1
    ext x
    fin_cases x
    all_goals aesop
  have hident : IdentDistrib (fun a (i : Fin 4) => ![X₁, X₂, X₁', X₂'] i a)
    (fun a (j : Fin 4) => ![X₁', X₂, X₁, X₂'] j a) := by
    exact { aemeasurable_fst := by
              apply Measurable.aemeasurable
              rw [measurable_pi_iff]
              intro x
              fin_cases x;
              all_goals aesop
            aemeasurable_snd := by
              apply Measurable.aemeasurable
              rw [measurable_pi_iff]
              intro x
              fin_cases x;
              all_goals aesop
            map_eq := by
              rw [(ProbabilityTheory.iIndepFun_iff_map_prod_eq_prod_map_map (![X₁, X₂, X₁', X₂'])
              (fun _ ↦ hG) (Fin.cases hX₁ <| Fin.cases hX₂ <| Fin.cases hX₁' <|
              Fin.cases hX₂' Fin.rec0)).mp h_indep,
              (ProbabilityTheory.iIndepFun_iff_map_prod_eq_prod_map_map (![X₁', X₂, X₁, X₂'])
              (fun _ ↦ hG) (Fin.cases hX₁' <| Fin.cases hX₂ <| Fin.cases hX₁ <|
              Fin.cases hX₂' Fin.rec0)).mp h_indep2]
              congr
              ext i
              fin_cases i
              all_goals simp[h₁.map_eq] }
  have hmeas1 : Measurable (fun p : Fin 4 → G => (p 0 + p 1, p 0 + p 1 + p 2 + p 3)) := by
    simp_all only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    apply Measurable.prod
    · exact (measurable_pi_apply _).add (measurable_pi_apply _)
    · apply Measurable.add
      · apply Measurable.add
        · exact (measurable_pi_apply _).add (measurable_pi_apply _)
        · apply measurable_pi_apply
      · apply measurable_pi_apply
  have hUVS : IdentDistrib (prod U S) (prod V S)
  · convert (IdentDistrib.comp hident hmeas1)
    all_goals {simp; abel}
  have hUVWS : IdentDistrib (prod (prod U W) S) (prod (prod V W) S)
  · convert (IdentDistrib.comp hident hmeas2)
    all_goals {simp; abel}
  have hU : Measurable U := Measurable.add hX₁ hX₂
  have hV : Measurable V := Measurable.add hX₁' hX₂
  have hW : Measurable W := Measurable.add hX₁' hX₁
  have hS : Measurable S := by measurability
  rw [condMutualInfo_eq hV hW hS, condMutualInfo_eq hU hW hS, chain_rule'' ℙ hU hS,
    chain_rule'' ℙ hV hS, chain_rule'' ℙ hW hS, chain_rule'' ℙ _ hS, chain_rule'' ℙ _ hS,
    IdentDistrib.entropy_eq hUVS, IdentDistrib.entropy_eq hUVWS]
  · exact Measurable.prod (by exact hU) (by exact hW)
  · exact Measurable.prod (by exact hV) (by exact hW)


/--
$$ I(U : V | S) + I(V : W | S) + I(W : U | S) $$
is less than or equal to
$$ 6 \eta k - \frac{1 - 5 \eta}{1-\eta} (2 \eta k - I_1).$$
-/
lemma sum_condMutual_le :
    I[ U : V | S ] + I[ V : W | S ] + I[ W : U | S ]
      ≤ 6 * η * k - (1 - 5 * η) / (1 - η) * (2 * η * k - I₁) := by
  have : I[W:U|S] = I₂ := by
    rw [condMutualInfo_comm]
    · exact Measurable.add' hX₁' hX₁
    · exact Measurable.add' hX₁ hX₂
  rw [I₃_eq, this]
  have h₂ := second_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h := add_le_add (add_le_add_left h₂ I₁) h₂
  convert h using 1
  field_simp [η]
  ring
  all_goals { simpa }

local notation3:max "c[" A "; " μ " # " B " ; " μ' "]" =>
  d[p.X₀₁; ℙ # A; μ] - d[p.X₀₁ # X₁] + (d[p.X₀₂; ℙ # B; μ'] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " # " B "]" =>
  d[p.X₀₁ # A] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # B] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " | " B " # " C " | " D "]" => d[p.X₀₁ # A|B] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # C|D] - d[p.X₀₂ # X₂])

lemma ruzsa_helper_lemma' [IsProbabilityMeasure (ℙ : Measure Ω)] {X B C : Ω → G}
    (hX : Measurable X) (hB : Measurable B) (hC : Measurable C)
    (h_indep : IndepFun X (⟨B, C⟩)) :
    d[X # B | B + C] = d[X # C | B + C] := by
  let π : G × G →+ G :=
  { toFun := fun x ↦ x.2 - x.1
    map_zero' := by simp
    map_add' := fun a b ↦ by simp only [Prod.snd_add, Prod.fst_add,
      ElementaryAddCommGroup.sub_eq_add]; abel }
  let Y : Fin 4 → Ω → G := ![-X, C, fun _ ↦ 0, B + C]
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    fin_cases i
    exacts [hX.neg, hC, measurable_const, hB.add hC]
  calc d[X # B | B + C]
    = d[X | fun _ : Ω ↦ (0 : G) # B | B + C] := by rw [cond_rdist_of_const hX]
  _ = d[π ∘ ⟨-X, fun _ : Ω ↦ (0 : G)⟩ | fun _ : Ω ↦ (0 : G) # π ∘ ⟨C, B + C⟩ | B + C] := by
        congr
        · ext1 ω; simp
        · ext1 ω
          simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, Pi.add_apply]
          abel
  _ = d[π ∘ ⟨Y 0, Y 2⟩ | Y 2 # π ∘ ⟨Y 1, Y 3⟩ | Y 3] := by congr
  _ = d[-X | fun _ : Ω ↦ (0 : G) # C | B + C] := by
        rw [cond_rdist_of_inj_map _ _ hY_meas π (fun _ ↦ sub_right_injective)]
        · congr
        · have h1 : (⟨Y 0, Y 2⟩) = (fun x ↦ (-x, 0)) ∘ X := by ext1 ω; simp
          have h2 : (⟨Y 1, Y 3⟩) = (fun p ↦ (p.2, p.1 + p.2)) ∘ (⟨B, C⟩) := by
            ext1 ω;
            simp only [ElementaryAddCommGroup.neg_eq_self, Matrix.cons_val_one, Matrix.head_cons,
              Function.comp_apply, Prod.mk.injEq, Matrix.cons_val', Pi.add_apply, Matrix.empty_val',
              Matrix.cons_val_fin_one, true_and]
            congr
          rw [h1, h2]
          refine h_indep.comp ?_ ?_
          · exact measurable_neg.prod_mk measurable_const
          · exact measurable_snd.prod_mk (measurable_fst.add measurable_snd)
  _ = d[-X # C | B + C] := by rw [cond_rdist_of_const]; exact hX.neg
  _ = d[X # C | B + C] := by -- because ElementaryAddCommGroup G 2
        congr
        simp

lemma ruzsa_helper_lemma {B C : Ω → G} (hB : Measurable B) (hC : Measurable C) :
    d[p.X₀₂ # B | B + C] = d[p.X₀₂ # C | B + C] := by
  -- we want to apply `ruzsa_helper_lemma'`, but for that all variables need to be in the same
  -- probability space
  let Ω' := Ω₀₂ × Ω
  set X₂' : Ω' → G := p.X₀₂ ∘ Prod.fst with hX₂'_def
  have hX₂' : Measurable X₂' := p.hmeas2.comp measurable_fst
  let B' : Ω' → G := B ∘ Prod.snd
  have hB' : Measurable B' := hB.comp measurable_snd
  let C' : Ω' → G := C ∘ Prod.snd
  have hC' : Measurable C' := hC.comp measurable_snd
  -- h1 and h2 should be applications of a new lemma?
  have h1 : d[p.X₀₂ # B | B + C] = d[X₂' # B' | B' + C'] := by
    refine cond_rdist'_of_copy p.X₀₂ hB (hB.add hC) X₂' hB' (hB'.add hC') ?_ ?_
    · constructor
      · exact p.hmeas2.aemeasurable
      · exact hX₂'.aemeasurable
      · rw [Measure.volume_eq_prod, ← Measure.map_map p.hmeas2 measurable_fst]
        simp
    · constructor
      · exact (hB.prod_mk (hB.add hC)).aemeasurable
      · exact (hB'.prod_mk (hB'.add hC')).aemeasurable
      · rw [Measure.volume_eq_prod]
        have : ⟨B', B' + C'⟩ = (⟨B, B + C⟩) ∘ Prod.snd := by ext1 _; simp
        rw [this, ← Measure.map_map _ measurable_snd]
        · simp only [Measure.map_snd_prod, measure_univ, one_smul]
          rfl
        · exact hB.prod_mk (hB.add hC)
  have h2 : d[p.X₀₂ # C | B + C] = d[X₂' # C' | B' + C'] := by
    refine cond_rdist'_of_copy p.X₀₂ hC (hB.add hC) X₂' hC' (hB'.add hC') ?_ ?_
    · constructor
      · exact p.hmeas2.aemeasurable
      · exact hX₂'.aemeasurable
      · rw [Measure.volume_eq_prod, ← Measure.map_map p.hmeas2 measurable_fst]
        simp
    · constructor
      · exact (hC.prod_mk (hB.add hC)).aemeasurable
      · exact (hC'.prod_mk (hB'.add hC')).aemeasurable
      · rw [Measure.volume_eq_prod]
        have : ⟨C', B' + C'⟩ = (⟨C, B + C⟩) ∘ Prod.snd := by ext1 _; simp
        rw [this, ← Measure.map_map _ measurable_snd]
        · simp only [Measure.map_snd_prod, measure_univ, one_smul]
          rfl
        · exact hC.prod_mk (hB.add hC)
  rw [h1, h2, ruzsa_helper_lemma' hX₂' hB' hC']
  rw [indepFun_iff_map_prod_eq_prod_map_map hX₂' (hB'.prod_mk hC'), Measure.volume_eq_prod]
  have h_prod : (fun ω ↦ (X₂' ω, prod B' C' ω)) = Prod.map p.X₀₂ (⟨B, C⟩) := by ext1; simp
  have h_comp_snd : (fun a ↦ (B' a, C' a)) = (⟨B, C⟩) ∘ Prod.snd := by ext1; simp
  rw [h_prod, h_comp_snd, hX₂'_def, ← Measure.map_map _ measurable_snd,
    ← Measure.map_map _ measurable_fst, Measure.map_prod_map]
  rotate_left
  · simp only [Measure.map_fst_prod, measure_univ, one_smul]
    infer_instance
  · simp only [Measure.map_snd_prod, measure_univ, one_smul]
    infer_instance
  · exact p.hmeas2
  · exact hB.prod_mk hC
  · exact p.hmeas2
  · exact hB.prod_mk hC
  congr
  · simp
  · simp

variable [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

lemma hU : H[U] = H[X₁' + X₂'] := by
  apply IdentDistrib.entropy_eq
  apply ProbabilityTheory.IdentDistrib.add
  repeat assumption
  · have aux : IndepFun (Matrix.vecCons X₁ ![X₂, X₁', X₂'] 0)
                        (Matrix.vecCons X₁ ![X₂, X₁', X₂'] 1) := by
      apply ProbabilityTheory.iIndepFun.indepFun h_indep (i := 0) (j := 1); simp
    simp at aux; assumption
  · have aux : IndepFun (Matrix.vecCons X₁ ![X₂, X₁', X₂'] 2)
                        (Matrix.vecCons X₁ ![X₂, X₁', X₂'] 3) := by
      apply ProbabilityTheory.iIndepFun.indepFun h_indep (i := 2) (j := 3); decide
    simp at aux; assumption

abbrev S1 : Fin 3 → Finset (Fin 4)
  | 0 => {0}
  | 1 => {1}
  | 2 => {2, 3}

def f1 (x : Fin 3) : Ω → Π _ : S1 x, G :=
  match x with
  | 0 => fun ω _ => X₁ ω
  | 1 => fun ω _ => X₂ ω
  | 2 => fun ω i => match i with
                    | { val := 2, property := _ } => X₁' ω
                    | { val := 3, property := _ } => X₂' ω

variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition1' : iIndepFun (fun _ => MeasurableSpace.pi) (f1 X₁ X₂ X₁' X₂') := by
  have aux_0 (i : { x // x ∈ S1 0 }) : (↑i : Fin 4) = 0 := by
    rw [← List.mem_singleton]
    apply i.property
  have aux_1 (i : { x // x ∈ S1 1 }) : (↑i : Fin 4) = 1 := by
    rw [← List.mem_singleton]
    apply i.property
  have aux : f1 X₁ X₂ X₁' X₂' = fun (l : Fin 3) (x : Ω) (i : S1 l) ↦ ![X₁, X₂, X₁', X₂'] (↑i) x := by
    funext a
    match a with
    | 0 => simp [aux_0]; rfl
    | 1 => simp [aux_1]; rfl
    | 2 =>
      funext x i
      have hi : i = (2 : Fin 4) ∨ i = (3 : Fin 4) := by
        match i with
        | { val := 2, property := _ }
        | { val := 3, property := _ } => reduce; decide
      rcases hi with hi2 | hi3
      · rw [show i = { val := 2, property := by decide } from (by aesop)]
        rfl
      · rw [show i = { val := 3, property := by decide } from (by aesop)]
        rfl
  rw [aux]
  apply iIndepFun.prod
  exact h_indep

def g : (i : Fin 3) → ({ x // x ∈ S1 i } → G) → G
  | 0 => fun X => X { val := 0, property := by decide }
  | 1 => fun X => X { val := 1, property := by decide }
  | 2 => fun X => X { val := 2, property := by decide } + X { val := 3, property := by decide }

lemma measurable_g (i : Fin 3) : Measurable (g (G := G) i) := by
  match i with
  | 2 =>
    have aux :
    Measurable (fun (X : { x // x ∈ S1 2 } → G) ↦ X { val := 2, property := by decide }
                                                 + X { val := 3, property := by decide }):= by
      measurability
    exact aux
  | 0 =>
    unfold g
    have aux :
    Measurable (fun (X : { x // x ∈ S1 0 } → G) ↦ X { val := 0, property := by decide }) := by
      measurability
    exact aux
  | 1 =>
    have aux :
    Measurable (fun (X : { x // x ∈ S1 1 } → G) ↦ X { val := 1, property := by decide }) := by
      measurability
    exact aux

variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition1 : iIndepFun (fun _ ↦ hG) ![X₁, X₂, X₁' + X₂'] := by
  have aux : ![X₁, X₂, X₁' + X₂'] = (fun i => g i ∘ f1 X₁ X₂ X₁' X₂' i) := by
    funext i
    match i with
    | 0 | 1 | 2 => rfl
  rw [aux]
  apply iIndepFun.comp (independenceCondition1' h_indep) g measurable_g

/--
$$ \sum_{i=1}^2 \sum_{A\in\{U,V,W\}} \big(d[X^0_i;A|S] - d[X^0_i;X_i]\big)$$
is less than or equal to
$$ \leq (6 - 3\eta) k + 3(2 \eta k - I_1).$$
-/
lemma sum_dist_diff_le :
  c[U|S # U|S] + c[V|S # V|S]  + c[W|S # W|S] ≤ (6 - 3 * η)*k + 3 * (2*η*k - I₁) := by
  let X₀₁ := p.X₀₁
  let X₀₂ := p.X₀₂

  have aux1 : H[S] + H[U] - H[X₁] - H[X₁' + X₂'] = H[S] - H[X₁] := by
    rw [hU X₁ X₂ X₁' X₂' h₁ h₂ h_indep]
    ring

  have aux2 : d[X₀₁ # U | U + (X₁' + X₂')] - d[X₀₁ # X₁]
            ≤ (H[U + (X₁' + X₂')] + H[U] - H[X₁] - H[X₁' + X₂']) / 2 :=
    condDist_diff_ofsum_le ℙ (hX := p.hmeas1) (hY := hX₁) (hZ := hX₂)
    (hZ' := Measurable.add hX₁' hX₂') (independenceCondition1 h_indep)

  have ineq1 : d[X₀₁ # U | S] - d[X₀₁ # X₁] ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 := by
    rw [← add_assoc, aux1] at aux2
    linarith [aux2]
  have ineq2 : d[X₀₂ # U | S] - d[X₀₂ # X₂] ≤ (H[S ; ℙ] - H[X₂ ; ℙ])/2 := by
    rw [← add_assoc, aux1] at aux2
    sorry
  have ineq3 : d[X₀₁ # V | S] - d[X₀₁ # X₁] ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 := by sorry
  have ineq4 : d[X₀₂ # V | S] - d[X₀₂ # X₂] ≤ (H[S ; ℙ] - H[X₂ ; ℙ])/2 := by sorry

  let W' := X₂ + X₂'
  have ineq5 : d[X₀₁ # W | S] - d[X₀₁ # X₁] ≤ (H[S ; ℙ] + H[W ; ℙ] - H[X₁ ; ℙ] - H[W' ; ℙ])/2 := by
    sorry

  have ineq6 : d[X₀₂ # W' | S] - d[X₀₂ # X₂] ≤ (H[S ; ℙ] + H[W' ; ℙ] - H[X₂ ; ℙ] - H[W ; ℙ])/2 := by
    sorry

  have dist_eq : d[X₀₂ # W' | S] = d[X₀₂ # W | S]
  · have S_eq : S = (X₂ + X₂') + (X₁' + X₁)
    · rw [add_comm X₁' X₁, add_assoc _ X₂', add_comm X₂', ←add_assoc X₂, ←add_assoc X₂, add_comm X₂]
    rw [S_eq]
    exact ruzsa_helper_lemma p (hX₂.add hX₂') (hX₁'.add hX₁)

  -- Put everything together to bound the sum of the `c` terms
  have ineq7 : c[U|S # U|S] + c[V|S # V|S] + c[W|S # W|S] ≤ 3 * H[S ; ℙ] - 3/2 * H[X₁ ; ℙ] -3/2 * H[X₂ ; ℙ]
  · have step₁ :  c[U|S # U|S] ≤ H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2
    · calc c[U|S # U|S] = (d[p.X₀₁ # U|S] - d[p.X₀₁ # X₁]) + (d[p.X₀₂ # U|S] - d[p.X₀₂ # X₂]) := by ring
        _ ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 + (H[S ; ℙ] - H[X₂ ; ℙ])/2 := add_le_add ineq1 ineq2
        _ = H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2 := by ring
    have step₂ : c[V|S # V|S] ≤ H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2
    · calc c[V|S # V|S] =(d[p.X₀₁ # V|S] - d[p.X₀₁ # X₁]) + (d[p.X₀₂ # V|S] - d[p.X₀₂ # X₂]) := by ring
        _ ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 + (H[S ; ℙ] - H[X₂ ; ℙ])/2 := add_le_add ineq3 ineq4
        _ = H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2 := by ring
    have step₃ : c[W|S # W|S] ≤  H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2
    · calc c[W|S # W|S] = (d[X₀₁ # W | S] - d[X₀₁ # X₁]) + (d[X₀₂ # W' | S] - d[X₀₂ # X₂]) :=
          by rw [dist_eq]
        _ ≤ (H[S ; ℙ] + H[W ; ℙ] - H[X₁ ; ℙ] - H[W' ; ℙ])/2 + (H[S ; ℙ] + H[W' ; ℙ] - H[X₂ ; ℙ] - H[W ; ℙ])/2
          := add_le_add ineq5 ineq6
        _ = H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2 := by ring
    calc c[U|S # U|S] + c[V|S # V|S] + c[W|S # W|S] ≤ (H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2) +
      (H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2) + (H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2) :=
        add_le_add (add_le_add step₁ step₂) step₃
    _ = 3 * H[S ; ℙ] - 3/2 * H[X₁ ; ℙ] -3/2 * H[X₂ ; ℙ] := by ring

  have h_indep' : iIndepFun (fun _i => hG) ![X₁, X₂, X₂', X₁']
  · apply ProbabilityTheory.iIndepFun.reindex (Equiv.swap (2 : Fin 4) 3)
    convert h_indep using 1
    ext x
    fin_cases x ; all_goals { aesop }

  have ineq8 : 3 * H[S ; ℙ] ≤ 3/2 * (H[X₁ ; ℙ] + H[X₂ ; ℙ]) + 3*(2+η)*k - 3*I₁
  · calc 3 * H[S ; ℙ] ≤ 3 * (H[X₁ ; ℙ] / 2 + H[X₂ ; ℙ] / 2 + (2+η)*k - I₁) := by
          apply (mul_le_mul_left (zero_lt_three' ℝ)).mpr
            (ent_ofsum_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min)
      _ =  3/2 * ( H[X₁ ; ℙ] + H[X₂ ; ℙ]) + 3*(2+η)*k - 3*I₁ := by ring

  -- Final computation
  calc c[U|S # U|S] + c[V|S # V|S]  + c[W|S # W|S]  ≤ 3 * H[S ; ℙ] - 3/2 * H[X₁ ; ℙ] -3/2 * H[X₂ ; ℙ] := ineq7
     _ = 3 * H[S ; ℙ] - (3/2 *(H[X₁ ; ℙ] + H[X₂ ; ℙ])) := by ring
     _ ≤ (3/2 * ( H[X₁ ; ℙ] + H[X₂ ; ℙ]) + 3*(2+η)*k - 3*I₁) - (3/2 *(H[X₁ ; ℙ] + H[X₂ ; ℙ])) :=
        sub_le_sub_right ineq8 _
     _ = (6 - 3 * η)*k + 3 * (2*η*k - I₁) := by ring

/-- $U+V+W=0$. -/
lemma sum_uvw_eq_zero : U+V+W = 0 := by
  rw [add_comm X₁' X₂, ElementaryAddCommGroup.sum_add_sum_add_sum_eq_zero]

section construct_good
variable {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
variable {T₁ T₂ T₃ : Ω' → G}  (hT : T₁+T₂+T₃ = 0)
variable (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)


local notation3:max "δ[" μ "]" => I[T₁:T₂ ; μ] + I[T₂:T₃ ; μ] + I[T₃:T₁ ; μ]
local notation3:max "δ" => I[T₁:T₂] + I[T₂:T₃] + I[T₃:T₁]

local notation3:max "ψ[" A " # " B "]" => d[A # B] + η * (c[A # B])
local notation3:max "ψ[" A "; " μ " # " B " ; " μ' "]" =>
  d[A ; μ # B ; μ'] + η * c[A ; μ # B ; μ']

open BigOperators in
/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and
$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$
Then there exist random variables $T'_1, T'_2$ such that
$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X_1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2]) $$
is at most
$$ \delta + \eta ( d[X^0_1;T_1]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2]-d[X^0_2;X_2]) $$
$$ + \tfrac12 \eta I[T_1:T_3] + \tfrac12 \eta I[T_2:T_3].$$
-/
lemma construct_good_prelim :
    k ≤ δ + η * c[T₁ # T₂] + η * (I[T₁:T₃] + I[T₂:T₃])/2 := by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  let sum2 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₁; ℙ # T₁; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₁ # X₁]]
  let sum3 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₂; ℙ # T₂; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₂ # X₂]]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ψ[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]

  have hη : 0 ≤ η := by norm_num [η]
  have hP : IsProbabilityMeasure (Measure.map T₃ ℙ) := isProbabilityMeasure_map hT₃.aemeasurable
  have h2T₃ : T₃ = T₁ + T₂
  · calc T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hT, zero_sub]; simp
      _ = T₁ + T₂ := by rw [add_sub_cancel]
  have h2T₁ : T₁ = T₂ + T₃ := by simp [h2T₃, add_left_comm]
  have h2T₂ : T₂ = T₃ + T₁ := by simp [h2T₁, add_left_comm]

  have h1 : sum1 ≤ δ
  · have h1 : sum1 ≤ 3 * I[T₁ : T₂] + 2 * H[T₃] - H[T₁] - H[T₂] := ent_bsg hT₁ hT₂ h2T₃
    have h2 : H[⟨T₂, T₃⟩] = H[⟨T₁, T₂⟩]
    · apply entropy_of_comp_eq_of_comp ℙ (hT₂.prod_mk hT₃) (hT₁.prod_mk hT₂)
        (fun x ↦ (x.1 + x.2, x.1)) (fun x ↦ (x.2, x.1 + x.2))
      · ext1 x; simp [h2T₁]
      · ext1 x; simp [h2T₃]
    have h3 : H[⟨T₁, T₂⟩] = H[⟨T₃, T₁⟩]
    · apply entropy_of_comp_eq_of_comp ℙ (hT₁.prod_mk hT₂) (hT₃.prod_mk hT₁)
        (fun x ↦ (x.1 + x.2, x.1)) (fun x ↦ (x.2, x.1 + x.2))
      · ext1 x; simp [h2T₃]
      · ext1 x; simp [h2T₂]
    simp_rw [mutualInfo_def] at h1 ⊢; linarith

  have h2 : η * sum2 ≤ η * (d[p.X₀₁ # T₁] - d[p.X₀₁ # X₁] + I[T₁ : T₃] / 2)
  · have : sum2 = d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁]
    · simp [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _)]
      simp_rw [cond_rdist'_eq_sum hT₁ hT₃, integral_eq_sum,
        Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]
    gcongr
    linarith [condDist_le' ℙ ℙ p.hmeas1 hT₁ hT₃]

  have h3 : η * sum3 ≤ η * (d[p.X₀₂ # T₂] - d[p.X₀₂ # X₂] + I[T₂ : T₃] / 2)
  · have : sum3 = d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂]
    · simp [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _)]
      simp_rw [cond_rdist'_eq_sum hT₂ hT₃, integral_eq_sum,
        Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]
    gcongr
    linarith [condDist_le' ℙ ℙ p.hmeas2 hT₂ hT₃]

  have h4 : sum4 ≤ δ + η * c[T₁ # T₂] + η * (I[T₁ : T₃] + I[T₂ : T₃]) / 2
  · have : sum4 = sum1 + η * (sum2 + sum3)
    · simp only [integral_add (integrable_of_fintype _ _) (integrable_of_fintype _ _),
        integral_mul_left]
    linarith

  have hk : k ≤ sum4
  · suffices (Measure.map T₃ ℙ)[fun _ ↦ k] ≤ sum4 by simpa using this
    apply integral_mono_ae (integrable_of_fintype _ _) (integrable_of_fintype _ _)
    apply Countable.ae_of_singleton
    intros t ht
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' {t}]) :=
      cond_isProbabilityMeasure ℙ (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' {t}]) (μ' := ℙ[|T₃ ⁻¹' {t}]) p h_min hT₁ hT₂]
  exact hk.trans h4

  -- have h7 : k ≤ ψ[Y₁ # Y₂] := sorry

/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and
-
$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$

Then there exist random variables $T'_1, T'_2$ such that

$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X _1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2])$$

is at most

$$\delta + \frac{\eta}{3} \biggl( \delta + \sum_{i=1}^2 \sum_{j = 1}^3
    (d[X^0_i;T_j] - d[X^0_i; X_i]) \biggr).$$
-/
lemma construct_good : k ≤ δ + (η/3) * (δ + c[T₁ # T₁] + c[T₂ # T₂] + c[T₃ # T₃]) := by
  have v2 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₁ hT₃ hT₂
  have v3 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₂ hT₁ hT₃
  have v6 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₃ hT₂ hT₁
  simp only [mutualInfo, entropy_comm hT₂ hT₁, entropy_comm hT₃ hT₁, entropy_comm hT₃ hT₂]
    at *
  linarith

lemma construct_good' (μ : Measure Ω') [IsProbabilityMeasure μ]:
    k ≤ δ[μ] + (η/3) * (δ[μ] + c[T₁ ; μ # T₁ ; μ] + c[T₂ ; μ # T₂ ; μ] + c[T₃ ; μ # T₃ ; μ]) := by
  letI : MeasureSpace Ω' := ⟨μ⟩
  apply construct_good p X₁ X₂ h_min hT hT₁ hT₂ hT₃

lemma cond_c_eq_integral {Y Z : Ω' → G} (hY : Measurable Y) (hZ : Measurable Z) : c[Y | Z # Y | Z] =
    (Measure.map Z ℙ)[fun z => c[Y ; ℙ[|Z ⁻¹' {z}] # Y ; ℙ[|Z ⁻¹' {z}]]] := by
  simp only [integral_eq_sum, smul_sub, smul_add, smul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  simp_rw [← integral_eq_sum]
  rw [← cond_rdist'_eq_integral _ hY hZ, ← cond_rdist'_eq_integral _ hY hZ, integral_const,
    integral_const]
  have : IsProbabilityMeasure (Measure.map Z ℙ) := isProbabilityMeasure_map hZ.aemeasurable
  simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]


variable {R : Ω' → G} (hR : Measurable R)
local notation3:max "δ'" => I[T₁:T₂|R] + I[T₂:T₃|R] + I[T₃:T₁|R]

lemma delta'_eq_integral : δ' = (Measure.map R ℙ)[fun r => δ[ℙ[|R⁻¹' {r}]]] := by
  simp_rw [condMutualInfo_eq_integral_mutualInfo, integral_eq_sum, smul_add,
    Finset.sum_add_distrib]

lemma cond_construct_good :
    k ≤ δ' + (η/3) * (δ' + c[T₁ | R # T₁ | R] + c[T₂ | R # T₂ | R] + c[T₃ | R # T₃ | R])  := by
  rw [delta'_eq_integral, cond_c_eq_integral _ _ _ hT₁ hR, cond_c_eq_integral _ _ _ hT₂ hR,
    cond_c_eq_integral _ _ _ hT₃ hR]
  simp_rw [integral_eq_sum, ← Finset.sum_add_distrib, ← smul_add, Finset.mul_sum, mul_smul_comm,
    ← Finset.sum_add_distrib, ← smul_add]
  simp_rw [← integral_eq_sum]
  have : IsProbabilityMeasure (Measure.map R ℙ) := isProbabilityMeasure_map (by measurability)
  calc
    k = (Measure.map R ℙ)[fun _r => k] := by
      rw [integral_const]; simp
    _ ≤ _ := ?_
  simp_rw [integral_eq_sum]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : ℙ (R⁻¹' {r}) = 0
  · rw [Measure.map_apply hR (MeasurableSet.singleton r), hr]
    simp
  simp_rw [smul_eq_mul]
  gcongr (?_ * ?_)
  · apply rdist_nonneg hX₁ hX₂
  · rfl
  have : IsProbabilityMeasure (ℙ[|R ⁻¹' {r}])
  · refine cond_isProbabilityMeasure ℙ hr
  apply construct_good' p X₁ X₂ h_min hT hT₁ hT₂ hT₃

end construct_good

/-- If $d[X_1;X_2] > 0$ then  there are $G$-valued random variables $X'_1, X'_2$ such that
Phrased in the contrapositive form for convenience of proof. -/
theorem tau_strictly_decreases_aux : d[X₁ # X₂] = 0 := by
  have hη : η = 1/9 := by rw [η, one_div]
  have h0 := cond_construct_good p X₁ X₂ hX₁ hX₂ h_min (sum_uvw_eq_zero ..)
    (show Measurable U by measurability) (show Measurable V by measurability)
    (show Measurable W by measurability) (show Measurable S by measurability)
  have h1 := sum_condMutual_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h2 := sum_dist_diff_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h_indep' : iIndepFun (fun _i => hG) ![X₁, X₂, X₂', X₁'] := by
    let σ : Fin 4 ≃ Fin 4 :=
    { toFun := ![0, 1, 3, 2]
      invFun := ![0, 1, 3, 2]
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
    refine' iIndepFun.reindex σ.symm _
    convert h_indep using 1
    ext i; fin_cases i <;> rfl
  have h3 := first_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
  have h : k ≤ (8*η + η^2) * k := calc
    k ≤ (1+η/3) * (6*η*k - (1-5*η) / (1-η) * (2*η*k - I₁)) + η/3*((6-3*η)*k + 3*(2*η*k-I₁)) := by
      rw [hη] at *
      linarith
    _ = (8*η+η^2)*k - ((1-5*η)/(1-η)*(1+η/3)-η)*(2*η*k-I₁) := by
      ring
    _ ≤ (8*η + η^2) * k := by
      rw [hη] at *
      norm_num
      linarith
  have : 0 ≤ k := rdist_nonneg hX₁ hX₂
  rw [hη] at *
  linarith
