import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.SetTheory.Cardinal.Finite


section Graph
namespace Set

variable {G G' : Type*}

-- TODO: maybe `Function.graph` for dot notation?
def graph (f : G → G') : Set (G×G') := {(x, f x) | x : G}

lemma graph_def (f : G → G') : graph f = {(x, f x) | x : G} := rfl

lemma card_graph (f : G → G') : Nat.card (graph f) = Nat.card G := by
  apply Nat.card_congr ⟨fun p => p.1.1, fun x => ⟨⟨x, f x⟩, x, rfl⟩,
      by rintro ⟨p, h, hh⟩; simp [← hh],
      by intro x; simp⟩

@[simp]
lemma mem_graph {f : G → G'} (x : G × G') : x ∈ graph f ↔ f x.1 = x.2 := by
  constructor
  · rintro ⟨_, rfl⟩; rfl
  · refine fun h ↦ ⟨x.1, ?_⟩
    rw [h]

lemma fst_injOn_graph (f : G → G') : (graph f).InjOn Prod.fst := fun x hx y hy h ↦
  Prod.ext h <| ((mem_graph x).mp hx).symm.trans <| (congr_arg f h).trans <| (mem_graph y).mp hy

@[simp]
lemma image_fst_graph {f : G → G'} : Prod.fst '' (graph f) = Set.univ := by
  ext x; simp

@[simp]
lemma image_snd_graph {f : G → G'} : Prod.snd '' (graph f) = f '' Set.univ := by
  ext x; simp

lemma graph_comp {A B C : Type*} {f : A → B} (g : B → C) :
    graph (g ∘ f) = (fun p ↦ (p.1, g p.2)) '' graph f := by
  ext x;
  simp only [mem_graph, Function.comp_apply, Set.mem_image, Prod.exists, exists_eq_left']
  constructor
  · intro h
    use x.1
    rw [h]
  · rintro ⟨x, rfl⟩; rfl

lemma graph_nonempty [Nonempty G] (f : G → G') : (graph f).Nonempty := by
  inhabit G; exact ⟨_, default, rfl⟩

lemma graph_add [AddGroup G] [AddCommGroup G'] {f : G →+ G'} {c : G × G'} :
    (c+·) '' graph f = {(g, f g + (c.2 - f c.1)) | g : G} := by
  ext x
  simp only [Set.image_add_left, Set.mem_preimage, mem_graph,
    Prod.fst_add, Prod.snd_add, Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, AddMonoidHom.map_add,
    AddMonoidHom.map_neg]
  constructor
  · intro h
    use x.1
    rw [add_comm, sub_eq_add_neg, add_assoc, h]
    convert show (x.1, x.2) = x from rfl
    abel
  · rintro ⟨g, rfl⟩;
    abel_nf

variable {G G' : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G'] [DecidableEq G]
  [DecidableEq G']

lemma equiv_filter_graph (f : G → G') :
    let A := (Set.graph f).toFinite.toFinset
    (A ×ˢ A).filter (fun (a, a') ↦ a + a' ∈ A) ≃ {x : G × G | f (x.1 + x.2) = f x.1 + f x.2} where
  toFun := fun ⟨a, ha⟩ ↦ by
    let A := (Set.graph f).toFinite.toFinset
    use (a.1.1, a.2.1)
    apply Finset.mem_filter.mp at ha
    have h {a} (h' : a ∈ A) := (Set.mem_graph _).mp <| (Set.graph f).toFinite.mem_toFinset.mp h'
    show f (a.1.1 + a.2.1) = (f a.1.1) + (f a.2.1)
    rw [h (Finset.mem_product.mp ha.1).1, h (Finset.mem_product.mp ha.1).2]
    exact h ha.2
  invFun := fun ⟨a, ha⟩ ↦ by
    use ((a.1, f a.1), (a.2, f a.2))
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    <;> apply (Set.graph f).toFinite.mem_toFinset.mpr
    · exact ⟨a.1, rfl⟩
    · exact ⟨a.2, rfl⟩
    · exact (Set.mem_graph _).mpr ha
  left_inv := fun ⟨x, hx⟩ ↦ by
    apply Subtype.ext
    show ((x.1.1, f x.1.1), x.2.1, f x.2.1) = x
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    rewrite [(Set.graph f).toFinite.mem_toFinset] at hx1 hx2
    rw [(Set.mem_graph x.1).mp hx1, (Set.mem_graph x.2).mp hx2]
  right_inv := fun _ ↦ rfl

end Set
end Graph
