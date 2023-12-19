import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.SetTheory.Cardinal.Finite


section Graph
namespace Set

variable {G G' : Type*}

def graph (f : G → G') : Set (G×G') := {(x, f x) | x : G}

lemma graph_def (f : G → G') : graph f = {(x, f x) | x : G} := rfl

lemma card_graph (f : G → G') : Nat.card (graph f) = Nat.card G := by
  apply Nat.card_congr ⟨fun p => p.1.1, fun x => ⟨⟨x, f x⟩, x, rfl⟩,
      by rintro ⟨p, h, hh⟩; simp [←hh],
      by intro x; simp⟩

@[simp]
lemma mem_graph {f : G → G'} (x : G × G') : x ∈ graph f ↔ f x.1 = x.2 := by
  constructor
  · rintro ⟨_, rfl⟩; rfl
  · refine fun h ↦ ⟨x.1, ?_⟩
    rw [h]

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

end Set
end Graph
