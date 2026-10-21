import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Tactic

namespace Erdos642.DenseMask20261019.GallaiTwins
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

/-- Original vertices and one additional copy of each nonterminal. -/
abbrev CopyVertex (A : Set V) := V ⊕ ↥(Aᶜ)

def project {A : Set V} : CopyVertex A → V
  | .inl v => v
  | .inr v => v.val

/-- Original edges lift between every available copy; each nonterminal pair is adjacent. -/
def doubled (G : SimpleGraph V) (A : Set V) : SimpleGraph (CopyVertex A) where
  Adj u v := (u ≠ v ∧ project u = project v) ∨ G.Adj (project u) (project v)
  symm := ⟨by intro u v; simp only [ne_comm, eq_comm, G.adj_comm]; exact id⟩
  loopless := ⟨by intro u; simp⟩

section Restore
variable (G : SimpleGraph V) (S : Set V) (a b : V)
variable (ha : a ∉ S) (hb : b ∈ S)

private def inc : G.induce S →g G.induce (insert a S) :=
  (G.induceHomOfLE (Set.subset_insert a S)).toHom

private noncomputable def retract (v : ↥(insert a S)) : S := by
  classical
  exact if h : v.val = a then ⟨b, hb⟩ else ⟨v.val, (Set.mem_insert_iff.mp v.property).resolve_left h⟩

include ha in
private theorem retract_inc (v : S) : retract S a b hb (inc G S a v) = v := by
  classical
  unfold retract
  split_ifs with h
  · change v.val = a at h
    exact False.elim (ha (h ▸ v.property))
  · apply Subtype.ext
    rfl

private theorem retract_reachable
    (ht : ∀ z ∈ S, G.Adj a z → z = b ∨ G.Adj b z)
    {u v : ↥(insert a S)} (h : (G.induce (insert a S)).Reachable u v) :
    (G.induce S).Reachable (retract S a b hb u) (retract S a b hb v) := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons u w v huw p ih =>
    apply SimpleGraph.Reachable.trans (v := retract S a b hb w) _ ih
    by_cases hu : u.val = a <;> by_cases hw : w.val = a
    · simp [retract, hu, hw]
    · have hwS : w.val ∈ S := (Set.mem_insert_iff.mp w.property).resolve_left hw
      have h' : G.Adj a w.val := by simpa [hu] using huw
      rcases ht w.val hwS h' with he | he
      · have hba : b ≠ a := by simpa [he] using hw
        simp [retract, hu, hw, he, hba]
      · apply SimpleGraph.Adj.reachable
        simpa [retract, hu, hw] using he
    · have huS : u.val ∈ S := (Set.mem_insert_iff.mp u.property).resolve_left hu
      have h' : G.Adj a u.val := by simpa [hw] using huw.symm
      rcases ht u.val huS h' with he | he
      · have hba : b ≠ a := by simpa [he] using hu
        simp [retract, hu, hw, he, hba]
      · apply SimpleGraph.Adj.reachable
        simpa [retract, hu, hw] using he.symm
    · apply SimpleGraph.Adj.reachable
      simpa [retract, hu, hw] using huw

include ha hb in
private theorem component_map_bijective
    (hab : G.Adj a b) (ht : ∀ z ∈ S, G.Adj a z → z = b ∨ G.Adj b z) :
    Function.Bijective (SimpleGraph.ConnectedComponent.map (inc G S a)) := by
  constructor
  · intro C D
    induction C using SimpleGraph.ConnectedComponent.ind with | _ u =>
      induction D using SimpleGraph.ConnectedComponent.ind with | _ v =>
        intro h
        apply SimpleGraph.ConnectedComponent.sound
        have hr := retract_reachable G S a b hb ht (SimpleGraph.ConnectedComponent.exact h)
        simpa only [retract_inc G S a b ha hb] using hr
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with | _ v =>
      by_cases hv : v.val = a
      · refine ⟨(G.induce S).connectedComponentMk ⟨b, hb⟩, ?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        apply SimpleGraph.Adj.reachable
        change G.Adj b v.val
        simpa [hv] using hab.symm
      · exact ⟨(G.induce S).connectedComponentMk
          ⟨v.val, (Set.mem_insert_iff.mp v.property).resolve_left hv⟩, rfl⟩

/-- Restoring a vertex attached only inside its mate's component preserves the component set. -/
noncomputable def restoreComponentEquiv
    (hab : G.Adj a b) (ht : ∀ z ∈ S, G.Adj a z → z = b ∨ G.Adj b z) :
    (G.induce S).ConnectedComponent ≃ (G.induce (insert a S)).ConnectedComponent :=
  Equiv.ofBijective _ (component_map_bijective G S a b ha hb hab ht)

private theorem restore_support
    (hab : G.Adj a b) (ht : ∀ z ∈ S, G.Adj a z → z = b ∨ G.Adj b z)
    (C : (G.induce S).ConnectedComponent) :
    (restoreComponentEquiv G S a b ha hb hab ht C).supp =
      (inc G S a) '' C.supp ∪
        {v | v.val = a ∧ (G.induce S).connectedComponentMk ⟨b, hb⟩ = C} := by
  classical
  ext v
  by_cases hv : v.val = a
  · have hm : (G.induce (insert a S)).connectedComponentMk v =
        (restoreComponentEquiv G S a b ha hb hab ht)
          ((G.induce S).connectedComponentMk ⟨b, hb⟩) := by
      apply SimpleGraph.ConnectedComponent.sound
      apply SimpleGraph.Adj.reachable
      change G.Adj v.val b
      simpa [hv] using hab
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, hm,
      Equiv.apply_eq_iff_eq, Set.mem_union, Set.mem_image, Set.mem_setOf_eq, hv, true_and]
    constructor
    · exact Or.inr
    · rintro (⟨u, hu, he⟩ | he)
      · have hval := congrArg Subtype.val he
        change u.val = v.val at hval
        have : u.val = a := hval.trans hv
        exact False.elim (ha (this ▸ u.property))
      · exact he
  · let u : S := ⟨v.val, (Set.mem_insert_iff.mp v.property).resolve_left hv⟩
    have hvu : inc G S a u = v := rfl
    rw [← hvu]
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_union,
      Set.mem_image, Set.mem_setOf_eq]
    change ((restoreComponentEquiv G S a b ha hb hab ht)
      ((G.induce S).connectedComponentMk u) =
      (restoreComponentEquiv G S a b ha hb hab ht) C) ↔ _
    rw [Equiv.apply_eq_iff_eq]
    constructor
    · intro h; exact Or.inl ⟨u, h, rfl⟩
    · rintro (⟨w, hw, he⟩ | he)
      · have hh := congrArg (fun z : ↥(insert a S) => z.val) he
        have : w = u := Subtype.ext hh
        simpa [this] using hw
      · exact False.elim (hv he.1)

theorem restore_support_card [Fintype V]
    (hab : G.Adj a b) (ht : ∀ z ∈ S, G.Adj a z → z = b ∨ G.Adj b z)
    (C : (G.induce S).ConnectedComponent) :
    (restoreComponentEquiv G S a b ha hb hab ht C).supp.ncard =
      C.supp.ncard + if (G.induce S).connectedComponentMk ⟨b, hb⟩ = C then 1 else 0 := by
  classical
  have hi : Function.Injective (inc G S a) := by
    intro u v h
    have hh := congrArg (fun z : ↥(insert a S) => z.val) h
    exact Subtype.ext hh
  rw [restore_support G S a b ha hb hab ht C]
  by_cases hc : (G.induce S).connectedComponentMk ⟨b, hb⟩ = C
  · let aa : ↥(insert a S) := ⟨a, Set.mem_insert a S⟩
    have he : {v : ↥(insert a S) | v.val = a ∧
        (G.induce S).connectedComponentMk ⟨b, hb⟩ = C} = {aa} := by
      ext v; simp [hc, aa, Subtype.ext_iff]
    have hn : aa ∉ (inc G S a) '' C.supp := by
      rintro ⟨v, hv, he⟩
      have hval : v.val = a := congrArg Subtype.val he
      exact ha (hval ▸ v.property)
    rw [he, Set.union_singleton, Set.ncard_insert_of_notMem hn,
      Set.ncard_image_of_injective _ hi]
    simp [hc]
  · simp only [hc, and_false, Set.setOf_false, Set.union_empty, if_false, add_zero]
    exact Set.ncard_image_of_injective _ hi

end Restore

noncomputable def halfComponents [Finite V] (G : SimpleGraph V) : ℕ := by
  classical
  letI := Fintype.ofFinite G.ConnectedComponent
  exact ∑ C : G.ConnectedComponent, C.supp.ncard / 2

/-- The component floor sum grows by at most one under actual single-twin restoration. -/
theorem restore_halfComponents [Fintype V] (G : SimpleGraph V) (S : Set V) (a b : V)
    (ha : a ∉ S) (hb : b ∈ S) (hab : G.Adj a b)
    (ht : ∀ z ∈ S, G.Adj a z → z = b ∨ G.Adj b z) :
    halfComponents (G.induce (insert a S)) ≤ halfComponents (G.induce S) + 1 := by
  classical
  letI := Fintype.ofFinite (G.induce S).ConnectedComponent
  letI := Fintype.ofFinite (G.induce (insert a S)).ConnectedComponent
  let e := restoreComponentEquiv G S a b ha hb hab ht
  unfold halfComponents
  rw [← e.sum_comp (fun C => C.supp.ncard / 2)]
  calc
    _ ≤ ∑ C : (G.induce S).ConnectedComponent,
        (C.supp.ncard / 2 + if (G.induce S).connectedComponentMk ⟨b, hb⟩ = C then 1 else 0) := by
      apply Finset.sum_le_sum
      intro C _
      change (restoreComponentEquiv G S a b ha hb hab ht C).supp.ncard / 2 ≤ _
      rw [restore_support_card G S a b ha hb hab ht C]
      split_ifs <;> omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Tutte--Berge's actual deletion obstruction, using induced deletion graphs. -/
noncomputable def obstruction [Finite V] (G : SimpleGraph V) (D : Set V) : ℕ :=
  D.ncard + halfComponents (G.induce Dᶜ)

theorem restore_obstruction [Fintype V] (G : SimpleGraph V) (D : Set V) (a b : V)
    (ha : a ∈ D) (hb : b ∉ D) (hab : G.Adj a b)
    (ht : ∀ z ∉ D, G.Adj a z → z = b ∨ G.Adj b z) :
    obstruction G (D \ {a}) ≤ obstruction G D := by
  classical
  have hcomp : (D \ {a})ᶜ = insert a Dᶜ := by ext v; simp; tauto
  have hh := restore_halfComponents G Dᶜ a b (by simpa using ha) hb hab ht
  have hn : a ∉ D \ {a} := by simp
  have he : insert a (D \ {a}) = D := by ext v; simp; aesop
  have hc := Set.ncard_insert_of_notMem (s := D \ {a}) hn
  rw [he] at hc
  unfold obstruction
  have heq := congrArg (fun S : Set V => halfComponents (G.induce S)) hcomp
  omega

/-- Either orientation of a singly deleted nonterminal twin has nonincreasing obstruction. -/
theorem doubled_restore_obstruction [Fintype V] (G : SimpleGraph V) (A : Set V)
    (D : Set (CopyVertex A)) (u v : CopyVertex A)
    (hu : u ∈ D) (hv : v ∉ D) (hp : project u = project v) :
    obstruction (doubled G A) (D \ {u}) ≤ obstruction (doubled G A) D := by
  classical
  have hne : u ≠ v := by intro h; exact hv (h ▸ hu)
  apply restore_obstruction (doubled G A) D u v hu hv (Or.inl ⟨hne, hp⟩)
  intro z hz huz
  by_cases hzv : z = v
  · exact Or.inl hzv
  · apply Or.inr
    rcases huz with ⟨huz, hpz⟩ | hadj
    · exact Or.inl ⟨Ne.symm hzv, hp.symm.trans hpz⟩
    · exact Or.inr (hp ▸ hadj)

end Erdos642.DenseMask20261019.GallaiTwins
