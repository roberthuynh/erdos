import PolarityPathCount
import C4Counting
import GraphTransfer

namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [DecidableEq P]

omit [Fintype P] in
theorem Polarity.ThreePath.counting_shape
    (π : Polarity (P := P) (L := L)) {u v : P} (huv : u ≠ v)
    (hnadj : ¬π.graph.Adj u v) (p : π.ThreePath u v) :
    Counting.IsThreePath s(u,v) (p.edges π) := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := Polarity.ThreePath.vertices_distinct π huv hnadj p
  refine ⟨u,p.val.1,p.val.2,v,rfl,?_,?_⟩
  · simp [h₁,h₂,h₃,h₄,h₅,h₆]
  · ext e
    simp only [Polarity.ThreePath.edges, Finset.mem_insert, Finset.mem_singleton]

omit [DecidableEq P] in
theorem Polarity.ThreePath.edges_subset
    (π : Polarity (P := P) (L := L)) {u v : P} (p : π.ThreePath u v) :
    p.edges π ⊆ π.graph.edgeFinset := by
  classical
  intro e he
  simp only [ThreePath.edges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · simpa using p.property.1
  · simpa using p.property.2.1
  · simpa using p.property.2.2

theorem Polarity.counting_path_family [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) {u v : P} (huv : u ≠ v)
    (hnadj : ¬π.graph.Adj u v) :
    ∃ paths : Finset (Finset (Sym2 P)),
      (∀ p ∈ paths, Counting.IsThreePath s(u,v) p ∧ p ⊆ π.graph.edgeFinset) ∧
      (∀ p ∈ paths, ∀ r ∈ paths, p ≠ r → Disjoint p r) ∧
      Configuration.ProjectivePlane.order P L - 1 ≤ paths.card := by
  classical
  obtain ⟨paths, hnum, hdis⟩ := π.exists_disjoint_three_paths huv hnadj
  refine ⟨paths.image (fun p => p.edges π), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨Polarity.ThreePath.counting_shape π huv hnadj r,
      Polarity.ThreePath.edges_subset π r⟩
  · intro p hp r hr hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hr
    exact hdis a ha b hb (fun h => hne (congrArg (fun p => p.edges π) h))
  · have hinj : Set.InjOn (fun p : π.ThreePath u v => p.edges π) (paths : Set _) := by
      intro a ha b hb heq
      dsimp only at heq
      by_contra hne
      have hd := hdis a ha b hb hne
      have hm : s(u,a.val.1) ∈ a.edges π := by simp [Polarity.ThreePath.edges]
      have hm' : s(u,a.val.1) ∈ b.edges π :=
        (congrArg (fun z : Finset (Sym2 P) => s(u,a.val.1) ∈ z) heq).mp hm
      exact Finset.disjoint_left.mp hd hm hm'
    rwa [Finset.card_image_iff.mpr hinj]

theorem Polarity.counting_family_for_added_edge
    [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (e : Sym2 P)
    (he : e ∈ G.edgeFinset \ π.graph.edgeFinset) :
    ∃ paths : Finset (Finset (Sym2 P)),
      (∀ p ∈ paths, Counting.IsThreePath e p ∧ p ⊆ π.graph.edgeFinset) ∧
      (∀ p ∈ paths, ∀ r ∈ paths, p ≠ r → Disjoint p r) ∧
      Configuration.ProjectivePlane.order P L - 1 ≤ paths.card := by
  classical
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := by simpa using (Finset.mem_sdiff.mp he).1
    have hnadj : ¬π.graph.Adj u v := by simpa using (Finset.mem_sdiff.mp he).2
    exact π.counting_path_family hadj.ne hnadj

/-- Actual graph transfer with the polarity path supplier fully proved.
Only edge balance and the short edit radius remain premises; no assumed
path-family/counting/source theorem is present. -/
theorem Polarity.graph_transfer [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (M t δ : ℕ)
    (hG : G.edgeFinset.card = M + t)
    (hQ : π.graph.edgeFinset.card + δ = M)
    (hsmall : (G.edgeFinset \ π.graph.edgeFinset).card ≤
      Configuration.ProjectivePlane.order P L - 1) :
    t * (Configuration.ProjectivePlane.order P L - 1) ≤ Counting.cycleCount G := by
  classical
  let A := G.edgeFinset \ π.graph.edgeFinset
  have hex : ∀ e : Sym2 P, ∃ paths : Finset (Finset (Sym2 P)), e ∈ A →
      (∀ p ∈ paths, Counting.IsThreePath e p ∧ p ⊆ π.graph.edgeFinset) ∧
      (∀ p ∈ paths, ∀ r ∈ paths, p ≠ r → Disjoint p r) ∧
      Configuration.ProjectivePlane.order P L - 1 ≤ paths.card := by
    intro e
    by_cases he : e ∈ A
    · obtain ⟨paths,hp⟩ := π.counting_family_for_added_edge G e he
      exact ⟨paths,fun _ => hp⟩
    · exact ⟨∅,fun h => False.elim (he h)⟩
  choose paths hp using hex
  apply Transfer.graph_transfer G π.graph M (Configuration.ProjectivePlane.order P L)
    t δ hG hQ hsmall paths
  · intro e he p hp'
    exact (hp e he).1 p hp'
  · intro e he p hp' r hr hne
    exact (hp e he).2.1 p hp' r hr hne
  · intro e he
    exact (hp e he).2.2

#print axioms Polarity.ThreePath.counting_shape
#print axioms Polarity.ThreePath.edges_subset
#print axioms Polarity.counting_path_family
#print axioms Polarity.counting_family_for_added_edge
#print axioms Polarity.graph_transfer

end Erdos60.Geometry
