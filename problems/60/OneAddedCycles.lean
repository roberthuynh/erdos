import MarkedPathBijection

namespace Erdos60.Counting
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Complete one-added-edge cycles form an actual family, with cardinality
the sum of all complete base-path counts. No matching hypothesis is needed. -/
theorem one_added_cycle_family (G Q : SimpleGraph V) (hQG : Q ≤ G) :
    ∃ F : Finset (Finset (Sym2 V)), F ⊆ cycles G ∧
      (∀ C ∈ F, (C \ Q.edgeFinset).card = 1) ∧
      F.card = ∑ e ∈ G.edgeFinset \ Q.edgeFinset, (baseThreePaths Q e).card := by
  classical
  let A := G.edgeFinset \ Q.edgeFinset
  let B := fun e => (baseThreePaths Q e).image (insert e)
  have hBsub : ∀ e ∈ A, B e ⊆ cycles G := by
    intro e he C hC
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hpath,hsub⟩ := (mem_baseThreePaths Q e p).mp hp
    apply (mem_cycles G _).mpr
    refine ⟨Finset.insert_subset (Finset.mem_sdiff.mp he).1 ?_,threePath_closes hpath⟩
    intro f hf
    have hfQ := hsub hf
    simp only [SimpleGraph.mem_edgeFinset] at hfQ ⊢
    exact SimpleGraph.edgeSet_mono hQG hfQ
  have hBcard : ∀ e ∈ A, (B e).card = (baseThreePaths Q e).card := by
    intro e he
    apply Finset.card_image_iff.mpr
    apply close_injective
    intro p hp hn
    exact (Finset.mem_sdiff.mp he).2 (((mem_baseThreePaths Q e p).mp hp).2 hn)
  have hBdis : ∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (B e) (B f) := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro C hCe hCf
    obtain ⟨p,hp,hCp⟩ := Finset.mem_image.mp hCe
    obtain ⟨r,hr,hCr⟩ := Finset.mem_image.mp hCf
    have heC : e ∈ insert f r := by rw [hCr, ← hCp]; simp
    rcases Finset.mem_insert.mp heC with hef | her
    · exact hne hef
    · exact (Finset.mem_sdiff.mp he).2 (((mem_baseThreePaths Q f r).mp hr).2 her)
  refine ⟨A.biUnion B, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨e,he,hCe⟩ := Finset.mem_biUnion.mp hC
    exact hBsub e he hCe
  · intro C hC
    obtain ⟨e,he,hCe⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hCe
    have hsub := ((mem_baseThreePaths Q e p).mp hp).2
    have heQ := (Finset.mem_sdiff.mp he).2
    have hd : insert e p \ Q.edgeFinset = {e} := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz,hn⟩
        rcases hz with hz | hz
        · exact hz
        · exact False.elim (hn (hsub hz))
      · rintro rfl
        exact ⟨Or.inl rfl,heQ⟩
    rw [hd]
    exact Finset.card_singleton _
  · rw [Finset.card_biUnion (by
      intro e he f hf hne
      exact hBdis e he f hf hne)]
    exact Finset.sum_congr rfl hBcard

#print axioms one_added_cycle_family
end Erdos60.Counting
