import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiComponents
import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiDeficiency

namespace Erdos642.DenseMask20261019.GallaiMatching
open SimpleGraph GallaiTwins GallaiComponents
variable {V : Type*}

private noncomputable def componentPartition (G : SimpleGraph V) :
    (Σ C : G.ConnectedComponent, C.supp) ≃ V where
  toFun x := x.2.val
  invFun x := ⟨G.connectedComponentMk x, ⟨x, by simp⟩⟩
  left_inv x := by
    rcases x with ⟨C, ⟨x, hx⟩⟩
    have hc : G.connectedComponentMk x = C := hx
    subst C
    rfl
  right_inv x := rfl

/-- Each actual component contributes twice its floor half and its parity indicator. -/
theorem half_odd_partition [Fintype V] (G : SimpleGraph V) :
    2 * halfComponents G + G.oddComponents.ncard = Nat.card V := by
  classical
  letI := Fintype.ofFinite G.ConnectedComponent
  have hc := Nat.card_congr (componentPartition G)
  simp only [Nat.card_sigma, Nat.card_coe_set_eq] at hc
  have ho : (∑ C : G.ConnectedComponent, if Odd C.supp.ncard then 1 else 0) =
      G.oddComponents.ncard := by
    simp [← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
  unfold halfComponents
  rw [← ho, Finset.mul_sum, ← Finset.sum_add_distrib, ← hc]
  apply Finset.sum_congr rfl
  intro C _
  by_cases h : Odd C.supp.ncard
  · have hm := Nat.odd_iff.mp h
    simp only [h, if_true]
    omega
  · have hn : C.supp.ncard % 2 ≠ 1 := fun hm => h (Nat.odd_iff.mpr hm)
    have hm : C.supp.ncard % 2 = 0 := by omega
    simp only [h, if_false]
    omega

theorem obstruction_partition [Fintype V] (G : SimpleGraph V) (D : Set V) :
    2 * obstruction G D + (G.induce Dᶜ).oddComponents.ncard = Nat.card V + D.ncard := by
  classical
  have h := half_odd_partition (G.induce Dᶜ)
  have hp := Set.ncard_add_ncard_compl D
  simp only [Nat.card_coe_set_eq, Set.ncard_univ] at h hp
  unfold obstruction
  omega

def deletionIso (G : SimpleGraph V) (D : Set V) :
    ((⊤ : G.Subgraph).deleteVerts D).coe ≃g G.induce Dᶜ where
  toFun x := ⟨x.val, x.property.2⟩
  invFun x := ⟨x.val, ⟨by trivial, x.property⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := by
    intro x y
    change G.Adj x.val y.val ↔ (_ ∧ _ ∧ _)
    simp [x.property.2, y.property.2]

theorem odd_deletion_eq [Fintype V] (G : SimpleGraph V) (D : Set V) :
    ((⊤ : G.Subgraph).deleteVerts D).coe.oddComponents.ncard =
      (G.induce Dᶜ).oddComponents.ncard := by
  classical
  let e := deletionIso G D
  have hc (C : ((⊤ : G.Subgraph).deleteVerts D).coe.ConnectedComponent) :
      C.supp.ncard = (e.connectedComponentEquiv C).supp.ncard :=
    Set.ncard_congr' (C.isoEquivSupp e)
  apply Set.ncard_congr'
  exact e.connectedComponentEquiv.subtypeEquiv
    (by intro C; change Odd _ ↔ Odd _; rw [hc C])

/-- A lower bound on every actual deletion obstruction supplies an actual matching. -/
theorem matching_of_obstruction [Fintype V] (G : SimpleGraph V) (t : ℕ)
    (h : ∀ D : Set V, t ≤ obstruction G D) :
    ∃ M : G.Subgraph, M.IsMatching ∧ t ≤ M.edgeSet.ncard := by
  classical
  have hzero := obstruction_partition G ∅
  have ht := h ∅
  simp only [Set.ncard_empty, add_zero] at hzero
  have hfeasible : 2 * t ≤ Nat.card V := by omega
  let d := Nat.card V - 2 * t
  have hd : Nat.card V = 2 * t + d := by dsimp [d]; omega
  have heven : Even (Nat.card V + d) := ⟨Nat.card V - t, by omega⟩
  have hdef : ∀ D : Set V,
      ((⊤ : G.Subgraph).deleteVerts D).coe.oddComponents.ncard ≤ D.ncard + d := by
    intro D
    rw [odd_deletion_eq]
    have hp := obstruction_partition G D
    have htD := h D
    omega
  obtain ⟨M, hM, hcard⟩ := GallaiDeficiency.exists_matching_of_deficiency G d heven hdef
  exact ⟨M, hM, by omega⟩

/-- Original terminal-component obstructions give the actual doubled matching surplus. -/
theorem doubled_matching [Fintype V] (G : SimpleGraph V) (A : Set V) (k : ℕ)
    (h : ∀ U : Set V,
      letI := Fintype.ofFinite (original G U).ConnectedComponent
      k ≤ U.ncard + ∑ C, terminals G A U C / 2) :
    ∃ M : (doubled G A).Subgraph, M.IsMatching ∧ Aᶜ.ncard + k ≤ M.edgeSet.ncard := by
  classical
  apply matching_of_obstruction
  intro D
  obtain ⟨U, _, hcost⟩ := GallaiNormalization.exists_normalized_deletion G A D
  rw [obstruction_identity] at hcost
  have hU := h U
  omega

end Erdos642.DenseMask20261019.GallaiMatching
