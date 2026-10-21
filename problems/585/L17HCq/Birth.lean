import L17HCq.Cross
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open Finset SimpleGraph BqLowerFamily
namespace Erdos585.L17HCq
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (q c : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V)
/- This physical extension proof uses the construction in BqLowerFamilyDirect.lean,
   replacing its fixed deficit by the parameter c. -/
structure Good (A B : Finset V) : Prop where
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith ↑A ↑B
  balance_left : A.card ≤ B.card + 1
  balance_right : B.card ≤ A.card + 1
  degree_bounds : ∀ v, q-1 ≤ G.degree v ∧ G.degree v ≤ 2*(q-1)
  edge_density : G.edgeFinset.card + c = (q-1) * Fintype.card V
  no_regular : NoRegular q G

theorem Good.swap {A B : Finset V} (h : Good q c G A B) : Good q c G B A where
  disjoint := h.disjoint.symm
  cover := by rw [union_comm, h.cover]
  bipartite := h.bipartite.symm
  balance_left := h.balance_right
  balance_right := h.balance_left
  degree_bounds := h.degree_bounds
  edge_density := h.edge_density
  no_regular := h.no_regular

/-- Once the actual selected neighbors are supplied, every graph invariant is preserved. -/
theorem extend_good_selected (hq : 4 ≤ q) {A B : Finset V} (h : Good q c G A B)
    (hsmall : A.card ≤ B.card) (hNB : N ⊆ B) (hN : N.card = q-1)
    (hload : ∀ v ∈ N, G.degree v ≤ 2*(q-1)-1) :
    Good q c (extendGraph G N) (insert none (A.image some)) (B.image some) := by
  have hAc : (insert none (A.image some)).card = A.card + 1 := by
    rw [card_insert_of_notMem (by simp), card_image_of_injective _ (Option.some_injective V)]
  have hBc : (B.image some).card = B.card :=
    card_image_of_injective _ (Option.some_injective V)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hxA hxB
    cases x with
    | none => simp at hxB
    | some v =>
      exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
  · ext x
    cases x with
    | none => simp
    | some v =>
      have hv : v ∈ A ∪ B := by rw [h.cover]; exact mem_univ _
      simpa using hv
  · refine ⟨?_, ?_⟩
    · rw [disjoint_coe]
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      cases x with
      | none => simp at hxB
      | some v => exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
    · intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => exact hxy.elim
        | some v => exact Or.inl ⟨by simp, by simpa using hNB hxy⟩
      | some v =>
        cases y with
        | none => exact Or.inr ⟨by simpa using hNB hxy, by simp⟩
        | some w => simpa using h.bipartite.mem_of_adj hxy
  · rw [hAc, hBc]
    omega
  · rw [hAc, hBc]
    have := h.balance_right
    omega
  · intro x
    cases x with
    | none => simp [hN]; omega
    | some v =>
      rw [degree_some]
      have hd := h.degree_bounds v
      by_cases hv : v ∈ N
      · have hl := hload v hv
        simp [hv]
        omega
      · simp [hv]
        omega
  · rw [edges_extend, hN, Fintype.card_option]
    have := h.edge_density
    nlinarith
  · exact noRegular_extend G N q (by omega) hN h.no_regular


theorem eligible_card (hq : 5 ≤ q) (hc : (q-1)*(q-2)+1 ≤ c)
    {A B : Finset V} (h : Good q c G A B) (hsmall : A.card ≤ B.card) :
    q-1 ≤ (B.filter fun v => G.degree v ≤ 2*(q-1)-1).card := by
  have hcard : A.card+B.card=Fintype.card V := by
    rw [← card_union_of_disjoint h.disjoint,h.cover,card_univ]
  have hdensity : G.edgeFinset.card+c=(q-1)*(A.card+B.card) := by
    rw [hcard];exact h.edge_density
  have hcapacity : (∑ v ∈ B, (2*(q-1)-G.degree v))+G.edgeFinset.card=2*(q-1)*B.card := by
    calc
      _ = (∑ v ∈ B, (2*(q-1)-G.degree v))+∑ v ∈ B,G.degree v := by
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' h.bipartite]
      _ = ∑ _v ∈ B,2*(q-1) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (h.degree_bounds v).2
      _ = _ := by simp [mul_comm]
  have hcap := BqLowerFamily.opposite_slots (q-1) A.card B.card G.edgeFinset.card c
    (∑ v ∈ B,(2*(q-1)-G.degree v)) hsmall hdensity hcapacity
  apply capacity_slots_plus_one (q-1) (by omega) B (fun v => G.degree v)
    (fun v _ => h.degree_bounds v)
  have hp : (q-1)-1=q-2 := by omega
  rw [hp]
  exact hc.trans hcap

theorem literalNext_good (q c : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (hq : 5 ≤ q) (hc : (q-1)*(q-2)+1 ≤ c) (h : Good q c G A B) :
    Good q c (extendGraph G (nextNeighbors q G A B L)) (nextA A B) (nextB A B) := by
  by_cases hsmall : A.card ≤ B.card
  · let S := B.filter fun v => G.degree v ≤ 2*(q-1)-1
    have hN : nextNeighbors q G A B L = leastNeighbors (q-1) S L.label := by
      simp [nextNeighbors,hsmall,S]
    have hNS : nextNeighbors q G A B L ⊆ S := by
      rw [hN]
      exact filter_subset _ S
    have hNB : nextNeighbors q G A B L ⊆ B := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).1
    have hNc : (nextNeighbors q G A B L).card = q-1 := by
      rw [hN]
      exact leastNeighbors_card (q-1) S L.label L.injective (eligible_card q c G hq hc h hsmall)
    have hload : ∀ v ∈ nextNeighbors q G A B L, G.degree v ≤ 2*(q-1)-1 := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).2
    have hn := extend_good_selected q c G (nextNeighbors q G A B L) (by omega) h hsmall hNB hNc hload
    simpa [nextA,nextB,hsmall] using hn
  · have hsmall' : B.card ≤ A.card := by omega
    let S := A.filter fun v => G.degree v ≤ 2*(q-1)-1
    have hN : nextNeighbors q G A B L = leastNeighbors (q-1) S L.label := by
      simp [nextNeighbors,hsmall,S]
    have hNS : nextNeighbors q G A B L ⊆ S := by
      rw [hN]
      exact filter_subset _ S
    have hNA : nextNeighbors q G A B L ⊆ A := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).1
    have hNc : (nextNeighbors q G A B L).card = q-1 := by
      rw [hN]
      exact leastNeighbors_card (q-1) S L.label L.injective (eligible_card q c G hq hc h.swap hsmall')
    have hload : ∀ v ∈ nextNeighbors q G A B L, G.degree v ≤ 2*(q-1)-1 := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).2
    have hn := extend_good_selected q c G (nextNeighbors q G A B L) (by omega) h.swap hsmall' hNA hNc hload
    simpa [nextA,nextB,hsmall] using hn.swap

theorem nextNeighbors_card (q c : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (hq : 5 ≤ q) (hc : (q-1)*(q-2)+1 ≤ c) (h : Good q c G A B) :
    (nextNeighbors q G A B L).card = q-1 := by
  by_cases hsmall : A.card ≤ B.card
  · simpa [nextNeighbors,hsmall] using
      leastNeighbors_card (q-1) (B.filter fun v => G.degree v ≤ 2*(q-1)-1)
        L.label L.injective (eligible_card q c G hq hc h hsmall)
  · have hrev : B.card ≤ A.card := by omega
    simpa [nextNeighbors,hsmall] using
      leastNeighbors_card (q-1) (A.filter fun v => G.degree v ≤ 2*(q-1)-1)
        L.label L.injective (eligible_card q c G hq hc h.swap hrev)


end Erdos585.L17HCq
