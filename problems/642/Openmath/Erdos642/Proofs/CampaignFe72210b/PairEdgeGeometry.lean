import Openmath.Erdos642.Proofs.CampaignFe72210b.SelfAvoidingEdges
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathWindowGeometry
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestSecondStage

/-! Literal selected edges of two chronological windows. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathCoordinates
open Erdos642.FiniteMarkov.PathAvoidance
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b) (C : Chain V)

def pairEdges (a g n : ℕ) (x : V) (w : Path V ((n+g)+a)) : Finset (Sym2 V) :=
  let pq := PathSplit.split a (n+g) w
  let zr := PathSplit.split g n pq.2
  F.selectedEdges (visited x pq.1) (visited (C.endpoint (C.endpoint x pq.1) zr.1) zr.2)

theorem windowWeightedCount_eq_pairEdges (a g n : ℕ) (x : V)
    (w : Path V ((n+g)+a)) (h : actualSA x w) :
    F.windowWeightedCount C a g n x w = ((F.pairEdges C a g n x w).card : ℝ) := by
  have hp := C.actualSA_split_prefix a (n+g) x w h
  have hs := C.actualSA_split_suffix a (n+g) x w h
  have hr := C.actualSA_split_suffix g n (C.endpoint x (PathSplit.split a (n+g) w).1)
    (PathSplit.split a (n+g) w).2 hs
  exact F.occupationWeightedCount_eq_selectedEdges _ _ _ _ hp hr

include C in
theorem prefix_visited_coordinate (a g n : ℕ) (x v : V)
    (w : Path V ((n+g)+a)) (hv : v ∈ visited x (PathSplit.split a (n+g) w).1) :
    ∃ i, i ≤ a ∧ coordinate x w i = v := by
  obtain ⟨i, hi, he⟩ := (mem_visited_iff_coordinate _ v _).mp hv
  refine ⟨i, hi, ?_⟩
  have hc := C.coordinate_append_prefix x (PathSplit.split a (n+g) w).1
    (PathSplit.split a (n+g) w).2 i hi
  rw [C.append_split] at hc
  exact hc.trans he

theorem later_visited_coordinate (a g n : ℕ) (x v : V)
    (w : Path V ((n+g)+a))
    (hv : v ∈ visited
      (C.endpoint (C.endpoint x (PathSplit.split a (n+g) w).1)
        (PathSplit.split g n (PathSplit.split a (n+g) w).2).1)
      (PathSplit.split g n (PathSplit.split a (n+g) w).2).2) :
    ∃ j, a+g ≤ j ∧ j ≤ a+g+n ∧ coordinate x w j = v := by
  obtain ⟨j, hj, he⟩ := (mem_visited_iff_coordinate _ v _).mp hv
  refine ⟨a+(g+j), by omega, by omega, ?_⟩
  have h1 := C.coordinate_append_suffix x (PathSplit.split a (n+g) w).1
    (PathSplit.split a (n+g) w).2 (g+j)
  rw [C.append_split] at h1
  have h2 := C.coordinate_append_suffix (C.endpoint x (PathSplit.split a (n+g) w).1)
    (PathSplit.split g n (PathSplit.split a (n+g) w).2).1
    (PathSplit.split g n (PathSplit.split a (n+g) w).2).2 j
  rw [C.append_split] at h2
  exact h1.trans (h2.trans he)

theorem closing_indices_of_pairEdges_nonempty (a g n : ℕ) (x : V)
    (w : Path V ((n+g)+a)) (hne : (F.pairEdges C a g n x w).Nonempty) :
    ∃ i j, i ≤ a ∧ a+g ≤ j ∧ j ≤ a+g+n ∧
      G.Adj (coordinate x w i) (coordinate x w j) := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  have hz' := Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2
  obtain ⟨i, hi, hei⟩ := prefix_visited_coordinate C a g n x z.2 w hz'.2.2
  obtain ⟨j, hj, hjn, hej⟩ := later_visited_coordinate C a g n x (F.root z.1) w hz'.2.1
  refine ⟨i,j,hi,hj,hjn,?_⟩
  rw [hei, hej]
  exact (F.adjacent z.1 z.2 hz'.1).symm

theorem pairEdges_supported (a g n : ℕ) (x : V) (w : Path V ((n+g)+a))
    (u v : V) (he : s(u,v) ∈ F.pairEdges C a g n x w) :
    G.Adj u v ∧
      (∃ i, i ≤ a+g+n ∧ coordinate x w i = u) ∧
      (∃ j, j ≤ a+g+n ∧ coordinate x w j = v) := by
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp he
  have hz' := Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2
  obtain ⟨i, hi, hei⟩ := prefix_visited_coordinate C a g n x z.2 w hz'.2.2
  obtain ⟨j, hj, hjn, hej⟩ := later_visited_coordinate C a g n x (F.root z.1) w hz'.2.1
  have hadj := F.adjacent z.1 z.2 hz'.1
  rcases Sym2.eq_iff.mp heq with h | h
  · refine ⟨?_, ⟨j,hjn,?_⟩, ⟨i,by omega,?_⟩⟩
    · simpa only [h.1,h.2] using hadj
    · exact hej.trans h.1
    · exact hei.trans h.2
  · refine ⟨?_, ⟨i,by omega,?_⟩, ⟨j,hjn,?_⟩⟩
    · simpa only [h.1,h.2] using hadj.symm
    · exact hei.trans h.2
    · exact hej.trans h.1

end Erdos642.CampaignFe72210b.ForestBundle
