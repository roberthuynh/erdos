import Openmath.Erdos642.Proofs.CampaignFe72210b.PairEdgeGeometry
import Openmath.Erdos642.Proofs.CampaignFe72210b.TwoWindowTransfer

/-! Literal selected pair edges inside actual full paths at arbitrary fixed offsets. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathCoordinates Erdos642.FiniteMarkov.PathAvoidance
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b) (C : Chain V)

def pairEdgesAt (off a g n suffix : ℕ) (x : V)
    (w : Path V ((suffix + ((n + g) + a)) + off)) : Finset (Sym2 V) :=
  let pq := PathSplit.split off (suffix + ((n + g) + a)) w
  F.pairEdges C a g n (C.endpoint x pq.1)
    (PathSplit.split ((n + g) + a) suffix pq.2).1

/-- Actual full-path self-avoidance identifies the offset count with distinct literal edges. -/
theorem windowWeightedCountAt_eq_pairEdgesAt (off a g n suffix : ℕ) (x : V)
    (w : Path V ((suffix + ((n + g) + a)) + off)) (hSA : actualSA x w) :
    F.windowWeightedCountAt C off a g n suffix x w =
      ((F.pairEdgesAt C off a g n suffix x w).card : ℝ) := by
  have hc := C.actualSA_window off ((n + g) + a) suffix x w hSA
  exact F.windowWeightedCount_eq_pairEdges C a g n _ _ hc

/-- Closing coordinates shift by the actual prefix offset. -/
theorem closing_indices_of_pairEdgesAt_nonempty (off a g n suffix : ℕ) (x : V)
    (w : Path V ((suffix + ((n + g) + a)) + off))
    (hne : (F.pairEdgesAt C off a g n suffix x w).Nonempty) :
    ∃ i j, off ≤ i ∧ i ≤ off + a ∧ off + a + g ≤ j ∧ j ≤ off + a + g + n ∧
      G.Adj (coordinate x w i) (coordinate x w j) := by
  obtain ⟨i, j, hi, hj0, hj1, hadj⟩ := F.closing_indices_of_pairEdges_nonempty C a g n
    (C.windowStart off ((n + g) + a) suffix x w)
    (Chain.windowPath off ((n + g) + a) suffix w) hne
  refine ⟨off + i, off + j, by omega, by omega, by omega, by omega, ?_⟩
  rw [C.coordinate_window off ((n + g) + a) suffix x w i (by omega),
    C.coordinate_window off ((n + g) + a) suffix x w j (by omega)]
  exact hadj

/-- Every endpoint of an actual selected edge has a full-path coordinate in the core range. -/
theorem pairEdgesAt_supported (off a g n suffix : ℕ) (x : V)
    (w : Path V ((suffix + ((n + g) + a)) + off))
    (u v : V) (he : s(u,v) ∈ F.pairEdgesAt C off a g n suffix x w) :
    G.Adj u v ∧
      (∃ i, off ≤ i ∧ i ≤ off + a + g + n ∧ coordinate x w i = u) ∧
      (∃ j, off ≤ j ∧ j ≤ off + a + g + n ∧ coordinate x w j = v) := by
  obtain ⟨hadj, ⟨i, hi, hei⟩, ⟨j, hj, hej⟩⟩ := F.pairEdges_supported C a g n
    (C.windowStart off ((n + g) + a) suffix x w)
    (Chain.windowPath off ((n + g) + a) suffix w) u v he
  refine ⟨hadj, ⟨off + i, by omega, by omega, ?_⟩, ⟨off + j, by omega, by omega, ?_⟩⟩
  · exact (C.coordinate_window off ((n + g) + a) suffix x w i (by omega)).trans hei
  · exact (C.coordinate_window off ((n + g) + a) suffix x w j (by omega)).trans hej

/-- The same actual edge set transported to a fixed full path length T. -/
def pairEdgesAtOfEq (off a g n suffix T : ℕ)
    (hT : (suffix + ((n + g) + a)) + off = T) (x : V) (w : Path V T) : Finset (Sym2 V) :=
  F.pairEdgesAt C off a g n suffix x (PathTransport.castPath hT.symm w)

 theorem windowWeightedCountAt_eq_pairEdgesAt_of_eq (off a g n suffix T : ℕ)
    (hT : (suffix + ((n + g) + a)) + off = T) (x : V) (w : Path V T) (hSA : actualSA x w) :
    F.windowWeightedCountAt C off a g n suffix x (PathTransport.castPath hT.symm w) =
      ((F.pairEdgesAtOfEq C off a g n suffix T hT x w).card : ℝ) := by
  cases hT
  exact F.windowWeightedCountAt_eq_pairEdgesAt C off a g n suffix x w hSA

 theorem closing_indices_of_pairEdgesAtOfEq_nonempty (off a g n suffix T : ℕ)
    (hT : (suffix + ((n + g) + a)) + off = T) (x : V) (w : Path V T)
    (hne : (F.pairEdgesAtOfEq C off a g n suffix T hT x w).Nonempty) :
    ∃ i j, off ≤ i ∧ i ≤ off + a ∧ off + a + g ≤ j ∧ j ≤ off + a + g + n ∧
      G.Adj (coordinate x w i) (coordinate x w j) := by
  cases hT
  exact F.closing_indices_of_pairEdgesAt_nonempty C off a g n suffix x w hne

 theorem pairEdgesAtOfEq_supported (off a g n suffix T : ℕ)
    (hT : (suffix + ((n + g) + a)) + off = T) (x : V) (w : Path V T)
    (u v : V) (he : s(u,v) ∈ F.pairEdgesAtOfEq C off a g n suffix T hT x w) :
    G.Adj u v ∧
      (∃ i, off ≤ i ∧ i ≤ off + a + g + n ∧ coordinate x w i = u) ∧
      (∃ j, off ≤ j ∧ j ≤ off + a + g + n ∧ coordinate x w j = v) := by
  cases hT
  exact F.pairEdgesAt_supported C off a g n suffix x w u v he

end Erdos642.CampaignFe72210b.ForestBundle
