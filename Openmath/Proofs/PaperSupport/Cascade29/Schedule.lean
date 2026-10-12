import Openmath.Proofs.PaperSupport.Cascade29.Types

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

/-- Named RIGHT on a tie, at every order of this family. -/
def nextLeft (D : GraphData) : Bool := decide (D.left.card < D.right.card)

def opposite (D : GraphData) : Finset D.Carrier :=
  if D.left.card < D.right.card then D.right else D.left

def eligible (D : GraphData) : Finset D.Carrier :=
  (opposite D).filter fun v => D.graph.degree v < 12

def sixes (D : GraphData) : Finset D.Carrier :=
  (opposite D).filter fun v => D.graph.degree v = 6

/-- Exact degree-six-first choice, followed by least other original labels. -/
def normalNeighbors (D : GraphData) : Finset D.Carrier :=
  sixes D ∪ BqCircularLowerFamily.leastNeighbors (6 - (sixes D).card)
    (eligible D \ sixes D) D.labels.label

abbrev nextNeighbors := normalNeighbors

@[reducible] def step (D : GraphData) : GraphData := D.add (nextLeft D) (nextNeighbors D)

@[reducible] def state : ℕ → GraphData
  | 0 => seedData
  | t+1 => step (state t)

theorem state_card (t : ℕ) : Fintype.card (state t).Carrier = 25+t := by
  induction t with
  | zero => decide
  | succ t ih =>
    change Fintype.card (Option (state t).Carrier) = 25+(t+1)
    rw [Fintype.card_option, ih]
    omega

end Erdos585.Cascade29
