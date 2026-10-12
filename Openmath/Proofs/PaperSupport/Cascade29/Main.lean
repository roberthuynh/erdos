import Openmath.Proofs.PaperSupport.Cascade29.FirstStep
import Openmath.Proofs.PaperSupport.Cascade29.NormalStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

/-- Unbounded induction on the same literal original graph-valued construction. -/
theorem state_normal (k : ℕ) : Normal (state (1+k)) := by
  induction k with
  | zero => exact first_normal
  | succ k ih =>
    have hn : 25 ≤ Fintype.card (state (1+k)).Carrier := by rw [state_card]; omega
    change Normal (step (state (1+k)))
    exact normal_step (state (1+k)) ih hn

theorem state_good (t : ℕ) : DataGood (state t) := by
  cases t with
  | zero => exact seed_good
  | succ k =>
    have heq : k+1 = 1+k := by omega
    rw [heq]
    exact (state_normal k).good

theorem cascade29_graph (t : ℕ) :
    Fintype.card (state t).Carrier = 25+t ∧ (state t).graph.IsBipartite ∧
      (∀ v, 6 ≤ (state t).graph.degree v) ∧ (state t).graph.maxDegree ≤ 12 ∧
      (state t).graph.edgeFinset.card = 6*(25+t)-29 ∧
      ¬ (∃ H : (state t).graph.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 7) := by
  have h := state_good t
  refine ⟨state_card t, h.bipartite.isBipartite, fun v => (h.degrees v).1, ?_, ?_, h.no7⟩
  · exact (state t).graph.maxDegree_le_of_forall_degree_le 12 (fun v => (h.degrees v).2)
  · have hd := h.density
    rw [state_card] at hd
    omega

/-- Bare original all-order theorem; no avoiding seed or chooser-success premise. -/
theorem cascade29_all_orders (n : ℕ) (hn : 25 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧
          (∀ v, 6 ≤ G.degree v) ∧ G.maxDegree ≤ 12 ∧ G.edgeFinset.card = 6*n-29 ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 7) := by
  let D := state (n-25)
  have hcard : 25+(n-25)=n := by omega
  refine ⟨D.Carrier,D.fintype,D.decEq,D.graph,D.decAdj,?_⟩
  simpa only [D,hcard] using cascade29_graph (n-25)

theorem cascade29_endpoint : Cascade29Endpoint := by
  intro n hn
  exact cascade29_all_orders n hn

end Erdos585.Cascade29
