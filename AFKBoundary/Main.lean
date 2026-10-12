import GeneralStar.Main
import Openmath.Proofs.PaperSupport.Cascade29.Main
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open Finset SimpleGraph

namespace Erdos585.AFKBoundary

private theorem cap_attained {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hcap : G.maxDegree ≤ D)
    (hdense : (D - 1) * Fintype.card V < 2 * G.edgeFinset.card) :
    ∃ v : V, G.degree v = D := by
  classical
  by_contra h
  push Not at h
  have hdeg : ∀ v : V, G.degree v ≤ D - 1 := by
    intro v
    have hv := G.degree_le_maxDegree v
    have hn := h v
    omega
  have hsum : (∑ v : V, G.degree v) ≤ ∑ _v : V, (D - 1) :=
    Finset.sum_le_sum (fun v _hv => hdeg v)
  have hbound : 2 * G.edgeFinset.card ≤ (D - 1) * Fintype.card V := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    simpa [Nat.mul_comm] using hsum
  omega

private theorem maxDegree_eq_of_density {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hcap : G.maxDegree ≤ D)
    (hdense : (D - 1) * Fintype.card V < 2 * G.edgeFinset.card) :
    G.maxDegree = D := by
  obtain ⟨v, hv⟩ := cap_attained G D hcap hdense
  apply Nat.le_antisymm hcap
  rw [← hv]
  exact G.degree_le_maxDegree v

/-- The integer density inequality is average degree at least 64/9, since n is positive. -/
theorem q5_afk_boundary_counterexamples (n : ℕ) (hn : 30 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧ G.maxDegree = 8 ∧
          64*n ≤ 18*G.edgeFinset.card ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 5) := by
  have hstart : GeneralStar.closedStart 5 ≤ n := by
    norm_num [GeneralStar.closedStart]
    omega
  have h := GeneralStar.general_star_endpoint 5 n (by omega) hstart
  let D := GeneralStar.closedFamily 5 n
  change GeneralStar.FamilyConclusion 5 n 13 D at h
  rcases h with ⟨hcard, hbip, _hmin, hcap, he, hno⟩
  have heq : D.graph.edgeFinset.card = 4*n-13 := he
  have hcap8 : D.graph.maxDegree ≤ 8 := hcap
  have hdense : 7 * Fintype.card D.Carrier < 2 * D.graph.edgeFinset.card := by
    change Fintype.card D.Carrier = n at hcard
    rw [hcard, heq]
    omega
  have hmax : D.graph.maxDegree = 8 := maxDegree_eq_of_density D.graph 8 hcap8 hdense
  have havg : 64*n ≤ 18*D.graph.edgeFinset.card := by
    rw [heq]
    omega
  exact ⟨D.Carrier, D.fintype, D.decEq, D.graph, D.decAdj, hcard, hbip, hmax, havg, hno⟩

/-- The integer density inequality is average degree at least 144/13, since n is positive. -/
theorem q7_afk_boundary_counterexamples (n : ℕ) (hn : 63 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧ G.maxDegree = 12 ∧
          144*n ≤ 26*G.edgeFinset.card ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 7) := by
  obtain ⟨V, vf, vd, G, gd, h⟩ := Cascade29.cascade29_endpoint n (by omega)
  let _ := vf
  let _ := vd
  let _ := gd
  rcases h with ⟨hcard, hbip, _hmin, hcap, he, hno⟩
  have hdense : 11 * Fintype.card V < 2 * G.edgeFinset.card := by
    rw [hcard, he]
    omega
  have hmax : G.maxDegree = 12 := maxDegree_eq_of_density G 12 hcap hdense
  have havg : 144*n ≤ 26*G.edgeFinset.card := by
    rw [he]
    omega
  exact ⟨V, vf, vd, G, gd, hcard, hbip, hmax, havg, hno⟩

end Erdos585.AFKBoundary
