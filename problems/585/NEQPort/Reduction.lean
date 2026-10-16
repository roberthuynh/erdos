import Openmath.Proofs.PaperSupport.BqMain
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/- 


-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset SimpleGraph
namespace Erdos585.NEQ
open QB4 B5
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G K : SimpleGraph V} [DecidableRel G.Adj]

/-- Actual original vertices of an actual component of original G[R]. -/
noncomputable def componentVerts (G : SimpleGraph V) (R : Finset V)
    (C : (G.induce (R : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact C.supp.toFinset.image (fun v : (R : Set V) => (v : V))

/-- Actual component test after the primary criterion's shore-name swap. -/
noncomputable def oddCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (S R : Finset V) : ℕ :=
  Nat.card {C : (G.induce (R : Set V)).ConnectedComponent |
    Odd (ec G (componentVerts G R C) S)}

noncomputable def delta (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S T : Finset V) : ℤ :=
  (q : ℤ) * ((#T : ℤ) - #S) + (ec G S S : ℤ) +
    ec G S (U \ (S ∪ T)) - oddCount G S (U \ (S ∪ T))

open scoped Classical in
def SpanningFactorOn (q : ℕ) (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∃ H : G.Subgraph, H.verts = (U : Set V) ∧ H.coe.IsRegularOfDegree q

open scoped Classical in
/-- UNPAID general constant-even-factor necessity, exactly the primary
Theorem1.4. Kept explicit; Mathlib's perfect-matching Tutte is insufficient. -/
def ConstantEvenFactorCriterion (q : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (U : Finset V),
    0 < q → Even q → ¬SpanningFactorOn q G U →
    ∃ S T : Finset V, S ⊆ U ∧ T ⊆ U ∧ Disjoint S T ∧ delta q G U S T < 0

/-- Same original support and edges, now justified inside the larger G. -/
def liftSubgraph (hle : K ≤ G) (H : K.Subgraph) : G.Subgraph where
  verts := H.verts
  Adj := H.Adj
  symm := H.symm
  edge_vert := H.edge_vert
  adj_sub := fun h => hle (H.adj_sub h)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma liftSubgraph_verts (hle : K ≤ G) (H : K.Subgraph) :
    (liftSubgraph hle H).verts = H.verts := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma liftSubgraph_coe (hle : K ≤ G) (H : K.Subgraph) :
    (liftSubgraph hle H).coe = H.coe := rfl

open scoped Classical in
theorem original_regular_transport {q : ℕ} (hle : K ≤ G)
    (h : ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨H, hne, hreg⟩ := h
  refine ⟨liftSubgraph hle H, hne, ?_⟩
  let f : (liftSubgraph hle H).coe ≃g H.coe :=
    { toEquiv := Equiv.refl H.verts
      map_rel_iff' := Iff.rfl }
  intro v
  exact (f.degree_eq v).symm.trans (hreg (f v))

omit [DecidableEq V] in
lemma dg_univ_eq_degree (v : V) : dg G univ v = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold dg
  congr 1
  ext w
  simp

omit [DecidableEq V] in
lemma ec_univ_eq_twice_edges : ec G univ univ = 2 * G.edgeSet.ncard := by
  unfold ec
  simp_rw [dg_univ_eq_degree]
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using G.sum_degrees_eq_twice_card_edges

lemma total_deficiency (D : ℤ) :
    deficiency D G univ univ = D * Fintype.card V - 2 * (G.edgeSet.ncard : ℤ) := by
  rw [deficiency_eq, ec_univ_eq_twice_edges, card_univ]
  norm_cast

lemma even_half (q : ℕ) (heven : Even q) : 2 * (q / 2) = q := by
  obtain ⟨k, hk⟩ := heven
  omega

lemma exact_density_deficiency (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (he : G.edgeSet.ncard + q / 2 = (q - 1) * Fintype.card V) :
    deficiency (2 * (q : ℤ) - 2) G univ univ = q := by
  rw [total_deficiency]
  have hp := Bq.pred_cast (by omega : 5 ≤ q)
  have hh := even_half q heven
  zify at he hh
  rw [hp] at he
  nlinarith

omit [Fintype V] [DecidableEq V] in
lemma critical_pair_order {q : ℕ} {S T : Finset V} (hq : 6 ≤ q)
    (hcard : #S = #T + 1) (hn : 2 ≤ #S + #T)
    (hsat : ∀ t ∈ T, dg G S t = 2 * q - 2) :
    4 * q - 5 ≤ #S + #T ∧ 2 * q ≤ #S + #T := by
  have hT : T.Nonempty := card_pos.mp (by omega)
  obtain ⟨t, ht⟩ := hT
  have hD : 2 * q - 2 ≤ #S := by
    rw [← hsat t ht]
    exact dg_le_card S t
  constructor <;> omega

omit [Fintype V] [DecidableEq V] in
lemma saturated_cross_count {q : ℕ} {S T : Finset V}
    (hsat : ∀ t ∈ T, dg G S t = 2 * q - 2) :
    ec G S T = #T * (2 * q - 2) := by
  rw [ec_comm]
  unfold ec
  calc
    (∑ t ∈ T, dg G S t) = ∑ _t ∈ T, (2 * q - 2) := sum_congr rfl hsat
    _ = #T * (2 * q - 2) := by simp

omit [Fintype V] [DecidableEq V] in
lemma critical_pair_density {q : ℕ} {S T : Finset V} (hq : 6 ≤ q)
    (hcard : #S = #T + 1)
    (hsat : ∀ t ∈ T, dg G S t = 2 * q - 2) :
    (q - 1) * (#S + #T) ≤ ec G S T + q := by
  have hD : 2 * q - 2 = 2 * (q - 1) := by omega
  have he : (q - 1) * (#S + #T) = ec G S T + (q - 1) := by
    rw [saturated_cross_count hsat, hcard, hD]
    ring
  omega

open scoped Classical in
/-- Actual NEQ critical partition -> original factor. The critical pair
premises remain explicit, not disguised as the bare graph endpoint. -/
theorem critical_saturated_pair (q : ℕ) (hq : 6 ≤ q) (S T : Finset V)
    (hST : Disjoint S T) (hcard : #S = #T + 1) (hn : 2 ≤ #S + #T)
    (hcap : G.maxDegree ≤ 2 * q - 2)
    (hsat : ∀ t ∈ T, dg G S t = 2 * q - 2) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  have hlarge := (critical_pair_order hq hcard hn hsat).2
  have hdense := critical_pair_density hq hcard hsat
  have hpairs := Bq.dense_pair (G := G) (by omega : 5 ≤ q) S T hST hlarge
    (fun s _ => (dg_le_maxDegree T s).trans hcap)
    (fun t _ => (dg_le_maxDegree S t).trans hcap) hdense
  exact exists_subgraph_of_regularPairs hST hpairs

set_option pp.proofs false in
#print ConstantEvenFactorCriterion
set_option pp.proofs false in
#print critical_saturated_pair
#print axioms original_regular_transport
#print axioms dg_univ_eq_degree
#print axioms ec_univ_eq_twice_edges
#print axioms total_deficiency
#print axioms even_half
#print axioms exact_density_deficiency
#print axioms critical_pair_order
#print axioms saturated_cross_count
#print axioms critical_pair_density
#print axioms critical_saturated_pair
end Erdos585.NEQ
