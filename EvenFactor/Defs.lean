import Openmath.Proofs.QB4.Defs
import Mathlib.Combinatorics.SimpleGraph.Tutte

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
open QB4
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def componentVerts (R : Finset V)
    (C : (G.induce (R : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact C.supp.toFinset.image (fun v : (R : Set V) => (v : V))

def oddTo (T R : Finset V) : ℕ :=
  Nat.card {C : (G.induce (R : Set V)).ConnectedComponent |
    Odd (ec G (componentVerts G R C) T)}

def standardDelta (q : ℕ) (S T : Finset V) : ℤ :=
  (q : ℤ) * ((#S : ℤ) - #T) + (ec G T T : ℤ) +
    ec G T (univ \ (S ∪ T)) - oddTo G T (univ \ (S ∪ T))

def SpanningFactor (q : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.IsSpanning ∧ H.coe.IsRegularOfDegree q

lemma componentVerts_subset (R : Finset V)
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    componentVerts G R C ⊆ R := by
  classical
  rintro v hv
  obtain ⟨w, _, rfl⟩ := mem_image.mp hv
  exact w.property

lemma singleton_internal (v : V) : ec G {v} {v} = 0 := by
  simp [ec, dg]

lemma singleton_remainder (v : V) : ec G {v} (univ \ {v}) = G.degree v := by
  unfold ec dg
  simp only [sum_singleton]
  have he : (univ \ {v}).filter (G.Adj v) = G.neighborFinset v := by
    ext w
    simp only [mem_filter, mem_sdiff, mem_univ, mem_singleton,
      true_and, mem_neighborFinset]
    exact ⟨fun h => h.2, fun h => ⟨by intro hw; subst w; exact G.irrefl h, h⟩⟩
  rw [he, card_neighborFinset_eq_degree]

/-- The low-degree branch is constructed from the actual original vertex. -/
theorem low_degree_barrier (q : ℕ) (v : V) (hv : G.degree v < q) :
    ∃ S T : Finset V, Disjoint S T ∧ standardDelta G q S T < 0 := by
  refine ⟨∅, {v}, disjoint_empty_left _, ?_⟩
  have hdeg := singleton_remainder G v
  have hzero := singleton_internal G v
  have hn : (0 : ℤ) ≤ oddTo G {v} (univ \ {v}) := Int.natCast_nonneg _
  unfold standardDelta
  simp only [card_empty, card_singleton, Int.natCast_zero, Int.natCast_one,
    zero_sub, mul_neg, mul_one, empty_union, hzero, hdeg, zero_add]
  have hc : (G.degree v : ℤ) < q := by exact_mod_cast hv
  omega

end Erdos585.EvenFactorCriterion
