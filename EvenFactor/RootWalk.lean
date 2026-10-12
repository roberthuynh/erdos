import EvenFactor.LiftedGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph Function
namespace Erdos585.EvenFactorCriterion
open QB4 FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

lemma remainder_not_S (S T : Finset V)
    (v : ((univ \ (S ∪ T) : Finset V) : Set V)) : (v : V) ∉ S :=
  fun hs => (mem_sdiff.mp v.property).2 (mem_union_left T hs)

lemma remainder_not_T (S T : Finset V)
    (v : ((univ \ (S ∪ T) : Finset V) : Set V)) : (v : V) ∉ T :=
  fun ht => (mem_sdiff.mp v.property).2 (mem_union_right S ht)

def rootR (hq : 0 < q) (S T : Finset V)
    (v : ((univ \ (S ∪ T) : Finset V) : Set V)) : RemainingVertex q G S T :=
  ⟨Sum.inl ((v : V),⟨0,hq⟩),by
    simpa only [mem_canonical_slot] using remainder_not_S S T v⟩

def stubR (S T : Finset V)
    (v : ((univ \ (S ∪ T) : Finset V) : Set V)) (w : V)
    (h : G.Adj (v : V) w) : RemainingVertex q G S T :=
  ⟨Sum.inr (⟨((v : V),w),h⟩ : G.Dart),by
    simpa only [mem_canonical_stub] using remainder_not_T S T v⟩

lemma rootR_to_stubR (hq : 0 < q) (S T : Finset V)
    (v : ((univ \ (S ∪ T) : Finset V) : Set V)) (w : V)
    (h : G.Adj (v : V) w) :
    (remainingGraph q G S T).Adj (rootR q G hq S T v) (stubR q G S T v w h) := rfl

lemma stubR_to_rootR (hq : 0 < q) (S T : Finset V)
    (v : ((univ \ (S ∪ T) : Finset V) : Set V)) (w : V)
    (h : G.Adj (v : V) w) :
    (remainingGraph q G S T).Adj (stubR q G S T v w h) (rootR q G hq S T v) := rfl

/-- One original edge is lifted to its actual three gadget edges. -/
theorem rootR_adj_reachable (hq : 0 < q) (S T : Finset V)
    (v w : ((univ \ (S ∪ T) : Finset V) : Set V)) (h : G.Adj (v : V) w) :
    (remainingGraph q G S T).Reachable (rootR q G hq S T v) (rootR q G hq S T w) := by
  have ht : (remainingGraph q G S T).Adj (stubR q G S T v w h)
      (stubR q G S T w v h.symm) := by
    change (⟨((w : V),(v : V)),h.symm⟩ : G.Dart) =
      (⟨((v : V),(w : V)),h⟩ : G.Dart).symm
    apply Dart.ext
    rfl
  exact (rootR_to_stubR q G hq S T v w h).reachable.trans
    (ht.reachable.trans (stubR_to_rootR q G hq S T w v h.symm).reachable)

/-- Actual original walks are lifted, not replaced by free quotient edges. -/
theorem rootR_reachable (hq : 0 < q) (S T : Finset V)
    (v w : ((univ \ (S ∪ T) : Finset V) : Set V))
    (h : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).Reachable v w) :
    (remainingGraph q G S T).Reachable (rootR q G hq S T v) (rootR q G hq S T w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | cons hadj p ih => exact (rootR_adj_reachable q G hq S T _ _ hadj).trans ih

end Erdos585.EvenFactorCriterion
