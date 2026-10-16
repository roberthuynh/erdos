import EvenFactor.OddCharge
import EvenFactor.DeleteIso

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
open QB4 FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma degree_partition (S T : Finset V) (hST : Disjoint S T) :
    (∑ v ∈ T, G.degree v) = ec G T S + ec G T T + ec G T (univ \ (S ∪ T)) := by
  unfold ec
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  have hr := dg_sdiff_add (G := G) (S := univ) (T := S ∪ T)
    (subset_univ (S ∪ T)) v
  rw [dg_union_of_disjoint hST, dg_full_degree G v] at hr
  omega

/-- The original Tutte deficit is exactly the difference between deleted original resources
and the upper bound on actual odd remaining gadget components. -/
theorem standardDelta_degree (q : ℕ) (S T : Finset V) (hST : Disjoint S T) :
    standardDelta G q S T =
      ((q * #S + (∑ v ∈ T, G.degree v) : ℕ) : ℤ) -
      ((q * #T + ec G S T + oddTo G T (univ \ (S ∪ T)) : ℕ) : ℤ) := by
  unfold standardDelta
  rw [degree_partition G S T hST, ec_comm T S]
  push_cast
  ring

/-- This local caller is paid from an actual positive canonical gadget deletion, rather than
from a factor criterion or a numerical component profile. -/
theorem canonical_positive_negative (q : ℕ) (hq : 0 < q) (heven : Even q)
    (hmin : ∀ v : V, q ≤ G.degree v) (S T : Finset V) (hST : Disjoint S T)
    (hp : 0 < gadgetDeficiency (gadget q G) (canonicalDeletion q G S T)) :
    standardDelta G q S T < 0 := by
  have hb := remaining_odd_bound q G hq heven hmin S T hST
  unfold gadgetDeficiency at hp
  rw [canonical_oddRemaining q G S T, canonical_card q G S T] at hp
  have hbz : ((remainingGraph q G S T).oddComponents.ncard : ℤ) ≤
      (q * #T + ec G S T + oddTo G T (univ \ (S ∪ T)) : ℕ) := by exact_mod_cast hb
  rw [standardDelta_degree G q S T hST]
  omega

end Erdos585.EvenFactorCriterion
