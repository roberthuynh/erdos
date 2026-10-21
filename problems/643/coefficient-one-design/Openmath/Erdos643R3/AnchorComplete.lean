import Openmath.Erdos643R3.AnchorShare
import Openmath.Erdos643R3.AnchorApexAdapter

set_option autoImplicit false
namespace Erdos643R3.AnchorComplete
open Finset
open Erdos643R3.Identity Erdos643R3.CPrime
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- The universal both-heavy anchor bound, for the original apex deficit and
the original activity count, follows from uniformity and forbidden-copy avoidance. -/
theorem g3hPrime (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    G3hPrime H := by
  intro x y u v w hxy hCN ha hl hu hw hp
  obtain ⟨h,hu3,hw3,hcard,hd⟩ :=
    AnchorApexAdapter.original_data hH hav hxy hCN hl hu hw hp
  rw [AnchorApexAdapter.apexDeficit_eq h hu hw]
  exact le_of_lt (AnchorShare.share_host h hcard hu3 hw3 hd ha)

end Erdos643R3.AnchorComplete
