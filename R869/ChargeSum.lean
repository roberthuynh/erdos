/- Exact counting of disjoint original incoming unit edges. -/
import R854.ProfileFree
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7S0002R869
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma disjoint_incoming_sum {A K F : Finset V} {R : V → Finset V}
    (hR : ∀ z ∈ F, R z ⊆ K)
    (hd : Set.PairwiseDisjoint (↑F) R) :
    ∑ z ∈ F, ec G A (R z) ≤ ec G A K := by
  have hsub : F.biUnion R ⊆ K := by
    intro y hy
    obtain ⟨z,hz,hyr⟩ := mem_biUnion.mp hy
    exact hR z hz hyr
  have heq : ec G A (F.biUnion R) = ∑ z ∈ F, ec G A (R z) := by
    simp_rw [ec_comm A]
    unfold ec
    exact sum_biUnion hd
  rw [← heq]
  exact ec_mono_right A hsub

lemma disjoint_charge_budget {A K F : Finset V} {R : V → Finset V} {c : ℕ}
    (hR : ∀ z ∈ F, R z ⊆ K)
    (hd : Set.PairwiseDisjoint (↑F) R)
    (hc : ∀ z ∈ F, c ≤ ec G A (R z)) :
    c * #F ≤ ec G A K := by
  calc c * #F = ∑ _z ∈ F, c := by simp [mul_comm]
       _ ≤ ∑ z ∈ F, ec G A (R z) := sum_le_sum hc
       _ ≤ ec G A K := disjoint_incoming_sum hR hd

#print axioms disjoint_charge_budget
end Erdos585.QB7S0002R869
