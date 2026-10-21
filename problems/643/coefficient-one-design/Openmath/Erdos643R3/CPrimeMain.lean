import Openmath.Erdos643R3.CPrime
import Openmath.Erdos643R3.G1BiconeAdapter

set_option autoImplicit false
namespace Erdos643R3.CPrimeMain
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.L1Top
  Erdos643R3.Redistribution Erdos643R3.RedistArith Erdos643R3.CPrime
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- The actual G1 theorem supplies every local condition used by C'. -/
theorem biconeG1 (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) : BiconeG1 H := by
  intro x y u v w hxy hCN hd
  have hg := G1BiconeAdapter.deficient_geometric hH hav hxy hCN hd
  unfold G1Combinatorics.GeometricG1 at hg
  refine ⟨?_, fun hu => (hg.2.1 hu).2, fun hv => (hg.2.2 hv).2⟩
  unfold ExactlyOneLight Light
  have hh := hg.1
  tauto

/-- Theorem C' funding, with unconditional G1 and only G3h' left as the named
mathematical input. No anchor-existence or pot-bound assumption is hidden. -/
theorem funded_of_G3hPrime (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hG3 : G3hPrime H) : ∀ q ∈ activePairs H, totalDeficit H q ≤ pot H q :=
  funded_of_G1_G3hPrime hH hav (biconeG1 hH hav) hG3

/-- G1 supplies a triangular witness for every actual deficient triple. -/
theorem deficient_has_witness (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ∀ T ∈ H, Deficient H T → ∃ q, Triangular H q ∧ T ∈ bicone H q := by
  intro T hT hd
  obtain ⟨a,b,c,_,_,_,rfl⟩ := card_eq_three.mp (hH T hT)
  have hact := G1Main.deficient_act_eq_one hT hH hav (by
    unfold Deficient charge at hd
    linarith)
  have hp : 0 < act H {a,b,c} := by omega
  obtain ⟨q,hq⟩ := card_pos.mp hp
  obtain ⟨hqa,hTb⟩ := mem_filter.mp hq
  exact ⟨q,(mem_activePairs.mp hqa).2.1,hTb⟩

/-- The recipient condition in L1Top, from the proved G1 and named G3h'. -/
theorem recovery_of_G3hPrime (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hG3 : G3hPrime H) : ∀ T ∈ H, Deficient H T → 0 ≤ final H T := by
  exact hrec_of_funded_bicones H (deficient_has_witness hH hav) (funded_of_G3hPrime hH hav hG3)

/-- Conditional coefficient-one endpoint: its sole extra input is G3h', supplied in the final assembly by AnchorComplete.g3hPrime. -/
theorem endpoint_of_G3hPrime (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hG3 : G3hPrime H) :
    Phi H ≤ 0 ∧ (H.card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) :=
  conditional_endpoint H hH (recovery_of_G3hPrime hH hav hG3)

end Erdos643R3.CPrimeMain
