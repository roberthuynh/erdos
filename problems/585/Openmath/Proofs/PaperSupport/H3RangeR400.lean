import Openmath.Proofs.PaperSupport.R400Next.Main
import Openmath.Proofs.PaperSupport.R400Largest.Main

/-! Exact height-three range extension of the original nonstrict selectors.
Every graph hypothesis and the common-omission/exact-support output is literal.
The two isolated module trees change only their numerical parameter bundle.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.H3RangeR400
open QB4 B5 L34 H3Unequal
universe u

/-- All original graph fields, with exact h=3 range and no selector/factor premise. -/
structure Host (q a j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  large : 16384 ≤ q
  lower : 16 ≤ a
  upper : a ≤ 32
  surplus : j = 1 ∨ j = 2
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  edges : G.edgeSet.ncard + (3 * q - a) = (q - 1) * Fintype.card V
  proper : ∀ X : Finset V, 3 ≤ #X → #X < Fintype.card V →
    3 * (q : ℤ) - a ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

/-- One original omission pays every cut and fixes the exact nonempty factor support. -/
def Conclusion (q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
    (∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0) ∧
    FactorOn q G A (B \ O) ∧
    ∃ H : G.Subgraph, H.verts = (↑(A ∪ (B \ O)) : Set V) ∧
      H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

variable {q a j : ℕ} {V : Type u} [Fintype V]
  {G : SimpleGraph V} {A B : Finset V}

lemma Host.constant_cast (host : Host q a j G A B) :
    ((3 * q - a : ℕ) : ℤ) = 3 * (q : ℤ) - a := by
  have hle : a ≤ 3 * q := by have hl := host.large; have hu := host.upper; omega
  rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]

lemma Host.to_next (host : Host q a j G A B) (hj : j = 1) :
    AllHNextH3R400.Host 3 q a j G A B := by
  refine ⟨⟨by decide, rfl, ?_, host.lower, ?_, ?_⟩,
    host.disjoint, host.cover, host.bipartite, host.card, host.order,
    host.min_degree, host.cap_degree, host.edges, ?_⟩
  · norm_num
    exact host.large
  · norm_num
    exact host.upper
  · simpa using hj
  · intro X hX hproper
    change ((3 * q - a : ℕ) : ℤ) ≤ _
    rw [host.constant_cast]
    exact host.proper X hX hproper

lemma Host.to_largest (host : Host q a j G A B) (hj : j = 2) :
    AllHLargestH3R400.Host 3 q a j G A B := by
  refine ⟨⟨by decide, rfl, ?_, host.lower, ?_, ?_⟩,
    host.disjoint, host.cover, host.bipartite, host.card, host.order,
    host.min_degree, host.cap_degree, host.edges, ?_⟩
  · norm_num
    exact host.large
  · norm_num
    exact host.upper
  · simpa using hj
  · intro X hX hproper
    change ((3 * q - a : ℕ) : ℤ) ≤ _
    rw [host.constant_cast]
    exact host.proper X hX hproper

/-- Full range, both surplus branches, on every original finite carrier universe. -/
theorem h3_range_selector (q a j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host q a j G A B) :
    Conclusion q j G A B := by
  classical
  have hresult : ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
      (∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0) ∧
      ∃ H : G.Subgraph, H.verts = (↑(A ∪ (B \ O)) : Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
    rcases host.surplus with hj | hj
    · exact AllHNextH3R400.allh_next_nonstrict 3 q a j G A B (host.to_next hj)
    · exact AllHLargestH3R400.allh_largest_nonstrict 3 q a j G A B (host.to_largest hj)
  obtain ⟨O, hOB, hOj, hcuts, H, hverts, hne, hreg⟩ := hresult
  exact ⟨O, hOB, hOj, hcuts,
    factor_of_common_omission q j host.card hOB hOj hcuts, H, hverts, hne, hreg⟩

/-- Next-surplus branch j=1. -/
theorem h3_range_j1 (q a : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host q a 1 G A B) :
    Conclusion q 1 G A B := h3_range_selector q a 1 G A B host

/-- Largest-surplus branch j=2. -/
theorem h3_range_j2 (q a : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host q a 2 G A B) :
    Conclusion q 2 G A B := h3_range_selector q a 2 G A B host

#print axioms h3_range_selector
#print axioms h3_range_j1
#print axioms h3_range_j2
end Erdos585.H3RangeR400
