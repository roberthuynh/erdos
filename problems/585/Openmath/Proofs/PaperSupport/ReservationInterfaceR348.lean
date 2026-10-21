import Openmath.Proofs.PaperSupport.B5Factor

/-! R348 exact original mixed-matching reservation interface.
This file declares a proposition,
not a theorem proving the reservation endpoint. UnitBMatchingR352Modules.lean
proves the separate cut-criterion interface. Ordered pairs encode each original edge exactly once from
the disjoint A shore to the B shore. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.MixedMatchingReservationR348
universe u

/-- Capacity-one original A-to-B edge set. -/
def OriginalEdges {V : Type u} (G : SimpleGraph V) (A B : Finset V)
    (E : Finset (V × V)) : Prop :=
  E ⊆ A ×ˢ B ∧ ∀ e ∈ E, G.Adj e.1 e.2

/-- Individual matching. There is no shared-vertex restriction between L and M. -/
def PairMatching {V : Type u} (E : Finset (V × V)) : Prop :=
  (∀ a : V, #{e ∈ E | e.1 = a} ≤ 1) ∧
  (∀ b : V, #{e ∈ E | e.2 = b} ≤ 1)

/-- Literal original host assumptions of R345. All deficits use integers. -/
structure OriginalHost (r h j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  r_pos : 1 ≤ r
  h_min : 2 ≤ h
  h_max : h ≤ r + 1
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  min_A : ∀ a ∈ A, r + 1 ≤ G.degree a
  cap_A : ∀ a ∈ A, G.degree a ≤ 2 * r
  cap_B : ∀ b ∈ B, G.degree b ≤ 2 * r
  proper_floor : ∀ U : Finset V, h ≤ #U → #U < Fintype.card V →
    (r : ℤ) * Fintype.card V - (G.edgeSet.ncard : ℤ) + 1 ≤
      (r : ℤ) * #U - ((G.induce (U : Set V)).edgeSet.ncard : ℤ)

/-- Endpoint proposition, defined here. The separate UnitBMatchingCutCriterion
is proved in UnitBMatchingR352Modules.lean.
Empty shores and matchings and j=0 are permitted.
The output is one actual original unit edge set with full A quota, B capacity,
all prescribed L edges included, and all M edges excluded. -/
def ReservationClaim : Prop :=
  ∀ (r h j : ℕ), ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V), OriginalHost r h j G A B →
    ∀ L M : Finset (V × V), OriginalEdges G A B L → OriginalEdges G A B M →
      PairMatching L → PairMatching M → Disjoint L M → #L + #M ≤ r * j + 1 →
      ∃ F : Finset (V × V), OriginalEdges G A B F ∧ L ⊆ F ∧ Disjoint F M ∧
        (∀ a ∈ A, #{e ∈ F | e.1 = a} = r) ∧
        (∀ b ∈ B, #{e ∈ F | e.2 = b} ≤ r)

/-- Construction proposition used by the proof. This file defines the proposition;
it does not prove it or make it an assumption of ReservationClaim.
For the application, E is the original residual edge set outside L union M,
d a = r - deg_L(a), and c b = r - deg_L(b). -/
def UnitBMatchingCutCriterion : Prop :=
  ∀ {V : Type u} (A B : Finset V) (E : Finset (V × V)) (d c : V → ℕ),
    E ⊆ A ×ˢ B →
    (∀ P ⊆ A, ∀ T ⊆ B,
      (∑ a ∈ P, d a) ≤ #{e ∈ E | e.1 ∈ P ∧ e.2 ∉ T} + ∑ b ∈ T, c b) →
    ∃ J : Finset (V × V), J ⊆ E ∧
      (∀ a ∈ A, #{e ∈ J | e.1 = a} = d a) ∧
      (∀ b ∈ B, #{e ∈ J | e.2 = b} ≤ c b)

#check ReservationClaim
#check UnitBMatchingCutCriterion
#check Erdos585.QB4.exists_injOn_of_hall
#check Erdos585.QB4.exists_four_factor
#check Erdos585.B5Factor.exists_target_factor
#print ReservationClaim
#print UnitBMatchingCutCriterion
end Erdos585.MixedMatchingReservationR348
