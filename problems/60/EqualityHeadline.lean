import LinearRangeHeadline
import NearEquality
import PolarityMatchingCount

/-! Frozen linear-range theorem §6: equality iff an actual same-carrier
orthogonal polarity graph is extended by a matching on absolute vertices.
No geometric supplier or nearby-polarity premise is assumed. -/
namespace Erdos60.Headline
open scoped Classical
universe u
variable {P : Type u} [Fintype P]

/-- Actual equality classification on the original vertex carrier. Orthogonality
is expressed both by the exact M edge count and by q+1 absolute vertices.
The added graph is the actual graph difference G minus the polarity graph. -/
def OrthogonalMatchingExtension (G : SimpleGraph P) (q t : ℕ) : Prop :=
  ∃ (L : Type u) (fL : Fintype L) (mem : Membership P L), letI := fL; letI := mem
    ∃ pp : Configuration.ProjectivePlane P L, letI := pp
      Configuration.ProjectivePlane.order P L = q ∧
      ∃ π : Geometry.Polarity (P := P) (L := L),
        π.graph.edgeFinset.card = q*(q+1)^2/2 ∧
        Nat.card {a : P // π.Absolute a} = q+1 ∧
        π.graph ≤ G ∧
        (G.edgeFinset \ π.graph.edgeFinset).card = t ∧
        (∀ a b, (G \ π.graph).Adj a b → π.Absolute a ∧ π.Absolute b) ∧
        Counting.IsMatchingGraph (G \ π.graph)

/-- The forward equality classification uses the actual first-excess producer,
surplus edit transfer, and geometric equality necessity. -/
theorem orthogonal_matching_extension_of_equality (G : SimpleGraph P) (q t : ℕ)
    (heven : Even q) (hq : 10^16 ≤ q) (ht : 1 ≤ t) (hr : 10^8*t ≤ q)
    (hN : Fintype.card P = q^2+q+1) (hE : G.edgeFinset.card = q*(q+1)^2/2+t)
    (heq : Counting.cycleCount G = t*(q-1)) : OrthogonalMatchingExtension G q t := by
  classical
  obtain ⟨L,fL,mem,pp,ho,π,hsmall⟩ := nearby_polarity_of_few_cycles G q t
    heven hq ht hr hN hE heq.le
  let : Fintype L := fL
  let : Membership P L := mem
  let : Configuration.ProjectivePlane P L := pp
  have heven' : Even (Configuration.ProjectivePlane.order P L) := by simpa only [ho] using heven
  obtain ⟨hj,hM,hQG,hsupport,hmatching⟩ := π.near_equality_necessity G t heven' ht
    (by simpa only [ho] using hE) (by simpa only [ho] using hsmall)
    (by simpa only [ho] using heq)
  have habs := (π.edge_count_eq_iff_absolute_count heven').mp hM
  refine ⟨L,fL,mem,pp,ho,π,?_,?_,hQG,hj,hsupport,hmatching⟩
  · simpa only [ho] using hM
  · simpa only [ho] using habs

/-- Backward equality count: actual graph difference and union recover G,
then the proved absolute-matching construction count applies. -/
theorem equality_of_orthogonal_matching_extension (G : SimpleGraph P) (q t : ℕ)
    (hclass : OrthogonalMatchingExtension G q t) :
    Counting.cycleCount G = t*(q-1) := by
  classical
  obtain ⟨L,fL,mem,pp,ho,π,hM,habs,hQG,hj,hsupport,hmatching⟩ := hclass
  let : Fintype L := fL
  let : Membership P L := mem
  let : Configuration.ProjectivePlane P L := pp
  have hunion : π.graph ⊔ (G \ π.graph) = G := by
    ext a b
    change (π.graph.Adj a b ∨ (G.Adj a b ∧ ¬π.graph.Adj a b)) ↔ G.Adj a b
    constructor
    · rintro (hπ | ⟨hG,hnot⟩)
      · exact hQG hπ
      · exact hG
    · intro hG
      by_cases hπ : π.graph.Adj a b
      · exact Or.inl hπ
      · exact Or.inr ⟨hG,hπ⟩
  have hdiff : (G \ π.graph).edgeFinset.card = t := by
    rw [SimpleGraph.edgeFinset_sdiff]
    exact hj
  have hc := π.matching_absolute_cycle_count (G \ π.graph) hmatching hsupport
  rw [hunion] at hc
  simp only [← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card] at hc hdiff
  rw [hdiff,ho] at hc
  exact hc

/-- Full equality iff in the original linear surplus range. All hypotheses
refer to the actual host; no plane, polarity, or structural supplier is assumed. -/
theorem linear_range_equality_iff (G : SimpleGraph P) (q t : ℕ)
    (heven : Even q) (hq : 10^16 ≤ q) (ht : 1 ≤ t) (hr : 10^8*t ≤ q)
    (hN : Fintype.card P = q^2+q+1) (hE : G.edgeFinset.card = q*(q+1)^2/2+t) :
    Counting.cycleCount G = t*(q-1) ↔ OrthogonalMatchingExtension G q t := by
  exact ⟨orthogonal_matching_extension_of_equality G q t heven hq ht hr hN hE,
    equality_of_orthogonal_matching_extension G q t⟩

#print axioms orthogonal_matching_extension_of_equality
#print axioms equality_of_orthogonal_matching_extension
#print axioms linear_range_equality_iff
end Erdos60.Headline
