import Openmath.Attempt6.ReachableEndpointPool
import Openmath.Attempt6.RoutingSelection
import Mathlib.Data.Real.Basic

/-!
# Exact deterministic balanced reservoir completion

The categorical probability law and its concentration events are supplied
separately. Here the good-event shore counts produce actual disjoint balanced
sets. Every original or retained graph degree is controlled by set inclusion.
-/
namespace Erdos585.Attempt6

open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v w
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Complete one lower set inside an upper set to the prescribed count on
each of two complementary shores. The final balanced set is constructed. -/
theorem exists_balanced_completion (R T Q : Finset V) (m : ℕ)
    (hleft : (R ∩ Q).card ≤ m ∧ m ≤ ((R ∪ T) ∩ Q).card)
    (hright : (R ∩ Qᶜ).card ≤ m ∧ m ≤ ((R ∪ T) ∩ Qᶜ).card) :
    ∃ S : Finset V, R ⊆ S ∧ S ⊆ R ∪ T ∧
      (S ∩ Q).card = m ∧ (S ∩ Qᶜ).card = m ∧ S.card = 2 * m := by
  classical
  obtain ⟨A, hRA, hAU, hAcard⟩ := Finset.exists_subsuperset_card_eq
    (show R ∩ Q ⊆ (R ∪ T) ∩ Q from
      Finset.inter_subset_inter Finset.subset_union_left (by rfl)) hleft.1 hleft.2
  obtain ⟨B, hRB, hBU, hBcard⟩ := Finset.exists_subsuperset_card_eq
    (show R ∩ Qᶜ ⊆ (R ∪ T) ∩ Qᶜ from
      Finset.inter_subset_inter Finset.subset_union_left (by rfl)) hright.1 hright.2
  have hAQ : A ⊆ Q := hAU.trans Finset.inter_subset_right
  have hBQ : B ⊆ Qᶜ := hBU.trans Finset.inter_subset_right
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_compl.mp (hBQ hxB)) (hAQ hxA)
  have heqA : (A ∪ B) ∩ Q = A := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxA | hxB, hxQ⟩
      · exact hxA
      · exact False.elim ((Finset.mem_compl.mp (hBQ hxB)) hxQ)
    · exact fun hxA => ⟨Or.inl hxA, hAQ hxA⟩
  have heqB : (A ∪ B) ∩ Qᶜ = B := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxA | hxB, hxQ⟩
      · exact False.elim ((Finset.mem_compl.mp hxQ) (hAQ hxA))
      · exact hxB
    · exact fun hxB => ⟨Or.inr hxB, hBQ hxB⟩
  refine ⟨A ∪ B, ?_, ?_, by rw [heqA, hAcard], by rw [heqB, hBcard], ?_⟩
  · intro x hx
    by_cases hxQ : x ∈ Q
    · exact Finset.mem_union_left _ (hRA (Finset.mem_inter.mpr ⟨hx, hxQ⟩))
    · exact Finset.mem_union_right _ (hRB (Finset.mem_inter.mpr
        ⟨hx, Finset.mem_compl.mpr hxQ⟩))
  · exact Finset.union_subset (hAU.trans Finset.inter_subset_left)
      (hBU.trans Finset.inter_subset_left)
  · rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard]
    omega

/-- Simultaneous completion preserves all categorical disjointness.
No independence or final balanced set is postulated. -/
theorem exists_pairwise_disjoint_balanced_completion {I : Type v}
    (R T : I → Finset V) (Q : Finset V) (m : I → ℕ)
    (hdis : Pairwise (fun i j => Disjoint (R i ∪ T i) (R j ∪ T j)))
    (hcounts : ∀ i,
      ((R i ∩ Q).card ≤ m i ∧ m i ≤ ((R i ∪ T i) ∩ Q).card) ∧
      ((R i ∩ Qᶜ).card ≤ m i ∧ m i ≤ ((R i ∪ T i) ∩ Qᶜ).card)) :
    ∃ S : I → Finset V,
      (∀ i, R i ⊆ S i ∧ S i ⊆ R i ∪ T i ∧
        (S i ∩ Q).card = m i ∧ (S i ∩ Qᶜ).card = m i ∧ (S i).card = 2 * m i) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) := by
  classical
  choose S hS using fun i => exists_balanced_completion (R i) (T i) Q (m i)
    (hcounts i).1 (hcounts i).2
  refine ⟨S, hS, ?_⟩
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  exact Finset.disjoint_left.mp (hdis hij) ((hS i).2.1 hxi) ((hS j).2.1 hxj)

/-- Actual original-neighbor counts are monotone under enlargement of the
reservoir. This also applies to every retained graph on the same support. -/
theorem graphDegreeInto_mono_set (G : SimpleGraph V) {A B : Finset V}
    (hAB : A ⊆ B) (x : V) : graphDegreeInto G A x ≤ graphDegreeInto G B x := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ hAB)

/-- Actual neighbor counts are monotone under original edge inclusion. -/
theorem graphDegreeInto_mono_graph {G H : SimpleGraph V} (hGH : G ≤ H)
    (A : Finset V) (x : V) : graphDegreeInto G A x ≤ graphDegreeInto H A x := by
  classical
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, hGH (Finset.mem_filter.mp hy).2⟩

/-- Arbitrary balancing incurs no additional degree error: every center
satisfies the actual lower/upper sample sandwich. -/
theorem balanced_completion_degree_sandwich (G : SimpleGraph V)
    {R T S : Finset V} (hRS : R ⊆ S) (hST : S ⊆ R ∪ T) (x : V) :
    graphDegreeInto G R x ≤ graphDegreeInto G S x ∧
      graphDegreeInto G S x ≤ graphDegreeInto G (R ∪ T) x :=
  ⟨graphDegreeInto_mono_set G hRS x, graphDegreeInto_mono_set G hST x⟩

/-- The same sandwich holds at every original ambient center after mapping
retained vertices injectively into the original vertex support. -/
theorem balanced_completion_ambient_degree_sandwich
    {W : Type w} [DecidableEq W] (f : W ↪ V) (G : SimpleGraph V)
    {R T S : Finset W} (hRS : R ⊆ S) (hST : S ⊆ R ∪ T) (x : V) :
    graphDegreeInto G (R.map f) x ≤ graphDegreeInto G (S.map f) x ∧
      graphDegreeInto G (S.map f) x ≤ graphDegreeInto G ((R ∪ T).map f) x :=
  ⟨graphDegreeInto_mono_set G (Finset.map_subset_map.mpr hRS) x,
    graphDegreeInto_mono_set G (Finset.map_subset_map.mpr hST) x⟩

/-- Every monotone connecting property of the retained lower reservoir is
inherited by the actual completion. -/
theorem balanced_completion_preserves_monotone_property
    (P : Finset V → Prop) (hmono : Monotone P) {R S : Finset V}
    (hRS : R ⊆ S) (hR : P R) : P S := hmono hRS hR

/-- Exact nonempty route interiors survive enlargement of their containing
reservoir, retaining the original walk and its original edges. -/
theorem supportsRoute_mono_reservoir (G : SimpleGraph V) {R S T : Finset V}
    (hRS : R ⊆ S) {ell : ℕ} {x y : V} (hroute : SupportsRoute G R ell x y T) :
    SupportsRoute G S ell x y T := by
  rcases hroute with ⟨hne, hTR, hx, hy, hcard, hp⟩
  exact ⟨hne, hTR.trans hRS, hx, hy, hcard, hp⟩

/-- The sample lower and upper degree deviations transfer to every actual
completion with exactly the same error. -/
theorem balanced_completion_degree_error (G : SimpleGraph V)
    {R T S : Finset V} (hRS : R ⊆ S) (hST : S ⊆ R ∪ T) (x : V)
    (q err : ℝ)
    (hlower : q - err ≤ (graphDegreeInto G R x : ℝ))
    (hupper : (graphDegreeInto G (R ∪ T) x : ℝ) ≤ q + err) :
    |(graphDegreeInto G S x : ℝ) - q| ≤ err := by
  obtain ⟨hlo, hhi⟩ := balanced_completion_degree_sandwich G hRS hST x
  have hloR : (graphDegreeInto G R x : ℝ) ≤ graphDegreeInto G S x := by exact_mod_cast hlo
  have hhiR : (graphDegreeInto G S x : ℝ) ≤ graphDegreeInto G (R ∪ T) x := by exact_mod_cast hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A near-regular bipartite graph has the source's quantitative shore bounds,
derived by counting its actual original edges from each shore. -/
theorem bipartite_nearRegular_shore_card_bounds (G0 : SimpleGraph V)
    (Q : Finset V) (hG : G0.IsBipartiteWith (Q : Set V) (Qᶜ : Set V))
    (d0 e : ℝ) (hd0 : 0 < d0) (he : 0 ≤ e)
    (hlower : ∀ v, d0 - e ≤ (Nat.card (G0.neighborSet v) : ℝ))
    (hupper : ∀ v, (Nat.card (G0.neighborSet v) : ℝ) ≤ d0 + e) :
    (Fintype.card V : ℝ) * (1 / 2 - e / d0) ≤ (Q.card : ℝ) ∧
      (Q.card : ℝ) ≤ (Fintype.card V : ℝ) * (1 / 2 + e / d0) := by
  classical
  have hdegree (v : V) : Nat.card (G0.neighborSet v) = G0.degree v := by
    rw [Nat.card_eq_fintype_card, G0.card_neighborSet_eq_degree]
  have hsum := G0.isBipartiteWith_sum_degrees_eq (s := Q) (t := Qᶜ)
    (by simpa only [Finset.coe_compl] using hG)
  have hsumR : (∑ v ∈ Q, (G0.degree v : ℝ)) =
      ∑ v ∈ Qᶜ, (G0.degree v : ℝ) := by exact_mod_cast hsum
  have hlo (A : Finset V) : (d0 - e) * A.card ≤ ∑ v ∈ A, (G0.degree v : ℝ) := by
    calc
      (d0 - e) * A.card = ∑ _v ∈ A, (d0 - e) := by simp [mul_comm]; ring
      _ ≤ _ := Finset.sum_le_sum (fun v _ => by simpa only [hdegree] using hlower v)
  have hhi (A : Finset V) : (∑ v ∈ A, (G0.degree v : ℝ)) ≤ (d0 + e) * A.card := by
    calc
      _ ≤ ∑ _v ∈ A, (d0 + e) := Finset.sum_le_sum
        (fun v _ => by simpa only [hdegree] using hupper v)
      _ = _ := by simp [mul_comm]; ring
  have hcross1 := (hlo Q).trans (hsumR ▸ hhi Qᶜ)
  have hcross2 := (hlo Qᶜ).trans (hsumR.symm ▸ hhi Q)
  have hcard : (Q.card : ℝ) + (Qᶜ.card : ℝ) = Fintype.card V := by
    have hh : Q.card + Qᶜ.card = Fintype.card V := by
      rw [Finset.card_compl]
      exact Nat.add_sub_of_le (Finset.card_le_univ Q)
    exact_mod_cast hh
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have heN : 0 ≤ e * (Fintype.card V : ℝ) := mul_nonneg he hN
  have hleft : (Fintype.card V : ℝ) * (1 / 2 - e / d0) * d0 =
      (Fintype.card V : ℝ) * d0 / 2 - (Fintype.card V : ℝ) * e := by
    field_simp
    <;> ring
  have hright : (Fintype.card V : ℝ) * (1 / 2 + e / d0) * d0 =
      (Fintype.card V : ℝ) * d0 / 2 + (Fintype.card V : ℝ) * e := by
    field_simp
    <;> ring
  constructor
  · apply (mul_le_mul_iff_left₀ hd0).mp
    rw [hleft]
    nlinarith
  · apply (mul_le_mul_iff_left₀ hd0).mp
    rw [hright]
    nlinarith

/-- The source connecting contract, with explicit simple original paths and
pairwise disjoint nonempty exact interiors. Terminal occurrences may repeat;
the two terminals of each requested path are distinct. -/
def NonemptyInteriorConnecting (G : SimpleGraph V) (U : Finset V) (D : ℝ) (ell : ℕ) : Prop :=
  ∀ (n : ℕ) (terminal : Fin n × Bool → V),
    (∀ i, terminal (i, false) ≠ terminal (i, true)) →
    (∀ i, terminal i ∉ U) →
    (∀ v ∈ U, (((Finset.univ : Finset (Fin n × Bool)).filter
      (fun i => G.Adj v (terminal i))).card : ℝ) ≤ D) →
    ∃ T : Fin n → Finset V,
      (∀ i, SupportsRoute G U ell (terminal (i, false)) (terminal (i, true)) (T i)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j))

/-- Enlarging a connecting reservoir preserves the actual source routing
contract: new outside terminal lists and degree restrictions also satisfy
the lower reservoir's conditions, and its exact interiors remain available. -/
theorem nonemptyInteriorConnecting_mono (G : SimpleGraph V) (D : ℝ) (ell : ℕ)
    {R S : Finset V} (hRS : R ⊆ S)
    (hR : NonemptyInteriorConnecting G R D ell) :
    NonemptyInteriorConnecting G S D ell := by
  intro n terminal hdistinct houtside hload
  obtain ⟨T, hT, hdis⟩ := hR n terminal hdistinct
    (fun i hi => houtside i (hRS hi))
    (fun v hv => hload v (hRS hv))
  exact ⟨T, fun i => supportsRoute_mono_reservoir G hRS (hT i), hdis⟩

/-- Full deterministic source-pool integration: the sampled categorical
counts and sampled degree bounds produce actual disjoint balanced reservoirs.
The retained degree error, ambient degree bound, and any monotone connecting
contract are preserved by the chosen completion. -/
theorem exists_balanced_completion_with_controls {I : Type v}
    (R T : I → Finset V) (Q : Finset V) (m : I → ℕ)
    (hdis : Pairwise (fun i j => Disjoint (R i ∪ T i) (R j ∪ T j)))
    (hcounts : ∀ i,
      ((R i ∩ Q).card ≤ m i ∧ m i ≤ ((R i ∪ T i) ∩ Q).card) ∧
      ((R i ∩ Qᶜ).card ≤ m i ∧ m i ≤ ((R i ∪ T i) ∩ Qᶜ).card))
    (G0 G : SimpleGraph V) (q err M : I → ℝ)
    (hlower : ∀ i x, q i - err i ≤ (graphDegreeInto G0 (R i) x : ℝ))
    (hupper : ∀ i x, (graphDegreeInto G0 (R i ∪ T i) x : ℝ) ≤ q i + err i)
    (hambient : ∀ i x, (graphDegreeInto G (R i ∪ T i) x : ℝ) ≤ M i)
    (P : I → Finset V → Prop) (hmono : ∀ i, Monotone (P i))
    (hP : ∀ i, P i (R i)) :
    ∃ S : I → Finset V,
      (∀ i, R i ⊆ S i ∧ S i ⊆ R i ∪ T i ∧
        (S i ∩ Q).card = m i ∧ (S i ∩ Qᶜ).card = m i ∧ (S i).card = 2 * m i) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (∀ i x, |(graphDegreeInto G0 (S i) x : ℝ) - q i| ≤ err i ∧
        (graphDegreeInto G (S i) x : ℝ) ≤ M i) ∧
      ∀ i, P i (S i) := by
  obtain ⟨S, hS, hSdis⟩ :=
    exists_pairwise_disjoint_balanced_completion R T Q m hdis hcounts
  refine ⟨S, hS, hSdis, ?_, ?_⟩
  · intro i x
    refine ⟨balanced_completion_degree_error G0 (hS i).1 (hS i).2.1 x
      (q i) (err i) (hlower i x) (hupper i x), ?_⟩
    have hn := graphDegreeInto_mono_set G (hS i).2.1 x
    have hr : (graphDegreeInto G (S i) x : ℝ) ≤ graphDegreeInto G (R i ∪ T i) x := by
      exact_mod_cast hn
    exact hr.trans (hambient i x)
  · intro i
    exact (hmono i) (hS i).1 (hP i)

end Erdos585.Attempt6
