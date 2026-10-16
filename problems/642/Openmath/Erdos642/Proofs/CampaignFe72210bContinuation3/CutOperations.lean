import Openmath.Erdos642.Proofs.CampaignFe72210b.FinitePruning
import Openmath.Erdos642.Proofs.CampaignFe72210b.IncidenceCounts

/-! Actual induced edge partitions and the two local cut-extraction operations. -/
namespace Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.CampaignFe72210b
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def restrictedDegree (S : Finset V) (x : V) : ℕ := (S.filter (G.Adj x)).card
def edges (S : Finset V) : ℕ := inducedEdges G S
def cross (S U : Finset V) : ℕ := IncidenceCounts.count G U (S \ U)
noncomputable def average (S : Finset V) : ℝ := 2 * (edges G S : ℝ) / (S.card : ℝ)

theorem mask_degree_eq_restricted (S : Finset V) (x : V) (hx : x ∈ S) :
    (mask G S).degree x = restrictedDegree G S x := by
  rw [← (mask G S).card_neighborFinset_eq_degree]
  unfold restrictedDegree
  apply congrArg Finset.card
  ext y
  rw [(mask G S).mem_neighborFinset, Finset.mem_filter]
  change (G.Adj x y ∧ x ∈ S ∧ y ∈ S) ↔ y ∈ S ∧ G.Adj x y
  tauto

theorem mask_degree_eq_zero (S : Finset V) (x : V) (hx : x ∉ S) :
    (mask G S).degree x = 0 := by
  rw [← (mask G S).card_neighborFinset_eq_degree]
  have he : (mask G S).neighborFinset x = ∅ := by
    ext y
    rw [(mask G S).mem_neighborFinset]
    simp [mask, hx]
  rw [he]
  rfl

/-- Actual fixed-ambient handshaking on the selected vertices. -/
theorem count_self_eq_twice_edges (S : Finset V) :
    IncidenceCounts.count G S S = 2 * edges G S := by
  have hs : (∑ x ∈ S, restrictedDegree G S x) = ∑ x, (mask G S).degree x := by
    calc
      _ = ∑ x ∈ S, (mask G S).degree x :=
        Finset.sum_congr rfl fun x hx => (mask_degree_eq_restricted G S x hx).symm
      _ = _ := Finset.sum_subset (Finset.subset_univ S)
        (fun x _ hx => mask_degree_eq_zero G S x hx)
  exact hs.trans (mask G S).sum_degrees_eq_twice_card_edges

omit [Fintype V] in
theorem count_partition_left (S U B : Finset V) (hUS : U ⊆ S) :
    IncidenceCounts.count G S B =
      IncidenceCounts.count G U B + IncidenceCounts.count G (S \ U) B := by
  unfold IncidenceCounts.count
  rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hUS]

omit [Fintype V] in
theorem count_partition_right (S U B : Finset V) (hUS : U ⊆ S) :
    IncidenceCounts.count G B S =
      IncidenceCounts.count G B U + IncidenceCounts.count G B (S \ U) := by
  rw [IncidenceCounts.count_swap G B S, count_partition_left G S U B hUS,
    IncidenceCounts.count_swap G U B, IncidenceCounts.count_swap G (S \ U) B]

/-- The actual unordered edge partition; crossing edges are counted once. -/
theorem edges_partition (S U : Finset V) (hUS : U ⊆ S) :
    edges G S = edges G U + edges G (S \ U) + cross G S U := by
  have hs := count_partition_left G S U S hUS
  rw [count_partition_right G S U U hUS,
    count_partition_right G S U (S \ U) hUS,
    IncidenceCounts.count_swap G (S \ U) U,
    count_self_eq_twice_edges G S, count_self_eq_twice_edges G U,
    count_self_eq_twice_edges G (S \ U)] at hs
  unfold cross
  omega

/-- Positive average excludes both the empty set and a singleton. -/
theorem average_pos_card (S : Finset V) (hpos : 0 < average G S) : 2 ≤ S.card := by
  by_contra hn
  have hc : S.card ≤ 1 := by omega
  have hd : ∀ x ∈ S, restrictedDegree G S x = 0 := by
    intro x hx
    unfold restrictedDegree
    have he : S.filter (G.Adj x) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨hy, hxy⟩
      have h : x = y := Finset.card_le_one.mp hc x hx y hy
      subst y
      exact G.irrefl hxy
    rw [he]
    rfl
  have hs : (∑ x ∈ S, restrictedDegree G S x) = 0 :=
    Finset.sum_eq_zero fun x hx => hd x hx
  have hh := count_self_eq_twice_edges G S
  change (∑ x ∈ S, restrictedDegree G S x) = 2 * edges G S at hh
  rw [hs] at hh
  have he : edges G S = 0 := by omega
  simp [average, he] at hpos

theorem average_mul_card (S : Finset V) (hS : S.Nonempty) :
    average G S * (S.card : ℝ) = 2 * (edges G S : ℝ) := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  exact div_mul_cancel₀ _ hc

/-- Deleting an actual vertex below half the current average strictly increases average. -/
theorem average_erase_gt (S : Finset V) (x : V) (hx : x ∈ S)
    (hpos : 0 < average G S)
    (hlow : (restrictedDegree G S x : ℝ) < average G S / 2) :
    (S.erase x).Nonempty ∧ (S.erase x).card < S.card ∧
      average G S < average G (S.erase x) := by
  have hc := average_pos_card G S hpos
  have hecard := Finset.card_erase_add_one hx
  have hne : (S.erase x).Nonempty := Finset.card_pos.mp (by omega)
  have hcard : ((S.erase x).card : ℝ) + 1 = (S.card : ℝ) := by exact_mod_cast hecard
  have hedge : edges G (S.erase x) + restrictedDegree G S x = edges G S := by
    simpa only [edges, mask_degree_eq_restricted G S x hx] using
      inducedEdges_erase_add_degree G S x
  have hedger : (edges G (S.erase x) : ℝ) + (restrictedDegree G S x : ℝ) =
      (edges G S : ℝ) := by exact_mod_cast hedge
  have hs := average_mul_card G S ⟨x, hx⟩
  have he := average_mul_card G (S.erase x) hne
  rw [← hcard, ← hedger] at hs
  have hcp : 0 < ((S.erase x).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hscaled : average G S * ((S.erase x).card : ℝ) <
      average G (S.erase x) * ((S.erase x).card : ℝ) := by nlinarith
  exact ⟨hne, Finset.card_erase_lt_of_mem hx, (mul_lt_mul_iff_left₀ hcp).mp hscaled⟩

/-- Sparse cut: retain the complement without loss, or the smaller side with controlled loss. -/
theorem sparse_cut_alternative (S U : Finset V) (lam : ℝ)
    (hUS : U ⊆ S) (hpos : 0 < average G S)
    (hhalf : 2 * U.card ≤ S.card) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (hcut : (cross G S U : ℝ) < lam * average G S * (U.card : ℝ) / 3) :
    ((S \ U).Nonempty ∧ (S \ U).card < S.card ∧
      average G S ≤ average G (S \ U)) ∨
    (U.Nonempty ∧ U.card < S.card ∧ 2 * U.card ≤ S.card ∧
      0 < average G U ∧ (1 - lam) * average G S ≤ average G U) := by
  have hc := average_pos_card G S hpos
  have hU : U.Nonempty := by
    by_contra hn
    have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he, cross, IncidenceCounts.count] at hcut
  have hu : 0 < U.card := Finset.card_pos.mpr hU
  have hcards := Finset.card_sdiff_add_card_eq_card hUS
  have hW : (S \ U).Nonempty := Finset.card_pos.mp (by omega)
  have hw : 0 < (S \ U).card := Finset.card_pos.mpr hW
  have hWlt : (S \ U).card < S.card := by omega
  by_cases hkeep : average G S ≤ average G (S \ U)
  · exact Or.inl ⟨hW, hWlt, hkeep⟩
  · have hlose : average G (S \ U) < average G S := lt_of_not_ge hkeep
    have hur : 0 < (U.card : ℝ) := by exact_mod_cast hu
    have hwr : 0 < ((S \ U).card : ℝ) := by exact_mod_cast hw
    have hcardr : ((S \ U).card : ℝ) + (U.card : ℝ) = (S.card : ℝ) := by
      exact_mod_cast hcards
    have he := edges_partition G S U hUS
    have her : (edges G S : ℝ) = (edges G U : ℝ) + (edges G (S \ U) : ℝ) +
        (cross G S U : ℝ) := by exact_mod_cast he
    have hs := average_mul_card G S (hU.mono hUS)
    have ha := average_mul_card G U hU
    have hb := average_mul_card G (S \ U) hW
    rw [← hcardr, her] at hs
    have hpart : average G S * ((U.card : ℝ) + ((S \ U).card : ℝ)) =
        average G U * (U.card : ℝ) + average G (S \ U) * ((S \ U).card : ℝ) +
          2 * (cross G S U : ℝ) := by nlinarith
    have hterm := mul_lt_mul_of_pos_right hlose hwr
    have hstrong : (1 - 2 * lam / 3) * average G S * (U.card : ℝ) <
        average G U * (U.card : ℝ) := by nlinarith [hpart, hterm, hcut]
    have havg : (1 - 2 * lam / 3) * average G S < average G U :=
      (mul_lt_mul_iff_left₀ hur).mp hstrong
    have hweak : (1 - lam) * average G S ≤ average G U := by
      nlinarith [mul_nonneg hlam.le hpos.le]
    have hapos : 0 < average G U :=
      lt_of_lt_of_le (mul_pos (by linarith : 0 < 1 - lam) hpos) hweak
    exact Or.inr ⟨hU, by omega, hhalf, hapos, hweak⟩

end Erdos642.CampaignFe72210bContinuation3.CutExtraction
