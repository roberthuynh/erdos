import Openmath.Erdos643R3.WBeta

set_option autoImplicit false
open scoped BigOperators
namespace Erdos643R3.WBox

def slotCost (d : ℕ) : ℚ := 1 / (2 * (1 + (d : ℚ)))

theorem slotCost_antitone {d p : ℕ} (h : d ≤ p) : slotCost p ≤ slotCost d := by
  unfold slotCost
  have hh : (d : ℚ) ≤ p := by exact_mod_cast h
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith

theorem sum_cost_cap {α : Type*} (s : Finset α) (degree : α → ℕ) (p : ℕ)
    (hcap : ∀ v ∈ s, degree v ≤ p) :
    (s.card : ℚ) / (2 * (1 + (p : ℚ))) ≤ ∑ v ∈ s, slotCost (degree v) := by
  have hh : ∑ _v ∈ s, slotCost p ≤ ∑ v ∈ s, slotCost (degree v) := by
    apply Finset.sum_le_sum
    intro v hv
    exact slotCost_antitone (hcap v hv)
  simpa [slotCost, nsmul_eq_mul, div_eq_mul_inv] using hh

/-- A distinguished slot has cap `p+m`; all the other slots have cap `p`.
The conclusion is the exact expression used in Lemma W Step 2. -/
theorem sideW_le_sum_cost {α : Type*} [DecidableEq α] (s : Finset α) (degree : α → ℕ)
    (p m : ℕ) (hcap : ∀ v ∈ s, degree v ≤ p + m)
    (hstar : 1 ≤ m → ∃ z ∈ s, ∀ v ∈ s, v ≠ z → degree v ≤ p) :
    sideW s.card p m ≤ ∑ v ∈ s, slotCost (degree v) := by
  by_cases hm : 1 ≤ m
  · obtain ⟨z, hz, hothers⟩ := hstar hm
    have hrest := sum_cost_cap (s.erase z) degree p (by
      intro v hv
      have hv' := Finset.mem_erase.mp hv
      exact hothers v hv'.2 hv'.1)
    have hzcap := slotCost_antitone (hcap z hz)
    have hcard := Finset.card_erase_add_one hz
    have hcard' : ((s.erase z).card : ℚ) + 1 = s.card := by exact_mod_cast hcard
    have hsumcost := Finset.sum_erase_add s (fun v => slotCost (degree v)) hz
    unfold sideW
    rw [if_pos hm]
    change 1 / (2 * (1 + ((p + m : ℕ) : ℚ))) ≤ slotCost (degree z) at hzcap
    push_cast at hzcap
    rw [← add_assoc] at hzcap
    rw [show ((s.card : ℚ) - 1) = (s.erase z).card by linarith]
    linarith
  · have hm0 : m = 0 := by omega
    subst m
    simpa [sideW] using sum_cost_cap s degree p (by simpa using hcap)

/-- Lemma W Step 2 from two actual finite sums and their distinguished-slot caps. -/
theorem XW_le_costs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (sB : Finset α) (sC : Finset β) (degreeB : α → ℕ) (degreeC : β → ℕ) (m m2 : ℕ)
    (hcapB : ∀ v ∈ sB, degreeB v ≤ sC.card + m)
    (hcapC : ∀ v ∈ sC, degreeC v ≤ sB.card + m2)
    (hstarB : 1 ≤ m → ∃ z ∈ sB, ∀ v ∈ sB, v ≠ z → degreeB v ≤ sC.card)
    (hstarC : 1 ≤ m2 → ∃ z ∈ sC, ∀ v ∈ sC, v ≠ z → degreeC v ≤ sB.card) :
    XW sB.card sC.card m m2 false ≤
      (∑ v ∈ sB, slotCost (degreeB v)) + (∑ v ∈ sC, slotCost (degreeC v)) := by
  rw [XW_sides]
  exact add_le_add (sideW_le_sum_cost sB degreeB sC.card m hcapB hstarB)
    (sideW_le_sum_cost sC degreeC sB.card m2 hcapC hstarC)

theorem sideW_eq_loss (n p m : ℕ) :
    sideW n p m = (n : ℚ) / (2 * (1 + (p : ℚ))) - lossW p m := by
  by_cases hm : m = 0
  · subst m
    simp [sideW, lossW]
  · have hm1 : 1 ≤ m := by omega
    simp only [sideW, lossW, hm, hm1, ↓reduceIte]
    ring

theorem remove_isolated (z r : ℚ) (hz : 2 ≤ z) (hr : 0 ≤ r) :
    1 / z ≤ 1 / (z + r) + r / 2 := by
  have hz0 : 0 < z := by linarith
  have heq : 1 / z - 1 / (z + r) = r / (z * (z + r)) := by
    field_simp
    ring
  have hb : r / (z * (z + r)) ≤ r / 2 := by
    apply div_le_div_of_nonneg_left hr (by norm_num)
    nlinarith [mul_nonneg hr (le_of_lt hz0), sq_nonneg (z - 2)]
  linarith

/-- The whole numerical R_w estimate from finite slot sets and concrete caps.
`sW` contains the ordinary R_w slots; `sA` contains the A_w slots. -/
theorem betaW_le_finite_costs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (sW : Finset α) (sA : Finset β) (degreeW : α → ℕ) (degreeA : β → ℕ)
    (vDegree N m r0 : ℕ)
    (hv : vDegree ≤ 1 + sA.card)
    (hW : ∀ v ∈ sW, degreeW v ≤ sA.card)
    (hA : ∀ v ∈ sA, degreeA v ≤ 1 + sW.card + m)
    (hstar : 1 ≤ m → ∃ z ∈ sA, ∀ v ∈ sA, v ≠ z → degreeA v ≤ 1 + sW.card) :
    betaW N m ≤ 1 / (2 + (sW.card : ℚ) + N + r0) + slotCost vDegree +
      (∑ v ∈ sW, slotCost (degreeW v)) + (∑ v ∈ sA, slotCost (degreeA v)) + (r0 : ℚ) / 2 := by
  have ha : 1 ≤ m → 1 ≤ sA.card := by
    intro hm
    obtain ⟨z, hz, _⟩ := hstar hm
    exact Finset.one_le_card.mpr ⟨z, hz⟩
  have hb := betaW_le_cost sA.card (1 + sW.card) N m (by omega) ha
  have hvc := slotCost_antitone hv
  have hwc := sum_cost_cap sW degreeW sA.card hW
  have hac := sideW_le_sum_cost sA degreeA (1 + sW.card) m hA hstar
  rw [sideW_eq_loss] at hac
  have hi := remove_isolated (2 + (sW.card : ℚ) + N) r0 (by
    have h1 : (0 : ℚ) ≤ sW.card := Nat.cast_nonneg _
    have h2 : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    linarith) (by positivity)
  unfold gW at hb
  change 1 / (2 * (1 + ((1 + sA.card : ℕ) : ℚ))) ≤ slotCost vDegree at hvc
  push_cast at hb hac hvc
  ring_nf at hb hac hvc hwc hi ⊢
  linarith

theorem card_le_indicator {α : Type*} [DecidableEq α] (s : Finset α)
    (degree : α → ℕ) (m : ℕ) (hpos : ∀ v ∈ s, 1 ≤ degree v)
    (hcap : ∀ v ∈ s, degree v ≤ m)
    (hstar : 1 ≤ m → ∃ z ∈ s, ∀ v ∈ s, v ≠ z → degree v ≤ 0) :
    s.card ≤ if 1 ≤ m then 1 else 0 := by
  by_cases hm : 1 ≤ m
  · obtain ⟨z, hz, hothers⟩ := hstar hm
    rw [if_pos hm]
    have hsubset : s ⊆ {z} := by
      intro v hv
      simp only [Finset.mem_singleton]
      by_contra hne
      have h1 := hpos v hv
      have h2 := hothers v hv hne
      omega
    simpa using Finset.card_le_card hsubset
  · rw [if_neg hm]
    have hs : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have h1 := hpos v hv
      have h2 := hcap v hv
      omega
    simp [hs]

/-- The admissibility filter follows from positive degrees and the actual caps. -/
theorem admissible_of_caps {α β : Type*} [DecidableEq α] [DecidableEq β]
    (sB : Finset α) (sC : Finset β) (degreeB : α → ℕ) (degreeC : β → ℕ) (m m2 : ℕ)
    (hmass : 1 ≤ m + m2)
    (hposB : ∀ v ∈ sB, 1 ≤ degreeB v) (hposC : ∀ v ∈ sC, 1 ≤ degreeC v)
    (hcapB : ∀ v ∈ sB, degreeB v ≤ sC.card + m)
    (hcapC : ∀ v ∈ sC, degreeC v ≤ sB.card + m2)
    (hstarB : 1 ≤ m → ∃ z ∈ sB, ∀ v ∈ sB, v ≠ z → degreeB v ≤ sC.card)
    (hstarC : 1 ≤ m2 → ∃ z ∈ sC, ∀ v ∈ sC, v ≠ z → degreeC v ≤ sB.card) :
    admW sB.card sC.card m m2 false = true := by
  have hB : 1 ≤ m → 1 ≤ sB.card := by
    intro hm
    obtain ⟨z, hz, _⟩ := hstarB hm
    exact Finset.one_le_card.mpr ⟨z, hz⟩
  have hC : 1 ≤ m2 → 1 ≤ sC.card := by
    intro hm
    obtain ⟨z, hz, _⟩ := hstarC hm
    exact Finset.one_le_card.mpr ⟨z, hz⟩
  have hzB : sC.card = 0 → sB.card ≤ if 1 ≤ m then 1 else 0 := by
    intro hz
    exact card_le_indicator sB degreeB m hposB (by simpa [hz] using hcapB)
      (by simpa [hz] using hstarB)
  have hzC : sB.card = 0 → sC.card ≤ if 1 ≤ m2 then 1 else 0 := by
    intro hz
    exact card_le_indicator sC degreeC m2 hposC (by simpa [hz] using hcapC)
      (by simpa [hz] using hstarC)
  have hBC : 1 ≤ sB.card + m2 := by omega
  have hCB : 1 ≤ sC.card + m := by omega
  by_cases hm : 1 ≤ m <;> by_cases hm2 : 1 ≤ m2 <;>
    simp_all [admW] <;> tauto

/-- The entire numerical threshold holds for two finite slot families whose
positive degrees satisfy the exact ordinary and distinguished caps. -/
theorem threshold_le_finite_costs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (sB : Finset α) (sC : Finset β) (degreeB : α → ℕ) (degreeC : β → ℕ) (m m2 : ℕ)
    (hmass : 1 ≤ m + m2)
    (hposB : ∀ v ∈ sB, 1 ≤ degreeB v) (hposC : ∀ v ∈ sC, 1 ≤ degreeC v)
    (hcapB : ∀ v ∈ sB, degreeB v ≤ sC.card + m)
    (hcapC : ∀ v ∈ sC, degreeC v ≤ sB.card + m2)
    (hstarB : 1 ≤ m → ∃ z ∈ sB, ∀ v ∈ sB, v ≠ z → degreeB v ≤ sC.card)
    (hstarC : 1 ≤ m2 → ∃ z ∈ sC, ∀ v ∈ sC, v ≠ z → degreeC v ≤ sB.card) :
    tauW m m2 false ≤ betaW (sB.card + m2) m2 +
      (∑ v ∈ sB, slotCost (degreeB v)) + (∑ v ∈ sC, slotCost (degreeC v)) +
      ((m : ℚ) + m2) / 6 - 11 / 12 := by
  have hadm := admissible_of_caps sB sC degreeB degreeC m m2 hmass hposB hposC
    hcapB hcapC hstarB hstarC
  have hnum := w_unbounded sB.card sC.card m m2 hmass hadm
  have hcost := XW_le_costs sB sC degreeB degreeC m m2 hcapB hcapC hstarB hstarC
  unfold thetaW at hnum
  linarith

end Erdos643R3.WBox
