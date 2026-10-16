import Mathlib.Tactic

/-! Integer transfer arithmetic for the exact #60 endpoint.
This file proves arithmetic only. The graph path count and polarity producer
are separate obligations, not axioms or claimed consequences of this file. -/

set_option autoImplicit false
namespace Erdos60.Transfer

/-- Exact surplus identity; integer subtraction retains every deficit term. -/
theorem surplus_identity (q t j δ : ℤ) :
    j * (q - 1 - j + t + δ) - t * (q - 1) =
      (j - t) * (q - 1 - j) + j * δ := by ring

/-- The retained-path bound forces the sharp lower bound. -/
theorem lower_bound (q t j δ Z : ℤ)
    (ht : 0 ≤ t) (hjt : t ≤ j) (hsmall : j ≤ q - 1)
    (hδ : 0 ≤ δ) (hcount : j * (q - 1 - j + t + δ) ≤ Z) :
    t * (q - 1) ≤ Z := by
  have hj : 0 ≤ j := le_trans ht hjt
  have hprod := mul_nonneg (sub_nonneg.mpr hjt) (sub_nonneg.mpr hsmall)
  have hdef := mul_nonneg hj hδ
  have hid := surplus_identity q t j δ
  linarith

/-- At equality, strict slack forces no polarity deficit and no missing edges. -/
theorem equality_counts (q t j δ d Z : ℤ)
    (ht : 1 ≤ t) (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hbalance : d = j - t - δ) (hsmall : j < q - 1)
    (hcount : j * (q - 1 - d) ≤ Z) (heq : Z = t * (q - 1)) :
    j = t ∧ δ = 0 ∧ d = 0 := by
  have hjt : t ≤ j := by omega
  have hj : 0 < j := by omega
  have hslack : 0 < q - 1 - j := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hjt) (le_of_lt hslack)
  have hδp := mul_nonneg (le_of_lt hj) hδ
  have hid := surplus_identity q t j δ
  have hzero : (j - t) * (q - 1 - j) + j * δ ≤ 0 := by
    rw [hbalance] at hcount
    nlinarith only [hcount, heq, hid]
  have hδzero : j * δ = 0 := by omega
  have hδeq : δ = 0 := (mul_eq_zero.mp hδzero).resolve_left (ne_of_gt hj)
  have hpzero : (j - t) * (q - 1 - j) = 0 := by omega
  have hjzero : j - t = 0 :=
    (mul_eq_zero.mp hpzero).resolve_right (ne_of_gt hslack)
  exact ⟨by omega, hδeq, by omega⟩

/-- The stated linear interval guarantees the strict transfer slack. -/
theorem linear_range_slack (q t j : ℤ)
    (hq : 10^16 ≤ q) (hrange : 10^8 * t ≤ q)
    (hj : j < 3 * t) : j < q - 1 := by omega

/-- The localized retained paths give the producer's strict edit bound. -/
theorem first_excess_edits (q T j Z : ℝ)
    (hj : 0 ≤ j) (hq : 0 < q)
    (hslack : q / 2 < q - 1 - 896 * T)
    (hcount : j * (q - 1 - 896 * T) ≤ Z) (hfew : Z < T * q) :
    j < 2 * T := by
  have hh := mul_le_mul_of_nonneg_left (le_of_lt hslack) hj
  nlinarith

/-- Actual finite edge sets obey the surplus balance, without truncating subtraction. -/
theorem edge_balance {α : Type*} [DecidableEq α] (G Q : Finset α)
    (M t δ : ℤ) (hG : (G.card : ℤ) = M + t)
    (hQ : (Q.card : ℤ) = M - δ) :
    ((Q \ G).card : ℤ) = ((G \ Q).card : ℤ) - t - δ := by
  have h₁ := Finset.card_sdiff_add_card_inter G Q
  have h₂ := Finset.card_sdiff_add_card_inter Q G
  rw [Finset.inter_comm Q G] at h₂
  have hc₁ : ((G \ Q).card : ℤ) + ((G ∩ Q).card : ℤ) = G.card := by
    exact_mod_cast h₁
  have hc₂ : ((Q \ G).card : ℤ) + ((G ∩ Q).card : ℤ) = Q.card := by
    exact_mod_cast h₂
  omega

/-- Transfer on literal edge sets once the graph-specific retained-path bound is proved.
The bound is an explicit premise, so this is not the headline graph theorem. -/
theorem finite_edge_transfer {α : Type*} [DecidableEq α] (G Q : Finset α)
    (M q t δ Z : ℤ) (ht : 0 ≤ t) (hδ : 0 ≤ δ)
    (hG : (G.card : ℤ) = M + t) (hQ : (Q.card : ℤ) = M - δ)
    (hsmall : ((G \ Q).card : ℤ) ≤ q - 1)
    (hcount : ((G \ Q).card : ℤ) * (q - 1 - (Q \ G).card) ≤ Z) :
    t * (q - 1) ≤ Z := by
  have hb := edge_balance G Q M t δ hG hQ
  have hd : (0 : ℤ) ≤ (Q \ G).card := by positivity
  have hjt : t ≤ ((G \ Q).card : ℤ) := by omega
  apply lower_bound q t (G \ Q).card δ Z ht hjt hsmall hδ
  rw [hb] at hcount
  convert hcount using 1 <;> ring


/-- Natural cycle counts and truncated path counts imply the integer transfer bound.
The edge balance forces the path subtraction to stay untruncated. -/
theorem natural_transfer (q t j δ d Z : ℕ)
    (hbalance : d + t + δ = j) (hsmall : j ≤ q - 1)
    (hcount : j * (q - 1 - d) ≤ Z) : t * (q - 1) ≤ Z := by
  have hd : d ≤ q - 1 := by omega
  have hjt : t ≤ j := by omega
  have hcountZ : (j : ℤ) * ((q - 1 : ℕ) - (d : ℤ)) ≤ (Z : ℤ) := by
    have hc : (j : ℤ) * ((q - 1 - d : ℕ) : ℤ) ≤ (Z : ℤ) := by
      exact_mod_cast hcount
    rw [Nat.cast_sub hd] at hc
    exact hc
  have hbalZ : (d : ℤ) + (t : ℤ) + (δ : ℤ) = (j : ℤ) := by
    exact_mod_cast hbalance
  have hsmallZ : (j : ℤ) ≤ ((q - 1 : ℕ) : ℤ) := by exact_mod_cast hsmall
  have hrewrite : (((q - 1 : ℕ) : ℤ) + 1) - 1 - j + t + δ =
      ((q - 1 : ℕ) : ℤ) - d := by omega
  have hb := lower_bound (((q - 1 : ℕ) : ℤ) + 1) (t : ℤ) (j : ℤ)
    (δ : ℤ) (Z : ℤ) (by positivity) (by exact_mod_cast hjt)
    (by simpa using hsmallZ) (by positivity) (by rwa [hrewrite])
  have hr : (t : ℤ) * ((q - 1 : ℕ) : ℤ) ≤ (Z : ℤ) := by
    simpa using hb
  exact_mod_cast hr

end Erdos60.Transfer
