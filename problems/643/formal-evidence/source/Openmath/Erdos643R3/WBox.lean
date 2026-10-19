import Mathlib



set_option autoImplicit false

namespace Erdos643R3
namespace WBox

/-- `β` of Lemma W Step 1. -/
def betaW (N m2 : ℕ) : ℚ :=
  if m2 = 0 then 1 / 4 + 1 / (2 + (N : ℚ)) else 1 / 6 + 1 / (2 + (N : ℚ)) + 1 / (2 * (2 + (m2 : ℚ)))

/-- `XB + XC` of Lemma W Step 2 (and its mutual-case form, `mu = true`). -/
def XW (nB nC m m2 : ℕ) (mu : Bool) : ℚ :=
  if mu then (nC : ℚ) / (2 * (1 + (nB : ℚ))) + (nB : ℚ) / (2 * (1 + (nC : ℚ)))
  else
    (if 1 ≤ m then 1 / (2 * (1 + (nC : ℚ) + m)) + ((nB : ℚ) - 1) / (2 * (1 + (nC : ℚ)))
      else (nB : ℚ) / (2 * (1 + (nC : ℚ)))) +
    (if 1 ≤ m2 then 1 / (2 * (1 + (nB : ℚ) + m2)) + ((nC : ℚ) - 1) / (2 * (1 + (nB : ℚ)))
      else (nC : ℚ) / (2 * (1 + (nB : ℚ))))

/-- `Θ' = β + XB + XC + (m + m')/6 − 11/12`. -/
def thetaW (nB nC m m2 : ℕ) (mu : Bool) : ℚ :=
  betaW (nB + m2) m2 + XW nB nC m m2 mu + ((m : ℚ) + m2) / 6 - 11 / 12

/-- The threshold `τ` of §4. -/
def tauW (m m2 : ℕ) (mu : Bool) : ℚ :=
  if mu then 1 / 12
  else if m = 0 then (if m2 = 1 then 1 / 12 else 0)
  else if m = 1 then (if m2 = 1 then 1 / 6 else 1 / 12)
  else (m : ℚ) / (3 * ((m : ℚ) + 3)) + (if m2 = 1 then 1 / 12 else 0)

/-- Admissible points (where `thetap` of `wbox.py` does not return `None`). -/
def admW (nB nC m m2 : ℕ) (mu : Bool) : Bool :=
  decide (1 ≤ nB + m2) && decide (1 ≤ nC + m) &&
    (if mu then decide (nC = 0 ↔ nB = 0)
     else (!(decide (1 ≤ m)) || decide (1 ≤ nB)) && (!(decide (1 ≤ m2)) || decide (1 ≤ nC)) &&
       (!(decide (nC = 0)) || decide (nB ≤ (if 1 ≤ m then 1 else 0))) &&
       (!(decide (nB = 0)) || decide (nC ≤ (if 1 ≤ m2 then 1 else 0))))

/-- The point lies in the reduced box of Step 3. -/
def inBox (nB nC m m2 : ℕ) (mu : Bool) : Bool :=
  decide (nB ≤ 11) && decide (nC ≤ 11) && decide (1 ≤ m + m2) && decide (m + m2 ≤ 6) &&
    (!mu || (decide (m = 1) && decide (m2 = 1)))

/-- The finite check of Step 4 over all points `n_B, n_C ≤ 11`, `m, m' ≤ 6`, both values of `mu` (the mutual flag). -/
def wcheck : Bool :=
  (List.range 12).all fun nB => (List.range 12).all fun nC => (List.range 7).all fun m =>
    (List.range 7).all fun m2 => [false, true].all fun mu =>
      !(inBox nB nC m m2 mu && admW nB nC m m2 mu) || decide (tauW m m2 mu ≤ thetaW nB nC m m2 mu)

theorem wcheck_true : wcheck = true := by decide +kernel

/-- **Lemma W, Step 4** (g3hc §4): `Θ' ≥ τ` at every admissible point of the reduced box. -/
theorem wbox (nB nC m m2 : ℕ) (mu : Bool) (hbox : inBox nB nC m m2 mu = true)
    (hadm : admW nB nC m m2 mu = true) : tauW m m2 mu ≤ thetaW nB nC m m2 mu := by
  have hc := wcheck_true
  unfold wcheck at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have hb := hbox
  unfold inBox at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have h := hc nB (by omega) nC (by omega) m (by omega) m2 (by omega) mu (by cases mu <;> simp)
  rw [hbox, hadm] at h
  simpa using h

end WBox
end Erdos643R3
