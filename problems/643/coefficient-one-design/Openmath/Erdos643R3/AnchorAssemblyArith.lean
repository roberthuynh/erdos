import Openmath.Erdos643R3.WBox

set_option autoImplicit false
namespace Erdos643R3.AnchorAssemblyArith

def uThreshold (m : ℕ) (D : ℚ) : ℚ :=
  if m = 0 then 0 else if m = 1 then D - 1 / 12 else -(m : ℚ) / (3 * ((m : ℚ) + 3))

def comp (m : ℕ) (D : ℚ) : ℚ :=
  if m = 0 then 0 else if m = 1 then 1 / 12 - D else 1 / 3

theorem active_penalty (a m m2 : ℕ) (D : ℚ) (hD : 0 ≤ D)
    (ha : a ≤ 1 + (if m = 1 then 1 else 0) + (if m2 = 1 then 1 else 0)) :
    ((a : ℚ) - 1) * D ≤ (if m = 1 then D else 0) + (if m2 = 1 then D else 0) := by
  have ha' : (a : ℚ) ≤ 1 + (if m = 1 then 1 else 0) + (if m2 = 1 then 1 else 0) := by
    exact_mod_cast ha
  by_cases hm : m = 1 <;> by_cases hm2 : m2 = 1 <;>
    simp only [hm, hm2, ↓reduceIte] at ha' ⊢ <;> nlinarith

/-- The exhaustive three-case arithmetic of S3, also covering the no-type2 case
when its separate nonnegative W estimate is supplied. -/
theorem single_margin (a m m2 : ℕ) (D G W : ℚ) (hD0 : 0 ≤ D) (hD : D ≤ 1 / 12)
    (ha : a ≤ 1 + (if m = 1 then 1 else 0) + (if m2 = 1 then 1 else 0))
    (hG : uThreshold m D < G) (hW : WBox.tauW m m2 false ≤ W) :
    0 < G + W - ((a : ℚ) - 1) * D := by
  have hp := active_penalty a m m2 D hD0 ha
  by_cases hm0 : m = 0
  · subst m
    by_cases hm2 : m2 = 1 <;> simp [uThreshold, WBox.tauW, hm2] at hG hW hp <;> linarith
  · by_cases hm1 : m = 1
    · subst m
      by_cases hm2 : m2 = 1 <;> simp [uThreshold, WBox.tauW, hm2] at hG hW hp <;> linarith
    · by_cases hm2 : m2 = 1 <;> simp [uThreshold, WBox.tauW, hm0, hm1, hm2] at hG hW hp <;>
        rw [neg_div] at hG <;> linarith

theorem comp_budget (m : ℕ) (D E : ℚ) (hE : E ≤ 1 / 12) :
    comp m D + (if m = 1 then D + E else 0) ≤ (m : ℚ) / 6 := by
  by_cases hm0 : m = 0
  · subst m
    norm_num [comp]
  · by_cases hm1 : m = 1
    · subst m
      simp [comp]
      linarith
    · have hm : (2 : ℚ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
      simp only [comp, hm0, hm1, ↓reduceIte]
      linarith

/-- Both deficient sides, allowing each to have any number of type-2 slots. -/
theorem both_margin (a m m2 : ℕ) (D E U W : ℚ)
    (hD0 : 0 ≤ D) (hE0 : 0 ≤ E) (hD : D ≤ 1 / 12) (hE : E ≤ 1 / 12)
    (ha : a ≤ 1 + (if m = 1 then 1 else 0) + (if m2 = 1 then 1 else 0))
    (hU : 2 < U + (13 / 12 - D) + comp m D)
    (hW : 2 < W + (13 / 12 - E) + comp m2 E) :
    0 < (1 + (m : ℚ) + m2) / 6 + U + W - 2 - (a : ℚ) * (D + E) := by
  have hp := active_penalty a m m2 (D + E) (by linarith) ha
  have hb1 := comp_budget m D E hE
  have hb2 := comp_budget m2 E D hD
  rw [add_comm E D] at hb2
  nlinarith

end Erdos643R3.AnchorAssemblyArith
