import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

                                                                                                
                                                                                        
                                                                                      
                                                        
namespace Erdos642.CloudT9_20261021.ExponentFixedPoint

theorem b_eq_rpow {L ℓ b : ℝ} (hL : 0 < L) (hℓ : ℓ = L ^ ((1 : ℝ) / 4)) (hb : b = L / ℓ) :
    b = L ^ ((3 : ℝ) / 4) := by
  rw [hb, hℓ]
  have h := Real.rpow_sub hL (1 : ℝ) ((1 : ℝ) / 4)
  rw [Real.rpow_one] at h
  rw [← h]
  norm_num

theorem d_eq_rpow {L ℓ b d : ℝ} (hL : 0 < L) (hℓ : ℓ = L ^ ((1 : ℝ) / 4)) (hb : b = L / ℓ)
    (hd : d = b * L) : d = L ^ ((7 : ℝ) / 4) := by
  rw [hd, b_eq_rpow hL hℓ hb]
  have h := Real.rpow_add hL ((3 : ℝ) / 4) (1 : ℝ)
  rw [Real.rpow_one] at h
  rw [← h]
  norm_num

end Erdos642.CloudT9_20261021.ExponentFixedPoint
