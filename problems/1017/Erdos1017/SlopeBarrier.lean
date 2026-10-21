import Erdos1017.SplitDual
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace Erdos1017

/-- A finite integer split host obstructs any strictly larger anchored slope.
Only the dual lower bound is needed, not the exact split optimum. -/
theorem split_numeric_barrier (lam : ℝ) (hlam : Real.sqrt 7/3 < lam) :
    ∃ a s : ℕ, 0 < s ∧
      (1+lam)*(a+s:ℝ)^2/4 <
        (2:ℝ)/3*a*s-(1:ℝ)/6*s*(s-1)+lam*((a:ℝ)*s+(s:ℝ)*(s-1)/2) := by
  let r := Real.sqrt 7
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2=7 := Real.sq_sqrt (by norm_num)
  have hrlo : (7:ℝ)/3 < r := by nlinarith
  have hrhi : r < 3 := by nlinarith
  have hlpos : 0 < lam := by change r/3 < lam at hlam; linarith
  let t := r-2
  have htpos : 0 < t := by dsimp [t]; linarith
  let A := (3*r-7)/2*(lam-r/3)
  let B := (1+3*lam)/2
  have hA : 0 < A := by
    dsimp [A]
    change r/3 < lam at hlam
    exact mul_pos (by linarith) (sub_pos.mpr hlam)
  obtain ⟨s,hs⟩ := exists_nat_gt (max (1:ℝ) (B/A))
  have hspos : (0:ℝ) < s := lt_trans (by norm_num) (lt_of_le_of_lt (le_max_left _ _) hs)
  have hsN : 0 < s := by exact_mod_cast hspos
  have hBs : B < A*s := by
    have h := lt_of_le_of_lt (le_max_right (1:ℝ) (B/A)) hs
    exact (div_lt_iff₀ hA).mp h |>.trans_eq (mul_comm _ _)
  let a := ⌊t*(s:ℝ)⌋₊
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
  have halo : t*(s:ℝ)-1 ≤ a := le_of_lt (Nat.sub_one_lt_floor _)
  have hahi : (a:ℝ) ≤ t*s := Nat.floor_le (by positivity)
  have hxy : t*(s:ℝ)^2-s ≤ (a:ℝ)*s := by nlinarith
  have hsq : ((a:ℝ)+s)^2 ≤ ((t+1)*s)^2 := by
    have hsum : (a:ℝ)+s ≤ (t+1)*s := by nlinarith
    have hsum0 : 0 ≤ (a:ℝ)+s := by positivity
    exact sq_le_sq₀ hsum0 (by positivity) |>.mpr hsum
  have hid : (2/3+lam)*t+(lam/2-1/6)-(1+lam)*(t+1)^2/4=A := by
    dsimp [t,A]
    nlinarith [congrArg (fun z : ℝ => lam*z) hr2]
  have hlow : A*(s:ℝ)^2-B*s ≤
      (2:ℝ)/3*a*s-(1:ℝ)/6*s*(s-1)+lam*((a:ℝ)*s+(s:ℝ)*(s-1)/2) -
      (1+lam)*((a:ℝ)+s)^2/4 := by
    have hm1 := mul_le_mul_of_nonneg_left hxy (show 0 ≤ 2/3+lam by linarith)
    have hm2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (1+lam)/4 by positivity)
    have he := congrArg (fun z : ℝ => z*(s:ℝ)^2) hid
    dsimp [B]
    nlinarith [he]
  have hpos : 0 < A*(s:ℝ)^2-B*s := by nlinarith
  exact ⟨a,s,hsN,by linarith⟩

/-- Every slope larger than sqrt(7)/3 fails on a concrete finite simple graph. -/
theorem sharp_affine_slope_barrier (lam : ℝ) (hlam : Real.sqrt 7/3 < lam) :
    ∃ a s : ℕ, 0 < s ∧ ∀ P : FractionalPartition (splitGraph a s),
      (1+lam)*(Fintype.card (Fin a ⊕ Fin s):ℝ)^2/4 <
        P.cost+lam*((splitGraph a s).edgeFinset.card:ℝ) := by
  obtain ⟨a,s,hs,h⟩ := split_numeric_barrier lam hlam
  refine ⟨a,s,hs,?_⟩
  intro P
  have hp := split_partition_lower P
  rw [split_edge_count]
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add]
  linarith

end Erdos1017
