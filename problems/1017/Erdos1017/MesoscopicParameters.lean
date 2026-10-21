import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Integer part sizes for exact edge interpolation. This natural-number form
of the parity choice avoids negative integer quotients in graph cardinalities. -/
namespace Erdos1017.Mesoscopic

def partB (n s : ℕ) : ℕ := (3*n - 5*s - 7)/6
def partA (n s : ℕ) : ℕ := n - 2 - s - partB n s
def baseEdges (n s : ℕ) : ℕ :=
  partA n s * partB n s + (partA n s + partB n s)*s +
    s.choose 2 + 2*(partA n s+s)

theorem part_bounds (n s : ℕ) (hn : 100 ≤ n) (hs : 10*s ≤ n) :
    0 < partA n s ∧ 0 < partB n s ∧ partA n s + partB n s+s+2=n ∧
    3*partB n s+2*s < 3*partA n s ∧
    3*partA n s ≤ 3*partB n s+2*s+6 := by
  unfold partA partB
  omega

theorem part_step (n s : ℕ) (hn : 100 ≤ n) (hs : 10*(s+1) ≤ n) :
    (partA n (s+1)=partA n s ∧ partB n (s+1)+1=partB n s) ∨
    (partA n (s+1)+1=partA n s ∧ partB n (s+1)=partB n s) := by
  unfold partA partB
  omega

theorem part_zero (n : ℕ) (hn : 100 ≤ n) :
    partA n 0 = n/2 ∧ partB n 0+2 = n-n/2 := by
  unfold partA partB
  omega

theorem choose_two_real (s : ℕ) :
    (s.choose 2 : ℝ) = (s:ℝ)*(s-1)/2 := by
  exact Nat.cast_choose_two ℝ s

theorem baseEdges_real (n s : ℕ) :
    (baseEdges n s : ℝ) = (partA n s:ℝ)*partB n s +
      (partA n s+partB n s : ℝ)*s + (s:ℝ)*(s-1)/2 +
      2*((partA n s:ℝ)+s) := by
  simp only [baseEdges, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, choose_two_real]

theorem quarter_eq (n : ℕ) : n*n/4=(n/2)*(n-n/2) := by
  have hr := Nat.mod_lt n (by decide : 0 < 2)
  have he := Nat.mod_add_div n 2
  have hs : n-n/2+n/2=n := by omega
  have hsq : n*n=4*((n/2)*(n-n/2))+n%2 := by
    have hc : n%2=0 ∨ n%2=1 := by omega
    rcases hc with hc|hc <;> nlinarith
  omega

theorem quarter_bounds (n : ℕ) :
    (0:ℝ) ≤ (n:ℝ)^2/4-(n*n/4:ℕ) ∧ (n:ℝ)^2/4-(n*n/4:ℕ) ≤ 1/4 := by
  have hr := Nat.mod_lt n (by decide : 0 < 2)
  have he := Nat.mod_add_div n 2
  have hs : n-n/2+n/2=n := by omega
  have hsq : n*n=4*(n*n/4)+n%2 := by
    rw [quarter_eq]
    have hc : n%2=0 ∨ n%2=1 := by omega
    rcases hc with hc|hc <;> nlinarith
  have hreal : (n:ℝ)^2=4*(n*n/4:ℕ)+(n%2:ℕ) := by
    rw [pow_two]
    exact_mod_cast hsq
  have hmod0 : (0:ℝ) ≤ (n%2:ℕ) := Nat.cast_nonneg _
  have hmod1 : ((n%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show n%2 ≤ 1 by omega)
  constructor <;> nlinarith

theorem baseEdges_zero (n : ℕ) (hn : 100 ≤ n) : baseEdges n 0=n*n/4 := by
  obtain ⟨ha,hb⟩ := part_zero n hn
  simp only [baseEdges, Nat.choose_zero_succ, mul_zero, add_zero, ha]
  rw [quarter_eq]
  nlinarith

theorem baseEdges_identity (n s : ℕ) (hn : 100 ≤ n) (hs : 10*s ≤ n) :
    (baseEdges n s:ℝ) = (n:ℝ)^2/4 + ((n:ℝ)-1)*s/2 -
      ((s:ℝ)^2+((partA n s:ℝ)-partB n s-2)^2)/4 := by
  have h := (part_bounds n s hn hs).2.2.1
  have hr : (n:ℝ) = (partA n s:ℝ)+partB n s+s+2 := by exact_mod_cast h.symm
  rw [baseEdges_real,hr]
  ring

theorem baseEdges_step (n s : ℕ) (hn : 100 ≤ n) (hs : 10*(s+1) ≤ n) :
    baseEdges n s < baseEdges n (s+1) ∧
    baseEdges n (s+1) ≤ baseEdges n s + 2*partB n s := by
  have hs0 : 10*s ≤ n := by omega
  obtain ⟨ha0,hb0,hsize,hdlo,hdhi⟩ := part_bounds n s hn hs0
  have ha2 : 2 ≤ partA n s := by omega
  have hab : partA n s ≤ 2*partB n s+1 := by omega
  have hE := baseEdges_real n s
  have hE' := baseEdges_real n (s+1)
  have hsreal : ((s+1:ℕ):ℝ)=(s:ℝ)+1 := by push_cast; rfl
  rw [hsreal] at hE'
  rcases part_step n s hn hs with ⟨ha,hb⟩|⟨ha,hb⟩
  · have hb' : (partB n (s+1):ℝ)=(partB n s:ℝ)-1 := by
      have h : (partB n (s+1):ℝ)+1=(partB n s:ℝ) := by exact_mod_cast hb
      linarith
    rw [ha,hb'] at hE'
    have hdiff : baseEdges n (s+1)=baseEdges n s+partB n s+1 := by
      have h : (baseEdges n (s+1):ℝ)=(baseEdges n s:ℝ)+partB n s+1 := by nlinarith
      exact_mod_cast h
    omega
  · have ha' : (partA n (s+1):ℝ)=(partA n s:ℝ)-1 := by
      have h : (partA n (s+1):ℝ)+1=(partA n s:ℝ) := by exact_mod_cast ha
      linarith
    rw [ha',hb] at hE'
    have hdiff : baseEdges n (s+1)+1=baseEdges n s+partA n s := by
      have h : (baseEdges n (s+1):ℝ)+1=(baseEdges n s:ℝ)+partA n s := by nlinarith
      exact_mod_cast h
    omega

end Erdos1017.Mesoscopic
