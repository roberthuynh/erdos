import HighPair

namespace Erdos60.HighSurplus
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def highVertices (G : SimpleGraph V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun x => q+2 ≤ G.degree x
noncomputable def heavyHigh (G : SimpleGraph V) (q : ℕ) : Finset V :=
  (highVertices G q).filter fun x => (q : ℝ)/5 ≤ Statistics.vertexCycleStatistic G x
noncomputable def lightHigh (G : SimpleGraph V) (q : ℕ) : Finset V :=
  (highVertices G q).filter fun x => (Statistics.vertexCycleStatistic G x : ℝ) < (q : ℝ)/5

 theorem restricted_cycle_sum (G : SimpleGraph V) (A : Finset V) :
    (∑ x ∈ A, Statistics.vertexCycleStatistic G x) ≤ 4*Counting.cycleCount G := by
  rw [← Statistics.vertexCycleStatistic_sum_eq_four]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    (fun i _ _ => Nat.zero_le _)

 theorem heavyHigh_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : 0 < q) (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    (heavyHigh G q).card < 20*T := by
  classical
  have hs : (∑ x ∈ heavyHigh G q, (q : ℝ)/5) ≤
      ∑ x ∈ heavyHigh G q, (Statistics.vertexCycleStatistic G x : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hb := restricted_cycle_sum G (heavyHigh G q)
  have hbr : (∑ x ∈ heavyHigh G q, (Statistics.vertexCycleStatistic G x : ℝ)) ≤
      4*(Counting.cycleCount G : ℝ) := by exact_mod_cast hb
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  nlinarith

 theorem opposite_set_quadratic (G : SimpleGraph V) (A : Finset V)
    (hopp : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 2 ≤ Statistics.codegree G x y) :
    A.card*(A.card-1) ≤ 4*Counting.cycleCount G := by
  have hlocal (x : V) (hx : x ∈ A) : A.card-1 ≤ Statistics.vertexCycleStatistic G x := by
    have hs : (∑ y ∈ A.erase x, (1 : ℕ)) ≤
        ∑ y ∈ A.erase x, (Statistics.codegree G x y).choose 2 := by
      apply Finset.sum_le_sum
      intro y hy
      have hc := hopp x hx y (Finset.mem_erase.mp hy).2 (Finset.mem_erase.mp hy).1.symm
      have hh := Nat.choose_le_choose 2 hc
      simpa using hh
    have hb : (∑ y ∈ A.erase x, (Statistics.codegree G x y).choose 2) ≤
        Statistics.vertexCycleStatistic G x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.erase_subset_erase x (Finset.subset_univ A)
      · intro y _ _; exact Nat.zero_le _
    simp only [Finset.sum_const, Nat.smul_one_eq_cast, Nat.cast_id,
      Finset.card_erase_of_mem hx] at hs
    omega
  have hs := Finset.sum_le_sum hlocal
  have hb := restricted_cycle_sum G A
  simpa using hs.trans hb

 theorem lightHigh_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((lightHigh G q).card : ℝ) ≤ 1+2*Real.sqrt (T*q) := by
  classical
  have hopp : ∀ x ∈ lightHigh G q, ∀ y ∈ lightHigh G q,
      x ≠ y → 2 ≤ Statistics.codegree G x y := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hdx := (Finset.mem_filter.mp hx'.1).2
    have hdy := (Finset.mem_filter.mp hy'.1).2
    exact HighPair.high_pair_opposite G q T hq hT hr hN hE hZ hxy hdx hdy hx'.2 hy'.2
  have hquad := opposite_set_quadratic G (lightHigh G q) hopp
  by_cases hzero : (lightHigh G q).card = 0
  · rw [hzero]
    norm_num only [Nat.cast_zero]
    positivity
  · have hn : 1 ≤ (lightHigh G q).card := Nat.one_le_iff_ne_zero.mpr hzero
    have hquadr : ((lightHigh G q).card : ℝ)*((lightHigh G q).card-1) ≤
        4*(Counting.cycleCount G : ℝ) := by
      have hc : ((lightHigh G q).card : ℝ)*(((lightHigh G q).card-1 : ℕ) : ℝ) ≤
          4*(Counting.cycleCount G : ℝ) := by exact_mod_cast hquad
      simpa only [Nat.cast_sub hn,Nat.cast_one] using hc
    have hprod : 0 ≤ T*(q : ℝ) := mul_nonneg (by linarith) (by linarith)
    have hs := Real.sq_sqrt hprod
    have hs0 := Real.sqrt_nonneg (T*(q : ℝ))
    have hn' : (1 : ℝ) ≤ (lightHigh G q).card := by exact_mod_cast hn
    nlinarith

 theorem high_partition (G : SimpleGraph V) (q : ℕ) :
    (highVertices G q).card = (heavyHigh G q).card+(lightHigh G q).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := highVertices G q)
    (p := fun x => (q : ℝ)/5 ≤ Statistics.vertexCycleStatistic G x)
  simpa [heavyHigh,lightHigh,not_le] using h.symm

/-- Source §3 equation (9), on the actual high-vertex set. -/
theorem high_count_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((highVertices G q).card : ℝ) ≤ 1+2*Real.sqrt (T*q)+20*T ∧
      ((highVertices G q).card : ℝ) ≤ 3*Real.sqrt (T*q) := by
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  have hh := heavyHigh_bound G q T hq0 hZ
  have hl := lightHigh_bound G q T hq hT hr hN hE hZ
  have hp := high_partition G q
  have hpr : ((highVertices G q).card : ℝ) =
      (heavyHigh G q).card+(lightHigh G q).card := by exact_mod_cast hp
  have hs := Parameters.sqrt_parameter hq hT hr
  constructor <;> linarith

 theorem high_count_small (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((highVertices G q).card : ℝ) ≤ (q : ℝ)/10 ∧
      ((highVertices G q).card : ℝ)/((q : ℝ)+1) ≤ T := by
  have hh := high_count_bound G q T hq hT hr hN hE hZ
  exact Parameters.high_count_parameter hq hT hr hh.2

end Erdos60.HighSurplus
