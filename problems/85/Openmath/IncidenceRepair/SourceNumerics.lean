import Mathlib

open scoped BigOperators
namespace Erdos85.IncidenceRepair

theorem geometric_quotient_eq_sum (q n : ℕ) (hq : 2 ≤ q) :
    (q^n - 1) / (q - 1) = ∑ i ∈ Finset.range n, q^i := by
  have h := geom_sum_mul_add (q - 1) n
  rw [Nat.sub_add_cancel (show 1 ≤ q by omega)] at h
  have he : q^n - 1 = (∑ i ∈ Finset.range n, q^i) * (q - 1) := by omega
  rw [he, Nat.mul_div_cancel _ (show 0 < q - 1 by omega)]

theorem source_degree_split (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (q^n - 1) / (q-1) = q^(n-1) + (q^(n-1) - 1) / (q-1) := by
  rw [geometric_quotient_eq_sum q n hq, geometric_quotient_eq_sum q (n-1) hq]
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [Finset.sum_range_succ]
  omega

theorem source_degree_le_twice_gap (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (q^n - 1) / (q-1) ≤ 2 * q^(n-1) := by
  apply Nat.div_le_of_le_mul
  have hp : q^n = q^(n-1) * q := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]
  have hsub : q-1+1=q := by omega
  have hmul : q^(n-1) * 2 ≤ q^(n-1) * q := Nat.mul_le_mul_left _ hq
  nlinarith [Nat.sub_le (q^n) 1]

theorem source_gap_ge_two (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) :
    2 ≤ q^(n-1) := by
  have hp : q^(n-1) = q^(n-2)*q := by
    conv_lhs => rw [show n-1 = (n-2)+1 by omega]
    rw [pow_succ]
  have hpow : 1 ≤ q^(n-2) := Nat.one_le_pow _ _ (by omega)
  rw [hp]
  nlinarith

theorem source_codegree_le_gap_sub_one (q n : ℕ) :
    (q^(n-1)-1)/(q-1) ≤ q^(n-1)-1 := Nat.div_le_self _ _

theorem source_parameters (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) :
    (q^n - 1) / (q-1) = q^(n-1) + (q^(n-1) - 1) / (q-1) ∧
    (q^n - 1) / (q-1) ≤ 2*q^(n-1) ∧ 2 ≤ q^(n-1) ∧
    (q^(n-1)-1)/(q-1) ≤ q^(n-1)-1 := by
  exact ⟨source_degree_split q n hq (by omega),
    source_degree_le_twice_gap q n hq (by omega), source_gap_ge_two q n hq hn,
    source_codegree_le_gap_sub_one q n⟩

end Erdos85.IncidenceRepair
