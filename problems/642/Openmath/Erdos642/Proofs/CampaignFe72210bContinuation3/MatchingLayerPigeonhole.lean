import Mathlib

/-! Integer layer selection for the actual nested matching construction. -/
namespace Erdos642.CampaignFe72210bContinuation3.MatchingLayerPigeonhole

theorem dyadic_descent (s : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (hs : ∀ i < m, 2*s (i+1) < s i) : 2^m*s m < s 0 := by
  have hle : ∀ r ≤ m, 2^r*s r ≤ s 0 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      intro hr
      have hp := hs r (by omega)
      have hi := ih (by omega)
      calc
        2^(r+1)*s (r+1) = 2^r*(2*s (r+1)) := by ring
        _ ≤ 2^r*s r := (Nat.mul_lt_mul_of_pos_left hp (by positivity)).le
        _ ≤ s 0 := hi
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  calc
    2^(r+1)*s (r+1) = 2^r*(2*s (r+1)) := by ring
    _ < 2^r*s r := Nat.mul_lt_mul_of_pos_left (hs r (by omega)) (by positivity)
    _ ≤ s 0 := hle r (by omega)

/-- Genuine finite layer choice, including x=0. -/
theorem exists_doubling_layer (s : ℕ → ℕ) (n m x δ : ℕ)
    (hm : 1 ≤ m) (hidx : 1+m*x ≤ δ) (hpow : n ≤ 2^m)
    (hcard : s 1 ≤ n)
    (hpos : ∀ i, 1 ≤ i → i ≤ δ → 0 < s i) :
    ∃ q, 1 ≤ q ∧ q+x ≤ δ ∧ s q ≤ 2*s (q+x) := by
  by_contra h
  have hfail : ∀ q, 1 ≤ q → q+x ≤ δ → 2*s (q+x) < s q := by
    intro q hq hqx
    exact Nat.lt_of_not_ge (fun hh => h ⟨q,hq,hqx,hh⟩)
  have hstep : ∀ i < m, 2*s (1+(i+1)*x) < s (1+i*x) := by
    intro i hi
    have hmul : (i+1)*x ≤ m*x := Nat.mul_le_mul_right x (by omega)
    have hh := hfail (1+i*x) (by omega) (by nlinarith)
    convert hh using 1 <;> congr 2 <;> ring
  have hd := dyadic_descent (fun i => s (1+i*x)) m (by omega) hstep
  simp only [Nat.zero_mul,Nat.add_zero] at hd
  have hp : 1 ≤ s (1+m*x) := hpos _ (by omega) hidx
  have hl : 2^m ≤ 2^m*s (1+m*x) := by nlinarith [(show 0 < (2:ℕ)^m by positivity)]
  omega

end Erdos642.CampaignFe72210bContinuation3.MatchingLayerPigeonhole
