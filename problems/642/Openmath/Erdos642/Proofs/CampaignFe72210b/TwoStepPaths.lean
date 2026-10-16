import Openmath.Erdos642.Proofs.CampaignFe72210b.FiniteMarkov

/-! Actual two-step path laws, proved by summing omitted intermediate vertices. -/
namespace Erdos642.FiniteMarkov

universe u
variable {V : Type u}

/-- A recursive double length, definitionally exposing two future states per step. -/
def doubleLength : ℕ → ℕ
  | 0 => 0
  | n + 1 => doubleLength n + 2

theorem doubleLength_eq_two_mul (n : ℕ) : doubleLength n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [doubleLength, ih, Nat.mul_succ]

/-- First argument contains omitted odd states, second retained even states. -/
def interleave : {n : ℕ} → Path V n → Path V n → Path V (doubleLength n)
  | 0, _, _ => PUnit.unit
  | _n + 1, p, q => (p.1, (q.1, interleave p.2 q.2))

def sampleOdd : {n : ℕ} → Path V (doubleLength n) → Path V n
  | 0, _ => PUnit.unit
  | _n + 1, p => (p.1, sampleOdd p.2.2)

def sampleEven : {n : ℕ} → Path V (doubleLength n) → Path V n
  | 0, _ => PUnit.unit
  | _n + 1, p => (p.2.1, sampleEven p.2.2)

theorem sampleOdd_interleave {n : ℕ} (p q : Path V n) :
    sampleOdd (interleave p q) = p := by
  induction n with
  | zero => cases p; rfl
  | succ n ih =>
    change (p.1, sampleOdd (interleave p.2 q.2)) = p
    rw [ih]
    cases p
    rfl

theorem sampleEven_interleave {n : ℕ} (p q : Path V n) :
    sampleEven (interleave p q) = q := by
  induction n with
  | zero => cases q; rfl
  | succ n ih =>
    change (q.1, sampleEven (interleave p.2 q.2)) = q
    rw [ih]
    cases q
    rfl

theorem interleave_samples {n : ℕ} (p : Path V (doubleLength n)) :
    interleave (sampleOdd p) (sampleEven p) = p := by
  induction n with
  | zero => cases p; rfl
  | succ n ih =>
    change (p.1, (p.2.1, interleave (sampleOdd p.2.2) (sampleEven p.2.2))) = p
    rw [ih]
    cases p with
    | mk a p => cases p; rfl

/-- Every actual long path is uniquely its omitted and retained state sequences. -/
def interleaveEquiv (n : ℕ) : (Path V n × Path V n) ≃ Path V (doubleLength n) where
  toFun := fun p => interleave p.1 p.2
  invFun := fun p => (sampleOdd p, sampleEven p)
  left_inv := by intro p; simp [sampleOdd_interleave, sampleEven_interleave]
  right_inv := interleave_samples

/-- The identical equivalence with the conventional actual length `2*n`. -/
def interleaveTwoMulEquiv (n : ℕ) : (Path V n × Path V n) ≃ Path V (2 * n) :=
  (interleaveEquiv n).trans (Equiv.cast (congrArg (Path V) (doubleLength_eq_two_mul n)))

/-- Actual future states at times 2,4,...,2*n; the initial state is retained separately. -/
def sampleEvenTwoMul (n : ℕ) (p : Path V (2 * n)) : Path V n :=
  ((interleaveTwoMulEquiv n).symm p).2

theorem sampleEvenTwoMul_interleave (n : ℕ) (p q : Path V n) :
    sampleEvenTwoMul n (interleaveTwoMulEquiv n (p, q)) = q := by
  simp [sampleEvenTwoMul]

namespace Chain
variable [Fintype V] [DecidableEq V] (C : Chain V)

/-- Genuine two-step kernel, with stochastic properties proved from the original chain. -/
noncomputable def twoStep : Chain V where
  transition := C.transition ^ 2
  nonneg := by
    intro x y
    rw [pow_two, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (C.nonneg x z) (C.nonneg z y)
  row_sum := by
    intro x
    simp only [pow_two, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, C.row_sum, mul_one]
    exact C.row_sum x

omit [DecidableEq V] in
/-- Changing only the dependent length index leaves the actual path weight unchanged. -/
theorem weight_cast {a b : ℕ} (h : a = b) (x : V) (p : Path V a) :
    C.weight x (cast (congrArg (Path V) h) p) = C.weight x p := by
  cases h
  rfl

/-- Exact aggregation over all omitted intermediate vertices for each retained path. -/
theorem interleave_weight_sum (n : ℕ) (x : V) (q : Path V n) :
    (∑ p : Path V n, C.weight x (interleave p q)) = (C.twoStep).weight x q := by
  induction n generalizing x with
  | zero =>
    rw [Fintype.sum_unique]
    rfl
  | succ n ih =>
    change (∑ p : V × Path V n,
      C.transition x p.1 * (C.transition p.1 q.1 * C.weight q.1 (interleave p.2 q.2))) =
      (C.transition ^ 2) x q.1 * (C.twoStep).weight q.1 q.2
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_assoc, ← Finset.mul_sum, ih]
    rw [← Finset.sum_mul, pow_two, Matrix.mul_apply]

omit [DecidableEq V] in
theorem interleaveTwoMul_weight (n : ℕ) (x : V) (p q : Path V n) :
    C.weight x (interleaveTwoMulEquiv n (p, q)) = C.weight x (interleave p q) := by
  exact C.weight_cast (doubleLength_eq_two_mul n) x (interleave p q)

/-- Exact even-position sampled law for every real test function of the retained path. -/
theorem even_sample_expectation (n : ℕ) (x : V) (F : Path V n → ℝ) :
    (∑ p : Path V (2 * n), C.weight x p * F (sampleEvenTwoMul n p)) =
      ∑ q : Path V n, (C.twoStep).weight x q * F q := by
  calc
    _ = ∑ pq : Path V n × Path V n,
        C.weight x (interleaveTwoMulEquiv n pq) *
          F (sampleEvenTwoMul n (interleaveTwoMulEquiv n pq)) :=
      ((interleaveTwoMulEquiv n).sum_comp _).symm
    _ = ∑ pq : Path V n × Path V n, C.weight x (interleave pq.1 pq.2) * F pq.2 := by
      apply Finset.sum_congr rfl
      intro pq _
      rw [C.interleaveTwoMul_weight, sampleEvenTwoMul_interleave]
    _ = ∑ q : Path V n, (C.twoStep).weight x q * F q := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      change (∑ p : Path V n, C.weight x (interleave p q) * F q) = _
      rw [← Finset.sum_mul, C.interleave_weight_sum]

/-- Exact actual event probabilities for even sampling, with the same initial vertex. -/
theorem even_sample_eventMass (n : ℕ) (E : V → Path V n → Prop) (x : V) :
    C.eventMass (2 * n) (fun x p => E x (sampleEvenTwoMul n p)) x =
      (C.twoStep).eventMass n E x := by
  classical
  have h := C.even_sample_expectation n x (fun p => if E x p then 1 else 0)
  simpa only [eventMass, mul_ite, mul_one, mul_zero] using h

end Chain
end Erdos642.FiniteMarkov
