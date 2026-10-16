import Openmath.Erdos642.Proofs.CampaignFe72210b.OccupationTail
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents

/-! Bounded coboundary exponential moments for the genuine finite Markov path law. -/
namespace Erdos642.PoissonTilt
open Erdos642.FiniteMarkov
variable {V : Type*} [Fintype V]

def average (C : Chain V) (f : V → ℝ) (x : V) : ℝ :=
  ∑ y, C.transition x y * f y

def coboundary (C : Chain V) (u : V → ℝ) (x : V) : ℝ := u x - average C u x

theorem average_nonneg (C : Chain V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (x : V) :
    0 ≤ average C f x := Finset.sum_nonneg fun y _ => mul_nonneg (C.nonneg x y) (hf y)

theorem average_test (C : Chain V) (u : V → ℝ) (theta : ℝ) (x : V) :
    average C (fun y => 1 + theta * u y) x = 1 + theta * average C u x := by
  simp only [average, mul_add, mul_one, Finset.sum_add_distrib, C.row_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring_nf

/-- The scalar estimate holds for negative as well as positive coboundaries. -/
theorem scalar_test (u h r theta : ℝ) (hu : 0 ≤ u) (hur : u ≤ r)
    (hh : h ≤ 1) (hθ : 0 ≤ theta) :
    Real.exp (theta * h) * (1 - theta * h / (1 + theta * u)) ≤ Real.exp (theta^2 * r) := by
  have hr : 0 ≤ r := hu.trans hur
  have hm : 0 < 1 + theta * u := by positivity
  have hm1 : 1 ≤ 1 + theta * u := by nlinarith [mul_nonneg hθ hu]
  have hhu : h * u ≤ r * (1 + theta * u) := by
    calc
      h * u ≤ u := by nlinarith
      _ ≤ r := hur
      _ ≤ _ := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hhu (sq_nonneg theta)
  have he : theta * h - theta * h / (1 + theta * u) ≤ theta^2 * r := by
    calc
      _ = (theta^2 * (h * u)) / (1 + theta * u) := by field_simp [ne_of_gt hm]; ring_nf
      _ ≤ _ := (div_le_iff₀ hm).mpr (by nlinarith)
  have hlinear : 1 - theta * h / (1 + theta * u) ≤
      Real.exp (-(theta * h / (1 + theta * u))) := by
    have hh := Real.add_one_le_exp (-(theta * h / (1 + theta * u)))
    linarith
  calc
    _ ≤ Real.exp (theta * h) * Real.exp (-(theta * h / (1 + theta * u))) :=
      mul_le_mul_of_nonneg_left hlinear (Real.exp_pos _).le
    _ = Real.exp (theta * h - theta * h / (1 + theta * u)) := by rw [← Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr he

/-- The actual positive test function is a supersolution of the departure-state tilt. -/
theorem coboundary_test (C : Chain V) (u : V → ℝ) (r theta : ℝ)
    (hu : ∀ x, 0 ≤ u x) (hur : ∀ x, u x ≤ r)
    (hh : ∀ x, coboundary C u x ≤ 1) (hθ : 0 ≤ theta) (x : V) :
    Real.exp (theta * coboundary C u x) * average C (fun y => 1 + theta * u y) x ≤
      Real.exp (theta^2 * r) * (1 + theta * u x) := by
  have hm : 0 < 1 + theta * u x := by nlinarith [mul_nonneg hθ (hu x)]
  have hs := mul_le_mul_of_nonneg_right (scalar_test (u x) (coboundary C u x) r theta
    (hu x) (hur x) (hh x) hθ) hm.le
  calc
    _ = (Real.exp (theta * coboundary C u x) *
        (1 - theta * coboundary C u x / (1 + theta * u x))) * (1 + theta * u x) := by
      rw [average_test]
      unfold coboundary
      field_simp [ne_of_gt hm]
      ring_nf
    _ ≤ _ := hs

/-- Genuine finite-path moment, n transitions and exactly n+1 observations. -/
theorem coboundary_moment_test (C : Chain V) (u : V → ℝ) (r theta : ℝ)
    (hu : ∀ x, 0 ≤ u x) (hur : ∀ x, u x ≤ r)
    (hh : ∀ x, coboundary C u x ≤ 1) (hθ : 0 ≤ theta) (n : ℕ) (x : V) :
    (∑ p : Path V n, C.weight x p * Real.exp (theta * Chain.vertexSum (coboundary C u) x p)) ≤
      Real.exp (((n + 1 : ℕ) : ℝ) * theta^2 * r) * (1 + theta * u x) := by
  induction n generalizing x with
  | zero =>
    rw [Fintype.sum_unique]
    norm_num only [Chain.weight, Chain.vertexSum, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_mul]
    have htest := coboundary_test C u r theta hu hur hh hθ x
    have havg : 1 ≤ average C (fun y => 1 + theta * u y) x := by
      rw [average_test]
      have hp := average_nonneg C u hu x
      nlinarith [mul_nonneg hθ hp]
    exact (le_mul_of_one_le_right (Real.exp_pos _).le havg).trans htest
  | succ n ih =>
    change (∑ p : V × Path V n, (C.transition x p.1 * C.weight p.1 p.2) *
      Real.exp (theta * (coboundary C u x + Chain.vertexSum (coboundary C u) p.1 p.2))) ≤ _
    rw [Fintype.sum_prod_type]
    have heq : (∑ y, ∑ p : Path V n, (C.transition x y * C.weight y p) *
        Real.exp (theta * (coboundary C u x + Chain.vertexSum (coboundary C u) y p))) =
        Real.exp (theta * coboundary C u x) * ∑ y, C.transition x y *
          ∑ p : Path V n, C.weight y p * Real.exp (theta * Chain.vertexSum (coboundary C u) y p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_add, Real.exp_add]
      ring_nf
    rw [heq]
    calc
      _ ≤ Real.exp (theta * coboundary C u x) * ∑ y, C.transition x y *
          (Real.exp (((n + 1 : ℕ) : ℝ) * theta^2 * r) * (1 + theta * u y)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y) (C.nonneg x y)
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * theta^2 * r) *
          (Real.exp (theta * coboundary C u x) * average C (fun y => 1 + theta * u y) x) := by
        unfold average
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring_nf
      _ ≤ Real.exp (((n + 1 : ℕ) : ℝ) * theta^2 * r) *
          (Real.exp (theta^2 * r) * (1 + theta * u x)) :=
        mul_le_mul_of_nonneg_left (coboundary_test C u r theta hu hur hh hθ x) (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 1; push_cast; ring_nf

/-- The same actual moment, stated for n observations on n-1 transitions. -/
theorem coboundary_moment (C : Chain V) (u : V → ℝ) (r theta : ℝ)
    (hu : ∀ x, 0 ≤ u x) (hur : ∀ x, u x ≤ r)
    (hh : ∀ x, coboundary C u x ≤ 1) (hθ : 0 ≤ theta)
    (n : ℕ) (hn : 1 ≤ n) (x : V) :
    (∑ p : Path V (n - 1), C.weight x p * Real.exp (theta * Chain.vertexSum (coboundary C u) x p)) ≤
      (1 + theta * r) * Real.exp ((n : ℝ) * theta^2 * r) := by
  have hh' := coboundary_moment_test C u r theta hu hur hh hθ (n - 1) x
  have he : n - 1 + 1 = n := by omega
  rw [he] at hh'
  apply hh'.trans
  calc
    _ ≤ Real.exp ((n : ℝ) * theta^2 * r) * (1 + theta * r) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left (hur x) hθ])
        (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- Upper tail for the actual n-observation coboundary sum, from every initial state. -/
theorem coboundary_upper_tail (C : Chain V) (u : V → ℝ) (r epsilon : ℝ)
    (hr : 0 < r) (hε : 0 < epsilon) (hu : ∀ x, 0 ≤ u x) (hur : ∀ x, u x ≤ r)
    (hh : ∀ x, coboundary C u x ≤ 1) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1) (fun y p => epsilon * (n : ℝ) ≤ Chain.vertexSum (coboundary C u) y p) x ≤
      (1 + epsilon / 2) * Real.exp (-epsilon^2 * (n : ℝ) / (4 * r)) := by
  classical
  let theta := epsilon / (2 * r)
  have hθ : 0 ≤ theta := by dsimp [theta]; positivity
  have hmark := Erdos642.OccupationTail.finite_exponential_markov
    (C.weight (n := n - 1) x) (fun p => -Chain.vertexSum (coboundary C u) x p)
    (C.weight_nonneg x) theta (-(epsilon * (n : ℝ))) hθ
  have hmark' : C.eventMass (n - 1)
      (fun y p => epsilon * (n : ℝ) ≤ Chain.vertexSum (coboundary C u) y p) x ≤
      Real.exp (-theta * epsilon * (n : ℝ)) *
        ∑ p : Path V (n - 1), C.weight x p * Real.exp (theta * Chain.vertexSum (coboundary C u) x p) := by
    simpa only [Chain.eventMass, neg_le_neg_iff, mul_neg, neg_neg, neg_mul, mul_assoc] using hmark
  have hmoment := coboundary_moment C u r theta hu hur hh hθ n hn x
  have hpref : theta * r = epsilon / 2 := by dsimp [theta]; field_simp [ne_of_gt hr]
  have hexp : -theta * epsilon * (n : ℝ) + (n : ℝ) * theta^2 * r =
      -epsilon^2 * (n : ℝ) / (4 * r) := by dsimp [theta]; field_simp [ne_of_gt hr]; ring_nf
  calc
    _ ≤ Real.exp (-theta * epsilon * (n : ℝ)) *
        ((1 + theta * r) * Real.exp ((n : ℝ) * theta^2 * r)) :=
      hmark'.trans (mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le)
    _ = (1 + theta * r) * Real.exp (-theta * epsilon * (n : ℝ) + (n : ℝ) * theta^2 * r) := by
      rw [Real.exp_add]; ring_nf
    _ = _ := by rw [hpref, hexp]

theorem average_const_sub (C : Chain V) (r : ℝ) (u : V → ℝ) (x : V) :
    average C (fun y => r - u y) x = r - average C u x := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, C.row_sum, one_mul]

theorem coboundary_const_sub (C : Chain V) (r : ℝ) (u : V → ℝ) :
    coboundary C (fun y => r - u y) = fun y => -coboundary C u y := by
  funext x
  rw [coboundary, average_const_sub]
  unfold coboundary
  ring_nf

omit [Fintype V] in
theorem vertexSum_neg (f : V → ℝ) {n : ℕ} (x : V) (p : Path V n) :
    Chain.vertexSum (fun y => -f y) x p = -Chain.vertexSum f x p := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change -f x + Chain.vertexSum (fun y => -f y) p.1 p.2 = -(f x + Chain.vertexSum f p.1 p.2)
    rw [ih]
    ring_nf

/-- Lower tail is the upper tail of the complementary actual bounded potential. -/
theorem coboundary_lower_tail (C : Chain V) (u : V → ℝ) (r epsilon : ℝ)
    (hr : 0 < r) (hε : 0 < epsilon) (hu : ∀ x, 0 ≤ u x) (hur : ∀ x, u x ≤ r)
    (hh : ∀ x, -1 ≤ coboundary C u x) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1) (fun y p => Chain.vertexSum (coboundary C u) y p ≤ -epsilon * (n : ℝ)) x ≤
      (1 + epsilon / 2) * Real.exp (-epsilon^2 * (n : ℝ) / (4 * r)) := by
  have htail := coboundary_upper_tail C (fun y => r - u y) r epsilon hr hε
    (fun y => sub_nonneg.mpr (hur y)) (fun y => by linarith [hu y])
    (fun y => by rw [coboundary_const_sub]; linarith [hh y]) n hn x
  have he : C.eventMass (n - 1)
      (fun y p => epsilon * (n : ℝ) ≤ Chain.vertexSum (coboundary C (fun y => r - u y)) y p) x =
      C.eventMass (n - 1)
        (fun y p => Chain.vertexSum (coboundary C u) y p ≤ -epsilon * (n : ℝ)) x := by
    classical
    unfold Chain.eventMass
    apply Finset.sum_congr rfl
    intro p _
    dsimp only
    simp only [coboundary_const_sub, vertexSum_neg]
    have hp : (epsilon * (n : ℝ) ≤ -Chain.vertexSum (coboundary C u) x p) ↔
        Chain.vertexSum (coboundary C u) x p ≤ -epsilon * (n : ℝ) := by constructor <;> intro h <;> linarith
    simp only [hp]
  rw [he] at htail
  exact htail

/-- Two-sided actual bounded-potential tail; no independence is used. -/
theorem coboundary_two_sided_tail (C : Chain V) (u : V → ℝ) (r epsilon : ℝ)
    (hr : 0 < r) (hε : 0 < epsilon) (hu : ∀ x, 0 ≤ u x) (hur : ∀ x, u x ≤ r)
    (hh : ∀ x, coboundary C u x ≤ 1) (hhneg : ∀ x, -1 ≤ coboundary C u x)
    (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1) (fun y p => epsilon * (n : ℝ) ≤
      |Chain.vertexSum (coboundary C u) y p|) x ≤
      (2 + epsilon) * Real.exp (-epsilon^2 * (n : ℝ) / (4 * r)) := by
  have hmono := C.eventMass_mono (n := n - 1)
    (fun y p => epsilon * (n : ℝ) ≤ |Chain.vertexSum (coboundary C u) y p|)
    (fun y p => epsilon * (n : ℝ) ≤ Chain.vertexSum (coboundary C u) y p ∨
      Chain.vertexSum (coboundary C u) y p ≤ -epsilon * (n : ℝ)) (by
      intro y p hp
      by_cases hs : 0 ≤ Chain.vertexSum (coboundary C u) y p
      · rw [abs_of_nonneg hs] at hp
        exact Or.inl hp
      · rw [abs_of_neg (lt_of_not_ge hs)] at hp
        exact Or.inr (by linarith)) x
  have hunion := C.eventMass_union_le (n := n - 1)
    (fun y p => epsilon * (n : ℝ) ≤ Chain.vertexSum (coboundary C u) y p)
    (fun y p => Chain.vertexSum (coboundary C u) y p ≤ -epsilon * (n : ℝ)) x
  have hupp := coboundary_upper_tail C u r epsilon hr hε hu hur hh n hn x
  have hlow := coboundary_lower_tail C u r epsilon hr hε hu hur hhneg n hn x
  linarith

theorem average_add (C : Chain V) (f g : V → ℝ) (x : V) :
    average C (fun y => f y + g y) x = average C f x + average C g x := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_le_one (C : Chain V) (f : V → ℝ) (hf : ∀ x, f x ≤ 1) (x : V) :
    average C f x ≤ 1 := by
  calc
    _ ≤ ∑ y, C.transition x y * 1 :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf y) (C.nonneg x y)
    _ = 1 := by simp only [mul_one, C.row_sum]

variable [DecidableEq V]
open Matrix

/-- Genuine r-step smoothing by the actual stochastic matrix. -/
noncomputable def smooth (C : Chain V) (r : ℕ) (f : V → ℝ) : V → ℝ :=
  (C.transition^r) *ᵥ f

theorem smooth_zero (C : Chain V) (f : V → ℝ) : smooth C 0 f = f := by
  simp [smooth]

theorem smooth_succ (C : Chain V) (r : ℕ) (f : V → ℝ) (x : V) :
    smooth C (r + 1) f x = average C (smooth C r f) x := by
  unfold smooth
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

theorem smooth_bounds (C : Chain V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (r : ℕ) (x : V) :
    0 ≤ smooth C r f x ∧ smooth C r f x ≤ 1 := by
  induction r generalizing x with
  | zero => simpa only [smooth_zero] using And.intro (hf x) (hf1 x)
  | succ r ih =>
    rw [smooth_succ]
    exact ⟨average_nonneg C _ (fun y => (ih y).1) x,
      average_le_one C _ (fun y => (ih y).2) x⟩

/-- The literal finite Poisson potential; no inverse or gap is assumed. -/
noncomputable def potential (C : Chain V) (r : ℕ) (f : V → ℝ) (x : V) : ℝ :=
  ∑ j ∈ Finset.range r, smooth C j f x

theorem potential_bounds (C : Chain V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (r : ℕ) (x : V) :
    0 ≤ potential C r f x ∧ potential C r f x ≤ (r : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun j _ => (smooth_bounds C f hf hf1 j x).1
  · calc
      _ ≤ ∑ _j ∈ Finset.range r, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => (smooth_bounds C f hf hf1 j x).2
      _ = _ := by simp

theorem potential_succ (C : Chain V) (r : ℕ) (f : V → ℝ) :
    potential C (r + 1) f = fun x => potential C r f x + smooth C r f x := by
  funext x
  exact Finset.sum_range_succ _ r

/-- Exact actual-matrix telescoping, u-Pu = f-P^r f. -/
theorem potential_coboundary (C : Chain V) (r : ℕ) (f : V → ℝ) :
    coboundary C (potential C r f) = fun x => f x - smooth C r f x := by
  induction r with
  | zero =>
    funext x
    simp [potential, coboundary, average, smooth_zero]
  | succ r ih =>
    funext x
    rw [potential_succ]
    change potential C r f x + smooth C r f x -
      average C (fun y => potential C r f y + smooth C r f y) x = _
    rw [average_add, smooth_succ]
    have hh := congrFun ih x
    unfold coboundary at hh
    linarith

/-- Actual fixed-start moment for the empirical difference f-P^r f. -/
theorem smoothing_moment (C : Chain V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (r : ℕ)
    (theta : ℝ) (hθ : 0 ≤ theta) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    (∑ p : Path V (n - 1), C.weight x p *
      Real.exp (theta * Chain.vertexSum (fun y => f y - smooth C r f y) x p)) ≤
      (1 + theta * (r : ℝ)) * Real.exp ((n : ℝ) * theta^2 * (r : ℝ)) := by
  have hh := coboundary_moment C (potential C r f) (r : ℝ) theta
    (fun y => (potential_bounds C f hf hf1 r y).1)
    (fun y => (potential_bounds C f hf hf1 r y).2)
    (fun y => by
      rw [potential_coboundary]
      have hs := (smooth_bounds C f hf hf1 r y).1
      linarith [hf1 y]) hθ n hn x
  simpa only [potential_coboundary] using hh

/-- The accepted two-sided smoothing bound, for the genuine n-observation path law. -/
theorem smoothing_two_sided_tail (C : Chain V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (r : ℕ) (hr : 1 ≤ r)
    (epsilon : ℝ) (hε : 0 < epsilon) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1) (fun y p => epsilon * (n : ℝ) ≤
      |Chain.vertexSum (fun z => f z - smooth C r f z) y p|) x ≤
      (2 + epsilon) * Real.exp (-epsilon^2 * (n : ℝ) / (4 * (r : ℝ))) := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hh := coboundary_two_sided_tail C (potential C r f) (r : ℝ) epsilon hr' hε
    (fun y => (potential_bounds C f hf hf1 r y).1)
    (fun y => (potential_bounds C f hf hf1 r y).2)
    (fun y => by rw [potential_coboundary]; linarith [(smooth_bounds C f hf hf1 r y).1, hf1 y])
    (fun y => by rw [potential_coboundary]; linarith [(smooth_bounds C f hf hf1 r y).2, hf y]) n hn x
  simpa only [potential_coboundary] using hh

/-- Actual fixed-start upper tail for f-P^r f, with no reversibility or gap premise. -/
theorem smoothing_upper_tail (C : Chain V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (r : ℕ) (hr : 1 ≤ r)
    (epsilon : ℝ) (hε : 0 < epsilon) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1) (fun y p => epsilon * (n : ℝ) ≤
      Chain.vertexSum (fun z => f z - smooth C r f z) y p) x ≤
      (1 + epsilon / 2) * Real.exp (-epsilon^2 * (n : ℝ) / (4 * (r : ℝ))) := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hh := coboundary_upper_tail C (potential C r f) (r : ℝ) epsilon hr' hε
    (fun y => (potential_bounds C f hf hf1 r y).1)
    (fun y => (potential_bounds C f hf hf1 r y).2)
    (fun y => by rw [potential_coboundary]; linarith [(smooth_bounds C f hf hf1 r y).1, hf1 y]) n hn x
  simpa only [potential_coboundary] using hh

/-- Actual fixed-start lower tail for f-P^r f. -/
theorem smoothing_lower_tail (C : Chain V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (r : ℕ) (hr : 1 ≤ r)
    (epsilon : ℝ) (hε : 0 < epsilon) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1) (fun y p =>
      Chain.vertexSum (fun z => f z - smooth C r f z) y p ≤ -epsilon * (n : ℝ)) x ≤
      (1 + epsilon / 2) * Real.exp (-epsilon^2 * (n : ℝ) / (4 * (r : ℝ))) := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hh := coboundary_lower_tail C (potential C r f) (r : ℝ) epsilon hr' hε
    (fun y => (potential_bounds C f hf hf1 r y).1)
    (fun y => (potential_bounds C f hf hf1 r y).2)
    (fun y => by rw [potential_coboundary]; linarith [(smooth_bounds C f hf hf1 r y).2, hf y]) n hn x
  simpa only [potential_coboundary] using hh

end Erdos642.PoissonTilt
