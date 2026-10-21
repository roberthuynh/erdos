import Openmath.Erdos642.Proofs.CampaignFe72210b.PathMoment

namespace Erdos642.Joint20261019.ConvexTail
open Erdos642.FiniteMarkov
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Probability vector of all n+1 observations on an actual n-transition path. -/
noncomputable def empirical {n : ℕ} (x : V) (p : Path V n) : V → ℝ :=
  fun y => Chain.vertexSum (fun z => if z=y then (1:ℝ) else 0) x p / ((n+1:ℕ):ℝ)

theorem coordinate_sum {n : ℕ} (x : V) (p : Path V n) (f : V → ℝ) :
    (∑ y, Chain.vertexSum (fun z=>if z=y then (1:ℝ) else 0) x p * f y) =
      Chain.vertexSum f x p := by
  induction n generalizing x with
  | zero => simp [Chain.vertexSum]
  | succ n ih =>
    change (∑ y, ((if x=y then (1:ℝ) else 0)+
      Chain.vertexSum (fun z=>if z=y then (1:ℝ) else 0) p.1 p.2)*f y) =
      f x+Chain.vertexSum f p.1 p.2
    simp only [add_mul,Finset.sum_add_distrib]
    rw [ih]
    simp

theorem empirical_dot {n : ℕ} (x : V) (p : Path V n) (f : V → ℝ) :
    (∑ y, empirical x p y*f y) = Chain.vertexSum f x p/((n+1:ℕ):ℝ) := by
  simp only [empirical,div_mul_eq_mul_div,← Finset.sum_div]
  rw [coordinate_sum]

theorem vertexSum_const_one {n : ℕ} (x : V) (p : Path V n) :
    Chain.vertexSum (fun _ : V=>(1:ℝ)) x p=((n+1:ℕ):ℝ) := by
  induction n generalizing x with
  | zero => simp [Chain.vertexSum]
  | succ n ih =>
    change 1+Chain.vertexSum (fun _ : V=>(1:ℝ)) p.1 p.2 = _
    rw [ih]
    push_cast
    ring

theorem empirical_nonneg {n : ℕ} (x : V) (p : Path V n) (y : V) :
    0≤empirical x p y := by
  have hc : 0≤Chain.vertexSum (fun z=>if z=y then (1:ℝ) else 0) x p := by
    induction n generalizing x with
    | zero => simp only [Chain.vertexSum]; split_ifs <;> norm_num
    | succ n ih =>
      change 0≤(if x=y then (1:ℝ) else 0)+Chain.vertexSum _ p.1 p.2
      exact add_nonneg (by split_ifs <;> norm_num) (ih p.1 p.2)
  exact div_nonneg hc (Nat.cast_nonneg _)

theorem empirical_mem_simplex {n : ℕ} (x : V) (p : Path V n) :
    empirical x p ∈ stdSimplex ℝ V := by
  refine ⟨empirical_nonneg x p,?_⟩
  have hh := empirical_dot x p (fun _=>(1:ℝ))
  rw [vertexSum_const_one] at hh
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  simpa only [mul_one,div_self hn] using hh

theorem empirical_dot_observations (n : ℕ) (hn : 1≤n)
    (x : V) (p : Path V (n-1)) (f : V → ℝ) :
    (n:ℝ)*(∑ y,empirical x p y*f y)=Chain.vertexSum f x p := by
  rw [empirical_dot,Nat.sub_add_cancel hn]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  field_simp

end Erdos642.Joint20261019.ConvexTail
