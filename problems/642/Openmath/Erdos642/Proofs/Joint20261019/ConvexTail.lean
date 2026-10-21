import Openmath.Erdos642.Proofs.Joint20261019.ConvexTailMatrix
import Openmath.Erdos642.Proofs.Joint20261019.ConvexTailEmpirical
import Openmath.Erdos642.Proofs.Joint20261019.EnergySupport
import Openmath.Erdos642.Proofs.Joint20261019.EnergyLimit

namespace Erdos642.Joint20261019.ConvexTail
open Matrix Erdos642.FiniteMarkov
open scoped Topology
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (C : Chain V)

theorem log_ratio_moment (u v : V → ℝ) (hu : ∀ x,0<u x)
    (hun : (∑ x,u x^2)=1) (hA : (C.similarTransition u).IsHermitian)
    (hpos : ∀ f,0≤dotProduct f (C.similarTransition u *ᵥ f))
    (hv : ∀ x,0<v x) (n : ℕ) (x : V) :
    (∑ p : Path V n, C.weight x p *
      Real.exp (Chain.vertexSum (fun y=>Real.log (v y/(C.transition *ᵥ v) y)) x p)) ≤ 1/(u x)^2 := by
  have hh := ConvexTailMatrix.stationary_log_ratio_moment C u v hu hun hA hpos hv n
  have hx : u x^2*(∑ p : Path V n, C.weight x p *
      Real.exp (Chain.vertexSum (fun y=>Real.log (v y/(C.transition *ᵥ v) y)) x p)) ≤ 1 := by
    apply le_trans ?_ hh
    exact Finset.single_le_sum (fun y _ => mul_nonneg (sq_nonneg (u y))
      (Finset.sum_nonneg (fun p _ => mul_nonneg (C.weight_nonneg y p) (Real.exp_nonneg _))))
      (Finset.mem_univ x)
  apply (le_div_iff₀ (sq_pos_of_pos (hu x))).mpr
  simpa only [mul_comm] using hx

theorem event_tail_from_log_moment (g : V → ℝ) (n : ℕ) (x : V)
    (E : V → Path V n → Prop) (b M : ℝ)
    (hsupport : ∀ y p,E y p → b ≤ Chain.vertexSum g y p)
    (hmoment : (∑ p : Path V n,C.weight x p*Real.exp (Chain.vertexSum g x p)) ≤ M) :
    C.eventMass n E x ≤ Real.exp (-b)*M := by
  classical
  apply le_trans ?_ (mul_le_mul_of_nonneg_left hmoment (Real.exp_nonneg _))
  unfold Chain.eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : E x p
  · rw [if_pos hp]
    have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hsupport x p hp))
      (C.weight_nonneg x p)
    have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (-b))
    have he : Real.exp (-b)*(C.weight x p*Real.exp b)=C.weight x p := by
      rw [mul_left_comm,← Real.exp_add]
      simp
    rw [he] at hh'
    exact hh'
  · rw [if_neg hp]
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (C.weight_nonneg x p) (Real.exp_nonneg _))

/-- Finite-time convex occupation bound on the actual ordinary path law. -/
theorem convex_occupation_tail (u : V → ℝ) (hu : ∀ x,0<u x)
    (hun : (∑ x,u x^2)=1) (hA : (C.similarTransition u).IsHermitian)
    (hpos : ∀ f,0≤dotProduct f (C.similarTransition u *ᵥ f))
    (K : Set (V → ℝ)) (hK : IsCompact K) (hc : Convex ℝ K)
    (hsimplex : K ⊆ stdSimplex ℝ V) (b : ℝ)
    (henergy : ∀ q ∈ K,b≤Energy.energy (C.similarTransition u) q)
    (n : ℕ) (hn : 1≤n) (x : V) :
    C.eventMass (n-1) (fun y p=>empirical y p ∈ K) x ≤
      1/(u x)^2*Real.exp (-b*(n:ℝ)) := by
  classical
  by_cases hne : K.Nonempty
  · have hall : ∀ δ : ℝ,0<δ →
        C.eventMass (n-1) (fun y p=>empirical y p ∈ K) x ≤
          1/(u x)^2*Real.exp (-(b-δ)*(n:ℝ)) := by
      intro δ hδ
      obtain ⟨ε,hε,hreg⟩ := Energy.exists_small_regularization (C.similarTransition u)
        (fun x=>u x^2) K hK δ hδ
      have hsym : ∀ x y,C.similarTransition u x y=C.similarTransition u y x := by
        intro x y
        simpa only [star_trivial] using hA.apply y x
      obtain ⟨q,hq,v,hv,hmin,hsupp⟩ := Energy.exists_supporting_potential C u hu hun hsym
        K hK hne hc hsimplex ε hε
      have hbase : b-δ≤Energy.energy (C.similarTransition u) (fun x=>q x+ε*u x^2)-ε := by
        exact (sub_le_sub_right (henergy q hq) δ).trans (hreg q hq)
      have hsupp' : ∀ y (p : Path V (n-1)),empirical y p ∈ K →
          (b-δ)*(n:ℝ) ≤ Chain.vertexSum (fun z=>Real.log (v z/(C.transition *ᵥ v) z)) y p := by
        intro y p hp
        have hh := mul_le_mul_of_nonneg_left (hbase.trans (hsupp _ hp)) (Nat.cast_nonneg n : (0:ℝ)≤n)
        rw [empirical_dot_observations n hn] at hh
        simpa only [mul_comm] using hh
      have ht := event_tail_from_log_moment C (fun z=>Real.log (v z/(C.transition *ᵥ v) z))
        (n-1) x (fun y p=>empirical y p ∈ K) ((b-δ)*(n:ℝ)) (1/(u x)^2) hsupp'
        (log_ratio_moment C u v hu hun hA hpos hv (n-1) x)
      simpa only [neg_mul,mul_neg,mul_comm] using ht
    by_contra hbad
    have hlt : 1/(u x)^2*Real.exp (-b*(n:ℝ)) <
        C.eventMass (n-1) (fun y p=>empirical y p ∈ K) x := lt_of_not_ge hbad
    have hcont : Continuous (fun δ : ℝ=>1/(u x)^2*Real.exp (-(b-δ)*(n:ℝ))) := by fun_prop
    have hev := (hcont.continuousAt (x := (0:ℝ))).eventually_lt_const (by simpa using hlt)
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hev
    have hm : r/2 ∈ Metric.ball (0:ℝ) r := by
      simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)]
      linarith
    exact (not_lt_of_ge (hall (r/2) (half_pos hr))) (hball hm)
  · have he : K=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Set.mem_empty_iff_false,Chain.eventMass,if_false,Finset.sum_const_zero]
    positivity

end Erdos642.Joint20261019.ConvexTail
