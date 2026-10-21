import Openmath.Erdos642.Proofs.Joint20261019.SphereNet
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSmoothing
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Normalize

namespace Erdos642.Joint20261019.JointFamilyGeometry
open scoped BigOperators
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def root (q : V→ℝ) : EuclideanSpace ℝ V := WithLp.toLp 2 (fun x=>Real.sqrt (q x))
noncomputable def squares (h : EuclideanSpace ℝ V) : V→ℝ := fun x=>h x^2
noncomputable def l1 (p q : V→ℝ) : ℝ := ∑x,|p x-q x|
noncomputable def mass (p : V→ℝ) (S : Finset V) : ℝ := ∑x∈S,p x
noncomputable def excessSet (p q : V→ℝ) : Finset V := univ.filter (fun x=>q x<p x)

theorem squares_root (q : V→ℝ) (hq : q∈stdSimplex ℝ V) : squares (root q)=q := by
  funext x
  exact Real.sq_sqrt (hq.1 x)

theorem norm_root (q : V→ℝ) (hq : q∈stdSimplex ℝ V) : ‖root q‖=1 := by
  have hh : ‖root q‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑x,(Real.sqrt (q x))^2)=1
    simpa only [Real.sq_sqrt (hq.1 _)] using hq.2
  nlinarith [norm_nonneg (root q)]

theorem squares_simplex (h : EuclideanSpace ℝ V) (hh : ‖h‖=1) : squares h∈stdSimplex ℝ V := by
  refine ⟨fun x=>sq_nonneg _,?_⟩
  change (∑x,h x^2)=1
  rw [←EuclideanSpace.real_norm_sq_eq,hh]
  norm_num

                                                                             
theorem l1_squares (h w : EuclideanSpace ℝ V) (hh : ‖h‖=1) (hw : ‖w‖=1) :
    l1 (squares h) (squares w) ≤ 2*‖h-w‖ := by
  have he : l1 (squares h) (squares w) = ∑x, |(h-w) x| * |(h+w) x| := by
    unfold l1 squares
    apply sum_congr rfl
    intro x _
    rw [←abs_mul]
    congr 1
    change h x^2-w x^2=(h x-w x)*(h x+w x)
    ring
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset V)
    (fun x=>|(h-w) x|) (fun x=>|(h+w) x|)
  simp only [sq_abs] at hc
  rw [←EuclideanSpace.real_norm_sq_eq,←EuclideanSpace.real_norm_sq_eq,
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)] at hc
  have hsum : ‖h+w‖≤2 := by calc
    _ ≤ ‖h‖+‖w‖ := norm_add_le _ _
    _ = 2 := by rw [hh,hw]; norm_num
  rw [he]
  exact hc.trans (by nlinarith [norm_nonneg (h-w)])

theorem mass_diff_le_l1 (p q : V→ℝ) (S : Finset V) :
    |mass p S-mass q S|≤l1 p q := by
  unfold mass l1
  rw [←sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_univ_sum_of_nonneg fun x=>abs_nonneg (p x-q x))

theorem mean_diff_le_excess (p q f : V→ℝ) (hf : ∀x,0≤f x ∧ f x≤1) :
    (∑x,p x*f x)-(∑x,q x*f x) ≤ mass p (excessSet p q)-mass q (excessSet p q) := by
  rw [←sum_sub_distrib]
  unfold mass excessSet
  rw [←sum_sub_distrib, sum_filter]
  apply sum_le_sum
  intro x _
  split_ifs with hx
  · nlinarith [(hf x).2]
  · have hn : p x≤q x := le_of_not_gt hx
    nlinarith [(hf x).1]

theorem mass_diff_le_excess (p q : V→ℝ) (S : Finset V) :
    mass p S-mass q S ≤ mass p (excessSet p q)-mass q (excessSet p q) := by
  have hh := mean_diff_le_excess p q (fun x=>if x∈S then 1 else 0) (by intro x; split_ifs <;> norm_num)
  simpa [mass,←sum_filter] using hh

                                                                                    
theorem twice_mass_diff_le_l1 (p q : V→ℝ) (heq : (∑x,p x)=(∑x,q x)) (S : Finset V) :
    2*(mass p S-mass q S)≤l1 p q := by
  have hzero : ∑x,(p x-q x)=0 := by rw [sum_sub_distrib,heq]; ring
  have hpoint (x : V) : 2*(if x∈S then p x-q x else 0) ≤ |p x-q x|+(p x-q x) := by
    split_ifs
    · linarith [le_abs_self (p x-q x)]
    · linarith [neg_abs_le (p x-q x)]
  have hh := sum_le_sum (fun x (_:x∈(univ:Finset V))=>hpoint x)
  simp only [sum_add_distrib,hzero,add_zero,←mul_sum,←sum_filter] at hh
  simpa [mass,l1,sum_sub_distrib] using hh

/-- A low-mean function forces positive excess on its maximizing event. -/
theorem excess_detects_mean (q pi qw f : V→ℝ) (μ ε : ℝ)
    (hsame : (∑x,qw x)=(∑x,pi x))
    (hf : ∀x,0≤f x ∧ f x≤1) (hmean : μ≤∑x,pi x*f x)
    (hlow : (∑x,q x*f x)≤μ/4) (hclose : l1 q qw≤ε) :
    3*μ/4-2*ε ≤ mass q (excessSet qw pi)-mass pi (excessSet qw pi) := by
  have hl1sym : l1 qw q=l1 q qw := by unfold l1; apply sum_congr rfl; intro x _; exact abs_sub_comm _ _
  have hmeanclose : |(∑x,q x*f x)-(∑x,qw x*f x)|≤l1 q qw := by
    rw [←sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro x _
    rw [←sub_mul,abs_mul,abs_of_nonneg (hf x).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf x).2
  have hex := mean_diff_le_excess qw pi (fun x=>1-f x) (by intro x; constructor <;> linarith [(hf x).1,(hf x).2])
  have hcomp (p : V→ℝ) : (∑x,p x*(1-f x))=(∑x,p x)-(∑x,p x*f x) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [hcomp,hcomp,hsame] at hex
  have hmassclose := mass_diff_le_l1 q qw (excessSet qw pi)
  have hmeanabs := le_abs_self ((∑x,qw x*f x)-(∑x,q x*f x))
  rw [abs_sub_comm] at hmeanabs
  have hmassabs := neg_abs_le (mass q (excessSet qw pi)-mass qw (excessSet qw pi))
  linarith

theorem unit_near_subspace (E : Submodule ℝ (EuclideanSpace ℝ V))
    (h : EuclideanSpace ℝ V) (hh : ‖h‖=1) (p : E) (ε : ℝ) (hε : ε<1)
    (hclose : ‖h-(p : EuclideanSpace ℝ V)‖≤ε) :
    ∃ v:E, ‖v‖=1 ∧ ‖h-(v : EuclideanSpace ℝ V)‖≤2*ε := by
  have hp : p≠0 := by
    intro hp0
    rw [hp0,Submodule.coe_zero,sub_zero,hh] at hclose
    linarith
  have hpNorm : ‖p‖≠0 := norm_ne_zero_iff.mpr hp
  let v : E := ‖p‖⁻¹ • p
  have hv : ‖v‖=1 := by
    dsimp [v]
    simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ hpNorm
  have hpv : ‖(p : EuclideanSpace ℝ V)-(v : EuclideanSpace ℝ V)‖ = |‖p‖-1| := by
    change ‖p-v‖=|‖p‖-1|
    have hps : p=‖p‖ • v := by
      dsimp [v]
      rw [smul_smul]
      change p=(‖p‖*‖p‖⁻¹) • p
      rw [mul_inv_cancel₀ hpNorm,one_smul]
    calc
      ‖p-v‖=‖(‖p‖-1) • v‖ := by congr 1; rw [sub_smul,one_smul,←hps]
      _ = _ := by rw [norm_smul,hv,Real.norm_eq_abs,mul_one]
  have hnorm : |‖p‖-1|≤ε := by
    have hh' := abs_norm_sub_norm_le (p : EuclideanSpace ℝ V) h
    rw [hh,norm_sub_rev] at hh'
    exact hh'.trans hclose
  refine ⟨v,hv,?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub h (p : EuclideanSpace ℝ V) (v : EuclideanSpace ℝ V)
  rw [hpv] at ht
  linarith

theorem net_near_root (E : Submodule ℝ (EuclideanSpace ℝ V)) (W : Finset E)
    (μ : ℝ) (hμ : 0<μ) (hμ1 : μ≤1)
    (hcover : ∀v:E,‖v‖=1 → ∃w∈W,‖v-w‖≤μ/32)
    (q : V→ℝ) (hq : q∈stdSimplex ℝ V) (p:E)
    (hclose : ‖root q-(p : EuclideanSpace ℝ V)‖≤μ/32) :
    ∃w∈W,‖root q-(w : EuclideanSpace ℝ V)‖≤3*μ/32 := by
  obtain ⟨v,hv,hvclose⟩ := unit_near_subspace E (root q) (norm_root q hq) p (μ/32) (by linarith) hclose
  obtain ⟨w,hw,hwclose⟩ := hcover v hv
  refine ⟨w,hw,?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub (root q) (v : EuclideanSpace ℝ V) (w : EuclideanSpace ℝ V)
  have hwclose' : ‖(v : EuclideanSpace ℝ V)-(w : EuclideanSpace ℝ V)‖≤μ/32 := hwclose
  linarith

end Erdos642.Joint20261019.JointFamilyGeometry
