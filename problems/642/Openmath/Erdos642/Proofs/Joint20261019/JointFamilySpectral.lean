import Openmath.Erdos642.Proofs.Joint20261019.JointFamilyGeometry
import Openmath.Erdos642.Proofs.Joint20261019.Energy
import Openmath.Erdos642.Proofs.CampaignFe72210b.QuadraticPower

namespace Erdos642.Joint20261019.JointFamilySpectral
open Matrix Erdos642.CampaignFe72210bContinuation3 MomentSmoothing
open JointFamilyGeometry
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem energy_spectral (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (q : V→ℝ) (hq : q∈stdSimplex ℝ V) :
    Energy.energy A q = ∑j,(1-hA.eigenvalues j)*(inner ℝ (hA.eigenvectorBasis j) (root q))^2 := by
  have he := Erdos642.QuadraticPower.power_quadratic_expansion A hA 1 (fun x=>Real.sqrt (q x))
  simp only [pow_one] at he
  rw [Energy.energy_eq_dotProduct,he]
  have hn : (∑x,q x) = ∑j,(inner ℝ (hA.eigenvectorBasis j) (root q))^2 := by
    rw [hA.eigenvectorBasis.sum_sq_inner_right,norm_root q hq,hq.2]
    norm_num
  rw [hn,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold root
  ring

theorem projection_inner (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (h : EuclideanSpace ℝ V) (j : V) :
    inner ℝ (hA.eigenvectorBasis j) ((slowSpace A hA).orthogonalProjectionOnto h : EuclideanSpace ℝ V) =
      if j∈slowIndices A hA then inner ℝ (hA.eigenvectorBasis j) h else 0 := by
  classical
  rw [slow_projection_eq_sum]
  simp only [inner_sum,inner_smul_right,OrthonormalBasis.inner_eq_ite]
  simp

theorem complement_norm_sq (A : Matrix V V ℝ) (hA : A.IsHermitian) (h : EuclideanSpace ℝ V) :
    ‖h-((slowSpace A hA).orthogonalProjectionOnto h : EuclideanSpace ℝ V)‖^2 =
      ∑j,if j∈slowIndices A hA then 0 else (inner ℝ (hA.eigenvectorBasis j) h)^2 := by
  rw [←hA.eigenvectorBasis.sum_sq_inner_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_sub_right,projection_inner]
  split_ifs <;> simp

theorem complement_energy (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (heig : ∀j,hA.eigenvalues j≤1) (q : V→ℝ) (hq : q∈stdSimplex ℝ V) :
    (3/4:ℝ)*‖root q-((slowSpace A hA).orthogonalProjectionOnto (root q) : EuclideanSpace ℝ V)‖^2 ≤ Energy.energy A q := by
  rw [energy_spectral A hA q hq,complement_norm_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hj
  · simp only [mul_zero]
    exact mul_nonneg (sub_nonneg.mpr (heig j)) (sq_nonneg _)
  · have hjlt : hA.eigenvalues j<1/4 := by simpa [slowIndices] using hj
    nlinarith [sq_nonneg (inner ℝ (hA.eigenvectorBasis j) (root q))]

theorem low_energy_near_slow (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (heig : ∀j,hA.eigenvalues j≤1) (q : V→ℝ) (hq : q∈stdSimplex ℝ V)
    (μ : ℝ) (hμ : 0<μ) (he : Energy.energy A q≤μ^2/4096) :
    ‖root q-((slowSpace A hA).orthogonalProjectionOnto (root q) : EuclideanSpace ℝ V)‖≤μ/32 := by
  have hh := complement_energy A hA heig q hq
  nlinarith [norm_nonneg (root q-((slowSpace A hA).orthogonalProjectionOnto (root q) : EuclideanSpace ℝ V))]

theorem gap_energy_distance (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (u : V→ℝ) (hu : ∀x,0≤u x) (hun : ∑x,u x^2=1) (hAu : A*ᵥu=u)
    (γ : ℝ) (hγ : 0≤γ)
    (hgap : ∀f:V→ℝ,dotProduct f u=0 → dotProduct f (A*ᵥf)≤(1-γ)*∑x,f x^2)
    (q : V→ℝ) (hq : q∈stdSimplex ℝ V) :
    γ*‖root q-WithLp.toLp 2 u‖^2/2 ≤ Energy.energy A q := by
  let g : V→ℝ := fun x=>Real.sqrt (q x)
  let α := Erdos642.TiltedOperator.dot g u
  have hgn : Erdos642.TiltedOperator.sqNorm g=1 := by
    dsimp [Erdos642.TiltedOperator.sqNorm,g]
    simpa only [Real.sq_sqrt (hq.1 _)] using hq.2
  have hun' : Erdos642.TiltedOperator.sqNorm u=1 := hun
  have hα : 0≤α := Finset.sum_nonneg (fun x _=>mul_nonneg (Real.sqrt_nonneg _) (hu x))
  have hs : ∀f g:V→ℝ,Erdos642.TiltedOperator.dot f (A.mulVecLin g)=Erdos642.TiltedOperator.dot (A.mulVecLin f) g := by
    intro f g
    have ht : A.transpose=A := (Matrix.isHermitian_iff_isSymm.mp hA).eq
    simpa only [Erdos642.TiltedOperator.dot,dotProduct,Matrix.mulVecLin_apply,ht,mul_comm] using Matrix.dotProduct_transpose_mulVec A f g
  have hg : ∀f:V→ℝ,Erdos642.TiltedOperator.dot f u=0 →
      Erdos642.TiltedOperator.dot f (A.mulVecLin f)≤(1-γ)*Erdos642.TiltedOperator.sqNorm f := hgap
  have hp := Erdos642.TiltedOperator.quadratic_poincare A.mulVecLin u g γ hun' hAu hs hg
  have hproj : Erdos642.TiltedOperator.sqNorm (g-α • u)=1-α^2 := by
    rw [Erdos642.TiltedOperator.sqNorm_sub_smul,hgn,hun']
    change 1-2*α*α+α^2*1=1-α^2
    ring
  have hdist : ‖root q-WithLp.toLp 2 u‖^2=2-2*α := by
    have hh := Erdos642.TiltedOperator.sqNorm_sub_smul g u 1
    rw [hgn,hun'] at hh
    simp only [one_mul,one_pow,mul_one] at hh
    have he : ‖root q-WithLp.toLp 2 u‖^2=Erdos642.TiltedOperator.sqNorm (g-u) := by
      simp [EuclideanSpace.real_norm_sq_eq,Erdos642.TiltedOperator.sqNorm,root,g]
    rw [he]
    simp only [one_smul] at hh
    change Erdos642.TiltedOperator.sqNorm (g-u)=1-2*α+1 at hh
    linarith
  have hα1 : α≤1 := by nlinarith [sq_nonneg ‖root q-WithLp.toLp 2 u‖]
  have henergy : Energy.energy A q=1-Erdos642.TiltedOperator.dot g (A.mulVecLin g) := by
    rw [Energy.energy_eq_dotProduct,hq.2]
    rfl
  change γ*Erdos642.TiltedOperator.sqNorm (g-α • u)≤_ at hp
  rw [hproj,hgn,←henergy] at hp
  rw [hdist]
  have hsq : α^2≤α := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq hγ
  nlinarith

theorem event_energy (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (u : V→ℝ) (hu : ∀x,0≤u x) (hun : ∑x,u x^2=1) (hAu : A*ᵥu=u)
    (γ : ℝ) (hγ : 0≤γ)
    (hgap : ∀f:V→ℝ,dotProduct f u=0 → dotProduct f (A*ᵥf)≤(1-γ)*∑x,f x^2)
    (q : V→ℝ) (hq : q∈stdSimplex ℝ V) (S : Finset V) (μ : ℝ) (hμ : 0≤μ)
    (hbad : μ/4 ≤ mass q S-mass (fun x=>u x^2) S) :
    γ*μ^2/32≤Energy.energy A q := by
  have hunorm : ‖WithLp.toLp 2 u‖=1 := by
    have hh : ‖WithLp.toLp 2 u‖^2=1 := by simpa [EuclideanSpace.real_norm_sq_eq] using hun
    nlinarith [norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℝ V)]
  have hl := l1_squares (root q) (WithLp.toLp 2 u) (norm_root q hq) hunorm
  rw [squares_root q hq] at hl
  have hm := twice_mass_diff_le_l1 q (fun x=>u x^2) (hq.2.trans hun.symm) S
  change l1 q (fun x=>u x^2)≤_ at hl
  have hnorm : μ/4≤‖root q-WithLp.toLp 2 u‖ := by linarith
  have hsq : μ^2/16≤‖root q-WithLp.toLp 2 u‖^2 := by nlinarith [norm_nonneg (root q-WithLp.toLp 2 u)]
  have hmul := mul_le_mul_of_nonneg_left hsq hγ
  have he := gap_energy_distance A hA u hu hun hAu γ hγ hgap q hq
  nlinarith

end Erdos642.Joint20261019.JointFamilySpectral
