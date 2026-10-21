import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSmoothingMean

namespace Erdos642.Joint20261019.ConvexTailMatrix
open Matrix Erdos642.FiniteMarkov
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem root_square_le (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (u : V → ℝ) (hu : (∑ x, u x^2)=1) (hAu : A *ᵥ u=u)
    (hpos : ∀ f, 0 ≤ dotProduct f (A *ᵥ f)) (f : V → ℝ) :
    (dotProduct f u)^2 ≤ dotProduct f (A *ᵥ f) := by
  let L := A.mulVecLin
  have hs : ∀ f g, Erdos642.TiltedOperator.dot f (L g) =
      Erdos642.TiltedOperator.dot (L f) g := by
    intro f g
    have ht : A.transpose=A := (Matrix.isHermitian_iff_isSymm.mp hA).eq
    simpa only [L, Erdos642.TiltedOperator.dot, dotProduct, Matrix.mulVecLin_apply, ht,
      mul_comm] using Matrix.dotProduct_transpose_mulVec A f g
  let c := Erdos642.TiltedOperator.dot f u
  have hc : Erdos642.TiltedOperator.dot u (L f)=c := by
    rw [hs, show L u=u from hAu, Erdos642.TiltedOperator.dot_comm]
  have he : Erdos642.TiltedOperator.dot (f-c • u) (L (f-c • u)) =
      Erdos642.TiltedOperator.dot f (L f)-c^2 := by
    simp only [map_sub,map_smul,Erdos642.TiltedOperator.dot_sub_left,
      Erdos642.TiltedOperator.dot_sub_right,Erdos642.TiltedOperator.dot_smul_left,
      Erdos642.TiltedOperator.dot_smul_right]
    rw [show L u=u from hAu,Erdos642.TiltedOperator.dot_self,
      show Erdos642.TiltedOperator.sqNorm u=1 from hu,hc]
    dsimp [c]
    ring
  have hh := hpos (f-c • u)
  change 0 ≤ Erdos642.TiltedOperator.dot (f-c • u) (L (f-c • u)) at hh
  rw [he] at hh
  exact sub_nonneg.mp hh

theorem schur_upper (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (hBnonneg : ∀ x y, 0≤B x y) (w : V → ℝ) (hw : ∀ x, 0<w x)
    (hBw : B *ᵥ w=w) (f : V → ℝ) :
    dotProduct f (B *ᵥ f) ≤ ∑ x, f x^2 := by
  have hsym : ∀ x y, B x y=B y x := by
    intro x y
    simpa only [star_trivial] using hB.apply y x
  have hrow : ∀ x, ∑ y, B x y*w y=w x := fun x => congrFun hBw x
  have hterm : ∀ x y, 2*(B x y*f x*f y) ≤
      B x y*(f x^2*w y/w x+f y^2*w x/w y) := by
    intro x y
    have hh := sq_nonneg (f x*w y-f y*w x)
    have hz : 2*(f x*f y) ≤ f x^2*w y/w x+f y^2*w x/w y := by
      have he : f x^2*w y/w x+f y^2*w x/w y =
          (f x^2*w y^2+f y^2*w x^2)/(w x*w y) := by
        field_simp [ne_of_gt (hw x),ne_of_gt (hw y)]
      rw [he]
      apply (le_div_iff₀ (mul_pos (hw x) (hw y))).mpr
      nlinarith only [hh]
    have hh' := mul_le_mul_of_nonneg_left hz (hBnonneg x y)
    nlinarith only [hh']
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) =>
    Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hterm x y))
  have hleft : (∑ x, ∑ y, 2*(B x y*f x*f y)) = 2*dotProduct f (B *ᵥ f) := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hone : (∑ x, ∑ y, B x y*(f x^2*w y/w x)) = ∑ x, f x^2 := by
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = (f x^2/w x)*(∑ y, B x y*w y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [hrow]; field_simp [ne_of_gt (hw x)]
  have htwo : (∑ x, ∑ y, B x y*(f y^2*w x/w y)) = ∑ x, f x^2 := by
    rw [Finset.sum_comm]
    simpa only [hsym] using hone
  simp_rw [mul_add] at hh
  rw [hleft] at hh
  simp_rw [Finset.sum_add_distrib] at hh
  rw [hone,htwo] at hh
  linarith

variable (C : Chain V)

theorem average_pos (v : V → ℝ) (hv : ∀ x,0<v x) (x : V) :
    0 < (C.transition *ᵥ v) x := by
  have hex : ∃ y, 0<C.transition x y := by
    by_contra hh
    push_neg at hh
    have hz : ∑ y, C.transition x y=0 := Finset.sum_eq_zero (fun y _ => le_antisymm (hh y) (C.nonneg x y))
    rw [C.row_sum] at hz
    norm_num at hz
  obtain ⟨y,hy⟩ := hex
  exact Finset.sum_pos' (fun z _ => mul_nonneg (C.nonneg x z) (hv z).le)
    ⟨y,Finset.mem_univ _,mul_pos hy (hv y)⟩

theorem similarTilt_quadratic (u d f : V → ℝ) :
    dotProduct f (C.similarTilt u d *ᵥ f) =
      dotProduct (fun x=>d x*f x) (C.similarTransition u *ᵥ (fun x=>d x*f x)) := by
  simp only [dotProduct,Matrix.mulVec,Chain.similarTilt,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Genuine stationary log-ratio moment, with n transitions and n+1 observations. -/
theorem stationary_log_ratio_moment (u v : V → ℝ) (hu : ∀ x,0<u x)
    (hun : (∑ x,u x^2)=1) (hA : (C.similarTransition u).IsHermitian)
    (hpos : ∀ f,0≤dotProduct f (C.similarTransition u *ᵥ f))
    (hv : ∀ x,0<v x) (n : ℕ) :
    (∑ x,u x^2*∑ p : Path V n, C.weight x p *
      Real.exp (Chain.vertexSum (fun y=>Real.log (v y/(C.transition *ᵥ v) y)) x p)) ≤ 1 := by
  let d : V → ℝ := fun x=>Real.sqrt (v x/(C.transition *ᵥ v) x)
  have hav := average_pos C v hv
  have hd : ∀ x,0<d x := fun x=>Real.sqrt_pos.2 (div_pos (hv x) (hav x))
  have hdsq : ∀ x,d x^2=v x/(C.transition *ᵥ v) x :=
    fun x=>Real.sq_sqrt (div_nonneg (hv x).le (hav x).le)
  let B := C.similarTilt u d
  let b : V → ℝ := fun x=>u x*d x
  let w : V → ℝ := fun x=>u x*v x/d x
  have hB : B.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext x y
    have hh := hA.apply y x
    simp only [star_trivial] at hh
    dsimp [B,Chain.similarTilt]
    rw [hh]
    ring
  have hBn : ∀ x y,0≤B x y := by
    intro x y
    dsimp [B,Chain.similarTilt,Chain.similarTransition]
    exact mul_nonneg (mul_nonneg (hd x).le
      (div_nonneg (mul_nonneg (hu x).le (C.nonneg x y)) (hu y).le)) (hd y).le
  have hw : ∀ x,0<w x := fun x=>div_pos (mul_pos (hu x) (hv x)) (hd x)
  have hBw : B *ᵥ w=w := by
    ext x
    simp only [Matrix.mulVec,dotProduct]
    calc
      (∑ y,B x y*w y) = d x*u x*(C.transition *ᵥ v) x := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        dsimp [B,w,Chain.similarTilt,Chain.similarTransition]
        field_simp [ne_of_gt (hu y),ne_of_gt (hd y)]
      _ = w x := by
        dsimp [w]
        have hh := hdsq x
        field_simp [ne_of_gt (hav x)] at hh
        apply (eq_div_iff (ne_of_gt (hd x))).mpr
        calc
          _ = u x*(d x^2*(C.transition *ᵥ v) x) := by ring
          _ = u x*v x := by rw [hh]
  have hBpos : ∀ f,0≤dotProduct f (B *ᵥ f) := by
    intro f
    rw [show B=C.similarTilt u d from rfl,similarTilt_quadratic C]
    exact hpos _
  have hupper : ∀ f,dotProduct f (B *ᵥ f) ≤ 1*∑ x,f x^2 := by
    intro f
    simpa only [one_mul] using schur_upper B hB hBn w hw hBw f
  have hlow : (dotProduct b b)^2 ≤ dotProduct b (B *ᵥ b) := by
    have hh := root_square_le (C.similarTransition u) hA u hun
      (Erdos642.CampaignFe72210bContinuation3.MomentSmoothingMean.similarTransition_fixes_root C u hu)
      hpos (fun x=>d x*b x)
    rw [show B=C.similarTilt u d from rfl,similarTilt_quadratic C]
    convert hh using 1
    congr 1
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro x _
    dsimp [b]
    ring
  have hb : (∑ x,b x^2) ≤ 1 := by
    have hs : dotProduct b b=∑ x,b x^2 := by simp only [dotProduct,pow_two]
    rw [hs] at hlow
    have hh := hupper b
    simp only [one_mul] at hh
    have hnon := Finset.sum_nonneg (fun x (_ : x ∈ (Finset.univ : Finset V)) => sq_nonneg (b x))
    nlinarith
  have hpower := Erdos642.QuadraticPower.quadratic_power_bound B hB 1 (by norm_num)
    hBpos hupper n b
  simp only [one_pow,one_mul] at hpower
  have hprod : ∀ x (p : Path V n), Chain.vertexProduct d x p =
      Real.exp (Chain.vertexSum (fun y=>Real.log (v y/(C.transition *ᵥ v) y)) x p) := by
    clear hpower
    intro x p
    induction n generalizing x with
    | zero =>
      change d x^2=Real.exp (Real.log (v x/(C.transition *ᵥ v) x))
      rw [hdsq,Real.exp_log (div_pos (hv x) (hav x))]
    | succ n ih =>
      change d x^2*Chain.vertexProduct d p.1 p.2 =
        Real.exp (Real.log (v x/(C.transition *ᵥ v) x)+Chain.vertexSum _ p.1 p.2)
      rw [ih,Real.exp_add,Real.exp_log (div_pos (hv x) (hav x)),hdsq]
  simp_rw [← hprod]
  rw [C.weighted_path_moment u d (fun x=>ne_of_gt (hu x)) n]
  exact (le_abs_self _).trans (hpower.trans hb)

end Erdos642.Joint20261019.ConvexTailMatrix
