import Erdos1017.RectangleArithmetic

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def normalizedAffineBudget (S q : ℝ) : ℝ :=
  (1-Real.sqrt 7/3)*(S+1)^2/4+(Real.sqrt 7/3)*(1+q)/2

theorem rectangle_affine_certificate (p : ι → ℝ) (m sl sh ml mh : ℝ)
    (hv : ValidRectangle sl sh ml mh)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, p i ≤ m)
    (hSl : sl ≤ ∑ i, p i) (hSh : (∑ i, p i) ≤ sh)
    (hml : ml ≤ m) (hmh : m ≤ mh) (hq : (∑ i, (p i)^2) = m^2) :
    (∀ T, 0 ≤ rectangleLaw p sl sh mh T) ∧
    (∀ B : Finset ι, B.card ≤ 2 → subsetMoment (rectangleLaw p sl sh mh) B = ∏ i ∈ B, p i) ∧
    ((∑ T : Finset ι, if T.Nonempty then rectangleLaw p sl sh mh T else 0) ≤
      normalizedAffineBudget (∑ i, p i) (m^2)) := by
  obtain ⟨hsl,hsh,hml0,hmm,hmh1,hqsl,hV,hX,hgap⟩ := hv
  have hm0 : 0 ≤ m := hml0.trans hml
  have hql : ml^2 ≤ m^2 := pow_le_pow_left₀ hml0 hml 2
  have hqh : m^2 ≤ mh^2 := pow_le_pow_left₀ hm0 hmh 2
  have hc := rectangle_selector_certificate p sl sh ml mh hsl hsh hml0 hmm hmh1 hqsl hV hX
    hp (fun i => (hm i).trans hmh) hSl hSh (by rwa [hq]) (by rwa [hq])
  refine ⟨hc.1,hc.2.1,?_⟩
  have hs0 : 0 ≤ (∑ i, p i)-sl := sub_nonneg.mpr hSl
  have hs1 : 0 ≤ (∑ i, p i)+sl+2 := by linarith
  have hsquare : (sl+1)^2 ≤ ((∑ i, p i)+1)^2 := by nlinarith [mul_nonneg hs0 hs1]
  have hpoly : (1-(441:ℝ)/500)*(sl+1)^2/4+((441:ℝ)/500)*(1+ml^2)/2 ≤
      (1-(441:ℝ)/500)*((∑ i,p i)+1)^2/4+((441:ℝ)/500)*(1+m^2)/2 := by linarith
  have hroot : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hrootSq : (Real.sqrt 7)^2 = 7 := Real.sq_sqrt (by norm_num)
  have hLambda : Real.sqrt 7/3 ≤ (441:ℝ)/500 := by nlinarith
  have hcoeff : 0 ≤ ((∑ i,p i)+1)^2-2*(1+m^2) := by nlinarith
  have hcompare := mul_nonneg (sub_nonneg.mpr hLambda) hcoeff
  have hcost := hc.2.2
  unfold rectangleGap at hgap
  unfold normalizedAffineBudget
  nlinarith

/-- A valid covering rectangle yields the sharp normalized selector budget. -/
theorem covered_affine_selector (p : ι → ℝ) (m : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, p i ≤ m) (hq : (∑ i, (p i)^2) = m^2)
    (hcover : RectangleCovered (∑ i,p i) m) :
    ∃ w : Finset ι → ℝ, (∀ T, 0 ≤ w T) ∧
      (∀ B : Finset ι, B.card ≤ 2 → subsetMoment w B = ∏ i ∈ B, p i) ∧
      ((∑ T : Finset ι, if T.Nonempty then w T else 0) ≤
        normalizedAffineBudget (∑ i,p i) (m^2)) := by
  obtain ⟨sl,sh,ml,mh,hv,hSl,hSh,hml,hmh⟩ := hcover
  exact ⟨rectangleLaw p sl sh mh,
    rectangle_affine_certificate p m sl sh ml mh hv hp hm hSl hSh hml hmh hq⟩

end Erdos1017
