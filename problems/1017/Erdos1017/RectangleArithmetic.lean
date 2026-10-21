import Erdos1017.RectangleSelector

namespace Erdos1017

noncomputable def rectangleGap (sl sh ml mh : ℝ) : ℝ :=
  (1-(441:ℝ)/500)*(sl+1)^2/4-1+((441:ℝ)/500)*(1+ml^2)/2+
    rectangleP sh mh*rectangleBracket sl sh ml mh

def ValidRectangle (sl sh ml mh : ℝ) : Prop :=
  2 ≤ sl ∧ sl ≤ sh ∧ 0 ≤ ml ∧ ml ≤ mh ∧ mh < 1 ∧ mh^2 < sl ∧
    0 ≤ sl-2*mh ∧ sh+logCoefficientUpper 13 mh*mh^2 < 18 ∧
      0 ≤ rectangleGap sl sh ml mh

def RectangleCovered (S m : ℝ) : Prop :=
  ∃ sl sh ml mh, ValidRectangle sl sh ml mh ∧ sl ≤ S ∧ S ≤ sh ∧ ml ≤ m ∧ m ≤ mh

end Erdos1017
