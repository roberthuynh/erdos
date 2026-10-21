import Erdos1017.RectangleCells.Batch00
import Erdos1017.RectangleCells.Batch01
import Erdos1017.RectangleCells.Batch02
import Erdos1017.RectangleCells.Batch03
import Erdos1017.RectangleCells.Batch04
import Erdos1017.RectangleCells.Batch05
import Erdos1017.RectangleCells.Batch06
import Erdos1017.RectangleCells.Batch07
import Erdos1017.RectangleCells.Batch08
import Erdos1017.RectangleCells.Batch09
import Erdos1017.RectangleCells.Batch10
import Erdos1017.RectangleCells.Batch11
import Erdos1017.RectangleCells.Batch12
import Erdos1017.RectangleCells.Batch13
import Erdos1017.RectangleCells.Batch14
import Erdos1017.RectangleCells.Batch15
import Erdos1017.RectangleCells.Batch16
import Erdos1017.RectangleCells.Batch17
import Erdos1017.RectangleCells.Batch18
import Erdos1017.RectangleCells.Batch19
import Erdos1017.RectangleCells.Batch20
import Erdos1017.RectangleCells.Batch21
import Erdos1017.RectangleCells.Batch22
import Erdos1017.RectangleCells.Batch23
import Erdos1017.RectangleAffine

namespace Erdos1017
open scoped BigOperators

theorem continuous_rectangle_covered (S m : ℝ)
    (hSl : (17:ℝ)/8 ≤ S) (hSh : S ≤ (7:ℝ)/2)
    (hmL : 0 ≤ m) (hmH : m ≤ (4:ℝ)/5) : RectangleCovered S m := by
  rcases le_total S (45/16) with hcut0 | hcut0
  · rcases le_total m (2/5) with hcut1 | hcut1
    · rcases le_total S (79/32) with hcut2 | hcut2
      · rcases le_total m (1/5) with hcut3 | hcut3
        · exact rectangle_coverage_00 S m hSl hcut2 hmL hcut3
        · rcases le_total S (147/64) with hcut4 | hcut4
          · rcases le_total m (3/10) with hcut5 | hcut5
            · exact rectangle_coverage_01 S m hSl hcut4 hcut3 hcut5
            · rcases le_total S (283/128) with hcut6 | hcut6
              · exact rectangle_coverage_02 S m hSl hcut6 hcut5 hcut1
              · exact rectangle_coverage_03 S m hcut6 hcut4 hcut5 hcut1
          · exact rectangle_coverage_04 S m hcut4 hcut2 hcut3 hcut1
      · exact rectangle_coverage_05 S m hcut2 hcut0 hmL hcut1
    · rcases le_total S (79/32) with hcut7 | hcut7
      · rcases le_total m (3/5) with hcut8 | hcut8
        · rcases le_total S (147/64) with hcut9 | hcut9
          · rcases le_total m (1/2) with hcut10 | hcut10
            · rcases le_total S (283/128) with hcut11 | hcut11
              · rcases le_total m (9/20) with hcut12 | hcut12
                · rcases le_total S (555/256) with hcut13 | hcut13
                  · rcases le_total m (17/40) with hcut14 | hcut14
                    · exact rectangle_coverage_06 S m hSl hcut13 hcut1 hcut14
                    · exact rectangle_coverage_07 S m hSl hcut13 hcut14 hcut12
                  · exact rectangle_coverage_08 S m hcut13 hcut11 hcut1 hcut12
                · rcases le_total S (555/256) with hcut15 | hcut15
                  · rcases le_total m (19/40) with hcut16 | hcut16
                    · rcases le_total S (1099/512) with hcut17 | hcut17
                      · exact rectangle_coverage_09 S m hSl hcut17 hcut12 hcut16
                      · exact rectangle_coverage_10 S m hcut17 hcut15 hcut12 hcut16
                    · rcases le_total S (1099/512) with hcut18 | hcut18
                      · exact rectangle_coverage_11 S m hSl hcut18 hcut16 hcut10
                      · exact rectangle_coverage_12 S m hcut18 hcut15 hcut16 hcut10
                  · exact rectangle_coverage_13 S m hcut15 hcut11 hcut12 hcut10
              · exact rectangle_coverage_14 S m hcut11 hcut9 hcut1 hcut10
            · rcases le_total S (283/128) with hcut19 | hcut19
              · rcases le_total m (11/20) with hcut20 | hcut20
                · rcases le_total S (555/256) with hcut21 | hcut21
                  · rcases le_total m (21/40) with hcut22 | hcut22
                    · exact rectangle_coverage_15 S m hSl hcut21 hcut10 hcut22
                    · exact rectangle_coverage_16 S m hSl hcut21 hcut22 hcut20
                  · exact rectangle_coverage_17 S m hcut21 hcut19 hcut10 hcut20
                · exact rectangle_coverage_18 S m hSl hcut19 hcut20 hcut8
              · exact rectangle_coverage_19 S m hcut19 hcut9 hcut10 hcut8
          · exact rectangle_coverage_20 S m hcut9 hcut7 hcut1 hcut8
        · exact rectangle_coverage_21 S m hSl hcut7 hcut8 hmH
      · exact rectangle_coverage_22 S m hcut7 hcut0 hcut1 hmH
  · exact rectangle_coverage_23 S m hcut0 hSh hmL hmH

theorem continuous_sharp_selector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (m : ℝ) (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, p i ≤ m)
    (hq : (∑ i, (p i)^2) = m^2)
    (hSl : (17:ℝ)/8 ≤ ∑ i,p i) (hSh : (∑ i,p i) ≤ (7:ℝ)/2)
    (hmL : 0 ≤ m) (hmH : m ≤ (4:ℝ)/5) :
    ∃ w : Finset ι → ℝ, (∀ T, 0 ≤ w T) ∧
      (∀ B : Finset ι, B.card ≤ 2 → subsetMoment w B = ∏ i ∈ B, p i) ∧
      ((∑ T : Finset ι, if T.Nonempty then w T else 0) ≤
        normalizedAffineBudget (∑ i,p i) (m^2)) := by
  exact covered_affine_selector p m hp hm hq
    (continuous_rectangle_covered (∑ i,p i) m hSl hSh hmL hmH)

end Erdos1017
