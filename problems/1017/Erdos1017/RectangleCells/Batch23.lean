import Erdos1017.RectangleArithmetic

namespace Erdos1017

theorem rectangle_valid_009 : ValidRectangle (45/16) (191/64) (0) (1/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_008 : ValidRectangle (191/64) (101/32) (0) (1/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_007 : ValidRectangle (45/16) (191/64) (1/5) (3/10) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_006 : ValidRectangle (45/16) (191/64) (3/10) (2/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_005 : ValidRectangle (191/64) (101/32) (1/5) (2/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_004 : ValidRectangle (101/32) (7/2) (0) (2/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_003 : ValidRectangle (45/16) (191/64) (2/5) (3/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_002 : ValidRectangle (191/64) (101/32) (2/5) (3/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_001 : ValidRectangle (45/16) (101/32) (3/5) (4/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_000 : ValidRectangle (101/32) (7/2) (2/5) (4/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_coverage_23 (S m : ℝ)
    (hSl : (45/16) ≤ S) (hSh : S ≤ (7/2)) (hmL : (0) ≤ m) (hmH : m ≤ (4/5)) :
    RectangleCovered S m := by
  rcases le_total m (2/5) with hcut0 | hcut0
  · rcases le_total S (101/32) with hcut1 | hcut1
    · rcases le_total m (1/5) with hcut2 | hcut2
      · rcases le_total S (191/64) with hcut3 | hcut3
        · exact ⟨(45/16), (191/64), (0), (1/5), rectangle_valid_009, hSl, hcut3, hmL, hcut2⟩
        · exact ⟨(191/64), (101/32), (0), (1/5), rectangle_valid_008, hcut3, hcut1, hmL, hcut2⟩
      · rcases le_total S (191/64) with hcut4 | hcut4
        · rcases le_total m (3/10) with hcut5 | hcut5
          · exact ⟨(45/16), (191/64), (1/5), (3/10), rectangle_valid_007, hSl, hcut4, hcut2, hcut5⟩
          · exact ⟨(45/16), (191/64), (3/10), (2/5), rectangle_valid_006, hSl, hcut4, hcut5, hcut0⟩
        · exact ⟨(191/64), (101/32), (1/5), (2/5), rectangle_valid_005, hcut4, hcut1, hcut2, hcut0⟩
    · exact ⟨(101/32), (7/2), (0), (2/5), rectangle_valid_004, hcut1, hSh, hmL, hcut0⟩
  · rcases le_total S (101/32) with hcut6 | hcut6
    · rcases le_total m (3/5) with hcut7 | hcut7
      · rcases le_total S (191/64) with hcut8 | hcut8
        · exact ⟨(45/16), (191/64), (2/5), (3/5), rectangle_valid_003, hSl, hcut8, hcut0, hcut7⟩
        · exact ⟨(191/64), (101/32), (2/5), (3/5), rectangle_valid_002, hcut8, hcut6, hcut0, hcut7⟩
      · exact ⟨(45/16), (101/32), (3/5), (4/5), rectangle_valid_001, hSl, hcut6, hcut7, hmH⟩
    · exact ⟨(101/32), (7/2), (2/5), (4/5), rectangle_valid_000, hcut6, hSh, hcut0, hmH⟩

end Erdos1017
