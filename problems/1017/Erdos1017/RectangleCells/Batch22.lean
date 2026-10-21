import Erdos1017.RectangleArithmetic

namespace Erdos1017

theorem rectangle_valid_023 : ValidRectangle (79/32) (643/256) (2/5) (9/20) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_022 : ValidRectangle (643/256) (327/128) (2/5) (9/20) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_021 : ValidRectangle (79/32) (327/128) (9/20) (1/2) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_020 : ValidRectangle (327/128) (169/64) (2/5) (9/20) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_019 : ValidRectangle (327/128) (169/64) (9/20) (1/2) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_018 : ValidRectangle (79/32) (327/128) (1/2) (11/20) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_017 : ValidRectangle (79/32) (327/128) (11/20) (3/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_016 : ValidRectangle (327/128) (169/64) (1/2) (3/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_015 : ValidRectangle (169/64) (349/128) (2/5) (1/2) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_014 : ValidRectangle (349/128) (45/16) (2/5) (1/2) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_013 : ValidRectangle (169/64) (45/16) (1/2) (3/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_012 : ValidRectangle (79/32) (169/64) (3/5) (7/10) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_011 : ValidRectangle (79/32) (169/64) (7/10) (4/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_valid_010 : ValidRectangle (169/64) (45/16) (3/5) (4/5) := by
  norm_num [ValidRectangle, rectangleGap, rectangleP, rectangleBracket, rectangleB, rectangleCorrectedLower, collisionLower, rectangleU, tradeThetaThree, tradeThetaHigher, tradeDenominator, expUpper, logCoefficientUpper, Finset.sum_range_succ, Nat.factorial]

theorem rectangle_coverage_22 (S m : ℝ)
    (hSl : (79/32) ≤ S) (hSh : S ≤ (45/16)) (hmL : (2/5) ≤ m) (hmH : m ≤ (4/5)) :
    RectangleCovered S m := by
  rcases le_total m (3/5) with hcut0 | hcut0
  · rcases le_total S (169/64) with hcut1 | hcut1
    · rcases le_total m (1/2) with hcut2 | hcut2
      · rcases le_total S (327/128) with hcut3 | hcut3
        · rcases le_total m (9/20) with hcut4 | hcut4
          · rcases le_total S (643/256) with hcut5 | hcut5
            · exact ⟨(79/32), (643/256), (2/5), (9/20), rectangle_valid_023, hSl, hcut5, hmL, hcut4⟩
            · exact ⟨(643/256), (327/128), (2/5), (9/20), rectangle_valid_022, hcut5, hcut3, hmL, hcut4⟩
          · exact ⟨(79/32), (327/128), (9/20), (1/2), rectangle_valid_021, hSl, hcut3, hcut4, hcut2⟩
        · rcases le_total m (9/20) with hcut6 | hcut6
          · exact ⟨(327/128), (169/64), (2/5), (9/20), rectangle_valid_020, hcut3, hcut1, hmL, hcut6⟩
          · exact ⟨(327/128), (169/64), (9/20), (1/2), rectangle_valid_019, hcut3, hcut1, hcut6, hcut2⟩
      · rcases le_total S (327/128) with hcut7 | hcut7
        · rcases le_total m (11/20) with hcut8 | hcut8
          · exact ⟨(79/32), (327/128), (1/2), (11/20), rectangle_valid_018, hSl, hcut7, hcut2, hcut8⟩
          · exact ⟨(79/32), (327/128), (11/20), (3/5), rectangle_valid_017, hSl, hcut7, hcut8, hcut0⟩
        · exact ⟨(327/128), (169/64), (1/2), (3/5), rectangle_valid_016, hcut7, hcut1, hcut2, hcut0⟩
    · rcases le_total m (1/2) with hcut9 | hcut9
      · rcases le_total S (349/128) with hcut10 | hcut10
        · exact ⟨(169/64), (349/128), (2/5), (1/2), rectangle_valid_015, hcut1, hcut10, hmL, hcut9⟩
        · exact ⟨(349/128), (45/16), (2/5), (1/2), rectangle_valid_014, hcut10, hSh, hmL, hcut9⟩
      · exact ⟨(169/64), (45/16), (1/2), (3/5), rectangle_valid_013, hcut1, hSh, hcut9, hcut0⟩
  · rcases le_total S (169/64) with hcut11 | hcut11
    · rcases le_total m (7/10) with hcut12 | hcut12
      · exact ⟨(79/32), (169/64), (3/5), (7/10), rectangle_valid_012, hSl, hcut11, hcut0, hcut12⟩
      · exact ⟨(79/32), (169/64), (7/10), (4/5), rectangle_valid_011, hSl, hcut11, hcut12, hmH⟩
    · exact ⟨(169/64), (45/16), (3/5), (4/5), rectangle_valid_010, hcut11, hSh, hcut0, hmH⟩

end Erdos1017
