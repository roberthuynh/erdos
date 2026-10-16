import GeneralStar.Optimizer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

/-- Literal bare all-integer, every-order, prescribed original graph endpoint. -/
theorem general_star_family (q n : ℕ) (hq : 5 ≤ q) (hn : closedStart q ≤ n) :
    FamilyConclusion q n (closedDeficit q) (closedFamily q n) := c24 q n hq hn

theorem general_star_endpoint : C24Endpoint := c24_endpoint

theorem closedStart_pos (q : ℕ) (hq : 5 ≤ q) : 0 < closedStart q := by
  unfold closedStart
  split_ifs <;> omega

theorem closedFamily_nonempty (q n : ℕ) (hq : 5 ≤ q) (hn : closedStart q ≤ n) :
    Nonempty (closedFamily q n).Carrier := by
  have ho := (c24 q n hq hn).1
  have hs := closedStart_pos q hq
  apply Fintype.card_pos_iff.mp
  change 0 < (closedFamily q n).order
  omega

theorem closedStart_common (q : ℕ) (hq : 7 ≤ q) : closedStart q ≤ 4*q-4 := by
  have hlow : ¬(q=5 ∨ q=6) := by omega
  have hp := closed_params q hq
  rcases hp with ⟨_hs,_hps,_hhs,_hpa,ha,hb,_hp,_hr,_hf,_hl⟩
  simp only [closedStart,if_neg hlow]
  omega

theorem general_star_common (q n : ℕ) (hq : 7 ≤ q) (hn : 4*q-4 ≤ n) :
    FamilyConclusion q n (closedDeficit q) (closedFamily q n) :=
  c24 q n (by omega) ((closedStart_common q hq).trans hn)

theorem general_star_optimized (q n : ℕ) (hq : 7 ≤ q) (hn : optimumStart q ≤ n) :
    FamilyConclusion q n (optimumDeficit q) (optimumFamily q n) := o24 q n hq hn

theorem general_star_optimized_common (q n : ℕ) (hq : 7 ≤ q) (hn : 4*q-4 ≤ n) :
    FamilyConclusion q n (optimumDeficit q) (optimumFamily q n) :=
  o24 q n hq ((o24_start q hq).trans hn)

/-- Projection to the exact finite lex tuple, with all original U guards internal. -/
theorem optimizerTuple_params (q : ℕ) (hq : 7 ≤ q) :
    let T := optimizerTuple q
    UParams q T.1 T.2.1 T.2.2.1 T.2.2.2 := (optimizerKey_spec q hq).1

end Erdos585.GeneralStar
