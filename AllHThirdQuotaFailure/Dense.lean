import AllHThirdQuotaFailure.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHThirdQuotaFailure
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma ec_lower (d : ℕ) {X W : Finset V} (hd : ∀ v∈X, d ≤ dg G W v) :
    d * #X ≤ ec G X W := by
  calc d * #X = ∑ _v ∈ X, d := by simp [sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := sum_le_sum hd

/-- The elementary dense criterion pays EVERY original capacity-one cut. -/
theorem dense_cuts (q d : ℕ) {P Q : Finset V}
    (hcard : #P = #Q) (hdq : q ≤ d) (hhalf : #P+q ≤ 2*d)
    (hleft : ∀ v∈P, d ≤ dg G Q v) (hright : ∀ v∈Q, d ≤ dg G P v) :
    ∀ X⊆P, ∀ Y⊆Q, q * #X ≤ ec G X (Q\Y) + q * #Y := by
  intro X hX Y hY
  by_cases hxy : #X ≤ #Y
  · exact (Nat.mul_le_mul_left q hxy).trans (Nat.le_add_left _ _)
  have hx := card_le_card hX
  have hy := card_le_card hY
  have hsX := card_sdiff_add_card_eq_card hX
  have hsY := card_sdiff_add_card_eq_card hY
  by_cases hxd : #X ≤ d
  · have hl := ec_lower d (fun v hv => hleft v (hX hv))
    have he := ec_sdiff_add_right (G := G) hY X
    have hp := ec_le_product (G := G) X Y
    by_cases hxq : #X ≤ q
    · zify at hl he hp hdq hxq
      have h1 := mul_nonneg (show (0:ℤ) ≤ #X by positivity)
        (show (0:ℤ) ≤ (d:ℤ)-q by omega)
      have h2 := mul_nonneg (show (0:ℤ) ≤ #Y by positivity)
        (show (0:ℤ) ≤ (q:ℤ)-#X by omega)
      zify
      nlinarith
    · zify at hl he hp hxd hxy hxq
      have h1 := mul_nonneg (show (0:ℤ) ≤ #X by positivity)
        (show (0:ℤ) ≤ (d:ℤ)-#X by omega)
      have h2 := mul_nonneg (show (0:ℤ) ≤ (#X:ℤ)-#Y by omega)
        (show (0:ℤ) ≤ (#X:ℤ)-q by omega)
      zify
      nlinarith
  · have hl := ec_lower d (X:=Q\Y) (W:=P) (fun v hv => hright v (sdiff_subset hv))
    have he := ec_sdiff_add_right (G := G) hX (Q\Y)
    have hp := ec_le_product (G := G) (Q\Y) (P\X)
    have hc := ec_comm (G := G) (Q\Y) X
    zify at hl he hp hc hcard hsX hsY hx hy hxd hhalf
    have h1 := mul_nonneg (show (0:ℤ) ≤ #(Q\Y) by positivity)
      (show (0:ℤ) ≤ (d:ℤ)-#P+#X-q by omega)
    have h2 := mul_nonneg (show (0:ℤ) ≤ (q:ℤ) by positivity)
      (show (0:ℤ) ≤ (#P:ℤ)-#X by omega)
    zify
    nlinarith

/-- Conventional dense bipartite factor criterion with actual original units. -/
theorem dense_factor (q : ℕ) {P Q : Finset V}
    (hcard : #P = #Q) (hm : q ≤ #P)
    (hleft : ∀ v∈P, #P+q ≤ 2*dg G Q v)
    (hright : ∀ v∈Q, #P+q ≤ 2*dg G P v) : FactorOn q G P Q := by
  let d := (#P+q+1)/2
  have hdq : q ≤ d := by dsimp [d]; omega
  have hhalf : #P+q ≤ 2*d := by dsimp [d]; omega
  have hl : ∀ v∈P, d ≤ dg G Q v := by
    intro v hv
    have hh := hleft v hv
    dsimp [d]
    omega
  have hr : ∀ v∈Q, d ≤ dg G P v := by
    intro v hv
    have hh := hright v hv
    dsimp [d]
    omega
  exact B5Factor.exists_target_factor (k:=q) P Q hcard
    (dense_cuts q d hcard hdq hhalf hl hr)

end Erdos585.AllHThirdQuotaFailure
