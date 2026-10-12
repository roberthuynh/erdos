import AllHFourthQuotaFailure.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] r248InterfaceDecidableEq
namespace Erdos585.AllHFourthQuotaFailure
open QB4 B5 L34 H3Unequal
universe u

/-- Integer rectangle algebra for the conventional discriminant criterion. -/
lemma rectangle_cut (m q d x y e : ℤ) (hq : 0≤q) (hx : 0≤x) (hy : 0≤y)
    (hs : x+y≤m) (hc : (2*q-d)^2≤m*(2*d-m))
    (he : x*(d-y)≤e) : q*(x-y)≤e := by
  by_cases hp : 0≤d-q-y
  · have h1 := mul_nonneg hx hp
    have h2 := mul_nonneg hq hy
    nlinarith
  · have hprod := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤m-y-x by omega) (show d-q-y≤0 by omega)
    nlinarith [sq_nonneg (2*y-(m+d-2*q))]

variable {V : Type u} {G : SimpleGraph V}

lemma ec_lower (d : ℕ) {X W : Finset V} (hd : ∀ v∈X, d≤dg G W v) :
    d*#X≤ec G X W := by
  calc d*#X = ∑ _v∈X,d := by simp [sum_const,smul_eq_mul,mul_comm]
    _ ≤ _ := sum_le_sum hd

/-- Every cut is paid using the same actual capacity-one original rectangle. -/
theorem dense_cuts (q d : ℕ) {P Q : Finset V} (hcard : #P=#Q)
    (hc : (2*(q:ℤ)-d)^2≤(#P:ℤ)*(2*d-#P))
    (hl : ∀ v∈P,d≤dg G Q v) (hr : ∀ v∈Q,d≤dg G P v) :
    ∀ X⊆P, ∀ Y⊆Q, q*#X≤ec G X (Q\Y)+q*#Y := by
  intro X hX Y hY
  have hx := card_le_card hX
  have hy := card_le_card hY
  have hsX := card_sdiff_add_card_eq_card hX
  have hsY := card_sdiff_add_card_eq_card hY
  by_cases hsum : #X+#Y≤#P
  · have he := ec_lower d (fun v hv => hl v (hX hv))
    have hsplit := ec_sdiff_add_right (G:=G) hY X
    have hprod := ec_le_product (G:=G) X Y
    zify at he hsplit hprod hsum
    have hb : (#X:ℤ)*((d:ℤ)-#Y)≤ec G X (Q\Y) := by nlinarith
    have hh := rectangle_cut (#P) q d (#X) (#Y) (ec G X (Q\Y))
      (by positivity) (by positivity) (by positivity) hsum hc hb
    zify
    nlinarith
  · have he := ec_lower d (X:=Q\Y) (W:=P) (fun v hv => hr v (sdiff_subset hv))
    have hsplit := ec_sdiff_add_right (G:=G) hX (Q\Y)
    have hprod := ec_le_product (G:=G) (Q\Y) (P\X)
    have hcomm := ec_comm (G:=G) (Q\Y) X
    zify at he hsplit hprod hcomm hcard hsX hsY hx hy hsum
    have hb : (#(Q\Y):ℤ)*((d:ℤ)-#(P\X))≤ec G X (Q\Y) := by nlinarith
    have hh := rectangle_cut (#P) q d (#(Q\Y)) (#(P\X)) (ec G X (Q\Y))
      (by positivity) (by positivity) (by positivity) (by omega) hc hb
    zify
    nlinarith

/-- Fixed-ratio arithmetic pays the stronger classical criterion, with margin. -/
lemma ratio_margin (m q d : ℤ) (hq : 0≤q) (hdm : d≤m)
    (hd : 13*q≤8*d) (hm : 8*m≤25*q) (hdu : d≤2*q) :
    q^2≤16*(m*(2*d-m)-(2*q-d)^2) := by
  have hmlo : 13*q≤8*m := by omega
  have hgap : q≤8*(2*d-m) := by omega
  have hp := mul_le_mul hmlo hgap hq (show 0≤8*m by omega)
  have hsq : 64*(2*q-d)^2≤9*q^2 := by
    have hprod := mul_nonneg (show 0≤3*q-8*(2*q-d) by omega)
      (show 0≤3*q+8*(2*q-d) by omega)
    nlinarith
  nlinarith

/-- The same quantitative margin holds at the ACTUAL retained minimum degree. -/
theorem actual_minimum_margin (q : ℕ) {P Q : Finset V} (hcard : #P=#Q)
    (hne : P.Nonempty) (hm : 8*#P≤25*q)
    (hl : ∀ v∈P,13*q≤8*dg G Q v) (hr : ∀ v∈Q,13*q≤8*dg G P v)
    (hu : ∀ v∈P,dg G Q v<2*q) (hv : ∀ v∈Q,dg G P v<2*q) :
    ∃ δ : ℕ, ActualMinimum G δ P Q ∧ 13*q≤8*δ ∧ δ<2*q ∧
      (q:ℤ)^2≤16*((#P:ℤ)*(2*(δ:ℤ)-#P)-(2*(q:ℤ)-δ)^2) := by
  let S := (P.image (dg G Q)) ∪ (Q.image (dg G P))
  obtain ⟨v,hvP⟩ := hne
  have hS : S.Nonempty := ⟨dg G Q v,mem_union_left _ (mem_image_of_mem _ hvP)⟩
  obtain ⟨δ,hδ,hmin⟩ := exists_min_image S id hS
  have hleft : ∀ v∈P,δ≤dg G Q v := fun v hv =>
    hmin _ (mem_union_left _ (mem_image_of_mem _ hv))
  have hright : ∀ v∈Q,δ≤dg G P v := fun v hv =>
    hmin _ (mem_union_right _ (mem_image_of_mem _ hv))
  have hatt : (∃ v∈P,dg G Q v=δ) ∨ (∃ v∈Q,dg G P v=δ) := by
    rcases mem_union.mp hδ with hh | hh
    · exact Or.inl (mem_image.mp hh)
    · exact Or.inr (mem_image.mp hh)
  have hlow : 13*q≤8*δ := by
    rcases hatt with ⟨w,hw,he⟩ | ⟨w,hw,he⟩
    · simpa only [he] using hl w hw
    · simpa only [he] using hr w hw
  have hupp : δ<2*q := by
    rcases hatt with ⟨w,hw,he⟩ | ⟨w,hw,he⟩
    · simpa only [he] using hu w hw
    · simpa only [he] using hv w hw
  have hdm : δ≤#P := by
    have hh := hleft v hvP
    have hb := dg_le_card (G:=G) Q v
    omega
  refine ⟨δ,?_,hlow,hupp,?_⟩
  · simpa only [ActualMinimum] using
      And.intro hleft (And.intro hright hatt)
  · exact ratio_margin (#P) q δ (by positivity) (by exact_mod_cast hdm)
      (by exact_mod_cast hlow) (by exact_mod_cast hm) (by exact_mod_cast hupp.le)

/-- Factor on the exact original shores, using the derived stronger cut guard. -/
theorem dense_factor (q : ℕ) {P Q : Finset V} (hcard : #P=#Q)
    (hq : 8≤q) (hne : P.Nonempty) (hm : 8*#P≤25*q)
    (hl : ∀ v∈P,13*q≤8*dg G Q v) (hr : ∀ v∈Q,13*q≤8*dg G P v) :
    FactorOn q G P Q := by
  let d := (13*q+7)/8
  have hd : 13*q≤8*d := by dsimp [d]; omega
  have hdu : d≤2*q := by dsimp [d]; omega
  have hleft : ∀ v∈P,d≤dg G Q v := by
    intro v hv
    have hh := hl v hv
    dsimp [d]
    omega
  have hright : ∀ v∈Q,d≤dg G P v := by
    intro v hv
    have hh := hr v hv
    dsimp [d]
    omega
  obtain ⟨v,hv⟩ := hne
  have hdm : d≤#P := by have hh := hleft v hv; have hb := dg_le_card (G:=G) Q v; omega
  have hmargin : (q:ℤ)^2≤16*((#P:ℤ)*(2*(d:ℤ)-#P)-(2*(q:ℤ)-d)^2) := by
    exact ratio_margin (#P) q d (by positivity) (by exact_mod_cast hdm)
      (by exact_mod_cast hd) (by exact_mod_cast hm) (by exact_mod_cast hdu)
  have hc : (2*(q:ℤ)-d)^2≤(#P:ℤ)*(2*d-#P) := by nlinarith [sq_nonneg (q:ℤ)]
  exact B5Factor.exists_target_factor (k:=q) P Q hcard (dense_cuts q d hcard hc hleft hright)

end Erdos585.AllHFourthQuotaFailure
