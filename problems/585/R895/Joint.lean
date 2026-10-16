import R883.LocalB
import R895.LocalB
import R895.Global
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0000R895
open QB4 QB7SmallLobeR643 QB7S0002R869
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- One deficit on the entire original right ground, with fixed original port coefficients. -/
def jointDeficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (P L S T : Finset V) : ℤ :=
  4 * #(T ∩ L) + (ec G P (T ∩ S) : ℤ) - 2 * #(T ∩ S) - capped G P T

lemma joint_deficit_trace {P L S Y R : Finset V}
    (hLS : Disjoint L S) (hY : Y ⊆ L) (hR : R ⊆ S) :
    jointDeficit G P L S (Y ∪ R) = (ec G P R : ℤ) - rankTerm G P Y R - 2 * #R := by
  have hYL : (Y ∪ R) ∩ L = Y := by
    ext x
    simp only [mem_inter,mem_union]
    have hdis := disjoint_left.mp hLS
    have hy := @hY x
    have hr := @hR x
    tauto
  have hRS : (Y ∪ R) ∩ S = R := by
    ext x
    simp only [mem_inter,mem_union]
    have hdis := disjoint_left.mp hLS
    have hy := @hY x
    have hr := @hR x
    tauto
  unfold jointDeficit rankTerm
  rw [hYL,hRS]
  omega

/-- All sixteen traces follow from the original proper-support capped floor. -/
lemma joint_deficit_trace_bound {U W S P P' L L' Y R : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hY : Y ⊆ L) (hR : R ⊆ S) :
    jointDeficit G P L S (Y ∪ R) ≤ max 0 (df G U Y - 6) := by
  have hb := h.capped_rank_lower hi hY hR
  rw [joint_deficit_trace h.rightSep₁ hY hR]
  omega

lemma joint_deficit_ground_bound {U W S P P' L L' T : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hT : T ⊆ L ∪ S) :
    jointDeficit G P L S T ≤ max 0 (df G U (T ∩ L) - 6) := by
  have he : (T ∩ L) ∪ (T ∩ S) = T := by
    ext x
    simp only [mem_union,mem_inter]
    have ht := @hT x
    simp only [mem_union] at ht
    tauto
  have hb := joint_deficit_trace_bound h hi (inter_subset_right : T ∩ L ⊆ L)
    (inter_subset_right : T ∩ S ⊆ S)
  rw [he] at hb
  exact hb

lemma ec_modular_right (P A B : Finset V) :
    ec G P (A ∪ B) + ec G P (A ∩ B) = ec G P A + ec G P B := by
  unfold ec
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl (fun x hx => dg_union_add_dg_inter (G := G) A B x)

lemma joint_deficit_supermodular (P L S A B : Finset V) :
    jointDeficit G P L S A + jointDeficit G P L S B ≤
      jointDeficit G P L S (A ∪ B) + jointDeficit G P L S (A ∩ B) := by
  have hc := capped_submodular (G := G) P A B
  have huL : (A ∪ B) ∩ L = (A ∩ L) ∪ (B ∩ L) := by ext x; simp only [mem_inter,mem_union]; tauto
  have hiL : (A ∩ B) ∩ L = (A ∩ L) ∩ (B ∩ L) := by ext x; simp only [mem_inter]; tauto
  have huS : (A ∪ B) ∩ S = (A ∩ S) ∪ (B ∩ S) := by ext x; simp only [mem_inter,mem_union]; tauto
  have hiS : (A ∩ B) ∩ S = (A ∩ S) ∩ (B ∩ S) := by ext x; simp only [mem_inter]; tauto
  have hL := card_union_add_card_inter (A ∩ L) (B ∩ L)
  have hS := card_union_add_card_inter (A ∩ S) (B ∩ S)
  have he := ec_modular_right (G := G) P (A ∩ S) (B ∩ S)
  unfold jointDeficit
  rw [huL,hiL,huS,hiS]
  omega

lemma joint_deficit_le_two {U W S P P' L L' T : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L = 8) (hT : T ⊆ L ∪ S) : jointDeficit G P L S T ≤ 2 := by
  have hb := joint_deficit_ground_bound h hi hT
  have hm := df_le_of_subset (G := G) (inter_subset_right : T ∩ L ⊆ L)
    (fun y hy => hi.capW y (h.subsets.2.2.1 hy))
  omega

noncomputable def badJointMarkers (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P L S : Finset V) : Finset V :=
  (L.filter fun z => dg G U z < 6).filter fun z =>
    ∃ Y ⊆ L.erase z, ∃ R ⊆ S, #R ≤ 1 ∧ 1 ≤ jointDeficit G P L S (Y ∪ R)

lemma joint_bad_witness {U W S P P' L L' : Finset V} {z : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L = 8) (hz : z ∈ badJointMarkers G U P L S) :
    z ∈ L ∧ dg G U z = 5 ∧ ∃ T ⊆ L ∪ S, z ∉ T ∧ #(T ∩ S) ≤ 1 ∧
      jointDeficit G P L S T = 1 ∧ df G U (T ∩ L) = 7 := by
  obtain ⟨hzM,Y,hY,R,hR,hcard,hpos⟩ := mem_filter.mp hz
  obtain ⟨hzL,hdz⟩ := mem_filter.mp hzM
  have hYL : Y ⊆ L := hY.trans (erase_subset z L)
  have hb := joint_deficit_trace_bound h hi hYL hR
  have he : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hzL
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  have hnz : z ∉ Y ∪ R := by
    intro hh
    rcases mem_union.mp hh with hh|hh
    · exact (mem_erase.mp (hY hh)).1 rfl
    · exact disjoint_left.mp h.rightSep₁ hzL (hR hh)
  have hYL' : (Y ∪ R) ∩ L = Y := by
    ext x
    simp only [mem_inter,mem_union]
    have hd := disjoint_left.mp h.rightSep₁
    have hy := @hYL x
    have hr := @hR x
    tauto
  have hRS : (Y ∪ R) ∩ S = R := by
    ext x
    simp only [mem_inter,mem_union]
    have hd := disjoint_left.mp h.rightSep₁
    have hy := @hYL x
    have hr := @hR x
    tauto
  refine ⟨hzL,by omega,Y ∪ R,union_subset (hYL.trans subset_union_left) (hR.trans subset_union_right),
    hnz,by rwa [hRS],by omega,?_⟩
  rw [hYL']
  omega


lemma joint_omission_bound {U W S P P' L L' T : Finset V} {z : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L = 8) (hz : z ∈ L) (hdz : dg G U z < 6)
    (hT : T ⊆ L ∪ S) (hnz : z ∉ T) : jointDeficit G P L S T ≤ 1 := by
  have hb := joint_deficit_ground_bound h hi hT
  have hsub : T ∩ L ⊆ L.erase z := by
    intro y hy
    exact mem_erase.mpr ⟨fun he => hnz (he ▸ (mem_inter.mp hy).1),(mem_inter.mp hy).2⟩
  have he : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz
  have hm := df_le_of_subset (G := G) hsub
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  omega

lemma joint_two_omissions_bound {U W S P P' L L' T : Finset V} {z w : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L = 8) (hz : z ∈ L) (hw : w ∈ L) (hzw : z ≠ w)
    (hdz : dg G U z = 5) (hdw : dg G U w = 5)
    (hT : T ⊆ L ∪ S) (hnz : z ∉ T) (hnw : w ∉ T) : jointDeficit G P L S T ≤ 0 := by
  have hb := joint_deficit_ground_bound h hi hT
  have hsub : T ∩ L ⊆ (L.erase z).erase w := by
    intro y hy
    exact mem_erase.mpr ⟨fun he => hnw (he ▸ (mem_inter.mp hy).1),
      mem_erase.mpr ⟨fun he => hnz (he ▸ (mem_inter.mp hy).1),(mem_inter.mp hy).2⟩⟩
  have hez : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz
  have hew : df G U ((L.erase z).erase w) + (6-(dg G U w : ℤ)) = df G U (L.erase z) :=
    sum_erase_add (L.erase z) (fun y => 6-(dg G U y : ℤ)) (mem_erase.mpr ⟨hzw.symm,hw⟩)
  have hm := df_le_of_subset (G := G) hsub
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp (mem_erase.mp hy).2).2))
  omega

/-- All joint witnesses project into this one inclusion-minimal maximum-two support. -/
lemma joint_minimal_maximum {U W S P P' L L' : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L = 8) (hbad : 2 ≤ #(badJointMarkers G U P L S)) :
    ∃ K ⊆ L ∪ S, jointDeficit G P L S K = 2 ∧ #(K ∩ S) ≤ 2 ∧
      (∀ T ⊆ K, jointDeficit G P L S T = 2 → T = K) ∧
      ∀ z ∈ badJointMarkers G U P L S,
        z ∈ K ∧ ∃ T ⊆ K, z ∉ T ∧ #(T ∩ S) ≤ 1 ∧ jointDeficit G P L S T = 1 := by
  obtain ⟨z,hz,w,hw,hzw⟩ := Finset.one_lt_card.mp (by omega : 1 < #(badJointMarkers G U P L S))
  obtain ⟨hzL,hdz,A,hA,hnz,hAc,hdA,_⟩ := joint_bad_witness h hi hδ hz
  obtain ⟨hwL,hdw,B,hB,hnw,hBc,hdB,_⟩ := joint_bad_witness h hi hδ hw
  have hzero := joint_two_omissions_bound h hi hδ hzL hwL hzw hdz hdw
    (inter_subset_left.trans hA) (fun hh => hnz (mem_inter.mp hh).1) (fun hh => hnw (mem_inter.mp hh).2)
  have hup := joint_deficit_le_two h hi hδ (union_subset hA hB)
  have hsm := joint_deficit_supermodular (G := G) P L S A B
  have hmax : jointDeficit G P L S (A ∪ B) = 2 := by omega
  let C := (A ∪ B).powerset.filter fun K => jointDeficit G P L S K = 2
  have hC : C.Nonempty := ⟨A ∪ B,mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _),hmax⟩⟩
  obtain ⟨K,hK,hmin⟩ := exists_min_image C Finset.card hC
  obtain ⟨hKAB,hKd⟩ := mem_filter.mp hK
  have hKAB' := mem_powerset.mp hKAB
  have hKL : K ⊆ L ∪ S := hKAB'.trans (union_subset hA hB)
  have hminimal : ∀ T ⊆ K, jointDeficit G P L S T = 2 → T = K := by
    intro T hTK hTd
    apply eq_of_subset_of_card_le hTK
    exact hmin T (mem_filter.mpr ⟨mem_powerset.mpr (hTK.trans hKAB'),hTd⟩)
  have hport : #(K ∩ S) ≤ 2 := by
    have hsub : K ∩ S ⊆ (A ∩ S) ∪ (B ∩ S) := by
      intro x hx
      have hh := hKAB' (mem_inter.mp hx).1
      rcases mem_union.mp hh with ha|hb
      · exact mem_union_left _ (mem_inter.mpr ⟨ha,(mem_inter.mp hx).2⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hb,(mem_inter.mp hx).2⟩)
    have hc := card_le_card hsub
    have hu := card_union_le (A ∩ S) (B ∩ S)
    omega
  refine ⟨K,hKL,hKd,hport,hminimal,?_⟩
  intro v hv
  obtain ⟨hvL,hdv,Y,hY,hnv,hYc,hdY,_⟩ := joint_bad_witness h hi hδ hv
  have hvK : v ∈ K := by
    by_contra hn
    have hb := joint_omission_bound h hi hδ hvL (by omega) hKL hn
    omega
  have hIU := joint_omission_bound (T := Y ∩ K) h hi hδ hvL (by omega)
    (inter_subset_left.trans hY) (fun hh => hnv (mem_inter.mp hh).1)
  have hUU := joint_deficit_le_two h hi hδ (union_subset hY hKL)
  have hsm' := joint_deficit_supermodular (G := G) P L S Y K
  refine ⟨hvK,Y ∩ K,inter_subset_right,fun hh => hnv (mem_inter.mp hh).1,?_,by omega⟩
  exact (card_le_card (show (Y ∩ K) ∩ S ⊆ Y ∩ S from fun x hx => mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).1,(mem_inter.mp hx).2⟩)).trans hYc

lemma joint_projected_portions_disjoint {U W S P P' L L' K A B : Finset V} {z w : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L = 8) (hK : K ⊆ L ∪ S)
    (hmin : ∀ T ⊆ K, jointDeficit G P L S T = 2 → T = K)
    (hz : z ∈ badJointMarkers G U P L S) (hw : w ∈ badJointMarkers G U P L S)
    (hzw : z ≠ w) (hA : A ⊆ K) (hB : B ⊆ K) (hnz : z ∉ A) (hnw : w ∉ B)
    (hdA : jointDeficit G P L S A = 1) (hdB : jointDeficit G P L S B = 1) :
    A ∪ B = K ∧ Disjoint (K \ A) (K \ B) := by
  obtain ⟨hzL,hdz,_⟩ := joint_bad_witness h hi hδ hz
  obtain ⟨hwL,hdw,_⟩ := joint_bad_witness h hi hδ hw
  have hzero := joint_two_omissions_bound h hi hδ hzL hwL hzw hdz hdw
    ((inter_subset_left.trans hA).trans hK)
    (fun hh => hnz (mem_inter.mp hh).1) (fun hh => hnw (mem_inter.mp hh).2)
  have hup := joint_deficit_le_two h hi hδ ((union_subset hA hB).trans hK)
  have hsm := joint_deficit_supermodular (G := G) P L S A B
  have heq := hmin (A ∪ B) (union_subset hA hB) (by omega)
  refine ⟨heq,disjoint_left.mpr ?_⟩
  intro y hya hyb
  have hyK := (mem_sdiff.mp hya).1
  rw [← heq] at hyK
  rcases mem_union.mp hyK with hh|hh
  · exact (mem_sdiff.mp hya).2 hh
  · exact (mem_sdiff.mp hyb).2 hh


/-- Empty-trace deficit on actual original edges. -/
def emptyDeficit (G : SimpleGraph V) [DecidableRel G.Adj] (P Y : Finset V) : ℤ :=
  -rankTerm G P Y ∅
noncomputable def emptyHeavy (G : SimpleGraph V) [DecidableRel G.Adj] (P Y : Finset V) : Finset V :=
  P.filter fun x => 5 ≤ dg G Y x
noncomputable def badEmptyMarkers (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P L : Finset V) : Finset V :=
  (L.filter fun z => dg G U z < 6).filter fun z => ∃ Y ⊆ L.erase z, 1 ≤ emptyDeficit G P Y

lemma empty_deficit_bound {U W S P P' L L' Y : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hY : Y ⊆ L) :
    emptyDeficit G P Y ≤ max 0 (df G U Y - 6) := by
  have hb := h.capped_rank_lower hi hY (empty_subset S)
  simp only [card_empty,Nat.cast_zero,mul_zero,add_zero] at hb
  have he : ec G P (∅ : Finset V) = 0 := by simp [ec,dg]
  rw [he] at hb
  unfold emptyDeficit
  omega

lemma empty_heavy_accounting {U W S P P' L L' Y : Finset V}
    (h : Split G U W S P P' L L') (hY : Y ⊆ L) :
    let H := emptyHeavy G P Y
    let a : ℤ := #Y - #H
    let b : ℤ := ec G H ((L ∪ S) \ Y)
    emptyDeficit G P Y = df G U Y-2*a-df G W H-b ∧ gv G H Y = 6*a+2*df G W H+2*b := by
  dsimp only
  let H := emptyHeavy G P Y
  have hH : H ⊆ P := filter_subset _ _
  have hdegree : df G P Y = df G U Y := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (hY hy)]
  have hdeq := df_eq (G := G) P Y
  rw [hdegree,ec_comm] at hdeq
  have hfull : df G (L ∪ S) H = df G W H := by
    unfold df
    exact sum_congr rfl fun x hx => by rw [h.degree_left (hH hx)]
  have hf := df_eq (G := G) (L ∪ S) H
  rw [hfull] at hf
  have hcomp := ec_sdiff_add_right (G := G) (hY.trans (subset_union_left : L ⊆ L ∪ S)) H
  have hsplit := ec_sdiff_add_left (G := G) hH Y
  have hsum := sum_sdiff hH (f := fun x => min 4 (dg G Y x))
  have hhigh : (∑ x ∈ H, min 4 (dg G Y x)) = 4 * #H := by
    calc _ = ∑ _x ∈ H, 4 := by
          apply sum_congr rfl
          intro x hx
          exact min_eq_left (by have hh := (mem_filter.mp hx).2; omega)
      _ = _ := by simp [mul_comm]
  have hlow : (∑ x ∈ P \ H, min 4 (dg G Y x)) = ec G (P \ H) Y := by
    apply sum_congr rfl
    intro x hx
    have hn : ¬ 5 ≤ dg G Y x := by
      intro hh
      exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,hh⟩)
    exact min_eq_right (by omega)
  have hc : capped G P Y = 4 * #H + ec G (P \ H) Y := by unfold capped; omega
  unfold emptyDeficit rankTerm gv
  simp only [union_empty]
  change -(capped G P Y-4*(#Y : ℤ)) = df G U Y-2*((#Y : ℤ)-#H)-df G W H-
    (ec G H ((L ∪ S) \ Y) : ℤ) ∧
    6*((#H : ℤ)+#Y)-2*(ec G H Y : ℤ) =
    6*((#Y : ℤ)-#H)+2*df G W H+2*(ec G H ((L ∪ S) \ Y) : ℤ)
  constructor <;> omega

lemma empty_equality_geometry {U W S P P' L L' Y : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hY : Y ⊆ L)
    (hpos : 0 < emptyDeficit G P Y) (heq : emptyDeficit G P Y = df G U Y-6) :
    let H := emptyHeavy G P Y
    let a : ℤ := #Y-#H
    (a=2 ∨ a=3) ∧ df G W H + (ec G H ((L ∪ S) \ Y) : ℤ) = 6-2*a := by
  dsimp only
  let H := emptyHeavy G P Y
  have hH : H ⊆ P := filter_subset _ _
  obtain ⟨haccount,hpotential⟩ := empty_heavy_accounting h hY
  change emptyDeficit G P Y = df G U Y-2*((#Y : ℤ)-#H)-df G W H-
    (ec G H ((L ∪ S) \ Y) : ℤ) at haccount
  change gv G H Y = 6*((#Y : ℤ)-#H)+2*df G W H+2*(ec G H ((L ∪ S) \ Y) : ℤ) at hpotential
  have hen : 0 ≤ df G W H := df_nonneg fun x hx => hi.capU x (h.subsets.1 (hH hx))
  have hne : H.Nonempty := by
    by_contra hn
    have hempty : H=∅ := not_nonempty_iff_eq_empty.mp hn
    rw [hempty] at haccount
    have hmass : df G U Y ≤ 2*#Y := by
      unfold df
      calc _ ≤ ∑ _y ∈ Y, (2 : ℤ) := sum_le_sum fun y hy => by
             have := hi.minW y (h.subsets.2.2.1 (hY hy)); omega
        _ = _ := by simp [mul_comm]
    have he0 : df G W (∅ : Finset V)=0 := by simp [df]
    have hb0 : ec G (∅ : Finset V) ((L ∪ S) \ Y)=0 := by simp [ec]
    rw [he0,hb0] at haccount
    simp only [card_empty,Nat.cast_zero,sub_zero] at haccount
    omega
  obtain ⟨x,hx⟩ := hne
  have hh := (mem_filter.mp hx).2
  have hsize := hh.trans (dg_le_card Y x)
  have hpositive := card_pos.mpr (show H.Nonempty from ⟨x,hx⟩)
  have hfloor := h.local_floor hi hH (hY.trans subset_union_left) (by omega)
  change (((#Y : ℤ)-#H)=2 ∨ ((#Y : ℤ)-#H)=3) ∧ df G W H +
    (ec G H ((L ∪ S) \ Y) : ℤ) = 6-2*((#Y : ℤ)-#H)
  omega

lemma empty_global_bound {U W S P P' L L' Y : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L=8) (hY : Y ⊆ L) : emptyDeficit G P Y ≤ 2 := by
  have hb := empty_deficit_bound h hi hY
  have hm := df_le_of_subset (G := G) hY (fun y hy => hi.capW y (h.subsets.2.2.1 hy))
  omega

lemma empty_maximum_mass {U W S P P' L L' K : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L=8) (hK : K ⊆ L) (hKd : emptyDeficit G P K=2) : df G U K=8 := by
  have hb := empty_deficit_bound h hi hK
  have hm := df_le_of_subset (G := G) hK (fun y hy => hi.capW y (h.subsets.2.2.1 hy))
  omega

lemma empty_maximum_incoming {U W S P P' L L' K : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L=8) (hK : K ⊆ L) (hKd : emptyDeficit G P K=2) :
    let H := emptyHeavy G P K
    (ec G (P \ H) K : ℤ) = 4*((#K : ℤ)-#H)-2 := by
  dsimp only
  let H := emptyHeavy G P K
  have hH : H ⊆ P := filter_subset _ _
  have hm := empty_maximum_mass h hi hδ hK hKd
  have hdegree : df G P K = df G U K := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (hK hy)]
  have hd := df_eq (G := G) P K
  rw [hdegree,ec_comm] at hd
  have hrow : df G (L ∪ S) H = df G W H := by
    unfold df
    exact sum_congr rfl fun x hx => by rw [h.degree_left (hH hx)]
  have hr := df_eq (G := G) (L ∪ S) H
  rw [hrow] at hr
  have hcomp := ec_sdiff_add_right (G := G) (hK.trans (subset_union_left : L ⊆ L ∪ S)) H
  have hleft := ec_sdiff_add_left (G := G) hH K
  obtain ⟨ha,hb⟩ := empty_equality_geometry h hi hK (by omega) (by omega)
  change df G W H + (ec G H ((L ∪ S) \ K) : ℤ)=6-2*((#K : ℤ)-#H) at hb
  change (ec G (P \ H) K : ℤ) = 4*((#K : ℤ)-#H)-2
  omega

lemma empty_piece_charge {U W S P P' L L' K Y : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L=8) (hK : K ⊆ L) (hYK : Y ⊆ K)
    (hKd : emptyDeficit G P K=2) (hYd : emptyDeficit G P Y=1)
    (hYm : df G U Y=7) (hne : (K \ Y).Nonempty) :
    (if (#K : ℤ)-#(emptyHeavy G P K)=2 then 2 else 3) ≤ ec G (P \ emptyHeavy G P K) (K \ Y) := by
  let H := emptyHeavy G P K
  let H' := emptyHeavy G P Y
  let X := H \ H'
  let R := K \ Y
  let O := (L ∪ S) \ K
  let a : ℤ := #K-#H
  let ay : ℤ := #Y-#H'
  let ell : ℤ := (ec G X O : ℤ)+df G W X
  let m : ℤ := ec G (P \ H) R
  have hH : H ⊆ P := filter_subset _ _
  have hH' : H' ⊆ H := by
    intro x hx
    obtain ⟨hxP,hh⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hxP,hh.trans (dg_mono (G := G) hYK x)⟩
  have hX : X ⊆ P := sdiff_subset.trans hH
  have hR : R ⊆ L := sdiff_subset.trans hK
  have hmK := empty_maximum_mass h hi hδ hK hKd
  obtain ⟨ha,hb⟩ := empty_equality_geometry h hi hK (by omega) (by omega)
  obtain ⟨hay,hby⟩ := empty_equality_geometry h hi (hYK.trans hK) (by omega) (by omega)
  change a=2 ∨ a=3 at ha
  change ay=2 ∨ ay=3 at hay
  change df G W H + (ec G H O : ℤ)=6-2*a at hb
  change df G W H' + (ec G H' ((L ∪ S) \ Y) : ℤ)=6-2*ay at hby
  have hcardR := card_sdiff_add_card_eq_card hYK
  have hcardX := card_sdiff_add_card_eq_card hH'
  have hg : (#X : ℤ)-#R=ay-a := by dsimp [a,ay,X,R]; omega
  have hdis : Disjoint O R := by
    apply disjoint_left.mpr
    intro x hxO hxR
    exact (mem_sdiff.mp hxO).2 (mem_sdiff.mp hxR).1
  have hpartition : (L ∪ S) \ Y=O ∪ R := by
    ext x
    simp only [O,R,mem_sdiff,mem_union]
    have hY := @hYK x
    have hk := @hK x
    tauto
  have hby' := ec_union_right (G := G) hdis H'
  rw [← hpartition] at hby'
  have hb' := ec_sdiff_add_left (G := G) hH' O
  change ec G X O+ec G H' O=ec G H O at hb'
  have hepart := sum_sdiff hH' (f := fun x => 6-(dg G W x : ℤ))
  change df G W X+df G W H'=df G W H at hepart
  have hen := df_nonneg (G := G) (fun x hx => hi.capU x (h.subsets.1 (hX hx)))
  have he'n := df_nonneg (G := G) (fun x hx => hi.capU x (h.subsets.1 (hH (hH' hx))))
  have hcross : (ec G H' R : ℤ)=ell-2*(ay-a) := by dsimp [ell]; omega
  have hell : 0 ≤ ell := by dsimp [ell]; omega
  have hellcap : ell ≤ 6-2*a := by dsimp [ell]; omega
  have hcrossn : 0 ≤ ell-2*(ay-a) := by omega
  have hmassR : df G U R=1 := by
    have hh := sum_sdiff hYK (f := fun y => 6-(dg G U y : ℤ))
    change df G U R+df G U Y=df G U K at hh
    omega
  have hdegree : df G P R=df G U R := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (hR hy)]
  have hright := df_eq (G := G) P R
  rw [hdegree,hmassR,ec_comm] at hright
  have hrightsplit := ec_sdiff_add_left (G := G) hH R
  have hinnersplit := ec_sdiff_add_left (G := G) hH' R
  change ec G X R+ec G H' R=ec G H R at hinnersplit
  have hpotential : gv G X R=2*((ay-1)-(a-1))+2*m+2+2*ell := by
    unfold gv
    dsimp [m,ell]
    omega
  have hm := QB7S0001R883.singleton_piece_charge_numeric h hi hX hR (card_pos.mpr hne)
    (a := a-1) (ay := ay-1) (by omega) (by omega) (by omega) hell (by omega) (by omega) hpotential
  change (if a=2 then 2 else 3) ≤ ec G (P \ H) R
  split_ifs at * <;> omega


lemma joint_deficit_interior {P L S T : Finset V} (hLS : Disjoint L S) (hT : T ⊆ L) :
    jointDeficit G P L S T = emptyDeficit G P T := by
  have hh := joint_deficit_trace (G := G) (P := P) hLS hT (empty_subset S)
  simpa [emptyDeficit,ec,dg] using hh

lemma empty_projected_family_card {U W S P P' L L' K B : Finset V} {Y : V → Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hδ : df G U L=8)
    (hK : K ⊆ L) (hKd : emptyDeficit G P K=2)
    (hY : ∀ z ∈ B, Y z ⊆ K ∧ emptyDeficit G P (Y z)=1 ∧ df G U (Y z)=7 ∧ (K \ Y z).Nonempty)
    (hdis : Set.PairwiseDisjoint (↑B : Set V) (fun z => K \ Y z)) : #B ≤ 3 := by
  have hcharge : ∀ z ∈ B, (if (#K : ℤ)-#(emptyHeavy G P K)=2 then 2 else 3) ≤
      ec G (P \ emptyHeavy G P K) (K \ Y z) := by
    intro z hz
    obtain ⟨hsub,hd,hm,hne⟩ := hY z hz
    exact empty_piece_charge h hi hδ hK hsub hKd hd hm hne
  have hb := disjoint_charge_budget (G := G) (fun z hz => sdiff_subset : ∀ z ∈ B, K \ Y z ⊆ K) hdis hcharge
  have hm := empty_maximum_mass h hi hδ hK hKd
  obtain ⟨ha,he⟩ := empty_equality_geometry h hi hK (by omega) (by omega)
  have hin := empty_maximum_incoming h hi hδ hK hKd
  dsimp only at ha hin
  rcases ha with ha|ha
  · simp only [ha,↓reduceIte] at hb
    omega
  · simp only [ha,show ¬(3 : ℤ)=2 by omega,↓reduceIte] at hb
    omega

lemma empty_bad_witness {U W S P P' L L' : Finset V} {z : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hδ : df G U L=8) (hz : z ∈ badEmptyMarkers G U P L) :
    z ∈ L ∧ dg G U z=5 ∧ ∃ Y ⊆ L.erase z, emptyDeficit G P Y=1 ∧ df G U Y=7 := by
  obtain ⟨hzM,Y,hY,hpos⟩ := mem_filter.mp hz
  obtain ⟨hzL,hdz⟩ := mem_filter.mp hzM
  have hb := empty_deficit_bound h hi (hY.trans (erase_subset z L))
  have he : df G U (L.erase z)+(6-(dg G U z : ℤ))=df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hzL
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  exact ⟨hzL,by omega,Y,hY,by omega,by omega⟩

lemma empty_bad_joint_subset {U W S P P' L L' : Finset V}
    (h : Split G U W S P P' L L') : badEmptyMarkers G U P L ⊆ badJointMarkers G U P L S := by
  intro z hz
  obtain ⟨hzM,Y,hY,hpos⟩ := mem_filter.mp hz
  apply mem_filter.mpr
  refine ⟨hzM,Y,hY,∅,empty_subset S,by simp,?_⟩
  simpa only [union_empty,joint_deficit_interior h.rightSep₁ (hY.trans (erase_subset z L))] using hpos

/-- The empty D8 owner bound uses disjoint original incoming edges. -/
theorem empty_bad_eight_card {U W S P P' L L' : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hδ : df G U L=8) :
    #(badEmptyMarkers G U P L) ≤ 3 := by
  let B := badEmptyMarkers G U P L
  change #B ≤ 3
  by_cases hbad : 2 ≤ #B
  · obtain ⟨z,hz,w,hw,hzw⟩ := Finset.one_lt_card.mp (by omega : 1 < #B)
    obtain ⟨hzL,hdz,A,hA,hdA,_⟩ := empty_bad_witness h hi hδ hz
    obtain ⟨hwL,hdw,C,hC,hdC,_⟩ := empty_bad_witness h hi hδ hw
    have hAL : A ⊆ L := hA.trans (erase_subset z L)
    have hCL : C ⊆ L := hC.trans (erase_subset w L)
    have hnz : z ∉ A := fun hh => (mem_erase.mp (hA hh)).1 rfl
    have hnw : w ∉ C := fun hh => (mem_erase.mp (hC hh)).1 rfl
    have hzero := joint_two_omissions_bound (T := A ∩ C) h hi hδ hzL hwL hzw hdz hdw
      ((inter_subset_left.trans hAL).trans subset_union_left)
      (fun hh => hnz (mem_inter.mp hh).1) (fun hh => hnw (mem_inter.mp hh).2)
    have hup := joint_deficit_le_two h hi hδ ((union_subset hAL hCL).trans subset_union_left)
    have hsm := joint_deficit_supermodular (G := G) P L S A C
    simp only [joint_deficit_interior h.rightSep₁ hAL,joint_deficit_interior h.rightSep₁ hCL,
      joint_deficit_interior h.rightSep₁ (union_subset hAL hCL)] at hsm hup
    have hmax : emptyDeficit G P (A ∪ C)=2 := by omega
    let F := L.powerset.filter fun K => emptyDeficit G P K=2
    have hF : F.Nonempty := ⟨A ∪ C,mem_filter.mpr ⟨mem_powerset.mpr (union_subset hAL hCL),hmax⟩⟩
    obtain ⟨K,hK,hmin⟩ := exists_min_image F Finset.card hF
    obtain ⟨hKL,hKd⟩ := mem_filter.mp hK
    have hKL' := mem_powerset.mp hKL
    have hminimal : ∀ T ⊆ K, jointDeficit G P L S T=2 → T=K := by
      intro T hTK hTd
      rw [joint_deficit_interior h.rightSep₁ (hTK.trans hKL')] at hTd
      exact eq_of_subset_of_card_le hTK (hmin T (mem_filter.mpr ⟨mem_powerset.mpr (hTK.trans hKL'),hTd⟩))
    have hchoices : ∀ v ∈ B, v ∈ K ∧ ∃ Y ⊆ K, v ∉ Y ∧ emptyDeficit G P Y=1 ∧ df G U Y=7 := by
      intro v hv
      obtain ⟨hvL,hdv,T,hT,hdT,hmT⟩ := empty_bad_witness h hi hδ hv
      have hTL : T ⊆ L := hT.trans (erase_subset v L)
      have hnv : v ∉ T := fun hh => (mem_erase.mp (hT hh)).1 rfl
      have hvK : v ∈ K := by
        by_contra hn
        have hh := joint_omission_bound h hi hδ hvL (by omega) (hKL'.trans subset_union_left) hn
        rw [joint_deficit_interior h.rightSep₁ hKL'] at hh
        omega
      have hIU := joint_omission_bound (T := T ∩ K) h hi hδ hvL (by omega)
        ((inter_subset_left.trans hTL).trans subset_union_left) (fun hh => hnv (mem_inter.mp hh).1)
      have hUU := joint_deficit_le_two h hi hδ ((union_subset hTL hKL').trans subset_union_left)
      have hsm' := joint_deficit_supermodular (G := G) P L S T K
      simp only [joint_deficit_interior h.rightSep₁ hTL,joint_deficit_interior h.rightSep₁ hKL',
        joint_deficit_interior h.rightSep₁ (inter_subset_left.trans hTL)] at hsm' hIU
      have hId : emptyDeficit G P (T ∩ K)=1 := by omega
      have hm := empty_deficit_bound h hi (inter_subset_left.trans hTL : T ∩ K ⊆ L)
      have hmass := df_le_of_subset (G := G) (inter_subset_left : T ∩ K ⊆ T)
        (fun y hy => hi.capW y (h.subsets.2.2.1 (hTL hy)))
      exact ⟨hvK,T ∩ K,inter_subset_right,fun hh => hnv (mem_inter.mp hh).1,hId,by omega⟩
    let Y : V → Finset V := fun v => if hv : v ∈ B then Classical.choose (hchoices v hv).2 else ∅
    have hYs : ∀ v ∈ B, Y v ⊆ K ∧ v ∉ Y v ∧ emptyDeficit G P (Y v)=1 ∧ df G U (Y v)=7 := by
      intro v hv
      dsimp only [Y]
      rw [dif_pos hv]
      exact Classical.choose_spec (hchoices v hv).2
    have hdis : Set.PairwiseDisjoint (↑B : Set V) (fun v => K \ Y v) := by
      intro v hv w hw hvw
      obtain ⟨hvK,hnv,hdv,hmv⟩ := hYs v hv
      obtain ⟨hwK,hnw,hdw,hmw⟩ := hYs w hw
      exact (joint_projected_portions_disjoint h hi hδ (hKL'.trans subset_union_left) hminimal
        (empty_bad_joint_subset h hv) (empty_bad_joint_subset h hw) hvw hvK hwK hnv hnw
        (by rwa [joint_deficit_interior h.rightSep₁ (hvK.trans hKL')])
        (by rwa [joint_deficit_interior h.rightSep₁ (hwK.trans hKL')])).2
    apply empty_projected_family_card h hi hδ hKL' hKd _ hdis
    intro v hv
    obtain ⟨hvK,hnv,hdv,hmv⟩ := hYs v hv
    exact ⟨hvK,hdv,hmv,v,mem_sdiff.mpr ⟨(hchoices v hv).1,hnv⟩⟩
  · omega


/-- Disjoint nonempty portions cannot claim more port owners than physical ports. -/
lemma disjoint_port_owners_card {B K S : Finset V} {T : V → Finset V}
    (hport : ∀ z ∈ B, ((K \ T z) ∩ S).Nonempty)
    (hdis : Set.PairwiseDisjoint (↑B : Set V) (fun z => K \ T z)) : #B ≤ #(K ∩ S) := by
  let f : V → V := fun z => if hz : z ∈ B then Classical.choose (hport z hz) else z
  have hf : ∀ z ∈ B, f z ∈ (K \ T z) ∩ S := by
    intro z hz
    dsimp only [f]
    rw [dif_pos hz]
    exact Classical.choose_spec (hport z hz)
  apply card_le_card_of_injOn f
  · intro z hz
    have hh := mem_inter.mp (hf z hz)
    exact mem_inter.mpr ⟨(mem_sdiff.mp hh.1).1,hh.2⟩
  · intro z hz w hw heq
    by_contra hne
    have hd := hdis hz hw hne
    exact disjoint_left.mp hd (mem_inter.mp (hf z hz)).1 (heq ▸ (mem_inter.mp (hf w hw)).1)

lemma joint_projected_singleton_bad {U W S P P' L L' K T : Finset V} {z t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hδ : df G U L=8)
    (hK : K ⊆ L ∪ S) (hT : T ⊆ K) (hKS : K ∩ S={t})
    (htT : t ∈ T) (hnz : z ∉ T) (hz : z ∈ badJointMarkers G U P L S)
    (hTd : jointDeficit G P L S T=1) : z ∈ badSingletonMarkers G U P L t 8 := by
  obtain ⟨hzL,hdz,_⟩ := joint_bad_witness h hi hδ hz
  have htS : t ∈ S := (mem_inter.mp (show t ∈ K ∩ S by rw [hKS]; simp)).2
  have hTS : T ∩ S={t} := by
    apply eq_of_subset_of_card_le
    · rw [← hKS]
      exact fun x hx => mem_inter.mpr ⟨hT (mem_inter.mp hx).1,(mem_inter.mp hx).2⟩
    · have hh : t ∈ T ∩ S := mem_inter.mpr ⟨htT,htS⟩
      have hc := card_pos.mpr (show (T ∩ S).Nonempty from ⟨t,hh⟩)
      simp only [card_singleton]
      omega
  have hTL : T ∩ L ⊆ L.erase z := by
    intro x hx
    exact mem_erase.mpr ⟨fun he => hnz (he ▸ (mem_inter.mp hx).1),(mem_inter.mp hx).2⟩
  have he : (T ∩ L) ∪ {t}=T := by
    rw [← hTS]
    ext x
    simp only [mem_union,mem_inter]
    have hh := @hK x
    have hhT := @hT x
    simp only [mem_union] at hh
    tauto
  have hF := joint_deficit_trace (G := G) (P := P) h.rightSep₁
    (inter_subset_right : T ∩ L ⊆ L) (singleton_subset_iff.mpr htS)
  rw [he] at hF
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨hzL,by omega⟩,T ∩ L,hTL,?_⟩
  unfold singletonDeficit
  simp only [card_singleton] at hF
  omega

/-- One shared original obstruction set covers empty and all four singleton traces. -/
theorem joint_bad_eight_card {U W S P P' L L' : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hs : ∀ s ∈ S, dg G U s=6) (hδ : df G U L=8) :
    #(badJointMarkers G U P L S) ≤ 4 := by
  let B := badJointMarkers G U P L S
  change #B ≤ 4
  by_cases hbad : 2 ≤ #B
  · obtain ⟨K,hK,hKd,hport,hmin,hchoices⟩ := joint_minimal_maximum h hi hδ hbad
    let T : V → Finset V := fun z => if hz : z ∈ B then Classical.choose (hchoices z hz).2 else ∅
    have hTs : ∀ z ∈ B, T z ⊆ K ∧ z ∉ T z ∧ #(T z ∩ S) ≤ 1 ∧ jointDeficit G P L S (T z)=1 := by
      intro z hz
      dsimp only [T]
      rw [dif_pos hz]
      exact Classical.choose_spec (hchoices z hz).2
    have hdis : Set.PairwiseDisjoint (↑B : Set V) (fun z => K \ T z) := by
      intro z hz w hw hzw
      obtain ⟨hzK,hnz,hzc,hdz⟩ := hTs z hz
      obtain ⟨hwK,hnw,hwc,hdw⟩ := hTs w hw
      exact (joint_projected_portions_disjoint h hi hδ hK hmin hz hw hzw hzK hwK hnz hnw hdz hdw).2
    by_cases htwo : #(K ∩ S)=2
    · have hports : ∀ z ∈ B, ((K \ T z) ∩ S).Nonempty := by
        intro z hz
        by_contra hn
        have hsub : K ∩ S ⊆ T z ∩ S := by
          intro x hx
          have hxK := (mem_inter.mp hx).1
          have hxS := (mem_inter.mp hx).2
          by_cases hxt : x ∈ T z
          · exact mem_inter.mpr ⟨hxt,hxS⟩
          · exact False.elim (hn ⟨x,mem_inter.mpr ⟨mem_sdiff.mpr ⟨hxK,hxt⟩,hxS⟩⟩)
        have hh := card_le_card hsub
        have hc := (hTs z hz).2.2.1
        omega
      have hc := disjoint_port_owners_card hports hdis
      omega
    · by_cases hzero : K ∩ S=∅
      · have hKL : K ⊆ L := by
          intro x hx
          rcases mem_union.mp (hK hx) with hl|hS
          · exact hl
          · have hh : x ∈ K ∩ S := mem_inter.mpr ⟨hx,hS⟩
            rw [hzero] at hh
            simp at hh
        have hsub : B ⊆ badEmptyMarkers G U P L := by
          intro z hz
          obtain ⟨hzL,hdz,_⟩ := joint_bad_witness h hi hδ hz
          obtain ⟨hzK,hnz,hzc,hdzT⟩ := hTs z hz
          have hTL : T z ⊆ L.erase z := fun x hx => mem_erase.mpr ⟨fun he => hnz (he ▸ hx),hKL (hzK hx)⟩
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨hzL,by omega⟩,T z,hTL,
            by rw [← joint_deficit_interior h.rightSep₁ (hzK.trans hKL)]; omega⟩
        have hc := card_le_card hsub
        have he := empty_bad_eight_card h hi hδ
        omega
      · have hone : #(K ∩ S)=1 := by have hn := card_pos.mpr (nonempty_iff_ne_empty.mpr hzero); omega
        obtain ⟨t,hKS⟩ := card_eq_one.mp hone
        have htS : t ∈ S := (mem_inter.mp (show t ∈ K ∩ S by rw [hKS]; simp)).2
        let C := B.filter fun z => t ∉ T z
        have hC : #C ≤ 1 := by
          have hports : ∀ z ∈ C, ((K \ T z) ∩ S).Nonempty := by
            intro z hz
            obtain ⟨hzB,hnt⟩ := mem_filter.mp hz
            have htK : t ∈ K := (mem_inter.mp (show t ∈ K ∩ S by rw [hKS]; simp)).1
            exact ⟨t,mem_inter.mpr ⟨mem_sdiff.mpr ⟨htK,hnt⟩,htS⟩⟩
          have hd : Set.PairwiseDisjoint (↑C : Set V) (fun z => K \ T z) := by
            intro z hz w hw hzw
            exact hdis (mem_filter.mp hz).1 (mem_filter.mp hw).1 hzw
          have hc := disjoint_port_owners_card hports hd
          omega
        have hsub : B \ C ⊆ badSingletonMarkers G U P L t 8 := by
          intro z hz
          obtain ⟨hzB,hnC⟩ := mem_sdiff.mp hz
          obtain ⟨hzK,hnz,hzc,hdz⟩ := hTs z hzB
          have htT : t ∈ T z := by
            by_contra hn
            exact hnC (mem_filter.mpr ⟨hzB,hn⟩)
          exact joint_projected_singleton_bad h hi hδ hK hzK hKS htT hnz hzB hdz
        have hqsum := singleton_incidence_sum h htS hs
        have hqmin := (lobe_port_bounds h.swap hi htS).1
        have hq : ec G P {t} ≤ 5 := by omega
        have hsingle := singleton_bad_eight_card h hi htS hq hδ
        have hc := card_le_card hsub
        have hcard := card_sdiff_add_card_eq_card (filter_subset (fun z => t ∉ T z) B)
        change #(B \ C)+#C=#B at hcard
        omega
  · omega

lemma joint_bad_deficiency {U W S P P' L L' : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hδ : df G U L=8) :
    df G U (badJointMarkers G U P L S)=#(badJointMarkers G U P L S) := by
  unfold df
  calc _ = ∑ _z ∈ badJointMarkers G U P L S, (1 : ℤ) := by
         apply sum_congr rfl
         intro z hz
         have hd := (joint_bad_witness h hi hδ hz).2.1
         simp [hd]
       _ = _ := by simp

lemma joint_not_bad_rank {U P L S Y R : Finset V} {z : V}
    (hLS : Disjoint L S) (hz : z ∈ L) (hdz : dg G U z < 6)
    (hgood : z ∉ badJointMarkers G U P L S)
    (hY : Y ⊆ L.erase z) (hR : R ⊆ S) (hr : #R ≤ 1) :
    (ec G P R : ℤ)-2*#R ≤ rankTerm G P Y R := by
  have hn : ¬ 1 ≤ jointDeficit G P L S (Y ∪ R) := by
    intro hh
    exact hgood (mem_filter.mpr ⟨mem_filter.mpr ⟨hz,hdz⟩,Y,hY,R,hR,hr,hh⟩)
  rw [joint_deficit_trace hLS (hY.trans (erase_subset z L)) hR] at hn
  omega

lemma joint_bad_deficiency_le_four {U W S P P' L L' : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hs : ∀ s ∈ S, dg G U s=6) (hδ : df G U L=8) :
    df G U (badJointMarkers G U P L S) ≤ 4 := by
  rw [joint_bad_deficiency h hi hδ]
  exact_mod_cast joint_bad_eight_card h hi hs hδ

#print axioms joint_deficit_trace_bound
#print axioms joint_deficit_supermodular
#print axioms joint_minimal_maximum
#print axioms joint_projected_portions_disjoint
#print axioms empty_bad_eight_card
#print axioms joint_bad_eight_card
#print axioms joint_bad_deficiency_le_four
#print axioms joint_not_bad_rank
end Erdos585.QB7S0000R895
