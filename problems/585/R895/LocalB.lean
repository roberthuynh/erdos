/- R895: arbitrary-profile singleton projection and physical incoming charges.
The generic machinery through singleton_bad_subset is adapted from R883.LocalB,
which itself builds on R869.LocalB and R869.ChargeSum. The R895 addition is the
degree-six/seven/eight q table; no separator degree-five premise is used. -/
import R869.LocalB
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0000R895
open QB4 QB7SmallLobeR643 QB7S0002R869
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma singleton_equality_geometry {U W S P P' L L' Y : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hY : Y ⊆ L)
    (hpos : 0 < singletonDeficit G P Y t)
    (heq : singletonDeficit G P Y t = df G U Y - 4) :
    let H := singletonHeavy G P Y t
    let a : ℤ := #Y - #H
    let b : ℤ := ec G H ((L ∪ S) \ (Y ∪ {t}))
    (a = 1 ∨ a = 2) ∧ df G W H + b = 4-2*a ∧
      4 ≤ a + ec G H {t} := by
  dsimp only
  let H := singletonHeavy G P Y t
  have hH : H ⊆ P := filter_subset _ _
  obtain ⟨haccount,hpotential⟩ := singleton_heavy_accounting h ht hY
  change singletonDeficit G P Y t = df G U Y - 2*((#Y : ℤ)-#H)-df G W H-
    (ec G H ((L ∪ S) \ (Y ∪ {t})) : ℤ) at haccount
  change gv G H (Y ∪ {t}) = 6*((#Y : ℤ)-#H)+6+2*df G W H+
    2*(ec G H ((L ∪ S) \ (Y ∪ {t})) : ℤ) at hpotential
  have hepsn : 0 ≤ df G W H := df_nonneg fun x hx => hi.capU x (h.subsets.1 (hH hx))
  have hne : H.Nonempty := by
    by_contra hn
    have hempty : H = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [hempty] at haccount
    have hmass : df G U Y ≤ 2*#Y := by
      unfold df
      calc _ ≤ ∑ _y ∈ Y, (2 : ℤ) := sum_le_sum fun y hy => by
             have := hi.minW y (h.subsets.2.2.1 (hY hy)); omega
        _ = _ := by simp [mul_comm]
    have he0 : df G W (∅ : Finset V) = 0 := by simp [df]
    have hb0 : ec G (∅ : Finset V) ((L ∪ S) \ (Y ∪ {t})) = 0 := by simp [ec]
    rw [he0,hb0] at haccount
    simp only [card_empty,Nat.cast_zero,sub_zero] at haccount
    omega
  obtain ⟨x,hx⟩ := hne
  have hh := (mem_filter.mp hx).2
  have hsize := hh.trans (dg_le_card (Y ∪ {t}) x)
  have hpositive := card_pos.mpr (show H.Nonempty from ⟨x,hx⟩)
  have hfloor := h.local_floor hi hH
    (union_subset (hY.trans subset_union_left) ((singleton_subset_iff.mpr ht).trans subset_union_right))
    (by omega)
  have hdis : Disjoint Y ({t} : Finset V) := h.rightSep₁.mono hY (singleton_subset_iff.mpr ht)
  have hdeg := dg_union_of_disjoint (G := G) hdis x
  have hsing : dg G {t} x ≤ 1 := by simpa using dg_le_card (G := G) ({t} : Finset V) x
  have hYlarge : 4 ≤ #Y := by have := dg_le_card (G := G) Y x; omega
  have hfloor' := h.local_floor hi hH (hY.trans subset_union_left) (by omega)
  have hm := ec_mono_left (G := G) hH ({t} : Finset V)
  have hepsm := df_le_of_subset (G := G) (hH.trans h.subsets.1) hi.capU
  rw [hi.defU] at hepsm
  have hepsall := df_le_of_subset (G := G) hH (fun x hx => hi.capU x (h.subsets.1 hx))
  have heunion := ec_union_right (G := G) hdis H
  have hcard := card_union_of_disjoint hdis
  simp only [card_singleton] at hcard
  unfold gv at hfloor hfloor'
  unfold gv at hpotential
  change (((#Y : ℤ)-#H) = 1 ∨ ((#Y : ℤ)-#H) = 2) ∧ df G W H +
    (ec G H ((L ∪ S) \ (Y ∪ {t})) : ℤ) = 4-2*((#Y : ℤ)-#H) ∧
      4 ≤ ((#Y : ℤ)-#H) + (ec G H {t} : ℤ)
  omega

lemma singleton_global_bound {U W S P P' L L' Y : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hY : Y ⊆ L) (hδ : df G U L = D) (hD : 6 ≤ D) :
    singletonDeficit G P Y t ≤ D-4 := by
  have hb := singleton_deficit_bound h hi ht hY
  have hm := df_le_of_subset (G := G) hY (fun y hy => hi.capW y (h.subsets.2.2.1 hy))
  omega

lemma singleton_omission_bound {U W S P P' L L' Y : Finset V} {t z : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hz : z ∈ L) (hdz : dg G U z < 6)
    (hY : Y ⊆ L.erase z) (hδ : df G U L = D) (hD : 6 ≤ D) :
    singletonDeficit G P Y t ≤ D-5 := by
  have he : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  have hb := singleton_deficit_bound h hi ht (hY.trans (erase_subset z L))
  omega

noncomputable def badSingletonMarkers (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P L : Finset V) (t : V) (D : ℤ) : Finset V :=
  (L.filter fun z => dg G U z < 6).filter fun z =>
    ∃ Y ⊆ L.erase z, D-5 ≤ singletonDeficit G P Y t

lemma singleton_bad_witness {U W S P P' L L' : Finset V} {t z : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D)
    (hz : z ∈ badSingletonMarkers G U P L t D) :
    z ∈ L ∧ dg G U z = 5 ∧
      ∃ Y ⊆ L.erase z, singletonDeficit G P Y t = D-5 ∧ df G U Y = D-1 := by
  obtain ⟨hzM,Y,hY,hpos⟩ := mem_filter.mp hz
  obtain ⟨hzL,hdz⟩ := mem_filter.mp hzM
  have hu := singleton_omission_bound h hi ht hzL hdz hY hδ hD
  have hb := singleton_deficit_bound h hi ht (hY.trans (erase_subset z L))
  have he : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hzL
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  exact ⟨hzL,by omega,Y,hY,by omega,by omega⟩

lemma singleton_two_omissions_bound {U W S P P' L L' Y : Finset V} {t z w : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D)
    (hz : z ∈ L) (hw : w ∈ L) (hzw : z ≠ w)
    (hdz : dg G U z = 5) (hdw : dg G U w = 5)
    (hY : Y ⊆ (L.erase z).erase w) :
    singletonDeficit G P Y t ≤ D-6 := by
  have hez : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz
  have hew : df G U ((L.erase z).erase w) + (6-(dg G U w : ℤ)) = df G U (L.erase z) :=
    sum_erase_add (L.erase z) (fun y => 6-(dg G U y : ℤ)) (mem_erase.mpr ⟨hzw.symm,hw⟩)
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp (mem_erase.mp hy).2).2))
  have hb := singleton_deficit_bound h hi ht
    (hY.trans ((erase_subset w (L.erase z)).trans (erase_subset z L)))
  omega

lemma singleton_minimal_maximum {U W S P P' L L' : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D)
    (hbad : 2 ≤ #(badSingletonMarkers G U P L t D)) :
    ∃ K ⊆ L, singletonDeficit G P K t = D-4 ∧
      (∀ T ⊆ K, singletonDeficit G P T t = D-4 → T = K) ∧
      ∀ z ∈ badSingletonMarkers G U P L t D,
        ∃ Y ⊆ K, z ∉ Y ∧ singletonDeficit G P Y t = D-5 ∧ df G U Y = D-1 := by
  obtain ⟨z,hz,w,hw,hzw⟩ := Finset.one_lt_card.mp (by omega : 1 < #(badSingletonMarkers G U P L t D))
  obtain ⟨hzL,hdz,A,hA,hdA,hmA⟩ := singleton_bad_witness h hi ht hδ hD hz
  obtain ⟨hwL,hdw,B,hB,hdB,hmB⟩ := singleton_bad_witness h hi ht hδ hD hw
  have hAB : A ∩ B ⊆ (L.erase z).erase w := by
    intro y hy
    obtain ⟨hya,hyb⟩ := mem_inter.mp hy
    exact mem_erase.mpr ⟨(mem_erase.mp (hB hyb)).1,hA hya⟩
  have hzero := singleton_two_omissions_bound h hi ht hδ hD hzL hwL hzw hdz hdw hAB
  have hjoin : A ∪ B ⊆ L := union_subset (hA.trans (erase_subset z L)) (hB.trans (erase_subset w L))
  have hup := singleton_global_bound h hi ht hjoin hδ hD
  have hsm := singleton_deficit_supermodular (G := G) P A B t
  have hmax : singletonDeficit G P (A ∪ B) t = D-4 := by omega
  let C := L.powerset.filter fun K => singletonDeficit G P K t = D-4
  have hC : C.Nonempty := ⟨A ∪ B,mem_filter.mpr ⟨mem_powerset.mpr hjoin,hmax⟩⟩
  obtain ⟨K,hK,hmin⟩ := exists_min_image C Finset.card hC
  obtain ⟨hKL,hKd⟩ := mem_filter.mp hK
  have hKL' := mem_powerset.mp hKL
  have hminimal : ∀ T ⊆ K, singletonDeficit G P T t = D-4 → T = K := by
    intro T hTK hTd
    apply eq_of_subset_of_card_le hTK
    exact hmin T (mem_filter.mpr ⟨mem_powerset.mpr (hTK.trans hKL'),hTd⟩)
  refine ⟨K,hKL',hKd,hminimal,?_⟩
  intro v hv
  obtain ⟨hvL,hdv,Y,hY,hdY,hmY⟩ := singleton_bad_witness h hi ht hδ hD hv
  have hI : Y ∩ K ⊆ L.erase v := inter_subset_left.trans hY
  have hIU := singleton_omission_bound h hi ht hvL (by omega) hI hδ hD
  have hUU := singleton_global_bound h hi ht
    (union_subset (hY.trans (erase_subset v L)) hKL') hδ hD
  have hsm' := singleton_deficit_supermodular (G := G) P Y K t
  have hId : singletonDeficit G P (Y ∩ K) t = D-5 := by omega
  have hmass := singleton_deficit_bound h hi ht (hI.trans (erase_subset v L))
  have he : df G U (L.erase v) + (6-(dg G U v : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hvL
  have hm := df_le_of_subset (G := G) hI
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  exact ⟨Y ∩ K,inter_subset_right,
    fun hh => (mem_erase.mp (hI hh)).1 rfl,hId,by omega⟩

lemma singleton_maximum_witness_union {U W S P P' L L' K A B : Finset V} {t z w : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D) (hK : K ⊆ L)
    (hmin : ∀ T ⊆ K, singletonDeficit G P T t = D-4 → T = K)
    (hz : z ∈ L) (hw : w ∈ L) (hzw : z ≠ w)
    (hdz : dg G U z = 5) (hdw : dg G U w = 5)
    (hA : A ⊆ K) (hB : B ⊆ K) (hnz : z ∉ A) (hnw : w ∉ B)
    (hdA : singletonDeficit G P A t = D-5) (hdB : singletonDeficit G P B t = D-5) :
    A ∪ B = K ∧ Disjoint (K \ A) (K \ B) := by
  have hAB : A ∩ B ⊆ (L.erase z).erase w := by
    intro y hy
    obtain ⟨hya,hyb⟩ := mem_inter.mp hy
    exact mem_erase.mpr ⟨fun hh => hnw (hh ▸ hyb),
      mem_erase.mpr ⟨fun hh => hnz (hh ▸ hya),hK (hA hya)⟩⟩
  have hzero := singleton_two_omissions_bound h hi ht hδ hD hz hw hzw hdz hdw hAB
  have hjoin : A ∪ B ⊆ K := union_subset hA hB
  have hup := singleton_global_bound h hi ht (hjoin.trans hK) hδ hD
  have hsm := singleton_deficit_supermodular (G := G) P A B t
  have heq := hmin (A ∪ B) hjoin (by omega)
  refine ⟨heq,disjoint_left.mpr ?_⟩
  intro y hya hyb
  have hyK := (mem_sdiff.mp hya).1
  rw [← heq] at hyK
  rcases mem_union.mp hyK with hh|hh
  · exact (mem_sdiff.mp hya).2 hh
  · exact (mem_sdiff.mp hyb).2 hh

lemma singleton_port_scar {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 5) :
    (ec G P {t} : ℤ) + df G W P ≤ 4 := by
  have hlarge := h.swap.left_large hi
  have hf := h.swap.local_floor hi (Subset.refl P')
    (union_subset subset_union_left ((erase_subset t S).trans subset_union_right))
    (by have := card_le_card (subset_union_left : L' ⊆ L' ∪ S.erase t); omega)
  have hbal := h.swap.local_balance hi
  have hS : #(S.erase t) = 3 := by rw [card_erase_of_mem ht,h.cardS]
  have hd : Disjoint L' (S.erase t) := h.rightSep₂.mono_right (erase_subset t S)
  have he := ec_union_right (G := G) hd P'
  have her := ec_erase_right (G := G) (P := P') ht
  have hefull := ec_union_right (G := G) h.rightSep₂ P'
  have hdf : df G (L' ∪ S) P' = df G W P' := by
    unfold df
    exact sum_congr rfl fun x hx => by rw [h.swap.degree_left hx]
  have hdeq := df_eq (G := G) (L' ∪ S) P'
  rw [hdf] at hdeq
  have hsum : df G W P + df G W P' = 1 := by
    have hh := sum_union h.leftDisjoint (f := fun x => 6-(dg G W x : ℤ))
    change df G W (P ∪ P') = df G W P + df G W P' at hh
    rw [h.leftCover,hi.defU] at hh
    omega
  have hport := dg_union_of_disjoint (G := G) h.leftDisjoint t
  rw [h.leftCover,hdt] at hport
  have hept : ec G P {t} = dg G P t := by rw [ec_comm]; simp [ec]
  unfold gv at hf
  rw [card_union_of_disjoint hd,hS,he] at hf
  omega

lemma singleton_maximum_mass {U W S P P' L L' K : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D) (hK : K ⊆ L)
    (hKd : singletonDeficit G P K t = D-4) : df G U K = D := by
  have hm := df_le_of_subset (G := G) hK (fun y hy => hi.capW y (h.subsets.2.2.1 hy))
  have hb := singleton_deficit_bound h hi ht hK
  omega

lemma singleton_maximum_incoming {U W S P P' L L' K : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D)
    (hK : K ⊆ L) (hKd : singletonDeficit G P K t = D-4) :
    let H := singletonHeavy G P K t
    (ec G (P \ H) K : ℤ) = 6*((#K : ℤ)-#H)-D+df G W H+
      ec G H {t}+ec G H ((L ∪ S) \ (K ∪ {t})) := by
  dsimp only
  let H := singletonHeavy G P K t
  have hH : H ⊆ P := filter_subset _ _
  have hm := singleton_maximum_mass h hi ht hδ hD hK hKd
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
  have hT : K ∪ {t} ⊆ L ∪ S := union_subset (hK.trans subset_union_left)
    ((singleton_subset_iff.mpr ht).trans subset_union_right)
  have hcomp := ec_sdiff_add_right (G := G) hT H
  have hdis := h.rightSep₁.mono hK (singleton_subset_iff.mpr ht)
  have hpart := ec_union_right (G := G) hdis H
  have hleft := ec_sdiff_add_left (G := G) hH K
  change (ec G (P \ H) K : ℤ) = 6*((#K : ℤ)-#H)-D+df G W H+
    ec G H {t}+ec G H ((L ∪ S) \ (K ∪ {t}))
  omega

lemma singleton_piece_charge_numeric {U W S P P' L L' X R : Finset V}
    {a ay ell m : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hX : X ⊆ P) (hR : R ⊆ L) (hr : 1 ≤ #R)
    (ha : a = 1 ∨ a = 2) (hay : ay = 1 ∨ ay = 2)
    (hg : (#X : ℤ)-#R = ay-a)
    (he0 : 0 ≤ ell) (hecap : ell ≤ 4-2*a) (hen : 0 ≤ ell-2*(ay-a))
    (hpotential : gv G X R = 2*(ay-a)+2*m+2+2*ell) : (if a = 1 then 2 else 3) ≤ m := by
  by_cases hlarge : 4 ≤ #X+#R
  · have hf := h.local_floor hi hX (hR.trans subset_union_left) hlarge
    omega
  · have hcases : (#X = 0 ∧ #R = 1) ∨ (#X = 1 ∧ #R = 1) ∨
        (#X = 1 ∧ #R = 2) ∨ (#X = 2 ∧ #R = 1) := by omega
    have he := ec_product_bound (G := G) X R
    unfold gv at hpotential
    rcases hcases with ⟨hx,hr⟩|⟨hx,hr⟩|⟨hx,hr⟩|⟨hx,hr⟩ <;>
      rw [hx,hr] at hpotential he hg <;> norm_num at hpotential he hg <;> omega

lemma singleton_piece_charge {U W S P P' L L' K Y : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D)
    (hK : K ⊆ L) (hYK : Y ⊆ K)
    (hKd : singletonDeficit G P K t = D-4)
    (hYd : singletonDeficit G P Y t = D-5) (hYm : df G U Y = D-1)
    (hne : (K \ Y).Nonempty) :
    (if (#K : ℤ)-#(singletonHeavy G P K t) = 1 then 2 else 3) ≤
      ec G (P \ singletonHeavy G P K t) (K \ Y) := by
  let H := singletonHeavy G P K t
  let H' := singletonHeavy G P Y t
  let X := H \ H'
  let R := K \ Y
  let O := (L ∪ S) \ (K ∪ {t})
  let a : ℤ := #K-#H
  let ay : ℤ := #Y-#H'
  let ell : ℤ := (ec G X O : ℤ) + df G W X
  let m : ℤ := ec G (P \ H) R
  have hH : H ⊆ P := filter_subset _ _
  have hH' : H' ⊆ H := singleton_heavy_mono (G := G) hYK
  have hX : X ⊆ P := sdiff_subset.trans hH
  have hR : R ⊆ L := sdiff_subset.trans hK
  have hmK := singleton_maximum_mass h hi ht hδ hD hK hKd
  obtain ⟨ha,hb,hτ⟩ := singleton_equality_geometry h hi ht hK (by omega) (by omega)
  obtain ⟨hay,hby,hτy⟩ := singleton_equality_geometry h hi ht (hYK.trans hK) (by omega) (by omega)
  change a = 1 ∨ a = 2 at ha
  change ay = 1 ∨ ay = 2 at hay
  change df G W H + (ec G H O : ℤ) = 4-2*a at hb
  change df G W H' + (ec G H' ((L ∪ S) \ (Y ∪ {t})) : ℤ) = 4-2*ay at hby
  have hcardR := card_sdiff_add_card_eq_card hYK
  have hcardX := card_sdiff_add_card_eq_card hH'
  have hg : (#X : ℤ)-#R = ay-a := by dsimp [a,ay,X,R]; omega
  have hO : O ⊆ (L ∪ S) := sdiff_subset
  have hdis : Disjoint O R := by
    apply disjoint_left.mpr
    intro x hxO hxR
    exact (mem_sdiff.mp hxO).2 (mem_union_left _ (mem_sdiff.mp hxR).1)
  have hpartition : (L ∪ S) \ (Y ∪ {t}) = O ∪ R := by
    ext x
    simp only [O,R,mem_sdiff,mem_union,mem_singleton]
    have hY := @hYK x
    have hKL := @hK x
    have htK : t ∉ K := fun hh => disjoint_left.mp h.rightSep₁ (hK hh) ht
    have hxt : x ∈ K → x ≠ t := fun hh he => htK (he ▸ hh)
    tauto
  have hby' := ec_union_right (G := G) hdis H'
  rw [← hpartition] at hby'
  have hb' := ec_sdiff_add_left (G := G) hH' O
  change ec G X O + ec G H' O = ec G H O at hb'
  have hepart := sum_sdiff hH' (f := fun x => 6-(dg G W x : ℤ))
  change df G W X + df G W H' = df G W H at hepart
  have hen := df_nonneg (G := G) (fun x hx => hi.capU x (h.subsets.1 (hX hx)))
  have he'n := df_nonneg (G := G) (fun x hx => hi.capU x (h.subsets.1 (hH (hH' hx))))
  have hcross : (ec G H' R : ℤ) = ell-2*(ay-a) := by dsimp [ell]; omega
  have hell : 0 ≤ ell := by dsimp [ell]; omega
  have hellcap : ell ≤ 4-2*a := by dsimp [ell]; omega
  have hcrossn : 0 ≤ ell-2*(ay-a) := by omega
  have hmassR : df G U R = 1 := by
    have hh := sum_sdiff hYK (f := fun y => 6-(dg G U y : ℤ))
    change df G U R + df G U Y = df G U K at hh
    omega
  have hdegree : df G P R = df G U R := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (hR hy)]
  have hright := df_eq (G := G) P R
  rw [hdegree,hmassR,ec_comm] at hright
  have hrightsplit := ec_sdiff_add_left (G := G) hH R
  have hinnersplit := ec_sdiff_add_left (G := G) hH' R
  change ec G X R + ec G H' R = ec G H R at hinnersplit
  have hpotential : gv G X R = 2*(ay-a)+2*m+2+2*ell := by
    unfold gv
    dsimp [m,ell]
    omega
  have hm := singleton_piece_charge_numeric h hi hX hR (card_pos.mpr hne)
    ha hay hg hell hellcap hcrossn hpotential
  change (if a = 1 then 2 else 3) ≤ (ec G (P \ H) R : ℤ) at hm
  change (if a = 1 then 2 else 3) ≤ ec G (P \ H) R
  split_ifs at * <;> omega

/-- A minimum maximizer gives disjoint original right portions for every bad marker. -/
lemma singleton_bad_charge_budget {U W S P P' L L' : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D)
    (hbad : 2 ≤ #(badSingletonMarkers G U P L t D)) :
    ∃ K ⊆ L, singletonDeficit G P K t = D-4 ∧
      let H := singletonHeavy G P K t
      let a : ℤ := #K-#H
      (a = 1 ∨ a = 2) ∧ 4 ≤ a + ec G H {t} ∧
      ((if a = 1 then 2 else 3) * #(badSingletonMarkers G U P L t D) : ℕ) ≤
        ec G (P \ H) K ∧
      (ec G (P \ H) K : ℤ) = 4*a+4-D+ec G H {t} := by
  let B := badSingletonMarkers G U P L t D
  obtain ⟨K,hK,hKd,hmin,hchoices⟩ := singleton_minimal_maximum h hi ht hδ hD hbad
  let Y : V → Finset V := fun z => if hz : z ∈ B then Classical.choose (hchoices z hz) else ∅
  have hYs : ∀ z ∈ B, Y z ⊆ K ∧ z ∉ Y z ∧ singletonDeficit G P (Y z) t = D-5 ∧ df G U (Y z) = D-1 := by
    intro z hz
    dsimp only [Y]
    rw [dif_pos hz]
    exact Classical.choose_spec (hchoices z hz)
  let R : V → Finset V := fun z => K \ Y z
  have hR : ∀ z ∈ B, R z ⊆ K := fun z hz => sdiff_subset
  have hvertices : ∀ z ∈ B, z ∈ L ∧ dg G U z = 5 := by
    intro z hz
    exact (singleton_bad_witness h hi ht hδ hD hz).imp_right And.left
  have hRne : ∀ z ∈ B, (R z).Nonempty := by
    intro z hz
    obtain ⟨hzL,hdz⟩ := hvertices z hz
    have hzK : z ∈ K := by
      by_contra hnot
      have hKe : K ⊆ L.erase z := by
        intro y hy
        exact mem_erase.mpr ⟨fun hh => hnot (hh ▸ hy),hK hy⟩
      have hh := singleton_omission_bound h hi ht hzL (by omega) hKe hδ hD
      omega
    exact ⟨z,mem_sdiff.mpr ⟨hzK,(hYs z hz).2.1⟩⟩
  have hdis : Set.PairwiseDisjoint (↑B : Set V) R := by
    intro z hz w hw hzw
    obtain ⟨hzL,hdz⟩ := hvertices z hz
    obtain ⟨hwL,hdw⟩ := hvertices w hw
    obtain ⟨hYz,hnz,hdYz,_⟩ := hYs z hz
    obtain ⟨hYw,hnw,hdYw,_⟩ := hYs w hw
    exact (singleton_maximum_witness_union h hi ht hδ hD hK hmin
      hzL hwL hzw hdz hdw hYz hYw hnz hnw hdYz hdYw).2
  have hcharge : ∀ z ∈ B, (if (#K : ℤ)-#(singletonHeavy G P K t) = 1 then 2 else 3) ≤
      ec G (P \ singletonHeavy G P K t) (R z) := by
    intro z hz
    obtain ⟨hY,hnz,hdY,hmY⟩ := hYs z hz
    exact singleton_piece_charge h hi ht hδ hD hK hY hKd hdY hmY (hRne z hz)
  have hbudget := disjoint_charge_budget (G := G) hR hdis hcharge
  obtain ⟨ha,hb,hτ⟩ := singleton_equality_geometry h hi ht hK (by omega)
    (by have hm := singleton_maximum_mass h hi ht hδ hD hK hKd; omega)
  have hincoming := singleton_maximum_incoming h hi ht hδ hD hK hKd
  refine ⟨K,hK,hKd,ha,hτ,hbudget,?_⟩
  dsimp only at *
  omega

lemma singleton_bad_deficiency {U W S P P' L L' : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D) :
    df G U (badSingletonMarkers G U P L t D) = #(badSingletonMarkers G U P L t D) := by
  unfold df
  calc _ = ∑ _z ∈ badSingletonMarkers G U P L t D, (1 : ℤ) := by
         apply sum_congr rfl
         intro z hz
         have hd := (singleton_bad_witness h hi ht hδ hD hz).2.1
         simp [hd]
       _ = _ := by simp

lemma singleton_not_bad_rank {U P L Y : Finset V} {t z : V} {D : ℤ}
    (hz : z ∈ L) (hdz : dg G U z < 6)
    (hgood : z ∉ badSingletonMarkers G U P L t D) (hY : Y ⊆ L.erase z) :
    (ec G P {t} : ℤ)-(D-6) ≤ rankTerm G P Y {t} := by
  have hn : ¬ D-5 ≤ singletonDeficit G P Y t := by
    intro hh
    exact hgood (mem_filter.mpr ⟨mem_filter.mpr ⟨hz,hdz⟩,Y,hY,hh⟩)
  unfold singletonDeficit at hn
  omega

lemma singleton_bad_subset (U P L : Finset V) (t : V) (D : ℤ) :
    badSingletonMarkers G U P L t D ⊆ QB7ProfileFreeR854.deficientMarkers G U L :=
  filter_subset _ _

theorem singleton_bad_card_bound {U W S P P' L L' : Finset V} {t : V} {D : ℤ} {n : ℕ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : 6 ≤ D) (hn : 1 ≤ n)
    (hlow : 3 ≤ ec G P {t} → 8-D+(ec G P {t} : ℤ) < 2*((n : ℤ)+1))
    (hhigh : 12-D+(ec G P {t} : ℤ) < 3*((n : ℤ)+1)) :
    #(badSingletonMarkers G U P L t D) ≤ n := by
  by_cases hbad : 2 ≤ #(badSingletonMarkers G U P L t D)
  · obtain ⟨K,hK,hKd,ha,hτ,hbudget,hincoming⟩ := singleton_bad_charge_budget h hi ht hδ hD hbad
    have hm := ec_mono_left (G := G) (filter_subset _ _ : singletonHeavy G P K t ⊆ P) ({t} : Finset V)
    change ec G (singletonHeavy G P K t) {t} ≤ ec G P {t} at hm
    change 4 ≤ ((#K : ℤ)-#(singletonHeavy G P K t)) + ec G (singletonHeavy G P K t) {t} at hτ
    change (ec G (P \ singletonHeavy G P K t) K : ℤ) =
      4*((#K : ℤ)-#(singletonHeavy G P K t))+4-D+ec G (singletonHeavy G P K t) {t} at hincoming
    rcases ha with ha|ha
    · simp only [ha,↓reduceIte] at hbudget
      have hh := hlow (by omega)
      omega
    · simp only [ha,show ¬(2 : ℤ) = 1 by omega,↓reduceIte] at hbudget
      omega
  · omega

/-- R881 Section 5 bounds on actual singleton bad-marker sets. -/
def singletonCardBound (D : ℤ) (q : ℕ) : ℕ :=
  if D = 6 then (if q ≤ 2 then 2 else 3)
  else if D = 7 then (if q ≤ 3 then 2 else 3)
  else (if q ≤ 4 then 2 else 3)

theorem singleton_bad_table {U W S P P' L L' : Finset V} {t : V} {D : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = D) (hD : D = 6 ∨ D = 7 ∨ D = 8)
    (hq : ec G P {t} ≤ 5) :
    #(badSingletonMarkers G U P L t D) ≤ singletonCardBound D (ec G P {t}) := by
  apply singleton_bad_card_bound h hi ht hδ (by omega)
  · unfold singletonCardBound
    split_ifs <;> omega
  · intro hh
    unfold singletonCardBound
    split_ifs <;> omega
  · unfold singletonCardBound
    split_ifs <;> omega

theorem singleton_bad_eight_card {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hq : ec G P {t} ≤ 5) (hδ : df G U L = 8) :
    #(badSingletonMarkers G U P L t 8) ≤ 3 := by
  have hh := singleton_bad_table h hi ht hδ (by omega) hq
  unfold singletonCardBound at hh
  split_ifs at hh <;> omega

#print axioms singleton_bad_table
#print axioms singleton_bad_eight_card



end Erdos585.QB7S0000R895
