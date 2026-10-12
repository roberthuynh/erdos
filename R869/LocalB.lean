import R854.ProfileFree
import R869.ChargeSum
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0002R869
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- Positive values are precisely failed original singleton capped cuts. -/
def singletonDeficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Y : Finset V) (t : V) : ℤ :=
  (ec G P {t} : ℤ) - rankTerm G P Y {t}

lemma singleton_deficit_bound {U W S P P' L L' Y : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hY : Y ⊆ L) :
    singletonDeficit G P Y t ≤ max 0 (df G U Y - 4) := by
  have hh := h.capped_rank_lower hi hY (singleton_subset_iff.mpr ht)
  simp only [card_singleton] at hh
  unfold singletonDeficit
  omega

lemma singleton_rank_of_mass_le_four {U W S P P' L L' Y : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hY : Y ⊆ L) (hδ : df G U Y ≤ 4) :
    (ec G P {t} : ℤ) ≤ rankTerm G P Y {t} := by
  have hh := singleton_deficit_bound h hi ht hY
  have hmax : max 0 (df G U Y - 4) = 0 := max_eq_left (by omega)
  rw [hmax] at hh
  unfold singletonDeficit at hh
  omega

lemma capped_submodular (P A B : Finset V) :
    capped G P (A ∪ B) + capped G P (A ∩ B) ≤ capped G P A + capped G P B := by
  unfold capped
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro x hx
  have hd := dg_union_add_dg_inter (G := G) A B x
  have huA := dg_mono (G := G) (subset_union_left : A ⊆ A ∪ B) x
  have huB := dg_mono (G := G) (subset_union_right : B ⊆ A ∪ B) x
  have hiA := dg_mono (G := G) (inter_subset_left : A ∩ B ⊆ A) x
  have hiB := dg_mono (G := G) (inter_subset_right : A ∩ B ⊆ B) x
  omega

lemma singleton_deficit_supermodular (P A B : Finset V) (t : V) :
    singletonDeficit G P A t + singletonDeficit G P B t ≤
      singletonDeficit G P (A ∪ B) t + singletonDeficit G P (A ∩ B) t := by
  have hc := capped_submodular (G := G) P (A ∪ {t}) (B ∪ {t})
  have hu : (A ∪ {t}) ∪ (B ∪ {t}) = (A ∪ B) ∪ {t} := by ext x; simp
  have hi : (A ∪ {t}) ∩ (B ∪ {t}) = (A ∩ B) ∪ {t} := by
    ext x
    simp only [mem_inter,mem_union,mem_singleton]
    tauto
  rw [hu,hi] at hc
  have hcard := card_union_add_card_inter A B
  unfold singletonDeficit rankTerm
  omega

omit [DecidableEq V] in
lemma five_six_deficiency {U L Y : Finset V}
    (hs : ∀ y ∈ L, dg G U y = 5 ∨ dg G U y = 6) (hY : Y ⊆ L) :
    df G U Y = #{y ∈ Y | dg G U y = 5} := by
  unfold df
  rw [← sum_boole]
  apply sum_congr rfl
  intro y hy
  rcases hs y (hY hy) with hh|hh <;> simp [hh]

lemma singleton_deficit_le_two {U W S P P' L L' Y : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hY : Y ⊆ L) (hδ : df G U L = 6) :
    singletonDeficit G P Y t ≤ 2 := by
  have hh := singleton_deficit_bound h hi ht hY
  have hm := df_le_of_subset (G := G) hY (fun y hy => hi.capW y (h.subsets.2.2.1 hy))
  omega

lemma singleton_deficit_omission_le_one {U W S P P' L L' Y : Finset V} {t z : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hz : z ∈ L) (hdz : dg G U z = 5)
    (hY : Y ⊆ L.erase z) (hδ : df G U L = 6) :
    singletonDeficit G P Y t ≤ 1 := by
  have he : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  have hh := singleton_deficit_bound h hi ht (hY.trans (erase_subset z L))
  omega

/-- The original degree-four separator port has at most three units including the scar. -/
lemma singleton_port_scar {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 4) :
    (ec G P {t} : ℤ) + df G W P ≤ 3 := by
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

noncomputable def singletonHeavy (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Y : Finset V) (t : V) : Finset V :=
  P.filter fun x => 5 ≤ dg G (Y ∪ {t}) x

lemma capped_heavy_decomposition (P Y : Finset V) (t : V) :
    capped G P (Y ∪ {t}) = 4 * #(singletonHeavy G P Y t) +
      ec G (P \ singletonHeavy G P Y t) (Y ∪ {t}) := by
  let H := singletonHeavy G P Y t
  have hH : H ⊆ P := filter_subset _ _
  have hsum := sum_sdiff hH (f := fun x => min 4 (dg G (Y ∪ {t}) x))
  have hhigh : (∑ x ∈ H, min 4 (dg G (Y ∪ {t}) x)) = 4 * #H := by
    calc _ = ∑ _x ∈ H, 4 := by
          apply sum_congr rfl
          intro x hx
          have hh := (mem_filter.mp hx).2
          exact min_eq_left (by omega)
      _ = _ := by simp [mul_comm]
  have hlow : (∑ x ∈ P \ H, min 4 (dg G (Y ∪ {t}) x)) = ec G (P \ H) (Y ∪ {t}) := by
    apply sum_congr rfl
    intro x hx
    have hn : ¬ 5 ≤ dg G (Y ∪ {t}) x := by
      intro hh
      exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,hh⟩)
    exact min_eq_right (by omega)
  unfold capped
  change _ = 4 * #H + ec G (P \ H) (Y ∪ {t})
  omega

lemma singleton_heavy_accounting {U W S P P' L L' Y : Finset V} {t : V}
    (h : Split G U W S P P' L L') (ht : t ∈ S) (hY : Y ⊆ L) :
    let H := singletonHeavy G P Y t
    let a : ℤ := #Y - #H
    let e := df G W H
    let b : ℤ := ec G H ((L ∪ S) \ (Y ∪ {t}))
    singletonDeficit G P Y t = df G U Y - 2*a-e-b ∧
    gv G H (Y ∪ {t}) = 6*a+6+2*e+2*b := by
  dsimp only
  let H := singletonHeavy G P Y t
  have hH : H ⊆ P := filter_subset _ _
  have hT : Y ∪ {t} ⊆ L ∪ S := union_subset (hY.trans subset_union_left)
    ((singleton_subset_iff.mpr ht).trans subset_union_right)
  have hsep : Disjoint Y ({t} : Finset V) := h.rightSep₁.mono hY (singleton_subset_iff.mpr ht)
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
  have hcomp := ec_sdiff_add_right (G := G) hT H
  have hsplit := ec_sdiff_add_left (G := G) hH (Y ∪ {t})
  have he := ec_union_right (G := G) hsep P
  have hc := capped_heavy_decomposition (G := G) P Y t
  change capped G P (Y ∪ {t}) = 4 * #H + ec G (P \ H) (Y ∪ {t}) at hc
  have hcard := card_union_of_disjoint hsep
  unfold singletonDeficit rankTerm gv
  change (ec G P {t} : ℤ) - ((capped G P (Y ∪ {t}) : ℤ)-4*#Y) =
    df G U Y - 2*((#Y : ℤ)-#H)-df G W H-(ec G H ((L ∪ S) \ (Y ∪ {t})) : ℤ) ∧
    6*((#H : ℤ)+#(Y ∪ {t}))-2*(ec G H (Y ∪ {t}) : ℤ) =
      6*((#Y : ℤ)-#H)+6+2*df G W H+2*(ec G H ((L ∪ S) \ (Y ∪ {t})) : ℤ)
  simp only [card_singleton] at hcard
  constructor <;> omega

/-- Equality in the positive-cut floor has only the two original R857 geometries. -/
lemma singleton_equality_geometry {U W S P P' L L' Y : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 4) (hY : Y ⊆ L)
    (hpos : 0 < singletonDeficit G P Y t)
    (heq : singletonDeficit G P Y t = df G U Y - 4) :
    let H := singletonHeavy G P Y t
    let a : ℤ := #Y - #H
    let b : ℤ := ec G H ((L ∪ S) \ (Y ∪ {t}))
    (a = 1 ∨ a = 2) ∧ df G W H = 0 ∧ b = 4-2*a ∧
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
  have hport := singleton_port_scar h hi ht hdt
  have hm := ec_mono_left (G := G) hH ({t} : Finset V)
  have hepsm := df_le_of_subset (G := G) (hH.trans h.subsets.1) hi.capU
  rw [hi.defU] at hepsm
  have hepsall := df_le_of_subset (G := G) hH (fun x hx => hi.capU x (h.subsets.1 hx))
  have heunion := ec_union_right (G := G) hdis H
  have hcard := card_union_of_disjoint hdis
  simp only [card_singleton] at hcard
  unfold gv at hfloor hfloor'
  unfold gv at hpotential
  change (((#Y : ℤ)-#H) = 1 ∨ ((#Y : ℤ)-#H) = 2) ∧ df G W H = 0 ∧
    (ec G H ((L ∪ S) \ (Y ∪ {t})) : ℤ) = 4-2*((#Y : ℤ)-#H) ∧
      4 ≤ ((#Y : ℤ)-#H) + (ec G H {t} : ℤ)
  omega

lemma singleton_heavy_mono {P A B : Finset V} {t : V} (hAB : A ⊆ B) :
    singletonHeavy G P A t ⊆ singletonHeavy G P B t := by
  intro x hx
  obtain ⟨hxP,hh⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hxP,hh.trans (dg_mono (G := G) (union_subset_union_left hAB) x)⟩

lemma singleton_maximum_mass {U W S P P' L L' K : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = 6) (hK : K ⊆ L)
    (hKd : singletonDeficit G P K t = 2) : df G U K = 6 := by
  have hm := df_le_of_subset (G := G) hK (fun y hy => hi.capW y (h.subsets.2.2.1 hy))
  have hb := singleton_deficit_bound h hi ht hK
  omega

lemma singleton_maximum_incoming {U W S P P' L L' K : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 4) (hδ : df G U L = 6)
    (hK : K ⊆ L) (hKd : singletonDeficit G P K t = 2) :
    ec G (P \ singletonHeavy G P K t) K ≤ 9 := by
  let H := singletonHeavy G P K t
  have hH : H ⊆ P := filter_subset _ _
  have hm := singleton_maximum_mass h hi ht hδ hK hKd
  obtain ⟨ha,he,hb,hτ⟩ := singleton_equality_geometry h hi ht hdt hK (by omega) (by omega)
  change ((#K : ℤ)-#H = 1 ∨ (#K : ℤ)-#H = 2) at ha
  change df G W H = 0 at he
  change (ec G H ((L ∪ S) \ (K ∪ {t})) : ℤ) = 4-2*((#K : ℤ)-#H) at hb
  have hp := singleton_port_scar h hi ht hdt
  have hpnon := df_nonneg (G := G) (fun x hx => hi.capU x (h.subsets.1 hx))
  have hτm := ec_mono_left (G := G) hH ({t} : Finset V)
  have hdegree : df G P K = df G U K := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (hK hy)]
  have hd := df_eq (G := G) P K
  rw [hdegree,ec_comm] at hd
  have hrow : df G (L ∪ S) H = 0 := by
    have hh : df G (L ∪ S) H = df G W H := by
      unfold df
      exact sum_congr rfl fun x hx => by rw [h.degree_left (hH hx)]
    rwa [he] at hh
  have hr := df_eq (G := G) (L ∪ S) H
  rw [hrow] at hr
  have hT : K ∪ {t} ⊆ L ∪ S := union_subset (hK.trans subset_union_left)
    ((singleton_subset_iff.mpr ht).trans subset_union_right)
  have hcomp := ec_sdiff_add_right (G := G) hT H
  have hdis := h.rightSep₁.mono hK (singleton_subset_iff.mpr ht)
  have hpart := ec_union_right (G := G) hdis H
  have hleft := ec_sdiff_add_left (G := G) hH K
  change ec G (P \ H) K ≤ 9
  omega

lemma singleton_piece_charge_numeric {U W S P P' L L' X R : Finset V}
    {a ay ell m : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hX : X ⊆ P) (hR : R ⊆ L) (hr : 1 ≤ #R)
    (ha : a = 1 ∨ a = 2) (hay : ay = 1 ∨ ay = 2)
    (hg : (#X : ℤ)-#R = ay-a)
    (he0 : 0 ≤ ell) (hecap : ell ≤ 4-2*a) (hen : 0 ≤ ell-2*(ay-a))
    (hpotential : gv G X R = 2*(ay-a)+2*m+2+2*ell) : 2 ≤ m := by
  by_cases hlarge : 4 ≤ #X+#R
  · have hf := h.local_floor hi hX (hR.trans subset_union_left) hlarge
    omega
  · have hcases : (#X = 0 ∧ #R = 1) ∨ (#X = 1 ∧ #R = 1) ∨
        (#X = 1 ∧ #R = 2) ∨ (#X = 2 ∧ #R = 1) := by omega
    have he := ec_product_bound (G := G) X R
    unfold gv at hpotential
    rcases hcases with ⟨hx,hr⟩|⟨hx,hr⟩|⟨hx,hr⟩|⟨hx,hr⟩ <;>
      rw [hx,hr] at hpotential he hg <;> norm_num at hpotential he hg <;> omega

lemma singleton_piece_charge {U W S P P' L L' K Y : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 4) (hδ : df G U L = 6)
    (hK : K ⊆ L) (hYK : Y ⊆ K)
    (hKd : singletonDeficit G P K t = 2)
    (hYd : singletonDeficit G P Y t = 1) (hYm : df G U Y = 5)
    (hne : (K \ Y).Nonempty) :
    2 ≤ ec G (P \ singletonHeavy G P K t) (K \ Y) := by
  let H := singletonHeavy G P K t
  let H' := singletonHeavy G P Y t
  let X := H \ H'
  let R := K \ Y
  let O := (L ∪ S) \ (K ∪ {t})
  let a : ℤ := #K-#H
  let ay : ℤ := #Y-#H'
  let ell : ℤ := ec G X O
  let m : ℤ := ec G (P \ H) R
  have hH : H ⊆ P := filter_subset _ _
  have hH' : H' ⊆ H := singleton_heavy_mono (G := G) hYK
  have hX : X ⊆ P := sdiff_subset.trans hH
  have hR : R ⊆ L := sdiff_subset.trans hK
  have hmK := singleton_maximum_mass h hi ht hδ hK hKd
  obtain ⟨ha,he,hb,hτ⟩ := singleton_equality_geometry h hi ht hdt hK (by omega) (by omega)
  obtain ⟨hay,hey,hby,hτy⟩ := singleton_equality_geometry h hi ht hdt (hYK.trans hK) (by omega) (by omega)
  change a = 1 ∨ a = 2 at ha
  change ay = 1 ∨ ay = 2 at hay
  change df G W H = 0 at he
  change (ec G H O : ℤ) = 4-2*a at hb
  change (ec G H' ((L ∪ S) \ (Y ∪ {t})) : ℤ) = 4-2*ay at hby
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
  have hcross : (ec G H' R : ℤ) = ell-2*(ay-a) := by dsimp [ell]; omega
  have hell : 0 ≤ ell := by dsimp [ell]; positivity
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
  change (2 : ℤ) ≤ (ec G (P \ H) R : ℤ) at hm
  change (2 : ℕ) ≤ ec G (P \ H) R
  omega

/-- Bad markers quantify over every positive cut, not only maximum cuts. -/
noncomputable def badSingletonMarkers (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P L : Finset V) (t : V) : Finset V :=
  (L.filter fun z => dg G U z = 5).filter fun z =>
    ∃ Y ⊆ L.erase z, 0 < singletonDeficit G P Y t

lemma singleton_bad_witness {U W S P P' L L' : Finset V} {t z : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = 6)
    (hz : z ∈ badSingletonMarkers G U P L t) :
    z ∈ L ∧ dg G U z = 5 ∧
      ∃ Y ⊆ L.erase z, singletonDeficit G P Y t = 1 ∧ df G U Y = 5 := by
  obtain ⟨hzM,Y,hY,hpos⟩ := mem_filter.mp hz
  obtain ⟨hzL,hdz⟩ := mem_filter.mp hzM
  have hu := singleton_deficit_omission_le_one h hi ht hzL hdz hY hδ
  have hb := singleton_deficit_bound h hi ht (hY.trans (erase_subset z L))
  have he : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hzL
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  exact ⟨hzL,hdz,Y,hY,by omega,by omega⟩

lemma singleton_two_omissions_nonpositive {U W S P P' L L' Y : Finset V} {t z w : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = 6)
    (hz : z ∈ L) (hw : w ∈ L) (hzw : z ≠ w)
    (hdz : dg G U z = 5) (hdw : dg G U w = 5)
    (hY : Y ⊆ (L.erase z).erase w) :
    singletonDeficit G P Y t ≤ 0 := by
  have hez : df G U (L.erase z) + (6-(dg G U z : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz
  have hew : df G U ((L.erase z).erase w) + (6-(dg G U w : ℤ)) = df G U (L.erase z) :=
    sum_erase_add (L.erase z) (fun y => 6-(dg G U y : ℤ)) (mem_erase.mpr ⟨hzw.symm,hw⟩)
  have hm := df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp (mem_erase.mp hy).2).2))
  have hb := singleton_deficit_bound h hi ht
    (hY.trans ((erase_subset w (L.erase z)).trans (erase_subset z L)))
  omega

lemma singleton_minimal_maximum {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = 6)
    (hbad : 2 ≤ #(badSingletonMarkers G U P L t)) :
    ∃ K ⊆ L, singletonDeficit G P K t = 2 ∧
      (∀ T ⊆ K, singletonDeficit G P T t = 2 → T = K) ∧
      ∀ z ∈ badSingletonMarkers G U P L t,
        ∃ Y ⊆ K, z ∉ Y ∧ singletonDeficit G P Y t = 1 ∧ df G U Y = 5 := by
  obtain ⟨z,hz,w,hw,hzw⟩ := Finset.one_lt_card.mp (by omega : 1 < #(badSingletonMarkers G U P L t))
  obtain ⟨hzL,hdz,A,hA,hdA,hmA⟩ := singleton_bad_witness h hi ht hδ hz
  obtain ⟨hwL,hdw,B,hB,hdB,hmB⟩ := singleton_bad_witness h hi ht hδ hw
  have hAB : A ∩ B ⊆ (L.erase z).erase w := by
    intro y hy
    obtain ⟨hya,hyb⟩ := mem_inter.mp hy
    exact mem_erase.mpr ⟨(mem_erase.mp (hB hyb)).1,hA hya⟩
  have hzero := singleton_two_omissions_nonpositive h hi ht hδ hzL hwL hzw hdz hdw hAB
  have hjoin : A ∪ B ⊆ L := union_subset (hA.trans (erase_subset z L)) (hB.trans (erase_subset w L))
  have hup := singleton_deficit_le_two h hi ht hjoin hδ
  have hsm := singleton_deficit_supermodular (G := G) P A B t
  have hmax : singletonDeficit G P (A ∪ B) t = 2 := by omega
  let C := L.powerset.filter fun K => singletonDeficit G P K t = 2
  have hC : C.Nonempty := ⟨A ∪ B,mem_filter.mpr ⟨mem_powerset.mpr hjoin,hmax⟩⟩
  obtain ⟨K,hK,hmin⟩ := exists_min_image C Finset.card hC
  obtain ⟨hKL,hKd⟩ := mem_filter.mp hK
  have hKL' := mem_powerset.mp hKL
  have hminimal : ∀ T ⊆ K, singletonDeficit G P T t = 2 → T = K := by
    intro T hTK hTd
    apply eq_of_subset_of_card_le hTK
    exact hmin T (mem_filter.mpr ⟨mem_powerset.mpr (hTK.trans hKL'),hTd⟩)
  refine ⟨K,hKL',hKd,hminimal,?_⟩
  intro v hv
  obtain ⟨hvL,hdv,Y,hY,hdY,hmY⟩ := singleton_bad_witness h hi ht hδ hv
  have hI : Y ∩ K ⊆ L.erase v := inter_subset_left.trans hY
  have hIU := singleton_deficit_omission_le_one h hi ht hvL hdv hI hδ
  have hUU := singleton_deficit_le_two h hi ht
    (union_subset (hY.trans (erase_subset v L)) hKL') hδ
  have hsm' := singleton_deficit_supermodular (G := G) P Y K t
  have hId : singletonDeficit G P (Y ∩ K) t = 1 := by omega
  have hmass := singleton_deficit_bound h hi ht (hI.trans (erase_subset v L))
  have he : df G U (L.erase v) + (6-(dg G U v : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hvL
  have hm := df_le_of_subset (G := G) hI
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  exact ⟨Y ∩ K,inter_subset_right,
    fun hh => (mem_erase.mp (hI hh)).1 rfl,hId,by omega⟩

lemma singleton_maximum_witness_union {U W S P P' L L' K A B : Finset V} {t z w : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hδ : df G U L = 6) (hK : K ⊆ L)
    (hmin : ∀ T ⊆ K, singletonDeficit G P T t = 2 → T = K)
    (hz : z ∈ L) (hw : w ∈ L) (hzw : z ≠ w)
    (hdz : dg G U z = 5) (hdw : dg G U w = 5)
    (hA : A ⊆ K) (hB : B ⊆ K) (hnz : z ∉ A) (hnw : w ∉ B)
    (hdA : singletonDeficit G P A t = 1) (hdB : singletonDeficit G P B t = 1) :
    A ∪ B = K ∧ Disjoint (K \ A) (K \ B) := by
  have hAB : A ∩ B ⊆ (L.erase z).erase w := by
    intro y hy
    obtain ⟨hya,hyb⟩ := mem_inter.mp hy
    exact mem_erase.mpr ⟨fun hh => hnw (hh ▸ hyb),
      mem_erase.mpr ⟨fun hh => hnz (hh ▸ hya),hK (hA hya)⟩⟩
  have hzero := singleton_two_omissions_nonpositive h hi ht hδ hz hw hzw hdz hdw hAB
  have hjoin : A ∪ B ⊆ K := union_subset hA hB
  have hup := singleton_deficit_le_two h hi ht (hjoin.trans hK) hδ
  have hsm := singleton_deficit_supermodular (G := G) P A B t
  have heq := hmin (A ∪ B) hjoin (by omega)
  refine ⟨heq,disjoint_left.mpr ?_⟩
  intro y hya hyb
  have hyK := (mem_sdiff.mp hya).1
  rw [← heq] at hyK
  rcases mem_union.mp hyK with hh|hh
  · exact (mem_sdiff.mp hya).2 hh
  · exact (mem_sdiff.mp hyb).2 hh

/-- One original degree-five marker meets all positive singleton cuts simultaneously. -/
theorem six_five_safe_marker {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (_hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hδ : df G U L = 6)
    (hprofile : ∀ y ∈ L, dg G U y = 5 ∨ dg G U y = 6) :
    ∃ z ∈ L, dg G U z = 5 ∧
      ∀ Y ⊆ L.erase z, (ec G P {t} : ℤ) ≤ rankTerm G P Y {t} := by
  let M := L.filter fun z => dg G U z = 5
  let B := badSingletonMarkers G U P L t
  have hM : #M = 6 := by
    have hh := five_six_deficiency (G := G) hprofile (Subset.refl L)
    change df G U L = (#M : ℤ) at hh
    omega
  by_contra hn
  have hall : ∀ z ∈ M, z ∈ B := by
    intro z hz
    obtain ⟨hzL,hdz⟩ := mem_filter.mp hz
    have hfailed : ¬ ∀ Y ⊆ L.erase z, (ec G P {t} : ℤ) ≤ rankTerm G P Y {t} := by
      intro hh
      exact hn ⟨z,hzL,hdz,hh⟩
    push Not at hfailed
    obtain ⟨Y,hY,hf⟩ := hfailed
    exact mem_filter.mpr ⟨hz,Y,hY,by unfold singletonDeficit; omega⟩
  have hBM : B = M := Subset.antisymm (filter_subset _ _) hall
  have hB : #B = 6 := by rw [hBM,hM]
  obtain ⟨K,hK,hKd,hmin,hchoices⟩ := singleton_minimal_maximum h hi ht hδ (by change 2 ≤ #B; omega)
  let Y : V → Finset V := fun z => if hz : z ∈ B then Classical.choose (hchoices z hz) else ∅
  have hYs : ∀ z ∈ B, Y z ⊆ K ∧ z ∉ Y z ∧ singletonDeficit G P (Y z) t = 1 ∧ df G U (Y z) = 5 := by
    intro z hz
    dsimp only [Y]
    rw [dif_pos hz]
    exact Classical.choose_spec (hchoices z hz)
  let R : V → Finset V := fun z => K \ Y z
  have hR : ∀ z ∈ B, R z ⊆ K := fun z hz => sdiff_subset
  have hvertices : ∀ z ∈ B, z ∈ L ∧ dg G U z = 5 := by
    intro z hz
    have hh : z ∈ M := hBM ▸ hz
    exact mem_filter.mp hh
  have hRne : ∀ z ∈ B, (R z).Nonempty := by
    intro z hz
    obtain ⟨hzL,hdz⟩ := hvertices z hz
    have hzK : z ∈ K := by
      by_contra hnot
      have hKe : K ⊆ L.erase z := by
        intro y hy
        exact mem_erase.mpr ⟨fun hh => hnot (hh ▸ hy),hK hy⟩
      have hh := singleton_deficit_omission_le_one h hi ht hzL hdz hKe hδ
      omega
    exact ⟨z,mem_sdiff.mpr ⟨hzK,(hYs z hz).2.1⟩⟩
  have hdis : Set.PairwiseDisjoint (↑B : Set V) R := by
    intro z hz w hw hzw
    obtain ⟨hzL,hdz⟩ := hvertices z hz
    obtain ⟨hwL,hdw⟩ := hvertices w hw
    obtain ⟨hYz,hnz,hdYz,_⟩ := hYs z hz
    obtain ⟨hYw,hnw,hdYw,_⟩ := hYs w hw
    exact (singleton_maximum_witness_union h hi ht hδ hK hmin
      hzL hwL hzw hdz hdw hYz hYw hnz hnw hdYz hdYw).2
  have hcharge : ∀ z ∈ B, 2 ≤ ec G (P \ singletonHeavy G P K t) (R z) := by
    intro z hz
    obtain ⟨hY,hnz,hdY,hmY⟩ := hYs z hz
    exact singleton_piece_charge h hi ht hdt hδ hK hY hKd hdY hmY (hRne z hz)
  have hbudget := disjoint_charge_budget (G := G) hR hdis hcharge
  have hincoming := singleton_maximum_incoming h hi ht hdt hδ hK hKd
  omega

#print axioms singleton_equality_geometry
#print axioms singleton_piece_charge
#print axioms six_five_safe_marker
#print axioms singleton_deficit_bound
#print axioms singleton_deficit_supermodular
#print axioms singleton_minimal_maximum
#print axioms singleton_maximum_witness_union
end Erdos585.QB7S0002R869
