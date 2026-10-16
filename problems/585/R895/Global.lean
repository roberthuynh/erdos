/- R895 literal S0000 original cut accounting and all-trace assembly. -/
import R883.Global
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0000R895
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700
  QB7Separator0111R721 QB7Selector0012R751 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma interior_deficiencies {U W S P P' L L' : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hs : ∀ s ∈ S, dg G U s = 6) :
    5 ≤ df G U L ∧ 5 ≤ df G U L' ∧
    df G U L + df G U L' = 13 ∧ df G U L ≤ 8 ∧ df G U L' ≤ 8 := by
  have hds : df G U S = 0 := by
    unfold df
    apply sum_eq_zero
    intro s hss
    rw [hs s hss]
    norm_num
  have hd := hi.defW
  unfold df at hd
  rw [← h.rightCover,sum_union (show Disjoint (L ∪ L') S from disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),
    sum_union h.rightDisjoint] at hd
  change df G U L+df G U L'+df G U S = 13 at hd
  have h₁ := h.interior_scar hi
  have h₂ := h.swap.interior_scar hi
  exact ⟨h₁,h₂,by omega,by omega,by omega⟩

lemma singleton_incidence_sum {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (ht : t ∈ S)
    (hs : ∀ s ∈ S, dg G U s = 6) :
    ec G P {t} + ec G P' {t} = 6 := by
  have he := ec_union_left (G := G) h.leftDisjoint ({t} : Finset V)
  rw [h.leftCover,ec_comm] at he
  simpa [ec,hs t ht] using he.symm

lemma lobe_ports_upper {U W S P P' L L' R : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hR : R ⊆ S) :
    (ec G P R : ℤ) ≤ df G U L + 3*#R - 5 := by
  have hp := h.left_large hi
  have hf := h.local_floor hi (Subset.refl P)
    (union_subset subset_union_left (hR.trans subset_union_right))
    (by have hm := card_le_card (subset_union_left : L ⊆ L ∪ R); omega)
  have hb := h.local_balance hi
  have hd : df G P L = df G U L := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right hy]
  have he := df_eq (G := G) P L
  have hc := ec_comm (G := G) L P
  unfold gv at hf
  rw [card_union_of_disjoint (h.rightSep₁.mono_right hR),
    ec_union_right (h.rightSep₁.mono_right hR)] at hf
  omega

lemma lobe_port_bounds {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) :
    1 ≤ ec G P {t} ∧ (ec G P {t} : ℤ) ≤ df G U L-2 := by
  have hupper := lobe_ports_upper h hi (singleton_subset_iff.mpr ht)
  have hother := lobe_ports_upper h hi (erase_subset t S)
  have he := ec_union_right (G := G) h.rightSep₁ P
  have hefull := df_eq (G := G) W P
  have hdeg : ec G P W = ec G P (L ∪ S) := by
    unfold ec
    exact sum_congr rfl fun x hx => (h.degree_left hx).symm
  have hδ : df G P L = df G U L := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right hy]
  have heL := df_eq (G := G) P L
  have hcomm := ec_comm (G := G) L P
  have hb := h.local_balance hi
  have hdef := df_le_of_subset (G := G) h.subsets.1 hi.capU
  rw [hi.defU] at hdef
  have hcard := card_erase_add_one ht
  have herase := ec_erase_right (G := G) (P := P) ht
  have hsing : ec G P {t} = dg G P t := by rw [ec_comm]; simp [ec]
  simp only [card_singleton,Nat.cast_one] at hupper
  rw [h.cardS] at hcard
  omega

lemma deficient_marker_outside {U W S P P' L L' B : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hB : B ⊆ L) (hweight : df G U B < df G U L) :
    ∃ z ∈ L, dg G U z < 6 ∧ z ∉ B := by
  by_contra hn
  push Not at hn
  have hsub : deficientMarkers G U L ⊆ B := by
    intro z hz
    exact hn z (mem_filter.mp hz).1 (mem_filter.mp hz).2
  have hd := df_le_of_subset (G := G) hsub
    (fun z hz => hi.capW z (h.subsets.2.2.1 (hB hz)))
  rw [markers_deficiency (fun z hz => hi.capW z (h.subsets.2.2.1 hz))] at hd
  omega

lemma retained_rank_lower {U W S P P' L L' Y R : Finset V} {z : V} {c : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hY : Y ⊆ L.erase z) (hR : R ⊆ S) (hc : 0 ≤ c)
    (hδ : df G U (L.erase z)+2*(#R : ℤ)-6 ≤ c) :
    (ec G P R : ℤ)-c ≤ rankTerm G P Y R := by
  have hd := (df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2)))
  have hh := h.capped_rank_lower hi (hY.trans (erase_subset z L)) hR
  have hm : max 0 (df G U Y+2*#R-6) ≤ c := max_le hc (by omega)
  omega

/-- Any failure beyond the empty/singleton traces supplies original mass-two tails. -/
lemma failed_pair_tails {U W S P P' L L' : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hu : u0 ∈ P) (hdu : dg G W u0 = 5)
    (hz₁ : z₁ ∈ L) (hz₂ : z₂ ∈ L')
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hlow : ∀ Y₁ ⊆ L.erase z₁, ∀ Y₂ ⊆ L'.erase z₂, ∀ R ⊆ S,
      #R ≤ 1 → 4*(#R : ℤ) ≤ rankTerm G P Y₁ R+rankTerm G P' Y₂ R)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ Q ⊆ S, #Q = 2 ∧ ∃ a : PortTail G U P L Q,
      ∃ b : PortTail G U P' L' Q,
        u0 ∈ a.X ∧ z₁ ∈ a.B ∧ z₂ ∈ b.B := by
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := hlow Y₁ hY₁ Y₂ hY₂ R hR hrlo
    omega
  by_cases hr2 : #R = 2
  · obtain ⟨a,b,ha,hz₁',hz₂',_,_,_⟩ := QB7S0001R883.full_two_trace_tails h hi hu hdu
      hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 (by omega)
    have hq : #(S \ R) = 2 := by
      have hc := card_sdiff_add_card_eq_card hR
      rw [h.cardS,hr2] at hc
      omega
    exact ⟨S \ R,sdiff_subset,hq,a,b,ha,hz₁',hz₂'⟩
  by_cases hr3 : #R = 3
  · have := three_rank h hi hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr3
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega

#print axioms interior_deficiencies
#print axioms failed_pair_tails
end Erdos585.QB7S0000R895
