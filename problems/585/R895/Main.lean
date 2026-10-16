/- R895 full literal S0000 assembly on original unit edges. -/
import R895.Global
import R895.LocalB
import R895.Tails
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0000R895
open QB4 QB7SmallLobeR643 QB7ProfileFreeR854 QB7S0002R869
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma fixed_factor_of_safe_pair {U W S P P' L L' : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hu : u0 ∈ P) (hdu : dg G W u0 = 5)
    (hz₁ : z₁ ∈ L) (hz₂ : z₂ ∈ L')
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hlow : ∀ Y₁ ⊆ L.erase z₁, ∀ Y₂ ⊆ L'.erase z₂, ∀ R ⊆ S,
      #R ≤ 1 → 4*(#R : ℤ) ≤ rankTerm G P Y₁ R+rankTerm G P' Y₂ R)
    (hsafe : z₁ ∉ tailMarkers G U P L u0) :
    FixedOmissionFactor G U W z₁ z₂ := by
  by_contra hf
  obtain ⟨Q,hQ,hq,a,b,ha,hz₁',hz₂'⟩ := failed_pair_tails h hi hu hdu hz₁ hz₂ hd₁ hd₂ hlow hf
  let t : ScarTail G U P L u0 :=
    ⟨a.X,a.B,a.left,a.right,a.balance,a.potential,ha,z₁,hz₁',hd₁⟩
  exact hsafe (mem_filter.mpr ⟨mem_filter.mpr ⟨hz₁,hd₁⟩,t,hz₁'⟩)

lemma low_rank_middle {U W S P P' L L' : Finset V} {z₁ z₂ : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hs : ∀ s ∈ S, dg G U s = 6)
    (_hD₁ : df G U L = 6 ∨ df G U L = 7)
    (hD₂ : df G U L' = 6 ∨ df G U L' = 7)
    (hDsum : df G U L+df G U L'=13)
    (hz₁ : z₁ ∈ L) (hz₂ : z₂ ∈ L')
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hgood : ∀ s ∈ S, z₁ ∉ badSingletonMarkers G U P L s (df G U L) ∨
      z₂ ∉ badSingletonMarkers G U P' L' s (df G U L')) :
    ∀ Y₁ ⊆ L.erase z₁, ∀ Y₂ ⊆ L'.erase z₂, ∀ R ⊆ S,
      #R ≤ 1 → 4*(#R : ℤ) ≤ rankTerm G P Y₁ R+rankTerm G P' Y₂ R := by
  intro Y₁ hY₁ Y₂ hY₂ R hR hr
  by_cases hr0 : #R = 0
  · have hReq := card_eq_zero.mp hr0
    have he₁ : df G U (L.erase z₁)+(6-(dg G U z₁ : ℤ))=df G U L :=
      sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz₁
    have he₂ : df G U (L'.erase z₂)+(6-(dg G U z₂ : ℤ))=df G U L' :=
      sum_erase_add L' (fun y => 6-(dg G U y : ℤ)) hz₂
    have ha := retained_rank_lower h hi hY₁ hR (show (0:ℤ)≤0 by omega) (by omega)
    have hb := retained_rank_lower h.swap hi hY₂ hR (show (0:ℤ)≤0 by omega) (by omega)
    rw [hReq] at ha hb ⊢
    simp only [card_empty,Nat.cast_zero,ec,dg,sub_zero,mul_zero] at ha hb ⊢
    omega
  have hr1 : #R = 1 := by omega
  obtain ⟨s,hsR⟩ := card_eq_one.mp hr1
  have hss : s ∈ S := hR (hsR.symm ▸ mem_singleton_self s)
  have hsum := singleton_incidence_sum h hss hs
  have ha := singleton_omission_bound h hi hss hz₁ hd₁ (Y := Y₁) hY₁ rfl (by omega)
  have hb := singleton_omission_bound h.swap hi hss hz₂ hd₂ (Y := Y₂) hY₂ rfl (by omega)
  rcases hgood s hss with hn|hn
  · have hh := singleton_not_bad_rank hz₁ hd₁ hn hY₁
    unfold singletonDeficit at hb
    rw [hsR]
    simp only [card_singleton,Nat.cast_one]
    omega
  · have hh := singleton_not_bad_rank hz₂ hd₂ hn hY₂
    unfold singletonDeficit at ha
    rw [hsR]
    simp only [card_singleton,Nat.cast_one]
    omega

lemma singleton_rectangle_card {U W S P P' L L' : Finset V} {s : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hs : ∀ t ∈ S, dg G U t = 6) (hss : s ∈ S)
    (hD₁ : df G U L = 6 ∨ df G U L = 7)
    (hD₂ : df G U L' = 6 ∨ df G U L' = 7)
    (hDsum : df G U L+df G U L'=13) :
    #(badSingletonMarkers G U P L s (df G U L) ×ˢ
      badSingletonMarkers G U P' L' s (df G U L')) ≤ 6 := by
  have hq₁ := lobe_port_bounds h hi hss
  have hq₂ := lobe_port_bounds h.swap hi hss
  have hsum := singleton_incidence_sum h hss hs
  have hc₁ := singleton_bad_table h hi hss rfl (by omega) (by omega)
  have hc₂ := singleton_bad_table h.swap hi hss rfl (by omega) (by omega)
  rw [card_product]
  rcases hD₁ with hD₁|hD₁ <;>
    rcases hD₂ with hD₂|hD₂
  all_goals try omega
  all_goals rw [hD₁] at hc₁
  all_goals rw [hD₂] at hc₂
  all_goals rw [hD₁,hD₂]
  all_goals unfold singletonCardBound at hc₁ hc₂
  all_goals split_ifs at hc₁ hc₂ <;>
    first | omega | exact (Nat.mul_le_mul hc₁ hc₂).trans (by decide)

lemma select_middle {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hu : u0 ∈ P) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 6)
    (hD₁ : df G U L = 6 ∨ df G U L = 7)
    (hD₂ : df G U L' = 6 ∨ df G U L' = 7)
    (hDsum : df G U L+df G U L'=13) :
    ∃ z₁ ∈ L, ∃ z₂ ∈ L', dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  let M₁ := deficientMarkers G U L
  let M₂ := deficientMarkers G U L'
  let A := tailMarkers G U P L u0
  let C := (M₁ \ A) ×ˢ M₂
  let rect := fun s => badSingletonMarkers G U P L s (df G U L) ×ˢ
    badSingletonMarkers G U P' L' s (df G U L')
  have hA : A ⊆ M₁ := tailMarkers_subset U P L u0
  have hdA : df G U A ≤ 2 := tailMarkers_deficiency h hi hdu
  have hdM₁ : df G U M₁=df G U L := markers_deficiency fun z hz => hi.capW z (h.subsets.2.2.1 hz)
  have hdM₂ : df G U M₂=df G U L' := markers_deficiency fun z hz => hi.capW z (h.subsets.2.2.2 hz)
  have hCmass : df G U L-2 ≤ df G U (M₁ \ A) := by
    have he := sum_sdiff hA (f := fun z => 6-(dg G U z : ℤ))
    change df G U (M₁ \ A)+df G U A=df G U M₁ at he
    omega
  have htotal : 28 ≤ ∑ p ∈ C, pairWeight G U p := by
    dsimp [C]
    rw [product_weight,hdM₂]
    rcases hD₁ with ha|ha <;> rcases hD₂ with hb|hb <;> nlinarith
  have hrect : ∀ s ∈ S, #(rect s) ≤ 6 := by
    intro s hss
    exact singleton_rectangle_card h hi hs hss hD₁ hD₂ hDsum
  have hunion : #(S.biUnion rect) ≤ 24 := by
    have hh := card_biUnion_le_card_mul S rect 6 hrect
    rw [h.cardS] at hh
    exact hh
  have hnsub : ¬ C ⊆ S.biUnion rect := by
    intro hsub
    have hcard := (card_le_card hsub).trans hunion
    have hweight : (∑ p ∈ C, pairWeight G U p) = #C := by
      calc _ = ∑ _p ∈ C, (1 : ℤ) := by
             apply sum_congr rfl
             intro p hp
             obtain ⟨s,hss,hps⟩ := mem_biUnion.mp (hsub hp)
             obtain ⟨hp₁,hp₂⟩ := mem_product.mp hps
             have ha := (singleton_bad_witness h hi hss rfl (by omega) hp₁).2.1
             have hb := (singleton_bad_witness h.swap hi hss rfl (by omega) hp₂).2.1
             simp [pairWeight,ha,hb]
           _ = _ := by simp
    omega
  obtain ⟨p,hp,hpnot⟩ := not_subset.mp hnsub
  obtain ⟨hp₁,hp₂⟩ := mem_product.mp hp
  obtain ⟨hpM₁,hpsafe⟩ := mem_sdiff.mp hp₁
  obtain ⟨hz₁,hd₁⟩ := mem_filter.mp hpM₁
  obtain ⟨hz₂,hd₂⟩ := mem_filter.mp hp₂
  have hgood : ∀ s ∈ S, p.1 ∉ badSingletonMarkers G U P L s (df G U L) ∨
      p.2 ∉ badSingletonMarkers G U P' L' s (df G U L') := by
    intro s hss
    by_contra hn
    push Not at hn
    exact hpnot (mem_biUnion.mpr ⟨s,hss,mem_product.mpr hn⟩)
  refine ⟨p.1,hz₁,p.2,hz₂,hd₁,hd₂,?_⟩
  exact fixed_factor_of_safe_pair h hi hu hdu hz₁ hz₂ hd₁ hd₂
    (low_rank_middle h hi hs hD₁ hD₂ hDsum hz₁ hz₂ hd₁ hd₂ hgood) hpsafe

#print axioms select_middle
#print axioms fixed_factor_of_safe_pair
#print axioms low_rank_middle
#print axioms singleton_rectangle_card
end Erdos585.QB7S0000R895
