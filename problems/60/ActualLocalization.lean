import OppositeTransport
import ResidualSelection

namespace Erdos60.Localization
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def highCycleVertices (G : SimpleGraph V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun x => 4*(q : ℝ)/5 < Statistics.vertexCycleStatistic G x
noncomputable def giantDeficientVertices (G : SimpleGraph V) (q : ℕ) (T : ℝ) : Finset V :=
  Finset.univ.filter fun x => (q : ℝ)-76*T <
    (G.neighborFinset x ∩ SurplusRows.deficientVertices G q).card
noncomputable def exceptionalVertices (G : SimpleGraph V) (q : ℕ) (T : ℝ) : Finset V :=
  highCycleVertices G q ∪ HighSurplus.highVertices G q ∪
    SurplusRows.deepDeficient G q ∪ giantDeficientVertices G q T

omit [DecidableEq V] in
 theorem deficientVertices_iff (G : SimpleGraph V) (q : ℕ) (x : V) :
    x ∈ SurplusRows.deficientVertices G q ↔ G.degree x < q+1 := by
  simp only [SurplusRows.deficientVertices,Finset.mem_filter,Finset.mem_univ,true_and]
  unfold Statistics.degreeDeficiency
  omega

 theorem highCycleVertices_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (_hq : (0 : ℝ) < q) (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((highCycleVertices G q).card : ℝ) ≤ 5*T := by
  have hs : (∑ x ∈ highCycleVertices G q, 4*(q : ℝ)/5) ≤
      ∑ x ∈ highCycleVertices G q, (Statistics.vertexCycleStatistic G x : ℝ) := by
    exact Finset.sum_le_sum (fun x hx => le_of_lt (Finset.mem_filter.mp hx).2)
  have hb := HighSurplus.restricted_cycle_sum G (highCycleVertices G q)
  have hbr : (∑ x ∈ highCycleVertices G q, (Statistics.vertexCycleStatistic G x : ℝ)) ≤
      4*(Counting.cycleCount G : ℝ) := by exact_mod_cast hb
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  nlinarith

 theorem deficient_support_size_min (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((SurplusRows.deficientVertices G q).card : ℝ) ≤ (q : ℝ)+20*T ∧
      (∀ x, (q : ℝ)-26*T ≤ G.degree x) := by
  have hb := SurplusRows.localized_deficit_bounds G q T hq hT hr heven hN hE hZ
  have hs := SurplusRows.deficient_card_le_total G q
  have hsr : ((SurplusRows.deficientVertices G q).card : ℝ) ≤ Statistics.totalDeficiency G q := by
    exact_mod_cast hs
  refine ⟨by linarith [hb.2.1],?_⟩
  intro x
  have hf := hb.2.2.2.1 x
  have hd := Statistics.degree_add_deficiency G q x
  have hdn : q+1 ≤ G.degree x+Statistics.degreeDeficiency G q x := by omega
  have hdr : (q : ℝ)+1 ≤ (G.degree x : ℝ)+Statistics.degreeDeficiency G q x := by exact_mod_cast hdn
  linarith

 theorem giantDeficientVertices_card (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    (giantDeficientVertices G q T).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hs := (deficient_support_size_min G q T hq hT hr heven hN hE hZ).1
  exact Statistics.large_deficient_neighbor_unique G q T hq hT hr
    (SurplusRows.deficientVertices G q) hs hZ u v
    (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2

/-- The one actual exceptional set from source §6 has at most 51T vertices. -/
theorem exceptionalVertices_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((exceptionalVertices G q T).card : ℝ) ≤ 51*T := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hc := highCycleVertices_bound G q T hq0 hZ
  have hb := SurplusRows.localized_deficit_bounds G q T hq hT hr heven hN hE hZ
  have hg := giantDeficientVertices_card G q T hq hT hr heven hN hE hZ
  have hgr : ((giantDeficientVertices G q T).card : ℝ) ≤ 1 := by exact_mod_cast hg
  have h1 := Finset.card_union_le (highCycleVertices G q) (HighSurplus.highVertices G q)
  have h2 := Finset.card_union_le (highCycleVertices G q ∪ HighSurplus.highVertices G q)
    (SurplusRows.deepDeficient G q)
  have h3 := Finset.card_union_le
    (highCycleVertices G q ∪ HighSurplus.highVertices G q ∪ SurplusRows.deepDeficient G q)
    (giantDeficientVertices G q T)
  have hn : (exceptionalVertices G q T).card ≤ (highCycleVertices G q).card +
      (HighSurplus.highVertices G q).card+(SurplusRows.deepDeficient G q).card+
      (giantDeficientVertices G q T).card := by unfold exceptionalVertices; omega
  have hnr : ((exceptionalVertices G q T).card : ℝ) ≤ (highCycleVertices G q).card +
      (HighSurplus.highVertices G q).card+(SurplusRows.deepDeficient G q).card+
      (giantDeficientVertices G q T).card := by exact_mod_cast hn
  linarith [hb.1,hb.2.2.2.2]

 theorem outside_exceptional_properties (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    (x : V) (hx : x ∉ exceptionalVertices G q T) :
    (G.degree x=q ∨ G.degree x=q+1) ∧
      (Statistics.vertexCycleStatistic G x : ℝ) ≤ 4*(q : ℝ)/5 ∧
      ((G.neighborFinset x ∩ SurplusRows.deficientVertices G q).card : ℝ) ≤ 50*T := by
  classical
  have hA : x ∉ highCycleVertices G q := by
    intro h; exact hx (by simp [exceptionalVertices,h])
  have hH : x ∉ HighSurplus.highVertices G q := by
    intro h; exact hx (by simp [exceptionalVertices,h])
  have hD : x ∉ SurplusRows.deepDeficient G q := by
    intro h; exact hx (by simp [exceptionalVertices,h])
  have hgiant : x ∉ giantDeficientVertices G q T := by
    intro h; exact hx (by simp [exceptionalVertices,h])
  have hdx : G.degree x=q ∨ G.degree x=q+1 := by
    simp only [HighSurplus.highVertices,Finset.mem_filter,Finset.mem_univ,true_and] at hH
    simp only [SurplusRows.deepDeficient,Finset.mem_filter,Finset.mem_univ,true_and] at hD
    unfold Statistics.degreeDeficiency at hD
    omega
  refine ⟨hdx,?_,?_⟩
  · simpa [highCycleVertices] using hA
  · have hf := deficient_support_size_min G q T hq hT hr heven hN hE hZ
    have hsplit := Statistics.deficient_neighbor_dichotomy G q T hq hT hr heven hN
      (SurplusRows.deficientVertices G q) (deficientVertices_iff G q) hf.1 hf.2 hZ x
    rcases hsplit with hsmall | hlarge
    · exact le_of_lt hsmall
    · exact False.elim (hgiant (by simp [giantDeficientVertices,hlarge]))

 theorem opposite_codegree (G : SimpleGraph V) {u v : V} (h : Opposite G u v) :
    2 ≤ Statistics.codegree G u v := by
  classical
  obtain ⟨huv,a,b,hab,hua,hva,hub,hvb⟩ := h
  have hsub : ({a,b} : Finset V) ⊆ G.neighborFinset u ∩ G.neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp_all
  have hc := Finset.card_le_card hsub
  simpa [hab,Statistics.codegree] using hc

 theorem outside_opposite_transport (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    (u v : V) (hu : u ∉ exceptionalVertices G q T) (hv : v ∉ exceptionalVertices G q T)
    (hop : Opposite G u v) :
    (q : ℝ)/20 ≤ ((G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card : ℝ) := by
  have hpu := outside_exceptional_properties G q T hq hT hr heven hN hE hZ u hu
  have hpv := outside_exceptional_properties G q T hq hT hr heven hN hE hZ v hv
  have hdv : q ≤ G.degree v := by rcases hpv.1 with h | h <;> omega
  have ht := Transport.opposite_transport_density G q T hq hT hr heven hN hE hZ
    hop.1 (opposite_codegree G hop) hpu.1 hdv (by nlinarith [hpu.2.1]) hpu.2.2 hpv.2.2
  have he : Transport.neighborCycleCount G v =
      (G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card := by
    unfold Transport.neighborCycleCount Statistics.positiveCycleVertices
    congr 1
    ext x
    simp
  rw [he] at ht
  exact ht.2

/-- Actual linear-support theorem from the frozen LINEAR-SUPPORT-THEOREM.md.
All localization hypotheses have been derived from this actual graph. -/
theorem actual_linear_cycle_support (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ∃ S0 : Finset V, (S0.card : ℝ) ≤ 252*T ∧
      ∀ a b c d : V, a ≠ c → b ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
        (a ∈ S0 ∧ b ∈ S0) ∨ (b ∈ S0 ∧ c ∈ S0) ∨
        (c ∈ S0 ∧ d ∈ S0) ∨ (d ∈ S0 ∧ a ∈ S0) := by
  apply quantitative_cycle_support G (exceptionalVertices G q T) q T hq hT hr hZ
  · exact exceptionalVertices_bound G q T hq hT hr heven hN hE hZ
  · exact outside_opposite_transport G q T hq hT hr heven hN hE hZ

end Erdos60.Localization
