import ActualLocalization
import DegreeCapCore
import CompletionBasic

namespace Erdos60.Localization
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Retain the explicit support constructed by the frozen localization API,
including all original high and deeply deficient vertices. -/
theorem actual_support_with_outside_degrees (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ∃ S0 : Finset V, (S0.card : ℝ) ≤ 252*T ∧
      Core.SupportsEveryFourCycle G S0 ∧
      (∀ v, v ∉ S0 → G.degree v = q ∨ G.degree v = q+1) ∧
      HighSurplus.highVertices G q ∪ SurplusRows.deepDeficient G q ⊆ S0 := by
  let X := exceptionalVertices G q T
  let S0 := X ∪ residualFinset G X
  have hX := exceptionalVertices_bound G q T hq hT hr heven hN hE hZ
  have ht := outside_opposite_transport G q T hq hT hr heven hN hE hZ
  have hs : (S0.card : ℝ) ≤ 252*T :=
    residual_support_of_opposite_transport G X q T hq hT hr hZ hX ht
  refine ⟨S0,hs,?_,?_,?_⟩
  · intro a b c d hac hbd hab hbc hcd hda
    have hh := cycle_has_support_edge G (↑X : Set V) hac hbd hab hbc hcd hda
    simpa only [S0,support,Set.mem_union,Finset.mem_union,mem_residualFinset,
      Finset.mem_coe] using hh
  · intro v hv
    have hvX : v ∉ X := fun h => hv (Finset.mem_union_left _ h)
    exact (outside_exceptional_properties G q T hq hT hr heven hN hE hZ v hvX).1
  · intro v hv
    apply Finset.mem_union_left
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)

/-- One actual core and one actual retained graph, carrying simultaneous
completion and outside-support contracts from the original first-excess host. -/
structure ActualCoreData (G : SimpleGraph V) (q : ℕ) (T : ℝ) where
  core : Finset V
  retained : SimpleGraph V
  retained_eq : retained = Core.outsideGraph G core
  size : (core.card : ℝ) ≤ 292*T
  noFourCycle : Completion.NoFourCycle retained
  cap : ∀ v, retained.degree v ≤ q+1
  lower : ∀ v, (q : ℝ)-318*T ≤ retained.degree v
  outsideDegree : ∀ v, v ∉ core → retained.degree v = G.degree v ∧
    (retained.degree v = q ∨ retained.degree v = q+1)
  outsideAdj : ∀ v w, v ∉ core → (retained.Adj v w ↔ G.Adj v w)
  deficient : ((Core.deficientVertices retained q).card : ℝ) ≤ (q : ℝ)-1+312*T
  deepSubset : Core.deepVertices retained q ⊆ core
  deepCount : ((Core.deepVertices retained q).card : ℝ) ≤ 292*T
  originalDeficient : ((Core.deficientVertices G q).card : ℝ) ≤ (q : ℝ)-1+20*T
  originalMinimum : ∀ v, (q : ℝ)+1-26*T ≤ G.degree v
  originalHighDeep : HighSurplus.highVertices G q ∪ SurplusRows.deepDeficient G q ⊆ core
  orderLarge : 10^8 ≤ q
  completionMinimum : ∀ v, 999*q ≤ 1000*retained.degree v
  completionDeficient : 1000*(Core.deficientVertices retained q).card ≤ 1001*q
  completionDeep : 1000*(Finset.univ.filter (fun v : V => retained.degree v ≤ q-1)).card ≤ q

theorem actual_completion_core (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    Nonempty (ActualCoreData G q T) := by
  classical
  obtain ⟨S0,hsize,hcover,houtside,hhighdeep⟩ :=
    actual_support_with_outside_degrees G q T hq hT hr heven hN hE hZ
  have hb := SurplusRows.localized_deficit_bounds G q T hq hT hr heven hN hE hZ
  have hexcess : ((∑ v : V, (G.degree v-(q+1)) : ℕ) : ℝ) ≤ 20*T := by
    simpa only [Statistics.totalSurplus,Statistics.degreeSurplus] using
      SurplusRows.totalSurplus_bound G q T hq hT hr heven hN hE hZ
  have hmin : ∀ v, (q : ℝ)+1-26*T ≤ G.degree v := by
    intro v
    have hf := hb.2.2.2.1 v
    have hd := Statistics.degree_add_deficiency G q v
    have hn : q+1 ≤ G.degree v+Statistics.degreeDeficiency G q v := by omega
    have hdR : (q : ℝ)+1 ≤ (G.degree v : ℝ)+Statistics.degreeDeficiency G q v := by
      exact_mod_cast hn
    linarith
  have hdefs : Core.deficientVertices G q = SurplusRows.deficientVertices G q := by
    ext v
    simp only [Core.deficientVertices,SurplusRows.deficientVertices,Finset.mem_filter,
      Finset.mem_univ,true_and]
    unfold Statistics.degreeDeficiency
    omega
  have hdef : ((Core.deficientVertices G q).card : ℝ) ≤ (q : ℝ)-1+20*T := by
    rw [hdefs]
    have hc := SurplusRows.deficient_card_le_total G q
    have hcR : ((SurplusRows.deficientVertices G q).card : ℝ) ≤ Statistics.totalDeficiency G q := by
      exact_mod_cast hc
    exact hcR.trans hb.2.1
  obtain ⟨S,hsub,hS,hfree,hcap,hminF,houtF,hdefF,hdeep,hdeepF⟩ :=
    Core.exists_core_292_with_deficiency G S0 q T hcover hsize hexcess hmin houtside hdef
  refine ⟨{
    core := S
    retained := Core.outsideGraph G S
    retained_eq := rfl
    size := hS
    noFourCycle := ?_
    cap := hcap
    lower := hminF
    outsideDegree := houtF
    outsideAdj := ?_
    deficient := hdefF
    deepSubset := hdeep
    deepCount := hdeepF
    originalDeficient := hdef
    originalMinimum := hmin
    originalHighDeep := hhighdeep.trans hsub
    orderLarge := ?_
    completionMinimum := ?_
    completionDeficient := ?_
    completionDeep := ?_ }⟩
  · intro a b c d hac hbd hab hbc hcd hda
    exact hfree a b c d hac hbd hab hbc hcd hda
  · intro v w hv
    change (G.Adj v w ∧ ¬(v ∈ S ∧ w ∈ S)) ↔ G.Adj v w
    simp [hv]
  · have hh : (10^8 : ℝ) ≤ q := by linarith
    exact_mod_cast hh
  · intro v
    have hm := hminF v
    have hh : (999 : ℝ)*q ≤ 1000*((Core.outsideGraph G S).degree v : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (1000 : ℝ)*((Core.deficientVertices (Core.outsideGraph G S) q).card : ℝ) ≤
        1001*q := by linarith
    exact_mod_cast hh
  · have hh : (1000 : ℝ)*((Core.deepVertices (Core.outsideGraph G S) q).card : ℝ) ≤ q := by linarith
    have hnat : 1000*(Core.deepVertices (Core.outsideGraph G S) q).card ≤ q := by exact_mod_cast hh
    have hq1 : 1 ≤ q := by
      have hh : (1 : ℝ) ≤ q := by linarith
      exact_mod_cast hh
    have heq : Finset.univ.filter (fun v : V => (Core.outsideGraph G S).degree v ≤ q-1) =
        Core.deepVertices (Core.outsideGraph G S) q := by
      ext v
      simp only [Core.deepVertices,Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    rwa [heq]

#print axioms actual_support_with_outside_degrees
#print axioms actual_completion_core
end Erdos60.Localization
