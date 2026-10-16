import R882.Terminal
import R882.Normalization
import R882.Quantitative
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R882
open QB4 B5 R837 NEQAssembly R866
universe u

/-- Every h forcing on the literal original finite graph. All critical support,
edge thinning, deletion, orientation and selector hypotheses are internal. -/
theorem every_h_forcing (h q : ℕ) (hh : 6 ≤ h)
    (hq : 4096*(h+1)^2 ≤ q)
    (hcubic : 12*(h:ℤ)^3-40*(h:ℤ)^2+42*(h:ℤ)-15 ≤ q) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hn : 2*q ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2*q-2)
    (he : ((q:ℤ)-1)*Fintype.card V-(G.edgeSet.ncard:ℤ) ≤ (h:ℤ)*q-16*h^2) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  by_contra hno
  obtain ⟨A,B,S,K,hdis,hcov,hS,hKG,hbS,hnS,hcapS,hminS,heS,hnoS,hfloor⟩ :=
    Normalization.original_graph_normalization h q hh hq G hbip hn hcap he hno
  letI : DecidableRel K.Adj := Classical.decRel _
  have hq32 := Normalization.cutoff h q hh hq
  have hcast := Normalization.F_cast hq32
  have hqpos : 1 ≤ q := by omega
  have hcp : Capped K (2*(q-1)) S := by
    convert hcapS using 1 <;> omega
  have host : R837.Host h q K S := {
    height := hh,large := (numeric hh hq).1,induced := hbS,order := hnS,
    minimum := hminS,cap := hcp,
    exact_deficit := by rw [heS,hcast],
    proper := by simpa only [R837.StrictFloor,hcast] using hfloor }
  obtain ⟨T,red⟩ := exists_threshold_reduction host
  let c : ℤ := deficit K (q-1) T-deficit K (q-1) S
  let e : ℕ := c.toNat
  have hc0 : 0 ≤ c := red.cost_nonnegative
  have hce : (e:ℤ)=c := Int.toNat_of_nonneg hc0
  have hemax : e ≤ 4*h^2-10*h+4 := by
    have hhmax := red.cost_upper
    change c ≤ _ at hhmax
    rw [← hce,← R866.budget_cast hh] at hhmax
    exact_mod_cast hhmax
  have hbT := red.induced
  have htotal : ((q:ℤ)-1)*Fintype.card (Carrier T)-
      ((K.induce (Carrier T)).edgeSet.ncard:ℤ)=(h:ℤ)*q-16*h^2+e := by
    rw [carrier_deficit K T hbT hqpos]
    have hf := host.exact_deficit
    dsimp [c] at hce
    linarith
  have hproper : ∀ U : Finset (Carrier T), h≤#U → #U<Fintype.card (Carrier T) →
      (h:ℤ)*q-16*h^2+1≤((q:ℤ)-1)*#U-
        (((K.induce (Carrier T)).induce (U : Set (Carrier T))).edgeSet.ncard:ℤ) := by
    apply carrier_subset_floor K T hbT hqpos
    intro U hUT hu hp
    apply host.proper U ⟨hUT.1.trans red.included.1,hUT.2.trans red.included.2⟩ hu
    have ho := Nat.add_le_add (card_le_card red.included.1) (card_le_card red.included.2)
    change order T ≤ order S at ho
    omega
  have hhigh : ∀ v : Carrier T, q+2*h-4 ≤ (K.induce (Carrier T)).degree v := by
    intro v
    have hv := v.property
    rcases mem_union.mp hv with ha | hb
    · rw [carrier_degree_left K T hbT v (by simpa [sideA] using ha)]
      exact red.minimum.1 v ha
    · rw [carrier_degree_right K T hbT v (by simpa [sideB] using hb)]
      exact red.minimum.2 v hb
  have hcapterm : ∀ v : Carrier T, (K.induce (Carrier T)).degree v ≤ 2*q-2 := by
    intro v
    have hv := v.property
    rcases mem_union.mp hv with ha | hb
    · rw [carrier_degree_left K T hbT v (by simpa [sideA] using ha)]
      have hc:=red.cap.1 v ha
      omega
    · rw [carrier_degree_right K T hbT v (by simpa [sideB] using hb)]
      have hc:=red.cap.2 v hb
      omega
  have hgapterm : |(#(sideB T):ℤ)-#(sideA T)| ≤ (h:ℤ)-1 := by
    rw [card_sideA,card_sideB]
    exact retained_imbalance host red
  have factor := terminal_unoriented (K.induce (Carrier T)) (sideA T) (sideB T)
    h q e hh hq hcubic hemax (sides_disjoint T hbT.1) (by
      ext v
      simp only [mem_union,mem_univ]
      have hv := v.property
      simpa [sideA,sideB] using hv)
    (carrier_bipartite K T hbT) (by rw [carrier_order T hbT.1];exact red.order)
    hhigh hcapterm htotal hproper hgapterm
  have kfactor := NEQAssembly.original_induced_regular_transport K (T.1 ∪ T.2) factor
  exact hno (NEQ.original_regular_transport hKG kfactor)

/-- Exact signed cutoff, with no natural subtraction in the cubic term. -/
def cubic_cutoff (h : ℕ) : ℤ :=
  max (4096*((h:ℤ)+1)^2) (12*(h:ℤ)^3-40*(h:ℤ)^2+42*(h:ℤ)-15)

/-- The exact max-cutoff version of the original-graph theorem. -/
theorem cubic_forcing (h q : ℕ) (hh : 6 ≤ h) (hq : cubic_cutoff h ≤ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hn : 2*q ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2*q-2)
    (he : ((q:ℤ)-1)*Fintype.card V-(G.edgeSet.ncard:ℤ) ≤ (h:ℤ)*q-16*h^2) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  have hquad : 4096*(h+1)^2 ≤ q := by
    have hl := (le_max_left (4096*((h:ℤ)+1)^2)
      (12*(h:ℤ)^3-40*(h:ℤ)^2+42*(h:ℤ)-15)).trans hq
    exact_mod_cast hl
  exact every_h_forcing h q hh hquad (le_max_right _ _ |>.trans hq) G hbip hn hcap he

/-- Literal real four-thirds deficit forces an actual original regular subgraph. -/
theorem superlinear_forcing (q : ℕ) (hq : 2^30 ≤ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hn : 2*q ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2*q-2)
    (he : ((q:ℝ)-1)*Fintype.card V-(G.edgeSet.ncard:ℝ) ≤
      Real.rpow (q:ℝ) (4/3:ℝ)/8) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨hh,hcut,hcube,hdef⟩ := quantitative_numeric q hq
  apply every_h_forcing (height q) q hh hcut hcube G hbip hn hcap
  exact_mod_cast he.trans hdef

#print axioms cubic_forcing
#print axioms every_h_forcing
#print axioms superlinear_forcing
end Erdos585.R882
