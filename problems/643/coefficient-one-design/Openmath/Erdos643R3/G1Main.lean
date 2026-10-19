import Openmath.Erdos643R3.G1Combinatorics
import Openmath.Erdos643R3.G1Bicone
import Openmath.Erdos643R3.G1Threshold

set_option autoImplicit false
namespace Erdos643R3.G1Main
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound
  Erdos643R3.SlotModel Erdos643R3.Lemma1g Erdos643R3.Lemma3 Erdos643R3.Pw2312
  Erdos643R3.G1Combinatorics Erdos643R3.L1Top
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- Theorem G1(i), in slot counts: exactly one type-2 slot in a deficient triple. -/
theorem deficient_type2_eq_one {a b c : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a,b,c} + tauW H {a,b,c} < 2) :
    (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1 := by
  have hp := deficient_type2_pos hT hH hav hd
  by_contra hn
  have hg : 2 ≤ (profileOf H a b c).t0 + (profileOf H a b c).t1 + (profileOf H a b c).t2 := by
    change 2 ≤ (tset H a b c).card + (tset H b c a).card + (tset H c a b).card
    omega
  have hL := lemma3 hT hH hav
  have := G1Threshold.theorem4g_a (profileOf H a b c) hL.2 hg
  linarith [hL.1]

/-- Theorem G1: the deficient profile with its type-2 slot in A satisfies the G1 pattern. -/
theorem deficient_compliant {a b c z : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a,b,c} + tauW H {a,b,c} < 2) (hz : z ∈ tset H a b c) :
    G1Combinatorics.Compliant0 (profileOf H a b c) := by
  have ht := deficient_type2_eq_one hT hH hav hd
  obtain ⟨htA,htB,htC⟩ := unique_type2 hz ht
  have h0 : (profileOf H a b c).t0 = 1 := by change (tset H a b c).card = 1; rw [htA]; simp
  have h1 : (profileOf H a b c).t1 = 0 := by change (tset H b c a).card = 0; rw [htB]; simp
  have h2 : (profileOf H a b c).t2 = 0 := by change (tset H c a b).card = 0; rw [htC]; simp
  by_contra hc
  have hc' : ¬ G1Threshold.Compliant0 (profileOf H a b c) := hc
  have hL := lemma3 hT hH hav
  have := G1Threshold.theorem4g_b (profileOf H a b c) hL.2 h0 h1 h2 hc'
  linarith [hL.1]

/-- Theorem G1(ii)-(iii), for the type-2 slot and its actual partner. -/
theorem deficient_geometric {a b c z w : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a,b,c} + tauW H {a,b,c} < 2) (hz : z ∈ tset H a b c)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w}) :
    GeometricG1 (H := H) a b c w := by
  have hi := deficient_isolated_zero hT hH hav hd
  exact (compliant_iff_geometric hT hH hav hz (deficient_type2_eq_one hT hH hav hd) hb hc hi.2.1 hi.2.2).mp
    (deficient_compliant hT hH hav hd hz)

/-- A concrete G1 witness with its exact common-link and unique triangle-option identities. -/
def Witness (a b c z w : V) : Prop :=
  z ∈ tset H a b c ∧ nb H a b c z = {w} ∧ nc H a b c z = {w} ∧
    CN H {a,z} = {{b,c},{b,w},{c,w}} ∧
    (options H a b c).filter (Triangular H) = {{a,z}} ∧
    GeometricG1 (H := H) a b c w

/-- Assemble the exact G1 witness once its type-2 slot is oriented into group A. -/
theorem witness_of_type2 {a b c z : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a,b,c} + tauW H {a,b,c} < 2) (hz : z ∈ tset H a b c) :
    ∃ w, Witness (H := H) a b c z w := by
  have hzA := (mem_filter.mp hz).1
  have hzb := (mem_filter.mp hz).2.1
  have hzc := (mem_filter.mp hz).2.2
  obtain ⟨w,hb,hc⟩ := lemma2 hT hH hav hzA (card_pos.mp hzb) (card_pos.mp hzc)
  exact ⟨w,hz,hb,hc,CN_type2 hT hH hav hzA hb hc,
    unique_triangle_option hT hH hav hz (deficient_type2_eq_one hT hH hav hd),
    deficient_geometric hT hH hav hd hz hb hc⟩

/-- **Theorem G1**, with an explicit cyclic orientation of every deficient triple. -/
theorem theoremG1 {a b c : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a,b,c} + tauW H {a,b,c} < 2) :
    (∃ z w, Witness (H := H) a b c z w) ∨
    (∃ z w, Witness (H := H) b c a z w) ∨
    (∃ z w, Witness (H := H) c a b z w) := by
  have ht := deficient_type2_eq_one hT hH hav hd
  by_cases hA : 0 < (tset H a b c).card
  · obtain ⟨z,hz⟩ := card_pos.mp hA
    obtain ⟨w,hw⟩ := witness_of_type2 hT hH hav hd hz
    exact Or.inl ⟨z,w,hw⟩
  by_cases hB : 0 < (tset H b c a).card
  · obtain ⟨z,hz⟩ := card_pos.mp hB
    have e : ({b,c,a} : Finset V) = {a,b,c} := triple_perm (fun t => by tauto)
    obtain ⟨w,hw⟩ := witness_of_type2 (triple_rot hT) hH hav (by rwa [e]) hz
    exact Or.inr (Or.inl ⟨z,w,hw⟩)
  have hC : 0 < (tset H c a b).card := by omega
  obtain ⟨z,hz⟩ := card_pos.mp hC
  have e : ({c,a,b} : Finset V) = {a,b,c} := triple_perm (fun t => by tauto)
  obtain ⟨w,hw⟩ := witness_of_type2 (triple_rot (triple_rot hT)) hH hav (by rwa [e]) hz
  exact Or.inr (Or.inr ⟨z,w,hw⟩)

/-- Every deficient triple belongs to exactly one active bicone. -/
theorem deficient_act_eq_one {a b c : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a,b,c} + tauW H {a,b,c} < 2) : act H {a,b,c} = 1 := by
  rw [G1Bicone.deficient_act_eq_triangle_options hT hH (by
    unfold Deficient charge
    linarith), card_triangle_options hT hH hav]
  exact deficient_type2_eq_one hT hH hav hd

/-- Corollary 6g, unconditional for the singleton-C orientation of a deficient triple. -/
theorem corollary6g {a b c z w : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a,b,c} + tauW H {a,b,c} < 2) (hz : z ∈ tset H a b c)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w}) (hC : grp H c a b = {w}) :
    (tset H a b c).card = 1 ∧ (tset H b c a).card = 0 ∧ (tset H c a b).card = 0 ∧
    (gset H a b c).card = 0 ∧ (gset H c a b).card = 0 ∧ (fset H b c a).card = 0 ∧
    (fset H c a b).card = 1 ∧ (grp H a b c).card = 1 + (fset H a b c).card ∧
    (grp H b c a).card = (gset H b c a).card := by
  have hi := deficient_isolated_zero hT hH hav hd
  exact compliant_shape hz (deficient_type2_eq_one hT hH hav hd) hb hc hi.1 hi.2.1 hi.2.2 hC
    (deficient_compliant hT hH hav hd hz)

end Erdos643R3.G1Main
