import L34MinimumSupport.Quotas

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.L34MinimumSupport
open QB4 B5
universe u

open scoped Classical in
/-- Bare L34 support consequence on original vertices and original edge units. -/
theorem l34_minimum_support (q : ℕ) (hq : 5 ≤ q) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 2 * q - 2)
    (hn : 2 * q ≤ Fintype.card V)
    (he : (q - 1) * Fintype.card V - (2 * q - 5) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      4 * q - 6 ≤ H.verts.ncard := by
  classical
  by_cases hq5 : q = 5
  · subst q
    exact BqMinimumSupport.bq_minimum_support 5 (by omega) G hbip hdeg (by omega)
      (by simpa using he)
  have hq6 : 6 ≤ q := by omega
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U,W,_,hUW,hcover,hbw⟩ := exists_sides hbip o
  have hcard : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW,hcover,card_univ]
  have hec := ec_eq_ncard hbw
  have hnontrunc : (2 * q - 5) ≤ (q - 1) * Fintype.card V := by
    have hm := Nat.mul_le_mul_right (Fintype.card V) (by omega : 1 ≤ q - 1)
    simp only [one_mul] at hm
    omega
  have hDense : (q - 1) * (#U + #W) ≤ ec G U W + (2 * q - 5) := by
    rw [hcard,hec]
    omega
  obtain ⟨P,hP,Q,hQ,hnPQ,hePQ,hminimum⟩ := minimum_dense_source q U W (by omega) hDense
  have hPQ := hUW.mono hP hQ
  have hlarge := dense_order hq6 hnPQ hePQ
  obtain ⟨K,hKG,heK,hminP,hcapP,hminQ,hcapQ,hs⟩ := thinned_source hq6 hPQ hnPQ hePQ
    (fun a _ => (dg_le_maxDegree Q a).trans hdeg)
    (fun a _ => (dg_le_maxDegree P a).trans hdeg) hminimum
  obtain ⟨A,B,_,_,hAB,hretain,hfactor⟩ := retained_factor (G := K) hq6 hPQ hnPQ
    hminP hcapP hminQ hcapQ heK hs
  obtain ⟨H,hne,hreg,hsize⟩ := BqMinimumSupport.factor_subgraph (G := G)
    (by omega : 0 < q) hAB (by omega)
    (BqMinimumSupport.factor_mono_graph hKG hfactor)
  exact ⟨H,hne,hreg,by omega⟩

end Erdos585.L34MinimumSupport
