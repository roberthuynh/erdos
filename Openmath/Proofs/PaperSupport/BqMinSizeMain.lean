import Openmath.Proofs.PaperSupport.BqMinSizeBridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.BqMinimumSupport
open QB4 B5
universe u

/-- Bare original-graph endpoint, with every dense-source guard supplied internally. -/
theorem bq_minimum_support : MinimumSupportEndpoint.{u} := by
  classical
  intro q hq V _ G hbip hcap hn he
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U,W,_,hUW,hcover,hbw⟩ := exists_sides hbip o
  have hcard : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW,hcover,card_univ]
  have hec := ec_eq_ncard hbw
  have hnontrunc := BqOrder.threshold_nontruncated hq hn
  have hDense : (q - 1) * (#U + #W) ≤ ec G U W + q := by
    rw [hcard,hec]
    omega
  obtain ⟨P,hP,Q,hQ,hnPQ,hePQ,hminimum⟩ := minimum_dense_source q U W (by omega) hDense
  have hPQ := hUW.mono hP hQ
  have hlarge := dense_order hq hnPQ hePQ
  obtain ⟨K,hKG,heK,hminP,hcapP,hminQ,hcapQ,hs⟩ := thinned_source hq hPQ hnPQ hePQ
    (fun a _ => (dg_le_maxDegree Q a).trans hcap)
    (fun a _ => (dg_le_maxDegree P a).trans hcap) hminimum
  obtain ⟨A,B,_,_,hAB,hretain,hfactor⟩ := retained_factor (G := K) hq hPQ (by omega)
    hminP hcapP hminQ hcapQ heK hs
  obtain ⟨H,hne,hreg,hsize⟩ := factor_subgraph (G := G) (by omega : 0 < q) hAB
    (by omega) (factor_mono_graph hKG hfactor)
  exact ⟨H,hne,hreg,by omega⟩
end Erdos585.BqMinimumSupport
