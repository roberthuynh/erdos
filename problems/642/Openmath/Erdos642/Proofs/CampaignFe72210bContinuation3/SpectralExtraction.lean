import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.ExtractParameters
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.RegularizationAssembly

/-! Genuine regularization, cut descent and normalized gap composed on actual subgraphs. -/
namespace Erdos642.CampaignFe72210bContinuation3.SpectralExtraction
open Erdos642.CampaignFe72210b CutExtraction
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [-instance] FinsetCoe.fintype in
/-- Original graph density produces an actual injectively embedded spectral host.
The nested subtype records the actual noninduced regularization then induced cut graph. -/
theorem exists_spectral_host (hn : 3≤Fintype.card V)
    (hD : ExtractParameters.baseConstant*(Real.log (Fintype.card V:ℝ))^2 ≤ graphAverage G) :
    ∃ S : Finset V, S.Nonempty ∧ ∃ J : SimpleGraph (S:Set V),
    ∃ _ : DecidableRel J.Adj, ∃ W : Finset (S:Set V), W.Nonempty ∧
      let H := J.induce (W:Set (S:Set V))
      ∃ f : H →g G, Function.Injective f ∧
        3 ≤ Fintype.card (W:Set (S:Set V)) ∧
        Fintype.card (W:Set (S:Set V)) ≤ Fintype.card V ∧
        0 < graphAverage H ∧
        graphAverage G/(400*Real.log (Fintype.card V:ℝ)) ≤ (H.minDegree:ℝ) ∧
        H.maxDegree ≤ 100*H.minDegree ∧ H.IsBipartite ∧ H.Connected ∧
        HasBipartiteSpectralGap H (ExtractParameters.suppliedGap (Fintype.card V)) := by
  classical
  let n := Fintype.card V
  let D := graphAverage G
  have hell := IntegrationParameters.log_order_gt_one n hn
  have hDpos : 0<D := by
    have hb : 0<ExtractParameters.baseConstant := by norm_num [ExtractParameters.baseConstant]
    exact (mul_pos hb (sq_pos_of_pos (by linarith))).trans_le hD
  -- The frozen supplier returns the reducible actual-graph predicate Regularized.
  obtain ⟨S,hSne,J,instJ,hmap,hJbip,hJpos,hJret,_hJdegree,hJratio,hJorder⟩ :=
    RegularizationAssembly.exists_regularized_subgraph G (by omega) hDpos
  let : DecidableRel J.Adj := instJ
  have : Nonempty (S:Set V) := hSne.to_subtype
  obtain ⟨xmin,hxmin⟩ := J.exists_minimal_degree_vertex
  have hratio3 : J.maxDegree ≤ 3*J.minDegree := by
    apply J.maxDegree_le_of_forall_degree_le
    intro x
    rw [hxmin]
    exact hJratio x xmin
  have hratio6 : J.maxDegree ≤ 6*J.minDegree := by omega
  obtain ⟨W,hWne,hWorder,hHpos,hHret,hHmin,_hH24,hHratio,hHbip,hHconn,_hHexpand,hHgap⟩ :=
    CutExtraction.exists_induced_cut_expander J n (by omega) hJorder hJpos hJbip hratio6
  have : Nonempty (W:Set (S:Set V)) := hWne.to_subtype
  let H := J.induce (W:Set (S:Set V))
  let f : H →g G :=
    { toFun := fun x => x.val.val
      map_rel' := fun h => hmap _ _ h }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  have hmin : D/(400*Real.log (n:ℝ)) ≤ (H.minDegree:ℝ) := by
    calc
      _ = (D/(100*Real.log (n:ℝ)))/4 := by
        field_simp
        ring
      _ ≤ graphAverage J/4 := div_le_div_of_nonneg_right hJret (by norm_num)
      _ ≤ _ := hHmin
  have htwo : (2:ℝ) ≤ (H.minDegree:ℝ) :=
    (ExtractParameters.degree_scale_ge_two n hn D hD).trans hmin
  have hHthree : 3≤Fintype.card (W:Set (S:Set V)) := by
    let x : (W:Set (S:Set V)) := Classical.choice inferInstance
    have hminNat : 2≤H.minDegree := by exact_mod_cast htwo
    have hdegree := H.minDegree_le_degree x
    have hcard := H.degree_lt_card_verts x
    omega
  have hsmall := ExtractParameters.gap_comparison n hn
  have hgap : HasBipartiteSpectralGap H (ExtractParameters.suppliedGap n) :=
    ExtractParameters.actual_gap_weaken H _ _ hHgap hsmall.1 hsmall.2
  exact ⟨S,hSne,J,instJ,W,hWne,f,hf,hHthree,hWorder.trans hJorder,hHpos,hmin,
    hHratio,hHbip,hHconn,hgap⟩
end Erdos642.CampaignFe72210bContinuation3.SpectralExtraction
