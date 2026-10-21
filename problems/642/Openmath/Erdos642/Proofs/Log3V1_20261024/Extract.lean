import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.RegularizationAssembly
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutExtractSubtype
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.AvoidanceHeredity
import Openmath.Erdos642.Proofs.DenseMask20261019.MaskCore

   
                                                                                      
                                                                                   
                               

                                                                                          
                                                        
                                                          
                                                                                             
                                                                                             
           

                                     
                                                        
                                                                                   
                                                                                        
                                                                                
                                                                                 
                                                    
                                                                                             
                                                                                  
  

namespace Erdos642.Log3V1_20261024.Extract

open SimpleGraph
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.CampaignFe72210bContinuation3.GraphExpansionConductance

universe u

                                                                                              
                                                                                          
                                                                                
theorem hasRichCycle_of_host {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (f : H →g G)
    (hf : Function.Injective f) (hH : HasRichCycle H) : HasRichCycle G :=
  hasRichCycle_of_injective_hom f hf hH

/-- Avoidance passes from `G` to every injectively embedded host. -/
theorem not_hasRichCycle_host {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (f : H →g G)
    (hf : Function.Injective f) (hG : ¬ HasRichCycle G) : ¬ HasRichCycle H :=
  not_hasRichCycle_of_injective_hom f hf hG

/-- The written cut constant `a = ln 2 / 6` (synthesis §1, input 2). -/
noncomputable def cutConstant : ℝ := Real.log 2 / 6

/-- The original trigger constant `C₁ = 200 K` (synthesis §2). -/
noncomputable def hostConstant (K : ℝ) : ℝ := 200 * K

theorem cutConstant_pos : 0 < cutConstant := by
  unfold cutConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Elementary logarithm facts for `n ≥ 3` and `L = ln(2n)`. -/
theorem log_facts (n : ℕ) (hn : 3 ≤ n) :
    0 < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) ∧
      0 < Real.log (2 * (n : ℝ)) ∧ cutConstant ≤ Real.log (2 * (n : ℝ)) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hle : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h2L : Real.log (2 : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  refine ⟨hlogn, hle, hlogn.trans_le hle, ?_⟩
  unfold cutConstant
  linarith

/-- `a/L ≤ lossParameter n / 3`, i.e. `ln 2/(6 ln(2n)) ≤ ln 2/(6 ln n)`. -/
theorem cutRate_le_loss (n : ℕ) (hn : 3 ≤ n) :
    cutConstant / Real.log (2 * (n : ℝ)) ≤ lossParameter n / 3 := by
  obtain ⟨hlogn, hle, _, _⟩ := log_facts n hn
  unfold cutConstant lossParameter
  rw [div_div, div_div]
  refine div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) ?_ ?_
  · linarith
  · linarith

/-- `a/L ≤ 1`. -/
theorem cutRate_le_one (n : ℕ) (hn : 3 ≤ n) :
    cutConstant / Real.log (2 * (n : ℝ)) ≤ 1 := by
  obtain ⟨_, _, hL0, haL⟩ := log_facts n hn
  rw [div_le_one hL0]
  exact haL

omit [DecidableEq V] in
/-- The strict original edge trigger gives `D = graphAverage G > 400 K L³`. -/
theorem average_gt_of_edges (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℝ)
    (hn : 3 ≤ Fintype.card V)
    (he : hostConstant K * (Fintype.card V : ℝ) * Real.log (2 * (Fintype.card V : ℝ)) ^ 3 <
      (G.edgeFinset.card : ℝ)) :
    400 * K * Real.log (2 * (Fintype.card V : ℝ)) ^ 3 < graphAverage G := by
  have hnpos : (0 : ℝ) < Fintype.card V := by
    have : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hD : graphAverage G = 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) := by
    unfold graphAverage
    rw [degreeVolume_eq_twice_edges]
  rw [hD, lt_div_iff₀ hnpos]
  unfold hostConstant at he
  have hring : 400 * K * Real.log (2 * (Fintype.card V : ℝ)) ^ 3 * (Fintype.card V : ℝ) =
      2 * (200 * K * (Fintype.card V : ℝ) * Real.log (2 * (Fintype.card V : ℝ)) ^ 3) := by
    ring
  rw [hring]
  linarith

/-- `D > 400 K L³` and `0 < ln n ≤ L` give `D/(400 ln n) ≥ K L²`. -/
theorem degree_scale_ge (K D ℓ L : ℝ) (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L)
    (hD : 400 * K * L ^ 3 < D) : K * L ^ 2 ≤ D / (400 * ℓ) := by
  have h400 : 0 < 400 * ℓ := by linarith
  rw [le_div_iff₀ h400]
  have hKL : 0 ≤ 400 * (K * L ^ 2) := mul_nonneg (by norm_num) (mul_nonneg hK (sq_nonneg L))
  have h1 : 400 * (K * L ^ 2) * ℓ ≤ 400 * (K * L ^ 2) * L :=
    mul_le_mul_of_nonneg_left hℓL hKL
  have h2 : K * L ^ 2 * (400 * ℓ) = 400 * (K * L ^ 2) * ℓ := by ring
  have h3 : 400 * (K * L ^ 2) * L = 400 * K * L ^ 3 := by ring
  rw [h2]
  linarith

attribute [-instance] FinsetCoe.fintype in
/-- Stage-3 host theorem. For every `K ≥ 0`, with `C₁ = 200 K`, `L = ln(2n)` and
`a = ln 2/6`: every finite simple `G` on `n ≥ 3` vertices with `C₁ n L³ < e(G)` that avoids
rich cycles has an injectively embedded host `H` (on an abstract finite type) satisfying the
host hypotheses of `MaskCore.exists_dense_mask` verbatim, with `d = minDegree H` and
`φ = a/L`, and avoiding rich cycles itself. -/
theorem exists_mask_host (K : ℝ) (hK : 0 ≤ K) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (he : hostConstant K * (Fintype.card V : ℝ) * Real.log (2 * (Fintype.card V : ℝ)) ^ 3 <
      (G.edgeFinset.card : ℝ))
    (ha : ¬ HasRichCycle G) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj) (f : H →g G),
      Function.Injective f ∧ ¬ HasRichCycle H ∧ H.IsBipartite ∧ H.Connected ∧
      Fintype.card W ≤ Fintype.card V ∧
      ∃ d φ : ℝ, d = (H.minDegree : ℝ) ∧
        φ = cutConstant / Real.log (2 * (Fintype.card V : ℝ)) ∧
        0 < Fintype.card W ∧
        (∀ v, d ≤ (H.degree v : ℝ)) ∧ (∀ v, (H.degree v : ℝ) ≤ 100 * d) ∧
        (∀ X : Finset W, (X.card : ℝ) ≤ (Fintype.card W : ℝ) / 2 →
          φ * d * (X.card : ℝ) ≤ crossing H X) ∧
        K * Real.log (2 * (Fintype.card V : ℝ)) ^ 2 ≤ d ∧
        cutConstant / Real.log (2 * (Fintype.card V : ℝ)) ≤ φ ∧ φ ≤ 1 ∧
        Real.log (2 * (Fintype.card W : ℝ)) ≤ Real.log (2 * (Fintype.card V : ℝ)) := by
  have hn2 : 2 ≤ Fintype.card V := by omega
  obtain ⟨hlogn, hlognL, hL0, _⟩ := log_facts (Fintype.card V) hn
  have hD := average_gt_of_edges G K hn he
  have hDpos : 0 < graphAverage G := by
    have h0 : 0 ≤ 400 * K * Real.log (2 * (Fintype.card V : ℝ)) ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hK) (pow_nonneg hL0.le 3)
    linarith
                                                                                       
  obtain ⟨S, hSne, J, instJ, hmap, hJbip, hJpos, hJret, _hJdegree, hJratio, hJorder⟩ :=
    RegularizationAssembly.exists_regularized_subgraph G hn2 hDpos
  let : DecidableRel J.Adj := instJ
  have : Nonempty (S : Set V) := hSne.to_subtype
  obtain ⟨xmin, hxmin⟩ := J.exists_minimal_degree_vertex
  have hratio3 : J.maxDegree ≤ 3 * J.minDegree := by
    apply J.maxDegree_le_of_forall_degree_le
    intro x
    rw [hxmin]
    exact hJratio x xmin
  have hratio6 : J.maxDegree ≤ 6 * J.minDegree := by omega
                                                     
  obtain ⟨W, hWne, hWorder, _hHpos, _hHret, hHmin, _hH24, hHratio, hHbip, hHconn, hHexpand,
      _hHgap⟩ :=
    CutExtraction.exists_induced_cut_expander J (Fintype.card V) hn2 hJorder hJpos hJbip hratio6
  have : Nonempty (W : Set (S : Set V)) := hWne.to_subtype
  let H := J.induce (W : Set (S : Set V))
  let f : H →g G :=
    { toFun := fun x => x.val.val
      map_rel' := fun h => hmap _ _ h }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  have hmin : graphAverage G / (400 * Real.log (Fintype.card V : ℝ)) ≤ (H.minDegree : ℝ) := by
    calc
      _ = (graphAverage G / (100 * Real.log (Fintype.card V : ℝ))) / 4 := by
        ring
      _ ≤ graphAverage J / 4 := div_le_div_of_nonneg_right hJret (by norm_num)
      _ ≤ _ := hHmin
  have hdK : K * Real.log (2 * (Fintype.card V : ℝ)) ^ 2 ≤ (H.minDegree : ℝ) :=
    (degree_scale_ge K _ _ _ hK hlogn hlognL hD).trans hmin
  have hd_avg : (H.minDegree : ℝ) ≤ graphAverage H := average_degree_ge_min H
  have hphi_le := cutRate_le_loss (Fintype.card V) hn
  have hphi0 : 0 ≤ cutConstant / Real.log (2 * (Fintype.card V : ℝ)) :=
    div_nonneg cutConstant_pos.le hL0.le
  have hcut : ∀ X : Finset (W : Set (S : Set V)),
      (X.card : ℝ) ≤ (Fintype.card (W : Set (S : Set V)) : ℝ) / 2 →
      cutConstant / Real.log (2 * (Fintype.card V : ℝ)) * (H.minDegree : ℝ) * (X.card : ℝ) ≤
        crossing H X := by
    intro X hX
    refine le_trans ?_ (hHexpand X hX)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul hphi_le hd_avg (Nat.cast_nonneg _) (hphi0.trans hphi_le)
  have hcardW : Fintype.card (W : Set (S : Set V)) ≤ Fintype.card V := hWorder.trans hJorder
  have hWpos : 0 < Fintype.card (W : Set (S : Set V)) := Fintype.card_pos
  have hLW : Real.log (2 * (Fintype.card (W : Set (S : Set V)) : ℝ)) ≤
      Real.log (2 * (Fintype.card V : ℝ)) := by
    have h0 : (0 : ℝ) < Fintype.card (W : Set (S : Set V)) := by exact_mod_cast hWpos
    have h1 : (Fintype.card (W : Set (S : Set V)) : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hcardW
    exact Real.log_le_log (by linarith) (by linarith)
  have hlo : ∀ v, (H.minDegree : ℝ) ≤ (H.degree v : ℝ) := by
    intro v
    exact_mod_cast H.minDegree_le_degree v
  have hhi : ∀ v, (H.degree v : ℝ) ≤ 100 * (H.minDegree : ℝ) := by
    intro v
    have h1 : H.degree v ≤ 100 * H.minDegree := (H.degree_le_maxDegree v).trans hHratio
    exact_mod_cast h1
  exact ⟨↥(W : Set (S : Set V)), inferInstance, inferInstance, H, inferInstance, f, hf,
    not_hasRichCycle_of_injective_hom f hf ha, hHbip, hHconn, hcardW,
    (H.minDegree : ℝ), cutConstant / Real.log (2 * (Fintype.card V : ℝ)), rfl, rfl, hWpos,
    hlo, hhi, hcut, hdK, le_rfl, cutRate_le_one (Fintype.card V) hn, hLW⟩

/-- Stage-3 host fed to the stage-2 dense mask, for stage 7. The caller fixes `C0` and `K` with
`800/a ≤ C0`, `16 C0² ≤ K`, `64 C0 ≤ K` (synthesis §2) and `p = 1/(C0 L)`; the conclusion
after the host data is `MaskCore.exists_dense_mask`'s conclusion verbatim, for the host `H`,
`d = minDegree H` and `φ = a/L`. -/
theorem exists_dense_mask_host (K C0 p : ℝ) (hC0 : 800 / cutConstant ≤ C0)
    (hK1 : 16 * C0 ^ 2 ≤ K) (hK2 : 64 * C0 ≤ K) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hp : p = 1 / (C0 * Real.log (2 * (Fintype.card V : ℝ))))
    (he : hostConstant K * (Fintype.card V : ℝ) * Real.log (2 * (Fintype.card V : ℝ)) ^ 3 <
      (G.edgeFinset.card : ℝ))
    (ha : ¬ HasRichCycle G) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj) (f : H →g G),
      Function.Injective f ∧ ¬ HasRichCycle H ∧ H.IsBipartite ∧ H.Connected ∧
      Fintype.card W ≤ Fintype.card V ∧
      ∃ d φ : ℝ, d = (H.minDegree : ℝ) ∧
        φ = cutConstant / Real.log (2 * (Fintype.card V : ℝ)) ∧
        0 < Fintype.card W ∧
        (∀ v, d ≤ (H.degree v : ℝ)) ∧ (∀ v, (H.degree v : ℝ) ≤ 100 * d) ∧
        K * Real.log (2 * (Fintype.card V : ℝ)) ^ 2 ≤ d ∧
        ∃ Q R : Finset W, R = Qᶜ ∧
          (∀ v, p*(H.degree v : ℝ)/2 ≤ ((H.neighborFinset v ∩ Q).card : ℝ) ∧
            ((H.neighborFinset v ∩ Q).card : ℝ) ≤ 2*p*(H.degree v : ℝ)) ∧
          (p*(Fintype.card W : ℝ)/2 ≤ (Q.card : ℝ) ∧
            (Q.card : ℝ) ≤ 2*p*(Fintype.card W : ℝ) ∧ 2 ≤ Q.card) ∧
          2*Fintype.card W ≤ inducedEdges H Q ∧
          (∀ v, 3*d/4 ≤ ((H.neighborFinset v ∩ R).card : ℝ)) ∧
          (∀ [Fintype (Set.Elem (R : Set W))] [DecidableEq (Set.Elem (R : Set W))]
            [DecidableRel (H.induce (R : Set W)).Adj],
            DenseMask20261019.CutEscape.Expands (H.induce (R : Set W)) (3*φ/1600)) ∧
          Fintype.card W ≤ 2*R.card := by
  have hK : 0 ≤ K := by
    have := sq_nonneg C0
    linarith
  obtain ⟨W, instF, instD, H, instR, f, hf, havoid, hbip, hconn, hcard, d, φ, hd, hφ, hN,
      hlo, hhi, hcut, hdK, hφa, hφ1, hL⟩ := exists_mask_host K hK G hn he ha
  exact ⟨W, instF, instD, H, instR, f, hf, havoid, hbip, hconn, hcard, d, φ, hd, hφ, hN,
    hlo, hhi, hdK,
    DenseMask20261019.MaskCore.exists_dense_mask H cutConstant C0 K
      (Real.log (2 * (Fintype.card V : ℝ))) φ d p hN hlo hhi hcut hp cutConstant_pos hC0
      hK1 hK2 hdK hφa hφ1 hL⟩

end Erdos642.Log3V1_20261024.Extract
