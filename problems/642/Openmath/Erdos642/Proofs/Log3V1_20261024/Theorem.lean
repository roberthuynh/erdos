import Openmath.Erdos642.Proofs.Log3V1_20261024.Extract
import Openmath.Erdos642.Proofs.Log3V1_20261024.LayerHall
import Openmath.Erdos642.Proofs.Log3V1_20261024.ToughPaths
import Openmath.Erdos642.Proofs.Log3V1_20261024.Merger
import Openmath.Erdos642.Proofs.Log3V1_20261024.Constants
import Openmath.Erdos642.Proofs.DenseMask20261019.GraphPayment

   
                                                                                       
                                                                                   
                               

                                                                                               
                                                                                                
                                                                        

                              
                                                                               
                                                                                                 
                                                                                  
                                                                                       
                                                            
                                                               
                                                                                           
                                                                           
                                                                                        
                                                                                           
  

namespace Erdos642.Log3V1_20261024

open SimpleGraph
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.GraphExpansionConductance
open Erdos642.DenseMask20261019

universe u

/-- The universal layer supply returned by `ToughLayersV2.exists_tough_layers D0 a_s` at its
constant `Ks`, for vertex and index types in universe `u`. Restated verbatim (with `D := D0`,
`a := a_s`) so that the host step can take it as one hypothesis. -/
def LayerSupply (Ks : ℝ) : Prop :=
  ∀ (V I : Type u) [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
  ∀ (b : ℕ) (hb : 1 ≤ b) (d lam L : ℝ) (S : I → Finset V),
    2 ≤ Fintype.card V → b ≤ Fintype.card V → 0 < d → 0 < lam → lam ≤ 1 →
    CutEscape.Expands G lam →
    (∀ v, d ≤ (G.degree v : ℝ)) → (∀ v, (G.degree v : ℝ) ≤ Constants.D0 * d) →
    Fintype.card I ≤ 2 * Fintype.card V → (∀ i, d ≤ ((S i).card : ℝ)) →
    Real.log (2 * (Fintype.card V : ℝ)) ≤ L →
    Ks * L ≤ (UniformLayers.rate b hb : ℝ) * d →
    Constants.a_s / L ^ 2 ≤ (UniformLayers.rate b hb : ℝ) * lam →
    ∃ omega : V → Fin b,
      (∀ i, ToughLayersV2.LayerGood G ((UniformLayers.rate b hb : ℝ) * d) Constants.D0 S
        (UniformLayers.layer omega i)) ∧
      Pairwise (fun i j => Disjoint (UniformLayers.layer omega i) (UniformLayers.layer omega j)) ∧
      Finset.univ.biUnion (UniformLayers.layer omega) = Finset.univ

/-- The supply of `exists_tough_layers D0 a_s` at universe `u`, with `1000000 ≤ Ks`. -/
theorem exists_layerSupply : ∃ Ks : ℝ, 1000000 ≤ Ks ∧ LayerSupply.{u} Ks :=
  ToughLayersV2.exists_tough_layers.{u, u} Constants.D0 Constants.a_s Constants.one_le_D0
    Constants.a_s_pos

/-- `d + 1 ≤ |W|`: the minimum degree is below the order. -/
theorem minDegree_add_one_le {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (d : ℝ) (hd : d = (H.minDegree : ℝ)) (hN : 0 < Fintype.card W) :
    d + 1 ≤ (Fintype.card W : ℝ) := by
  have : Nonempty W := Fintype.card_pos_iff.mp hN
  let v : W := Classical.arbitrary W
  have h1 := H.minDegree_le_degree v
  have h2 := H.degree_lt_card_verts v
  have h3 : H.minDegree + 1 ≤ Fintype.card W := by omega
  rw [hd]
  exact_mod_cast h3

/-- Synthesis §§3–6 on the host: MaskCore's one fixed pair `Q`, `R`, the tough layers of
`H.induce R`, the token injections, the merger and the payment give a rich cycle of `H`. -/
theorem host_false (Ks : ℝ) (hKs : 0 ≤ Ks) (hlayers : LayerSupply.{u} Ks)
    {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hH : ¬HasRichCycle H) (L : ℝ) (hL1 : 1 ≤ L) (d φ : ℝ) (hd : d = (H.minDegree : ℝ))
    (hN : 0 < Fintype.card W)
    (hlo : ∀ v, d ≤ (H.degree v : ℝ)) (hhi : ∀ v, (H.degree v : ℝ) ≤ 100 * d)
    (hcut : ∀ X : Finset W, (X.card : ℝ) ≤ (Fintype.card W : ℝ) / 2 →
      φ * d * (X.card : ℝ) ≤ crossing H X)
    (hdK : Constants.K Ks * L ^ 2 ≤ d) (hφa : Constants.a / L ≤ φ) (hφ1 : φ ≤ 1)
    (hLW : Real.log (2 * (Fintype.card W : ℝ)) ≤ L) : False := by
  have hL0 : 0 < L := by linarith
  have hd0 : 0 ≤ d := le_trans (by have := Constants.K_pos Ks; positivity) hdK
  -- §3: one fixed pair `Q`, `R = Qᶜ`.
  obtain ⟨Q, R, hR, hQdeg, ⟨-, -, hQ2⟩, hdense, hres, hexp, hWR⟩ :=
    MaskCore.exists_dense_mask H Constants.a Constants.C0 (Constants.K Ks) L φ d
      (1 / (Constants.C0 * L)) hN hlo hhi hcut rfl Constants.a_pos Constants.C0_ge_a
      (Constants.K_ge_C0_sq Ks) (Constants.K_ge_C0 Ks) hdK hφa hφ1 hLW
  have hp0 : 0 < 1 / (Constants.C0 * L) := Constants.p_pos L _ hL0 rfl
  have hQ : ∀ v, ((H.neighborFinset v ∩ Q).card : ℝ) ≤
      2 * (1 / (Constants.C0 * L)) * (H.degree v : ℝ) := fun v => (hQdeg v).2
  -- §5: the number of layers `b = phaseCount |Q|`.
  have hb : 1 ≤ Constants.phaseCount Q.card := Constants.one_le_phaseCount _
  have hQW : Q.card ≤ Fintype.card W := Finset.card_le_univ Q
  have hlogQ : Real.log (Q.card : ℝ) ≤ L :=
    Constants.log_le_of_le Q.card (Fintype.card W) (by omega) hQW L hLW
  have hbL : (Constants.phaseCount Q.card : ℝ) ≤ Constants.Cη * L :=
    Constants.phaseCount_le Q.card (by omega) L hlogQ hL1
  have hW1 : d + 1 ≤ (Fintype.card W : ℝ) := minDegree_add_one_le H d hd hN
  have hbR : Constants.phaseCount Q.card ≤ R.card :=
    Constants.le_card_R Ks L d _ (Fintype.card W) R.card hL1 hdK hW1 hWR hbL
  have h2R : 2 ≤ R.card := Constants.two_le_card_R Ks L d (Fintype.card W) R.card hL1 hdK hW1 hWR
  -- §4: the residual graph `G' = H[R]` on `↥R`, queries indexed by `↥Q`.
  have hG' : ¬HasRichCycle (H.induce (R : Set W)) :=
    Extract.not_hasRichCycle_host (liftHom H R) (liftHom_injective H R) hH
  have h2V : 2 ≤ Fintype.card ↥(R : Set W) := by rw [card_elem_eq]; exact h2R
  have hbV : Constants.phaseCount Q.card ≤ Fintype.card ↥(R : Set W) := by
    rw [card_elem_eq]; exact hbR
  have hRW : Fintype.card ↥(R : Set W) ≤ Fintype.card W := by
    rw [card_elem_eq]; exact Finset.card_le_univ R
  have hLV : Real.log (2 * (Fintype.card ↥(R : Set W) : ℝ)) ≤ L :=
    (Constants.log_two_mul_le _ _ (by omega) hRW).trans hLW
  have hhiV : ∀ v : ↥(R : Set W),
      ((H.induce (R : Set W)).degree v : ℝ) ≤ Constants.D0 * (3 * d / 4) := fun v =>
    (degree_induce_le H R d hhi v).trans (Constants.degree_ratio d hd0)
  obtain ⟨omega, hgood, hdisj, -⟩ :=
    hlayers ↥(R : Set W) ↥(Q : Set W) (H.induce (R : Set W)) hG' (Constants.phaseCount Q.card) hb
      (3 * d / 4) (3 * φ / 1600) L (querySet H Q R) h2V hbV (Constants.d0_pos Ks L d hL1 hdK)
      (Constants.lam_pos L φ hL0 hφa) (Constants.lam_le_one φ hφ1) hexp
      (degree_induce_ge H R d hres) hhiV (card_Q_le_two_card_R Q R hWR) (querySet_card_ge d hres)
      hLV (Constants.layer_scale Ks L d _ hb hKs hL1 hdK hbL)
      (Constants.layer_expansion L φ _ hb hL1 hφa hbL)
  -- §5: every layer is ordinary `η`-tough, hence `Linked` with `γ = η/4` and inside-connected.
  have hlinkR : ∀ i, Linked (H.induce (R : Set W)) (UniformLayers.layer omega i) Constants.γ :=
    fun i => linked_of_ordinaryTough (H.induce (R : Set W)) _ Constants.η_pos Constants.η_le_one
      (hgood i).2.2.2.1
  have hconnR : ∀ i, InsideConnected (H.induce (R : Set W)) (UniformLayers.layer omega i) :=
    fun i => insideConnected_of_ordinaryTough (H.induce (R : Set W)) _ Constants.η_pos
      (hgood i).2.2.2.1
  -- §4: Hall load `800·p·d ≤ rho` with `rho = rate·d₀`, and the query conjunct of each layer.
  have hrho : 0 < (UniformLayers.rate (Constants.phaseCount Q.card) hb : ℝ) * (3 * d / 4) := by
    have hbpos : (0 : ℝ) < (Constants.phaseCount Q.card : ℝ) := by exact_mod_cast hb
    have h0 := Constants.d0_pos Ks L d hL1 hdK
    change 0 < 1 / (Constants.phaseCount Q.card : ℝ) * (3 * d / 4)
    positivity
  have hpd : 800 * (1 / (Constants.C0 * L)) * d ≤
      (UniformLayers.rate (Constants.phaseCount Q.card) hb : ℝ) * (3 * d / 4) :=
    Constants.hall_load L d _ _ hb hL1 hd0 rfl hbL
  obtain ⟨A, -, hQA, hAdisj, hinj, hlink, hconn, -⟩ :=
    layers_package H Q R hR (1 / (Constants.C0 * L)) d
      ((UniformLayers.rate (Constants.phaseCount Q.card) hb : ℝ) * (3 * d / 4)) Constants.γ
      hp0.le hrho hQ hhi hpd (UniformLayers.layer omega)
      (fun i => query_bound_of_layerGood H Q R (H.induce (R : Set W)) _ Constants.D0 _ (hgood i))
      hdisj hlinkR hconnR
  choose f hf using hinj
  -- §6: the merger closes one simple cycle through `Q`; the dense mask pays for it.
  obtain ⟨v, c, hc, hcov⟩ :=
    cycle_through_tokens H Q hQ2 Constants.γ Constants.γ_pos Constants.γ_le_one _ hb
      (Constants.phase_bound Q.card (by omega)) A hAdisj hQA f (fun i => (hf i).1)
      (fun i z => ((hf i).2 z).1) (fun i z => ((hf i).2 z).2) hlink hconn
  exact hH (GraphPayment.rich_of_cycle_covers_dense_mask H c hc Q hcov hdense)

                                                                                         
                                                                                               
                                                   
theorem original_log3_rich_cycle :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      C * (Fintype.card V : ℝ) * Real.log (2 * (Fintype.card V : ℝ)) ^ 3 <
        (G.edgeFinset.card : ℝ) → HasRichCycle G := by
  obtain ⟨Ks, hKs, hlayers⟩ := exists_layerSupply.{u}
  refine ⟨Constants.C Ks, Constants.C_pos Ks, ?_⟩
  intro V _ _ G _ he
  by_contra ha
  -- §2: small orders are excluded by the antecedent, and the host trigger holds.
  have hn3 : 3 ≤ Fintype.card V :=
    Constants.three_le_of_edges Ks (Fintype.card V) G.edgeFinset.card
      SimpleGraph.card_edgeFinset_le_card_choose_two he
  have hL1 : 1 ≤ Real.log (2 * (Fintype.card V : ℝ)) :=
    Constants.one_le_log_two_mul _ (by omega)
  have he' : Extract.hostConstant (Constants.K Ks) * (Fintype.card V : ℝ) *
      Real.log (2 * (Fintype.card V : ℝ)) ^ 3 < (G.edgeFinset.card : ℝ) :=
    Constants.host_trigger Ks _ _ _ (by linarith) he
  obtain ⟨W, _, _, H, _, f, hf, hH, -, -, -, d, φ, hd, hφ, hN, hlo, hhi, hcut, hdK, hφa, hφ1,
      hLW⟩ := Extract.exists_mask_host (Constants.K Ks) (Constants.K_nonneg Ks) G hn3 he' ha
  exact host_false Ks (by linarith) hlayers H hH _ hL1 d φ hd hN hlo hhi hcut hdK hφa hφ1 hLW

end Erdos642.Log3V1_20261024
