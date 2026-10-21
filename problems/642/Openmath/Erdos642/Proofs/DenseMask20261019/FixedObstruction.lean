import Openmath.Erdos642.Proofs.DenseMask20261019.AvoidanceOrder
import Openmath.Erdos642.Proofs.DenseMask20261019.ThinningConcentration

/-! A fixed surviving history produces an actual original-graph obstruction. -/
noncomputable section
namespace Erdos642.DenseMask20261019.FixedObstruction
open SimpleGraph Finset MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.SourcePools
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open NestedSampling ComponentObstruction AvoidanceOrder
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def lift (W : Finset V) (S : Finset W) : Finset V := S.image Subtype.val

@[simp] theorem card_lift (W : Finset V) (S : Finset W) :
    (lift W S).card = S.card := Finset.card_image_of_injective _ Subtype.val_injective

@[simp] theorem lift_univ (W : Finset V) : lift W Finset.univ = W := by
  ext v
  simp [lift]

theorem lift_inter (W : Finset V) (S T : Finset W) :
    lift W (S ∩ T) = lift W S ∩ lift W T :=
  Finset.image_inter _ _ Subtype.val_injective

theorem lift_sample (W : Finset V) (s : V → Bool) :
    lift W (sampleVertices (fun w : W => s w.val)) = W ∩ sampleVertices s := by
  ext v
  simp [lift, sampleVertices, and_comm]

theorem lift_core (W U : Finset V) (hUW : U ⊆ W) :
    lift W (Finset.univ.filter (fun w : W => w.val ∈ U)) = U := by
  ext v
  simp only [lift, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact hw
  · intro hv; exact ⟨⟨v, hUW hv⟩, hv, rfl⟩

theorem degree_lift (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (S : Finset W) (v : W) :
    restrictedDegree G (lift W S) v.val =
      restrictedDegree (G.comap (Subtype.val : W → V)) S v := by
  unfold restrictedDegree lift
  rw [Finset.filter_image, Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

theorem degree_survivor (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (v : W) :
    restrictedDegree G W v.val = (G.comap (Subtype.val : W → V)).degree v := by
  calc
    _ = restrictedDegree (G.comap (Subtype.val : W → V)) Finset.univ v := by
      simpa only [lift_univ] using degree_lift G W Finset.univ v
    _ = _ := by
      unfold restrictedDegree
      congr 1
      ext w
      simp

theorem boundary_mask (A W : Finset V) (hWA : W ⊆ A) (s : V → Bool)
    (hd : Disjoint (A \ W) (sampleVertices s)) :
    A ∩ sampleVertices s = lift W (sampleVertices (fun w : W => s w.val)) := by
  rw [lift_sample]
  ext v
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨?_, hs⟩
    by_contra hw
    exact (Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨ha, hw⟩)) hs
  · rintro ⟨hw, hs⟩; exact ⟨hWA hw, hs⟩

theorem componentUnion_idem (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q U : Finset V) :
    componentUnion G Q (componentUnion G Q U) = componentUnion G Q U := by
  ext v
  simp only [mem_componentUnion]
  constructor
  · rintro ⟨hv, w, hw, hreach⟩
    obtain ⟨hwQ, z, hz, hzw⟩ := (mem_componentUnion G Q U w).mp
      (Finset.mem_inter.mp hw).2
    exact ⟨hv, z, hz, hzw.trans hreach⟩
  · rintro ⟨hv, z, hz, hzv⟩
    exact ⟨hv, v, Finset.mem_inter.mpr ⟨hv,
      (mem_componentUnion G Q U v).mpr ⟨hv, z, hz, hzv⟩⟩, Reachable.rfl⟩

/-- This event only refers to the two actual original masks Q and M.
The chosen surviving history and closed core are absent from its definition. -/
def Obstruction (G : SimpleGraph V) [DecidableRel G.Adj]
    (C rho beta k : ℝ) (Q M : Finset V) : Prop :=
  Q ⊆ M ∧
  (∀ v ∈ Q, rho/64 ≤ (restrictedDegree G Q v : ℝ)) ∧
  (∀ v, (restrictedDegree G Q v : ℝ) ≤ beta) ∧
  (∀ c : (mask G Q).ConnectedComponent, (∃ v ∈ Q, v ∈ c.supp) →
    orderLower C (rho/64) ≤ ((componentVertices G Q c).card : ℝ)) ∧
  ∃ B : Finset V, B ⊆ Q ∧ componentUnion G Q B = B ∧
    k/5 ≤ (B.card : ℝ) ∧
    ((componentUnion G M B).card : ℝ) ≤ 9*k/17 ∧
    componentUnion G M B ⊆ closedNeighborhood G B

/-- A positive absolute constant works for every fixed surviving history.
The probability is over two fresh whole masks, not a conditional iid assertion. -/
theorem exists_fixed_history_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ (A W U : Finset V) (rho beta k : ℝ),
      W ⊆ A → U ⊆ W → 1 ≤ W.card →
      (∀ v ∈ W, rho/8 ≤ (restrictedDegree G W v : ℝ)) →
      (∀ v, (restrictedDegree G A v : ℝ) ≤ beta) →
      (∀ x ∈ U, ∀ y ∈ W, G.Adj x y → y ∈ U) →
      9*k/10 ≤ (U.card : ℝ) → (U.card : ℝ) ≤ k → rho/4 ≤ k →
      1000000*log (2*W.card) ≤ rho →
      (1/2 : ℝ)*(1/2 : ℝ)^(A \ W).card ≤
        ((sampleMeasure V half).prod (sampleMeasure V half)).real
          {x | Obstruction G C rho beta k
            (A ∩ sampleVertices (thin x.1 x.2)) (A ∩ sampleVertices x.1)} := by
  obtain ⟨C, hC, horder⟩ := exists_component_order_constant
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid A W U rho beta k hWA hUW hn hdegree hcap
    hclosed hUlo hUhi hk hr
  let H := G.comap (Subtype.val : W → V)
  let U' : Finset W := Finset.univ.filter (fun w => w.val ∈ U)
  have hUc : U'.card = U.card := by
    rw [← card_lift W U', lift_core W U hUW]
  have hn' : 1 ≤ Fintype.card W := by simpa using hn
  have hdegree' : ∀ v : W, rho/8 ≤ (H.degree v : ℝ) := by
    intro v
    rw [← degree_survivor G W v]
    exact hdegree v.val v.property
  let E : Set ((W → Bool) × (W → Bool)) :=
    {x | k/5 ≤ ((U' ∩ sampleVertices (thin x.1 x.2)).card : ℝ) ∧
      ((U' ∩ sampleVertices x.1).card : ℝ) ≤ 9*k/17 ∧
      ∀ v, rho/64 ≤ ((H.neighborFinset v ∩ sampleVertices (thin x.1 x.2)).card : ℝ)}
  have hgood : 1/2 ≤ ((sampleMeasure W half).prod (sampleMeasure W half)).real E := by
    apply ThinningConcentration.good_two_mask_probability H U' rho k hn'
    · simpa only [hUc] using hUlo
    · simpa only [hUc] using hUhi
    · exact hdegree'
    · exact hk
    · simpa using hr
  have hr0 : 0 < rho := by
    have hnR : (1 : ℝ) ≤ W.card := by exact_mod_cast hn
    have hl : 0 < log (2*(W.card : ℝ)) := log_pos (by linarith)
    linarith
  let μ := (sampleMeasure V half).prod (sampleMeasure V half)
  let F : Set ((V → Bool) × (V → Bool)) :=
    {x | Disjoint (A \ W) (sampleVertices x.1) ∧ ThinningEvent.restrictedPair W x ∈ E}
  have hfactor : μ.real F = (1/2 : ℝ)^(A \ W).card *
      ((sampleMeasure W half).prod (sampleMeasure W half)).real E := by
    convert
      ThinningEvent.fixed_boundary_event (A \ W) W Finset.sdiff_disjoint half half E
        using 1 <;> norm_num [μ, F, half]
  have hsub : F ⊆ {x | Obstruction G C rho beta k
      (A ∩ sampleVertices (thin x.1 x.2)) (A ∩ sampleVertices x.1)} := by
    intro x hx
    obtain ⟨hd, hx⟩ := hx
    change k/5 ≤ ((U' ∩ sampleVertices (thin
        (fun w : W => x.1 w.val) (fun w : W => x.2 w.val))).card : ℝ) ∧
      ((U' ∩ sampleVertices (fun w : W => x.1 w.val)).card : ℝ) ≤ 9*k/17 ∧
      ∀ v, rho/64 ≤ ((H.neighborFinset v ∩ sampleVertices (thin
        (fun w : W => x.1 w.val) (fun w : W => x.2 w.val))).card : ℝ) at hx
    let Q := A ∩ sampleVertices (thin x.1 x.2)
    let M := A ∩ sampleVertices x.1
    have hthin : sampleVertices (thin x.1 x.2) ⊆ sampleVertices x.1 := by
      intro v hv
      have hh : x.1 v = true ∧ x.2 v = true := by
        simpa [sampleVertices, thin] using hv
      simpa [sampleVertices] using hh.1
    have hdQ := Finset.disjoint_of_subset_right hthin hd
    have hQ : Q = lift W (sampleVertices (fun w : W => thin x.1 x.2 w.val)) :=
      boundary_mask A W hWA _ hdQ
    have hM : M = lift W (sampleVertices (fun w : W => x.1 w.val)) :=
      boundary_mask A W hWA _ hd
    have hQM : Q ⊆ M := Finset.inter_subset_inter_left hthin
    have hMW : M ⊆ W := by rw [hM, lift_sample]; exact Finset.inter_subset_left
    have hQW := hQM.trans hMW
    have hcountsQ : k/5 ≤ ((Q ∩ U).card : ℝ) := by
      rw [hQ, ← lift_core W U hUW, ← lift_inter, card_lift, Finset.inter_comm]
      exact hx.1
    have hcountsM : ((M ∩ U).card : ℝ) ≤ 9*k/17 := by
      rw [hM, ← lift_core W U hUW, ← lift_inter, card_lift, Finset.inter_comm]
      exact hx.2.1
    have hdW : ∀ v ∈ W, rho/64 ≤ (restrictedDegree G Q v : ℝ) := by
      intro v hv
      rw [hQ, degree_lift G W _ ⟨v, hv⟩]
      have he : restrictedDegree H (sampleVertices (fun w : W => thin x.1 x.2 w.val)) ⟨v,hv⟩ =
          (H.neighborFinset ⟨v,hv⟩ ∩ sampleVertices (thin
            (fun w : W => x.1 w.val) (fun w : W => x.2 w.val))).card := by
        unfold restrictedDegree
        congr 1
        ext w
        simp [Finset.mem_inter, and_comm, thin, sampleVertices]
      rw [he]
      exact hx.2.2 ⟨v,hv⟩
    have hneighbor : ∀ v ∈ M, ∃ w ∈ Q, G.Adj v w := by
      intro v hv
      have hp : 0 < (Q.filter (G.Adj v)).card := by
        have hdv := hdW v (hMW hv)
        unfold restrictedDegree at hdv
        exact_mod_cast (show (0 : ℝ) < (Q.filter (G.Adj v)).card by linarith)
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hp
      exact ⟨w, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
    change Obstruction G C rho beta k Q M
    refine ⟨hQM, (fun v hv => hdW v (hQW hv)), ?_, ?_,
      componentUnion G Q U, ?_, componentUnion_idem G Q U, ?_, ?_, ?_⟩
    · intro v
      exact (show (restrictedDegree G Q v : ℝ) ≤ restrictedDegree G A v from by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_left)).trans (hcap v)
    · exact horder V G havoid Q (rho/64) (by positivity) (fun v hv => hdW v (hQW hv))
    · intro v hv; exact ((mem_componentUnion G Q U v).mp hv).1
    · simpa only [componentUnion_eq_inter G Q U W hQW hclosed] using hcountsQ
    · simpa only [nested_componentUnion_eq G Q M U W hQM hMW hclosed hneighbor] using hcountsM
    · exact nested_componentUnion_subset_neighborhood G Q M U W hQM hMW hclosed hneighbor
  calc
    _ = (1/2 : ℝ)^(A \ W).card * (1/2) := by ring
    _ ≤ μ.real F := by rw [hfactor]; exact mul_le_mul_of_nonneg_left hgood (by positivity)
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

end Erdos642.DenseMask20261019.FixedObstruction
