import Openmath.Erdos642.Proofs.DenseMask20261019.PrunedHistory
import Openmath.Erdos642.Proofs.DenseMask20261019.FixedObstruction
import Openmath.Erdos642.Proofs.DenseMask20261019.AdaptiveObstruction

/-! Actual pruned bad histories in the initial-mask/fresh-thinning experiment. -/
noncomputable section
namespace Erdos642.DenseMask20261019.GlobalObstruction
open Finset SimpleGraph MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.SourcePools
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open NestedSampling FixedObstruction
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual sampled degree bounds and literal bad-set/boundary witnesses. -/
def BadHistory (G : SimpleGraph V) [DecidableRel G.Adj]
    (rho D k b : ℝ) (A : Finset V) : Prop :=
  (∀ v ∈ A, rho/2 ≤ (restrictedDegree G A v : ℝ)) ∧
  (∀ v, (restrictedDegree G A v : ℝ) ≤ 2*D*rho) ∧
  ∃ U B : Finset V, U ⊆ A ∧ B ⊆ A ∧ Disjoint U B ∧ (U.card : ℝ) = k ∧
    (∀ x ∈ U, ∀ y ∈ A, G.Adj x y → y ∈ U ∨ y ∈ B) ∧
    (B.card : ℝ) ≤ b

def badHistories (G : SimpleGraph V) [DecidableRel G.Adj]
    (rho D k b : ℝ) : Finset (V → Bool) :=
  Finset.univ.filter (fun a => BadHistory G rho D k b (sampleVertices a))

/-- The actual degree-good small-boundary event, with a required upper
bound K on the original bad-set size. No particular size is selected yet. -/
def boundedBadSamples (G : SimpleGraph V) [DecidableRel G.Adj]
    (rho D s K : ℝ) : Set (V → Bool) :=
  {a | (∀ v ∈ sampleVertices a, rho/2 ≤ (restrictedDegree G (sampleVertices a) v : ℝ)) ∧
    (∀ v, (restrictedDegree G (sampleVertices a) v : ℝ) ≤ 2*D*rho) ∧
    ∃ U B : Finset V, U ⊆ sampleVertices a ∧ B ⊆ sampleVertices a ∧
      Disjoint U B ∧ U.Nonempty ∧ (U.card : ℝ) ≤ K ∧
      (∀ x ∈ U, ∀ y ∈ sampleVertices a, G.Adj x y → y ∈ U ∨ y ∈ B) ∧
      (B.card : ℝ) ≤ s*(U.card : ℝ)}

theorem bad_history_size (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (rho D k b : ℝ) (h : BadHistory G rho D k b A)
    (hk : 0 < k) (hb : b ≤ k) : rho/4 ≤ k := by
  obtain ⟨hlo, _, U, B, hUA, _, _, hU, hboundary, hB⟩ := h
  have hu : U.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (show (0 : ℝ) < U.card by linarith))
  obtain ⟨x, hx⟩ := hu
  have hsub : A.filter (G.Adj x) ⊆ U ∪ B := by
    intro y hy
    rcases hboundary x hx y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2 with hU | hB
    · exact Finset.mem_union_left _ hU
    · exact Finset.mem_union_right _ hB
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le U B)
  have hcR : (restrictedDegree G A x : ℝ) ≤ (U.card : ℝ)+(B.card : ℝ) := by
    exact_mod_cast hc
  have hd := hlo x (hUA hx)
  linarith

/-- Actual finite-size pigeonhole, retaining the upper cutoff K.
The selected size is a natural cardinality of a literal bad-set witness. -/
theorem exists_bad_history_mass (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (rho D s K m : ℝ) (hn : 1 ≤ Fintype.card V) (hm : 0 < m)
    (hmass : m ≤ (sampleMeasure V p).real (boundedBadSamples G rho D s K)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Fintype.card V ∧ (k : ℝ) ≤ K ∧
      m/(Fintype.card V : ℝ) ≤
        (sampleMeasure V p).real (badHistories G rho D k (s*k) : Set (V → Bool)) := by
  let μ := sampleMeasure V p
  let T : Fin (Fintype.card V) → Set (V → Bool) := fun i =>
    if (i.val+1 : ℝ) ≤ K then
      (badHistories G rho D (i.val+1) (s*(i.val+1)) : Set (V → Bool)) else ∅
  have hcover : boundedBadSamples G rho D s K ⊆ ⋃ i, T i := by
    intro a ha
    obtain ⟨hlo, hhi, U, B, hUA, hBA, hUB, hUne, hUK, hboundary, hB⟩ := ha
    have hUpos : 0 < U.card := Finset.card_pos.mpr hUne
    have hUn : U.card ≤ Fintype.card V := Finset.card_le_univ U
    let i : Fin (Fintype.card V) := ⟨U.card-1, by omega⟩
    have hi : i.val+1 = U.card := by dsimp [i]; omega
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have hiK : (i.val+1 : ℝ) ≤ K := by exact_mod_cast (show (i.val : ℝ)+1 ≤ K by
      have hh : (i.val : ℝ)+1 = (U.card : ℝ) := by exact_mod_cast hi
      linarith)
    simp only [T, if_pos hiK, Finset.mem_coe, badHistories, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨hlo, hhi, U, B, hUA, hBA, hUB, ?_, hboundary, ?_⟩
    · exact_mod_cast hi.symm
    · have hh : (i.val : ℝ)+1 = (U.card : ℝ) := by exact_mod_cast hi
      simpa only [hh] using hB
  let i₀ : Fin (Fintype.card V) := ⟨0, by omega⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (Fintype.card V)))
    (fun i => μ.real (T i)) ⟨i₀, Finset.mem_univ _⟩
  have hsum : (∑ j, μ.real (T j)) ≤ (Fintype.card V : ℝ)*μ.real (T i) := by
    calc
      _ ≤ ∑ _j : Fin (Fintype.card V), μ.real (T i) :=
        Finset.sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp
  have hall : m ≤ (Fintype.card V : ℝ)*μ.real (T i) :=
    hmass.trans ((measureReal_mono hcover (measure_ne_top _ _)).trans
      ((measureReal_iUnion_fintype_le T).trans hsum))
  have hiK : (i.val+1 : ℝ) ≤ K := by
    by_contra h
    have he : T i = ∅ := by simp [T, h]
    rw [he, measureReal_empty, mul_zero] at hall
    linarith
  refine ⟨i.val+1, by omega, by omega, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_one] using hiK
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hh : m/(Fintype.card V : ℝ) ≤ μ.real (T i) :=
    (div_le_iff₀ hnR).mpr (by nlinarith [hall])
  simpa only [T, if_pos hiK, Nat.cast_add, Nat.cast_one] using hh

/-- The initial mask has rate p; the two fresh masks are independent and fair. -/
def experiment (V : Type*) [Fintype V] (p : unitInterval) :
    Measure ((V → Bool) × ((V → Bool) × (V → Bool))) :=
  (sampleMeasure V p).prod ((sampleMeasure V half).prod (sampleMeasure V half))

def obstructionEvent (G : SimpleGraph V) [DecidableRel G.Adj]
    (C rho D k : ℝ) : Set ((V → Bool) × ((V → Bool) × (V → Bool))) :=
  {x | Obstruction G C rho (2*D*rho) k
    (sampleVertices x.1 ∩ sampleVertices (thin x.2.1 x.2.2))
    (sampleVertices x.1 ∩ sampleVertices x.2.1)}

theorem exponential_boundary_cost (m : ℕ) (c : ℝ) (hmc : (m : ℝ) ≤ c) :
    exp (-c*log 2) ≤ (1/2 : ℝ)^m := by
  calc
    _ ≤ exp (-(m : ℝ)*log 2) := exp_le_exp.mpr (by
      have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
      nlinarith)
    _ = (exp (-log 2))^m := by
      rw [show -(m : ℝ)*log 2 = (m : ℝ)*(-log 2) by ring, exp_nat_mul]
    _ = _ := by rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

                                                               
                                                                          
theorem exists_bad_history_probability_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ (p : unitInterval) (rho D k b : ℝ),
      1 ≤ Fintype.card V → 0 < rho → 1 ≤ D → 0 ≤ b →
      rho/4 ≤ k → 16*D*b ≤ k/10 →
      1000000*log (2*Fintype.card V) ≤ rho →
      (sampleMeasure V p).real (badHistories G rho D k b : Set (V → Bool)) *
          ((1/2)*exp (-(1+16*D)*b*log 2)) ≤
        (experiment V p).real (obstructionEvent G C rho D k) := by
  obtain ⟨C, hC, hfixed⟩ := FixedObstruction.exists_fixed_history_constant
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid p rho D k b hn hrho hD hb hk hsmall hr
  apply AdaptiveObstruction.product_event_lower_bound (sampleMeasure V p)
    ((sampleMeasure V half).prod (sampleMeasure V half))
    (obstructionEvent G C rho D k) (badHistories G rho D k b)
    ((1/2)*exp (-(1+16*D)*b*log 2)) (by positivity)
  intro a ha
  obtain ⟨hlo, hhi, U, B, hUA, hBA, hUB, hU, hboundary, hB⟩ :=
    (Finset.mem_filter.mp ha).2
  obtain ⟨W, hW, hdegree, hclosed, hUlo, hUhi, hWpos, hloss⟩ :=
    PrunedHistory.exists_pruned_history G (sampleVertices a) B U rho D k b
      hBA hUA hUB hboundary hrho hD hk hb hU hB hsmall hlo hhi
  have hWA : W ⊆ sampleVertices a := hW.trans Finset.sdiff_subset
  have hcore : U ∩ W ⊆ W := Finset.inter_subset_right
  have hrW : 1000000*log (2*W.card) ≤ rho := by
    have hc : (W.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ W
    have hw : (1 : ℝ) ≤ W.card := by exact_mod_cast hWpos
    have hl : log (2*(W.card : ℝ)) ≤ log (2*Fintype.card V) :=
      log_le_log (by positivity) (by linarith)
    linarith
  have hsection := hfixed V G havoid (sampleVertices a) W (U ∩ W) rho (2*D*rho) k
    hWA hcore hWpos hdegree hhi hclosed hUlo hUhi hk hrW
  have hcost := exponential_boundary_cost (sampleVertices a \ W).card ((1+16*D)*b) hloss
  have hcost' : (1/2)*exp (-(1+16*D)*b*log 2) ≤
      (1/2 : ℝ)*(1/2 : ℝ)^(sampleVertices a \ W).card := by
    convert mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 1/2) using 1 <;>
      congr 2 <;> ring
  exact hcost'.trans hsection

/-- The explicit polynomial normalization, assuming the stated ACTUAL
bad-history mass. Deriving that mass from expansion failure is separate. -/
theorem exists_normalized_bad_history_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ (p : unitInterval) (rho D k b : ℝ),
      1 ≤ Fintype.card V → 0 < rho → 1 ≤ D → 0 ≤ b →
      rho/4 ≤ k → 16*D*b ≤ k/10 →
      1000000*log (2*Fintype.card V) ≤ rho →
      1/(2*(Fintype.card V : ℝ)^5) ≤
        (sampleMeasure V p).real (badHistories G rho D k b : Set (V → Bool)) →
      (1/(4*(Fintype.card V : ℝ)^5))*exp (-(1+16*D)*b*log 2) ≤
        (experiment V p).real (obstructionEvent G C rho D k) := by
  obtain ⟨C, hC, hprob⟩ := exists_bad_history_probability_constant
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid p rho D k b hn hrho hD hb hk hsmall hr hmass
  have hp := hprob V G havoid p rho D k b hn hrho hD hb hk hsmall hr
  have hm := mul_le_mul_of_nonneg_right hmass
    (show 0 ≤ (1/2 : ℝ)*exp (-(1+16*D)*b*log 2) by positivity)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  calc
    _ = (1/(2*(Fintype.card V : ℝ)^5))*((1/2)*exp (-(1+16*D)*b*log 2)) := by
      field_simp
      <;> ring
    _ ≤ _ := hm.trans hp

/-- Selects the actual bad-set size, derives its minimum size from original
degrees, prunes, pays deletion, and integrates the fresh-mask obstruction.
Only the stated initial degree-good bad-event mass remains an input. -/
theorem exists_selected_obstruction_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ (p : unitInterval) (rho D s K : ℝ),
      1 ≤ Fintype.card V → 0 < rho → 1 ≤ D → 0 ≤ s →
      16*D*s ≤ 1/10 → 1000000*log (2*Fintype.card V) ≤ rho →
      1/(2*(Fintype.card V : ℝ)^4) ≤
        (sampleMeasure V p).real (boundedBadSamples G rho D s K) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ Fintype.card V ∧ (k : ℝ) ≤ K ∧ rho/4 ≤ k ∧
        (1/(4*(Fintype.card V : ℝ)^5))*exp (-(1+16*D)*(s*k)*log 2) ≤
          (experiment V p).real (obstructionEvent G C rho D k) := by
  obtain ⟨C, hC, hprob⟩ := exists_normalized_bad_history_constant
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid p rho D s K hn hrho hD hs hsmall hr hmass
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  obtain ⟨k, hk1, hkn, hkK, hkMass⟩ := exists_bad_history_mass G p rho D s K
    (1/(2*(Fintype.card V : ℝ)^4)) hn (by positivity) hmass
  have hm : 1/(2*(Fintype.card V : ℝ)^5) ≤
      (sampleMeasure V p).real (badHistories G rho D k (s*k) : Set (V → Bool)) := by
    convert hkMass using 1 <;> field_simp <;> ring
  have hknR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs1 : s ≤ 1 := by
    have hh := mul_nonneg (show 0 ≤ D-1 by linarith) hs
    nlinarith
  have hne : (badHistories G rho D k (s*k)).Nonempty := by
    by_contra he
    have he' : badHistories G rho D k (s*k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [he', Finset.coe_empty, measureReal_empty] at hm
    have hp : (0 : ℝ) < 1/(2*(Fintype.card V : ℝ)^5) := by positivity
    linarith
  obtain ⟨a, ha⟩ := hne
  have hkR : rho/4 ≤ k := bad_history_size G (sampleVertices a) rho D k (s*k)
    (Finset.mem_filter.mp ha).2 hknR (by nlinarith)
  have hsmallk : 16*D*(s*(k : ℝ)) ≤ (k : ℝ)/10 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hknR.le
    nlinarith
  exact ⟨k, hk1, hkn, hkK, hkR, hprob V G havoid p rho D k (s*k)
    hn hrho hD (by positivity) hkR hsmallk hr hm⟩

end Erdos642.DenseMask20261019.GlobalObstruction
