import Openmath.Erdos642.Proofs.DenseMask20261019.DeletionComponents
import Openmath.Erdos642.Proofs.DenseMask20261019.Sampling
import Openmath.Erdos642.Proofs.DenseMask20261019.AvoidanceOrder
import Openmath.Erdos642.Proofs.DenseMask20261019.CutEscape

/-! Ordinary toughness counts every actual surviving induced component. -/
noncomputable section
namespace Erdos642.DenseMask20261019.Toughness
open Finset SimpleGraph Real
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open ComponentObstruction ComponentEntropy DeletionComponents AvoidanceOrder
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem balanced_subfamily {I : Type*} [DecidableEq I]
    (F : Finset I) (w : I → ℝ) (n : ℝ) (hn : 0 < n)
    (hmax : ∀ i ∈ F, w i ≤ n/2) (hs : n/2 < ∑ i ∈ F, w i) :
    ∃ A ⊆ F, n/4 ≤ ∑ i ∈ A, w i ∧ (∑ i ∈ A, w i) ≤ n/2 := by
  classical
  by_cases hlarge : ∃ i ∈ F, n/4 ≤ w i
  · obtain ⟨i, hi, hwi⟩ := hlarge
    exact ⟨{i}, Finset.singleton_subset_iff.mpr hi, by simpa using hwi,
      by simpa using hmax i hi⟩
  · have hsmall : ∀ i ∈ F, w i < n/4 := by
      intro i hi
      exact lt_of_not_ge (fun h => hlarge ⟨i, hi, h⟩)
    let S := F.powerset.filter (fun A => n/4 ≤ ∑ i ∈ A, w i)
    have hS : S.Nonempty := ⟨F, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset_self F, by linarith⟩⟩
    obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image S (fun A => A.card) hS
    obtain ⟨hAF, hlo⟩ := Finset.mem_filter.mp hA
    have hAF' : A ⊆ F := Finset.mem_powerset.mp hAF
    have hAne : A.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [he, Finset.sum_empty] at hlo
      linarith
    obtain ⟨i, hi⟩ := hAne
    have herase : (∑ j ∈ A.erase i, w j) < n/4 := by
      by_contra h
      have hmem : A.erase i ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset i A).trans hAF'), le_of_not_gt h⟩
      have hc := hmin (A.erase i) hmem
      rw [Finset.card_erase_of_mem hi] at hc
      have hp := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    refine ⟨A, hAF', hlo, ?_⟩
    have he := Finset.sum_erase_add A w hi
    have hw := hsmall i (hAF' hi)
    linarith

private theorem union_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (F : Finset (mask G W).ConnectedComponent) :
    unionVertices G W F ⊆ W := by
  intro x hx
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hx
  exact ((mem_componentVertices G W c x).mp hc).1

private theorem union_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (F : Finset (mask G W).ConnectedComponent) :
    closedNeighborhood G (unionVertices G W F) \ unionVertices G W F ⊆ Finset.univ \ W := by
  intro y hy
  obtain ⟨hphi, hyU⟩ := Finset.mem_sdiff.mp hy
  have hadj : ∃ x ∈ unionVertices G W F, G.Adj x y := by
    rcases Finset.mem_union.mp hphi with h | h
    · exact False.elim (hyU h)
    · obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp h
      exact ⟨x, hx, (G.mem_neighborFinset x y).mp hxy⟩
  obtain ⟨x, hx, hxy⟩ := hadj
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hyW =>
    hyU (DeletionComponents.union_closed G W F x hx y hyW hxy)⟩

private theorem expanded_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (F : Finset (mask G W).ConnectedComponent) (eps : ℝ)
    (hexp : CutEscape.Expands G eps)
    (hhalf : ((unionVertices G W F).card : ℝ) ≤ (Fintype.card V : ℝ)/2) :
    eps*((unionVertices G W F).card : ℝ) ≤ ((Finset.univ \ W).card : ℝ) := by
  have hhalfN : 2*(unionVertices G W F).card ≤ Fintype.card V := by
    exact_mod_cast (show 2*((unionVertices G W F).card : ℝ) ≤ Fintype.card V by linarith)
  exact (hexp _ hhalfN).trans (by exact_mod_cast Finset.card_le_card (union_boundary G W F))

/-- Excluding a largest surviving component leaves an original union controlled by expansion. -/
theorem exists_largest_remainder (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (eps : ℝ) (hn : 1 ≤ Fintype.card V) (heps : 0 < eps)
    (hexp : CutEscape.Expands G eps) (hne : (liveComponents G W).Nonempty) :
    ∃ c ∈ liveComponents G W,
      eps*((unionVertices G W ((liveComponents G W).erase c)).card : ℝ) ≤
        4*((Finset.univ \ W).card : ℝ) := by
  classical
  let F := liveComponents G W
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image F
    (fun c => (componentVertices G W c).card) hne
  let T := F.erase c
  let n : ℝ := Fintype.card V
  have hn0 : 0 < n := by
    dsimp [n]
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hsmall : ∀ i ∈ T, ((componentVertices G W i).card : ℝ) ≤ n/2 := by
    intro i hi
    obtain ⟨hic, hiF⟩ := Finset.mem_erase.mp hi
    have hm := hmax i hiF
    have hd := support_disjoint G W i c hic
    have hh := Finset.card_le_univ (componentVertices G W i ∪ componentVertices G W c)
    rw [Finset.card_union_of_disjoint hd] at hh
    have hcN : 2*(componentVertices G W i).card ≤ Fintype.card V := by omega
    have hcR : 2*((componentVertices G W i).card : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast hcN
    linarith
  have hT : ((unionVertices G W T).card : ℝ) =
      ∑ i ∈ T, ((componentVertices G W i).card : ℝ) := by
    exact_mod_cast union_card G W T
  refine ⟨c, hc, ?_⟩
  by_cases hhalf : ((unionVertices G W T).card : ℝ) ≤ n/2
  · have hh := expanded_union G W T eps hexp hhalf
    change eps*((unionVertices G W T).card : ℝ) ≤ _
    nlinarith [show (0 : ℝ) ≤ ((Finset.univ \ W).card : ℝ) by positivity]
  · have htotal : n/2 < ∑ i ∈ T, ((componentVertices G W i).card : ℝ) := by
      rw [← hT]; exact lt_of_not_ge hhalf
    obtain ⟨A, _, hlo, hhi⟩ := balanced_subfamily T
      (fun i => ((componentVertices G W i).card : ℝ)) n hn0 hsmall htotal
    have hA : ((unionVertices G W A).card : ℝ) =
        ∑ i ∈ A, ((componentVertices G W i).card : ℝ) := by
      exact_mod_cast union_card G W A
    have hb := expanded_union G W A eps hexp (by rwa [hA])
    have hlo' : n/4 ≤ ((unionVertices G W A).card : ℝ) := by rwa [hA]
    have hTn : ((unionVertices G W T).card : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast Finset.card_le_univ (unionVertices G W T)
    have he := mul_le_mul_of_nonneg_left hlo' heps.le
    have ht := mul_le_mul_of_nonneg_left hTn heps.le
    change eps*((unionVertices G W T).card : ℝ) ≤ _
    nlinarith

private theorem degree_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    restrictedDegree G Finset.univ v = G.degree v := by
  unfold restrictedDegree
  congr 1
  ext w
  simp

/-- One universal avoidance constant gives ordinary toughness for every original deletion. -/
theorem exists_toughness_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ delta D eps : ℝ, 1 ≤ Fintype.card V → 4 ≤ delta → 1 ≤ D → 0 < eps →
      CutEscape.Expands G eps →
      (∀ v, delta ≤ (G.degree v : ℝ)) → (∀ v, (G.degree v : ℝ) ≤ D*delta) →
      5 ≤ eps*orderLower C (delta/4) → OrdinaryTough G (1/(16*D)) := by
  obtain ⟨C, hC, horder⟩ := AvoidanceOrder.exists_component_order_constant
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid delta D eps hn hdelta hD heps hexp hlo hhi hsize
  classical
  have hd : 0 < delta := by linarith
  have hD0 : 0 < D := by linarith
  apply (ordinaryTough_iff_finset G (1/(16*D))).mpr
  intro Z hk
  let A : Finset V := Finset.univ \ Z
  let k := componentCount G A
  change (1/(16*D))*(k : ℝ) ≤ (Z.card : ℝ)
  by_contra hbad
  have hz : (Z.card : ℝ) < (k : ℝ)/(16*D) := by
    have hh := lt_of_not_ge hbad
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hh
  have hz' := (lt_div_iff₀ (by positivity : 0 < 16*D)).mp hz
  obtain ⟨W, hW, hdegree, hcharge⟩ := Sampling.exists_pruned_sample G Finset.univ Z
    (Finset.subset_univ _) (delta/4) delta (D*delta) (by positivity)
    (fun v _ => by simpa [degree_univ] using hlo v)
    (fun v _ => by simpa [degree_univ] using hhi v)
  let P := A \ W
  let l := componentCount G W
  have hP : (P.card : ℝ) ≤ 4*D*(Z.card : ℝ) := by
    change (delta-2*(delta/4))*(P.card : ℝ) ≤ D*delta*(Z.card : ℝ) at hcharge
    have hh : delta*(P.card : ℝ) ≤ delta*(2*D*(Z.card : ℝ)) := by nlinarith only [hcharge]
    have hcan := (mul_le_mul_iff_right₀ hd).mp hh
    nlinarith [mul_nonneg hD0.le (Nat.cast_nonneg Z.card)]
  have hcount := componentCount_mono_delete G A W hW
  have hcountR : (k : ℝ) ≤ (l : ℝ)+(P.card : ℝ) := by exact_mod_cast hcount
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hl : 3*(k : ℝ)/4 < l := by nlinarith
  have hl2 : 2 ≤ l := by
    by_contra h
    have hln : l ≤ 1 := by omega
    have hlR : (l : ℝ) ≤ 1 := by exact_mod_cast hln
    linarith
  have hne : (liveComponents G W).Nonempty := Finset.card_pos.mp (by
    change 0 < l; omega)
  obtain ⟨c, hc, hboundary⟩ := exists_largest_remainder G W eps hn heps hexp hne
  let T := (liveComponents G W).erase c
  let m := orderLower C (delta/4)
  change 5 ≤ eps*m at hsize
  have hm : 0 < m := by dsimp [m, orderLower]; positivity
  have hcomponent : ∀ i ∈ T, m ≤ ((componentVertices G W i).card : ℝ) := by
    intro i hi
    have hiF := (Finset.mem_erase.mp hi).2
    obtain ⟨v, hvW, _, hvi⟩ := ObstructionCollections.collection_meets G W W
      (Finset.Subset.refl _) hiF
    exact horder V G havoid W (delta/4) (by positivity) hdegree i ⟨v,hvW,hvi⟩
  have hTc : (T.card : ℝ) = (l : ℝ)-1 := by
    have hh := Finset.card_erase_add_one hc
    have hhR : (T.card : ℝ)+1 = l := by exact_mod_cast hh
    linarith
  have hTlo : ((l : ℝ)-1)*m ≤ ((unionVertices G W T).card : ℝ) := by
    calc
      _ = (T.card : ℝ)*m := by rw [hTc]
      _ = ∑ _i ∈ T, m := by simp [mul_comm]
      _ ≤ ∑ i ∈ T, ((componentVertices G W i).card : ℝ) := Finset.sum_le_sum hcomponent
      _ = _ := by exact_mod_cast (union_card G W T).symm
  have hTsize : (k : ℝ)*m/4 ≤ ((unionVertices G W T).card : ℝ) := by
    have hcoef : (k : ℝ)/4 ≤ (l : ℝ)-1 := by linarith
    have hh := mul_le_mul_of_nonneg_right hcoef hm.le
    nlinarith
  have hpartW := Finset.card_sdiff_add_card_eq_card hW
  have hpartZ := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Z)
  have hWU : W ⊆ Finset.univ := Finset.subset_univ _
  have hpartU := Finset.card_sdiff_add_card_eq_card hWU
  have htotalN : (Finset.univ \ W).card = Z.card+P.card := by
    change P.card+W.card = A.card at hpartW
    simp only [Finset.card_univ] at hpartZ hpartU
    change A.card+Z.card = Fintype.card V at hpartZ
    omega
  have htotal : ((Finset.univ \ W).card : ℝ) ≤ (1+4*D)*(Z.card : ℝ) := by
    have hh : ((Finset.univ \ W).card : ℝ) = (Z.card : ℝ)+(P.card : ℝ) := by
      exact_mod_cast htotalN
    nlinarith
  have hlow : 5*(k : ℝ)/4 ≤ eps*((unionVertices G W T).card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hTsize heps.le
    have h2 := mul_le_mul_of_nonneg_right hsize (show 0 ≤ (k : ℝ)/4 by positivity)
    nlinarith
  have hup : eps*((unionVertices G W T).card : ℝ) ≤ 20*D*(Z.card : ℝ) := by
    have hh : 4*(1+4*D)*(Z.card : ℝ) ≤ 20*D*(Z.card : ℝ) := by
      nlinarith [mul_nonneg (show 0 ≤ D-1 by linarith) (Nat.cast_nonneg Z.card)]
    change eps*((unionVertices G W T).card : ℝ) ≤ 4*((Finset.univ \ W).card : ℝ) at hboundary
    linarith
  nlinarith

end Erdos642.DenseMask20261019.Toughness
