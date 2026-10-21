import Openmath.Attempt6.Statement
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.RegularizationAssembly

/-!
Actual extraction from eligible active #642 code, with original-edge embedding.
The degree ratio is tightened from the generic cut wrapper to twelve.
The robust certificate keeps the original ambient logarithm. It does not assert
the order-normalized CJMM predicate for a potentially much smaller core.
No routing, additive near-regularization, sampler or density-to-cycle theorem
is supplied by this module.
-/
namespace Erdos585.Attempt6.RobustCore

open SimpleGraph
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open CutExtraction GraphExpansionConductance

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

attribute [-instance] FinsetCoe.fintype in
theorem exists_original_cut_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hD : 0 < graphAverage G) :
    ∃ S : Finset V, S.Nonempty ∧ ∃ J : SimpleGraph (S : Set V),
      ∃ _ : DecidableRel J.Adj, ∃ W : Finset (S : Set V), W.Nonempty ∧
      let H := J.induce (W : Set (S : Set V))
      ∃ f : H →g G, Function.Injective f ∧
        Fintype.card (W : Set (S : Set V)) ≤ Fintype.card V ∧
        H.IsBipartite ∧ H.Connected ∧ 0 < graphAverage H ∧
        graphAverage G / (400 * Real.log (Fintype.card V : ℝ)) ≤
          (H.minDegree : ℝ) ∧
        H.maxDegree ≤ 12 * H.minDegree ∧ H.maxDegree ≤ 18 * H.minDegree ∧
        (∀ A : Finset (W : Set (S : Set V)),
          (A.card : ℝ) ≤ (Fintype.card (W : Set (S : Set V)) : ℝ) / 2 →
          (lossParameter (Fintype.card V) / 3) * graphAverage H *
            (A.card : ℝ) ≤ crossing H A) := by
  classical
  obtain ⟨S, hSne, J, instJ, hmap, hJbip, hJpos, hJret, _, hJratio, hJorder⟩ :=
    RegularizationAssembly.exists_regularized_subgraph G hn hD
  let : DecidableRel J.Adj := instJ
  let : Nonempty (S : Set V) := hSne.to_subtype
  obtain ⟨xmin, hxmin⟩ := J.exists_minimal_degree_vertex
  have hratio3 : J.maxDegree ≤ 3 * J.minDegree := by
    apply J.maxDegree_le_of_forall_degree_le
    intro x
    rw [hxmin]
    exact hJratio x xmin
  obtain ⟨W, hWne, hWorder, hHpos, _, hHmin, _, _, hHbip, hHconn, hHexpand, _⟩ :=
    CutExtraction.exists_induced_cut_expander J (Fintype.card V) hn hJorder hJpos
      hJbip (by omega)
  let : Nonempty (W : Set (S : Set V)) := hWne.to_subtype
  let H := J.induce (W : Set (S : Set V))
  let f : H →g G := ⟨fun x => x.val.val, fun h => hmap _ _ h⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have hmax : H.maxDegree ≤ J.maxDegree := by
    apply H.maxDegree_le_of_forall_degree_le
    intro x
    rw [← mask_degree_eq_induce J W x]
    exact (mask_degree_le J W x.val).trans (J.degree_le_maxDegree x.val)
  have hminJ : (J.minDegree : ℝ) ≤ graphAverage J := average_degree_ge_min J
  have hratio12 : H.maxDegree ≤ 12 * H.minDegree := by
    have hmaxR : (H.maxDegree : ℝ) ≤ J.maxDegree := by exact_mod_cast hmax
    have hratioR : (J.maxDegree : ℝ) ≤ 3 * (J.minDegree : ℝ) := by exact_mod_cast hratio3
    have hh : (H.maxDegree : ℝ) ≤ 12 * (H.minDegree : ℝ) := by linarith
    exact_mod_cast hh
  have hmin : graphAverage G / (400 * Real.log (Fintype.card V : ℝ)) ≤
      (H.minDegree : ℝ) := by
    calc
      _ = (graphAverage G / (100 * Real.log (Fintype.card V : ℝ))) / 4 := by ring
      _ ≤ graphAverage J / 4 := div_le_div_of_nonneg_right hJret (by norm_num)
      _ ≤ _ := hHmin
  exact ⟨S, hSne, J, instJ, W, hWne, f, hf, hWorder.trans hJorder,
    hHbip, hHconn, hHpos, hmin, hratio12,
      (show H.maxDegree ≤ 18 * H.minDegree from by omega), hHexpand⟩

noncomputable def externalNeighbors (G : SimpleGraph V) (U : Finset V) : Finset V := by
  classical
  exact Uᶜ.filter (fun v => ∃ u ∈ U, G.Adj u v)

/-- Finite form of CJMM Definition 3.1. Neighbors are outside U. -/
noncomputable def RobustExpander (G : SimpleGraph V) (epsilon s : ℝ) : Prop := by
  classical
  exact ∀ U : Finset V, 1 ≤ U.card →
    (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3 →
    ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset →
      (F.card : ℝ) ≤ s * U.card →
      epsilon * U.card / (logTwo (Fintype.card V : ℝ)) ^ 2 ≤
        ((externalNeighbors (G.deleteEdges F) U).card : ℝ)

omit [Fintype V] in
theorem count_le_split (G K : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel K.Adj] (A B : Finset V) :
    IncidenceCounts.count G A B ≤ IncidenceCounts.count K A B +
      IncidenceCounts.count (G \ K) A B := by
  classical
  unfold IncidenceCounts.count
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  have hsub : B.filter (G.Adj a) ⊆
      B.filter (K.Adj a) ∪ B.filter ((G \ K).Adj a) := by
    intro b hb
    obtain ⟨hbB, hab⟩ := Finset.mem_filter.mp hb
    by_cases hk : K.Adj a b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbB, hk⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbB, hab, hk⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem count_le_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : IncidenceCounts.count G A B ≤ 2 * G.edgeFinset.card := by
  calc
    _ ≤ ∑ a ∈ A, G.degree a := IncidenceCounts.count_le_sum_degree G A B
    _ ≤ ∑ a : V, G.degree a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      intro a ha hnot
      exact Nat.zero_le _
    _ = _ := G.sum_degrees_eq_twice_card_edges

theorem count_le_external_degree (G K : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel K.Adj] (hKG : K ≤ G) (U : Finset V) :
    IncidenceCounts.count K U Uᶜ ≤ (externalNeighbors K U).card * G.maxDegree := by
  classical
  have heq : IncidenceCounts.count K U Uᶜ =
      IncidenceCounts.count K U (externalNeighbors K U) := by
    unfold IncidenceCounts.count
    apply Finset.sum_congr rfl
    intro u hu
    congr 1
    ext v
    simp only [Finset.mem_filter, externalNeighbors]
    constructor
    · intro hv
      exact ⟨⟨hv.1, u, hu, hv.2⟩, hv.2⟩
    · intro hv
      exact ⟨hv.1.1, hv.2⟩
  rw [heq]
  apply IncidenceCounts.count_le_card_mul
  intro v hv
  exact (K.degree_le_of_le hKG).trans (G.degree_le_maxDegree v)

theorem crossing_two_thirds (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℝ) (ha : 0 ≤ a)
    (hcut : ∀ A : Finset V,
      (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      a * (A.card : ℝ) ≤ crossing G A)
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    (a / 2) * (U.card : ℝ) ≤ crossing G U := by
  have hu0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  by_cases hh : (U.card : ℝ) ≤ (Fintype.card V : ℝ) / 2
  · have hc := hcut U hh
    nlinarith [mul_nonneg ha hu0]
  · have hpart : (U.card : ℝ) + Uᶜ.card = Fintype.card V := by
      exact_mod_cast (show U.card + Uᶜ.card = Fintype.card V by simp)
    have hc := hcut Uᶜ (by linarith)
    have heq : crossing G Uᶜ = crossing G U := by
      rw [crossing_eq_cut, crossing_eq_cut, cut_compl]
    rw [heq] at hc
    have hcomp : (U.card : ℝ) / 2 ≤ Uᶜ.card := by linarith
    have hm := mul_le_mul_of_nonneg_left hcomp ha
    nlinarith

theorem crossing_after_deletion (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (F : Finset (Sym2 V)) :
    crossing G U ≤
      ((externalNeighbors (G.deleteEdges F) U).card : ℝ) * G.maxDegree +
        2 * (F.card : ℝ) := by
  classical
  let K := G.deleteEdges F
  have hKG : K ≤ G := by intro a b h; exact h.1
  have hsplit := count_le_split G K U Uᶜ
  have hremain := count_le_external_degree G K hKG U
  have hremoved := count_le_twice_edges (G \ K) U Uᶜ
  have hremedges : (G \ K).edgeFinset ⊆ F := by
    intro e he
    have heG : e ∈ G.edgeFinset :=
      (SimpleGraph.edgeFinset_mono sdiff_le) he
    by_contra hf
    have heK : e ∈ K.edgeFinset := by
      change e ∈ (G.deleteEdges F).edgeFinset
      rw [SimpleGraph.edgeFinset_deleteEdges]
      exact Finset.mem_sdiff.mpr ⟨heG, hf⟩
    have hnot : e ∉ K.edgeFinset := by
      have hm : e ∈ G.edgeFinset ∧ e ∉ K.edgeFinset := by
        simpa only [SimpleGraph.edgeFinset_sdiff, Finset.mem_sdiff] using he
      exact hm.2
    exact hnot heK
  have hcard := Finset.card_le_card hremedges
  simp only [SimpleGraph.edgeFinset_card, Fintype.card_eq_nat_card] at hremoved hcard
  have hbound : IncidenceCounts.count G U Uᶜ ≤
      (externalNeighbors K U).card * G.maxDegree + 2 * F.card :=
    hsplit.trans (Nat.add_le_add hremain (hremoved.trans (Nat.mul_le_mul_left 2 hcard)))
  rw [CutExtraction.crossing_eq_incidence]
  exact_mod_cast hbound

noncomputable def RobustExpanderAt (G : SimpleGraph V) (L epsilon s : ℝ) : Prop := by
  classical
  exact ∀ U : Finset V, 1 ≤ U.card →
    (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3 →
    ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset →
      (F.card : ℝ) ≤ s * U.card →
      epsilon * U.card / L ^ 2 ≤
        ((externalNeighbors (G.deleteEdges F) U).card : ℝ)

theorem robust_arithmetic {d L u b : ℝ} (hd : 0 < d) (hL : 32 ≤ L)
    (hu : 0 ≤ u) (_hb : 0 ≤ b)
    (h : d * u / (12 * L) ≤ 18 * d * b + 2 * (d / L ^ 2 * u)) :
    (1 / 32 : ℝ) * u / L ^ 2 ≤ b := by
  have hLp : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLp
  have hs := mul_le_mul_of_nonneg_right h (sq_nonneg L)
  have heq1 : d * u / (12 * L) * L ^ 2 = d * u * L / 12 := by
    field_simp
  have heq2 : (18 * d * b + 2 * (d / L ^ 2 * u)) * L ^ 2 =
      18 * d * b * L ^ 2 + 2 * d * u := by
    field_simp
  rw [heq1, heq2] at hs
  have hlower : (8 / 3 : ℝ) * (d * u) ≤ d * u * L / 12 := by
    nlinarith [mul_nonneg (mul_nonneg hd.le hu) (sub_nonneg.mpr hL)]
  have hx : d * u ≤ d * (27 * (b * L ^ 2)) := by nlinarith
  have hu27 : u ≤ 27 * (b * L ^ 2) := by
    by_contra hh
    have hp : 0 < d * (u - 27 * (b * L ^ 2)) := mul_pos hd (by linarith)
    nlinarith
  apply (div_le_iff₀ (sq_pos_of_pos hLp)).mpr
  nlinarith [mul_nonneg _hb (sq_nonneg L)]

/-- An ambient-log cut certificate pays arbitrary original edge deletions at
that same logarithmic scale. This does not identify ambient and core orders. -/
theorem robust_at_of_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (d L : ℝ) (hd : 0 < d) (hL : 32 ≤ L)
    (hmax : (G.maxDegree : ℝ) ≤ 18 * d)
    (hcut : ∀ A : Finset V,
      (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      (d / (6 * L)) * (A.card : ℝ) ≤ crossing G A) :
    RobustExpanderAt G L (1 / 32) (d / L ^ 2) := by
  classical
  intro U hUnonempty hU F hFG hF
  have hLp : 0 < L := by linarith
  have hc := crossing_two_thirds G (d / (6 * L)) (by positivity) hcut U hU
  have hu : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ (externalNeighbors (G.deleteEdges F) U).card := Nat.cast_nonneg _
  have he : crossing G U ≤
      18 * d * (externalNeighbors (G.deleteEdges F) U).card +
        2 * (d / L ^ 2 * U.card) := by
    have he0 := crossing_after_deletion G U F
    have hm := mul_le_mul_of_nonneg_left hmax hb
    nlinarith
  apply robust_arithmetic hd hL hu hb
  have hleft : d * (U.card : ℝ) / (12 * L) =
      (d / (6 * L) / 2) * (U.card : ℝ) := by ring
  rw [hleft]
  exact hc.trans he

theorem lossParameter_logTwo (n : ℕ) (hn : 2 ≤ n) :
    lossParameter n / 3 = 1 / (6 * logTwo (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold lossParameter logTwo
  field_simp
  norm_num

attribute [-instance] FinsetCoe.fintype in
/-- Density supplies an actual original core with robust expansion at the
original order logarithm. The core order may be smaller, and is not substituted
into this logarithm. The entire downstream argument must preserve this scale. -/
theorem exists_original_robust_core_at_ambient_log (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) (hD : 0 < graphAverage G)
    (hL : 32 ≤ logTwo (Fintype.card V : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧ ∃ J : SimpleGraph (S : Set V),
      ∃ _ : DecidableRel J.Adj, ∃ W : Finset (S : Set V), W.Nonempty ∧
      let H := J.induce (W : Set (S : Set V))
      ∃ f : H →g G, Function.Injective f ∧
        Fintype.card (W : Set (S : Set V)) ≤ Fintype.card V ∧
        H.IsBipartite ∧ H.Connected ∧ 0 < graphAverage H ∧
        graphAverage G / (400 * logTwo (Fintype.card V : ℝ)) ≤
          graphAverage H ∧
        H.maxDegree ≤ 18 * H.minDegree ∧
        RobustExpanderAt H (logTwo (Fintype.card V : ℝ)) (1 / 32)
          (graphAverage H / (logTwo (Fintype.card V : ℝ)) ^ 2) := by
  classical
  obtain ⟨S, hSne, J, instJ, W, hWne, f, hf, horder, hbip, hconn, hpos,
    hmin, hratio12, hratio18, hcut⟩ := exists_original_cut_core G hn hD
  let : DecidableRel J.Adj := instJ
  let : Nonempty (W : Set (S : Set V)) := hWne.to_subtype
  let H := J.induce (W : Set (S : Set V))
  have hminavg : (H.minDegree : ℝ) ≤ graphAverage H := average_degree_ge_min H
  have hmax : (H.maxDegree : ℝ) ≤ 18 * graphAverage H := by
    have hr : (H.maxDegree : ℝ) ≤ 18 * (H.minDegree : ℝ) := by exact_mod_cast hratio18
    linarith
  have hcutL : ∀ A : Finset (W : Set (S : Set V)),
      (A.card : ℝ) ≤ (Fintype.card (W : Set (S : Set V)) : ℝ) / 2 →
      (graphAverage H / (6 * logTwo (Fintype.card V : ℝ))) *
        (A.card : ℝ) ≤ crossing H A := by
    intro A hA
    have hc := hcut A hA
    rw [lossParameter_logTwo (Fintype.card V) hn] at hc
    convert hc using 1
    ring
  have hrob := robust_at_of_cut H (graphAverage H) (logTwo (Fintype.card V : ℝ))
    hpos hL hmax hcutL
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (Fintype.card V : ℝ) := Real.log_pos (by linarith)
  have hlogtwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlogtwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log (Fintype.card V : ℝ) ≤ logTwo (Fintype.card V : ℝ) := by
    unfold logTwo
    apply (le_div_iff₀ hlogtwoPos).mpr
    nlinarith
  have hret : graphAverage G / (400 * logTwo (Fintype.card V : ℝ)) ≤
      graphAverage H := by
    apply le_trans _ (hmin.trans hminavg)
    exact div_le_div_of_nonneg_left hD.le (by positivity) (by linarith)
  exact ⟨S, hSne, J, instJ, W, hWne, f, hf, horder, hbip, hconn, hpos,
    hret, hratio18, hrob⟩

end Erdos585.Attempt6.RobustCore
