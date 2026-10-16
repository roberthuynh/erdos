import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.ActualMaxCut
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.RegularizationPruning
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.NestedMatchingLayers
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MatchingLayerPigeonhole
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MatchingUnion
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.RegularizationParameters

/-! Actual original-graph regularization, including the restricted matching interval. -/
namespace Erdos642.CampaignFe72210bContinuation3.RegularizationAssembly

open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open CutExtraction NestedMatchingLayers

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem antitone_upto (f : ℕ → Finset V) (δ : ℕ)
    (hstep : ∀ i, i < δ → f (i + 1) ⊆ f i) :
    ∀ j, j ≤ δ → ∀ i, i ≤ j → f j ⊆ f i := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    have h : i = 0 := by omega
    subst i
    exact Finset.Subset.refl _
  | succ j ih =>
    intro hj i hi
    by_cases h : i = j + 1
    · subst i; exact Finset.Subset.refl _
    · exact (hstep j (by omega)).trans (ih (by omega) i (by omega))

omit [Fintype V] [DecidableEq V] in
/-- Restrict actual inverse layer bijections to the last right shore in an integer interval. -/
theorem exists_interval_partners (G : SimpleGraph V) (A0 B0 : Finset V) (δ : ℕ)
    (L : Layers G A0 B0 δ) (_hAB : Disjoint A0 B0)
    (q x : ℕ) (hq : 1 ≤ q) (hqx : q + x ≤ δ) :
    let A := L.left q
    let B := L.right (q + x)
    ∃ partner : Fin (x + 1) → ↥(B : Set V) → ↥(A : Set V),
      (∀ i, Function.Injective (partner i)) ∧
      (∀ b, Function.Injective (fun i => (partner i b).val)) ∧
      (∀ i b, G.Adj (partner i b).val b.val) := by
  classical
  let A := L.left q
  let B := L.right (q + x)
  let idx : Fin (x + 1) → ℕ := fun i => q - 1 + i.val
  have hidx : ∀ i, idx i < δ := by intro i; dsimp [idx]; omega
  have hlo : ∀ i, q ≤ idx i + 1 := by intro i; dsimp [idx]; omega
  have hhi : ∀ i, idx i + 1 ≤ q + x := by intro i; dsimp [idx]; omega
  have hleft : ∀ i, L.left (idx i + 1) ⊆ A := by
    intro i
    exact antitone_upto L.left δ L.leftNested (idx i + 1) ((hhi i).trans hqx) q (hlo i)
  have hright : ∀ i, B ⊆ L.right (idx i + 1) := by
    intro i
    exact antitone_upto L.right δ L.rightNested (q + x) hqx (idx i + 1) (hhi i)
  have hbij : ∀ i : Fin (x + 1),
      ∃ e : ↥(L.left (idx i + 1) : Set V) ≃ ↥(L.right (idx i + 1) : Set V),
        (∀ a, G.Adj a.val (e a).val) ∧
        (∀ a, (L.matching (idx i)).Adj a.val (e a).val) :=
    fun i => L.bijection (idx i) (hidx i)
  choose e heG heM using hbij
  let liftB : ∀ i : Fin (x + 1), ↥(B : Set V) → ↥(L.right (idx i + 1) : Set V) :=
    fun i b => ⟨b.val, hright i b.property⟩
  let partner : Fin (x + 1) → ↥(B : Set V) → ↥(A : Set V) :=
    fun i b => ⟨((e i).symm (liftB i b)).val, hleft i ((e i).symm (liftB i b)).property⟩
  have hmatching : ∀ i b, (L.matching (idx i)).Adj (partner i b).val b.val := by
    intro i b
    simpa only [partner, liftB, Equiv.apply_symm_apply] using
      heM i ((e i).symm (liftB i b))
  have horiginal : ∀ i b, G.Adj (partner i b).val b.val := by
    intro i b
    exact L.matchingLe (idx i) (hidx i) (hmatching i b)
  have hinjective : ∀ i, Function.Injective (partner i) := by
    intro i b c h
    have hval := congrArg Subtype.val h
    change ((e i).symm (liftB i b)).val = ((e i).symm (liftB i c)).val at hval
    have hback := (e i).symm.injective (Subtype.ext hval)
    have hval' : (liftB i b).val = (liftB i c).val := congrArg Subtype.val hback
    exact Subtype.ext hval'
  have hseparate : ∀ b, Function.Injective (fun i => (partner i b).val) := by
    intro b i j hij
    change (partner i b).val = (partner j b).val at hij
    have hidxeq : idx i = idx j := by
      by_contra hne
      have hnot := L.separated (idx i) (hidx i) (idx j) (hidx j) hne
        (partner i b).val b.val (hmatching i b)
      have hjedge := hmatching j b
      rw [← hij] at hjedge
      exact hnot hjedge
    apply Fin.ext
    dsimp [idx] at hidxeq
    omega
  exact ⟨partner, hinjective, hseparate, horiginal⟩

omit [Fintype V] [DecidableEq V] in
private theorem edgeCard_of_graph_eq {K L : SimpleGraph V}
    [Fintype K.edgeSet] [Fintype L.edgeSet] (h : K = L) :
    K.edgeFinset.card = L.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact @Fintype.card_congr _ _ _ _
    (Equiv.cast (congrArg (fun H : SimpleGraph V => ↥H.edgeSet) h))

attribute [-instance] FinsetCoe.fintype in
/-- A genuine minimum-degree core of the actual maximum-cut graph. -/
theorem exists_cut_minimum_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hD : 0 < graphAverage G) :
    ∃ S W : Finset V, W.Nonempty ∧
      (∀ a ∈ W, graphAverage G / 4 ≤ ((mask (ActualMaxCut.cutGraph G S) W).degree a : ℝ)) := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨S, _, _, _, he⟩ := ActualMaxCut.exists_cut_half_degree_and_edges G
  let K := ActualMaxCut.cutGraph G S
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hDformula : graphAverage G = 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) := by
    unfold graphAverage
    rw [degreeVolume_eq_twice_edges]
  have hE : inducedEdges K Finset.univ = K.edgeFinset.card := by
    unfold inducedEdges
    exact edgeCard_of_graph_eq (mask_univ K)
  have hpot : 0 ≤ pruningPotential K (graphAverage G / 4) Finset.univ := by
    unfold pruningPotential
    rw [hE, Finset.card_univ, hDformula]
    have heR : (G.edgeFinset.card : ℝ) ≤ 2 * (K.edgeFinset.card : ℝ) := by exact_mod_cast he
    have hcancel : (2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) / 4) *
        (Fintype.card V : ℝ) = (G.edgeFinset.card : ℝ) / 2 := by field_simp; ring
    rw [hcancel]
    linarith
  obtain ⟨W, _, hW, _, hmin, _⟩ :=
    RegularizationPruning.exists_induced_min_degree_nonnegative_potential K
      Finset.univ Finset.univ_nonempty (graphAverage G / 4) (by positivity) hpot
  refine ⟨S, W, hW, ?_⟩
  intro a ha
  rw [mask_degree_eq_induce K W ⟨a, ha⟩]
  exact hmin ⟨a, ha⟩

attribute [-instance] FinsetCoe.fintype in
/-- Actual original-edge regularization, with no hypothetical host or graph supplier. -/
def Regularized (G : SimpleGraph V) (scale : ℝ) : Prop :=
  ∃ W : Finset V, W.Nonempty ∧
    ∃ J : SimpleGraph (W : Set V), ∃ _ : DecidableRel J.Adj,
      (∀ x y : (W : Set V), J.Adj x y → G.Adj x.val y.val) ∧
      J.IsBipartite ∧ 0 < graphAverage J ∧ scale ≤ graphAverage J ∧
      (∀ x : (W : Set V), scale ≤ (J.degree x : ℝ)) ∧
      (∀ x y : (W : Set V), J.degree x ≤ 3 * J.degree y) ∧
      Fintype.card (W : Set V) ≤ Fintype.card V

attribute [-instance] FinsetCoe.fintype in
private theorem regularized_of_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B) (t : ℕ)
    (partner : Fin t → ↥(B : Set V) → ↥(A : Set V))
    (hinjective : ∀ i, Function.Injective (partner i))
    (hseparate : ∀ b, Function.Injective (fun i => (partner i b).val))
    (hadj : ∀ i b, G.Adj (partner i b).val b.val)
    (hB : B.Nonempty) (hsize : A.card ≤ 2 * B.card)
    (ht : 1 ≤ t) (scale : ℝ) (hscale : scale ≤ (t : ℝ) / 3) : Regularized G scale := by
  classical
  let U := MatchingUnion.unionGraph A B hAB t partner
  let W0 := A ∪ B
  have hspec := MatchingUnion.typed_union_spec A B hAB t partner G
    hinjective hseparate hadj hB hsize
  obtain ⟨_, hbip, horder, horder3, hedge, hdegree, _, _⟩ := hspec
  have hedge0 : inducedEdges U W0 = t * B.card :=
    (inducedEdges_eq_induce U W0).trans hedge
  have hcard0 : W0.card ≤ 3 * B.card := by
    change Fintype.card (W0 : Set V) ≤ 3 * B.card at horder3
    have hc : Fintype.card (W0 : Set V) = W0.card :=
      Fintype.card_of_finset' W0 (fun _ => Iff.rfl)
    omega
  have hpot : 0 ≤ pruningPotential U ((t : ℝ) / 3) W0 := by
    unfold pruningPotential
    rw [hedge0]
    have hcardR : (W0.card : ℝ) ≤ 3 * (B.card : ℝ) := by exact_mod_cast hcard0
    push_cast
    nlinarith [(show (0 : ℝ) ≤ t by positivity)]
  have hW0 : W0.Nonempty := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨b, Finset.mem_union.mpr (Or.inr hb)⟩
  obtain ⟨W, hsub, hW, _, hmin, havg⟩ :=
    RegularizationPruning.exists_induced_min_degree_nonnegative_potential U W0 hW0
      ((t : ℝ) / 3) (by positivity) hpot
  let J := U.induce (W : Set V)
  have hupper : ∀ x : (W : Set V), J.degree x ≤ t := by
    intro x
    change (U.induce (W : Set V)).degree x ≤ t
    rw [← mask_degree_eq_induce U W x]
    exact (mask_degree_le U W x.val).trans
      (MatchingUnion.degree_le_of_mem_union A B hAB t partner hinjective hseparate
        x.val (hsub x.property))
  have hcardW : Fintype.card (W : Set V) = W.card :=
    Fintype.card_of_finset' W (fun _ => Iff.rfl)
  have haverage : 2 * ((t : ℝ) / 3) ≤ graphAverage J := by
    unfold graphAverage
    rw [degreeVolume_eq_twice_edges, hcardW]
    exact havg
  have hpositive : 0 < (t : ℝ) / 3 := by
    have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    exact div_pos htR (by norm_num)
  refine ⟨W, hW, J, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact MatchingUnion.unionGraph_le_original A B hAB t partner G hadj hxy
  · exact induce_isBipartite U W (MatchingUnion.unionGraph_isBipartiteWith A B hAB t partner).isBipartite
  · linarith
  · linarith
  · intro x
    exact hscale.trans (hmin x)
  · intro x y
    have hx : (J.degree x : ℝ) ≤ t := by exact_mod_cast hupper x
    have hy := hmin y
    exact_mod_cast (show (J.degree x : ℝ) ≤ 3 * (J.degree y : ℝ) by linarith)
  · rw [hcardW]
    exact Finset.card_le_univ W

attribute [-instance] FinsetCoe.fintype in
/-- The large-degree branch builds the literal cut, layers, edge union and final graph. -/
theorem regularized_large_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hD : 8 ≤ graphAverage G) :
    Regularized G (graphAverage G / (100 * Real.log (Fintype.card V : ℝ))) := by
  classical
  have hDpos : 0 < graphAverage G := by linarith
  obtain ⟨S, W0, hW0, hmin⟩ := exists_cut_minimum_core G hn hDpos
  let R := mask (ActualMaxCut.cutGraph G S) W0
  have hRG : R ≤ G := (mask_le (ActualMaxCut.cutGraph G S) W0).trans (ActualMaxCut.cutGraph_le G S)
  let A1 := S ∩ W0
  let B1 := W0 \ S
  have hAB1 : Disjoint A1 B1 := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).1
  have hAsub : A1 ⊆ W0 := Finset.inter_subset_right
  have hBsub : B1 ⊆ W0 := Finset.sdiff_subset
  have hbip : R.IsBipartiteWith (A1 : Set V) (B1 : Set V) := by
    refine ⟨Finset.disjoint_coe.mpr hAB1, ?_⟩
    intro a b hab
    change (ActualMaxCut.cutGraph G S).Adj a b ∧ a ∈ W0 ∧ b ∈ W0 at hab
    obtain ⟨hcut, haW, hbW⟩ := hab
    rcases (ActualMaxCut.cutGraph_adj G S a b).mp hcut with ⟨_, h | h⟩
    · exact Or.inl ⟨Finset.mem_inter.mpr ⟨h.1, haW⟩, Finset.mem_sdiff.mpr ⟨hbW, h.2⟩⟩
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨haW, h.1⟩, Finset.mem_inter.mpr ⟨h.2, hbW⟩⟩
  have hshores : A1.Nonempty ∧ B1.Nonempty := by
    obtain ⟨a, ha⟩ := hW0
    have hpos : 0 < R.degree a := by
      have hh := hmin a ha
      exact_mod_cast (show (0 : ℝ) < R.degree a by linarith)
    obtain ⟨b, hab⟩ := (R.degree_pos_iff_exists_adj a).mp hpos
    rcases hbip.mem_of_adj hab with h | h
    · exact ⟨⟨a, h.1⟩, ⟨b, h.2⟩⟩
    · exact ⟨⟨b, h.2⟩, ⟨a, h.1⟩⟩
  have hbalanced : ∃ A B : Finset V,
      Disjoint A B ∧ A.Nonempty ∧ A ⊆ W0 ∧ B ⊆ W0 ∧
        R.IsBipartiteWith (A : Set V) (B : Set V) ∧ B.card ≤ A.card := by
    by_cases hcard : B1.card ≤ A1.card
    · exact ⟨A1, B1, hAB1, hshores.1, hAsub, hBsub, hbip, hcard⟩
    · exact ⟨B1, A1, hAB1.symm, hshores.2, hBsub, hAsub, hbip.symm, by omega⟩
  obtain ⟨A, B, hAB, hA, hAW, _, hbipAB, hcardAB⟩ := hbalanced
  let δ := Nat.ceil (graphAverage G / 4)
  have hcontain : ∀ a ∈ A, R.neighborFinset a ⊆ B := by
    intro a ha b hb
    exact hbipAB.mem_of_mem_adj ha (by simpa using hb)
  have hdegree : ∀ a ∈ A, δ ≤ R.degree a := by
    intro a ha
    exact Nat.ceil_le.mpr (hmin a (hAW ha))
  obtain ⟨L⟩ := NestedMatchingLayers.exists_nested_matching_layers R A B δ hA hAB hcardAB hcontain hdegree
  let n := Fintype.card V
  let m := RegularizationParameters.layerCount n
  let x := RegularizationParameters.layerWidth n (graphAverage G)
  obtain ⟨hm, hpow, _, _⟩ := RegularizationParameters.layerCount_spec n hn
  obtain ⟨hidx, _, hscale⟩ := RegularizationParameters.rounded_layer_spec n (graphAverage G) hn hD
  have hstart : (L.right 1).card ≤ n := Finset.card_le_univ _
  have hpositive : ∀ i, 1 ≤ i → i ≤ δ → 0 < (L.right i).card := by
    intro i hi hle
    exact (L.rightNonempty i hi hle).card_pos
  obtain ⟨q, hq, hqx, hdoubling⟩ := MatchingLayerPigeonhole.exists_doubling_layer
    (fun i => (L.right i).card) n m x δ hm hidx hpow hstart hpositive
  obtain ⟨partner, hinjective, hseparate, hadj⟩ := exists_interval_partners R A B δ L hAB q x hq hqx
  have hDisjoint : Disjoint (L.left q) (L.right (q + x)) :=
    hAB.mono (L.leftSubset q (by omega)) (L.rightSubset (q + x) hqx)
  have hsize : (L.left q).card ≤ 2 * (L.right (q + x)).card := by
    rw [L.equalCard q hq (by omega)]
    exact hdoubling
  exact regularized_of_union G (L.left q) (L.right (q + x)) hDisjoint (x + 1) partner
    hinjective hseparate (fun i b => hRG (hadj i b))
    (L.rightNonempty (q + x) (by omega) hqx) hsize (by omega)
    (graphAverage G / (100 * Real.log (n : ℝ))) hscale

attribute [-instance] FinsetCoe.fintype in
private theorem regularized_small_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hD : 0 < graphAverage G) (hsmall : graphAverage G < 8) :
    Regularized G (graphAverage G / (100 * Real.log (Fintype.card V : ℝ))) := by
  classical
  have hnebot : G ≠ ⊥ := by
    intro heq
    subst G
    simp [graphAverage, degreeVolume] at hD
  obtain ⟨a, b, hab⟩ := G.ne_bot_iff_exists_adj.mp hnebot
  have hne : a ≠ b := hab.ne
  let W : Finset V := {a, b}
  have hW : W.Nonempty := ⟨a, by simp [W]⟩
  have hcard : Fintype.card (W : Set V) = 2 := by
    rw [Fintype.card_of_finset' W (fun _ => Iff.rfl)]
    simp [W, hne]
  let J := SimpleGraph.completeGraph (W : Set V)
  have hdegree : ∀ x : (W : Set V), J.degree x = 1 := by
    intro x
    rw [SimpleGraph.complete_graph_degree, hcard]
  have hclass : ∀ x : (W : Set V), x.val = a ∨ x.val = b := by
    intro x
    simpa [W] using x.property
  have hvalNe : ∀ x y : (W : Set V), J.Adj x y → x.val ≠ y.val := by
    intro x y hxy hval
    exact hxy (Subtype.ext hval)
  have hbip : J.IsBipartite := by
    have hh : J.IsBipartiteWith {x | x.val = a} {x | x.val = b} := by
      refine ⟨?_, ?_⟩
      · apply Set.disjoint_left.mpr
        intro x hx hy
        exact hne (hx.symm.trans hy)
      · intro x y hxy
        have hx := hclass x
        have hy := hclass y
        have hh := hvalNe x y hxy
        aesop
    exact hh.isBipartite
  have havg : graphAverage J = 1 := by
    unfold graphAverage degreeVolume
    simp only [hdegree, Nat.cast_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, hcard]
    norm_num
  have hscale := RegularizationParameters.small_degree_scale (Fintype.card V)
    (graphAverage G) hn hsmall.le
  refine ⟨W, hW, J, inferInstance, ?_, hbip, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hx := hclass x
    have hy := hclass y
    have hxyNe := hvalNe x y hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact False.elim (hxyNe (hx.trans hy.symm))
    · exact hx.symm ▸ hy.symm ▸ hab
    · exact hx.symm ▸ hy.symm ▸ hab.symm
    · exact False.elim (hxyNe (hx.trans hy.symm))
  · rw [havg]; norm_num
  · rwa [havg]
  · intro x
    simpa only [hdegree, Nat.cast_one] using hscale
  · intro x y
    rw [hdegree x, hdegree y]
    norm_num
  · rwa [hcard]

attribute [-instance] FinsetCoe.fintype in
/-- A positive-average original graph supplies its own actual regularized subgraph. -/
theorem exists_regularized_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hD : 0 < graphAverage G) :
    Regularized G (graphAverage G / (100 * Real.log (Fintype.card V : ℝ))) := by
  by_cases hlarge : 8 ≤ graphAverage G
  · exact regularized_large_degree G hn hlarge
  · exact regularized_small_degree G hn hD (by linarith)

end Erdos642.CampaignFe72210bContinuation3.RegularizationAssembly
