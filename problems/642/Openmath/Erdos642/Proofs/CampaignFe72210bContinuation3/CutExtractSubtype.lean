import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutRetention
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphExpansionGap

/-! Actual induced-graph packaging of finite cut extraction.

All degree, edge, cut, bipartite and spectral conclusions refer to the induced
graph on the selected subtype. Regularization of an arbitrary input is separate.
-/
namespace Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.GraphDirichlet
open Erdos642.CampaignFe72210bContinuation3.GraphExpansionConductance
open Erdos642.CampaignFe72210bContinuation3.GraphExpansionGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def graphAverage : ℝ := degreeVolume G / (Fintype.card V : ℝ)

omit [DecidableEq V] in
theorem degreeVolume_eq_twice_edges :
    degreeVolume G = 2 * (G.edgeFinset.card : ℝ) := by
  unfold degreeVolume
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem average_univ_eq_graphAverage :
    average G Finset.univ = graphAverage G := by
  have he : (mask G Finset.univ).edgeFinset.card = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
    exact Fintype.card_congr
      (Equiv.cast (congrArg (fun H : SimpleGraph V => ↥H.edgeSet) (mask_univ G)))
  unfold average edges inducedEdges graphAverage
  rw [degreeVolume_eq_twice_edges]
  simp only [he, Finset.card_univ]

attribute [-instance] FinsetCoe.fintype in
theorem restrictedDegree_eq_induce (W : Finset V) (x : (W : Set V)) :
    restrictedDegree G W x.val = (G.induce (W : Set V)).degree x := by
  rw [← mask_degree_eq_restricted G W x.val x.property]
  exact mask_degree_eq_induce G W x

attribute [-instance] FinsetCoe.fintype in
theorem average_eq_induce (W : Finset V) :
    average G W = graphAverage (G.induce (W : Set V)) := by
  unfold average edges graphAverage
  rw [inducedEdges_eq_induce G W, degreeVolume_eq_twice_edges]
  congr 1
  exact_mod_cast (Fintype.card_of_finset' (p := (W : Set V)) W (fun _ => Iff.rfl)).symm

def subtypeValueEmbedding (W : Finset V) : (W : Set V) ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

def ambientFinset (W : Finset V) (A : Finset (W : Set V)) : Finset V :=
  A.map (subtypeValueEmbedding W)

attribute [-instance] FinsetCoe.fintype in
omit [Fintype V] [DecidableEq V] in
theorem ambientFinset_subset (W : Finset V) (A : Finset (W : Set V)) :
    ambientFinset W A ⊆ W := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
  exact y.property

attribute [-instance] FinsetCoe.fintype in
theorem ambientFinset_univ (W : Finset V) :
    ambientFinset W Finset.univ = W := by
  ext x
  constructor
  · exact fun h => ambientFinset_subset W Finset.univ h
  · intro hx
    exact Finset.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

attribute [-instance] FinsetCoe.fintype in
theorem ambientFinset_compl (W : Finset V) (A : Finset (W : Set V)) :
    ambientFinset W Aᶜ = W \ ambientFinset W A := by
  change (Finset.univ \ A).map (subtypeValueEmbedding W) = _
  rw [Finset.map_sdiff]
  exact congrArg (fun B : Finset V => B \ ambientFinset W A) (ambientFinset_univ W)

attribute [-instance] FinsetCoe.fintype in
omit [Fintype V] [DecidableEq V] in
theorem count_induce_eq_ambient (W : Finset V) (A B : Finset (W : Set V)) :
    IncidenceCounts.count (G.induce (W : Set V)) A B =
      IncidenceCounts.count G (ambientFinset W A) (ambientFinset W B) := by
  simp only [IncidenceCounts.count, ambientFinset, Finset.card_filter, Finset.sum_map]
  rfl

theorem crossing_eq_incidence (A : Finset V) :
    crossing G A = (IncidenceCounts.count G A Aᶜ : ℝ) := by
  classical
  simp only [crossing, IncidenceCounts.count, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rfl

attribute [-instance] FinsetCoe.fintype in
theorem crossing_induce_eq_cross (W : Finset V) (A : Finset (W : Set V)) :
    crossing (G.induce (W : Set V)) A = (cross G W (ambientFinset W A) : ℝ) := by
  rw [crossing_eq_incidence, count_induce_eq_ambient, ambientFinset_compl]
  rfl

attribute [-instance] FinsetCoe.fintype in
theorem terminal_induce_expansion (W : Finset V) (lam : ℝ) (hterm : Terminal G lam W) :
    ∀ A : Finset (W : Set V),
      (A.card : ℝ) ≤ (Fintype.card (W : Set V) : ℝ) / 2 →
      (lam / 3) * graphAverage (G.induce (W : Set V)) * (A.card : ℝ) ≤
        crossing (G.induce (W : Set V)) A := by
  intro A hA
  have hcard : 2 * A.card ≤ W.card := by
    have hWcard : Fintype.card (W : Set V) = W.card :=
      Fintype.card_of_finset' W (fun _ => Iff.rfl)
    rw [hWcard] at hA
    exact_mod_cast (show (2 : ℝ) * (A.card : ℝ) ≤ (W.card : ℝ) by linarith)
  have hhalf : 2 * (ambientFinset W A).card ≤ W.card := by
    simpa [ambientFinset] using hcard
  have hh := hterm.2 (ambientFinset W A) (ambientFinset_subset W A) hhalf
  rw [crossing_induce_eq_cross, ← average_eq_induce]
  simpa [ambientFinset] using hh

attribute [-instance] FinsetCoe.fintype in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem induce_isBipartite (W : Finset V) (hbip : G.IsBipartite) :
    (G.induce (W : Set V)).IsBipartite := by
  exact SimpleGraph.Colorable.of_hom
    (show G.induce (W : Set V) →g G from
      { toFun := Subtype.val, map_rel' := fun h => h }) hbip

attribute [-instance] FinsetCoe.fintype in
/-- Actual cut extraction from a given bipartite six-almost-regular graph.
Positive degrees, cut expansion, connectedness and the full spectral predicate
are conclusions proved for the actual induced subtype graph. -/
theorem exists_induced_cut_expander (n : ℕ) (hn : 2 ≤ n)
    (horder : Fintype.card V ≤ n) (hpos : 0 < graphAverage G)
    (hbip : G.IsBipartite) (hratio : G.maxDegree ≤ 6 * G.minDegree) :
    ∃ W : Finset V, W.Nonempty ∧
      let H := G.induce (W : Set V)
      Fintype.card (W : Set V) ≤ Fintype.card V ∧
      0 < graphAverage H ∧ graphAverage G / 2 ≤ graphAverage H ∧
      graphAverage G / 4 ≤ (H.minDegree : ℝ) ∧
      H.maxDegree ≤ 24 * H.minDegree ∧ H.maxDegree ≤ 100 * H.minDegree ∧
      H.IsBipartite ∧ H.Connected ∧
      (∀ A : Finset (W : Set V),
        (A.card : ℝ) ≤ (Fintype.card (W : Set V) : ℝ) / 2 →
        (lossParameter n / 3) * graphAverage H * (A.card : ℝ) ≤ crossing H A) ∧
      HasBipartiteSpectralGap H (((lossParameter n / 3) / 100) ^ 2 / 8) := by
  classical
  have hcardpos : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp [graphAverage, hz] at hpos
  have : Nonempty V := Fintype.card_pos_iff.mp hcardpos
  have havgpos : 0 < average G Finset.univ := by
    simpa only [average_univ_eq_graphAverage] using hpos
  obtain ⟨W, _, hWpos, hterm, hret, hmindeg⟩ :=
    exists_terminal_half_density G Finset.univ n hn (by simpa using horder) havgpos
  have hWne : W.Nonempty := Finset.card_pos.mp (by
    have hc := average_pos_card G W hWpos
    omega)
  have : Nonempty (W : Set V) := hWne.to_subtype
  let H := G.induce (W : Set V)
  have hHpos : 0 < graphAverage H := by
    simpa only [average_eq_induce] using hWpos
  have hHret : graphAverage G / 2 ≤ graphAverage H := by
    rw [average_univ_eq_graphAverage, average_eq_induce] at hret
    exact hret
  have hdegree : ∀ x : (W : Set V), graphAverage G / 4 ≤ (H.degree x : ℝ) := by
    intro x
    have hh := hmindeg x.val x.property
    rw [average_univ_eq_graphAverage, restrictedDegree_eq_induce] at hh
    exact hh
  obtain ⟨xmin, hxmin⟩ := H.exists_minimal_degree_vertex
  have hmin : graphAverage G / 4 ≤ (H.minDegree : ℝ) := by
    rw [hxmin]
    exact hdegree xmin
  have hdegpos : ∀ x : (W : Set V), 0 < H.degree x := by
    intro x
    have hh : (0 : ℝ) < H.degree x := lt_of_lt_of_le (by positivity) (hdegree x)
    exact_mod_cast hh
  have hmaxle : H.maxDegree ≤ G.maxDegree := by
    apply H.maxDegree_le_of_forall_degree_le
    intro x
    rw [← mask_degree_eq_induce G W x]
    exact (mask_degree_le G W x.val).trans (G.degree_le_maxDegree x.val)
  have hminG : (G.minDegree : ℝ) ≤ graphAverage G := average_degree_ge_min G
  have hmaxreal : (H.maxDegree : ℝ) ≤ 24 * (H.minDegree : ℝ) := by
    have ha : (H.maxDegree : ℝ) ≤ G.maxDegree := by exact_mod_cast hmaxle
    have hb : (G.maxDegree : ℝ) ≤ 6 * (G.minDegree : ℝ) := by exact_mod_cast hratio
    linarith
  have hratio24 : H.maxDegree ≤ 24 * H.minDegree := by exact_mod_cast hmaxreal
  have hratio100 : H.maxDegree ≤ 100 * H.minDegree := by omega
  have hHbip : H.IsBipartite := induce_isBipartite G W hbip
  have hexpand := terminal_induce_expansion G W (lossParameter n) hterm
  have hlam : 0 < lossParameter n / 3 :=
    div_pos (lossParameter_pos_le_half n hn).1 (by norm_num)
  have hlam2 : lossParameter n / 3 ≤ 2 := by
    have hh := (lossParameter_pos_le_half n hn).2
    linarith
  have hconn : H.Connected := expansion_connected H hdegpos (lossParameter n / 3) hlam hexpand
  have hgap : HasBipartiteSpectralGap H (((lossParameter n / 3) / 100) ^ 2 / 8) := by
    apply graph_hasBipartiteSpectralGap_of_expansion H hdegpos hHbip 100
      (lossParameter n / 3) (by norm_num) hlam hlam2
    · exact_mod_cast hratio100
    · exact hexpand
  refine ⟨W, hWne, ?_, hHpos, hHret, hmin, hratio24, hratio100, hHbip, hconn, hexpand, hgap⟩
  have hWcard : Fintype.card (W : Set V) = W.card :=
    Fintype.card_of_finset' (p := (W : Set V)) W (fun _ => Iff.rfl)
  rw [hWcard]
  exact Finset.card_le_univ W

end Erdos642.CampaignFe72210bContinuation3.CutExtraction
