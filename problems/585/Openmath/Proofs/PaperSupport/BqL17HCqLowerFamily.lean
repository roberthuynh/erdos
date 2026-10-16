import L17HCq.Family
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open Finset SimpleGraph BqLowerFamily
namespace Erdos585.L17HCq

/-- Extract the actual finite carrier and original Subgraph endpoint from proved data. -/
theorem original_endpoint (q c : ℕ) (D : LabeledGraph) (hq : 1 ≤ q)
    (h : D.IsGood q c) (n : ℕ) (hn : D.order=n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V=n ∧ G.IsBipartite ∧
          (∀ v,q-1 ≤ G.degree v) ∧ G.maxDegree ≤ 2*q-2 ∧
          G.edgeFinset.card+c=(q-1)*n ∧
          ¬ (∃ H : G.Subgraph,H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) := by
  letI := D.finite
  letI := D.eqDec
  letI := D.adjDec
  change Good q c D.graph D.A D.B at h
  refine ⟨D.carrier,D.finite,D.eqDec,D.graph,D.adjDec,hn,h.bipartite.isBipartite,
    fun v => (h.degree_bounds v).1,?_,?_,h.no_regular⟩
  · have hm := D.graph.maxDegree_le_of_forall_degree_le (2*(q-1))
      (fun v => (h.degree_bounds v).2)
    have hc : 2*(q-1)=2*q-2 := by omega
    rwa [hc] at hm
  · rw [← hn]
    exact h.edge_density

/-- Every original order is realized by the exact raw L17 least-label birth family. -/
theorem l17_all_orders (n : ℕ) (hn : 17 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V=n ∧ G.IsBipartite ∧
          (∀ v,4 ≤ G.degree v) ∧ G.maxDegree ≤ 8 ∧
          G.edgeFinset.card+13=4*n ∧
          ¬ (∃ H : G.Subgraph,H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 5) := by
  have hc : (l17Family (n-17)).order=n := by rw [l17_family_order];omega
  exact original_endpoint 5 13 (l17Family (n-17)) (by decide) (l17_family_good _) n hc

/-- Every natural q>=5 and original order is realized by the exact HCq family. -/
theorem hcq_all_orders (q : ℕ) (hq : 5 ≤ q) (n : ℕ) (hn : 2*q+7 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V=n ∧ G.IsBipartite ∧
          (∀ v,q-1 ≤ G.degree v) ∧ G.maxDegree ≤ 2*q-2 ∧
          G.edgeFinset.card+(q^2-2*q-2)=(q-1)*n ∧
          ¬ (∃ H : G.Subgraph,H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) := by
  have hc : (hcqFamily q (n-(2*q+7))).order=n := by rw [hcq_family_order];omega
  exact original_endpoint q (hcqDeficit q) (hcqFamily q (n-(2*q+7))) (by omega)
    (hcq_family_good q hq _) n hc

theorem l17_natural_all_orders (n : ℕ) (hn : 17 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V=n ∧ G.IsBipartite ∧
          (∀ v,4 ≤ G.degree v) ∧ G.maxDegree ≤ 8 ∧
          G.edgeFinset.card=4*n-13 ∧
          ¬ (∃ H : G.Subgraph,H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 5) := by
  rcases l17_all_orders n hn with ⟨V,vf,vd,G,gd,hcard,hb,hl,hu,he,hno⟩
  letI := vf
  letI := vd
  letI := gd
  exact ⟨V,vf,vd,G,gd,hcard,hb,hl,hu,by omega,hno⟩

theorem hcq_natural_all_orders (q : ℕ) (hq : 5 ≤ q) (n : ℕ) (hn : 2*q+7 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V=n ∧ G.IsBipartite ∧
          (∀ v,q-1 ≤ G.degree v) ∧ G.maxDegree ≤ 2*q-2 ∧
          G.edgeFinset.card=(q-1)*n-(q^2-2*q-2) ∧
          ¬ (∃ H : G.Subgraph,H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) := by
  rcases hcq_all_orders q hq n hn with ⟨V,vf,vd,G,gd,hcard,hb,hl,hu,he,hno⟩
  letI := vf
  letI := vd
  letI := gd
  exact ⟨V,vf,vd,G,gd,hcard,hb,hl,hu,by omega,hno⟩

@[simp] theorem l17_family_seed : l17Family 0=l17SeedData := rfl
@[simp] theorem hcq_family_seed (q : ℕ) : hcqFamily q 0=hcqSeedData q := rfl
@[simp] theorem l17_family_step (k : ℕ) : l17Family (k+1)=(l17Family k).step 5 := rfl
@[simp] theorem hcq_family_step (q k : ℕ) : hcqFamily q (k+1)=(hcqFamily q k).step q := rfl

theorem l17_birth_card (k : ℕ) : ((l17Family k).neighbors 5).card=4 :=
  LabeledGraph.neighbors_card 5 13 (l17Family k) (by decide) (by decide) (l17_family_good k)

theorem hcq_birth_card (q : ℕ) (hq : 5 ≤ q) (k : ℕ) : ((hcqFamily q k).neighbors q).card=q-1 :=
  LabeledGraph.neighbors_card q (hcqDeficit q) (hcqFamily q k) hq
    (hcq_deficit_guard q hq) (hcq_family_good q hq k)

theorem LabeledGraph.step_graph (q : ℕ) (D : LabeledGraph) :
    letI := D.eqDec
    (D.step q).graph=extendGraph D.graph (D.neighbors q) := by
  letI := D.eqDec
  rfl

/-- Original unit-edge and degree transport for the literal step graph above. -/
theorem LabeledGraph.step_new_degree (q c : ℕ) (D : LabeledGraph) (hq : 5 ≤ q)
    (hc : (q-1)*(q-2)+1 ≤ c) (h : D.IsGood q c) :
    letI := D.finite
    letI := D.eqDec
    letI := D.adjDec
    (extendGraph D.graph (D.neighbors q)).degree none=q-1 := by
  letI := D.finite
  letI := D.eqDec
  letI := D.adjDec
  exact (degree_none D.graph (D.neighbors q)).trans (D.neighbors_card q c hq hc h)

/-- Receiving A on a tie is part of the actual construction. -/
theorem LabeledGraph.step_shore_A (q : ℕ) (D : LabeledGraph) :
    letI := D.eqDec
    (D.step q).A=if D.A.card ≤ D.B.card then insert none (D.A.image some) else D.A.image some := by
  letI := D.eqDec
  rfl

theorem LabeledGraph.step_shore_B (q : ℕ) (D : LabeledGraph) :
    letI := D.eqDec
    (D.step q).B=if D.A.card ≤ D.B.card then D.B.image some else insert none (D.B.image some) := by
  letI := D.eqDec
  rfl

end Erdos585.L17HCq
