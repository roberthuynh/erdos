import R788.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.H4BareR788
open QB4 B5 H3Unequal AllHTopCritical
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {q : ℕ} {A B P Q : Finset V}

/-- Explicit interim input: a q-factor on the literal balanced original h4 band host.
The independent R783 supplier discharges this proposition in `R788/Endpoint.lean`. -/
def CoreFactorSupplier (q : ℕ) : Prop :=
  ∀ {W : Type u} [Fintype W] (K : SimpleGraph W) (L R : Finset W) (F : ℤ),
    AllHCommonPinsR773.Host 4 q F K L R →
    ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

/-- R753's actual induced core satisfies every literal band-host field. -/
theorem actual_core_host (host : Host 4 q G A B)
    (core : R753.TwoOffsetCore q G A B P Q) :
    AllHCommonPinsR773.Host 4 q (R753.defect q G (P∪Q))
      (G.induce (↑(P∪Q) : Set V)) (R753.shore P Q P) (R753.shore P Q Q) := by
  classical
  let K := G.induce (↑(P∪Q) : Set V)
  let PP := R753.shore P Q P
  let QQ := R753.shore P Q Q
  have hp : PP.image Subtype.val = P := R753.shore_image P subset_union_left
  have hq : QQ.image Subtype.val = Q := R753.shore_image Q subset_union_right
  have cp : #PP = #P := R753.shore_card P subset_union_left
  have cq : #QQ = #Q := R753.shore_card Q subset_union_right
  have hd : Disjoint PP QQ := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp core.disjoint
      ((R753.mem_shore P v).mp hv) ((R753.mem_shore Q v).mp hw)
  have hc : PP∪QQ = univ := by
    ext v
    have hv := v.property
    simp only [mem_union,mem_univ,iff_true]
    exact (mem_union.mp hv).elim
      (fun h => Or.inl ((R753.mem_shore P v).mpr h))
      (fun h => Or.inr ((R753.mem_shore Q v).mpr h))
  have hb : K.IsBipartiteWith (PP : Set (↑(P∪Q) : Set V))
      (QQ : Set (↑(P∪Q) : Set V)) := by
    constructor
    · exact Set.disjoint_left.mpr (fun v hv hw => Finset.disjoint_left.mp hd hv hw)
    · intro v w hadj
      have hv := v.property
      have hw := w.property
      rcases host.bipartite.mem_of_adj (show G.Adj v.val w.val from hadj) with h | h
      · have vp : v.val ∈ P := (mem_union.mp hv).resolve_right
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint h.1 (core.right_subset ht))
        have wq : w.val ∈ Q := (mem_union.mp hw).resolve_left
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint (core.left_subset ht) h.2)
        exact Or.inl ⟨(R753.mem_shore P v).mpr vp,(R753.mem_shore Q w).mpr wq⟩
      · have vq : v.val ∈ Q := (mem_union.mp hv).resolve_left
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint (core.left_subset ht) h.1)
        have wp : w.val ∈ P := (mem_union.mp hw).resolve_right
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint h.2 (core.right_subset ht))
        exact Or.inr ⟨(R753.mem_shore Q v).mpr vq,(R753.mem_shore P w).mpr wp⟩
  have he : ec K PP QQ = ec G P Q := by
    have hh := NEQAssembly.ec_embedding_image K G
      (SimpleGraph.Embedding.induce (G := G) (↑(P∪Q) : Set V)) PP QQ
    change ec G (PP.image Subtype.val) (QQ.image Subtype.val) = _ at hh
    rw [hp,hq] at hh
    exact hh.symm
  refine { height := by decide
           large := host.parameters.large
           disjoint := hd
           cover := by simpa only [Finset.ext_iff,Finset.mem_union] using hc
           balanced := cp.trans (core.balanced.trans cq.symm)
           bipartite := hb
           order := ?_
           min_degree := core.minimum
           cap := core.cap
           total := ?_
           range := ?_
           proper := core.induced_strict_floor }
  · rw [Fintype.card_of_finset' (P∪Q) (fun _ => Iff.rfl)]
    exact core.order
  · rw [R753.paired_defect host core.left_subset core.right_subset]
    change coreDefect q K PP QQ = coreDefect q G P Q
    unfold coreDefect
    rw [cp,cq,he]
  · have hh := core.exact_defect
    norm_num [AllHCommonPinsR773.baseDeficit,AllHCommonPinsR773.constant]
    omega

/-- Balanced contradiction derives its actual core; only its factor supplier is explicit. -/
theorem balanced_host_impossible (supplier : CoreFactorSupplier.{u} q)
    (host : Host 4 q G A B) : False := by
  obtain ⟨P,Q,core⟩ := R753.construct_two_offset_core host
  have actual := actual_core_host host core
  exact core.no_regular (supplier _ _ _ _ actual)

/-- Bare original h4 endpoint, conditional solely on the literal balanced core supplier. -/
theorem bare_h4_of_core_factor (q : ℕ) (hq : 25600 ≤ q)
    (supplier : CoreFactorSupplier.{u} q) (G : SimpleGraph V)
    (hbip : G.IsBipartite) (hcap : G.maxDegree ≤ 2*q-2)
    (hn : 2*q ≤ Fintype.card V)
    (he : (q-1)*Fintype.card V-(4*q-44) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact bare_h4_of_balanced_impossible q hq
    (by intro W inst K L R host; exact balanced_host_impossible supplier host)
    G hbip hcap hn he

/-- Raw n-vertex original-graph caller with the literal per-vertex degree cap. -/
theorem bare_h4_raw_of_core_factor (q n : ℕ) (hq : 25600 ≤ q)
    (supplier : CoreFactorSupplier.{u} q) (G : SimpleGraph V)
    (card : Fintype.card V=n) (bipartite : G.IsBipartite)
    (cap : ∀ v : V, G.degree v ≤ 2*q-2) (order : 2*q ≤ n)
    (edges : (q-1)*n-(4*q-44) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact bare_h4_of_core_factor q hq supplier G bipartite
    (G.maxDegree_le_of_forall_degree_le _ cap) (by omega) (by simpa [card] using edges)

#print axioms actual_core_host
#print axioms balanced_host_impossible
#print axioms bare_h4_of_core_factor
#print axioms bare_h4_raw_of_core_factor
end Erdos585.H4BareR788
