import R701.Main
import R699.Main
import R707.Main
import R703.Main
import R704.Main
import R706.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.H49BalancedR715
open QB4 B5 H3Unequal AllHTopCritical H49Q0R701
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {q : ℕ} {A B P Q : Finset V}

/-- Actual finite preimage shore in the original induced carrier. -/
def shore (P Q R : Finset V) : Finset (↑(P∪Q) : Set V) :=
  univ.filter fun v => v.val ∈ R
omit [Fintype V] in
lemma mem_shore (R : Finset V) (v : (↑(P∪Q) : Set V)) :
    v ∈ shore P Q R ↔ v.val ∈ R := by simp [shore]
omit [Fintype V] in
lemma shore_image (R : Finset V) (hR : R ⊆ P∪Q) :
    (shore P Q R).image Subtype.val = R := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_shore R w).mp hw
  · intro hv
    exact mem_image.mpr ⟨⟨v,hR hv⟩,(mem_shore R ⟨v,hR hv⟩).mpr hv,rfl⟩
omit [Fintype V] in
lemma shore_card (R : Finset V) (hR : R ⊆ P∪Q) : #(shore P Q R) = #R := by
  calc
    #(shore P Q R) = #((shore P Q R).image Subtype.val) :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ = #R := congrArg Finset.card (shore_image R hR)

/-- All proper-Q0 hypotheses derived from the actual original constructor. -/
theorem actual_q0_host (host : Host 3 q G A B) (piece : Q0 q G A B P Q) :
    Omit1Q0CutChainR699.Host q (G.induce (↑(P∪Q) : Set V))
      (shore P Q P) (shore P Q Q) := by
  classical
  let K := G.induce (↑(P∪Q) : Set V)
  let PP := shore P Q P
  let QQ := shore P Q Q
  have hp : (shore P Q P).image Subtype.val = P := shore_image P subset_union_left
  have hq : (shore P Q Q).image Subtype.val = Q := shore_image Q subset_union_right
  have cp : #PP = #P := shore_card P subset_union_left
  have cq : #QQ = #Q := shore_card Q subset_union_right
  have hd : Disjoint PP QQ := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp piece.disjoint ((mem_shore P v).mp hv) ((mem_shore Q v).mp hw)
  have hc : PP∪QQ = univ := by
    ext v
    have hv := v.property
    simp only [mem_union, mem_univ, iff_true]
    exact (mem_union.mp hv).elim
      (fun h => Or.inl ((mem_shore P v).mpr h))
      (fun h => Or.inr ((mem_shore Q v).mpr h))
  have hb : K.IsBipartiteWith (PP : Set (↑(P∪Q) : Set V)) (QQ : Set (↑(P∪Q) : Set V)) := by
    constructor
    · exact Set.disjoint_left.mpr (fun v hv hw => Finset.disjoint_left.mp hd hv hw)
    · intro v w hadj
      have hv := v.property
      have hw := w.property
      rcases host.bipartite.mem_of_adj (show G.Adj v.val w.val from hadj) with h | h
      · have vp : v.val ∈ P := (mem_union.mp hv).resolve_right
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint h.1 (piece.right_subset ht))
        have wq : w.val ∈ Q := (mem_union.mp hw).resolve_left
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint (piece.left_subset ht) h.2)
        exact Or.inl ⟨(mem_shore P v).mpr vp,(mem_shore Q w).mpr wq⟩
      · have vq : v.val ∈ Q := (mem_union.mp hv).resolve_left
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint (piece.left_subset ht) h.1)
        have wp : w.val ∈ P := (mem_union.mp hw).resolve_right
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint h.2 (piece.right_subset ht))
        exact Or.inr ⟨(mem_shore Q v).mpr vq,(mem_shore P w).mpr wp⟩
  have he : ec K PP QQ = ec G P Q := by
    have hh := NEQAssembly.ec_embedding_image K G
      (SimpleGraph.Embedding.induce (G := G) (↑(P∪Q) : Set V)) PP QQ
    change ec G (PP.image Subtype.val) (QQ.image Subtype.val) = _ at hh
    rw [hp,hq] at hh
    exact hh.symm
  refine ⟨⟨host.parameters.large, by norm_num, hd,?_,?_,hb,piece.cap,?_,?_⟩,
    piece.minimum,piece.no_regular⟩
  · apply Finset.coe_injective
    simpa only [Finset.coe_union, Finset.coe_univ] using
      congrArg (fun S : Finset (↑(P∪Q) : Set V) => (S : Set (↑(P∪Q) : Set V))) hc
  · exact cp.trans (piece.balanced.trans cq.symm)
  · have ht := paired_defect host piece.left_subset piece.right_subset
    have hh := piece.exact_defect
    rw [ht] at hh
    change coreDefect q K PP QQ = _
    unfold coreDefect at hh ⊢
    rw [cp,cq,he]
    simpa using hh
  · intro S hl hp
    have hh := piece.induced_strict_floor S hl hp
    change 3*(q : ℤ)-31+0+1 ≤ defect q (G.induce (↑(P∪Q) : Set V)) S
    linarith

/-- The exact literal negative-family split, using both actual proved branch suppliers. -/
theorem q0_unit_cuts (host : Omit1Q0CutChainR699.Host q G A B) :
    ∃ a ∈ A, ∃ b ∈ B, Omit1UnitCutAdapterR707.UnitCuts q G A B a b := by
  obtain ⟨S,T,hs,ht,_,_,extrema⟩ := Omit1Q0CutChainR699.negative_extrema host
  by_cases he : S = T
  · have hu : ∀ N : Finset V, Omit1PrefixR691.g q G A B N < 0 → N = S := by
      intro N hn
      have ex := extrema N hn
      rw [← he] at ex
      exact Subset.antisymm ex.2 ex.1
    obtain ⟨a,ha,b,hb,uc⟩ := Omit1UniqueR704.unique_pair_paid_of_unique_negative host hs hu
    exact ⟨a,(mem_inter.mp ha).1,b,(mem_sdiff.mp hb).1,uc⟩
  · obtain ⟨a,ha,b,hb,uc⟩ :=
      Omit1ChainBranchR703.strict_chain_unit_cuts host S T hs ht he extrema
    exact ⟨a,(mem_inter.mp ha).1,b,(mem_sdiff.mp hb).1,uc⟩

/-- One actual negative cut pays the retained shore size before invoking R707. -/
theorem q0_shore_size (host : Omit1Q0CutChainR699.Host q G A B) : q ≤ #A-1 := by
  obtain ⟨S,hs⟩ := Omit1Q0CutChainR699.exists_negative host
  have d := Omit1Q0CutChainR699.all_negative host S hs
  have hi := d.imbalance
  unfold Omit1PrefixR691.k at hi
  have hc := Omit1PrefixR691.support_card host.toHost S
  have hA := card_le_card (inter_subset_left : A∩S ⊆ A)
  have ho := d.order
  omega

/-- Every literal original balanced Host3 is impossible; all Q0 and cut inputs are derived. -/
theorem balanced_host_impossible (host : Host 3 q G A B) : False := by
  obtain ⟨P,Q,piece⟩ := construct_q0 host
  have actual := actual_q0_host host piece
  obtain ⟨a,ha,b,hb,uc⟩ := q0_unit_cuts actual
  exact Omit1UnitCutAdapterR707.contradict_noq actual.disjoint actual.balanced ha hb
    (by have h := actual.large; omega) (q0_shore_size actual) uc actual.no_regular

/-- Bare original H49 graph endpoint, without balanced/Q0/floor/cut/factor suppliers. -/
theorem bare_h49 (q : ℕ) (hq : 16384 ≤ q) (G : SimpleGraph V)
    (hbip : G.IsBipartite) (hcap : G.maxDegree ≤ 2*q-2)
    (hn : 2*q ≤ Fintype.card V)
    (he : (q-1)*Fintype.card V-(3*q-32) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact H49CriticalR706.bare_h49_of_balanced_impossible q hq
    (by intro W inst K U T host; exact balanced_host_impossible host) G hbip hcap hn he

#print axioms actual_q0_host
#print axioms q0_unit_cuts
#print axioms q0_shore_size
#print axioms balanced_host_impossible
#print axioms bare_h49
end Erdos585.H49BalancedR715
