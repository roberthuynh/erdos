import NEQAssembly.Minimal

/-! Explicit conditional assembly.
FullCarrierBarrierKernel below is an explicit proposition assumed by the theorem.
This file does not prove that proposition or introduce it as an axiom.
The bare endpoint is not claimed by this source. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.NEQAssembly
open QB4 B5 NEQ
universe u

def FullCarrierBarrierKernel (q : ℕ) : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (K : SimpleGraph W),
    K.maxDegree ≤ 2 * q - 2 →
    (¬∃ H : K.Subgraph, H.IsSpanning ∧ H.coe.IsRegularOfDegree q) →
    ∃ S T : Finset W, Disjoint S T ∧ NEQ.delta q K univ S T < 0

lemma original_shore_swap {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (S T : Finset V) :
    NEQ.delta q G univ T S =
      (q : ℤ) * ((#S : ℤ) - #T) + (ec G T T : ℤ) +
      ec G T (univ \ (S ∪ T)) - oddCount G T (univ \ (S ∪ T)) := by
  unfold NEQ.delta
  rw [union_comm T S]

theorem critical_counter_extraction {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 6 ≤ q) (heven : Even q) (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + q / 2)
    (havoid : ¬∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ∃ U : Finset V, ∃ K : SimpleGraph (U : Set V),
      2 ≤ Fintype.card (U : Set V) ∧ K ≤ G.induce (U : Set V) ∧
      K.maxDegree ≤ 2 * q - 2 ∧
      K.edgeSet.ncard + q / 2 = (q - 1) * Fintype.card (U : Set V) ∧
      (∀ X : Finset (U : Set V), X.Nonempty → X ≠ univ →
        (q : ℤ) + 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec K X X : ℤ)) ∧
      (¬∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) := by
  obtain ⟨U, K, hnK, hsub, hcapK, hexact, hfloor⟩ := critical_extraction q hq heven G hn hcap he
  exact ⟨U, K, hnK, hsub, hcapK, hexact, hfloor,
    extraction_preserves_avoidance q G U K hsub havoid⟩

lemma no_spanning_of_no_original_support {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (havoid : ¬∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ¬∃ H : G.Subgraph, H.IsSpanning ∧ H.coe.IsRegularOfDegree q := by
  rintro ⟨H, hspanning, hregular⟩
  have hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hnonempty
  have hv : v ∈ H.verts := by rw [hspanning.verts_eq_univ]; exact Set.mem_univ _
  exact havoid ⟨H, ⟨v, hv⟩, hregular⟩

/-- This theorem assumes the cut proposition FullCarrierBarrierKernel through hkernel.
It does not establish the conclusion without that premise. -/
theorem neq_from_full_carrier_barrier_kernel {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (hkernel : FullCarrierBarrierKernel.{u} q) (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + q / 2) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  by_contra havoid
  obtain ⟨U, K, hnK, hsub, hcapK, hexact, hfloor, havoidK⟩ :=
    critical_counter_extraction q hq heven G hn hcap he havoid
  have hnospan := no_spanning_of_no_original_support q K hnK havoidK
  obtain ⟨S, T, hST, hnegative⟩ := hkernel K hcapK hnospan
  have hregular := regular_of_critical_barrier q hq heven K hnK hcapK hexact hfloor S T hST hnegative
  exact havoid (original_thinned_induced_regular_transport G U K hsub hregular)

#print axioms FullCarrierBarrierKernel
#print axioms original_shore_swap
#print axioms critical_counter_extraction
#print axioms no_spanning_of_no_original_support
#print axioms neq_from_full_carrier_barrier_kernel
end Erdos585.NEQAssembly
