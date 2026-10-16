import NEQAssembly.Counts
import NEQAssembly.Critical

/-! Minimum actual original dense support and exact original edge thinning.
Frozen23792c95: no cut/factor criterion is assumed in this extraction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.NEQAssembly
open QB4 B5 NEQ
universe u

def DenseOn {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (U : Finset V) : Prop :=
  2 ≤ #U ∧ 2 * (q - 1) * #U ≤ ec G U U + q

theorem minimal_dense_support {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (heven : Even q) (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + q / 2) :
    ∃ U : Finset V, DenseOn q G U ∧
      ∀ X : Finset V, X ⊂ U → ¬DenseOn q G X := by
  have hhalf := even_half q heven
  have hseed : DenseOn q G univ := by
    unfold DenseOn
    simp only [card_univ, ec_univ_eq_twice_edges]
    exact ⟨hn, by nlinarith⟩
  let family : Finset (Finset V) := univ.powerset.filter (DenseOn q G)
  have hseedmem : (univ : Finset V) ∈ family :=
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hseed⟩
  obtain ⟨U, hU, hmin⟩ := exists_min_image family Finset.card ⟨univ, hseedmem⟩
  refine ⟨U, (mem_filter.mp hU).2, ?_⟩
  intro X hX hXdense
  have hXmem : X ∈ family :=
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hXdense⟩
  have hsmall := hmin X hXmem
  have hstrict := card_lt_card hX
  omega

lemma minimal_original_floor {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 6 ≤ q) (heven : Even q) (G : SimpleGraph V)
    (U : Finset V)
    (hminimal : ∀ X : Finset V, X ⊂ U → ¬DenseOn q G X)
    (X : Finset V) (hne : X.Nonempty) (hproper : X ⊂ U) :
    (q : ℤ) + 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec G X X : ℤ) := by
  by_cases hn : 2 ≤ #X
  · have hfail : ec G X X + q < 2 * (q - 1) * #X := by
      exact lt_of_not_ge (fun h => hminimal X hproper ⟨hn, h⟩)
    rw [ec_self_eq_twice_induced_edges] at hfail
    have hhalf := even_half q heven
    have he : (G.induce (X : Set V)).edgeSet.ncard + q / 2 < (q - 1) * #X := by
      nlinarith
    have hf := proper_floor_from_failure hq heven he
    rw [ec_self_eq_twice_induced_edges]
    exact_mod_cast hf
  · have hx : #X = 1 := by have hp := hne.card_pos; omega
    obtain ⟨v, rfl⟩ := card_eq_one.mp hx
    simp only [card_singleton, Nat.cast_one, mul_one]
    have hzero : ec G {v} {v} = 0 := by simp [ec, dg]
    rw [hzero]
    norm_num only [Nat.cast_zero, sub_zero]
    have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
    linarith

theorem critical_extraction {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 6 ≤ q) (heven : Even q) (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + q / 2) :
    ∃ U : Finset V, ∃ K : SimpleGraph (U : Set V),
      2 ≤ Fintype.card (U : Set V) ∧ K ≤ G.induce (U : Set V) ∧
      K.maxDegree ≤ 2 * q - 2 ∧
      K.edgeSet.ncard + q / 2 = (q - 1) * Fintype.card (U : Set V) ∧
      ∀ X : Finset (U : Set V), X.Nonempty → X ≠ univ →
        (q : ℤ) + 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec K X X : ℤ) := by
  obtain ⟨U, hU, hminimal⟩ := minimal_dense_support q heven G hn he
  have horder : Fintype.card (U : Set V) = #U := by simp
  have hnU : 2 ≤ Fintype.card (U : Set V) := by rw [horder]; exact hU.1
  have hhalf := even_half q heven
  have heU : (q - 1) * Fintype.card (U : Set V) ≤
      (G.induce (U : Set V)).edgeSet.ncard + q / 2 := by
    have hd := hU.2
    rw [ec_self_eq_twice_induced_edges] at hd
    rw [horder]
    nlinarith
  have hm : (q - 1) * Fintype.card (U : Set V) - q / 2 ≤
      (G.induce (U : Set V)).edgeSet.ncard :=
    (threshold_add hq hnU).mpr heU
  obtain ⟨K, hsub, hcard⟩ := original_edge_thinning (G.induce (U : Set V)) _ hm
  have hcapK := thinned_cap K (G.induce (U : Set V)) (2 * q - 2) hsub
    (induced_cap G U (2 * q - 2) hcap)
  refine ⟨U, K, hnU, hsub, hcapK, ?_, ?_⟩
  · rw [hcard]
    have hb : q / 2 ≤ (q - 1) * Fintype.card (U : Set V) := by
      have hh : q / 2 ≤ q - 1 := by omega
      have hmul := Nat.mul_le_mul_left (q - 1) (by omega : 1 ≤ Fintype.card (U : Set V))
      have hmul' : q - 1 ≤ (q - 1) * Fintype.card (U : Set V) := by
        simpa only [mul_one] using hmul
      exact hh.trans hmul'
    omega
  · intro X hne hproper
    let Y : Finset V := X.image (fun v : (U : Set V) => (v : V))
    have hYcard : #Y = #X := card_image_of_injective X Subtype.val_injective
    have hYsub : Y ⊆ U := by
      intro v hv
      obtain ⟨w, _, rfl⟩ := mem_image.mp hv
      exact w.property
    have hYproper : Y ⊂ U := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hYsub, ?_⟩
      intro hYU
      have hcardX : #X = #(univ : Finset (U : Set V)) := by
        rw [← hYcard, hYU, card_univ, horder]
      exact hproper (eq_of_subset_of_card_le (subset_univ X) (by omega))
    have hf := minimal_original_floor q hq heven G U hminimal Y (hne.image _) hYproper
    let f : G.induce (U : Set V) ↪g G := SimpleGraph.Embedding.induce (G := G) (U : Set V)
    have hcount : ec G Y Y = ec (G.induce (U : Set V)) X X :=
      ec_embedding_image (G.induce (U : Set V)) G f X X
    have hmono := ec_mono_original K (G.induce (U : Set V)) hsub X X
    rw [hYcard, hcount] at hf
    exact le_trans hf (by exact sub_le_sub_left (by exact_mod_cast hmono) _)

theorem extraction_preserves_avoidance {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (U : Finset V) (K : SimpleGraph (U : Set V))
    (hsub : K ≤ G.induce (U : Set V))
    (havoid : ¬∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ¬∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  intro h
  exact havoid (original_thinned_induced_regular_transport G U K hsub h)

#print axioms DenseOn
#print axioms minimal_dense_support
#print axioms minimal_original_floor
#print axioms critical_extraction
#print axioms extraction_preserves_avoidance
end Erdos585.NEQAssembly
