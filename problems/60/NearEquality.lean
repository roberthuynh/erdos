import PolarityTransfer
import PolarityAbsoluteBound
import PolarityExactCount
import PolarityNucleus
import MatchingEquality
import OneAddedCycles
import PolarityMatchingCount

namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [DecidableEq P]
  [Configuration.ProjectivePlane P L] [Finite L]

/-- Actual polarity equality transfer with its geometric path supplier proved. -/
theorem Polarity.graph_transfer_equality
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (M t δ : ℕ)
    (ht : 1 ≤ t) (hG : G.edgeFinset.card = M + t)
    (hQ : π.graph.edgeFinset.card + δ = M)
    (hsmall : (G.edgeFinset \ π.graph.edgeFinset).card <
      Configuration.ProjectivePlane.order P L - 1)
    (heq : Counting.cycleCount G = t * (Configuration.ProjectivePlane.order P L - 1)) :
    (G.edgeFinset \ π.graph.edgeFinset).card = t ∧ δ = 0 ∧
      (π.graph.edgeFinset \ G.edgeFinset).card = 0 := by
  classical
  let A := G.edgeFinset \ π.graph.edgeFinset
  have hex : ∀ e : Sym2 P, ∃ paths : Finset (Finset (Sym2 P)), e ∈ A →
      (∀ p ∈ paths, Counting.IsThreePath e p ∧ p ⊆ π.graph.edgeFinset) ∧
      (∀ p ∈ paths, ∀ r ∈ paths, p ≠ r → Disjoint p r) ∧
      Configuration.ProjectivePlane.order P L - 1 ≤ paths.card := by
    intro e
    by_cases he : e ∈ A
    · obtain ⟨paths,hp⟩ := π.counting_family_for_added_edge G e he
      exact ⟨paths,fun _ => hp⟩
    · exact ⟨∅,fun h => False.elim (he h)⟩
  choose paths hp using hex
  apply Transfer.graph_transfer_equality G π.graph M (Configuration.ProjectivePlane.order P L)
    t δ ht hG hQ hsmall paths
  · intro e he p hp'
    exact (hp e he).1 p hp'
  · intro e he p hp' r hr hne
    exact (hp e he).2.1 p hp' r hr hne
  · intro e he
    exact (hp e he).2.2
  · exact heq

/-- The first necessary equality conclusions for an actual nearby polarity.
Even-order edge deficit is discharged rather than assumed. The edit-radius
producer remains a premise and is not asserted here. -/
theorem Polarity.near_equality_edits
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (t : ℕ)
    (heven : Even (Configuration.ProjectivePlane.order P L)) (ht : 1 ≤ t)
    (hG : G.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 / 2 + t)
    (hsmall : (G.edgeFinset \ π.graph.edgeFinset).card <
      Configuration.ProjectivePlane.order P L - 1)
    (heq : Counting.cycleCount G = t * (Configuration.ProjectivePlane.order P L - 1)) :
    (G.edgeFinset \ π.graph.edgeFinset).card = t ∧
    π.graph.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 / 2 ∧ π.graph ≤ G := by
  classical
  let M := Configuration.ProjectivePlane.order P L *
    (Configuration.ProjectivePlane.order P L + 1)^2 / 2
  let δ := M - π.graph.edgeFinset.card
  have hub : π.graph.edgeFinset.card ≤ M := π.edge_count_upper heven
  have hQ : π.graph.edgeFinset.card + δ = M := by dsimp [δ]; omega
  obtain ⟨hj,hδ,hd⟩ := π.graph_transfer_equality G M t δ ht hG hQ hsmall heq
  refine ⟨hj,by omega,?_⟩
  have hs : π.graph.edgeFinset ⊆ G.edgeFinset :=
    Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hd)
  intro a b hab
  have he : s(a,b) ∈ π.graph.edgeFinset := by simpa using hab
  simpa using hs he

/-- Equality forces every actual added edge's complete base-path family to
attain its minimum. This uses a variable path-count sum, not a uniform-count
assumption or the matching converse. -/
theorem Polarity.base_path_count_min_of_equality
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (t : ℕ)
    (hQG : π.graph ≤ G)
    (hj : (G.edgeFinset \ π.graph.edgeFinset).card = t)
    (heq : Counting.cycleCount G = t * (Configuration.ProjectivePlane.order P L - 1))
    (e : Sym2 P) (he : e ∈ G.edgeFinset \ π.graph.edgeFinset) :
    (Counting.baseThreePaths π.graph e).card = Configuration.ProjectivePlane.order P L - 1 := by
  classical
  let A := G.edgeFinset \ π.graph.edgeFinset
  let k := Configuration.ProjectivePlane.order P L - 1
  have hnum : ∀ f ∈ A, k ≤ (Counting.baseThreePaths π.graph f).card := by
    intro f hf
    obtain ⟨paths,hpath,_,hn⟩ := π.counting_family_for_added_edge G f hf
    have hsub : paths ⊆ Counting.baseThreePaths π.graph f := by
      intro p hp
      exact (Counting.mem_baseThreePaths _ _ _).mpr (hpath p hp)
    exact hn.trans (Finset.card_le_card hsub)
  obtain ⟨F,hF,_,hFc⟩ := Counting.one_added_cycle_family G π.graph hQG
  have hle : (∑ f ∈ A, (Counting.baseThreePaths π.graph f).card) ≤ t * k := by
    rw [← hFc, ← heq]
    exact Finset.card_le_card hF
  have hl := Finset.sum_le_sum hnum
  have hc : (∑ _f ∈ A, k) = t * k := by simp [A,hj]
  have hsum : (∑ _f ∈ A, k) = ∑ f ∈ A, (Counting.baseThreePaths π.graph f).card := by omega
  exact ((Finset.sum_eq_sum_iff_of_le hnum).mp hsum e he).symm

theorem Polarity.added_endpoints_absolute_of_equality
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (t : ℕ)
    (hQG : π.graph ≤ G)
    (hj : (G.edgeFinset \ π.graph.edgeFinset).card = t)
    (heq : Counting.cycleCount G = t * (Configuration.ProjectivePlane.order P L - 1))
    {a b : P} (hab : G.Adj a b) (hn : ¬π.graph.Adj a b) :
    π.Absolute a ∧ π.Absolute b := by
  have he : s(a,b) ∈ G.edgeFinset \ π.graph.edgeFinset := by
    apply Finset.mem_sdiff.mpr
    constructor <;> simpa using (by assumption)
  have hc := π.base_path_count_min_of_equality G t hQG hj heq s(a,b) he
  rw [π.baseThreePaths_card hab.ne hn] at hc
  exact π.absolute_of_three_path_count_min hab.ne hn hc

theorem Polarity.added_matching_of_equality
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (t : ℕ)
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hcard : Nat.card {a : P // π.Absolute a} = Configuration.ProjectivePlane.order P L + 1)
    (hQG : π.graph ≤ G)
    (hj : (G.edgeFinset \ π.graph.edgeFinset).card = t)
    (heq : Counting.cycleCount G = t * (Configuration.ProjectivePlane.order P L - 1)) :
    Counting.IsMatchingGraph (G \ π.graph) := by
  classical
  obtain ⟨w,hnabs,hw⟩ := π.nucleus_of_even_absolute_card heven hcard
  obtain ⟨F,hF,hOne,hFc⟩ := Counting.one_added_cycle_family G π.graph hQG
  have hFexact : F.card = t * (Configuration.ProjectivePlane.order P L - 1) := by
    rw [hFc]
    calc
      (∑ e ∈ G.edgeFinset \ π.graph.edgeFinset,
        (Counting.baseThreePaths π.graph e).card) =
          ∑ _e ∈ G.edgeFinset \ π.graph.edgeFinset,
            (Configuration.ProjectivePlane.order P L - 1) := by
        apply Finset.sum_congr rfl
        intro e he
        exact π.base_path_count_min_of_equality G t hQG hj heq e he
      _ = _ := by simp [hj]
  intro a b c hab hac
  change (G.Adj a b ∧ ¬π.graph.Adj a b) at hab
  change (G.Adj a c ∧ ¬π.graph.Adj a c) at hac
  by_contra hbc
  obtain ⟨ha,hb⟩ := π.added_endpoints_absolute_of_equality G t hQG hj heq hab.1 hab.2
  have hc := (π.added_endpoints_absolute_of_equality G t hQG hj heq hac.1 hac.2).2
  have haw : a ≠ w := by intro h; apply hnabs; rw [← h]; exact ha
  have hbw : b ≠ w := by intro h; apply hnabs; rw [← h]; exact hb
  have hcw : c ≠ w := by intro h; apply hnabs; rw [← h]; exact hc
  have hba := hab.1.ne.symm
  have hacne := hac.1.ne
  have hd : [b,a,c,w].Nodup := by simp [hba,hbc,hbw,hacne,haw,hcw]
  have habG : s(a,b) ∈ G.edgeFinset := by simpa using hab.1
  have hacG : s(a,c) ∈ G.edgeFinset := by simpa using hac.1
  have hcwG : s(c,w) ∈ G.edgeFinset := by simpa using hQG (hw c hc).symm
  have hwbG : s(w,b) ∈ G.edgeFinset := by simpa using hQG (hw b hb)
  have habQ : s(a,b) ∉ π.graph.edgeFinset := by simpa using hab.2
  have hacQ : s(a,c) ∉ π.graph.edgeFinset := by simpa using hac.2
  have hstrict := Counting.shared_added_edges_strict_count G π.graph F hF hOne
    a b c w hd habG hacG hcwG hwbG habQ hacQ
  omega

/-- Full forward equality classification relative to an actual nearby polarity.
The actual short-radius polarity producer remains a separate obligation. -/
theorem Polarity.near_equality_necessity
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (t : ℕ)
    (heven : Even (Configuration.ProjectivePlane.order P L)) (ht : 1 ≤ t)
    (hG : G.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 / 2 + t)
    (hsmall : (G.edgeFinset \ π.graph.edgeFinset).card <
      Configuration.ProjectivePlane.order P L - 1)
    (heq : Counting.cycleCount G = t * (Configuration.ProjectivePlane.order P L - 1)) :
    (G.edgeFinset \ π.graph.edgeFinset).card = t ∧
    π.graph.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 / 2 ∧
    π.graph ≤ G ∧
    (∀ a b, (G \ π.graph).Adj a b → π.Absolute a ∧ π.Absolute b) ∧
    Counting.IsMatchingGraph (G \ π.graph) := by
  obtain ⟨hj,hM,hQG⟩ := π.near_equality_edits G t heven ht hG hsmall heq
  have hcard := (π.edge_count_eq_iff_absolute_count heven).mp hM
  refine ⟨hj,hM,hQG,?_,π.added_matching_of_equality G t heven hcard hQG hj heq⟩
  intro a b hab
  change (G.Adj a b ∧ ¬π.graph.Adj a b) at hab
  exact π.added_endpoints_absolute_of_equality G t hQG hj heq hab.1 hab.2

#print axioms Polarity.graph_transfer_equality
#print axioms Polarity.near_equality_edits
#print axioms Polarity.base_path_count_min_of_equality
#print axioms Polarity.added_endpoints_absolute_of_equality
#print axioms Polarity.added_matching_of_equality
#print axioms Polarity.near_equality_necessity
end Erdos60.Geometry
