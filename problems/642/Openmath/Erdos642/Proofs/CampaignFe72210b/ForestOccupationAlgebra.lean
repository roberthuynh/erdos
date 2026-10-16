import Openmath.Erdos642.Proofs.CampaignFe72210b.OccupationAlgebra

/-! Literal leaf unions, completed-history good roots, and deterministic visit-weight bounds. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov Erdos642.OccupationTail Erdos642.OccupationAlgebra
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : Erdos642.CampaignFe72210b.ForestBundle G A B q m b)

def leafUnion (f : Fin q) (J : Finset (Fin m)) : Finset V :=
  J.biUnion (fun j => F.leaves (f, j))

omit [Fintype V] in
 theorem leafUnion_subset (f : Fin q) (J : Finset (Fin m)) : F.leafUnion f J ⊆ B := by
  intro v hv
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
  exact F.leaves_subset (f, j) hj

omit [Fintype V] in
 theorem leafUnion_card (f : Fin q) (J : Finset (Fin m)) :
    (F.leafUnion f J).card = J.card * b := by
  have hdis : (J : Set (Fin m)).PairwiseDisjoint (fun j => F.leaves (f, j)) := by
    intro j _ k _ hne
    exact F.leaves_disjoint f j k hne
  rw [leafUnion, Finset.card_biUnion hdis]
  simp [F.leaves_card]

 theorem leafUnion_occupation (f : Fin q) (J : Finset (Fin m))
    {n : ℕ} (x : V) (p : Path V n) :
    occupation (F.leafUnion f J) x p = ∑ j ∈ J, occupation (F.leaves (f, j)) x p := by
  have hdis : (J : Set (Fin m)).PairwiseDisjoint (fun j => F.leaves (f, j)) := by
    intro j _ k _ hne
    exact F.leaves_disjoint f j k hne
  rw [occupation_eq_sum_singletons, leafUnion, Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro j _
  exact (occupation_eq_sum_singletons (F.leaves (f, j)) x p).symm

noncomputable def goodInForest (f : Fin q) (a : ℝ) {n : ℕ} (x : V) (p : Path V n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => a ≤ occupation (F.leaves (f, j)) x p)

noncomputable def goodStars (a : ℝ) {n : ℕ} (x : V) (p : Path V n) : Finset (Fin q × Fin m) := by
  classical
  exact Finset.univ.filter (fun i => a ≤ occupation (F.leaves i) x p)

omit [Fintype V] in
@[simp] theorem mem_goodInForest (f : Fin q) (a : ℝ) {n : ℕ} (x : V) (p : Path V n) (j : Fin m) :
    j ∈ F.goodInForest f a x p ↔ a ≤ occupation (F.leaves (f, j)) x p := by
  classical
  simp [goodInForest]

omit [Fintype V] in
@[simp] theorem mem_goodStars (a : ℝ) {n : ℕ} (x : V) (p : Path V n) (i : Fin q × Fin m) :
    i ∈ F.goodStars a x p ↔ a ≤ occupation (F.leaves i) x p := by
  classical
  simp [goodStars]

omit [Fintype V] in
 theorem goodStars_card (a : ℝ) {n : ℕ} (x : V) (p : Path V n) :
    (F.goodStars a x p).card = ∑ f : Fin q, (F.goodInForest f a x p).card := by
  classical
  simp only [goodStars, goodInForest, Finset.card_filter]
  rw [Fintype.sum_prod_type]

noncomputable def goodRootSet (a : ℝ) {n : ℕ} (x : V) (p : Path V n) : Finset V :=
  F.roots (F.goodStars a x p)

omit [Fintype V] in
 theorem goodRootSet_subset (a : ℝ) {n : ℕ} (x : V) (p : Path V n) :
    F.goodRootSet a x p ⊆ A := F.roots_subset _

omit [Fintype V] in
 theorem goodRootSet_card (a : ℝ) {n : ℕ} (x : V) (p : Path V n) :
    (F.goodRootSet a x p).card = ∑ f : Fin q, (F.goodInForest f a x p).card := by
  rw [goodRootSet, F.roots_card, F.goodStars_card]

 theorem goodRootSet_occupation (a : ℝ) {n k : ℕ}
    (x : V) (p : Path V n) (y : V) (r : Path V k) :
    occupation (F.goodRootSet a x p) y r =
      ∑ i ∈ F.goodStars a x p, occupation {F.root i} y r := by
  rw [occupation_eq_sum_singletons, goodRootSet, F.sum_roots]

/-- The weighted count uses actual vertex multiplicities in both observed paths. -/
noncomputable def occupationWeightedCount {n k : ℕ}
    (x : V) (p : Path V n) (y : V) (r : Path V k) : ℝ :=
  F.weightedCount (fun v => occupation {v} x p) (fun v => occupation {v} y r)

 theorem occupationWeightedCount_good_lower (a : ℝ) {n k : ℕ}
    (x : V) (p : Path V n) (y : V) (r : Path V k) :
    a * occupation (F.goodRootSet a x p) y r ≤ F.occupationWeightedCount x p y r := by
  have hnonneg {j : ℕ} (v z : V) (w : Path V j) : 0 ≤ occupation {v} z w := by
    rw [occupation_singleton_eq_count]
    positivity
  have hh := F.weightedCount_lower (fun v => occupation {v} x p)
    (fun v => occupation {v} y r) (fun v => hnonneg v x p) (fun v => hnonneg v y r)
    a (F.goodStars a x p) (by
      intro i hi
      rw [← occupation_eq_sum_singletons]
      exact (F.mem_goodStars a x p i).mp hi)
  change a * occupation (F.roots (F.goodStars a x p)) y r ≤
    F.weightedCount (fun v => occupation {v} x p) (fun v => occupation {v} y r)
  rw [occupation_eq_sum_singletons (F.roots (F.goodStars a x p)) y r]
  exact hh

/-- A nonempty collection of individually bad stars has strictly low union occupation. -/
theorem bad_leafUnion_occupation_lt (f : Fin q) (J : Finset (Fin m)) (hJ : J.Nonempty)
    (a : ℝ) {n : ℕ} (x : V) (p : Path V n)
    (hbad : ∀ j ∈ J, occupation (F.leaves (f, j)) x p < a) :
    occupation (F.leafUnion f J) x p < (J.card : ℝ) * a := by
  rw [F.leafUnion_occupation]
  calc
    _ < ∑ _j ∈ J, a := Finset.sum_lt_sum_of_nonempty hJ hbad
    _ = _ := by simp

end Erdos642.CampaignFe72210b.ForestBundle
