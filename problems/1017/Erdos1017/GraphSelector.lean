import Erdos1017.CategoricalSelector
import Erdos1017.CliqueLaw
import Mathlib.Tactic.FieldSimp

/-! An actual finite-graph partition from independent choices in vertex parts. -/
namespace Erdos1017
open scoped BigOperators
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

noncomputable def partSize (part : V → ι) (i : ι) : ℕ :=
  (Finset.univ.filter (fun v => part v = i)).card

noncomputable def vertexChoiceProb (a : ℝ) (part : V → ι) (i : ι) : Option V → ℝ
  | none => 1 - partSize part i / a
  | some v => if part v = i then 1/a else 0

noncomputable def chosenVertices (part : V → ι) (x : ι → Option V) : Finset V :=
  Finset.univ.filter (fun v => x (part v) = some v)

omit [DecidableEq V] [Fintype ι] in
theorem vertexChoice_total (a : ℝ) (part : V → ι) (i : ι) :
    ∑ y : Option V, vertexChoiceProb a part i y = 1 := by
  simp [Fintype.sum_option, vertexChoiceProb, Finset.sum_ite, partSize, div_eq_mul_inv]

omit [DecidableEq V] [Fintype ι] in
theorem vertexChoice_nonneg {a : ℝ} (ha : 0 < a) (part : V → ι)
    (hmax : ∀ i, (partSize part i : ℝ) ≤ a) (i : ι) (y : Option V) :
    0 ≤ vertexChoiceProb a part i y := by
  cases y with
  | none => exact sub_nonneg.mpr ((div_le_one ha).mpr (hmax i))
  | some v =>
    dsimp [vertexChoiceProb]
    split_ifs
    · exact div_nonneg (by norm_num) ha.le
    · exact le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem chosenVertices_clique (G : SimpleGraph V) (part : V → ι)
    (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v) (x : ι → Option V) :
    G.IsClique (chosenVertices part x : Set V) := by
  intro u hu v hv huv
  apply (hG u v).mpr
  intro hp
  have hxu : x (part u) = some u := by simpa [chosenVertices] using hu
  have hxv : x (part v) = some v := by simpa [chosenVertices] using hv
  rw [hp] at hxu
  exact huv (Option.some.inj (hxu.symm.trans hxv))

theorem vertexChoice_edge_load {a : ℝ} (ha : a ≠ 0)
    (G : SimpleGraph V) (part : V → ι)
    (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v) (u v : V) (huv : G.Adj u v) :
    (∑ x : ι → Option V, if u ∈ chosenVertices part x ∧ v ∈ chosenVertices part x
      then a^2 * categoricalMass (vertexChoiceProb a part) x else 0) = 1 := by
  have hp := categorical_pair (vertexChoiceProb a part) (vertexChoice_total a part)
    (part u) (part v) ((hG u v).mp huv) (some u) (some v)
  calc
    _ = a^2 * ∑ x : ι → Option V, categoricalMass (vertexChoiceProb a part) x *
        ((if x (part u) = some u then 1 else 0) *
         (if x (part v) = some v then 1 else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hu : x (part u) = some u <;> by_cases hv : x (part v) = some v <;>
        simp [chosenVertices, hu, hv]
    _ = 1 := by rw [hp]; simp [vertexChoiceProb]; field_simp

/-- Every complete multipartite graph with each part of size at most `a` has a
fractional clique partition of cost at most `a²`. This is an actual graph witness. -/
theorem multipartite_partition_le_square {a : ℝ} (ha : 0 < a)
    (G : SimpleGraph V) (part : V → ι)
    (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (hmax : ∀ i, (partSize part i : ℝ) ≤ a) :
    ∃ P : FractionalPartition G, P.cost ≤ a^2 := by
  let w : (ι → Option V) → ℝ := fun x => a^2 * categoricalMass (vertexChoiceProb a part) x
  have hw (x : ι → Option V) : 0 ≤ w x := by
    apply mul_nonneg (sq_nonneg a)
    exact Finset.prod_nonneg (fun i _ => vertexChoice_nonneg ha part hmax i (x i))
  let P := partitionOfCliqueLawPruned G (chosenVertices part) w hw
    (chosenVertices_clique G part hG) (vertexChoice_edge_load (ne_of_gt ha) G part hG)
  refine ⟨P, ?_⟩
  change (partitionOfCliqueLawPruned G (chosenVertices part) w hw _ _).cost ≤ a^2
  rw [partitionOfCliqueLawPruned_cost]
  calc
    _ ≤ ∑ x, w x := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs
      · exact le_rfl
      · exact hw x
    _ = a^2 := by
      simp only [w, ← Finset.mul_sum]
      rw [categorical_total _ (vertexChoice_total a part), mul_one]

end Erdos1017
