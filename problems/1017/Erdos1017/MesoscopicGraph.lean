import Erdos1017.MesoscopicDual
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos1017.Mesoscopic
open scoped BigOperators

abbrev Vertex (a b s : ℕ) := (Fin a ⊕ Fin b) ⊕ (Fin s ⊕ Fin 2)

def color {a b s : ℕ} : Vertex a b s → Fin 4
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => 3

def allowed {a b s : ℕ} (T : Finset (Fin 2 × Fin b)) : Vertex a b s → Vertex a b s → Prop
  | .inr (.inr d), .inl (.inr j) => (d,j) ∈ T
  | .inl (.inr j), .inr (.inr d) => (d,j) ∈ T
  | _, _ => True

instance {a b s : ℕ} (T : Finset (Fin 2 × Fin b)) : DecidableRel (@allowed a b s T) :=
  fun u v => by rcases u with (i|i)|(i|i) <;> rcases v with (j|j)|(j|j) <;>
    simp only [allowed] <;> infer_instance

theorem allowed_symm {a b s : ℕ} (T : Finset (Fin 2 × Fin b)) (u v : Vertex a b s) :
    allowed T u v ↔ allowed T v u := by
  rcases u with (i|i)|(i|i) <;> rcases v with (j|j)|(j|j) <;> rfl

def graph (a b s : ℕ) (T : Finset (Fin 2 × Fin b)) : SimpleGraph (Vertex a b s) where
  Adj u v := u ≠ v ∧ (color u ≠ color v ∨ color u = 2) ∧ allowed T u v
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_, (allowed_symm T u v).mp h.2.2⟩
    by_cases he : color u = color v
    · right; rcases h.2.1 with hn|hc
      · exact (hn he).elim
      · exact he ▸ hc
    · exact Or.inl (Ne.symm he)⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (a b s : ℕ) (T : Finset (Fin 2 × Fin b)) : DecidableRel (graph a b s T).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∨ _) ∧ _))

noncomputable def coefficient : Fin 4 → Fin 4 → ℝ :=
  ![![0,1,2/3,1], ![1,0,-2/3,-1], ![2/3,-2/3,-1/3,-2/3], ![1,-1,-2/3,0]]

noncomputable def weight {a b s : ℕ} (u v : Vertex a b s) : ℝ :=
  if u=v then 0 else coefficient (color u) (color v)

def colorCount {V : Type*} [DecidableEq V] (p : V → Fin 4) (S : Finset V) (i : Fin 4) : ℕ :=
  (S.filter (fun u => p u=i)).card

theorem count_independent {a b s : ℕ} (T : Finset (Fin 2 × Fin b))
    (S : Finset (Vertex a b s)) (hS : (graph a b s T).IsClique (S : Set _))
    (i : Fin 4) (hi : i ≠ 2) : colorCount color S i ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huS, hui⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS, hvi⟩ := Finset.mem_filter.mp hv
  by_contra hne
  have h := (hS huS hvS hne).2.1
  rcases h with h|h
  · exact h (hui.trans hvi.symm)
  · exact hi (hui.symm.trans h)

theorem grouped_sum {V : Type*} [DecidableEq V] (p : V → Fin 4)
    (S : Finset V) (f : Fin 4 → ℝ) :
    (∑ u ∈ S, f (p u)) = ∑ i : Fin 4, (colorCount p S i : ℝ)*f i := by
  rw [← Finset.sum_fiberwise' S p f]
  simp only [Finset.sum_const, nsmul_eq_mul, colorCount]

theorem grouped_pairs {V : Type*} [DecidableEq V] (p : V → Fin 4)
    (S : Finset V) (f : Fin 4 → Fin 4 → ℝ) :
    (∑ u ∈ S, ∑ v ∈ S, f (p u) (p v)) =
      ∑ i : Fin 4, ∑ j : Fin 4, (colorCount p S i : ℝ)*(colorCount p S j : ℝ)*f i j := by
  simp_rw [grouped_sum p S]
  rw [grouped_sum p S (fun i => ∑ j : Fin 4, (colorCount p S j : ℝ)*f i j)]
  simp only [Finset.mul_sum, mul_assoc]

theorem weight_cell {a b s : ℕ} (S : Finset (Vertex a b s)) :
    cell weight S =
      (colorCount color S 0 : ℝ)*colorCount color S 1 +
      (2:ℝ)/3*colorCount color S 0*colorCount color S 2 -
      (2:ℝ)/3*colorCount color S 1*colorCount color S 2 -
      (1:ℝ)/6*colorCount color S 2*(colorCount color S 2-1) +
      (colorCount color S 3 : ℝ)*colorCount color S 0 -
      (colorCount color S 3 : ℝ)*colorCount color S 1 -
      (2:ℝ)/3*colorCount color S 3*colorCount color S 2 := by
  have he (u v : Vertex a b s) : weight u v =
      coefficient (color u) (color v) - if u=v then coefficient (color u) (color u) else 0 := by
    by_cases h : u=v
    · subst v; simp [weight]
    · simp [weight,h]
  have hd : (∑ u ∈ S, ∑ v ∈ S, if u=v then coefficient (color u) (color u) else 0) =
      ∑ u ∈ S, coefficient (color u) (color u) := by
    apply Finset.sum_congr rfl
    intro u hu
    simp [hu]
  unfold cell
  simp_rw [he, Finset.sum_sub_distrib]
  rw [hd, grouped_pairs color S coefficient, grouped_sum color S (fun i => coefficient i i)]
  simp only [Fin.sum_univ_succ, coefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero]
  norm_num [show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  ring

theorem graph_lower (a b s : ℕ) (T : Finset (Fin 2 × Fin b))
    (P : FractionalPartition (graph a b s T)) :
    total (graph a b s T) weight ≤ P.cost := by
  apply signed_lower _ _ (fun u => by simp [weight]) _ P
  intro S hS
  rw [weight_cell]
  exact four_part_cell _ _ _ _
    (count_independent T S hS 0 (by decide))
    (count_independent T S hS 1 (by decide))
    (count_independent T S hS 3 (by decide))

end Erdos1017.Mesoscopic
