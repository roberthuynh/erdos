import Erdos1017.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Erdos1017
open scoped BigOperators

/-- The join of an independent a-set and a complete s-set. -/
def splitGraph (a s : ℕ) : SimpleGraph (Fin a ⊕ Fin s) where
  Adj u v := u ≠ v ∧ (u.isRight ∨ v.isRight)
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (a s : ℕ) : DecidableRel (splitGraph a s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∨ _)))

@[simp] theorem splitGraph_inl_inr (a s : ℕ) (i : Fin a) (j : Fin s) :
    (splitGraph a s).Adj (.inl i) (.inr j) := by simp [splitGraph]

@[simp] theorem splitGraph_inr_inr (a s : ℕ) (i j : Fin s) :
    (splitGraph a s).Adj (.inr i) (.inr j) ↔ i ≠ j := by simp [splitGraph]

 theorem split_clique_left_card {a s : ℕ} (S : Finset (Fin a ⊕ Fin s))
    (hS : (splitGraph a s).IsClique (S : Set (Fin a ⊕ Fin s))) : S.toLeft.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have h := hS (by simpa using hi) (by simpa using hj) (by simpa using hij)
  simp [splitGraph] at h

 theorem split_cross_cell {a s : ℕ} (S : Finset (Fin a ⊕ Fin s)) (m : ℝ) :
    (∑ i : Fin a, ∑ j : Fin s, if Sum.inl i ∈ S ∧ Sum.inr j ∈ S then m else 0) =
      m * S.toLeft.card * S.toRight.card := by
  have hl : (∑ i : Fin a, if Sum.inl i ∈ S then (1 : ℝ) else 0) = S.toLeft.card := by
    have h : Finset.univ.filter (fun i => Sum.inl i ∈ S) = S.toLeft := by ext; simp
    simp only [Finset.sum_boole, h]
  have hr : (∑ j : Fin s, if Sum.inr j ∈ S then (1 : ℝ) else 0) = S.toRight.card := by
    have h : Finset.univ.filter (fun j => Sum.inr j ∈ S) = S.toRight := by ext; simp
    simp only [Finset.sum_boole, h]
  have hi (i : Fin a) (j : Fin s) :
      (if Sum.inl i ∈ S ∧ Sum.inr j ∈ S then m else 0) =
      m * (if Sum.inl i ∈ S then 1 else 0) * (if Sum.inr j ∈ S then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hi, ← Finset.mul_sum]
  rw [hr, ← Finset.sum_mul, ← Finset.mul_sum, hl]

 theorem split_cross_load {a s : ℕ} (P : FractionalPartition (splitGraph a s)) :
    (∑ S, P.mass S * S.toLeft.card * S.toRight.card) = (a : ℝ)*s := by
  simp_rw [← split_cross_cell]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin a ⊕ Fin s))))]
  simp_rw [P.edge_load _ _ (splitGraph_inl_inr a s _ _)]
  simp

 theorem split_right_cell {a s : ℕ} (S : Finset (Fin a ⊕ Fin s)) (m : ℝ) :
    (∑ i : Fin s, ∑ j : Fin s,
      if i ≠ j ∧ Sum.inr i ∈ S ∧ Sum.inr j ∈ S then m else 0) =
      m * (S.toRight.card : ℝ) * (S.toRight.card - 1) := by
  have hi (i j : Fin s) :
      (if i ≠ j ∧ Sum.inr i ∈ S ∧ Sum.inr j ∈ S then m else 0) =
      (if Sum.inr i ∈ S ∧ Sum.inr j ∈ S then m else 0) -
      (if i = j ∧ Sum.inr i ∈ S then m else 0) := by
    by_cases hij : i=j
    · subst j; simp
    · simp [hij]
  simp_rw [hi, Finset.sum_sub_distrib]
  have hpair : (∑ i : Fin s, ∑ j : Fin s, if Sum.inr i ∈ S ∧ Sum.inr j ∈ S then m else 0) =
      m * (S.toRight.card : ℝ)^2 := by
    have hid (i j : Fin s) : (if Sum.inr i ∈ S ∧ Sum.inr j ∈ S then m else 0) =
        m * (if i ∈ S.toRight then 1 else 0) * (if j ∈ S.toRight then 1 else 0) := by
      simp only [Finset.mem_toRight]
      split_ifs <;> simp_all
    have hr : (∑ j : Fin s, if j ∈ S.toRight then (1 : ℝ) else 0) = S.toRight.card := by
      have hf : Finset.univ.filter (fun j => j ∈ S.toRight) = S.toRight := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.sum_boole, hf]
    simp_rw [hid, ← Finset.mul_sum]
    rw [hr, ← Finset.sum_mul, ← Finset.mul_sum, hr]
    ring
  have hdiag : (∑ i : Fin s, ∑ j : Fin s, if i = j ∧ Sum.inr i ∈ S then m else 0) =
      m * S.toRight.card := by
    have hid (i j : Fin s) : (if i = j ∧ Sum.inr i ∈ S then m else 0) =
        if i = j then (if i ∈ S.toRight then m else 0) else 0 := by
      simp only [Finset.mem_toRight]
      split_ifs <;> simp_all
    simp_rw [hid]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun i => i ∈ S.toRight) = S.toRight := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hf]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hpair,hdiag]
  ring

 theorem split_right_load {a s : ℕ} (P : FractionalPartition (splitGraph a s)) :
    (∑ S, P.mass S * (S.toRight.card : ℝ) * (S.toRight.card - 1)) = (s : ℝ)*(s-1) := by
  simp_rw [← split_right_cell]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin a ⊕ Fin s))))]
  have hi (i j : Fin s) : (∑ S, if i ≠ j ∧ Sum.inr i ∈ S ∧ Sum.inr j ∈ S then P.mass S else 0) =
      if i ≠ j then (1 : ℝ) else 0 := by
    by_cases hij : i=j
    · simp [hij]
    · simpa only [hij, ne_eq, not_false_eq_true, true_and, if_true] using
        P.edge_load (.inr i) (.inr j) (by simpa using hij)
  simp_rw [hi]
  by_cases hs : s=0
  · subst s; simp
  · have hs1 : 1 ≤ s := by omega
    have row (i : Fin s) : (∑ j : Fin s, if i ≠ j then (1 : ℝ) else 0) = (s:ℝ)-1 := by
      have he (j : Fin s) : (if i ≠ j then (1:ℝ) else 0) = 1-(if i=j then 1 else 0) := by
        by_cases hij : i=j <;> simp [hij]
      simp_rw [he]
      simp
    simp_rw [row]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

 theorem split_dual_cell (l r : ℕ) (hl : l ≤ 1) :
    (2:ℝ)/3*l*r - (1:ℝ)/6*r*(r-1) ≤ 1 := by
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hl1 : (l:ℝ) ≤ 1 := by exact_mod_cast hl
  have hmul : (l:ℝ)*r ≤ r := by nlinarith
  have hp : (0:ℝ) ≤ ((r:ℝ)-2)*((r:ℝ)-3) := by
    by_cases hr : r ≤ 2
    · have hrr : (r:ℝ) ≤ 2 := by exact_mod_cast hr
      nlinarith
    · have hrr : (3:ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
      exact mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- A dual lower bound for every exact fractional partition, with negative
clique-side edge weights. It requires no assumption on the a:s ratio. -/
theorem split_partition_lower {a s : ℕ} (P : FractionalPartition (splitGraph a s)) :
    (2:ℝ)/3*a*s - (1:ℝ)/6*s*(s-1) ≤ P.cost := by
  have hcell (S : Finset (Fin a ⊕ Fin s)) :
      P.mass S * ((2:ℝ)/3*S.toLeft.card*S.toRight.card -
      (1:ℝ)/6*S.toRight.card*(S.toRight.card-1)) ≤ P.mass S := by
    by_cases hz : P.mass S=0
    · simp [hz]
    · exact mul_le_of_le_one_right (P.nonneg S)
        (split_dual_cell _ _ (split_clique_left_card S (P.supported S hz).1))
  have hh := Finset.sum_le_sum (fun S (_ : S ∈ Finset.univ) => hcell S)
  have he : (∑ S, P.mass S * ((2:ℝ)/3*S.toLeft.card*S.toRight.card -
      (1:ℝ)/6*S.toRight.card*(S.toRight.card-1))) =
      (2:ℝ)/3*(∑ S,P.mass S*S.toLeft.card*S.toRight.card) -
      (1:ℝ)/6*(∑ S,P.mass S*(S.toRight.card : ℝ)*(S.toRight.card-1)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _; ring
  rw [he,split_cross_load,split_right_load] at hh
  simpa only [FractionalPartition.cost, mul_assoc] using hh

 theorem split_edge_count (a s : ℕ) :
    ((splitGraph a s).edgeFinset.card : ℝ) = (a:ℝ)*s+(s:ℝ)*(s-1)/2 := by
  let G := splitGraph a s
  have hrow (u : Fin a ⊕ Fin s) :
      (∑ v,if G.Adj u v then (1:ℝ) else 0)=(G.degree u:ℝ) := by
    rw [← G.card_neighborFinset_eq_degree]
    simp [← SimpleGraph.mem_neighborFinset]
  have hd : (∑ u,∑ v,if G.Adj u v then (1:ℝ) else 0)=2*(G.edgeFinset.card:ℝ) := by
    simp_rw [hrow]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hr (i : Fin s) : (∑ j : Fin s,if i ≠ j then (1:ℝ) else 0)=(s:ℝ)-1 := by
    have he (j : Fin s) : (if i ≠ j then (1:ℝ) else 0)=1-(if i=j then 1 else 0) := by
      by_cases hij : i=j <;> simp [hij]
    simp_rw [he]
    simp
  have htotal : (∑ u : Fin a ⊕ Fin s,∑ v : Fin a ⊕ Fin s,if G.Adj u v then (1:ℝ) else 0)=
      2*(a:ℝ)*s+(s:ℝ)*(s-1) := by
    simp only [Fintype.sum_sum_type]
    simp only [G,splitGraph,Sum.isRight_inl,Sum.isRight_inr,Bool.false_eq_true,
      or_false,or_true,and_true,and_false,
      Sum.inl_ne_inr,Sum.inr_ne_inl,ne_eq,not_false_eq_true,if_true,if_false,
      Sum.inr.injEq]
    simp_rw [hr]
    simp
    ring
  change (G.edgeFinset.card:ℝ)=_
  linarith

end Erdos1017
