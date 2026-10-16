import GraphStatistics
import Mathlib.Tactic

namespace Erdos60.Statistics
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def subsetPairs (U : Finset V) : Finset (Sym2 V) :=
  U.offDiag.image Sym2.mk.uncurry

noncomputable def pairCodegree (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => codegree G x y,
    fun x y => by dsimp; rw [codegree_symm]⟩

@[simp] theorem pairCodegree_mk (G : SimpleGraph V) (x y : V) :
    pairCodegree G s(x,y) = codegree G x y := rfl

theorem two_mul_subsetPairs_sum (U : Finset V) (w : Sym2 V → ℕ) :
    2*(∑ p ∈ subsetPairs U, w p) = ∑ p ∈ U.offDiag, w (Sym2.mk.uncurry p) := by
  classical
  have hfiber (a b : V) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) :
      {z ∈ U.offDiag | Sym2.mk.uncurry z = s(a,b)} = {(a,b),(b,a)} := by
    ext z
    rcases z with ⟨u,v⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag,
      Function.uncurry_apply_pair, Sym2.eq_iff, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    aesop
  rw [Finset.mul_sum]
  apply Finset.sum_image'
  intro p hp
  rcases p with ⟨a,b⟩
  obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp hp
  calc
    2*w (Sym2.mk.uncurry (a,b)) =
        ∑ j ∈ ({(a,b),(b,a)} : Finset (V×V)), w (Sym2.mk.uncurry j) := by
      simp [hab, Sym2.eq_swap, two_mul]
    _ = _ := congrArg
      (fun S : Finset (V×V) => ∑ j ∈ S, w (Sym2.mk.uncurry j))
      (hfiber a b ha hb hab).symm

theorem subsetPairs_card (U : Finset V) : (subsetPairs U).card = U.card.choose 2 := by
  classical
  have hh := two_mul_subsetPairs_sum U (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.offDiag_card] at hh
  have hc : 2*(U.card.choose 2) = U.card*U.card-U.card := by
    calc
      2*(U.card.choose 2) = (U.card*(U.card-1)/2)*2 := by
        rw [Nat.choose_two_right, Nat.mul_comm 2]
      _ = U.card*(U.card-1) := Nat.div_mul_cancel (Nat.even_mul_pred_self U.card).two_dvd
      _ = U.card*U.card-U.card := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]

  norm_cast at hh
  omega

theorem subsetPairs_subset_unorderedPairs (U : Finset V) :
    subsetPairs U ⊆ unorderedPairs (V := V) := by
  classical
  intro p hp
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
  apply Finset.mem_image.mpr
  exact ⟨(x,y), by simpa using (Finset.mem_offDiag.mp hxy).2.2, rfl⟩

/-- Exact scalar identity behind the integer Cauchy bound. -/
theorem cast_sq_eq_cast_add_two_choose (n : ℕ) :
    (n : ℝ)^2 = n+2*(n.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  ring

/-- Finite-family Cauchy inequality with an actual binomial budget. -/
theorem codegree_cauchy {α : Type*} (s : Finset α) (a : α → ℕ) (Z : ℕ)
    (hb : ∑ i ∈ s, (a i).choose 2 ≤ 2*Z) :
    (∑ i ∈ s, (a i : ℝ)) ≤ s.card+2*Real.sqrt ((s.card : ℝ)*Z) := by
  have hsq : (∑ i ∈ s, (a i : ℝ)^2) =
      (∑ i ∈ s, (a i : ℝ))+2*∑ i ∈ s, ((a i).choose 2 : ℝ) := by
    simp_rw [cast_sq_eq_cast_add_two_choose]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun i => (a i : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hb' : (∑ i ∈ s, ((a i).choose 2 : ℝ)) ≤ 2*(Z : ℝ) := by exact_mod_cast hb
  have hcc : (∑ i ∈ s, (a i : ℝ))^2 ≤
      (s.card : ℝ)*(∑ i ∈ s, (a i : ℝ)) + 4*(s.card : ℝ)*Z := by
    rw [hsq] at hc
    nlinarith [mul_nonneg (show (0:ℝ) ≤ s.card by positivity)
      (show 0 ≤ 2*(Z : ℝ)-(∑ i ∈ s, ((a i).choose 2 : ℝ)) by linarith)]
  have hs0 := Real.sqrt_nonneg ((s.card : ℝ)*Z)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ (s.card : ℝ)*Z by positivity)
  have hk : (0:ℝ) ≤ s.card := by positivity
  by_contra hn
  have hn' : (s.card : ℝ)+2*Real.sqrt ((s.card : ℝ)*Z) < ∑ i ∈ s, (a i : ℝ) := lt_of_not_ge hn
  have hh := mul_nonneg hk (show 0 ≤ (∑ i ∈ s, (a i : ℝ))-
      (s.card : ℝ)-2*Real.sqrt ((s.card : ℝ)*Z) by linarith)
  nlinarith

/-- Source §1 equation (5), for the actual graph's unordered endpoint pairs
and actual ordinary unlabelled cycle count, with ambient chords allowed. -/
theorem subset_codegree_overlap (G : SimpleGraph V) (U : Finset V) :
    (∑ p ∈ subsetPairs U, (pairCodegree G p : ℝ)) ≤
      (U.card.choose 2 : ℝ)+2*Real.sqrt ((U.card.choose 2 : ℝ)*Erdos60.Counting.cycleCount G) := by
  classical
  have hweight : ∀ p : Sym2 V, (pairCodegree G p).choose 2 = pairWeight G p := by
    intro p
    rcases p with ⟨x,y⟩
    rfl
  have hb : ∑ p ∈ subsetPairs U, (pairCodegree G p).choose 2 ≤
      2*Erdos60.Counting.cycleCount G := by
    simp_rw [hweight]
    rw [← unorderedPair_sum_eq_twice]
    exact Finset.sum_le_sum_of_subset (subsetPairs_subset_unorderedPairs U)
  simpa only [subsetPairs_card] using codegree_cauchy (subsetPairs U) (pairCodegree G)
    (Erdos60.Counting.cycleCount G) hb

#print axioms subset_codegree_overlap
end Erdos60.Statistics
