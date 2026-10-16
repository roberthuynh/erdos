import CompletionBasic
import SubsetPathCount
import Mathlib.Data.Nat.Choose.Cast

/-! Completion §1 actual exceptional-set count from the real graph's two-path
counts. No common-neighbor or pair-count identity is assumed as a premise. -/
namespace Erdos60.Completion
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def exceptionalVertices (G : SimpleGraph V) (q : ℕ) (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => (q : ℝ)/100 ≤ (G.neighborFinset v ∩ S).card
noncomputable def goodFullVertices (G : SimpleGraph V) (q : ℕ) (S : Finset V) : Finset V :=
  (Finset.univ.filter fun v => G.degree v = q+1) \ exceptionalVertices G q S

@[simp] theorem mem_goodFullVertices (G : SimpleGraph V) (q : ℕ) (S : Finset V) (x : V) :
    x ∈ goodFullVertices G q S ↔ G.degree x = q+1 ∧ x ∉ exceptionalVertices G q S := by
  simp [goodFullVertices]

theorem cycles_empty_of_noFourCycle (G : SimpleGraph V) (hG : NoFourCycle G) :
    Counting.cycles G = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨C,hC⟩
  obtain ⟨hsub,a,b,c,d,hd,rfl⟩ := (Counting.mem_cycles _ _).mp hC
  have hac : a ≠ c := by
    intro h
    exact (List.nodup_cons.mp hd).1 (by simp [h])
  have hbd : b ≠ d := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (by simp [h])
  apply hG hac hbd
  · have := hsub (by simp [Counting.fourEdges] : s(a,b) ∈ Counting.fourEdges a b c d)
    simpa using this
  · have := hsub (by simp [Counting.fourEdges] : s(b,c) ∈ Counting.fourEdges a b c d)
    simpa using this
  · have := hsub (by simp [Counting.fourEdges] : s(c,d) ∈ Counting.fourEdges a b c d)
    simpa using this
  · have := hsub (by simp [Counting.fourEdges] : s(d,a) ∈ Counting.fourEdges a b c d)
    simpa using this

theorem large_section_choose_lower (q k : ℕ) (hq : 100000000 ≤ q)
    (hk : (q : ℝ)/100 ≤ k) :
    (q : ℝ)^2/21000 ≤ (k.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  have hq' : (100000000 : ℝ) ≤ q := by exact_mod_cast hq
  have hm := mul_nonneg (show 0 ≤ (k : ℝ)-q/100 by linarith)
    (show 0 ≤ (k : ℝ)+q/100-1 by linarith)
  have hq2 := mul_nonneg (show 0 ≤ (q : ℝ) by positivity)
    (show 0 ≤ (q : ℝ)-100000000 by linarith)
  nlinarith

/-- The actual exceptional set has at most 11000 vertices. -/
theorem exceptionalVertices_card (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (S : Finset V)
    (hS : 1000*S.card ≤ 1001*q) :
    (exceptionalVertices G q S).card ≤ 11000 := by
  classical
  have hbudget := Statistics.subset_path_bound G S
  simp only [Counting.cycleCount,cycles_empty_of_noFourCycle G hG,Finset.card_empty,
    mul_zero,zero_add] at hbudget
  have hsum : (∑ v ∈ exceptionalVertices G q S,
      ((G.neighborFinset v ∩ S).card).choose 2) ≤ S.card.choose 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i hi hnot => Nat.zero_le _)).trans hbudget
  have hlow : ((exceptionalVertices G q S).card : ℝ)*((q : ℝ)^2/21000) ≤
      ∑ v ∈ exceptionalVertices G q S, (((G.neighborFinset v ∩ S).card).choose 2 : ℝ) := by
    calc
      _ = ∑ v ∈ exceptionalVertices G q S, ((q : ℝ)^2/21000) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv => large_section_choose_lower q _ hq
        (Finset.mem_filter.mp hv).2)
  have hsumr : (∑ v ∈ exceptionalVertices G q S,
      (((G.neighborFinset v ∩ S).card).choose 2 : ℝ)) ≤ (S.card.choose 2 : ℝ) := by
    exact_mod_cast hsum
  rw [Nat.cast_choose_two] at hsumr
  have hSr : (1000 : ℝ)*S.card ≤ 1001*q := by exact_mod_cast hS
  have hq' : (100000000 : ℝ) ≤ q := by exact_mod_cast hq
  have hSq : (S.card : ℝ)^2 ≤ (1001*(q : ℝ)/1000)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1001*(q : ℝ)/1000-S.card by linarith)
      (show 0 ≤ 1001*(q : ℝ)/1000+S.card by positivity)]
  by_contra hn
  have hn' : (11000 : ℝ) < (exceptionalVertices G q S).card := by exact_mod_cast (Nat.lt_of_not_ge hn)
  have hm := mul_nonneg (show 0 ≤ ((exceptionalVertices G q S).card : ℝ)-11000 by linarith)
    (sq_nonneg (q : ℝ))
  nlinarith [sq_nonneg ((q : ℝ)-1)]

/-- A good full vertex has the strict integer neighbor-budget interface used
by the actual full-row intersection theorem. -/
theorem goodFullVertices_neighbor_budget (G : SimpleGraph V) (q : ℕ) (S : Finset V)
    {x : V} (hx : x ∈ goodFullVertices G q S) :
    G.degree x = q+1 ∧ 100*(G.neighborFinset x ∩ S).card < q := by
  obtain ⟨hfull,hnot⟩ := Finset.mem_sdiff.mp hx
  constructor
  · exact (Finset.mem_filter.mp hfull).2
  · have hn : ¬ (q : ℝ)/100 ≤ (G.neighborFinset x ∩ S).card := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    have hr : (100 : ℝ)*(G.neighborFinset x ∩ S).card < q := by linarith
    exact_mod_cast hr

/-- Actual number of good full rows after removing the exceptional set. -/
theorem goodFullVertices_card_lower (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q)
    (hN : Fintype.card V = q^2+q+1) (hcap : ∀ x, G.degree x ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q) :
    (q : ℝ)^2-(q : ℝ)/1000+1-11000 ≤
      (goodFullVertices G q (Finset.univ.filter (fun x => G.degree x ≤ q))).card := by
  classical
  let S := Finset.univ.filter (fun x => G.degree x ≤ q)
  let F := Finset.univ.filter (fun x => G.degree x = q+1)
  let B := exceptionalVertices G q S
  let A := goodFullVertices G q S
  have hB : B.card ≤ 11000 := exceptionalVertices_card G hG q hq S hS
  have hpart : F.card + S.card = Fintype.card V := by
    have hf : F = Finset.univ.filter (fun x => ¬G.degree x ≤ q) := by
      ext x
      have := hcap x
      simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    rw [hf,add_comm]
    simpa only [S,Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
        (p := fun x => G.degree x ≤ q)
  have hA : F.card ≤ A.card+B.card := by
    have hh := Finset.card_sdiff_add_card_inter F B
    have hi : (F ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
    change A.card + (F ∩ B).card = F.card at hh
    omega
  have hAr : (F.card : ℝ) ≤ A.card+B.card := by exact_mod_cast hA
  have hBr : (B.card : ℝ) ≤ 11000 := by exact_mod_cast hB
  have hSr : (1000 : ℝ)*S.card ≤ 1001*q := by exact_mod_cast hS
  rw [hN] at hpart
  have hpr : (F.card : ℝ)+S.card = (q : ℝ)^2+q+1 := by exact_mod_cast hpart
  change (q : ℝ)^2-q/1000+1-11000 ≤ A.card
  linarith

end Erdos60.Completion
