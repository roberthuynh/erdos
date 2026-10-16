import ParallelCounts

/-! The deficit-two specialization of Metsch (1991), Lemma 3.7(a).
Printed p19 supplies the counting argument; printed p44 Lemma6.3 uses this
specialization. Source PDF SHA256:
0fe0e7c6d7214480dc04f489b4fbb4bdb24d8bcebf2e75cb81ecc441c7959ad5.
The argument counts three actual finite parallel-neighborhood sets. The final
geometric theorems discharge all cardinal budgets using proved ParallelCounts
results and retain the original indexed line carrier, including empty lines. -/
namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

/-- Three-set lower Bonferroni bound, expressed without natural subtraction. -/
theorem three_sets_card_le {α : Type*} [DecidableEq α]
    (A B C T : Finset α) (hA : A ⊆ T) (hB : B ⊆ T) (hC : C ⊆ T) :
    A.card+B.card+C.card ≤ T.card+(A∩B).card+(A∩C).card+(B∩C).card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A∪B) C
  have hi : (A∪B)∩C = (A∩C)∪(B∩C) := by ext x; simp; tauto
  have h3 := Finset.card_union_le (A∩C) (B∩C)
  have h4 : ((A∪B)∪C).card ≤ T.card := by
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with hab | hc
    · rcases Finset.mem_union.mp hab with ha | hb
      · exact hA ha
      · exact hB hb
    · exact hC hc
  rw [hi] at h2
  omega

/-- Three deleted labels and pair-neighborhood budgets force the triangle
inequality. All hypotheses here concern actual finite sets, not geometry. -/
theorem parallel_triangle_card_bound {α : Type*} [DecidableEq α]
    (R A B C : Finset α) (u v w : α) (q a b c : ℕ)
    (hu : u∈R) (hv : v∈R) (hw : w∈R)
    (huv : u≠v) (huw : u≠w) (hvw : v≠w)
    (hA : A ⊆ R) (hB : B ⊆ R) (hC : C ⊆ R)
    (hnA : u∉A ∧ v∉A ∧ w∉A)
    (hnB : u∉B ∧ v∉B ∧ w∉B)
    (hnC : u∉C ∧ v∉C ∧ w∉C)
    (hR : R.card=2*q)
    (hAc : A.card+2=q+a) (hBc : B.card+2=q+b) (hCc : C.card+2=q+c)
    (hAB : (A∩B).card+1≤a*b)
    (hAC : (A∩C).card+1≤a*c)
    (hBC : (B∩C).card+1≤b*c) :
    (q:ℤ) ≤ (a:ℤ)*b+(a:ℤ)*c+(b:ℤ)*c-a-b-c := by
  let T := ((R.erase u).erase v).erase w
  have hTc : T.card+3=2*q := by
    have hv' : v ∈ R.erase u := Finset.mem_erase.mpr ⟨huv.symm,hv⟩
    have hw' : w ∈ (R.erase u).erase v :=
      Finset.mem_erase.mpr ⟨hvw.symm,Finset.mem_erase.mpr ⟨huw.symm,hw⟩⟩
    have h1 := Finset.card_erase_add_one hu
    have h2 := Finset.card_erase_add_one hv'
    have h3 := Finset.card_erase_add_one hw'
    dsimp [T]
    omega
  have subT : ∀ S : Finset α, S⊆R → u∉S ∧ v∉S ∧ w∉S → S⊆T := by
    intro S hs hn x hx
    simp only [T,Finset.mem_erase]
    exact ⟨fun he => hn.2.2 (he ▸ hx), fun he => hn.2.1 (he ▸ hx),
      fun he => hn.1 (he ▸ hx),hs hx⟩
  have hh := three_sets_card_le A B C T (subT A hA hnA) (subT B hB hnB) (subT C hC hnC)
  have hTcZ : (T.card:ℤ)+3=2*q := by exact_mod_cast hTc
  have hAcZ : (A.card:ℤ)+2=(q:ℤ)+a := by exact_mod_cast hAc
  have hBcZ : (B.card:ℤ)+2=(q:ℤ)+b := by exact_mod_cast hBc
  have hCcZ : (C.card:ℤ)+2=(q:ℤ)+c := by exact_mod_cast hCc
  have hABZ : ((A∩B).card:ℤ)+1≤(a:ℤ)*b := by exact_mod_cast hAB
  have hACZ : ((A∩C).card:ℤ)+1≤(a:ℤ)*c := by exact_mod_cast hAC
  have hBCZ : ((B∩C).card:ℤ)+1≤(b:ℤ)*c := by exact_mod_cast hBC
  have hhZ : (A.card:ℤ)+B.card+C.card ≤ T.card+(A∩B).card+(A∩C).card+(B∩C).card := by
    exact_mod_cast hh
  linarith

/-- A third parallel family loses the original line from a common-parallel
intersection. The cardinal bound is supplied by the actual pair count. -/
theorem triangle_pair_inter_bound (D : IndexedDesign q X I) {L A B : I}
    (hLA : D.Parallel L A) (hLB : D.Parallel L B)
    (hcount : (D.parallelLines A∩D.parallelLines B).card =
      D.lineDeficit A*D.lineDeficit B) :
    ((D.parallelLines L∩D.parallelLines A)∩
      (D.parallelLines L∩D.parallelLines B)).card+1 ≤ D.lineDeficit A*D.lineDeficit B := by
  have hmem : L ∈ D.parallelLines A∩D.parallelLines B := by
    simp only [Finset.mem_inter,D.mem_parallelLines]
    exact ⟨D.parallel_symm hLA,D.parallel_symm hLB⟩
  have hsub : (D.parallelLines L∩D.parallelLines A)∩
      (D.parallelLines L∩D.parallelLines B) ⊆
      (D.parallelLines A∩D.parallelLines B).erase L := by
    intro j hj
    simp only [Finset.mem_inter,D.mem_parallelLines] at hj
    apply Finset.mem_erase.mpr
    exact ⟨hj.1.1.1.symm,by
      simp only [Finset.mem_inter,D.mem_parallelLines]
      exact ⟨hj.1.2,hj.2.2⟩⟩
  have hh := Finset.card_le_card hsub
  have he := Finset.card_erase_add_one hmem
  omega

/-- The geometric triangle argument after the six literal common-parallel
cardinalities have been computed. The public geometric wrapper discharges them. -/
theorem parallel_triangle_of_counts (D : IndexedDesign q X I) {L A B C : I}
    (hLA : D.Parallel L A) (hLB : D.Parallel L B) (hLC : D.Parallel L C)
    (hAB : B ∈ D.meetingLines A) (hAC : C ∈ D.meetingLines A)
    (hBC : C ∈ D.meetingLines B)
    (hR : (D.parallelLines L).card=2*q)
    (hAc : (D.parallelLines L∩D.parallelLines A).card+2=q+D.lineDeficit A)
    (hBc : (D.parallelLines L∩D.parallelLines B).card+2=q+D.lineDeficit B)
    (hCc : (D.parallelLines L∩D.parallelLines C).card+2=q+D.lineDeficit C)
    (hABc : (D.parallelLines A∩D.parallelLines B).card=D.lineDeficit A*D.lineDeficit B)
    (hACc : (D.parallelLines A∩D.parallelLines C).card=D.lineDeficit A*D.lineDeficit C)
    (hBCc : (D.parallelLines B∩D.parallelLines C).card=D.lineDeficit B*D.lineDeficit C) :
    (q:ℤ) ≤ (D.lineDeficit A:ℤ)*D.lineDeficit B+
      (D.lineDeficit A:ℤ)*D.lineDeficit C+(D.lineDeficit B:ℤ)*D.lineDeficit C-
      D.lineDeficit A-D.lineDeficit B-D.lineDeficit C := by
  have hmAB := (D.mem_meetingLines A B).mp hAB
  have hmAC := (D.mem_meetingLines A C).mp hAC
  have hmBC := (D.mem_meetingLines B C).mp hBC
  have excludes : ∀ i j, (∃ x, D.inc x i ∧ D.inc x j) →
      j∉D.parallelLines i := by
    intro i j hm hp
    obtain ⟨x,hxi,hxj⟩ := hm
    exact ((D.mem_parallelLines i j).mp hp).2 x ⟨hxi,hxj⟩
  have hnA : A∉D.parallelLines L∩D.parallelLines A ∧
      B∉D.parallelLines L∩D.parallelLines A ∧ C∉D.parallelLines L∩D.parallelLines A := by
    refine ⟨?_,?_,?_⟩
    · intro h; exact ((D.mem_parallelLines A A).mp (Finset.mem_inter.mp h).2).1 rfl
    · exact fun h => excludes A B hmAB.2 (Finset.mem_inter.mp h).2
    · exact fun h => excludes A C hmAC.2 (Finset.mem_inter.mp h).2
  have hnB : A∉D.parallelLines L∩D.parallelLines B ∧
      B∉D.parallelLines L∩D.parallelLines B ∧ C∉D.parallelLines L∩D.parallelLines B := by
    refine ⟨?_,?_,?_⟩
    · exact fun h => excludes B A (by simpa only [and_comm] using hmAB.2) (Finset.mem_inter.mp h).2
    · intro h; exact ((D.mem_parallelLines B B).mp (Finset.mem_inter.mp h).2).1 rfl
    · exact fun h => excludes B C hmBC.2 (Finset.mem_inter.mp h).2
  have hnC : A∉D.parallelLines L∩D.parallelLines C ∧
      B∉D.parallelLines L∩D.parallelLines C ∧ C∉D.parallelLines L∩D.parallelLines C := by
    refine ⟨?_,?_,?_⟩
    · exact fun h => excludes C A (by simpa only [and_comm] using hmAC.2) (Finset.mem_inter.mp h).2
    · exact fun h => excludes C B (by simpa only [and_comm] using hmBC.2) (Finset.mem_inter.mp h).2
    · intro h; exact ((D.mem_parallelLines C C).mp (Finset.mem_inter.mp h).2).1 rfl
  exact parallel_triangle_card_bound (D.parallelLines L)
    (D.parallelLines L∩D.parallelLines A) (D.parallelLines L∩D.parallelLines B)
    (D.parallelLines L∩D.parallelLines C) A B C q (D.lineDeficit A) (D.lineDeficit B) (D.lineDeficit C)
    ((D.mem_parallelLines L A).mpr hLA) ((D.mem_parallelLines L B).mpr hLB)
    ((D.mem_parallelLines L C).mpr hLC) hmAB.1.symm hmAC.1.symm hmBC.1.symm
    Finset.inter_subset_left Finset.inter_subset_left Finset.inter_subset_left hnA hnB hnC
    hR hAc hBc hCc (D.triangle_pair_inter_bound hLA hLB hABc)
    (D.triangle_pair_inter_bound hLA hLC hACc) (D.triangle_pair_inter_bound hLB hLC hBCc)

/-- Integer form of the final scalar simplification when one triangle member
also has deficit two. -/
theorem deficit_two_triangle_arithmetic (q b c : ℕ)
    (h : (q:ℤ) ≤ 2*(b:ℤ)+2*(c:ℤ)+(b:ℤ)*c-2-b-c) :
    q+3 ≤ (b+1)*(c+1) := by
  have hh : (q:ℤ)+3 ≤ ((b:ℤ)+1)*((c:ℤ)+1) := by nlinarith
  exact_mod_cast hh

/-- Actual indexed-design specialization of Metsch3.7(a), with deficit-two
base line and three pairwise intersecting lines parallel to it. No common-
neighborhood or clique-count premise is left over. -/
theorem parallel_triangle_obstruction (D : IndexedDesign q X I)
    (hI : Fintype.card I=q^2+q+1) (hcap : ∀ i, D.lineDegree i≤q+1)
    {L A B C : I} (hL : D.lineDeficit L=2)
    (hLA : D.Parallel L A) (hLB : D.Parallel L B) (hLC : D.Parallel L C)
    (hAB : B∈D.meetingLines A) (hAC : C∈D.meetingLines A) (hBC : C∈D.meetingLines B) :
    (q:ℤ) ≤ (D.lineDeficit A:ℤ)*D.lineDeficit B+
      (D.lineDeficit A:ℤ)*D.lineDeficit C+(D.lineDeficit B:ℤ)*D.lineDeficit C-
      D.lineDeficit A-D.lineDeficit B-D.lineDeficit C := by
  have hmAB := (D.mem_meetingLines A B).mp hAB
  have hmAC := (D.mem_meetingLines A C).mp hAC
  have hmBC := (D.mem_meetingLines B C).mp hBC
  have hR : (D.parallelLines L).card=2*q := by
    rw [D.parallel_card_eq_q_mul_deficit L hI (hcap L),hL,Nat.mul_comm]
  exact D.parallel_triangle_of_counts hLA hLB hLC hAB hAC hBC hR
    (D.common_parallel_card_deficit_two hI (hcap L) (hcap A) hLA hL)
    (D.common_parallel_card_deficit_two hI (hcap L) (hcap B) hLB hL)
    (D.common_parallel_card_deficit_two hI (hcap L) (hcap C) hLC hL)
    (D.common_parallel_card_of_meet hI (hcap A) (hcap B) hmAB.1.symm hmAB.2)
    (D.common_parallel_card_of_meet hI (hcap A) (hcap C) hmAC.1.symm hmAC.2)
    (D.common_parallel_card_of_meet hI (hcap B) (hcap C) hmBC.1.symm hmBC.2)

/-- The exact actual-design triangle supplier used in the early Metsch route:
one of the three intersecting parallel lines also has deficit two. -/
theorem parallel_triangle_deficit_two (D : IndexedDesign q X I)
    (hI : Fintype.card I=q^2+q+1) (hcap : ∀ i, D.lineDegree i≤q+1)
    {L A B C : I} (hL : D.lineDeficit L=2) (hA : D.lineDeficit A=2)
    (hLA : D.Parallel L A) (hLB : D.Parallel L B) (hLC : D.Parallel L C)
    (hAB : B∈D.meetingLines A) (hAC : C∈D.meetingLines A) (hBC : C∈D.meetingLines B) :
    q+3 ≤ (D.lineDeficit B+1)*(D.lineDeficit C+1) := by
  have hh := D.parallel_triangle_obstruction hI hcap hL hLA hLB hLC hAB hAC hBC
  rw [hA] at hh
  apply deficit_two_triangle_arithmetic
  simpa only [Nat.cast_ofNat] using hh

#print axioms parallel_triangle_obstruction
#print axioms parallel_triangle_deficit_two
end Erdos60.Embedding.IndexedDesign
