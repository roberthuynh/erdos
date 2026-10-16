import ParallelCounts
import EmbeddingParameters
import DeficitTwo

namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

noncomputable def cliquesContaining (M : Finset (Finset I)) (i : I) : Finset (Finset I) :=
  M.filter fun C => i ∈ C

/-- Actual clique incidence injection at an outside point. Each clique is a
finite set of indexed line labels; distinct cliques share at most one label.
No desired incidence upper bound is a structure field or hypothesis. -/
theorem clique_incidence_le_parallel_point (D : IndexedDesign q X I)
    (M : Finset (Finset I)) (i : I) (p : X) (hpi : ¬D.inc p i)
    (hparallel : ∀ C ∈ M, ∀ j ∈ C, ∀ k ∈ C, j ≠ k → D.Parallel j k)
    (hpoint : ∀ C ∈ M, ∃ j ∈ C, D.inc p j)
    (hshare : ∀ C ∈ M, ∀ E ∈ M, C ≠ E → (C ∩ E).card ≤ 1) :
    (cliquesContaining M i).card ≤ D.lineDeficit i := by
  classical
  let A := cliquesContaining M i
  let B := D.pointLines p ∩ D.parallelLines i
  have hex : ∀ C : ↥A, ∃ j ∈ B, j ∈ C.val := by
    intro C
    have hC := Finset.mem_filter.mp C.property
    obtain ⟨j,hj,hpj⟩ := hpoint C.val hC.1
    have hij : i ≠ j := by intro h; exact hpi (h.symm ▸ hpj)
    exact ⟨j,Finset.mem_inter.mpr ⟨(D.mem_pointLines p j).mpr hpj,
      (D.mem_parallelLines i j).mpr (hparallel C.val hC.1 i hC.2 j hj hij)⟩,hj⟩
  choose f hf using hex
  let F : ↥A → ↥B := fun C => ⟨f C,(hf C).1⟩
  have hinj : Function.Injective F := by
    intro C E heq
    apply Subtype.ext
    by_contra hne
    have hC := Finset.mem_filter.mp C.property
    have hE := Finset.mem_filter.mp E.property
    have hfEq : f C=f E := congrArg Subtype.val heq
    have hiCE : i ∈ C.val ∩ E.val := Finset.mem_inter.mpr ⟨hC.2,hE.2⟩
    have hjCE : f C ∈ C.val ∩ E.val := Finset.mem_inter.mpr
      ⟨(hf C).2,hfEq ▸ (hf E).2⟩
    have hij : i=f C := Finset.card_le_one.mp (hshare C.val hC.1 E.val hE.1 hne) i hiCE (f C) hjCE
    have hpf := (D.mem_pointLines p (f C)).mp (Finset.mem_inter.mp (hf C).1).1
    exact hpi (hij.symm ▸ hpf)
  have hc := Fintype.card_le_of_injective F hinj
  rw [Fintype.card_coe,Fintype.card_coe] at hc
  have hB : B.card=D.lineDeficit i := by
    exact (D.point_parallel_count p i).trans (if_neg hpi)
  rwa [hB] at hc

/-- Actual clique incidence injection at an outside point. Each clique is a
finite set of indexed line labels; distinct cliques share at most one label.
No desired incidence upper bound is a structure field or hypothesis. -/
theorem clique_incidence_avoiding_le (D : IndexedDesign q X I)
    (M : Finset (Finset I)) (i h : I) (p : X)
    (hph : D.inc p h) (hih : D.Parallel i h)
    (hparallel : ∀ C ∈ M, ∀ j ∈ C, ∀ k ∈ C, j ≠ k → D.Parallel j k)
    (hpoint : ∀ C ∈ M, ∃ j ∈ C, D.inc p j)
    (hshare : ∀ C ∈ M, ∀ E ∈ M, C ≠ E → (C ∩ E).card ≤ 1) :
    ((cliquesContaining M i).filter fun C => h ∉ C).card ≤ D.lineDeficit i-1 := by
  classical
  have hpi : ¬D.inc p i := fun hpi => hih.2 p ⟨hpi,hph⟩
  let A := (cliquesContaining M i).filter fun C => h ∉ C
  let B := (D.pointLines p ∩ D.parallelLines i).erase h
  have hex : ∀ C : ↥A, ∃ j ∈ B, j ∈ C.val := by
    intro C
    have hCnot := Finset.mem_filter.mp C.property
    have hC := Finset.mem_filter.mp hCnot.1
    obtain ⟨j,hj,hpj⟩ := hpoint C.val hC.1
    have hij : i ≠ j := by intro h; exact hpi (h.symm ▸ hpj)
    have hjh : j ≠ h := by intro he; exact hCnot.2 (he ▸ hj)
    exact ⟨j,Finset.mem_erase.mpr ⟨hjh,Finset.mem_inter.mpr ⟨(D.mem_pointLines p j).mpr hpj,
      (D.mem_parallelLines i j).mpr (hparallel C.val hC.1 i hC.2 j hj hij)⟩⟩,hj⟩
  choose f hf using hex
  let F : ↥A → ↥B := fun C => ⟨f C,(hf C).1⟩
  have hinj : Function.Injective F := by
    intro C E heq
    apply Subtype.ext
    by_contra hne
    have hCnot := Finset.mem_filter.mp C.property
    have hC := Finset.mem_filter.mp hCnot.1
    have hE := Finset.mem_filter.mp (Finset.mem_filter.mp E.property).1
    have hfEq : f C=f E := congrArg Subtype.val heq
    have hiCE : i ∈ C.val ∩ E.val := Finset.mem_inter.mpr ⟨hC.2,hE.2⟩
    have hjCE : f C ∈ C.val ∩ E.val := Finset.mem_inter.mpr
      ⟨(hf C).2,hfEq ▸ (hf E).2⟩
    have hij : i=f C := Finset.card_le_one.mp (hshare C.val hC.1 E.val hE.1 hne) i hiCE (f C) hjCE
    have hpf := (D.mem_pointLines p (f C)).mp (Finset.mem_inter.mp (Finset.mem_erase.mp (hf C).1).2).1
    exact hpi (hij.symm ▸ hpf)
  have hc := Fintype.card_le_of_injective F hinj
  rw [Fintype.card_coe,Fintype.card_coe] at hc
  have hhmem : h ∈ D.pointLines p ∩ D.parallelLines i := by simp [hph,hih]
  have hB : B.card=D.lineDeficit i-1 := by
    rw [Finset.card_erase_of_mem hhmem,D.point_parallel_count p i,if_neg hpi]
  rwa [hB] at hc

/-- Each actual pairwise-parallel clique contains exactly one line through
an all-clique-meeting point. This yields the literal clique/line incidence count. -/
theorem sum_clique_incidence_at_point (D : IndexedDesign q X I)
    (M : Finset (Finset I)) (p : X)
    (hparallel : ∀ C ∈ M, ∀ j ∈ C, ∀ k ∈ C, j ≠ k → D.Parallel j k)
    (hpoint : ∀ C ∈ M, ∃ j ∈ C, D.inc p j) :
    (∑ j ∈ D.pointLines p, (cliquesContaining M j).card) = M.card := by
  classical
  have hone (C : Finset I) (hC : C ∈ M) :
      ((D.pointLines p).filter fun j => j ∈ C).card = 1 := by
    apply Finset.card_eq_one_iff_existsUnique.mpr
    obtain ⟨j,hj,hpj⟩ := hpoint C hC
    refine ⟨j,by simp [hj,hpj],?_⟩
    intro k hk
    have hkC := (Finset.mem_filter.mp hk).2
    have hpk := (D.mem_pointLines p k).mp (Finset.mem_filter.mp hk).1
    by_contra hkj
    exact (hparallel C hC k hkC j hj hkj).2 p ⟨hpk,hpj⟩
  calc
    _ = ∑ C ∈ M, ((D.pointLines p).filter fun j => j ∈ C).card := by
      simp only [cliquesContaining,Finset.card_filter]
      rw [Finset.sum_comm]
    _ = ∑ C ∈ M, 1 := Finset.sum_congr rfl hone
    _ = _ := by simp

 theorem sum_point_lineDegrees (D : IndexedDesign q X I) (p : X) :
    (∑ j ∈ D.pointLines p, D.lineDegree j) = Fintype.card X+q := by
  rw [D.sum_lineDegrees_subset]
  simp_rw [D.pointLines_inter_card]
  rw [← Finset.add_sum_erase Finset.univ (fun x : X => if x=p then q+1 else 1) (Finset.mem_univ p)]
  have hh : (∑ x ∈ Finset.univ.erase p, if x=p then q+1 else 1) = (Finset.univ.erase p).card := by
    calc
      _ = ∑ x ∈ Finset.univ.erase p, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [(Finset.mem_erase.mp hx).1]
      _ = _ := by simp
  rw [hh]
  simp only [if_true,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ]
  have hp : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨p⟩
  omega

/-- The source point-row deficit identity is derived from incidence joins. -/
theorem sum_point_lineDeficits (D : IndexedDesign q X I) (s : ℕ)
    (hX : Fintype.card X+s=q^2+q+1) (hcap : ∀ j, D.lineDegree j ≤ q+1) (p : X) :
    (∑ j ∈ D.pointLines p, D.lineDeficit j) = s := by
  have hpoint (j : I) : D.lineDegree j+D.lineDeficit j=q+1 := by
    unfold lineDeficit
    have hc := hcap j
    omega
  have hs := Finset.sum_congr (s₁ := D.pointLines p) rfl (fun j _ => hpoint j)
  simp only [Finset.sum_add_distrib,D.sum_point_lineDegrees,Finset.sum_const,
    nsmul_eq_mul,D.card_pointLines] at hs
  nlinarith

/-- Source6.7(d)'s actual global incidence upper bound. -/
theorem clique_total_le_missing_points (D : IndexedDesign q X I)
    (M : Finset (Finset I)) (s : ℕ) (p : X)
    (hX : Fintype.card X+s=q^2+q+1) (hcap : ∀ j, D.lineDegree j ≤ q+1)
    (hparallel : ∀ C ∈ M, ∀ j ∈ C, ∀ k ∈ C, j ≠ k → D.Parallel j k)
    (hpoint : ∀ C ∈ M, ∃ j ∈ C, D.inc p j)
    (hupper : ∀ j ∈ D.pointLines p, (cliquesContaining M j).card ≤ D.lineDeficit j) :
    M.card ≤ s := by
  rw [← D.sum_clique_incidence_at_point M p hparallel hpoint,
    ← D.sum_point_lineDeficits s hX hcap p]
  exact Finset.sum_le_sum hupper

/-- Literal finite coverage count: each clique through i has at most q other
labels, so its covered indexed parallel labels total at most q times incidence. -/
theorem covered_parallel_card_le (D : IndexedDesign q X I) (M : Finset (Finset I))
    (i : I) (A : Finset I) (hA : A ⊆ D.parallelLines i)
    (hcovered : ∀ j ∈ A, ∃ C ∈ cliquesContaining M i, j ∈ C)
    (hsize : ∀ C ∈ cliquesContaining M i, C.card ≤ q+1) :
    A.card ≤ (cliquesContaining M i).card*q := by
  classical
  have hsub : A ⊆ (cliquesContaining M i).biUnion (fun C => C.erase i) := by
    intro j hj
    obtain ⟨C,hC,hjC⟩ := hcovered j hj
    have hij := ((D.mem_parallelLines i j).mp (hA hj)).1
    exact Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_erase.mpr ⟨hij.symm,hjC⟩⟩
  calc
    A.card ≤ ((cliquesContaining M i).biUnion (fun C => C.erase i)).card := Finset.card_le_card hsub
    _ ≤ ∑ C ∈ cliquesContaining M i, (C.erase i).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ cliquesContaining M i, q := by
      apply Finset.sum_le_sum
      intro C hC
      have hiC := (Finset.mem_filter.mp hC).2
      rw [Finset.card_erase_of_mem hiC]
      have hc := hsize C hC
      omega
    _ = _ := by simp

/-- The strict source6.9 weighted lower count forces exact incidence once the
independently proved source6.7 incidence upper bound is available. -/
theorem clique_incidence_eq_of_many_covered (D : IndexedDesign q X I)
    (M : Finset (Finset I)) (i : I) (A : Finset I)
    (hd : 1 ≤ D.lineDeficit i) (hA : A ⊆ D.parallelLines i)
    (hmany : (D.lineDeficit i-1)*q < A.card)
    (hcovered : ∀ j ∈ A, ∃ C ∈ cliquesContaining M i, j ∈ C)
    (hsize : ∀ C ∈ cliquesContaining M i, C.card ≤ q+1)
    (hupper : (cliquesContaining M i).card ≤ D.lineDeficit i) :
    (cliquesContaining M i).card = D.lineDeficit i := by
  have hc := D.covered_parallel_card_le M i A hA hcovered hsize
  by_contra hn
  have hs : (cliquesContaining M i).card ≤ D.lineDeficit i-1 := by omega
  have hm := Nat.mul_le_mul_right q hs
  omega

/-- The actual source6.7(b) avoiding count gives existence, and actual shared
label uniqueness gives unique coverage of each parallel pair. -/
theorem unique_pair_clique_of_exact_incidence (D : IndexedDesign q X I)
    (M : Finset (Finset I)) {i j : I} (hij : i ≠ j)
    (hd : 1 ≤ D.lineDeficit i)
    (hexact : (cliquesContaining M i).card = D.lineDeficit i)
    (havoid : ((cliquesContaining M i).filter fun C => j ∉ C).card ≤ D.lineDeficit i-1)
    (hshare : ∀ C ∈ M, ∀ E ∈ M, C ≠ E → (C ∩ E).card ≤ 1) :
    ∃! C, C ∈ M ∧ i ∈ C ∧ j ∈ C := by
  classical
  have hex : ∃ C ∈ cliquesContaining M i, j ∈ C := by
    by_contra hn
    have hall : ∀ C ∈ cliquesContaining M i, j ∉ C := by simpa only [not_exists,not_and] using hn
    have he : (cliquesContaining M i).filter (fun C => j ∉ C) = cliquesContaining M i :=
      Finset.filter_true_of_mem hall
    rw [he,hexact] at havoid
    omega
  obtain ⟨C,hC,hjC⟩ := hex
  have hC' := Finset.mem_filter.mp hC
  refine ⟨C,⟨hC'.1,hC'.2,hjC⟩,?_⟩
  intro E hE
  by_contra hne
  have hl : (E ∩ C).card ≤ 1 := hshare E hE.1 C hC'.1 hne
  have heq : i=j := Finset.card_le_one.mp hl i (Finset.mem_inter.mpr ⟨hE.2.1,hC'.2⟩)
    j (Finset.mem_inter.mpr ⟨hE.2.2,hjC⟩)
  exact hij heq

 theorem parallel_degree_lt_full (D : IndexedDesign q X I)
    (hI : Fintype.card I=q^2+q+1) (hcap : ∀ j, D.lineDegree j ≤ q+1)
    {i j : I} (hij : D.Parallel i j) : D.lineDegree j ≠ q+1 := by
  intro hfull
  have hd : D.lineDeficit j=0 := by simp [lineDeficit,hfull]
  have hc := D.parallel_card_eq_q_mul_deficit j hI (hcap j)
  rw [hd,Nat.mul_zero] at hc
  have hi : i ∈ D.parallelLines j := (D.mem_parallelLines j i).mpr (D.parallel_symm hij)
  have hp := Finset.card_pos.mpr ⟨i,hi⟩
  omega

noncomputable def smallerParallel (D : IndexedDesign q X I) (i : I) : Finset I :=
  (D.parallelLines i).filter fun j => D.lineDeficit j < D.lineDeficit i

/-- Actual weighted parallel-line count behind the unified source6.9 induction.
The lower-deficit labels are counted from the design, never assumed plentiful. -/
theorem smallerParallel_many (D : IndexedDesign q X I) (s : ℕ)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q)
    (hI : Fintype.card I=q^2+q+1) (hX : Fintype.card X+s=q^2+q+1)
    (hcap : ∀ j, D.lineDegree j ≤ q+1) (hnone : ∀ j, D.lineDegree j ≠ q)
    (i : I) (hdi : 3 ≤ D.lineDeficit i) :
    (D.lineDeficit i-1)*q < (D.smallerParallel i).card := by
  classical
  let d := D.lineDeficit i
  have hd : 3 ≤ d := hdi
  have hkd : D.lineDegree i+d=q+1 := Nat.add_sub_cancel' (hcap i)
  have hd1 : d-1+1=d := by omega
  have hd2 : d-2+2=d := by omega
  have hpoint : ∀ j ∈ D.parallelLines i, D.lineDegree j ≤ D.lineDegree i+
      (if D.lineDeficit j<d then d-2 else 0) := by
    intro j hj
    have hp := (D.mem_parallelLines i j).mp hj
    have hfull := D.parallel_degree_lt_full hI hcap hp
    have hnc := hnone j
    have hcapj := hcap j
    have hdefj : D.lineDegree j+D.lineDeficit j=q+1 := Nat.add_sub_cancel' hcapj
    split_ifs with hsmall <;> omega
  have hsum := Finset.sum_le_sum hpoint
  have hfilter : (∑ j ∈ D.parallelLines i, if D.lineDeficit j<d then d-2 else 0) =
      (D.smallerParallel i).card*(d-2) := by
    rw [← Finset.sum_filter]
    simp [smallerParallel,d]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
  rw [hfilter,D.sum_parallel_lineDegrees,D.parallel_card_eq_q_mul_deficit i hI (hcap i)] at hsum
  have hdegreeX : D.lineDegree i ≤ Fintype.card X := by
    exact Finset.card_le_univ (D.linePoints i)
  have hrest : Fintype.card X-D.lineDegree i+s=q^2+d := by omega
  have hm := Erdos60.Embedding.Parameters.all_deficits_induction_strict q s d hq hs hd
  have hpositive : s ≤ (d-1)*q+d := by nlinarith
  have hb : (d-1)*q+d-s+s=(d-1)*q+d := Nat.sub_add_cancel hpositive
  have hweighted : d*((d-1)*q+d-s) ≤ (D.smallerParallel i).card*(d-2) := by
    change (Fintype.card X-D.lineDegree i)*d ≤ q*d*D.lineDegree i +
      (D.smallerParallel i).card*(d-2) at hsum
    have hrm := congrArg (fun n : ℕ => n*d) hrest
    have hkm := congrArg (fun n : ℕ => n*q*d) hkd
    have hdm := congrArg (fun n : ℕ => n*q*d) hd1
    have hbm := congrArg (fun n : ℕ => n*d) hb
    nlinarith
  have hstrict := Erdos60.Embedding.Parameters.all_deficits_product_strict q s d hq hs hd
  change (d-1)*q < (D.smallerParallel i).card
  by_contra hn
  have hsmall : (D.smallerParallel i).card ≤ (d-1)*q := by omega
  have hmul := Nat.mul_le_mul_right (d-2) hsmall
  omega

noncomputable def goodCliques (D : IndexedDesign q X I) (e a : ℕ) : Finset (Finset I) :=
  Finset.univ.filter (D.GoodClique e a)

@[simp] theorem mem_goodCliques (D : IndexedDesign q X I) (e a : ℕ) (C : Finset I) :
    C ∈ D.goodCliques e a ↔ D.GoodClique e a C := by simp [goodCliques]

 theorem goodCliquesContaining_eq (D : IndexedDesign q X I) (e a : ℕ) (i : I) :
    cliquesContaining (D.goodCliques e a) i = D.goodCliquesThrough e a i := by
  ext C
  simp [cliquesContaining]

/-- Source6.7(a), derived from the actual deficit-two construction and its
proved exact-two count. Every all-long point meets every actual good clique. -/
theorem good_clique_meets_clean_point (D : IndexedDesign q X I) (e a : ℕ)
    (hq : 0 < q) (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I=q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hstrict : 2*q < 3*(q-1-a))
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hconstruct : ∀ L H : I, D.lineDeficit L=2 → D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C)
    (C : Finset I) (hC : D.GoodClique e a C) (p : X)
    (hclean : ∀ i, D.inc p i → D.Long e i) :
    ∃ i ∈ C, D.inc p i := by
  classical
  obtain ⟨L,hLC,hdef⟩ := hC.2.2
  by_cases hpL : D.inc p L
  · exact ⟨L,hLC,hpL⟩
  obtain ⟨H,K,hHK,hLH,hLK,hHlong,hKlong,hpH,hpK⟩ :=
    D.clean_point_two_parallel L hdef (D.Long e) p hpL hclean
  obtain ⟨A,hAg,hLA,hHA⟩ := hconstruct L H hdef hHlong hLH
  obtain ⟨B,hBg,hLB,hKB⟩ := hconstruct L K hdef hKlong hLK
  have hAB : A ≠ B := by
    intro he
    have hKA : K ∈ A := he.symm ▸ hKB
    exact (hAg.1.1.2 H hHA K hKA hHK).2 p ⟨hpH,hpK⟩
  have htwo := D.deficit_two_exact e a L hq heq hshort hI (hcap L) hdef hstrict hinter
    (hconstruct L · hdef)
  have hsub : ({A,B} : Finset (Finset I)) ⊆ D.goodCliquesThrough e a L := by
    intro E hE
    simp only [Finset.mem_insert,Finset.mem_singleton] at hE
    rcases hE with rfl | rfl <;> simp_all
  have heq : ({A,B} : Finset (Finset I)) = D.goodCliquesThrough e a L :=
    Finset.eq_of_subset_of_card_le hsub (by simp [htwo,hAB])
  have hmem : C ∈ ({A,B} : Finset (Finset I)) := by rw [heq]; simp [hC,hLC]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨H,hHA,hpH⟩
  · exact ⟨K,hKB,hpK⟩

 theorem exists_full_line (D : IndexedDesign q X I) (s : ℕ)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q)
    (hX : Fintype.card X+s=q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q) :
    ∃ i, D.lineDegree i=q+1 := by
  classical
  have hpos : 0 < Fintype.card X := by
    by_contra hn
    have hc : Fintype.card X=0 := by omega
    rw [hc] at hX
    nlinarith
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp hpos
  by_contra hn
  have hnotfull : ∀ i, D.lineDegree i ≠ q+1 := by simpa only [not_exists] using hn
  have hpoint (i : I) : 2 ≤ D.lineDeficit i := by
    have hc := hcap i
    have hf := hnotfull i
    have hnonei := hnone i
    unfold lineDeficit
    omega
  have hsum := Finset.sum_le_sum (s := D.pointLines p) (fun i _ => hpoint i)
  rw [D.sum_point_lineDeficits s hX hcap p] at hsum
  simp only [Finset.sum_const,nsmul_eq_mul,D.card_pointLines] at hsum
  nlinarith

 theorem good_clique_card_le (D : IndexedDesign q X I) (e a s : ℕ)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q)
    (hI : Fintype.card I=q^2+q+1) (hX : Fintype.card X+s=q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q)
    (C : Finset I) (hC : D.GoodClique e a C) : C.card ≤ q+1 := by
  classical
  obtain ⟨L,hfull⟩ := D.exists_full_line s hq hs hX hcap hnone
  have hLpos : 0 < D.lineDegree L := by omega
  obtain ⟨p,hpL⟩ := Finset.card_pos.mp hLpos
  have hex : ∀ i : ↥C, ∃ x : ↥(D.linePoints L), D.inc x.val i.val := by
    intro i
    by_cases hiL : i.val=L
    · refine ⟨⟨p,hpL⟩,?_⟩
      simpa [hiL] using hpL
    · by_cases hm : ∃ x, D.inc x L ∧ D.inc x i.val
      · obtain ⟨x,hxL,hxi⟩ := hm
        exact ⟨⟨x,(D.mem_linePoints L x).mpr hxL⟩,hxi⟩
      · have hp : D.Parallel i.val L := ⟨hiL,by
          intro x hx
          exact hm ⟨x,hx.2,hx.1⟩⟩
        exact False.elim ((D.parallel_degree_lt_full hI hcap hp) hfull)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j heq
    apply Subtype.ext
    by_contra hij
    have hp := hC.1.1.2 i.val i.property j.val j.property hij
    have hxi := hf i
    have hxj := hf j
    have he : (f i).val=(f j).val := congrArg Subtype.val heq
    exact hp.2 (f i).val ⟨hxi,he.symm ▸ hxj⟩
  have hc := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe,Fintype.card_coe] at hc
  change C.card ≤ D.lineDegree L at hc
  rwa [hfull] at hc

 theorem exists_clean_outside_deficit_ge_two (D : IndexedDesign q X I) (e : ℕ) (L : I)
    (hq : 0 < q) (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I=q^2+q+1) (hcap : D.lineDegree L ≤ q+1)
    (hd : 2 ≤ D.lineDeficit L) :
    ∃ p : X, ¬D.inc p L ∧ ∀ i, D.inc p i → D.Long e i := by
  have hn : ¬D.parallelLines L ⊆ D.shortLines e := by
    intro hsub
    have hc := Finset.card_le_card hsub
    rw [D.parallel_card_eq_q_mul_deficit L hI hcap] at hc
    have hm := Nat.mul_le_mul_left q hd
    omega
  obtain ⟨H,hLH,hHshort⟩ := Finset.not_subset.mp hn
  have hHlong : D.Long e H := by
    have hns : ¬D.Short e H := by simpa using hHshort
    unfold Short Long at *
    omega
  obtain ⟨p,hpH,hclean⟩ := D.exists_clean_point_on_long e heq hshort H hHlong
  exact ⟨p,fun hpL => ((D.mem_parallelLines L H).mp hLH).2 p ⟨hpL,hpH⟩,hclean⟩

 theorem good_clique_incidence_upper (D : IndexedDesign q X I) (e a : ℕ)
    (hq : 0 < q) (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I=q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hnone : ∀ i, D.lineDegree i ≠ q)
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hmeet : ∀ p : X, (∀ j, D.inc p j → D.Long e j) →
      ∀ C : Finset I, D.GoodClique e a C → ∃ j ∈ C, D.inc p j)
    (L : I) :
    (cliquesContaining (D.goodCliques e a) L).card ≤ D.lineDeficit L := by
  classical
  by_cases hd0 : D.lineDeficit L=0
  · have hfull : D.lineDegree L=q+1 := by unfold lineDeficit at hd0; have := hcap L; omega
    have he : cliquesContaining (D.goodCliques e a) L=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro C hC
      have hC' := Finset.mem_filter.mp hC
      have hgood := (D.mem_goodCliques e a C).mp hC'.1
      obtain ⟨J,hJC,hdefJ⟩ := hgood.2.2
      have hJL : J ≠ L := by intro h; subst J; omega
      exact (D.parallel_degree_lt_full hI hcap (hgood.1.1.2 J hJC L hC'.2 hJL)) hfull
    simp [he,hd0]
  · have hd : 2 ≤ D.lineDeficit L := by
      have hc := hcap L
      have hn := hnone L
      unfold lineDeficit at *
      omega
    obtain ⟨p,hpL,hclean⟩ := D.exists_clean_outside_deficit_ge_two e L hq heq hshort hI (hcap L) hd
    apply D.clique_incidence_le_parallel_point (D.goodCliques e a) L p hpL
    · intro C hC; exact ((D.mem_goodCliques e a C).mp hC).1.1.2
    · intro C hC; exact hmeet p hclean C ((D.mem_goodCliques e a C).mp hC)
    · intro C hC E hE hne
      exact hinter C E ((D.mem_goodCliques e a C).mp hC) ((D.mem_goodCliques e a E).mp hE) hne

 theorem good_clique_incidence_avoiding_upper (D : IndexedDesign q X I) (e a : ℕ)
    (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hmeet : ∀ p : X, (∀ j, D.inc p j → D.Long e j) →
      ∀ C : Finset I, D.GoodClique e a C → ∃ j ∈ C, D.inc p j)
    (L H : I) (hH : D.Long e H) (hLH : D.Parallel L H) :
    ((cliquesContaining (D.goodCliques e a) L).filter fun C => H ∉ C).card ≤ D.lineDeficit L-1 := by
  obtain ⟨p,hpH,hclean⟩ := D.exists_clean_point_on_long e heq hshort H hH
  apply D.clique_incidence_avoiding_le (D.goodCliques e a) L H p hpH hLH
  · intro C hC; exact ((D.mem_goodCliques e a C).mp hC).1.1.2
  · intro C hC; exact hmeet p hclean C ((D.mem_goodCliques e a C).mp hC)
  · intro C hC E hE hne
    exact hinter C E ((D.mem_goodCliques e a C).mp hC) ((D.mem_goodCliques e a E).mp hE) hne

 theorem good_parallel_coverage_of_count (D : IndexedDesign q X I) (e a : ℕ)
    (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I=q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hmeet : ∀ p : X, (∀ j, D.inc p j → D.Long e j) →
      ∀ C : Finset I, D.GoodClique e a C → ∃ j ∈ C, D.inc p j)
    (L H : I) (hH : D.Long e H) (hLH : D.Parallel L H)
    (hexact : (cliquesContaining (D.goodCliques e a) L).card=D.lineDeficit L) :
    ∃! C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C := by
  have hd : 1 ≤ D.lineDeficit L := by
    have hc := D.parallel_card_eq_q_mul_deficit L hI (hcap L)
    have hpos := Finset.card_pos.mpr ⟨H,(D.mem_parallelLines L H).mpr hLH⟩
    nlinarith
  have havoid := D.good_clique_incidence_avoiding_upper e a heq hshort hinter hmeet L H hH hLH
  have hh := D.unique_pair_clique_of_exact_incidence (D.goodCliques e a) hLH.1 hd hexact havoid
    (fun C hC E hE hne => hinter C E ((D.mem_goodCliques e a C).mp hC)
      ((D.mem_goodCliques e a E).mp hE) hne)
  simpa only [D.mem_goodCliques] using hh

/-- One strong induction covers every deficit d≥3, including three. The
smaller-deficit parallel labels are proved plentiful by actual weighted counts.
The only construction supplier is the upstream source6.2–6.3 deficit-two clique
construction; no exact incidence or embedding promise is assumed. -/
theorem good_clique_exact_incidence (D : IndexedDesign q X I) (e a s : ℕ)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q)
    (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I=q^2+q+1) (hX : Fintype.card X+s=q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q)
    (hstrict : 2*q < 3*(q-1-a))
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hconstruct : ∀ L H : I, D.lineDeficit L=2 → D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C) :
    ∀ L : I, D.Long e L →
      (cliquesContaining (D.goodCliques e a) L).card=D.lineDeficit L := by
  classical
  have hq0 : 0 < q := by omega
  have hmeet : ∀ p : X, (∀ j, D.inc p j → D.Long e j) →
      ∀ C : Finset I, D.GoodClique e a C → ∃ j ∈ C, D.inc p j := by
    intro p hclean C hC
    exact D.good_clique_meets_clean_point e a hq0 heq hshort hI hcap hstrict hinter hconstruct C hC p hclean
  have hall : ∀ d : ℕ, ∀ L : I, D.lineDeficit L=d → D.Long e L →
      (cliquesContaining (D.goodCliques e a) L).card=D.lineDeficit L := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro L hdL hL
      have hupper := D.good_clique_incidence_upper e a hq0 heq hshort hI hcap hnone hinter hmeet L
      by_cases hd0 : D.lineDeficit L=0
      · omega
      by_cases hd2 : D.lineDeficit L=2
      · rw [D.goodCliquesContaining_eq,hd2]
        exact D.deficit_two_exact e a L hq0 heq hshort hI (hcap L) hd2 hstrict hinter (hconstruct L · hd2)
      have hd3 : 3 ≤ D.lineDeficit L := by
        have hc := hcap L
        have hn := hnone L
        unfold lineDeficit at *
        omega
      apply D.clique_incidence_eq_of_many_covered (D.goodCliques e a) L (D.smallerParallel L)
      · omega
      · exact Finset.filter_subset _ _
      · exact D.smallerParallel_many s hq hs hI hX hcap hnone L hd3
      · intro J hJ
        have hJ' := Finset.mem_filter.mp hJ
        have hpar := (D.mem_parallelLines L J).mp hJ'.1
        have hJlong : D.Long e J := by
          have hcapL := hcap L
          have hcapJ := hcap J
          have hdl : D.lineDegree L+D.lineDeficit L=q+1 := Nat.add_sub_cancel' hcapL
          have hdj : D.lineDegree J+D.lineDeficit J=q+1 := Nat.add_sub_cancel' hcapJ
          unfold Long at *
          omega
        have hJcount := ih (D.lineDeficit J) (by omega) J rfl hJlong
        obtain ⟨C,hC,hunique⟩ := D.good_parallel_coverage_of_count e a heq hshort hI hcap hinter hmeet
          J L hL (D.parallel_symm hpar) hJcount
        refine ⟨C,?_,hC.2.1⟩
        simp [cliquesContaining,hC.1,hC.2.2]
      · intro C hC
        have hgood := (D.mem_goodCliques e a C).mp (Finset.mem_filter.mp hC).1
        exact D.good_clique_card_le e a s hq hs hI hX hcap hnone C hgood
      · exact hupper
  intro L hL
  exact hall (D.lineDeficit L) L rfl hL

/-- Source6.9(a,b), actual indexed-line coverage and exact added-point count. -/
theorem good_clique_complete_coverage (D : IndexedDesign q X I) (e a s : ℕ)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q)
    (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I=q^2+q+1) (hX : Fintype.card X+s=q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q)
    (hstrict : 2*q < 3*(q-1-a))
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hconstruct : ∀ L H : I, D.lineDeficit L=2 → D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C) :
    (D.goodCliques e a).card=s ∧
      (∀ L : I, D.Long e L → (cliquesContaining (D.goodCliques e a) L).card=D.lineDeficit L) ∧
      (∀ L H : I, D.Long e L → D.Long e H → D.Parallel L H →
        ∃! C : Finset I, C ∈ D.goodCliques e a ∧ L ∈ C ∧ H ∈ C) := by
  classical
  have hq0 : 0 < q := by omega
  have hmeet : ∀ p : X, (∀ j, D.inc p j → D.Long e j) →
      ∀ C : Finset I, D.GoodClique e a C → ∃ j ∈ C, D.inc p j := by
    intro p hclean C hC
    exact D.good_clique_meets_clean_point e a hq0 heq hshort hI hcap hstrict hinter hconstruct C hC p hclean
  have hmult := D.good_clique_exact_incidence e a s hq hs heq hshort hI hX hcap hnone hstrict hinter hconstruct
  have hpair : ∀ L H : I, D.Long e L → D.Long e H → D.Parallel L H →
      ∃! C : Finset I, C ∈ D.goodCliques e a ∧ L ∈ C ∧ H ∈ C := by
    intro L H hL hH hLH
    simpa only [D.mem_goodCliques] using D.good_parallel_coverage_of_count e a heq hshort hI hcap hinter hmeet
      L H hH hLH (hmult L hL)
  refine ⟨?_,hmult,hpair⟩
  obtain ⟨L,hfull⟩ := D.exists_full_line s hq hs hX hcap hnone
  have hL : D.Long e L := by unfold Long; omega
  obtain ⟨p,hpL,hclean⟩ := D.exists_clean_point_on_long e heq hshort L hL
  have hcount := D.sum_clique_incidence_at_point (D.goodCliques e a) p
    (fun C hC => ((D.mem_goodCliques e a C).mp hC).1.1.2)
    (fun C hC => hmeet p hclean C ((D.mem_goodCliques e a C).mp hC))
  have hpointmult : (∑ j ∈ D.pointLines p, (cliquesContaining (D.goodCliques e a) j).card) =
      ∑ j ∈ D.pointLines p, D.lineDeficit j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hmult j (hclean j ((D.mem_pointLines p j).mp hj))
  rw [hpointmult,D.sum_point_lineDeficits s hX hcap p] at hcount
  exact hcount.symm

 theorem missing_points_ge_q_add_two (D : IndexedDesign q X I) (s : ℕ)
    (hs : 0 < s) (hI : Fintype.card I=q^2+q+1) (hX : Fintype.card X+s=q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q) :
    q+2 ≤ s := by
  have hnonneg (i : I) : (0 : ℤ) ≤ D.intDeficit i*(D.intDeficit i-2) := by
    rw [D.intDeficit_eq_nat (hcap i)]
    have hd : D.lineDeficit i=0 ∨ 2 ≤ D.lineDeficit i := by
      have hc := hcap i
      have hn := hnone i
      unfold lineDeficit
      omega
    rcases hd with hd | hd
    · simp [hd]
    · have hdz : (2 : ℤ) ≤ D.lineDeficit i := by exact_mod_cast hd
      nlinarith
  have hsum := Finset.sum_nonneg (s := (Finset.univ : Finset I)) (fun i _ => hnonneg i)
  rw [D.sum_intDeficit_mul_sub_two s hI hX] at hsum
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have hbound : (q : ℤ)+2 ≤ s := by nlinarith
  exact_mod_cast hbound

end Erdos60.Embedding.IndexedDesign
