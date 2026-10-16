import BasicCounts

/-! Metsch (1991), published book supplied by the user, printed pages2 and15:
source(B4) and Lemma3.1(a,b,c), specialized to the original fixed line-label
count q^2+q+1. Every incidence sum counts indexed labels; empty lines and
repeated singleton supports remain distinct. The formulas are derived by actual
finite bijections, subset incidence transposition, and a three-way label
partition. No embedding, clique completion, or source theorem is assumed.
The parallel-pair integer formula intentionally avoids truncated subtraction.
-/
namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

/-- Each outside point sees the fixed line via distinct other incident labels. -/
theorem outside_meeting_count (D : IndexedDesign q X I) {x : X} {i : I} (hxi : ¬D.inc x i) :
    (D.pointLines x ∩ D.meetingLines i).card = D.lineDegree i := by
  have hex : ∀ y : ↥(D.linePoints i), ∃ j, D.inc x j ∧ D.inc y.val j := by
    intro y
    have hxy : x ≠ y.val := by intro h; exact hxi (h.symm ▸ (D.mem_linePoints i y.val).mp y.property)
    obtain ⟨j,hj,_⟩ := D.unique_join x y.val hxy
    exact ⟨j,hj⟩
  choose f hf using hex
  have hne : ∀ y : ↥(D.linePoints i), f y ≠ i := by
    intro y h
    exact hxi (h ▸ (hf y).1)
  let g : ↥(D.linePoints i) → ↥(D.pointLines x ∩ D.meetingLines i) := fun y =>
    ⟨f y,Finset.mem_inter.mpr ⟨(D.mem_pointLines x _).mpr (hf y).1,
      (D.mem_meetingLines i _).mpr ⟨hne y,y.val,(D.mem_linePoints i _).mp y.property,(hf y).2⟩⟩⟩
  have hi : Function.Injective g := by
    intro y z h
    have he : f y=f z := congrArg Subtype.val h
    apply Subtype.ext
    exact D.intersection_unique (hne y) (hf y).2 (he ▸ (hf z).2)
      ((D.mem_linePoints i _).mp y.property) ((D.mem_linePoints i _).mp z.property)
  have hs : Function.Surjective g := by
    intro j
    have hjx := (D.mem_pointLines x j.val).mp (Finset.mem_inter.mp j.property).1
    obtain ⟨_,y,hyi,hyj⟩ := (D.mem_meetingLines i j.val).mp (Finset.mem_inter.mp j.property).2
    let yy : ↥(D.linePoints i) := ⟨y,(D.mem_linePoints i y).mpr hyi⟩
    refine ⟨yy,?_⟩
    apply Subtype.ext
    have hxy : x ≠ y := by intro h; exact hxi (h.symm ▸ hyi)
    exact D.join_unique hxy (hf yy).1 (hf yy).2 hjx hyj
  have hc := Fintype.card_of_bijective ⟨hi,hs⟩
  rw [Fintype.card_coe,Fintype.card_coe] at hc
  exact hc.symm

/-- Exact source(B4) outside-point count, before deficit notation. -/
theorem outside_parallel_count_add (D : IndexedDesign q X I) {x : X} {i : I} (hxi : ¬D.inc x i) :
    (D.pointLines x ∩ D.parallelLines i).card + D.lineDegree i = q+1 := by
  have he : (D.pointLines x ∩ D.parallelLines i) ∪ (D.pointLines x ∩ D.meetingLines i) = D.pointLines x := by
    ext j
    simp only [Finset.mem_union,Finset.mem_inter,D.mem_pointLines,D.mem_parallelLines,D.mem_meetingLines]
    constructor
    · rintro (⟨hxj,hpar⟩ | ⟨hxj,hmeet⟩) <;> exact hxj
    · intro hxj
      have hji : j ≠ i := by intro h; exact hxi (h ▸ hxj)
      by_cases hmeet : ∃ y, D.inc y i ∧ D.inc y j
      · exact Or.inr ⟨hxj,hji,hmeet⟩
      · exact Or.inl ⟨hxj,hji.symm,by simpa only [not_exists] using hmeet⟩
  have hd : Disjoint (D.pointLines x ∩ D.parallelLines i) (D.pointLines x ∩ D.meetingLines i) := by
    apply Finset.disjoint_left.mpr
    intro j hp hm
    obtain ⟨_,hno⟩ := (D.mem_parallelLines i j).mp (Finset.mem_inter.mp hp).2
    obtain ⟨_,y,hyi,hyj⟩ := (D.mem_meetingLines i j).mp (Finset.mem_inter.mp hm).2
    exact hno y ⟨hyi,hyj⟩
  have hc := Finset.card_union_of_disjoint hd
  rw [he,D.card_pointLines,D.outside_meeting_count hxi] at hc
  exact hc.symm

theorem point_parallel_count (D : IndexedDesign q X I) (x : X) (i : I) :
    (D.pointLines x ∩ D.parallelLines i).card = if D.inc x i then 0 else D.lineDeficit i := by
  by_cases hxi : D.inc x i
  · rw [if_pos hxi]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hxj := (D.mem_pointLines x j).mp (Finset.mem_inter.mp hj).1
    exact ((D.mem_parallelLines i j).mp (Finset.mem_inter.mp hj).2).2 x ⟨hxi,hxj⟩
  · rw [if_neg hxi]
    have hc := D.outside_parallel_count_add hxi
    dsimp [lineDeficit]
    omega

/-- Incidence double count over any family of indexed line labels. -/
theorem sum_lineDegrees_subset (D : IndexedDesign q X I) (J : Finset I) :
    (∑ j ∈ J, D.lineDegree j) = ∑ x : X, (D.pointLines x ∩ J).card := by
  simp_rw [D.lineDegree_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have he : D.pointLines x ∩ J = J.filter (D.inc x) := by ext j; simp [and_comm]
  rw [he]
  simp

/-- Source3.1(c), exact weighted parallel-degree count, preserving all labels. -/
theorem sum_parallel_lineDegrees (D : IndexedDesign q X I) (i : I) :
    (∑ j ∈ D.parallelLines i, D.lineDegree j) =
      (Fintype.card X-D.lineDegree i)*D.lineDeficit i := by
  rw [D.sum_lineDegrees_subset]
  simp_rw [D.point_parallel_count]
  have he : Finset.univ.filter (fun x : X => ¬D.inc x i) = Finset.univ \ D.linePoints i := by
    ext x; simp
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul]
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
  rfl

theorem linePoints_inter_card (D : IndexedDesign q X I) {i j : I} (hij : i ≠ j) :
    (D.linePoints i ∩ D.linePoints j).card = if ∃ x, D.inc x i ∧ D.inc x j then 1 else 0 := by
  by_cases hh : ∃ x, D.inc x i ∧ D.inc x j
  · rw [if_pos hh]
    apply Finset.card_eq_one_iff_existsUnique.mpr
    obtain ⟨x,hxi,hxj⟩ := hh
    refine ⟨x,by simp [hxi,hxj],?_⟩
    intro y hy
    have hyi := (D.mem_linePoints i y).mp (Finset.mem_inter.mp hy).1
    have hyj := (D.mem_linePoints j y).mp (Finset.mem_inter.mp hy).2
    exact D.intersection_unique hij hyi hxi hyj hxj
  · rw [if_neg hh]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hh ⟨x,(D.mem_linePoints i x).mp (Finset.mem_inter.mp hx).1,
      (D.mem_linePoints j x).mp (Finset.mem_inter.mp hx).2⟩

/-- Double-count actual incidences between arbitrary retained point and line subsets. -/
theorem subset_incidence_sum (D : IndexedDesign q X I) (S : Finset X) (J : Finset I) :
    (∑ j ∈ J, (D.linePoints j ∩ S).card) = ∑ x ∈ S, (D.pointLines x ∩ J).card := by
  have hl : ∀ j, (D.linePoints j ∩ S).card = ∑ x ∈ S, if D.inc x j then 1 else 0 := by
    intro j
    have he : D.linePoints j ∩ S = S.filter (fun x => D.inc x j) := by ext x; simp [and_comm]
    rw [he]; simp
  have hp : ∀ x, (D.pointLines x ∩ J).card = ∑ j ∈ J, if D.inc x j then 1 else 0 := by
    intro x
    have he : D.pointLines x ∩ J = J.filter (D.inc x) := by ext j; simp [and_comm]
    rw [he]; simp
  simp_rw [hl,hp]
  rw [Finset.sum_comm]

/-- Weighted common-incidence identity used for both cases of source3.1(b). -/
theorem parallel_line_incidence (D : IndexedDesign q X I) (i j : I) :
    (∑ k ∈ D.parallelLines i, (D.linePoints k ∩ D.linePoints j).card) =
      ((D.linePoints j).card-(D.linePoints j ∩ D.linePoints i).card)*D.lineDeficit i := by
  rw [D.subset_incidence_sum]
  simp_rw [D.point_parallel_count]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul]
  have he : (D.linePoints j).filter (fun x => ¬D.inc x i) = D.linePoints j \ D.linePoints i := by
    ext x; simp
  rw [he,Finset.card_sdiff,Finset.inter_comm]

/-- Intersection-degree sum distinguishes the indexed label j from all lines
meeting it. This remains valid when j has zero or one point. -/
theorem intersection_degree_sum (D : IndexedDesign q X I) (J : Finset I) (j : I) :
    (∑ k ∈ J, (D.linePoints k ∩ D.linePoints j).card) =
      (if j ∈ J then D.lineDegree j else 0) + (J ∩ D.meetingLines j).card := by
  have hterm : ∀ k, (D.linePoints k ∩ D.linePoints j).card =
      (if k=j then D.lineDegree j else 0) + (if k ∈ D.meetingLines j then 1 else 0) := by
    intro k
    by_cases hkj : k=j
    · subst k
      simp [lineDegree]
    · rw [if_neg hkj,D.linePoints_inter_card hkj]
      simp only [zero_add,D.mem_meetingLines]
      by_cases hm : ∃ x, D.inc x k ∧ D.inc x j
      · have hm' : ∃ x, D.inc x j ∧ D.inc x k := by obtain ⟨x,hx⟩ := hm; exact ⟨x,hx.symm⟩
        simp [hm,hm',hkj]
      · have hm' : ¬∃ x, D.inc x j ∧ D.inc x k := by rintro ⟨x,hx⟩; exact hm ⟨x,hx.symm⟩
        simp [hm,hm',hkj]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  have he : J.filter (fun k => k ∈ D.meetingLines j) = J ∩ D.meetingLines j := by ext k; simp
  simp only [Finset.sum_boole,he,Nat.cast_id]

/-- Every indexed line label is either the fixed label, parallel to it, or
meets it. Empty and repeated singleton labels are never merged. -/
theorem label_partition_card (D : IndexedDesign q X I) (J : Finset I) (j : I) :
    (J ∩ D.meetingLines j).card + (J ∩ D.parallelLines j).card + (if j ∈ J then 1 else 0) = J.card := by
  have hterm : ∀ k, (if k ∈ D.meetingLines j then 1 else 0) +
      (if k ∈ D.parallelLines j then 1 else 0) + (if k=j then 1 else 0) = (1:ℕ) := by
    intro k
    by_cases hkj : k=j
    · subst k
      simp [Parallel]
    · by_cases hm : ∃ x, D.inc x j ∧ D.inc x k
      · have hnp : ¬D.Parallel j k := fun hp => by obtain ⟨x,hx⟩ := hm; exact hp.2 x hx
        simp [D.mem_meetingLines,D.mem_parallelLines,hkj,hm,hnp]
      · have hp : D.Parallel j k := ⟨(fun h => hkj h.symm),by simpa only [not_exists] using hm⟩
        simp [D.mem_meetingLines,D.mem_parallelLines,hkj,hm,hp]
  have hh := Finset.sum_congr (s₁ := J) rfl (fun k hk => hterm k)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_const,smul_eq_mul,mul_one] at hh
  have hm : J.filter (fun k => k ∈ D.meetingLines j) = J ∩ D.meetingLines j := by ext k; simp
  have hp : J.filter (fun k => k ∈ D.parallelLines j) = J ∩ D.parallelLines j := by ext k; simp
  simpa only [Finset.sum_boole,hm,hp,Nat.cast_id] using hh

/-- Source3.1(b), intersecting distinct indexed lines. -/
theorem common_parallel_card_of_meet (D : IndexedDesign q X I) {i j : I}
    (hI : Fintype.card I = q^2+q+1)
    (hci : D.lineDegree i ≤ q+1) (hcj : D.lineDegree j ≤ q+1)
    (hij : i ≠ j) (hmeet : ∃ x, D.inc x i ∧ D.inc x j) :
    (D.parallelLines i ∩ D.parallelLines j).card = D.lineDeficit i*D.lineDeficit j := by
  have hnot : j ∉ D.parallelLines i := by
    intro hj
    obtain ⟨x,hx⟩ := hmeet
    exact ((D.mem_parallelLines i j).mp hj).2 x hx
  have hdeg := D.intersection_degree_sum (D.parallelLines i) j
  rw [if_neg hnot] at hdeg
  simp only [zero_add] at hdeg
  have hinc := D.parallel_line_incidence i j
  have hmeet' : ∃ x, D.inc x j ∧ D.inc x i := by obtain ⟨x,hx⟩ := hmeet; exact ⟨x,hx.symm⟩
  rw [D.linePoints_inter_card hij.symm,if_pos hmeet'] at hinc
  have hp := D.label_partition_card (D.parallelLines i) j
  rw [if_neg hnot,D.parallel_card_eq_q_mul_deficit i hI hci] at hp
  simp only [add_zero] at hp
  have hkpos : 0 < D.lineDegree j := by
    obtain ⟨x,hx⟩ := hmeet
    exact Finset.card_pos.mpr ⟨x,(D.mem_linePoints j x).mpr hx.2⟩
  have hdj : D.lineDegree j-1 + D.lineDeficit j = q := by
    have hh := Nat.sub_add_cancel hcj
    change D.lineDeficit j + D.lineDegree j = q+1 at hh
    omega
  have hm := congrArg (fun n => n*D.lineDeficit i) hdj
  simp only [Nat.add_mul] at hm
  rw [hdeg] at hinc
  change (D.parallelLines i ∩ D.meetingLines j).card =
    (D.lineDegree j-1)*D.lineDeficit i at hinc
  rw [hinc] at hp
  rw [Nat.mul_comm (D.lineDeficit i) (D.lineDeficit j)]
  omega

/-- Source3.1(b), parallel indexed lines, in subtraction-free incidence form. -/
theorem common_parallel_balance_of_parallel (D : IndexedDesign q X I) {i j : I}
    (hI : Fintype.card I = q^2+q+1) (hci : D.lineDegree i ≤ q+1)
    (hpar : D.Parallel i j) :
    (D.parallelLines i ∩ D.parallelLines j).card + 1 + D.lineDegree j*D.lineDeficit i =
      q*D.lineDeficit i + D.lineDegree j := by
  have hj : j ∈ D.parallelLines i := (D.mem_parallelLines i j).mpr hpar
  have hdeg := D.intersection_degree_sum (D.parallelLines i) j
  rw [if_pos hj] at hdeg
  have hinc := D.parallel_line_incidence i j
  have hno : ¬∃ x, D.inc x j ∧ D.inc x i := by
    rintro ⟨x,hx⟩
    exact hpar.2 x hx.symm
  rw [D.linePoints_inter_card hpar.1.symm,if_neg hno] at hinc
  simp only [Nat.sub_zero] at hinc
  have hp := D.label_partition_card (D.parallelLines i) j
  rw [if_pos hj,D.parallel_card_eq_q_mul_deficit i hI hci] at hp
  rw [hdeg] at hinc
  change D.lineDegree j+(D.parallelLines i ∩ D.meetingLines j).card =
    D.lineDegree j*D.lineDeficit i at hinc
  omega

/-- Exact source3.1(b) integer formula, avoiding truncated subtraction. -/
theorem common_parallel_card_of_parallel_int (D : IndexedDesign q X I) {i j : I}
    (hI : Fintype.card I = q^2+q+1)
    (hci : D.lineDegree i ≤ q+1) (hcj : D.lineDegree j ≤ q+1) (hpar : D.Parallel i j) :
    ((D.parallelLines i ∩ D.parallelLines j).card:ℤ) =
      (q:ℤ)-1 + ((D.lineDeficit i:ℤ)-1)*((D.lineDeficit j:ℤ)-1) := by
  have hh := D.common_parallel_balance_of_parallel hI hci hpar
  have hhz : ((D.parallelLines i ∩ D.parallelLines j).card:ℤ)+1+
      (D.lineDegree j:ℤ)*D.lineDeficit i = (q:ℤ)*D.lineDeficit i + D.lineDegree j := by exact_mod_cast hh
  have hd : (D.lineDegree j:ℤ)+(D.lineDeficit j:ℤ)=(q:ℤ)+1 := by
    have h := Nat.sub_add_cancel hcj
    change D.lineDeficit j + D.lineDegree j = q+1 at h
    exact_mod_cast (show D.lineDegree j + D.lineDeficit j = q+1 by omega)
  linear_combination hhz - ((D.lineDeficit i:ℤ)-1)*hd

/-- Deficit-two specialization needed by the early-route triangle argument. -/
theorem common_parallel_card_deficit_two (D : IndexedDesign q X I) {i j : I}
    (hI : Fintype.card I = q^2+q+1)
    (hci : D.lineDegree i ≤ q+1) (hcj : D.lineDegree j ≤ q+1)
    (hpar : D.Parallel i j) (hdi : D.lineDeficit i = 2) :
    (D.parallelLines i ∩ D.parallelLines j).card + 2 = q+D.lineDeficit j := by
  have hh := D.common_parallel_balance_of_parallel hI hci hpar
  rw [hdi] at hh
  have hd := Nat.sub_add_cancel hcj
  change D.lineDeficit j + D.lineDegree j = q+1 at hd
  omega

#print axioms common_parallel_card_of_meet
#print axioms common_parallel_card_of_parallel_int
#print axioms common_parallel_card_deficit_two
#print axioms parallel_line_incidence
#print axioms label_partition_card
#print axioms outside_parallel_count_add
#print axioms sum_parallel_lineDegrees
end Erdos60.Embedding.IndexedDesign
