import IndexedDesign

namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

noncomputable def parallelLines (D : IndexedDesign q X I) (i : I) : Finset I :=
  Finset.univ.filter (D.Parallel i)

noncomputable def meetingLines (D : IndexedDesign q X I) (i : I) : Finset I :=
  Finset.univ.filter (fun j => j ≠ i ∧ ∃ x, D.inc x i ∧ D.inc x j)

@[simp] theorem mem_parallelLines (D : IndexedDesign q X I) (i j : I) :
    j ∈ D.parallelLines i ↔ D.Parallel i j := by simp [parallelLines]
@[simp] theorem mem_meetingLines (D : IndexedDesign q X I) (i j : I) :
    j ∈ D.meetingLines i ↔ j ≠ i ∧ ∃ x, D.inc x i ∧ D.inc x j := by simp [meetingLines]

theorem lineDegree_eq_sum (D : IndexedDesign q X I) (i : I) :
    D.lineDegree i = ∑ x : X, if D.inc x i then 1 else 0 := by
  simp [lineDegree,linePoints]

theorem pointDegree_eq_sum (D : IndexedDesign q X I) (x : X) :
    (∑ i : I, if D.inc x i then 1 else 0) = q+1 := by
  simpa [pointLines] using D.card_pointLines x

/-- Literal indexed incidence double count; zero/singleton line labels remain counted. -/
theorem sum_lineDegrees (D : IndexedDesign q X I) :
    (∑ i : I, D.lineDegree i) = Fintype.card X * (q+1) := by
  simp_rw [D.lineDegree_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [D.pointDegree_eq_sum]
  simp

/-- Each point on a fixed line has exactly q other indexed lines through it. -/
theorem card_other_pointLines (D : IndexedDesign q X I) {x : X} {i : I} (hxi : D.inc x i) :
    Fintype.card {j : I // D.inc x j ∧ j ≠ i} = q := by
  have he : Finset.univ.filter (fun j => D.inc x j ∧ j ≠ i) = (D.pointLines x).erase i := by
    ext j; simp [and_comm]
  rw [Fintype.card_subtype,he,Finset.card_erase_of_mem ((D.mem_pointLines x i).mpr hxi),D.card_pointLines]
  omega

/-- Actual indexed lines meeting a fixed line, counted without identifying supports. -/
theorem card_meetingLines (D : IndexedDesign q X I) (i : I) :
    (D.meetingLines i).card = D.lineDegree i * q := by
  let T := (x : ↥(D.linePoints i)) × {j : I // D.inc x.val j ∧ j ≠ i}
  let f : T → ↥(D.meetingLines i) := fun p =>
    ⟨p.2.val,(D.mem_meetingLines i p.2.val).mpr
      ⟨p.2.property.2,p.1.val,(D.mem_linePoints i p.1.val).mp p.1.property,p.2.property.1⟩⟩
  have hi : Function.Injective f := by
    intro p r h
    have hj : p.2.val = r.2.val := congrArg Subtype.val h
    have hx : p.1.val = r.1.val := D.intersection_unique p.2.property.2
      p.2.property.1 (hj ▸ r.2.property.1)
      ((D.mem_linePoints i p.1.val).mp p.1.property)
      ((D.mem_linePoints i r.1.val).mp r.1.property)
    cases p with | mk x j =>
      cases r with | mk y k =>
        have hxy : x=y := Subtype.ext hx
        subst y
        have hjk : j=k := Subtype.ext hj
        subst k
        rfl
  have hs : Function.Surjective f := by
    intro j
    obtain ⟨hji,x,hxi,hxj⟩ := (D.mem_meetingLines i j.val).mp j.property
    refine ⟨⟨⟨x,(D.mem_linePoints i x).mpr hxi⟩,⟨j.val,hxj,hji⟩⟩,?_⟩
    apply Subtype.ext
    rfl
  have hc := Fintype.card_of_bijective ⟨hi,hs⟩
  have hT : Fintype.card T = D.lineDegree i*q := by
    simp only [T,Fintype.card_sigma]
    simp_rw [D.card_other_pointLines ((D.mem_linePoints i _).mp (Subtype.property _))]
    simp [lineDegree]
  rw [hT,Fintype.card_coe] at hc
  exact hc.symm

/-- Source Lemma3.1(a), before rewriting in deficit notation: all labels split
into the fixed line, the q*k meeting labels, and the parallel labels. -/
theorem parallel_card_identity (D : IndexedDesign q X I) (i : I) :
    (D.parallelLines i).card + q*D.lineDegree i + 1 = Fintype.card I := by
  have he : D.parallelLines i ∪ D.meetingLines i = Finset.univ.erase i := by
    ext j
    simp only [Finset.mem_union,D.mem_parallelLines,D.mem_meetingLines,Finset.mem_erase,
      Finset.mem_univ,and_true]
    constructor
    · rintro (⟨hij,h⟩ | ⟨hji,h⟩)
      · exact hij.symm
      · exact hji
    · intro hji
      by_cases hmeet : ∃ x, D.inc x i ∧ D.inc x j
      · exact Or.inr ⟨hji,hmeet⟩
      · exact Or.inl ⟨hji.symm,by simpa only [not_exists] using hmeet⟩
  have hd : Disjoint (D.parallelLines i) (D.meetingLines i) := by
    apply Finset.disjoint_left.mpr
    intro j hp hm
    obtain ⟨hne,hno⟩ := (D.mem_parallelLines i j).mp hp
    obtain ⟨_,x,hxi,hxj⟩ := (D.mem_meetingLines i j).mp hm
    exact hno x ⟨hxi,hxj⟩
  have hc := Finset.card_union_of_disjoint hd
  rw [he,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,D.card_meetingLines] at hc
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [Nat.mul_comm (D.lineDegree i) q] at hc
  omega

theorem pointLines_inter_card (D : IndexedDesign q X I) (x y : X) :
    (D.pointLines x ∩ D.pointLines y).card = if x=y then q+1 else 1 := by
  by_cases hxy : x=y
  · subst y
    simp
  · rw [if_neg hxy]
    apply Finset.card_eq_one_iff_existsUnique.mpr
    simpa only [Finset.mem_inter,D.mem_pointLines] using D.unique_join x y hxy

/-- Indexed incidence Gram double count, including all zero/singleton labels. -/
theorem sum_lineDegrees_sq (D : IndexedDesign q X I) :
    (∑ i : I, (D.lineDegree i)^2) = Fintype.card X * (Fintype.card X + q) := by
  have hbool : ∀ x y : X, (∑ i : I, (if D.inc x i then 1 else 0)*(if D.inc y i then 1 else 0)) =
      (D.pointLines x ∩ D.pointLines y).card := by
    intro x y
    have he : D.pointLines x ∩ D.pointLines y = Finset.univ.filter (fun i => D.inc x i ∧ D.inc y i) := by
      ext i; simp
    rw [he]
    have heach : ∀ i : I, (if D.inc x i then 1 else 0)*(if D.inc y i then 1 else 0) =
        (if D.inc x i ∧ D.inc y i then (1:ℕ) else 0) := by
      intro i
      split_ifs <;> simp_all
    simp_rw [heach]
    simp
  have hgram : (∑ i : I, (D.lineDegree i)^2) =
      ∑ x : X, ∑ y : X, (D.pointLines x ∩ D.pointLines y).card := by
    simp_rw [pow_two,D.lineDegree_eq_sum,Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    simp_rw [hbool]
  rw [hgram]
  have hrow : ∀ x : X, (∑ y : X, (D.pointLines x ∩ D.pointLines y).card) = Fintype.card X+q := by
    intro x
    simp_rw [D.pointLines_inter_card]
    rw [← Finset.add_sum_erase Finset.univ (fun y : X => if x=y then q+1 else 1) (Finset.mem_univ x)]
    have hh : (∑ y ∈ Finset.univ.erase x, if x=y then q+1 else 1) = (Finset.univ.erase x).card := by
      calc
        _ = ∑ y ∈ Finset.univ.erase x, 1 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [if_neg (Finset.mem_erase.mp hy).1.symm]
        _ = _ := by simp
    rw [hh]
    simp only [if_true,Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ]
    have hxcard : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
    omega
  simp_rw [hrow]
  simp

noncomputable def intDeficit (D : IndexedDesign q X I) (i : I) : ℤ := (q:ℤ)+1-D.lineDegree i

/-- First deficit moment, source3.2 with the fixed original indexed-line count. -/
theorem sum_intDeficit (D : IndexedDesign q X I) (s : ℕ)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1) :
    (∑ i : I, D.intDeficit i) = (s:ℤ)*(q+1) := by
  have hk : (∑ i : I, (D.lineDegree i:ℤ)) = (Fintype.card X:ℤ)*(q+1) := by
    exact_mod_cast D.sum_lineDegrees
  have hiZ : (Fintype.card I:ℤ) = (q:ℤ)^2+q+1 := by exact_mod_cast hI
  have hxZ : (Fintype.card X:ℤ)+s = (q:ℤ)^2+q+1 := by exact_mod_cast hX
  simp only [intDeficit,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hk]
  nlinarith

/-- Second deficit moment, source3.2, from the proved incidence Gram count. -/
theorem sum_intDeficit_sq (D : IndexedDesign q X I) (s : ℕ)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1) :
    (∑ i : I, (D.intDeficit i)^2) = (s:ℤ)*(q+s) := by
  have hk : (∑ i : I, (D.lineDegree i:ℤ)) = (Fintype.card X:ℤ)*(q+1) := by
    exact_mod_cast D.sum_lineDegrees
  have hk2 : (∑ i : I, (D.lineDegree i:ℤ)^2) = (Fintype.card X:ℤ)*(Fintype.card X+q) := by
    exact_mod_cast D.sum_lineDegrees_sq
  have hiZ : (Fintype.card I:ℤ) = (q:ℤ)^2+q+1 := by exact_mod_cast hI
  have hxZ : (Fintype.card X:ℤ)+s = (q:ℤ)^2+q+1 := by exact_mod_cast hX
  have hexp : ∀ i : I, (D.intDeficit i)^2 = ((q:ℤ)+1)^2 - 2*((q:ℤ)+1)*D.lineDegree i + (D.lineDegree i:ℤ)^2 := by
    intro i
    simp only [intDeficit]
    ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hk,hk2]
  nlinarith [sq_nonneg ((Fintype.card X:ℤ)+s-((q:ℤ)^2+q+1))]

/-- Source3.3 weighted moment. The exact integer identity itself does not
need the no-deficit-one hypothesis; that hypothesis is used for its inequalities. -/
theorem sum_intDeficit_mul_sub_two (D : IndexedDesign q X I) (s : ℕ)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1) :
    (∑ i : I, D.intDeficit i*(D.intDeficit i-2)) = (s:ℤ)*(s-q-2) := by
  have he : ∀ i : I, D.intDeficit i*(D.intDeficit i-2) = (D.intDeficit i)^2-2*D.intDeficit i := by
    intro i; ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,D.sum_intDeficit_sq s hI hX,D.sum_intDeficit s hI hX]
  ring

theorem exists_point_off_line (D : IndexedDesign q X I) (hq : 0 < q)
    (hI : Fintype.card I = q^2+q+1) (hX : q+1 < Fintype.card X) (i : I) :
    ∃ x, ¬D.inc x i := by
  by_contra hnone
  have hall : ∀ x, D.inc x i := by simpa only [not_exists,not_not] using hnone
  have hk : D.lineDegree i = Fintype.card X := by simp [lineDegree,linePoints,hall]
  have hh := D.parallel_card_identity i
  rw [hk,hI] at hh
  nlinarith

/-- An outside point labels the line's points by distinct lines through it. -/
theorem lineDegree_le_of_outside (D : IndexedDesign q X I) {i : I} {x : X}
    (hxi : ¬D.inc x i) : D.lineDegree i ≤ q+1 := by
  have hex : ∀ y : ↥(D.linePoints i), ∃ j : ↥(D.pointLines x), D.inc y.val j.val := by
    intro y
    have hxy : x ≠ y.val := by intro h; exact hxi (h.symm ▸ (D.mem_linePoints i y.val).mp y.property)
    obtain ⟨j,hj,_⟩ := D.unique_join x y.val hxy
    exact ⟨⟨j,(D.mem_pointLines x j).mpr hj.1⟩,hj.2⟩
  choose f hf using hex
  have hi : Function.Injective f := by
    intro y z h
    have hji : (f y).val ≠ i := by intro he; exact hxi (he ▸ (D.mem_pointLines x (f y).val).mp (f y).property)
    apply Subtype.ext
    exact D.intersection_unique hji (hf y) (by rw [h]; exact hf z)
      ((D.mem_linePoints i y.val).mp y.property) ((D.mem_linePoints i z.val).mp z.property)
  have hh := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,D.card_pointLines,lineDegree] using hh

/-- The density hypotheses derive the needed nonnegative deficits; no cap field is assumed. -/
theorem lineDegree_le (D : IndexedDesign q X I) (hq : 0 < q)
    (hI : Fintype.card I = q^2+q+1) (hX : q+1 < Fintype.card X) (i : I) :
    D.lineDegree i ≤ q+1 := by
  obtain ⟨x,hx⟩ := D.exists_point_off_line hq hI hX i
  exact D.lineDegree_le_of_outside hx

theorem intDeficit_eq_nat (D : IndexedDesign q X I) {i : I} (hcap : D.lineDegree i ≤ q+1) :
    D.intDeficit i = (D.lineDeficit i : ℤ) := by
  simp only [intDeficit,lineDeficit]
  rw [Nat.cast_sub hcap]
  push_cast
  rfl

/-- Source3.1(a) in natural deficit notation at the fixed original line count. -/
theorem parallel_card_eq_q_mul_deficit (D : IndexedDesign q X I) (i : I)
    (hI : Fintype.card I = q^2+q+1) (hcap : D.lineDegree i ≤ q+1) :
    (D.parallelLines i).card = q*D.lineDeficit i := by
  have hh := D.parallel_card_identity i
  rw [hI] at hh
  have hd : D.lineDeficit i + D.lineDegree i = q+1 := Nat.sub_add_cancel hcap
  nlinarith

#print axioms lineDegree_le
#print axioms parallel_card_eq_q_mul_deficit
#print axioms sum_intDeficit
#print axioms sum_intDeficit_sq
#print axioms sum_intDeficit_mul_sub_two
#print axioms sum_lineDegrees_sq
#print axioms sum_lineDegrees
#print axioms parallel_card_identity
end Erdos60.Embedding.IndexedDesign
