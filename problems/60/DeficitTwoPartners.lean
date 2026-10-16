import ParallelCounts
import EmbeddingParameters

/-! Actual indexed-design partners and local short-line bound, Metsch (1991)
Lemma6.2, printed p44. The original indexed line labels are retained.
Source PDF SHA256:
0fe0e7c6d7214480dc04f489b4fbb4bdb24d8bcebf2e75cb81ecc441c7959ad5.
No supplier for partners or cliques is assumed. -/
namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

/-- A full line has no parallel labels. With degree q excluded, every
parallel neighbor therefore has degree at most q-1. -/
theorem parallel_degree_le_pred (D : IndexedDesign q X I)
    (hI : Fintype.card I=q^2+q+1) (hcap : ∀ i, D.lineDegree i≤q+1)
    (hnone : ∀ i, D.lineDegree i≠q) {L H : I} (hLH : D.Parallel L H) :
    D.lineDegree H≤q-1 := by
  have hm : L∈D.parallelLines H := (D.mem_parallelLines _ _).mpr (D.parallel_symm hLH)
  have hp := Finset.card_pos.mpr ⟨L,hm⟩
  rw [D.parallel_card_eq_q_mul_deficit H hI (hcap H)] at hp
  have hc := hcap H
  have hn := hnone H
  unfold lineDeficit at hp
  have hfull : D.lineDegree H≠q+1 := by
    intro he
    simp only [he,Nat.sub_self,Nat.mul_zero] at hp
    omega
  omega

/-- The total degree gap from q-1 among the actual parallels of a
deficit-two line is exactly twice the excess missing-point budget. -/
theorem deficit_two_parallel_gap_sum (D : IndexedDesign q X I) (s : ℕ)
    (hq : 1≤q) (hI : Fintype.card I=q^2+q+1)
    (hX : Fintype.card X+s=q^2+q+1) (hbranch : q+2≤s)
    (hcap : ∀ i, D.lineDegree i≤q+1) (hnone : ∀ i, D.lineDegree i≠q)
    {L : I} (hL : D.lineDeficit L=2) :
    (∑ H∈D.parallelLines L, (q-1-D.lineDegree H))=2*(s-q-2) := by
  have hkL : D.lineDegree L+2=q+1 := by
    have hh := Nat.sub_add_cancel (hcap L)
    change D.lineDeficit L+D.lineDegree L=q+1 at hh
    omega
  have hkLX : D.lineDegree L≤Fintype.card X := Finset.card_le_univ _
  have hsum := D.sum_parallel_lineDegrees L
  rw [hL] at hsum
  have hc : (D.parallelLines L).card=2*q := by
    rw [D.parallel_card_eq_q_mul_deficit L hI (hcap L),hL,Nat.mul_comm]
  have hgap : (∑ H∈D.parallelLines L, (q-1-D.lineDegree H))+
      (∑ H∈D.parallelLines L, D.lineDegree H) = (D.parallelLines L).card*(q-1) := by
    rw [← Finset.sum_add_distrib]
    have he : ∀ H∈D.parallelLines L, q-1-D.lineDegree H+D.lineDegree H=q-1 := by
      intro H hH
      exact Nat.sub_add_cancel (D.parallel_degree_le_pred hI hcap hnone ((D.mem_parallelLines _ _).mp hH))
    rw [Finset.sum_congr rfl he]
    simp
  rw [hc,hsum] at hgap
  have hXsub := Nat.sub_add_cancel hkLX
  have hqsub : q-1+1=q := by omega
  have hs : s-q-2+q+2=s := by omega
  nlinarith

/-- Local source6.2(a), for any explicit cutoff, with the exact floor budget. -/
theorem deficit_two_short_parallel_card_mul (D : IndexedDesign q X I) (s e : ℕ)
    (hq : 1≤q) (he : 1≤e) (heq : e≤q)
    (hI : Fintype.card I=q^2+q+1) (hX : Fintype.card X+s=q^2+q+1)
    (hbranch : q+2≤s) (hcap : ∀ i, D.lineDegree i≤q+1)
    (hnone : ∀ i, D.lineDegree i≠q) {L : I} (hL : D.lineDeficit L=2) :
    ((D.parallelLines L).filter (fun H=>D.lineDegree H≤q-e)).card*(e-1) ≤ 2*(s-q-2) := by
  let S := (D.parallelLines L).filter (fun H=>D.lineDegree H≤q-e)
  have hs : ∀ H∈S, e-1≤q-1-D.lineDegree H := by
    intro H hH
    have hh := (Finset.mem_filter.mp hH).2
    omega
  calc
    _ = ∑ H∈S, (e-1) := by simp [S]
    _ ≤ ∑ H∈S, (q-1-D.lineDegree H) := Finset.sum_le_sum hs
    _ ≤ ∑ H∈D.parallelLines L, (q-1-D.lineDegree H) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun H hH hn=>Nat.zero_le _)
    _ = _ := D.deficit_two_parallel_gap_sum s hq hI hX hbranch hcap hnone hL

/-- The actual short parallels of a deficit-two line obey the frozen allowance. -/
theorem deficit_two_short_parallel_le_allowance (D : IndexedDesign q X I) (s : ℕ)
    (hq : 10^8≤q) (hI : Fintype.card I=q^2+q+1)
    (hX : Fintype.card X+s=q^2+q+1) (hbranch : q+2≤s)
    (hcap : ∀ i, D.lineDegree i≤q+1) (hnone : ∀ i, D.lineDegree i≠q)
    {L : I} (hL : D.lineDeficit L=2) :
    ((D.parallelLines L).filter (fun H=>D.lineDegree H≤q-Parameters.cutoff q)).card ≤
      Parameters.allowance q s := by
  have he := Parameters.cutoff_bounds q hq
  have hem : 0<Parameters.cutoff q-1 := by omega
  have heq : Parameters.cutoff q≤q := by omega
  apply (Nat.le_div_iff_mul_le hem).mpr
  exact D.deficit_two_short_parallel_card_mul s (Parameters.cutoff q) (by omega) (by omega)
    heq hI hX hbranch hcap hnone hL

/-- A line parallel to a deficit-two line meets exactly its own degree many
other parallel labels. This is an actual counted meeting set. -/
theorem parallel_meeting_card_deficit_two (D : IndexedDesign q X I) {L H : I}
    (hL : D.lineDeficit L=2) (hLH : D.Parallel L H) :
    (D.parallelLines L∩D.meetingLines H).card=D.lineDegree H := by
  have hm : H∈D.parallelLines L := (D.mem_parallelLines _ _).mpr hLH
  have hw := D.parallel_line_incidence L H
  have hd := D.intersection_degree_sum (D.parallelLines L) H
  have hno : ¬∃ x, D.inc x H∧D.inc x L := by
    rintro ⟨x,hx⟩
    exact hLH.2 x hx.symm
  rw [D.linePoints_inter_card hLH.1.symm,if_neg hno] at hw
  rw [if_pos hm] at hd
  rw [Nat.sub_zero,hL] at hw
  change (∑ K∈D.parallelLines L, (D.linePoints K∩D.linePoints H).card)=D.lineDegree H*2 at hw
  omega

/-- Actual source6.2(b). If no meeting parallel had deficit two, the gap
spent by H together with all its meeting parallels would exceed the total. -/
theorem deficit_two_parallel_partner (D : IndexedDesign q X I) (s : ℕ)
    (hq : 1≤q) (hI : Fintype.card I=q^2+q+1)
    (hX : Fintype.card X+s=q^2+q+1) (hbranch : q+2≤s)
    (hcap : ∀ i, D.lineDegree i≤q+1) (hnone : ∀ i, D.lineDegree i≠q)
    {L H : I} (hL : D.lineDeficit L=2) (hsmall : 2*(s-q-2)<q-1)
    (hLH : D.Parallel L H) :
    ∃ K, D.Parallel L K ∧ D.lineDeficit K=2 ∧ K∈D.meetingLines H := by
  classical
  let J := D.parallelLines L∩D.meetingLines H
  have hJ : J.card=D.lineDegree H := D.parallel_meeting_card_deficit_two hL hLH
  by_contra hn
  have hnoneJ : ∀ K∈J, D.lineDeficit K≠2 := by
    intro K hK hd
    exact hn ⟨K,(D.mem_parallelLines _ _).mp (Finset.mem_inter.mp hK).1,hd,
      (Finset.mem_inter.mp hK).2⟩
  have hgap : ∀ K∈J, 1≤q-1-D.lineDegree K := by
    intro K hK
    have hc := D.parallel_degree_le_pred hI hcap hnone
      ((D.mem_parallelLines _ _).mp (Finset.mem_inter.mp hK).1)
    have hd := hnoneJ K hK
    unfold lineDeficit at hd
    omega
  have hJsum : J.card ≤ ∑ K∈J, (q-1-D.lineDegree K) := by
    calc
      _ = ∑ K∈J, (1:ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum hgap
  have hHnot : H∉J := by
    intro hm
    exact ((D.mem_meetingLines H H).mp (Finset.mem_inter.mp hm).2).1 rfl
  have hsub : insert H J ⊆ D.parallelLines L := by
    intro K hK
    rcases Finset.mem_insert.mp hK with he | hJ
    · subst K; exact (D.mem_parallelLines _ _).mpr hLH
    · exact (Finset.mem_inter.mp hJ).1
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun K hK hn=>Nat.zero_le (q-1-D.lineDegree K))
  rw [Finset.sum_insert hHnot,D.deficit_two_parallel_gap_sum s hq hI hX hbranch hcap hnone hL] at hs
  have hc := D.parallel_degree_le_pred hI hcap hnone hLH
  have he := Nat.sub_add_cancel hc
  rw [hJ] at hJsum
  omega

/-- Endpoint numerical specialization; the partner follows from the original
missing-point budget, not an extra small-gap hypothesis. -/
theorem deficit_two_parallel_partner_large (D : IndexedDesign q X I) (s : ℕ)
    (hq : 10^8≤q) (hs : 500*s≤501*q)
    (hI : Fintype.card I=q^2+q+1) (hX : Fintype.card X+s=q^2+q+1)
    (hbranch : q+2≤s) (hcap : ∀ i, D.lineDegree i≤q+1)
    (hnone : ∀ i, D.lineDegree i≠q) {L H : I}
    (hL : D.lineDeficit L=2) (hLH : D.Parallel L H) :
    ∃ K, D.Parallel L K ∧ D.lineDeficit K=2 ∧ K∈D.meetingLines H := by
  apply D.deficit_two_parallel_partner s (by omega) hI hX hbranch hcap hnone hL ?_ hLH
  omega

#print axioms deficit_two_short_parallel_le_allowance
#print axioms deficit_two_parallel_partner
#print axioms deficit_two_parallel_partner_large
end Erdos60.Embedding.IndexedDesign
