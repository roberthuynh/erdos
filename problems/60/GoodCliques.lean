import BasicCounts
import ParallelCounts
import ParallelTriangle
import EmbeddingParameters
import DeficitTwoPartners

/-! Actual finite long-line cliques in the selected early Metsch route.
Definitions do not contain existence, completion, or source-theorem promises. -/
namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped BigOperators Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

def Short (D : IndexedDesign q X I) (e : ℕ) (i : I) : Prop := D.lineDegree i ≤ q-e
def Long (D : IndexedDesign q X I) (e : ℕ) (i : I) : Prop := q-e < D.lineDegree i
noncomputable def shortLines (D : IndexedDesign q X I) (e : ℕ) : Finset I :=
  Finset.univ.filter (D.Short e)
noncomputable def longLines (D : IndexedDesign q X I) (e : ℕ) : Finset I :=
  Finset.univ.filter (D.Long e)

def ParallelClique (D : IndexedDesign q X I) (e : ℕ) (C : Finset I) : Prop :=
  (∀ i ∈ C, D.Long e i) ∧ (∀ i ∈ C, ∀ j ∈ C, i ≠ j → D.Parallel i j)
def MaximalParallelClique (D : IndexedDesign q X I) (e : ℕ) (C : Finset I) : Prop :=
  D.ParallelClique e C ∧ ∀ M, D.ParallelClique e M → C ⊆ M → M = C
def GoodClique (D : IndexedDesign q X I) (e a : ℕ) (C : Finset I) : Prop :=
  D.MaximalParallelClique e C ∧ q-a ≤ C.card ∧ ∃ i ∈ C, D.lineDeficit i = 2

@[simp] theorem mem_shortLines (D : IndexedDesign q X I) (e : ℕ) (i : I) :
    i ∈ D.shortLines e ↔ D.Short e i := by simp [shortLines]
@[simp] theorem mem_longLines (D : IndexedDesign q X I) (e : ℕ) (i : I) :
    i ∈ D.longLines e ↔ D.Long e i := by simp [longLines]

theorem exists_maximal_parallel_extension (D : IndexedDesign q X I) (e : ℕ)
    (C : Finset I) (hC : D.ParallelClique e C) :
    ∃ M, C ⊆ M ∧ D.MaximalParallelClique e M := by
  classical
  let F := (Finset.univ : Finset I).powerset.filter fun M => C ⊆ M ∧ D.ParallelClique e M
  have hCF : C ∈ F := by simp [F,hC]
  obtain ⟨M,hMF,hmax⟩ := Finset.exists_max_image F Finset.card ⟨C,hCF⟩
  have hm := (Finset.mem_filter.mp hMF).2
  refine ⟨M,hm.1,hm.2,?_⟩
  intro N hN hMN
  have hNF : N ∈ F := by simp [F,hm.1.trans hMN,hN]
  exact (Finset.eq_of_subset_of_card_le hMN (hmax N hNF)).symm

/-- Short lines have large nonnegative moment weight. -/
theorem short_moment_lower (D : IndexedDesign q X I) (e : ℕ) (he : 1 ≤ e)
    (heq : e ≤ q) (i : I) (hi : D.Short e i) :
    (e : ℤ)^2-1 ≤ D.intDeficit i*(D.intDeficit i-2) := by
  have hdeg : D.lineDegree i ≤ q-e := hi
  have hn : e + D.lineDegree i ≤ q := by omega
  have hz : (e : ℤ)+D.lineDegree i ≤ q := by exact_mod_cast hn
  unfold intDeficit
  nlinarith [mul_nonneg
    (show 0 ≤ ((q : ℤ)+1-D.lineDegree i)-((e : ℤ)+1) by linarith)
    (show 0 ≤ ((q : ℤ)+1-D.lineDegree i)+(e : ℤ)-1 by
      have heZ : (1 : ℤ) ≤ e := by exact_mod_cast he
      linarith)]

/-- Actual source short-line sparsity, from the actual indexed-design moment. -/
theorem shortLines_card_le (D : IndexedDesign q X I) (s e : ℕ)
    (he : 1 ≤ e) (heq : e ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q)
    (hnum : (s : ℤ)*(s-q-2) < ((q-e+1 : ℕ) : ℤ)*((e : ℤ)^2-1)) :
    (D.shortLines e).card ≤ q-e := by
  have hnonneg : ∀ i, 0 ≤ D.intDeficit i*(D.intDeficit i-2) := by
    intro i
    have hc := hcap i
    have hn := hnone i
    unfold intDeficit
    by_cases hz : D.lineDegree i = q+1
    · simp [hz]
    · have hsmall : D.lineDegree i ≤ q-1 := by omega
      have hd : (D.lineDegree i : ℤ) ≤ (q : ℤ)-1 := by
        have : D.lineDegree i + 1 ≤ q := by omega
        have hiZ : (D.lineDegree i : ℤ)+1 ≤ q := by exact_mod_cast this
        omega
      nlinarith
  have hsum : ((D.shortLines e).card : ℤ)*((e : ℤ)^2-1) ≤ (s : ℤ)*(s-q-2) := by
    calc
      _ = ∑ i ∈ D.shortLines e, ((e : ℤ)^2-1) := by simp; ring
      _ ≤ ∑ i ∈ D.shortLines e, D.intDeficit i*(D.intDeficit i-2) :=
        Finset.sum_le_sum (fun i hi => D.short_moment_lower e he heq i ((D.mem_shortLines e i).mp hi))
      _ ≤ ∑ i : I, D.intDeficit i*(D.intDeficit i-2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i hi hnot => hnonneg i)
      _ = _ := D.sum_intDeficit_mul_sub_two s hI hX
  by_contra hn
  have hc : q-e+1 ≤ (D.shortLines e).card := by omega
  have hcz : ((q-e+1 : ℕ) : ℤ) ≤ (D.shortLines e).card := by exact_mod_cast hc
  have hz : 0 ≤ (e : ℤ)^2-1 := by
    have heZ : (1 : ℤ) ≤ e := by exact_mod_cast he
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hcz hz
  linarith

/-- Every long line has an actual point incident with no short line. -/
theorem exists_clean_point_on_long (D : IndexedDesign q X I) (e : ℕ)
    (_heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (i : I) (hi : D.Long e i) :
    ∃ x, D.inc x i ∧ ∀ j, D.inc x j → D.Long e j := by
  classical
  let U := (D.shortLines e).biUnion fun j => D.linePoints i ∩ D.linePoints j
  have hsmall : U.card ≤ (D.shortLines e).card := by
    calc
      _ ≤ ∑ j ∈ D.shortLines e, (D.linePoints i ∩ D.linePoints j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ D.shortLines e, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjshort := (D.mem_shortLines e j).mp hj
        have hij : i ≠ j := by intro h; subst j; exact (not_lt_of_ge hjshort) hi
        apply Finset.card_le_one.mpr
        intro x hx y hy
        obtain ⟨hxi,hxj⟩ := Finset.mem_inter.mp hx
        obtain ⟨hyi,hyj⟩ := Finset.mem_inter.mp hy
        exact D.intersection_unique hij ((D.mem_linePoints _ _).mp hxi)
          ((D.mem_linePoints _ _).mp hyi) ((D.mem_linePoints _ _).mp hxj)
          ((D.mem_linePoints _ _).mp hyj)
      _ = _ := by simp
  have hnot : ¬D.linePoints i ⊆ U := by
    intro hsub
    have hc := Finset.card_le_card hsub
    have hlong : q-e < (D.linePoints i).card := hi
    omega
  obtain ⟨x,hx,hxU⟩ := Finset.not_subset.mp hnot
  refine ⟨x,(D.mem_linePoints _ _).mp hx,?_⟩
  intro j hxj
  by_contra hj
  have hjs : j ∈ D.shortLines e := by
    apply (D.mem_shortLines e j).mpr
    unfold Short Long at *
    omega
  exact hxU (Finset.mem_biUnion.mpr ⟨j,hjs,Finset.mem_inter.mpr
    ⟨hx,(D.mem_linePoints _ _).mpr hxj⟩⟩)

/-- A sufficiently large actual parallel candidate containing a deficit-two
line extends to an actual good maximal clique. -/
theorem exists_good_clique_extension (D : IndexedDesign q X I) (e a : ℕ)
    (C : Finset I) (hC : D.ParallelClique e C) (hsize : q-a ≤ C.card)
    (hdef : ∃ i ∈ C, D.lineDeficit i = 2) :
    ∃ M, C ⊆ M ∧ D.GoodClique e a M := by
  obtain ⟨M,hCM,hM⟩ := D.exists_maximal_parallel_extension e C hC
  obtain ⟨i,hi,hdi⟩ := hdef
  exact ⟨M,hCM,hM,hsize.trans (Finset.card_le_card hCM),i,hCM hi,hdi⟩

/-- Actual source6.4(a) set inclusion before applying the common-parallel count. -/
theorem clique_inter_subset_common_parallel (D : IndexedDesign q X I) (e : ℕ)
    (C M : Finset I) (hC : D.ParallelClique e C) (hM : D.ParallelClique e M)
    {H K : I} (hHC : H ∈ C) (hKM : K ∈ M)
    (hHK : H ≠ K) (hmeet : ∃ x, D.inc x H ∧ D.inc x K) :
    C ∩ M ⊆ D.parallelLines H ∩ D.parallelLines K := by
  intro J hJ
  obtain ⟨hJC,hJM⟩ := Finset.mem_inter.mp hJ
  obtain ⟨x,hxH,hxK⟩ := hmeet
  have hJH : J ≠ H := by
    intro he
    subst J
    exact (hM.2 H hJM K hKM hHK).2 x ⟨hxH,hxK⟩
  have hJK : J ≠ K := by
    intro he
    subst J
    exact (hC.2 K hJC H hHC hHK.symm).2 x ⟨hxK,hxH⟩
  exact Finset.mem_inter.mpr ⟨(D.mem_parallelLines _ _).mpr
    (hC.2 H hHC J hJC (Ne.symm hJH)),(D.mem_parallelLines _ _).mpr
    (hM.2 K hKM J hJM (Ne.symm hJK))⟩

/-- Actual source6.4(b) set containment, including both distinguished labels. -/
theorem clique_union_subset_common_parallel (D : IndexedDesign q X I) (e : ℕ)
    (C M : Finset I) (hC : D.ParallelClique e C) (hM : D.ParallelClique e M)
    {H K : I} (hHC : H ∈ C) (hHM : H ∈ M) (hKC : K ∈ C) (hKM : K ∈ M) :
    C ∪ M ⊆ {H,K} ∪ (D.parallelLines H ∩ D.parallelLines K) := by
  intro J hJ
  by_cases hJH : J = H
  · simp [hJH]
  by_cases hJK : J = K
  · simp [hJK]
  apply Finset.mem_union_right
  apply Finset.mem_inter.mpr
  rcases Finset.mem_union.mp hJ with hJC | hJM
  · exact ⟨(D.mem_parallelLines _ _).mpr (hC.2 H hHC J hJC (Ne.symm hJH)),
      (D.mem_parallelLines _ _).mpr (hC.2 K hKC J hJC (Ne.symm hJK))⟩
  · exact ⟨(D.mem_parallelLines _ _).mpr (hM.2 H hHM J hJM (Ne.symm hJH)),
      (D.mem_parallelLines _ _).mpr (hM.2 K hKM J hJM (Ne.symm hJK))⟩

/-- Distinct actual maximal parallel cliques have distinct meeting witness
lines. Otherwise their actual union is a larger parallel clique. -/
theorem distinct_maximal_cliques_meeting_witness (D : IndexedDesign q X I) (e : ℕ)
    (C M : Finset I) (hC : D.MaximalParallelClique e C)
    (hM : D.MaximalParallelClique e M) (hne : C ≠ M) :
    ∃ H ∈ C, ∃ K ∈ M, H ≠ K ∧ ∃ x, D.inc x H ∧ D.inc x K := by
  classical
  by_contra hn
  have hcross : ∀ H ∈ C, ∀ K ∈ M, H ≠ K → D.Parallel H K := by
    intro H hH K hK hHK
    refine ⟨hHK,?_⟩
    intro x hx
    exact hn ⟨H,hH,K,hK,hHK,x,hx⟩
  have hUnion : D.ParallelClique e (C ∪ M) := by
    constructor
    · intro H hH
      rcases Finset.mem_union.mp hH with hH | hH
      · exact hC.1.1 H hH
      · exact hM.1.1 H hH
    · intro H hH K hK hHK
      rcases Finset.mem_union.mp hH with hHC | hHM <;>
        rcases Finset.mem_union.mp hK with hKC | hKM
      · exact hC.1.2 H hHC K hKC hHK
      · exact hcross H hHC K hKM hHK
      · exact D.parallel_symm (hcross K hKC H hHM hHK.symm)
      · exact hM.1.2 H hHM K hKM hHK
  have hUC := hC.2 (C ∪ M) hUnion Finset.subset_union_left
  have hUM := hM.2 (C ∪ M) hUnion Finset.subset_union_right
  exact hne (hUC.symm.trans hUM)

theorem long_deficit_le (D : IndexedDesign q X I) (e : ℕ) {i : I}
    (hi : D.Long e i) : D.lineDeficit i ≤ e := by
  unfold Long lineDeficit at *
  omega

/-- Source6.4(a), with the actual common-parallel count supplied by source3.1. -/
theorem clique_inter_card_le (D : IndexedDesign q X I) (e : ℕ)
    (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (C M : Finset I) (hC : D.ParallelClique e C) (hM : D.ParallelClique e M)
    {H K : I} (hHC : H ∈ C) (hKM : K ∈ M) (hHK : H ≠ K)
    (hmeet : ∃ x, D.inc x H ∧ D.inc x K) : (C ∩ M).card ≤ e^2 := by
  have hs := Finset.card_le_card
    (D.clique_inter_subset_common_parallel e C M hC hM hHC hKM hHK hmeet)
  rw [D.common_parallel_card_of_meet hI (hcap H) (hcap K) hHK hmeet] at hs
  have hH := D.long_deficit_le e (hC.1 H hHC)
  have hK := D.long_deficit_le e (hM.1 K hKM)
  exact hs.trans (by nlinarith [Nat.mul_self_le_mul_self hH,Nat.mul_le_mul_right (D.lineDeficit H) hK])

/-- Source6.4(b), in integer form avoiding truncated negative deficits. -/
theorem clique_union_card_le (D : IndexedDesign q X I) (e : ℕ)
    (he : 1 ≤ e) (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (C M : Finset I) (hC : D.ParallelClique e C) (hM : D.ParallelClique e M)
    {H K : I} (hHC : H ∈ C) (hHM : H ∈ M) (hKC : K ∈ C) (hKM : K ∈ M)
    (hHK : H ≠ K) : ((C ∪ M).card : ℤ) ≤ (q : ℤ)+1+((e : ℤ)-1)^2 := by
  have hpar := hC.2 H hHC K hKC hHK
  have hps : K ∈ D.parallelLines H := (D.mem_parallelLines _ _).mpr hpar
  have hqs : H ∈ D.parallelLines K := (D.mem_parallelLines _ _).mpr (D.parallel_symm hpar)
  have hposH := Finset.card_pos.mpr ⟨K,hps⟩
  have hposK := Finset.card_pos.mpr ⟨H,hqs⟩
  rw [D.parallel_card_eq_q_mul_deficit H hI (hcap H)] at hposH
  rw [D.parallel_card_eq_q_mul_deficit K hI (hcap K)] at hposK
  have hdH : 1 ≤ D.lineDeficit H := by nlinarith
  have hdK : 1 ≤ D.lineDeficit K := by nlinarith
  have heH := D.long_deficit_le e (hC.1 H hHC)
  have heK := D.long_deficit_le e (hC.1 K hKC)
  have hprod : ((D.lineDeficit H : ℤ)-1)*((D.lineDeficit K : ℤ)-1) ≤ ((e : ℤ)-1)^2 := by
    have hh : (1 : ℤ) ≤ D.lineDeficit H := by exact_mod_cast hdH
    have hk : (1 : ℤ) ≤ D.lineDeficit K := by exact_mod_cast hdK
    have hH : (D.lineDeficit H : ℤ) ≤ e := by exact_mod_cast heH
    have hK : (D.lineDeficit K : ℤ) ≤ e := by exact_mod_cast heK
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ e-D.lineDeficit H by omega)
      (show (0 : ℤ) ≤ (D.lineDeficit K : ℤ)-1 by omega),
      mul_nonneg (show (0 : ℤ) ≤ (e : ℤ)-1 by omega)
        (show (0 : ℤ) ≤ e-D.lineDeficit K by omega)]
  have hs := Finset.card_le_card
    (D.clique_union_subset_common_parallel e C M hC hM hHC hHM hKC hKM)
  have hu := Finset.card_union_le ({H,K} : Finset I) (D.parallelLines H ∩ D.parallelLines K)
  have hpair : ({H,K} : Finset I).card = 2 := by simp [hHK]
  rw [hpair] at hu
  have hn : (C ∪ M).card ≤ 2+(D.parallelLines H ∩ D.parallelLines K).card := hs.trans hu
  have hz : ((C ∪ M).card : ℤ) ≤ 2+(D.parallelLines H ∩ D.parallelLines K).card := by exact_mod_cast hn
  rw [D.common_parallel_card_of_parallel_int hI (hcap H) (hcap K) hpar] at hz
  omega

/-- Simplified early-route conclusion: distinct good cliques share at most one
actual indexed line, derived from source6.4 and the strict size margin. -/
theorem good_clique_intersection_le_one (D : IndexedDesign q X I) (e a : ℕ)
    (he : 1 ≤ e) (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hmargin : (q : ℤ)+1+((e : ℤ)-1)^2+(e : ℤ)^2 < 2*((q-a : ℕ) : ℤ))
    (C M : Finset I) (hC : D.GoodClique e a C) (hM : D.GoodClique e a M)
    (hne : C ≠ M) : (C ∩ M).card ≤ 1 := by
  obtain ⟨H,hHC,K,hKM,hHK,hmeet⟩ :=
    D.distinct_maximal_cliques_meeting_witness e C M hC.1 hM.1 hne
  have hinter := D.clique_inter_card_le e hI hcap C M hC.1.1 hM.1.1 hHC hKM hHK hmeet
  by_contra hn
  have hlarge : 1 < (C ∩ M).card := by omega
  obtain ⟨U,hU,W,hW,hUW⟩ := Finset.one_lt_card.mp hlarge
  have hunion := D.clique_union_card_le e he hI hcap C M hC.1.1 hM.1.1
    (Finset.mem_inter.mp hU).1 (Finset.mem_inter.mp hU).2
    (Finset.mem_inter.mp hW).1 (Finset.mem_inter.mp hW).2 hUW
  have hidentity := Finset.card_union_add_card_inter C M
  have hiZ : ((C ∩ M).card : ℤ) ≤ (e : ℤ)^2 := by exact_mod_cast hinter
  have hcZ : ((q-a : ℕ) : ℤ) ≤ C.card := by exact_mod_cast hC.2.1
  have hmZ : ((q-a : ℕ) : ℤ) ≤ M.card := by exact_mod_cast hM.2.1
  have hidZ : ((C ∪ M).card : ℤ)+(C ∩ M).card = C.card+M.card := by exact_mod_cast hidentity
  omega

/-- Source6.3 actual candidate: long lines missing L and meeting G. -/
noncomputable def meetingParallelLong (D : IndexedDesign q X I) (e : ℕ) (L G : I) : Finset I :=
  (D.parallelLines L ∩ D.meetingLines G) \ D.shortLines e

theorem meetingParallelLong_clique (D : IndexedDesign q X I) (e : ℕ)
    (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hsquare : (e+1)^2 ≤ q+2) {L G : I}
    (hL : D.lineDeficit L = 2) (hG : D.lineDeficit G = 2) (hLG : D.Parallel L G) :
    D.ParallelClique e (D.meetingParallelLong e L G) := by
  constructor
  · intro H hH
    have hn := (Finset.mem_sdiff.mp hH).2
    have hn' : ¬D.Short e H := by simpa only [D.mem_shortLines] using hn
    unfold Short Long at *
    omega
  · intro H hH K hK hHK
    obtain ⟨hHmem,hHshort⟩ := Finset.mem_sdiff.mp hH
    obtain ⟨hKmem,hKshort⟩ := Finset.mem_sdiff.mp hK
    obtain ⟨hLH,hGH⟩ := Finset.mem_inter.mp hHmem
    obtain ⟨hLK,hGK⟩ := Finset.mem_inter.mp hKmem
    refine ⟨hHK,?_⟩
    intro x hx
    have hHKmeet : K ∈ D.meetingLines H := (D.mem_meetingLines _ _).mpr
      ⟨hHK.symm,x,hx⟩
    have ht := D.parallel_triangle_deficit_two hI hcap hL hG hLG
      ((D.mem_parallelLines _ _).mp hLH) ((D.mem_parallelLines _ _).mp hLK)
      hGH hGK hHKmeet
    have hHlong : D.Long e H := by
      have : ¬D.Short e H := by simpa only [D.mem_shortLines] using hHshort
      unfold Short Long at *
      omega
    have hKlong : D.Long e K := by
      have : ¬D.Short e K := by simpa only [D.mem_shortLines] using hKshort
      unfold Short Long at *
      omega
    have hdH := D.long_deficit_le e hHlong
    have hdK := D.long_deficit_le e hKlong
    nlinarith [Nat.mul_le_mul_right (D.lineDeficit H+1) (Nat.add_le_add_right hdK 1),
      Nat.mul_self_le_mul_self (Nat.add_le_add_right hdH 1)]

/-- Exact source6.3 cardinal precursor: all lines parallel to L and meeting G
number q−1; deleting the actual short ones costs at most a. -/
theorem meetingParallelLong_card_lower (D : IndexedDesign q X I) (e a : ℕ)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) {L G : I}
    (hL : D.lineDeficit L = 2) (hG : D.lineDeficit G = 2) (hLG : D.Parallel L G)
    (hshort : (D.parallelLines L ∩ D.shortLines e).card ≤ a) :
    q-1 ≤ (D.meetingParallelLong e L G).card+a := by
  have hdegree : D.lineDegree G = q-1 := by
    have hh := Nat.sub_add_cancel (hcap G)
    change D.lineDeficit G + D.lineDegree G = q+1 at hh
    omega
  have hgp : G ∈ D.parallelLines L := (D.mem_parallelLines _ _).mpr hLG
  have hinter : (D.linePoints G ∩ D.linePoints L).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x,hx⟩
    obtain ⟨hxG,hxL⟩ := Finset.mem_inter.mp hx
    exact hLG.2 x ⟨(D.mem_linePoints _ _).mp hxL,(D.mem_linePoints _ _).mp hxG⟩
  have hw := D.parallel_line_incidence L G
  rw [D.intersection_degree_sum,hinter,Nat.sub_zero,hL,if_pos hgp] at hw
  have hj : (D.parallelLines L ∩ D.meetingLines G).card = q-1 := by
    change D.lineDegree G + _ = D.lineDegree G * 2 at hw
    omega
  have hcard := Finset.card_sdiff_add_card_inter
    (D.parallelLines L ∩ D.meetingLines G) (D.shortLines e)
  have hsub : ((D.parallelLines L ∩ D.meetingLines G) ∩ D.shortLines e).card ≤ a := by
    apply (Finset.card_le_card ?_).trans hshort
    intro j hj
    obtain ⟨hjLG,hjs⟩ := Finset.mem_inter.mp hj
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hjLG).1,hjs⟩
  change q-1 ≤ ((D.parallelLines L ∩ D.meetingLines G) \ D.shortLines e).card+a
  omega

/-- Actual good clique through L and any long parallel H meeting the specified
deficit-two G. The short-parallel budget is the separate source6.2(a) input. -/
theorem good_clique_for_meeting_parallel (D : IndexedDesign q X I) (e a : ℕ)
    (he : 2 ≤ e) (heq : e ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hsquare : (e+1)^2 ≤ q+2) {L G H : I}
    (hL : D.lineDeficit L = 2) (hG : D.lineDeficit G = 2) (hLG : D.Parallel L G)
    (hshort : (D.parallelLines L ∩ D.shortLines e).card ≤ a)
    (hLH : D.Parallel L H) (hHlong : D.Long e H) (hGH : H ∈ D.meetingLines G) :
    ∃ C, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C := by
  classical
  let M := D.meetingParallelLong e L G
  have hM := D.meetingParallelLong_clique e hI hcap hsquare hL hG hLG
  have hLlong : D.Long e L := by
    have hh := Nat.sub_add_cancel (hcap L)
    change D.lineDeficit L + D.lineDegree L = q+1 at hh
    unfold Long
    omega
  have hLM : L ∉ M := by
    intro h
    have hp := (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
    exact ((D.mem_parallelLines _ _).mp hp).1 rfl
  have hInsert : D.ParallelClique e (insert L M) := by
    constructor
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact hLlong
      · exact hM.1 J hJ
    · intro J hJ K hK hJK
      rcases Finset.mem_insert.mp hJ with rfl | hJ <;>
        rcases Finset.mem_insert.mp hK with rfl | hK
      · exact False.elim (hJK rfl)
      · exact (D.mem_parallelLines _ _).mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hK).1).1
      · exact D.parallel_symm ((D.mem_parallelLines _ _).mp
          (Finset.mem_inter.mp (Finset.mem_sdiff.mp hJ).1).1)
      · exact hM.2 J hJ K hK hJK
  have hsize : q-a ≤ (insert L M).card := by
    rw [Finset.card_insert_of_notMem hLM]
    have hh := D.meetingParallelLong_card_lower e a hcap hL hG hLG hshort
    change q-1 ≤ M.card+a at hh
    omega
  obtain ⟨C,hMC,hC⟩ := D.exists_good_clique_extension e a (insert L M) hInsert hsize
    ⟨L,by simp,hL⟩
  have hHM : H ∈ M := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_inter.mpr ⟨(D.mem_parallelLines _ _).mpr hLH,hGH⟩,?_⟩
    intro hs
    have hs' := (D.mem_shortLines _ _).mp hs
    exact (not_lt_of_ge hs') hHlong
  exact ⟨C,hC,hMC (by simp),hMC (by simp [hHM])⟩

/-- Specialization of actual short-line sparsity to the frozen square-root
cutoff and actual missing-point budget. No moment inequality remains a premise. -/
theorem shortLines_cutoff_card_le (D : IndexedDesign q X I) (s : ℕ)
    (hq : 100000000 ≤ q) (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q) :
    (D.shortLines (Erdos60.Embedding.Parameters.cutoff q)).card ≤
      q-Erdos60.Embedding.Parameters.cutoff q := by
  let e := Erdos60.Embedding.Parameters.cutoff q
  obtain ⟨he,he2,he3,he4,he5⟩ := Erdos60.Embedding.Parameters.cutoff_bounds q hq
  have heq : e ≤ q := by change 1000*e ≤ q at he4; omega
  have he1 : 1 ≤ e := by change 1000 ≤ e at he; omega
  have hnum := Erdos60.Embedding.Parameters.short_moment_strict q s hq hs hbranch
  change s*(s-q-2) < (q-e+1)*(e^2-1) at hnum
  have hnumZ : (s : ℤ)*((s-q-2 : ℕ) : ℤ) <
      ((q-e+1 : ℕ) : ℤ)*((e^2-1 : ℕ) : ℤ) := by exact_mod_cast hnum
  have hd : ((s-q-2 : ℕ) : ℤ) = (s : ℤ)-q-2 := by omega
  have he2pos : 1 ≤ e^2 := by nlinarith
  rw [hd,Nat.cast_sub he2pos,Nat.cast_pow,Nat.cast_one] at hnumZ
  exact D.shortLines_card_le s e he1 heq hI hX hcap hnone hnumZ

/-- Full source6.2–6.3 supplier at the selected parameters: every long line
parallel to a deficit-two line lies with it in an actual good maximal clique.
The short-parallel budget and deficit-two meeting partner are proved inputs
from DeficitTwoPartners, not hypotheses of this theorem. -/
theorem good_clique_for_long_parallel (D : IndexedDesign q X I) (s : ℕ)
    (hq : 100000000 ≤ q) (hs : 500*s ≤ 501*q)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1)
    (hbranch : q+2 ≤ s) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hnone : ∀ i, D.lineDegree i ≠ q) {L H : I}
    (hL : D.lineDeficit L = 2) (hLH : D.Parallel L H)
    (hHlong : D.Long (Erdos60.Embedding.Parameters.cutoff q) H) :
    ∃ C, D.GoodClique (Erdos60.Embedding.Parameters.cutoff q)
      (Erdos60.Embedding.Parameters.allowance q s) C ∧ L ∈ C ∧ H ∈ C := by
  classical
  let e := Erdos60.Embedding.Parameters.cutoff q
  let a := Erdos60.Embedding.Parameters.allowance q s
  obtain ⟨he,he2,he3,he4,he5⟩ := Erdos60.Embedding.Parameters.cutoff_bounds q hq
  have heq : e ≤ q := by change 1000*e ≤ q at he4; omega
  have heTwo : 2 ≤ e := by change 1000 ≤ e at he; omega
  have hshortRaw := D.deficit_two_short_parallel_le_allowance s hq hI hX hbranch hcap hnone hL
  have hshort : (D.parallelLines L ∩ D.shortLines e).card ≤ a := by
    have heqSet : D.parallelLines L ∩ D.shortLines e =
        (D.parallelLines L).filter (fun J => D.lineDegree J ≤ q-e) := by
      ext J
      simp [shortLines,Short]
    rw [heqSet]
    exact hshortRaw
  obtain ⟨G,hLG,hG,hHG⟩ := D.deficit_two_parallel_partner_large s hq hs hI hX
    hbranch hcap hnone hL hLH
  have hGH : H ∈ D.meetingLines G := by
    obtain ⟨hne,x,hx⟩ := (D.mem_meetingLines _ _).mp hHG
    exact (D.mem_meetingLines _ _).mpr ⟨hne.symm,x,hx.symm⟩
  exact D.good_clique_for_meeting_parallel e a heTwo heq hI hcap he5 hL hG hLG
    hshort hLH hHlong hGH

end Erdos60.Embedding.IndexedDesign
