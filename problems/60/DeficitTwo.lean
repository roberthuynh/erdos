import ParallelCounts
import GoodCliques
import EmbeddingParameters

namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

/-- Removing the one common line makes two clique families disjoint. -/
theorem erased_cliques_disjoint {A B : Finset I} {L : I}
    (hLA : L ∈ A) (hLB : L ∈ B) (hinter : (A ∩ B).card ≤ 1) :
    Disjoint (A.erase L) (B.erase L) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have he : i = L := Finset.card_le_one.mp hinter i
    (Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hi).2,(Finset.mem_erase.mp hj).2⟩)
    L (Finset.mem_inter.mpr ⟨hLA,hLB⟩)
  exact (Finset.mem_erase.mp hi).1 he

/-- Source p46's easier no-three argument is an actual finite incidence
count, rather than an assumption on the number of good cliques. -/
theorem parallel_cliques_no_three (D : IndexedDesign q X I) (a : ℕ) (L : I)
    (hI : Fintype.card I = q^2+q+1) (hcap : D.lineDegree L ≤ q+1)
    (hdef : D.lineDeficit L = 2) (hstrict : 2*q < 3*(q-1-a))
    (A B C : Finset I) (hLA : L ∈ A) (hLB : L ∈ B) (hLC : L ∈ C)
    (hA : q-a ≤ A.card) (hB : q-a ≤ B.card) (hC : q-a ≤ C.card)
    (hAp : ∀ i ∈ A, i ≠ L → D.Parallel L i)
    (hBp : ∀ i ∈ B, i ≠ L → D.Parallel L i)
    (hCp : ∀ i ∈ C, i ≠ L → D.Parallel L i)
    (hAB : (A ∩ B).card ≤ 1) (hAC : (A ∩ C).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) : False := by
  classical
  have hdAB := erased_cliques_disjoint hLA hLB hAB
  have hdAC := erased_cliques_disjoint hLA hLC hAC
  have hdBC := erased_cliques_disjoint hLB hLC hBC
  have hd : Disjoint (A.erase L ∪ B.erase L) (C.erase L) :=
    Finset.disjoint_union_left.mpr ⟨hdAC,hdBC⟩
  have hsub : A.erase L ∪ B.erase L ∪ C.erase L ⊆ D.parallelLines L := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact (D.mem_parallelLines L i).mpr (hAp i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1)
      · exact (D.mem_parallelLines L i).mpr (hBp i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1)
    · exact (D.mem_parallelLines L i).mpr (hCp i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd,Finset.card_union_of_disjoint hdAB,
    D.parallel_card_eq_q_mul_deficit L hI hcap,hdef] at hc
  have hAc := Finset.card_erase_add_one hLA
  have hBc := Finset.card_erase_add_one hLB
  have hCc := Finset.card_erase_add_one hLC
  have hlowA : q-1-a ≤ (A.erase L).card := by omega
  have hlowB : q-1-a ≤ (B.erase L).card := by omega
  have hlowC : q-1-a ≤ (C.erase L).card := by omega
  omega

/-- At a clean point outside a deficit-two line, exactly two distinct
parallel labels occur; since every incident line is long, both are long.
The intersecting witnesses will force distinct maximal cliques. -/
theorem clean_point_two_parallel (D : IndexedDesign q X I) (L : I)
    (hdef : D.lineDeficit L = 2) (long : I → Prop) (x : X)
    (hx : ¬D.inc x L) (hclean : ∀ i, D.inc x i → long i) :
    ∃ H K : I, H ≠ K ∧ D.Parallel L H ∧ D.Parallel L K ∧
      long H ∧ long K ∧ D.inc x H ∧ D.inc x K := by
  classical
  have hc := D.point_parallel_count x L
  rw [if_neg hx,hdef] at hc
  obtain ⟨H,K,hHK,he⟩ := Finset.card_eq_two.mp hc
  have hH : H ∈ D.pointLines x ∩ D.parallelLines L := by rw [he]; simp
  have hK : K ∈ D.pointLines x ∩ D.parallelLines L := by rw [he]; simp
  have hHx := (D.mem_pointLines x H).mp (Finset.mem_inter.mp hH).1
  have hKx := (D.mem_pointLines x K).mp (Finset.mem_inter.mp hK).1
  exact ⟨H,K,hHK,(D.mem_parallelLines L H).mp (Finset.mem_inter.mp hH).2,
    (D.mem_parallelLines L K).mp (Finset.mem_inter.mp hK).2,
    hclean H hHx,hclean K hKx,hHx,hKx⟩

noncomputable def goodCliquesThrough (D : IndexedDesign q X I) (e a : ℕ) (L : I) :
    Finset (Finset I) :=
  Finset.univ.filter (fun C => D.GoodClique e a C ∧ L ∈ C)

@[simp] theorem mem_goodCliquesThrough (D : IndexedDesign q X I) (e a : ℕ)
    (L : I) (C : Finset I) :
    C ∈ D.goodCliquesThrough e a L ↔ D.GoodClique e a C ∧ L ∈ C := by
  classical
  simp [goodCliquesThrough]

/-- All actual nearfull good cliques through a deficit-two line number at
most two, once the source intersection bound has been supplied. -/
theorem goodCliquesThrough_card_le_two (D : IndexedDesign q X I) (e a : ℕ) (L : I)
    (hI : Fintype.card I = q^2+q+1) (hcap : D.lineDegree L ≤ q+1)
    (hdef : D.lineDeficit L = 2) (hstrict : 2*q < 3*(q-1-a))
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1) :
    (D.goodCliquesThrough e a L).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨A,B,C,hA,hB,hC,hAB,hAC,hBC⟩ := Finset.two_lt_card_iff.mp
    (show 2 < (D.goodCliquesThrough e a L).card by omega)
  obtain ⟨hAg,hLA⟩ := (D.mem_goodCliquesThrough e a L A).mp hA
  obtain ⟨hBg,hLB⟩ := (D.mem_goodCliquesThrough e a L B).mp hB
  obtain ⟨hCg,hLC⟩ := (D.mem_goodCliquesThrough e a L C).mp hC
  apply D.parallel_cliques_no_three a L hI hcap hdef hstrict A B C
    hLA hLB hLC hAg.2.1 hBg.2.1 hCg.2.1
  · intro i hi hne
    exact hAg.1.1.2 L hLA i hi hne.symm
  · intro i hi hne
    exact hBg.1.1.2 L hLB i hi hne.symm
  · intro i hi hne
    exact hCg.1.1.2 L hLC i hi hne.symm
  · exact hinter A B hAg hBg hAB
  · exact hinter A C hAg hCg hAC
  · exact hinter B C hBg hCg hBC

/-- A clean point outside the deficit-two line follows from global short
line sparsity and its actual 2q parallel labels; no special witness is assumed. -/
theorem exists_clean_outside_deficit_two (D : IndexedDesign q X I) (e : ℕ) (L : I)
    (hq : 0 < q) (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I = q^2+q+1) (hcap : D.lineDegree L ≤ q+1)
    (hdef : D.lineDeficit L = 2) :
    ∃ x : X, ¬D.inc x L ∧ ∀ i, D.inc x i → D.Long e i := by
  classical
  have hn : ¬D.parallelLines L ⊆ D.shortLines e := by
    intro hsub
    have hc := Finset.card_le_card hsub
    rw [D.parallel_card_eq_q_mul_deficit L hI hcap,hdef] at hc
    omega
  obtain ⟨H,hHL,hHshort⟩ := Finset.not_subset.mp hn
  have hHlong : D.Long e H := by
    have hh : ¬D.Short e H := by simpa using hHshort
    unfold Short Long at *
    omega
  obtain ⟨x,hxH,hclean⟩ := D.exists_clean_point_on_long e heq hshort H hHlong
  have hpar := (D.mem_parallelLines L H).mp hHL
  refine ⟨x,?_,hclean⟩
  intro hxL
  exact hpar.2 x ⟨hxL,hxH⟩

/-- The source construction of cliques for long parallel neighbors yields
at least two: the two labels through a clean outside point intersect, so
cannot belong to the same actual parallel clique. -/
theorem goodCliquesThrough_card_ge_two (D : IndexedDesign q X I) (e a : ℕ) (L : I)
    (hdef : D.lineDeficit L = 2)
    (hclean : ∃ x : X, ¬D.inc x L ∧ ∀ i, D.inc x i → D.Long e i)
    (hconstruct : ∀ H : I, D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C) :
    2 ≤ (D.goodCliquesThrough e a L).card := by
  classical
  obtain ⟨x,hx,hclean⟩ := hclean
  obtain ⟨H,K,hHK,hLH,hLK,hHlong,hKlong,hxH,hxK⟩ :=
    D.clean_point_two_parallel L hdef (D.Long e) x hx hclean
  obtain ⟨A,hAg,hLA,hHA⟩ := hconstruct H hHlong hLH
  obtain ⟨B,hBg,hLB,hKB⟩ := hconstruct K hKlong hLK
  have hAB : A ≠ B := by
    intro he
    have hKA : K ∈ A := he.symm ▸ hKB
    have hpar := hAg.1.1.2 H hHA K hKA hHK
    exact hpar.2 x ⟨hxH,hxK⟩
  exact Finset.one_lt_card.mpr ⟨A,(D.mem_goodCliquesThrough e a L A).mpr ⟨hAg,hLA⟩,
    B,(D.mem_goodCliquesThrough e a L B).mpr ⟨hBg,hLB⟩,hAB⟩

/-- Exact deficit-two multiplicity, by the proved upper/lower finite counts.
The two upstream inputs are source6.2–6.4 construction and intersection
interfaces, not an assumed clique cardinality. -/
theorem goodCliquesThrough_card_eq_two (D : IndexedDesign q X I) (e a : ℕ) (L : I)
    (hI : Fintype.card I = q^2+q+1) (hcap : D.lineDegree L ≤ q+1)
    (hdef : D.lineDeficit L = 2) (hstrict : 2*q < 3*(q-1-a))
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hclean : ∃ x : X, ¬D.inc x L ∧ ∀ i, D.inc x i → D.Long e i)
    (hconstruct : ∀ H : I, D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C) :
    (D.goodCliquesThrough e a L).card = 2 :=
  Nat.le_antisymm (D.goodCliquesThrough_card_le_two e a L hI hcap hdef hstrict hinter)
    (D.goodCliquesThrough_card_ge_two e a L hdef hclean hconstruct)

/-- The actual clean outside point is derived rather than supplied.
Only the source6.2–6.4 clique construction/intersection suppliers remain. -/
theorem deficit_two_exact (D : IndexedDesign q X I) (e a : ℕ) (L : I)
    (hq : 0 < q) (heq : e ≤ q) (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I = q^2+q+1) (hcap : D.lineDegree L ≤ q+1)
    (hdef : D.lineDeficit L = 2) (hstrict : 2*q < 3*(q-1-a))
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hconstruct : ∀ H : I, D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C) :
    (D.goodCliquesThrough e a L).card = 2 :=
  D.goodCliquesThrough_card_eq_two e a L hI hcap hdef hstrict hinter
    (D.exists_clean_outside_deficit_two e L hq heq hshort hI hcap hdef) hconstruct

/-- Every long parallel neighbor belongs to exactly one good clique through
L, after existence has been constructed. Two such cliques would share L,H. -/
theorem parallel_long_good_clique_unique (D : IndexedDesign q X I) (e a : ℕ) (L H : I)
    (hpar : D.Parallel L H)
    (hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1)
    (hconstruct : ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C) :
    ∃! C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C := by
  obtain ⟨C,hCg,hLC,hHC⟩ := hconstruct
  refine ⟨C,⟨hCg,hLC,hHC⟩,?_⟩
  rintro B ⟨hBg,hLB,hHB⟩
  by_contra hBC
  have hh := hinter B C hBg hCg hBC
  have he : L = H := Finset.card_le_one.mp hh L (Finset.mem_inter.mpr ⟨hLB,hLC⟩)
    H (Finset.mem_inter.mpr ⟨hHB,hHC⟩)
  exact hpar.1 he

/-- Actual source6.4 supplies the intersection input; the sole remaining
external construction interface here is source6.2–6.3's nearfull clique. -/
theorem deficit_two_exact_from_constructed_cliques (D : IndexedDesign q X I) (e a : ℕ) (L : I)
    (hq : 0 < q) (he : 1 ≤ e) (heq : e ≤ q)
    (hshort : (D.shortLines e).card ≤ q-e)
    (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hdef : D.lineDeficit L = 2) (hstrict : 2*q < 3*(q-1-a))
    (hmargin : (q : ℤ)+1+((e : ℤ)-1)^2+(e : ℤ)^2 < 2*((q-a : ℕ) : ℤ))
    (hconstruct : ∀ H : I, D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C) :
    (D.goodCliquesThrough e a L).card = 2 := by
  exact D.deficit_two_exact e a L hq heq hshort hI (hcap L) hdef hstrict
    (D.good_clique_intersection_le_one e a he hI hcap hmargin) hconstruct

theorem deficit_two_parallel_coverage (D : IndexedDesign q X I) (e a : ℕ) (L H : I)
    (he : 1 ≤ e) (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hmargin : (q : ℤ)+1+((e : ℤ)-1)^2+(e : ℤ)^2 < 2*((q-a : ℕ) : ℤ))
    (hHlong : D.Long e H) (hpar : D.Parallel L H)
    (hconstruct : ∀ K : I, D.Long e K → D.Parallel L K →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ K ∈ C) :
    ∃! C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C :=
  D.parallel_long_good_clique_unique e a L H hpar
    (D.good_clique_intersection_le_one e a he hI hcap hmargin)
    (hconstruct H hHlong hpar)

/-- The uniform early-route parameters supply both strict clique margins;
no optimized or approximate real cutoff is substituted. -/
theorem deficit_two_exact_specialized (D : IndexedDesign q X I) (s : ℕ) (L : I)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s)
    (hshort : (D.shortLines (Parameters.cutoff q)).card ≤ q-Parameters.cutoff q)
    (hI : Fintype.card I = q^2+q+1) (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hdef : D.lineDeficit L = 2)
    (hconstruct : ∀ H : I, D.Long (Parameters.cutoff q) H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique (Parameters.cutoff q) (Parameters.allowance q s) C ∧
        L ∈ C ∧ H ∈ C) :
    (D.goodCliquesThrough (Parameters.cutoff q) (Parameters.allowance q s) L).card = 2 := by
  have he := Parameters.subtraction_bounds q s hq hs hbranch
  have hmargin := Parameters.strong_clique_union_strict q s hq hs hbranch
  have hmarginZ : (q : ℤ)+1+((Parameters.cutoff q-1 : ℕ) : ℤ)^2+
      (Parameters.cutoff q : ℤ)^2 < 2*((q-Parameters.allowance q s : ℕ) : ℤ) := by
    exact_mod_cast hmargin
  rw [Nat.cast_sub he.2.1, Nat.cast_one] at hmarginZ
  exact D.deficit_two_exact_from_constructed_cliques (Parameters.cutoff q)
    (Parameters.allowance q s) L (by omega) he.2.1 he.1 hshort hI hcap hdef
    (Parameters.triple_clique_strict q s hq hs hbranch) hmarginZ hconstruct

/-- Actual short-line sparsity for the chosen cutoff follows from the
proved indexed-design moment and the exact uniform parameter inequality. -/
theorem specialized_shortLines_bound (D : IndexedDesign q X I) (s : ℕ)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q) :
    (D.shortLines (Parameters.cutoff q)).card ≤ q-Parameters.cutoff q := by
  have he := Parameters.subtraction_bounds q s hq hs hbranch
  have hm := Parameters.short_moment_strict q s hq hs hbranch
  have hmZ : (s : ℤ)*((s-q-2 : ℕ) : ℤ) <
      ((q-Parameters.cutoff q+1 : ℕ) : ℤ)*(((Parameters.cutoff q)^2-1 : ℕ) : ℤ) := by
    exact_mod_cast hm
  have hsq : q ≤ s := by omega
  have hs2 : 2 ≤ s-q := by omega
  have he2 : 1 ≤ (Parameters.cutoff q)^2 := by nlinarith [he.2.1]
  rw [Nat.cast_sub hs2,Nat.cast_sub hsq,Nat.cast_sub he2,Nat.cast_pow] at hmZ
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at hmZ
  exact D.shortLines_card_le s (Parameters.cutoff q) he.2.1 he.1 hI hX hcap hnone hmZ

/-- Specialized deficit-two conclusion from actual design data. The only
remaining supplier is the actual source6.2–6.3 clique construction. -/
theorem deficit_two_exact_of_design (D : IndexedDesign q X I) (s : ℕ) (L : I)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q)
    (hdef : D.lineDeficit L = 2)
    (hconstruct : ∀ H : I, D.Long (Parameters.cutoff q) H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique (Parameters.cutoff q) (Parameters.allowance q s) C ∧
        L ∈ C ∧ H ∈ C) :
    (D.goodCliquesThrough (Parameters.cutoff q) (Parameters.allowance q s) L).card = 2 :=
  D.deficit_two_exact_specialized s L hq hs hbranch
    (D.specialized_shortLines_bound s hq hs hbranch hI hX hcap hnone)
    hI hcap hdef hconstruct

/-- Full actual deficit-two base of the selected early route: exactly two
good cliques, and unique coverage of every long parallel line. All source
construction and intersection suppliers are proved imported declarations. -/
theorem deficit_two_good_cliques (D : IndexedDesign q X I) (s : ℕ) (L : I)
    (hq : 10^8 ≤ q) (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X+s = q^2+q+1)
    (hcap : ∀ i, D.lineDegree i ≤ q+1) (hnone : ∀ i, D.lineDegree i ≠ q)
    (hdef : D.lineDeficit L = 2) :
    (D.goodCliquesThrough (Parameters.cutoff q) (Parameters.allowance q s) L).card = 2 ∧
      ∀ H : I, D.Long (Parameters.cutoff q) H → D.Parallel L H →
        ∃! C : Finset I, D.GoodClique (Parameters.cutoff q) (Parameters.allowance q s) C ∧
          L ∈ C ∧ H ∈ C := by
  have hconstruct : ∀ H : I, D.Long (Parameters.cutoff q) H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique (Parameters.cutoff q) (Parameters.allowance q s) C ∧
        L ∈ C ∧ H ∈ C := fun H hlong hpar =>
    D.good_clique_for_long_parallel s hq hs hI hX hbranch hcap hnone hdef hpar hlong
  have he := Parameters.subtraction_bounds q s hq hs hbranch
  have hm := Parameters.strong_clique_union_strict q s hq hs hbranch
  have hmZ : (q : ℤ)+1+((Parameters.cutoff q-1 : ℕ) : ℤ)^2+
      (Parameters.cutoff q : ℤ)^2 < 2*((q-Parameters.allowance q s : ℕ) : ℤ) := by
    exact_mod_cast hm
  rw [Nat.cast_sub he.2.1,Nat.cast_one] at hmZ
  refine ⟨D.deficit_two_exact_of_design s L hq hs hbranch hI hX hcap hnone hdef hconstruct,?_⟩
  intro H hlong hpar
  exact D.deficit_two_parallel_coverage (Parameters.cutoff q) (Parameters.allowance q s)
    L H he.2.1 hI hcap hmZ hlong hpar hconstruct

#print axioms parallel_cliques_no_three
#print axioms clean_point_two_parallel
#print axioms deficit_two_good_cliques
end Erdos60.Embedding.IndexedDesign
