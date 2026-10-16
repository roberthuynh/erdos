import BasicCounts
import Mathlib.Combinatorics.Configuration

/-! Metsch (1991), printed page 20, Lemma 3.8. The original line carrier I
remains indexed, including empty lines and repeated singleton supports. -/
namespace Erdos60.Embedding.ShortLineRestoration
open Finset
open scoped Classical
variable {q : ℕ} {X I P L : Type*} [Fintype X] [Fintype I]
variable [Membership P L] [Fintype P] [Fintype L]
variable [Configuration.ProjectivePlane P L]

noncomputable def uniquePoints (M : Finset L) (l : L) : Finset P :=
  Finset.univ.filter (fun p => p ∈ l ∧ ∀ m ∈ M, m ≠ l → p ∉ m)

/-- Each omitted plane line has at least q+2-|M| points lying on no other
omitted line. Actual plane intersections pay for all excluded points. -/
theorem uniquePoints_card (ho : Configuration.ProjectivePlane.order P L = q)
    (M : Finset L) (l : L) (hl : l ∈ M) :
    q+2 ≤ (uniquePoints (P := P) M l).card + M.card := by
  classical
  let C := Finset.univ.filter (fun p : P => p ∈ l)
  let H := fun m : L => Finset.univ.filter (fun p : P => p ∈ l ∧ p ∈ m)
  have hH : ∀ m ∈ M.erase l, (H m).card ≤ 1 := by
    intro m hm
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha1,ha2⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨hb1,hb2⟩ := (Finset.mem_filter.mp hb).2
    exact (Configuration.Nondegenerate.eq_or_eq ha1 hb1 ha2 hb2).resolve_right
      (Finset.mem_erase.mp hm).1.symm
  have hcover : C ⊆ uniquePoints M l ∪ (M.erase l).biUnion H := by
    intro p hp
    have hpl : p ∈ l := (Finset.mem_filter.mp hp).2
    by_cases hu : ∀ m ∈ M, m ≠ l → p ∉ m
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpl,hu⟩))
    · push Not at hu
      obtain ⟨m,hm,hml,hpm⟩ := hu
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨m,Finset.mem_erase.mpr ⟨hml,hm⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpl,hpm⟩⟩))
  have hC : C.card = q+1 := by
    simpa [C,Configuration.pointCount,Nat.card_eq_fintype_card,Fintype.card_subtype,ho] using
      Configuration.ProjectivePlane.pointCount_eq P l
  have hsum : (∑ m ∈ M.erase l, (H m).card) ≤ (M.erase l).card := by
    simpa using Finset.sum_le_sum hH
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le (uniquePoints M l) ((M.erase l).biUnion H)
  have hb := Finset.card_biUnion_le (s := M.erase l) (t := H)
  rw [hC] at hc
  rw [Finset.card_erase_of_mem hl] at hsum
  have hm := Finset.card_pos.mpr ⟨l,hl⟩
  omega

/-- If 2..q lines of a plane are omitted, more than the available new points
lie on exactly one omitted line. Hence an old point has unique missing line. -/
theorem exists_old_unique_missing
    (ho : Configuration.ProjectivePlane.order P L = q) (hq : 2 ≤ q)
    (f : X ↪ P) (hX : q^2-q+2 ≤ Fintype.card X)
    (M : Finset L) (hMlo : 2 ≤ M.card) (hMhi : M.card ≤ q) :
    ∃ x : X, ∃ l ∈ M, f x ∈ l ∧ ∀ m ∈ M, f x ∈ m → m = l := by
  classical
  let U := M.biUnion (uniquePoints (P := P) M)
  have hdis : (M : Set L).PairwiseDisjoint (uniquePoints (P := P) M) := by
    intro l hl m hm hlm
    apply Finset.disjoint_left.mpr
    intro p hp hpm
    exact (Finset.mem_filter.mp hp).2.2 m hm hlm.symm (Finset.mem_filter.mp hpm).2.1
  have hsum := Finset.sum_le_sum (fun l hl => uniquePoints_card ho M l hl)
  have hsumU : M.card*(q+2) ≤ U.card+M.card*M.card := by
    change M.card*(q+2) ≤ (M.biUnion (uniquePoints M)).card+M.card*M.card
    rw [Finset.card_biUnion hdis]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_add] using hsum
  let O := (Finset.univ : Finset P) \ Finset.univ.image f
  have himg : (Finset.univ.image f).card = Fintype.card X := by
    rw [Finset.card_image_of_injective _ f.injective,Finset.card_univ]
  have hO : O.card + Fintype.card X = q^2+q+1 := by
    have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset P) (Finset.univ.image f)
    simpa only [O,Finset.univ_inter,himg,Finset.card_univ,
      Configuration.ProjectivePlane.card_points P L,ho] using hh
  have hqq : q ≤ q^2 := by nlinarith
  have hX' : q^2+2 ≤ Fintype.card X+q := by omega
  have hOsmall : O.card < 2*q := by omega
  by_contra hn
  have hsub : U ⊆ O := by
    intro p hp
    obtain ⟨l,hl,hpl⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpl,hu⟩ := (Finset.mem_filter.mp hpl).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hpimage
    obtain ⟨x,hx,hfx⟩ := Finset.mem_image.mp hpimage
    subst p
    apply hn
    refine ⟨x,l,hl,hpl,?_⟩
    intro m hm hpm
    by_contra hml
    exact hu m hm hml hpm
  have hU := Finset.card_le_card hsub
  have hprod : 0 ≤ (M.card-2)*(q-M.card) := Nat.zero_le _
  have hprod' : 2*q+M.card*M.card ≤ M.card*(q+2) := by
    have he1 : M.card-2+2 = M.card := Nat.sub_add_cancel hMlo
    have he2 : q-M.card+M.card = q := Nat.sub_add_cancel hMhi
    nlinarith
  omega

/-- Exact partial embeddings preserve the number of omitted lines through
an old point. Line labels are never quotiented by their supports. -/
theorem omitted_incidence_card (D : IndexedDesign q X I)
    (f : X ↪ P) (J : Finset I) (r : I → L)
    (hinj : Set.InjOn r (J : Set I))
    (hrow : ∀ i ∈ J, ∀ x, D.inc x i ↔ f x ∈ r i)
    (ho : Configuration.ProjectivePlane.order P L = q) (x : X) :
    (D.pointLines x \ J).card =
      ((Finset.univ \ J.image r).filter (fun l => f x ∈ l)).card := by
  classical
  let F := J.filter (D.inc x)
  let H := (J.image r).filter (fun l => f x ∈ l)
  have himage : F.image r = H := by
    ext l
    simp only [F,H,Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨i,⟨hi,hxi⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,(hrow i hi x).mp hxi⟩
    · rintro ⟨⟨i,hi,rfl⟩,hxi⟩
      exact ⟨i,⟨hi,(hrow i hi x).mpr hxi⟩,rfl⟩
  have hcards : F.card = H.card := by
    rw [← himage]
    exact (Finset.card_image_iff.mpr (fun a ha b hb he =>
      hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he)).symm
  have horig := Finset.card_sdiff_add_card_inter (D.pointLines x) J
  have hF : D.pointLines x ∩ J = F := by ext i; simp [F,and_comm]
  rw [D.card_pointLines,hF] at horig
  let Q := Finset.univ.filter (fun l : L => f x ∈ l)
  have hQc : Q.card = q+1 := by
    simpa [Q,Configuration.lineCount,Nat.card_eq_fintype_card,Fintype.card_subtype,ho] using
      Configuration.ProjectivePlane.lineCount_eq L (f x)
  have hplane := Finset.card_sdiff_add_card_inter Q (J.image r)
  have hH : Q ∩ J.image r = H := by ext l; simp [Q,H,and_comm]
  have hmissing : Q \ J.image r = (Finset.univ \ J.image r).filter (fun l => f x ∈ l) := by
    ext l; simp [Q,and_comm]
  rw [hQc,hH,hmissing] at hplane
  omega

/-- The actual source3.8 single-label extension at an old point with exactly
one unused plane line. Both directions of incidence are constructed. -/
theorem restore_at_old_point (D : IndexedDesign q X I)
    (f : X ↪ P) (J : Finset I) (r : I → L)
    (hinj : Set.InjOn r (J : Set I))
    (hrow : ∀ i ∈ J, ∀ x, D.inc x i ↔ f x ∈ r i)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (x : X) (l : L) (hl : l ∉ J.image r) (hxl : f x ∈ l)
    (hunique : ∀ m, m ∉ J.image r → f x ∈ m → m = l) :
    ∃ i, i ∉ J ∧ ∀ y, D.inc y i ↔ f y ∈ l := by
  classical
  have hmc : ((Finset.univ \ J.image r).filter (fun m => f x ∈ m)).card = 1 := by
    apply Finset.card_eq_one.mpr
    refine ⟨l,?_⟩
    ext m
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hm
      exact hunique m hm.1 hm.2
    · rintro rfl
      exact ⟨hl,hxl⟩
  have hoc : (D.pointLines x \ J).card = 1 :=
    (omitted_incidence_card D f J r hinj hrow ho x).trans hmc
  obtain ⟨i,hi,hiunique⟩ := Finset.card_eq_one_iff_existsUnique.mp hoc
  obtain ⟨hxi,hiJ⟩ := Finset.mem_sdiff.mp hi
  have hxi' : D.inc x i := (D.mem_pointLines x i).mp hxi
  refine ⟨i,hiJ,?_⟩
  intro y
  by_cases hyx : y = x
  · subst y
    exact ⟨fun _ => hxl,fun _ => hxi'⟩
  have hxy : x ≠ y := Ne.symm hyx
  have hfxy : f x ≠ f y := fun he => hxy (f.injective he)
  constructor
  · intro hyi
    let m := Configuration.HasLines.mkLine (L := L) hfxy
    have hm := Configuration.HasLines.mkLine_ax (L := L) hfxy
    have hmnot : m ∉ J.image r := by
      intro hmimage
      obtain ⟨j,hj,hrj⟩ := Finset.mem_image.mp hmimage
      have hxj : D.inc x j := (hrow j hj x).mpr (hrj ▸ hm.1)
      have hyj : D.inc y j := (hrow j hj y).mpr (hrj ▸ hm.2)
      have hji := D.join_unique hxy hxj hyj hxi' hyi
      exact hiJ (hji ▸ hj)
    have hml := hunique m hmnot hm.1
    exact hml ▸ hm.2
  · intro hyl
    obtain ⟨j,⟨hxj,hyj⟩,_⟩ := D.unique_join x y hxy
    by_cases hji : j = i
    · exact hji ▸ hyj
    · have hj : j ∈ J := by
        by_contra hj
        exact hji (hiunique j (Finset.mem_sdiff.mpr ⟨(D.mem_pointLines x j).mpr hxj,hj⟩))
      have hrjl : r j = l := (Configuration.Nondegenerate.eq_or_eq
        ((hrow j hj x).mp hxj) ((hrow j hj y).mp hyj) hxl hyl).resolve_left hfxy
      exact False.elim (hl (Finset.mem_image.mpr ⟨j,hj,hrjl⟩))

/-- With one original label and one plane line unused, point-pencil counts
restore the exact incidence, even when the remaining original line is empty. -/
theorem restore_last_label (D : IndexedDesign q X I)
    (f : X ↪ P) (J : Finset I) (r : I → L)
    (hinj : Set.InjOn r (J : Set I))
    (hrow : ∀ i ∈ J, ∀ x, D.inc x i ↔ f x ∈ r i)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (i : I) (hi : Finset.univ \ J = {i})
    (l : L) (hl : Finset.univ \ J.image r = {l}) :
    i ∉ J ∧ l ∉ J.image r ∧ ∀ x, D.inc x i ↔ f x ∈ l := by
  classical
  have hiJ : i ∉ J := by
    have hh : i ∈ Finset.univ \ J := by rw [hi]; simp
    exact (Finset.mem_sdiff.mp hh).2
  have hlJ : l ∉ J.image r := by
    have hh : l ∈ Finset.univ \ J.image r := by rw [hl]; simp
    exact (Finset.mem_sdiff.mp hh).2
  refine ⟨hiJ,hlJ,?_⟩
  intro x
  have hcounts := omitted_incidence_card D f J r hinj hrow ho x
  have horig : D.pointLines x \ J = ({i} : Finset I).filter (D.inc x) := by
    ext j
    have hj : j ∉ J ↔ j = i := by
      have hh := Finset.ext_iff.mp hi j
      simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_singleton] using hh
    simp only [Finset.mem_sdiff,D.mem_pointLines,Finset.mem_filter,Finset.mem_singleton,hj]
    tauto
  rw [horig,hl] at hcounts
  have heq1 : ({i} : Finset I).filter (D.inc x) = if D.inc x i then {i} else ∅ := by
    ext j; by_cases h : D.inc x i <;> simp [h] <;> aesop
  have heq2 : ({l} : Finset L).filter (fun m => f x ∈ m) = if f x ∈ l then {l} else ∅ := by
    ext m; by_cases h : f x ∈ l <;> simp [h] <;> aesop
  rw [heq1,heq2] at hcounts
  by_cases hxi : D.inc x i <;> by_cases hxl : f x ∈ l <;> simp_all

omit [Fintype P] [Fintype L] [Configuration.ProjectivePlane P L] in
/-- Update one actual indexed line while preserving every previous assignment. -/
theorem extend_assignment (D : IndexedDesign q X I)
    (f : X ↪ P) (J : Finset I) (r : I → L)
    (hinj : Set.InjOn r (J : Set I))
    (hrow : ∀ i ∈ J, ∀ x, D.inc x i ↔ f x ∈ r i)
    (i : I) (hi : i ∉ J) (l : L) (hl : l ∉ J.image r)
    (hnew : ∀ x, D.inc x i ↔ f x ∈ l) :
    ∃ r' : I → L, Set.InjOn r' (↑(insert i J) : Set I) ∧
      (∀ j ∈ insert i J, ∀ x, D.inc x j ↔ f x ∈ r' j) ∧
      ∀ j ∈ J, r' j = r j := by
  classical
  let r' := Function.update r i l
  have hri : r' i = l := by simp [r']
  have hrold : ∀ j ∈ J, r' j = r j := by
    intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp [r',hji]
  refine ⟨r',?_,?_,hrold⟩
  · intro a ha b hb he
    rcases Finset.mem_insert.mp ha with hai | haJ
    · rcases Finset.mem_insert.mp hb with hbi | hbJ
      · exact hai.trans hbi.symm
      · have he' : l = r b := by simpa only [hai,hri,hrold b hbJ] using he
        exact False.elim (hl (Finset.mem_image.mpr ⟨b,hbJ,he'.symm⟩))
    · rcases Finset.mem_insert.mp hb with hbi | hbJ
      · have he' : r a = l := by simpa only [hbi,hrold a haJ,hri] using he
        exact False.elim (hl (Finset.mem_image.mpr ⟨a,haJ,he'⟩))
      · exact hinj haJ hbJ (by simpa only [hrold a haJ,hrold b hbJ] using he)
  · intro j hj x
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [hri]; exact hnew x
    · rw [hrold j hj]; exact hrow j hj x

/-- Actual restoration of every omitted indexed line, preserving the initial
embedding and its fixed old-point map. Empty and repeated singleton supports
remain separate indexed labels and acquire distinct plane lines. -/
theorem restore_short_lines (D : IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1)
    (hX : q^2-q+2 ≤ Fintype.card X)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (f : X ↪ P) (J : Finset I) (hJ : q^2+1 ≤ J.card) (r : I → L)
    (hinj : Set.InjOn r (J : Set I))
    (hrow : ∀ i ∈ J, ∀ x, D.inc x i ↔ f x ∈ r i) :
    ∃ R : I ↪ L, (∀ i x, D.inc x i ↔ f x ∈ R i) ∧ ∀ i ∈ J, R i = r i := by
  classical
  let F := (Finset.univ : Finset I).powerset.filter (fun K => J ⊆ K ∧
    ∃ s : I → L, Set.InjOn s (K : Set I) ∧
      (∀ i ∈ K, ∀ x, D.inc x i ↔ f x ∈ s i) ∧ ∀ i ∈ J, s i = r i)
  have hJF : J ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      Finset.Subset.refl _,r,hinj,hrow,fun _ _ => rfl⟩
  obtain ⟨K,hKF,hmax⟩ := Finset.exists_max_image F (fun K => K.card) ⟨J,hJF⟩
  obtain ⟨hJK,s,hsinj,hsrow,hspres⟩ := (Finset.mem_filter.mp hKF).2
  have hKall : K = Finset.univ := by
    by_contra hne
    have hproper : K ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,hne⟩
    obtain ⟨i0,_,hi0⟩ := Finset.exists_of_ssubset hproper
    let M := Finset.univ \ K.image s
    have hsimage : (K.image s).card = K.card := Finset.card_image_iff.mpr hsinj
    have hMpart : M.card+K.card = q^2+q+1 := by
      have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset L) (K.image s)
      simpa only [M,Finset.univ_inter,Finset.card_univ,hsimage,
        Configuration.ProjectivePlane.card_lines P L,ho] using hh
    have hOpart : (Finset.univ \ K).card+K.card = q^2+q+1 := by
      have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset I) K
      simpa only [Finset.univ_inter,Finset.card_univ,hI] using hh
    have hMcard : M.card = (Finset.univ \ K).card := by omega
    have hOpos : 0 < (Finset.univ \ K).card := Finset.card_pos.mpr
      ⟨i0,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi0⟩⟩
    have hMpos : 0 < M.card := by omega
    have hJKcard := Finset.card_le_card hJK
    have hMhi : M.card ≤ q := by omega
    have hstep : ∃ i, i ∉ K ∧ ∃ l, l ∉ K.image s ∧ ∀ x, D.inc x i ↔ f x ∈ l := by
      by_cases hMlo : 2 ≤ M.card
      · obtain ⟨x,l,hl,hxl,hu⟩ := exists_old_unique_missing ho hq f hX M hMlo hMhi
        have hlnot : l ∉ K.image s := (Finset.mem_sdiff.mp hl).2
        obtain ⟨i,hi,hiff⟩ := restore_at_old_point D f K s hsinj hsrow ho x l hlnot hxl
          (fun m hm hxm => hu m (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hm⟩) hxm)
        exact ⟨i,hi,l,hlnot,hiff⟩
      · have hMone : M.card = 1 := by omega
        have hOone : (Finset.univ \ K).card = 1 := by omega
        obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hOone
        obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hMone
        obtain ⟨hiK,hlK,hiff⟩ := restore_last_label D f K s hsinj hsrow ho i hi l hl
        exact ⟨i,hiK,l,hlK,hiff⟩
    obtain ⟨i,hi,l,hl,hiff⟩ := hstep
    obtain ⟨s',hs'inj,hs'row,hs'old⟩ := extend_assignment D f K s hsinj hsrow i hi l hl hiff
    have hnew : insert i K ∈ F := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_,s',hs'inj,hs'row,?_⟩
      · exact fun j hj => Finset.mem_insert.mpr (Or.inr (hJK hj))
      · intro j hj
        exact (hs'old j (hJK hj)).trans (hspres j hj)
    have hh := hmax (insert i K) hnew
    rw [Finset.card_insert_of_notMem hi] at hh
    omega
  let R : I ↪ L := ⟨s,fun a b he => hsinj (by rw [hKall]; simp) (by rw [hKall]; simp) he⟩
  refine ⟨R,?_,hspres⟩
  intro i x
  exact hsrow i (by rw [hKall]; simp) x

/-- The restored indexed-line map is a bijection onto the existing plane's
entire line carrier, by the exact original labelled-line count. -/
theorem restore_short_lines_equiv (D : IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1)
    (hX : q^2-q+2 ≤ Fintype.card X)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (f : X ↪ P) (J : Finset I) (hJ : q^2+1 ≤ J.card) (r : I → L)
    (hinj : Set.InjOn r (J : Set I))
    (hrow : ∀ i ∈ J, ∀ x, D.inc x i ↔ f x ∈ r i) :
    ∃ R : I ≃ L, (∀ i x, D.inc x i ↔ f x ∈ R i) ∧ ∀ i ∈ J, R i = r i := by
  classical
  obtain ⟨R,hinc,hpres⟩ := restore_short_lines D hq hI hX ho f J hJ r hinj hrow
  have hcard : Fintype.card I = Fintype.card L := by
    rw [hI,Configuration.ProjectivePlane.card_lines P L,ho]
  let E : I ≃ L := Equiv.ofBijective R
    ((Fintype.bijective_iff_injective_and_card R).mpr ⟨R.injective,hcard⟩)
  exact ⟨E,hinc,hpres⟩

#print axioms uniquePoints_card
#print axioms exists_old_unique_missing
#print axioms omitted_incidence_card
#print axioms restore_at_old_point
#print axioms restore_last_label
#print axioms extend_assignment
#print axioms restore_short_lines
#print axioms restore_short_lines_equiv
end Erdos60.Embedding.ShortLineRestoration
