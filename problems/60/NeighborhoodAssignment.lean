import NeighborhoodLines
import CompletionBasic
import PartialSymmetryFinal
import Polarity
import Mathlib.Tactic
/-!
Actual source-to-formal correspondence: COUNT-BASED-COMPLETION.md
Historical source SHA256 (before public exposition edits): d07eaa46889ac5a9808a097f281e43c25a768e5057e19ddefe5b72952d9eacbb,
§§6–7. All cycles in this file are ordinary C4s; ambient diagonals are allowed.

The frozen NeighborhoodLines geometric injections are used on actual plane
points and lines. The at-most-three pencil decomposition is constructed here
as actual finite line fibers, without assuming near-collinearity or the
existence of a dominant line. The one global exception and point-to-line
bijection are then constructed. Cross-block symmetry follows from actual
row/column cardinal equality, and the proved PartialSymmetryFinal theorem
provides reciprocity. The resulting actual polarity contains every edge.

`embedded_rows_produce_polarity` has no assumed polarity, line-assignment,
near-collinearity, or reciprocity conclusion. Its remaining explicit inputs
are an actual projective plane with embedded full rows, the original graph
C4-freeness/minimum degree, the missing-line population bound, the
high-incidence-neighbor producer, and the full-row population bound. Existing
HighIncidenceNeighbor and ExceptionalSet suppliers can discharge the latter
inputs; actual projective embedding remains a separate unproved supplier.
-/
namespace Erdos60.Completion
open scoped Classical
open Configuration
variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]
variable [Configuration.ProjectivePlane P L]

omit [Fintype P] [Fintype L] [Configuration.ProjectivePlane P L] in
/-- An actual noncollinear graph neighborhood has all its pair-lines outside
any family of actual graph-neighborhood rows. -/
theorem nonfeasible_pair_lines_missing (G : SimpleGraph P) (hG : NoFourCycle G)
    (A : Finset P) (row : P → L)
    (hrow : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x)
    (v : P) (hnon : ¬∃ l : L, ∀ x, G.Adj v x → x ∈ l)
    (x y : P) (hxy : x ≠ y) (hvx : G.Adj v x) (hvy : G.Adj v y)
    (l : L) (hxl : x ∈ l) (hyl : y ∈ l) :
    l ∉ A.image row := by
  classical
  intro hl
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hl
  subst l
  by_cases hav : a = v
  · subst a
    exact hnon ⟨row v,fun z hz => (hrow v ha z).mpr hz⟩
  · exact hxy (common_neighbor_unique hG (Ne.symm hav) hvx ((hrow a ha x).mp hxl)
      hvy ((hrow a ha y).mp hyl))

omit [Fintype P] [Fintype L] in
/-- The actual at-most-three missing lines through one selected neighbor
produce a dominant actual line with at most six neighborhood outliers. -/
theorem small_pencil_dominant (N : Finset P) (M : Finset L) (u : P)
    (q : ℝ) (hq : 10^8 ≤ q) (hN : 999*q/1000 ≤ N.card)
    (hM : (M.card : ℝ) ≤ 1002*q/1000) (hu : u ∈ N)
    (hpencil : (M.filter fun l => u ∈ l).card ≤ 3)
    (hpair : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → ∀ l : L, x ∈ l → y ∈ l → l ∈ M) :
    ∃ l : L, (N.filter fun x => x ∉ l).card ≤ 6 := by
  classical
  let R := M.filter fun l => u ∈ l
  let F := fun l : L => (N.erase u).filter fun x => x ∈ l
  have hcover : N.erase u ⊆ R.biUnion F := by
    intro x hx
    have hxN := (Finset.mem_erase.mp hx).2
    have hux : u ≠ x := (Finset.mem_erase.mp hx).1.symm
    let l := Configuration.HasLines.mkLine (L := L) hux
    have hh := Configuration.HasLines.mkLine_ax (L := L) hux
    exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr
      ⟨hpair u hu x hxN hux l hh.1 hh.2,hh.1⟩,Finset.mem_filter.mpr ⟨hx,hh.2⟩⟩
  have hRN : R.Nonempty := by
    have hn2 : 2 ≤ N.card := by
      have hc : (2:ℝ) ≤ N.card := by linarith
      exact_mod_cast hc
    have hec : 0 < (N.erase u).card := by rw [Finset.card_erase_of_mem hu]; omega
    obtain ⟨x,hx⟩ := Finset.card_pos.mp hec
    obtain ⟨l,hl,hxl⟩ := Finset.mem_biUnion.mp (hcover hx)
    exact ⟨l,hl⟩
  obtain ⟨l,hl,hmax⟩ := Finset.exists_max_image R (fun l => (F l).card) hRN
  have hsum : (N.erase u).card ≤ ∑ m ∈ R, (F m).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h3 : N.card ≤ 1+3*(F l).card := by
    have hsum' : (∑ m ∈ R, (F m).card) ≤ R.card*(F l).card := by
      calc
        _ ≤ ∑ _m ∈ R, (F l).card := Finset.sum_le_sum (fun m hm => hmax m hm)
        _ = _ := by simp
    have hm : R.card * (F l).card ≤ 3*(F l).card := Nat.mul_le_mul_right ((F l).card) hpencil
    rw [Finset.card_erase_of_mem hu] at hsum
    change R.card ≤ 3 at hpencil
    omega
  have hsmall : ∀ m ∈ R.erase l, (F m).card ≤ 3 := by
    intro m hm
    have hml : m ≠ l := (Finset.mem_erase.mp hm).1
    have hmR := (Finset.mem_erase.mp hm).2
    have hul : u ∈ l := (Finset.mem_filter.mp hl).2
    have hum : u ∈ m := (Finset.mem_filter.mp hmR).2
    have hoff : ∀ {n k : L}, n ≠ k → u ∈ n → u ∈ k →
        ∀ x ∈ F n, x ∉ k := by
      intro n k hnk hun huk x hx hxk
      have hx' := Finset.mem_filter.mp hx
      have hxu := (Finset.mem_erase.mp hx'.1).1
      exact hxu (Configuration.Nondegenerate.eq_or_eq hx'.2 hun hxk huk |>.resolve_right hnk)
    have hprod := cross_pairs_le_missing (F l) (F m) M l m
      (fun x hx => ⟨(Finset.mem_filter.mp hx).2,hoff hml.symm hul hum x hx⟩)
      (fun x hx => ⟨(Finset.mem_filter.mp hx).2,hoff hml hum hul x hx⟩)
      (fun x hx y hy n hxn hyn => hpair x ((Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2)
        y ((Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2)
        (fun he => hoff hml hum hul y hy (he ▸ (Finset.mem_filter.mp hx).2)) n hxn hyn)
    have h3R : (N.card : ℝ) ≤ 1+3*((F l).card : ℝ) := by exact_mod_cast h3
    have hprodR : ((F l).card : ℝ)*((F m).card : ℝ) ≤ M.card := by exact_mod_cast hprod
    by_contra hh
    have hh4 : (4:ℝ) ≤ (F m).card := by exact_mod_cast (show 4 ≤ (F m).card by omega)
    have hmul := mul_nonneg (show 0 ≤ ((F l).card : ℝ) by positivity) (sub_nonneg.mpr hh4)
    nlinarith
  have hout : N.filter (fun x => x ∉ l) ⊆ (R.erase l).biUnion F := by
    intro x hx
    obtain ⟨hxN,hxl⟩ := Finset.mem_filter.mp hx
    have hxu : x ≠ u := by intro he; subst x; exact hxl (Finset.mem_filter.mp hl).2
    obtain ⟨m,hm,hxm⟩ := Finset.mem_biUnion.mp (hcover (Finset.mem_erase.mpr ⟨hxu,hxN⟩))
    have hml : m ≠ l := by intro he; subst m; exact hxl (Finset.mem_filter.mp hxm).2
    exact Finset.mem_biUnion.mpr ⟨m,Finset.mem_erase.mpr ⟨hml,hm⟩,hxm⟩
  refine ⟨l,?_⟩
  have hb := (Finset.card_le_card hout).trans Finset.card_biUnion_le
  have hs : (∑ m ∈ R.erase l, (F m).card) ≤ (R.erase l).card*3 := by
    calc
      _ ≤ ∑ _m ∈ R.erase l, 3 := Finset.sum_le_sum hsmall
      _ = _ := by simp
  rw [Finset.card_erase_of_mem hl] at hs
  change R.card ≤ 3 at hpencil
  omega

omit [Fintype L] [Configuration.ProjectivePlane P L] in
theorem actual_full_rows_injOn (G : SimpleGraph P) (hG : NoFourCycle G)
    (A : Finset P) (row : P → L) (q : ℕ) (hq : 1 ≤ q)
    (hfull : ∀ a ∈ A, G.degree a = q+1)
    (hrow : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x) : Set.InjOn row (A : Set P) := by
  classical
  intro a ha b hb he
  by_contra hab
  have hc : (G.neighborFinset a).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hax : G.Adj a x := by simpa using hx
    have hay : G.Adj a y := by simpa using hy
    have hbx : G.Adj b x := (hrow b hb x).mp (he ▸ (hrow a ha x).mpr hax)
    have hby : G.Adj b y := (hrow b hb y).mp (he ▸ (hrow a ha y).mpr hay)
    exact common_neighbor_unique hG hab hax hbx hay hby
  rw [SimpleGraph.card_neighborFinset_eq_degree,hfull a ha] at hc
  omega

/-- A high-incidence neighbor leaves at most three actual missing lines in
its pencil. The represented lines are the actual full graph rows. -/
theorem high_incidence_small_missing_pencil (G : SimpleGraph P) (A : Finset P)
    (row : P → L) (M : Finset L) (q : ℕ) (hq : 2 ≤ q)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (hinj : Set.InjOn row (A : Set P))
    (hrow : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x)
    (hmissing : ∀ a ∈ A, row a ∉ M)
    (u : P) (hhigh : q-2 ≤ (G.neighborFinset u ∩ A).card) :
    (M.filter fun l => u ∈ l).card ≤ 3 := by
  classical
  let H := G.neighborFinset u ∩ A
  let I := H.image row
  let J := M.filter fun l => u ∈ l
  have hIc : I.card = H.card := Finset.card_image_iff.mpr (fun a ha b hb he =>
    hinj (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2 he)
  have hdis : Disjoint J I := by
    apply Finset.disjoint_left.mpr
    intro l hl hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    exact hmissing a (Finset.mem_inter.mp ha).2 (Finset.mem_filter.mp hl).1
  have hsub : J ∪ I ⊆ Finset.univ.filter (fun l : L => u ∈ l) := by
    intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      have hua : G.Adj u a := by simpa using (Finset.mem_inter.mp ha).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hrow a (Finset.mem_inter.mp ha).2 u).mpr hua.symm⟩
  have hb := Finset.card_le_card hsub
  have hpc : (Finset.univ.filter (fun l : L => u ∈ l)).card = q+1 := by
    simpa [Configuration.lineCount,Nat.card_eq_fintype_card,Fintype.card_subtype,ho] using
      Configuration.ProjectivePlane.lineCount_eq L u
  rw [Finset.card_union_of_disjoint hdis,hIc,hpc] at hb
  change J.card ≤ 3
  change q-2 ≤ H.card at hhigh
  omega

/-- Actual near-collinearity for every graph neighborhood once the plane and
high-incidence neighbor producer are supplied. Feasible rows are chosen exact. -/
theorem neighborhood_dominant_lines (G : SimpleGraph P) (hG : NoFourCycle G)
    (A : Finset P) (row : P → L) (q : ℕ) (hq : 10^8 ≤ q)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (hfull : ∀ a ∈ A, G.degree a = q+1)
    (hrow : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x)
    (hmin : ∀ v, (999:ℝ)*q/1000 ≤ G.degree v)
    (hmissing : ((Finset.univ \ A.image row).card : ℝ) ≤ (1002:ℝ)*q/1000)
    (hhigh : ∀ v, ∃ u, G.Adj v u ∧ q-2 ≤ (G.neighborFinset u ∩ A).card) :
    ∀ v, ∃ l : L, ((G.neighborFinset v).filter fun x => x ∉ l).card ≤ 6 ∧
      ((∃ m : L, ∀ x, G.Adj v x → x ∈ m) → ∀ x, G.Adj v x → x ∈ l) := by
  classical
  intro v
  by_cases hf : ∃ m : L, ∀ x, G.Adj v x → x ∈ m
  · obtain ⟨l,hl⟩ := hf
    refine ⟨l,?_,fun _ => hl⟩
    have he : ((G.neighborFinset v).filter fun x => x ∉ l) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx,hxl⟩ := Finset.mem_filter.mp hx
      exact hxl (hl x (by simpa using hx))
    rw [he]; simp
  · let M := Finset.univ \ A.image row
    have hpair : ∀ x ∈ G.neighborFinset v, ∀ y ∈ G.neighborFinset v, x ≠ y →
        ∀ l : L, x ∈ l → y ∈ l → l ∈ M := by
      intro x hx y hy hxy l hxl hyl
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,nonfeasible_pair_lines_missing G hG A row hrow v hf x y hxy
        (by simpa using hx) (by simpa using hy) l hxl hyl⟩
    obtain ⟨u,hvu,hhighu⟩ := hhigh v
    have hp := high_incidence_small_missing_pencil G A row M q (by omega) ho
      (actual_full_rows_injOn G hG A row q (by omega) hfull hrow) hrow
      (fun a ha hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_image.mpr ⟨a,ha,rfl⟩)) u hhighu
    obtain ⟨l,hl⟩ := small_pencil_dominant (G.neighborFinset v) M u q (by exact_mod_cast hq)
      (by simpa using hmin v) hmissing (by simpa using hvu) hp hpair
    exact ⟨l,hl,fun h => False.elim (hf h)⟩

omit [Fintype L] [Configuration.ProjectivePlane P L] in
theorem dominant_section_large (G : SimpleGraph P) (f : P → L) (v : P) (q : ℝ)
    (hmin : 999*q/1000 ≤ G.degree v)
    (hdom : ((G.neighborFinset v).filter fun x => x ∉ f v).card ≤ 6) :
    999*q/1000-6 ≤ (((G.neighborFinset v).filter fun x => x ∈ f v).card : ℝ) := by
  classical
  have hh := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v) (fun x => x ∈ f v)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
  have hhr : ((((G.neighborFinset v).filter fun x => x ∈ f v).card : ℝ) +
      (((G.neighborFinset v).filter fun x => x ∉ f v).card : ℝ)) = G.degree v := by exact_mod_cast hh
  have hd : (((G.neighborFinset v).filter fun x => x ∉ f v).card : ℝ) ≤ 6 := by exact_mod_cast hdom
  linarith

/-- All actual off-line neighborhood points coincide globally. -/
theorem dominant_lines_common_exception (G : SimpleGraph P) (hG : NoFourCycle G)
    (A : Finset P) (row f : P → L) (q : ℕ) (hq : 10^8 ≤ q)
    (hrow : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x)
    (hmin : ∀ v, (999:ℝ)*q/1000 ≤ G.degree v)
    (hmissing : ((Finset.univ \ A.image row).card : ℝ) ≤ (1002:ℝ)*q/1000)
    (hdom : ∀ v, ((G.neighborFinset v).filter fun x => x ∉ f v).card ≤ 6)
    (hfeas : ∀ v, (∃ m : L, ∀ x, G.Adj v x → x ∈ m) → ∀ x, G.Adj v x → x ∈ f v) :
    ∃ w : P, ∀ v x, G.Adj v x → x ≠ w → x ∈ f v := by
  classical
  have hsame : ∀ v w v' z, G.Adj v w → w ∉ f v → G.Adj v' z → z ∉ f v' → w = z := by
    intro v w v' z hvw hw hvz hz
    have hvnon : ¬∃ m : L, ∀ x, G.Adj v x → x ∈ m := fun h => hw (hfeas v h w hvw)
    have hvnon' : ¬∃ m : L, ∀ x, G.Adj v' x → x ∈ m := fun h => hz (hfeas v' h z hvz)
    let M := Finset.univ \ A.image row
    let C := (G.neighborFinset v).filter fun x => x ∈ f v
    let D := (G.neighborFinset v').filter fun x => x ∈ f v'
    apply common_exception_point C D M (f v) (f v') w z q (by exact_mod_cast hq)
      hmissing (dominant_section_large G f v q (hmin v) (hdom v))
      (dominant_section_large G f v' q (hmin v') (hdom v')) hw hz
      (fun a ha => (Finset.mem_filter.mp ha).2)
      (fun b hb => (Finset.mem_filter.mp hb).2)
    · intro a ha l hwl hal
      have hwa : w ≠ a := fun he => hw (he ▸ (Finset.mem_filter.mp ha).2)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,nonfeasible_pair_lines_missing G hG A row hrow
        v hvnon w a hwa hvw (by simpa using (Finset.mem_filter.mp ha).1) l hwl hal⟩
    · intro b hb l hzl hbl
      have hzb : z ≠ b := fun he => hz (he ▸ (Finset.mem_filter.mp hb).2)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,nonfeasible_pair_lines_missing G hG A row hrow
        v' hvnon' z b hzb hvz (by simpa using (Finset.mem_filter.mp hb).1) l hzl hbl⟩
  by_cases hb : ∃ v w, G.Adj v w ∧ w ∉ f v
  · obtain ⟨v,w,hvw,hw⟩ := hb
    refine ⟨w,?_⟩
    intro v' z hvz hzw
    by_contra hz
    exact hzw (hsame v' z v w hvz hz hvw hw)
  · obtain ⟨w,hw⟩ := Configuration.ProjectivePlane.exists_config (P := P) (L := L)
    refine ⟨w,?_⟩
    intro v x hvx hxw
    by_contra hxl
    exact hb ⟨v,x,hvx,hxl⟩

/-- Actual almost-contained neighborhoods of a C4-free dense graph determine
distinct assigned lines; no assignment bijection is assumed. -/
theorem neighborhood_line_assignment_injective (G : SimpleGraph P) (hG : NoFourCycle G)
    (f : P → L) (w : P) (q : ℕ) (hq : 10^8 ≤ q)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (hmin : ∀ v, (999:ℝ)*q/1000 ≤ G.degree v)
    (hcontain : ∀ v x, G.Adj v x → x ≠ w → x ∈ f v) : Function.Injective f := by
  classical
  intro a b he
  by_contra hab
  let X := (G.neighborFinset a).erase w
  let Y := (G.neighborFinset b).erase w
  have hcarderase (Z : Finset P) : Z.card ≤ (Z.erase w).card+1 := by
    by_cases hw : w ∈ Z
    · have hh := Finset.card_erase_add_one hw
      omega
    · rw [Finset.erase_eq_of_notMem hw]
      omega
  have hX : (G.degree a : ℝ)-1 ≤ X.card := by
    have hc : G.degree a ≤ X.card+1 := by simpa [X] using hcarderase (G.neighborFinset a)
    have hcR : (G.degree a : ℝ) ≤ (X.card : ℝ)+1 := by exact_mod_cast hc
    linarith
  have hY : (G.degree b : ℝ)-1 ≤ Y.card := by
    have hc : G.degree b ≤ Y.card+1 := by simpa [Y] using hcarderase (G.neighborFinset b)
    have hcR : (G.degree b : ℝ) ≤ (Y.card : ℝ)+1 := by exact_mod_cast hc
    linarith
  have hi : (X ∩ Y).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxa : G.Adj a x := by simpa using (Finset.mem_erase.mp (Finset.mem_inter.mp hx).1).2
    have hxb : G.Adj b x := by simpa using (Finset.mem_erase.mp (Finset.mem_inter.mp hx).2).2
    have hya : G.Adj a y := by simpa using (Finset.mem_erase.mp (Finset.mem_inter.mp hy).1).2
    have hyb : G.Adj b y := by simpa using (Finset.mem_erase.mp (Finset.mem_inter.mp hy).2).2
    exact common_neighbor_unique hG hab hxa hxb hya hyb
  have hs : X ∪ Y ⊆ Finset.univ.filter (fun x => x ∈ f a) := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hcontain a x (by simpa using (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1
    · rw [he]
      exact hcontain b x (by simpa using (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1
  have hc : (Finset.univ.filter (fun x => x ∈ f a)).card = q+1 := by
    simpa [Configuration.pointCount,Nat.card_eq_fintype_card,Fintype.card_subtype,ho] using
      Configuration.ProjectivePlane.pointCount_eq P (f a)
  have hu := Finset.card_le_card hs
  rw [hc] at hu
  have hh := Finset.card_union_add_card_inter X Y
  have hsum : X.card+Y.card ≤ q+2 := by omega
  have hsumR : (X.card : ℝ)+Y.card ≤ (q:ℝ)+2 := by exact_mod_cast hsum
  have hma := hmin a
  have hmb := hmin b
  have hqr : (10^8:ℝ) ≤ q := by exact_mod_cast hq
  linarith

omit [Fintype L] in
theorem assigned_full_row_eq (G : SimpleGraph P) (A : Finset P) (row f : P → L)
    (w : P) (q : ℕ) (hq : 2 ≤ q)
    (hfull : ∀ a ∈ A, G.degree a = q+1)
    (hrow : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x)
    (hcontain : ∀ v x, G.Adj v x → x ≠ w → x ∈ f v)
    (a : P) (ha : a ∈ A) : f a = row a := by
  classical
  let X := (G.neighborFinset a).erase w
  have hc : 1 < X.card := by
    have hh : (G.neighborFinset a).card-1 ≤ X.card := Finset.pred_card_le_card_erase
    rw [SimpleGraph.card_neighborFinset_eq_degree,hfull a ha] at hh
    omega
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hc
  have hx' := Finset.mem_erase.mp hx
  have hy' := Finset.mem_erase.mp hy
  have hax : G.Adj a x := by simpa using hx'.2
  have hay : G.Adj a y := by simpa using hy'.2
  exact (Configuration.Nondegenerate.eq_or_eq
    (hcontain a x hax hx'.1) (hcontain a y hay hy'.1)
    ((hrow a ha x).mpr hax) ((hrow a ha y).mpr hay)).resolve_left hxy

/-- The actual bijection extends full graph rows to symmetric row/column
indices by equality of actual plane row and column cardinalities. -/
theorem assigned_full_rows_symmetric (G : SimpleGraph P) (A : Finset P)
    (line : P ≃ L) (w : P)
    (hrow : ∀ a ∈ A, ∀ x, x ∈ line a ↔ G.Adj a x)
    (hcontain : ∀ v x, G.Adj v x → x ≠ w → x ∈ line v) :
    Erdos60.PartialSymmetry.SymmetricAt line ((A.erase w : Finset P) : Set P) := by
  classical
  intro a ha b
  have ha' := Finset.mem_erase.mp ha
  let R := Finset.univ.filter (fun x : P => x ∈ line a)
  let C := Erdos60.PartialSymmetryFinal.transposeRow line a
  have hs : R ⊆ C := by
    intro x hx
    have hxa : x ∈ line a := (Finset.mem_filter.mp hx).2
    have hax := (hrow a ha'.2 x).mp hxa
    exact (Erdos60.PartialSymmetryFinal.mem_transposeRow line a x).mpr
      (hcontain x a hax.symm ha'.1)
  have hR : R.card = Configuration.ProjectivePlane.order P L+1 := by
    simpa [R,Configuration.pointCount,Nat.card_eq_fintype_card,Fintype.card_subtype] using
      Configuration.ProjectivePlane.pointCount_eq P (line a)
  have hC := Erdos60.PartialSymmetryFinal.transposeRow_card line a
  have he : R = C := Finset.eq_of_subset_of_card_le hs (by rw [hR]; exact hC.le)
  have hh := Finset.ext_iff.mp he b
  simpa [R,C,Erdos60.PartialSymmetryFinal.mem_transposeRow] using hh.symm

/-- Completion after actual plane embedding. The near-collinearity,
common exception, bijection, and reciprocity are all produced internally;
only the actual embedded full rows and proved-later high-incidence producer
are inputs. No polarity existence premise is used. -/
theorem embedded_rows_produce_polarity (G : SimpleGraph P) (hG : NoFourCycle G)
    (A : Finset P) (row : P → L) (q : ℕ) (hq : 10^8 ≤ q)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (hfull : ∀ a ∈ A, G.degree a = q+1)
    (hrow : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x)
    (hmin : ∀ v, (999:ℝ)*q/1000 ≤ G.degree v)
    (hmissing : ((Finset.univ \ A.image row).card : ℝ) ≤ (1002:ℝ)*q/1000)
    (hhigh : ∀ v, ∃ u, G.Adj v u ∧ q-2 ≤ (G.neighborFinset u ∩ A).card)
    (hAsize : q^2-q+4 ≤ A.card) :
    ∃ π : Erdos60.Geometry.Polarity (P := P) (L := L), G ≤ π.graph := by
  classical
  have hex := neighborhood_dominant_lines G hG A row q hq ho hfull hrow hmin hmissing hhigh
  choose f hdom hfeas using hex
  obtain ⟨w,hcontain⟩ := dominant_lines_common_exception G hG A row f q hq hrow hmin hmissing hdom hfeas
  have hinj := neighborhood_line_assignment_injective G hG f w q hq ho hmin hcontain
  have hcard : Fintype.card P = Fintype.card L :=
    (Configuration.ProjectivePlane.card_points P L).trans (Configuration.ProjectivePlane.card_lines P L).symm
  let line : P ≃ L := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩)
  have hrow' : ∀ a ∈ A, ∀ x, x ∈ line a ↔ G.Adj a x := by
    intro a ha x
    change x ∈ f a ↔ _
    rw [assigned_full_row_eq G A row f w q (by omega) hfull hrow hcontain a ha]
    exact hrow a ha x
  have hs := assigned_full_rows_symmetric G A line w hrow' hcontain
  have hgood : Configuration.ProjectivePlane.order P L^2-
      Configuration.ProjectivePlane.order P L+3 ≤ (A.erase w).card := by
    rw [ho]
    have hh : A.card-1 ≤ (A.erase w).card := Finset.pred_card_le_card_erase
    omega
  have hrec := Erdos60.PartialSymmetryFinal.partial_symmetry line (A.erase w) hs hgood
  let π : Erdos60.Geometry.Polarity (P := P) (L := L) := ⟨line,hrec⟩
  refine ⟨π,?_⟩
  intro a b hab
  refine ⟨hab.ne,?_⟩
  by_cases hb : b = w
  · subst b
    exact hcontain w a hab.symm hab.ne
  · exact (hrec a b).mpr (hcontain a b hab hb)

#print axioms assigned_full_row_eq
#print axioms assigned_full_rows_symmetric
#print axioms embedded_rows_produce_polarity
#print axioms dominant_lines_common_exception
#print axioms neighborhood_line_assignment_injective
#print axioms actual_full_rows_injOn
#print axioms high_incidence_small_missing_pencil
#print axioms neighborhood_dominant_lines
#print axioms nonfeasible_pair_lines_missing
#print axioms small_pencil_dominant
end Erdos60.Completion
