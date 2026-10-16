import ParallelCounts
import Mathlib.Combinatorics.Configuration

namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
universe u v
variable {q : ℕ} {X : Type u} {I : Type v} [Fintype X] [Fintype I]

/-- One actual parallel-class extension. The indexed line type is unchanged. -/
noncomputable def extendByClass (D : IndexedDesign q X I) (C : Finset I)
    (hC : C.card = q+1) (hcover : ∀ x : X, ∃! i, i ∈ C ∧ D.inc x i) :
    IndexedDesign q (Option X) I where
  inc x i := match x with
    | none => i ∈ C
    | some x => D.inc x i
  point_degree := by
    intro x
    cases x with
    | none => simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using hC
    | some x => exact D.point_degree x
  unique_join := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (hxy rfl)
      | some y => exact hcover y
    | some x =>
      cases y with
      | none =>
        obtain ⟨i,hi,hu⟩ := hcover x
        exact ⟨i,hi.symm,fun j hj => hu j hj.symm⟩
      | some y => exact D.unique_join x y (fun h => hxy (congrArg Option.some h))

/-- The actual q-point line and all labels missing it form a parallel class. -/
theorem degree_q_parallel_class (D : IndexedDesign q X I)
    (hI : Fintype.card I = q^2+q+1) {i : I} (hi : D.lineDegree i = q) :
    (insert i (D.parallelLines i)).card = q+1 ∧
      ∀ x : X, ∃! j, j ∈ insert i (D.parallelLines i) ∧ D.inc x j := by
  classical
  have hn : i ∉ D.parallelLines i := by simp [Parallel]
  have hp := D.parallel_card_identity i
  rw [hI,hi] at hp
  have hpc : (D.parallelLines i).card = q := by nlinarith
  refine ⟨by rw [Finset.card_insert_of_notMem hn,hpc],?_⟩
  intro x
  by_cases hxi : D.inc x i
  · refine ⟨i,⟨by simp,hxi⟩,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj.1 with h | h
    · exact h
    · exact False.elim (((D.mem_parallelLines i j).mp h).2 x ⟨hxi,hj.2⟩)
  · have hc := D.outside_parallel_count_add hxi
    rw [hi] at hc
    have hone : (D.pointLines x ∩ D.parallelLines i).card = 1 := by omega
    obtain ⟨j,hj,hunique⟩ := Finset.card_eq_one_iff_existsUnique.mp hone
    refine ⟨j,⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mp hj).2),
      (D.mem_pointLines x j).mp (Finset.mem_inter.mp hj).1⟩,?_⟩
    intro k hk
    apply hunique k
    rcases Finset.mem_insert.mp hk.1 with rfl | hkp
    · exact False.elim (hxi hk.2)
    · exact Finset.mem_inter.mpr ⟨(D.mem_pointLines x k).mpr hk.2,hkp⟩

/-- Source3.4 with t=1, preserving every original line label. -/
noncomputable def extendAtDegreeQ (D : IndexedDesign q X I)
    (hI : Fintype.card I = q^2+q+1) (i : I) (hi : D.lineDegree i = q) :
    IndexedDesign q (Option X) I :=
  D.extendByClass (insert i (D.parallelLines i)) (D.degree_q_parallel_class hI hi).1
    (D.degree_q_parallel_class hI hi).2

@[simp] theorem extendAtDegreeQ_old (D : IndexedDesign q X I)
    (hI : Fintype.card I = q^2+q+1) (i : I) (hi : D.lineDegree i = q)
    (x : X) (j : I) : (D.extendAtDegreeQ hI i hi).inc (some x) j ↔ D.inc x j := Iff.rfl

@[simp] theorem extendAtDegreeQ_new (D : IndexedDesign q X I)
    (hI : Fintype.card I = q^2+q+1) (i : I) (hi : D.lineDegree i = q)
    (j : I) : (D.extendAtDegreeQ hI i hi).inc none j ↔ j=i ∨ D.Parallel i j := by
  simp only [extendAtDegreeQ,extendByClass,Finset.mem_insert,D.mem_parallelLines]

/-- In the high-density incomplete branch, a genuine degree-q line exists. -/
theorem exists_degree_q_of_dense_incomplete (D : IndexedDesign q X I)
    (hq : 2 ≤ q) (hI : Fintype.card I = q^2+q+1)
    (hlo : q^2 ≤ Fintype.card X) (hhi : Fintype.card X < q^2+q+1) :
    ∃ i, D.lineDegree i = q := by
  classical
  have hq0 : 0 < q := by omega
  have hX : q+1 < Fintype.card X := by nlinarith
  have hcap := D.lineDegree_le hq0 hI hX
  let s := q^2+q+1-Fintype.card X
  have hs : Fintype.card X+s=q^2+q+1 := by dsimp [s]; omega
  have hsz : 0 < s := by dsimp [s]; omega
  have hsb : s ≤ q+1 := by omega
  by_contra hn
  have hnon : ∀ i : I, 0 ≤ D.intDeficit i*(D.intDeficit i-2) := by
    intro i
    rw [D.intDeficit_eq_nat (hcap i)]
    have hne : D.lineDeficit i ≠ 1 := by
      intro h
      have hd := Nat.sub_add_cancel (hcap i)
      change D.lineDeficit i + D.lineDegree i = q+1 at hd
      exact hn ⟨i,by omega⟩
    by_cases hz : D.lineDeficit i = 0
    · simp [hz]
    · have h2 : 2 ≤ D.lineDeficit i := by omega
      have h2Z : (2 : ℤ) ≤ D.lineDeficit i := by exact_mod_cast h2
      exact mul_nonneg (by positivity) (by omega)
  have hsum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => hnon i)
  rw [D.sum_intDeficit_mul_sub_two s hI hs] at hsum
  have hszZ : (0 : ℤ) < s := by exact_mod_cast hsz
  have hsbZ : (s : ℤ) ≤ q+1 := by exact_mod_cast hsb
  nlinarith

/-- High-density designs cannot have more than the plane number of points. -/
theorem card_points_le_plane (D : IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hlo : q^2 ≤ Fintype.card X) :
    Fintype.card X ≤ q^2+q+1 := by
  have hq0 : 0 < q := by omega
  have hx : q+1 < Fintype.card X := by nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => D.lineDegree_le hq0 hI hx i)
  rw [D.sum_lineDegrees] at hsum
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hI] at hsum
  nlinarith

/-- Construct a full indexed design by induction, adjoining actual points one
at a time. Both old incidence and the original indexed line carrier survive. -/
theorem complete_by_missing (hq : 2 ≤ q) (hI : Fintype.card I = q^2+q+1) (s : ℕ) :
    ∀ (X : Type u) [Fintype X] (D : IndexedDesign q X I),
      q^2 ≤ Fintype.card X → Fintype.card X+s=q^2+q+1 →
      ∃ (Y : Type u) (fY : Fintype Y), letI := fY
        ∃ (E : IndexedDesign q Y I) (f : X ↪ Y),
          Fintype.card Y=q^2+q+1 ∧ ∀ x i, E.inc (f x) i ↔ D.inc x i := by
  induction s with
  | zero =>
    intro X _ D hlo hs
    refine ⟨X,inferInstance,D,Function.Embedding.refl X,?_,?_⟩
    · omega
    · intro x i
      rfl
  | succ s ih =>
    intro X _ D hlo hs
    have hhi : Fintype.card X < q^2+q+1 := by omega
    obtain ⟨i,hi⟩ := D.exists_degree_q_of_dense_incomplete hq hI hlo hhi
    let E := D.extendAtDegreeQ hI i hi
    have hlo' : q^2 ≤ Fintype.card (Option X) := by simp; omega
    have hs' : Fintype.card (Option X)+s=q^2+q+1 := by simp; omega
    obtain ⟨Y,fY,F,f,hY,hinc⟩ := ih (Option X) E hlo' hs'
    let : Fintype Y := fY
    let g : X ↪ Y := ⟨fun x => f (some x),fun x y h => Option.some.inj (f.injective h)⟩
    refine ⟨Y,fY,F,g,hY,?_⟩
    intro x j
    exact (hinc (some x) j).trans (D.extendAtDegreeQ_old hI i hi x j)

theorem exists_full_extension (D : IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hlo : q^2 ≤ Fintype.card X) :
    ∃ (Y : Type u) (fY : Fintype Y), letI := fY
      ∃ (E : IndexedDesign q Y I) (f : X ↪ Y),
        Fintype.card Y=q^2+q+1 ∧ ∀ x i, E.inc (f x) i ↔ D.inc x i := by
  have hc := D.card_points_le_plane hq hI hlo
  exact complete_by_missing hq hI (q^2+q+1-Fintype.card X) X D hlo (by omega)

/-- A full indexed design is an actual nondegenerate projective plane. -/
theorem full_count_plane (D : IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hX : Fintype.card X = q^2+q+1) :
    letI := D.membership
    Nonempty (Configuration.ProjectivePlane X I) := by
  classical
  let : Membership X I := D.membership
  have hq0 : 0 < q := by omega
  have hxlarge : q+1 < Fintype.card X := by rw [hX]; nlinarith
  have hcap := D.lineDegree_le hq0 hI hxlarge
  have hfull : ∀ i : I, D.lineDegree i = q+1 := by
    have hs : (∑ i : I, D.lineDegree i) = ∑ _i : I, (q+1) := by
      rw [D.sum_lineDegrees]
      simp [hX,hI]
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => hcap i)).mp hs i (Finset.mem_univ i)
  have hoff : ∀ i : I, ∃ x, ¬D.inc x i := fun i => D.exists_point_off_line hq0 hI hxlarge i
  let : Configuration.Nondegenerate X I := {
    exists_point := hoff
    exists_line := by
      intro x
      have hc : (D.pointLines x).card < (Finset.univ : Finset I).card := by
        rw [D.card_pointLines,Finset.card_univ,hI]
        nlinarith
      obtain ⟨i,_,hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
      refine ⟨i,?_⟩
      change ¬D.inc x i
      simpa only [D.mem_pointLines] using hi
    eq_or_eq := by
      intro x y i j hxi hyi hxj hyj
      by_cases hxy : x=y
      · exact Or.inl hxy
      · exact Or.inr (D.join_unique hxy hxi hyi hxj hyj) }
  let : Configuration.HasLines X I := {
    toNondegenerate := inferInstance
    mkLine := fun h => (D.unique_join _ _ h).choose
    mkLine_ax := fun h => (D.unique_join _ _ h).choose_spec.1 }
  let : Configuration.HasPoints X I := Configuration.HasLines.hasPoints (by omega)
  obtain ⟨l2⟩ : Nonempty I := Fintype.card_pos_iff.mp (by rw [hI]; positivity)
  have hl2 : 1 < (D.linePoints l2).card := by change 1 < D.lineDegree l2; rw [hfull]; omega
  obtain ⟨p2,hp2,p3,hp3,h23⟩ := Finset.one_lt_card.mp hl2
  have hp2l : D.inc p2 l2 := (D.mem_linePoints l2 p2).mp hp2
  have hp3l : D.inc p3 l2 := (D.mem_linePoints l2 p3).mp hp3
  obtain ⟨p1,hp1l⟩ := hoff l2
  have h12 : p1 ≠ p2 := by intro h; exact hp1l (h.symm ▸ hp2l)
  have h13 : p1 ≠ p3 := by intro h; exact hp1l (h.symm ▸ hp3l)
  obtain ⟨j12,hj12,_⟩ := D.unique_join p1 p2 h12
  obtain ⟨j13,hj13,_⟩ := D.unique_join p1 p3 h13
  have hsmall3 : ({l2,j12} : Finset I).card < (D.pointLines p2).card := by
    have hh : ({l2,j12} : Finset I).card ≤ 2 := Finset.card_le_two
    rw [D.card_pointLines]
    omega
  obtain ⟨l3,hl3,hl3not⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall3
  have hp2l3 : D.inc p2 l3 := (D.mem_pointLines p2 l3).mp hl3
  have hl3ne2 : l3 ≠ l2 := by intro h; apply hl3not; simp [h]
  have hl3ne12 : l3 ≠ j12 := by intro h; apply hl3not; simp [h]
  have hp1l3 : ¬D.inc p1 l3 := by
    intro h
    exact hl3ne12 (D.join_unique h12 h hp2l3 hj12.1 hj12.2)
  have hp3l3 : ¬D.inc p3 l3 := by
    intro h
    exact hl3ne2 (D.join_unique h23 hp2l3 h hp2l hp3l)
  have hsmall1 : ({j12,j13} : Finset I).card < (D.pointLines p1).card := by
    have hh : ({j12,j13} : Finset I).card ≤ 2 := Finset.card_le_two
    rw [D.card_pointLines]
    omega
  obtain ⟨l1,hl1,hl1not⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall1
  have hp1l1 : D.inc p1 l1 := (D.mem_pointLines p1 l1).mp hl1
  have hp2l1 : ¬D.inc p2 l1 := by
    intro h
    have he := D.join_unique h12 hp1l1 h hj12.1 hj12.2
    exact hl1not (by simp [he])
  have hp3l1 : ¬D.inc p3 l1 := by
    intro h
    have he := D.join_unique h13 hp1l1 h hj13.1 hj13.2
    exact hl1not (by simp [he])
  exact ⟨{ (inferInstance : Configuration.HasLines X I),
    (inferInstance : Configuration.HasPoints X I) with
    exists_config := ⟨p1,p2,p3,l1,l2,l3,hp1l,hp1l3,hp2l1,hp2l,hp2l3,hp3l1,hp3l,hp3l3⟩ }⟩

theorem plane_order_eq (D : IndexedDesign q X I)
    (hX : 0 < Fintype.card X) :
    letI := D.membership
    ∀ (_ : Configuration.ProjectivePlane X I), Configuration.ProjectivePlane.order X I = q := by
  let : Membership X I := D.membership
  intro pp
  let : Configuration.ProjectivePlane X I := pp
  obtain ⟨x⟩ : Nonempty X := Fintype.card_pos_iff.mp hX
  have hd : Configuration.lineCount I x = q+1 := D.point_degree x
  have hp := Configuration.ProjectivePlane.lineCount_eq (L := I) x
  omega

/-- Source3.5(a): actual high-density projective-plane completion, with an
injective point map, exact old incidence, and every indexed line label retained. -/
theorem dense_plane_extension (D : IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hlo : q^2 ≤ Fintype.card X) :
    ∃ (Y : Type u) (fY : Fintype Y), letI := fY
      ∃ (E : IndexedDesign q Y I) (f : X ↪ Y),
        Fintype.card Y=q^2+q+1 ∧
        (∀ x i, E.inc (f x) i ↔ D.inc x i) ∧
        (letI := E.membership
          ∃ pp : Configuration.ProjectivePlane Y I,
            letI := pp
            Configuration.ProjectivePlane.order Y I = q) := by
  classical
  obtain ⟨Y,fY,E,f,hY,hinc⟩ := D.exists_full_extension hq hI hlo
  let : Fintype Y := fY
  obtain ⟨pp⟩ := E.full_count_plane hq hI hY
  refine ⟨Y,fY,E,f,hY,hinc,pp,?_⟩
  exact E.plane_order_eq (by rw [hY]; positivity) pp

#print axioms degree_q_parallel_class
#print axioms extendAtDegreeQ
#print axioms exists_degree_q_of_dense_incomplete
#print axioms complete_by_missing
#print axioms exists_full_extension
#print axioms full_count_plane
#print axioms plane_order_eq
#print axioms dense_plane_extension
end Erdos60.Embedding.IndexedDesign
