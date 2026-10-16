import CliqueCoverage
import GreedyExtension
import ShortLineRestoration
import Mathlib.Combinatorics.Configuration

/-! Metsch source6.10: actual new symbols indexed by actual maximal good
parallel cliques. The original indexed line carrier is retained. Every
construction below has an explicit incidence relation and proved laws. -/
namespace Erdos60.Embedding.IndexedDesign
open Finset
open scoped Classical
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

/-- Source's P union P': the sum prevents any old/new or clique-symbol collapse. -/
abbrev RealizedPoint (D : IndexedDesign q X I) (e a : ℕ) :=
  X ⊕ ↥(D.goodCliques e a)

/-- Every original label is still available, even if the line is short. -/
def realizedInc (D : IndexedDesign q X I) (e a : ℕ) : D.RealizedPoint e a → I → Prop
  | .inl x, i => D.inc x i
  | .inr C, i => i ∈ C.val

@[simp] theorem realizedInc_old (D : IndexedDesign q X I) (e a : ℕ) (x : X) (i : I) :
    D.realizedInc e a (.inl x) i ↔ D.inc x i := Iff.rfl

@[simp] theorem realizedInc_new (D : IndexedDesign q X I) (e a : ℕ)
    (C : ↥(D.goodCliques e a)) (i : I) :
    D.realizedInc e a (.inr C) i ↔ i ∈ C.val := Iff.rfl

/-- Literal cardinality of the constructed point carrier. -/
theorem realizedPoint_card (D : IndexedDesign q X I) (e a s : ℕ)
    (hX : Fintype.card X+s = q^2+q+1) (hC : (D.goodCliques e a).card = s) :
    Fintype.card (D.RealizedPoint e a) = q^2+q+1 := by
  simpa only [RealizedPoint,Fintype.card_sum,Fintype.card_coe,hC] using hX

/-- A realized line contains exactly its old points and its actual clique symbols. -/
theorem realized_line_card (D : IndexedDesign q X I) (e a : ℕ) (i : I) :
    Nat.card {p : D.RealizedPoint e a // D.realizedInc e a p i} =
      D.lineDegree i + ((D.goodCliques e a).filter fun C => i ∈ C).card := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]
  congr 1
  · change Fintype.card {x : X // D.inc x i} = D.lineDegree i
    rw [Fintype.card_subtype]
    rfl
  · rw [Fintype.card_subtype]
    exact Finset.card_bij (fun C _ => C.val)
      (by intro C hC; simpa using (Finset.mem_filter.mp hC).2)
      (by intro C hC E hE he; exact Subtype.ext he)
      (by intro C hC; exact ⟨⟨C,(Finset.mem_filter.mp hC).1⟩,
        by simpa using (Finset.mem_filter.mp hC).2,rfl⟩)

/-- Source6.9's proved multiplicity fills every long line to exactly q+1. -/
theorem realized_long_line_card (D : IndexedDesign q X I) (e a : ℕ)
    (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hmult : ∀ i, D.Long e i →
      ((D.goodCliques e a).filter fun C => i ∈ C).card = D.lineDeficit i)
    (i : I) (hi : D.Long e i) :
    Nat.card {p : D.RealizedPoint e a // D.realizedInc e a p i} = q+1 := by
  rw [D.realized_line_card,hmult i hi]
  exact Nat.add_sub_of_le (hcap i)

/-- Distinct long labels meet at one old point, or at the unique actual good
clique containing that parallel pair. This proves the dual unique-join law. -/
theorem realized_long_unique_intersection (D : IndexedDesign q X I) (e a : ℕ)
    (hpair : ∀ i j, D.Long e i → D.Long e j → D.Parallel i j →
      ∃! C, C ∈ D.goodCliques e a ∧ i ∈ C ∧ j ∈ C)
    {i j : I} (hi : D.Long e i) (hj : D.Long e j) (hij : i ≠ j) :
    ∃! p : D.RealizedPoint e a, D.realizedInc e a p i ∧ D.realizedInc e a p j := by
  classical
  by_cases hmeet : ∃ x, D.inc x i ∧ D.inc x j
  · obtain ⟨x,hxi,hxj⟩ := hmeet
    refine ⟨.inl x,⟨hxi,hxj⟩,?_⟩
    intro p hp
    cases p with
    | inl y =>
      exact congrArg Sum.inl (D.intersection_unique hij hp.1 hxi hp.2 hxj)
    | inr C =>
      have hc := (D.mem_goodCliques e a C.val).mp C.property
      exact False.elim ((hc.1.1.2 i hp.1 j hp.2 hij).2 x ⟨hxi,hxj⟩)
  · have hp : D.Parallel i j := ⟨hij,fun x hx => hmeet ⟨x,hx⟩⟩
    obtain ⟨C,⟨hC,hiC,hjC⟩,hunique⟩ := hpair i j hi hj hp
    refine ⟨.inr ⟨C,hC⟩,⟨hiC,hjC⟩,?_⟩
    intro p hpi
    cases p with
    | inl x => exact False.elim (hp.2 x hpi)
    | inr E =>
      exact congrArg Sum.inr (Subtype.ext (hunique E.val ⟨E.property,hpi⟩))

/-- The actual long and short indexed-label sets partition every label. -/
theorem longLines_card_add_shortLines (D : IndexedDesign q X I) (e : ℕ) :
    (D.longLines e).card + (D.shortLines e).card = Fintype.card I := by
  classical
  have hu : D.longLines e ∪ D.shortLines e = Finset.univ := by
    ext i
    simp only [Finset.mem_union,D.mem_longLines,D.mem_shortLines,Finset.mem_univ]
    exact iff_true_intro (lt_or_ge (q-e) (D.lineDegree i))
  have hd : Disjoint (D.longLines e) (D.shortLines e) := by
    apply Finset.disjoint_left.mpr
    intro i hi hs
    exact (not_lt_of_ge ((D.mem_shortLines e i).mp hs)) ((D.mem_longLines e i).mp hi)
  simpa only [hu,Finset.card_univ] using (Finset.card_union_of_disjoint hd).symm

/-- At most q short indexed labels leave at least q²+1 actual long labels. -/
theorem longLines_card_lower (D : IndexedDesign q X I) (e : ℕ)
    (hI : Fintype.card I = q^2+q+1) (hshort : (D.shortLines e).card ≤ q) :
    q^2+1 ≤ (D.longLines e).card := by
  have hh := D.longLines_card_add_shortLines e
  omega

/-- The dual of the actual realized long-line structure, ready for source3.5.
Its point and line laws are proved above, rather than inserted as promises. -/
noncomputable def realizedDual (D : IndexedDesign q X I) (e a : ℕ)
    (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hmult : ∀ i, D.Long e i →
      ((D.goodCliques e a).filter fun C => i ∈ C).card = D.lineDeficit i)
    (hpair : ∀ i j, D.Long e i → D.Long e j → D.Parallel i j →
      ∃! C, C ∈ D.goodCliques e a ∧ i ∈ C ∧ j ∈ C) :
    IndexedDesign q ↥(D.longLines e) (D.RealizedPoint e a) where
  inc i p := D.realizedInc e a p i.val
  point_degree i := D.realized_long_line_card e a hcap hmult i.val
    ((D.mem_longLines e i.val).mp i.property)
  unique_join i j hij := D.realized_long_unique_intersection e a hpair
    ((D.mem_longLines e i.val).mp i.property)
    ((D.mem_longLines e j.val).mp j.property)
    (fun he => hij (Subtype.ext he))

@[simp] theorem realizedDual_old_inc (D : IndexedDesign q X I) (e a : ℕ)
    (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hmult : ∀ i, D.Long e i →
      ((D.goodCliques e a).filter fun C => i ∈ C).card = D.lineDeficit i)
    (hpair : ∀ i j, D.Long e i → D.Long e j → D.Parallel i j →
      ∃! C, C ∈ D.goodCliques e a ∧ i ∈ C ∧ j ∈ C)
    (i : ↥(D.longLines e)) (x : X) :
    (D.realizedDual e a hcap hmult hpair).inc i (.inl x) ↔ D.inc x i.val := Iff.rfl

#print axioms realizedDual
end Erdos60.Embedding.IndexedDesign

namespace Erdos60.Embedding.PlaneRealization
open scoped Classical
variable {P L I : Type*} [Membership P L]

/-- Dual incidence transported along the actual indexed-line bijection. -/
@[instance_reducible] def transportedMembership (R : I ≃ L) : Membership I P :=
  ⟨fun p i => p ∈ R i⟩

/-- Actual projective-plane laws after dualizing and returning the point carrier
through the proved bijection. No original indexed label is discarded. -/
@[instance_reducible] noncomputable def transportedPlane [Configuration.ProjectivePlane P L] (R : I ≃ L) :
    letI := transportedMembership R
    Configuration.ProjectivePlane I P := by
  letI := transportedMembership R
  exact {
    exists_point := by
      intro p
      obtain ⟨l,hl⟩ := Configuration.Nondegenerate.exists_line (L := L) p
      exact ⟨R.symm l,by simpa [Membership.mem,transportedMembership] using hl⟩
    exists_line := by
      intro i
      obtain ⟨p,hp⟩ := Configuration.Nondegenerate.exists_point (P := P) (R i)
      exact ⟨p,hp⟩
    eq_or_eq := by
      intro i j p r hip hjp hir hjr
      change p ∈ R i at hip
      change p ∈ R j at hjp
      change r ∈ R i at hir
      change r ∈ R j at hjr
      have hh := Configuration.Nondegenerate.eq_or_eq (P := P) (L := L) hip hir hjp hjr
      exact hh.elim Or.inr (fun he => Or.inl (R.injective he))
    mkPoint := fun hp => R.symm (Configuration.HasLines.mkLine (L := L) hp)
    mkPoint_ax := by
      intro p r hp
      simpa [Membership.mem,transportedMembership] using Configuration.HasLines.mkLine_ax (L := L) hp
    mkLine := fun hij => Configuration.HasPoints.mkPoint (P := P) (fun he => hij (R.injective he))
    mkLine_ax := by
      intro i j hij
      exact Configuration.HasPoints.mkPoint_ax (P := P) (fun he => hij (R.injective he))
    exists_config := by
      obtain ⟨p₁,p₂,p₃,l₁,l₂,l₃,h₁₂,h₁₃,h₂₁,h₂₂,h₂₃,h₃₁,h₃₂,h₃₃⟩ :=
        Configuration.ProjectivePlane.exists_config (P := P) (L := L)
      exact ⟨R.symm l₁,R.symm l₂,R.symm l₃,p₁,p₂,p₃,
        by simpa [Membership.mem,transportedMembership] using h₂₁,
        by simpa [Membership.mem,transportedMembership] using h₃₁,
        by simpa [Membership.mem,transportedMembership] using h₁₂,
        by simpa [Membership.mem,transportedMembership] using h₂₂,
        by simpa [Membership.mem,transportedMembership] using h₃₂,
        by simpa [Membership.mem,transportedMembership] using h₁₃,
        by simpa [Membership.mem,transportedMembership] using h₂₃,
        by simpa [Membership.mem,transportedMembership] using h₃₃⟩ }

/-- The transport preserves the literal plane order. -/
theorem transported_order [Fintype P] [Fintype L] [Fintype I]
    [Configuration.ProjectivePlane P L] (R : I ≃ L) :
    letI := transportedMembership R
    letI := transportedPlane R
    Configuration.ProjectivePlane.order I P = Configuration.ProjectivePlane.order P L := by
  let := transportedMembership R
  let := transportedPlane R
  obtain ⟨_,_,_,l,_,_,_⟩ := Configuration.ProjectivePlane.exists_config (P := P) (L := L)
  let i := R.symm l
  have hnew := Configuration.ProjectivePlane.lineCount_eq P i
  have hold := Configuration.ProjectivePlane.pointCount_eq P (R i)
  have he : Configuration.lineCount P i = Configuration.pointCount P (R i) := rfl
  omega

/-- Source3.8 and the actual cardinality bijection finish the original-carrier
transport. The input is an actual partial embedding in an actual plane. -/
theorem restore_and_transport {q : ℕ} {X : Type*} [Fintype X] [Fintype I]
    [Fintype P] [Fintype L] [Configuration.ProjectivePlane P L]
    (D : Erdos60.Embedding.IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hX : q^2-q+2 ≤ Fintype.card X)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (f : X ↪ P) (J : Finset I) (hJ : q^2+1 ≤ J.card)
    (r : I → L) (hinj : Set.InjOn r (J : Set I))
    (hrow : ∀ i ∈ J, ∀ x, D.inc x i ↔ f x ∈ r i) :
    ∃ M : Membership I P, letI := M
      ∃ plane : Configuration.ProjectivePlane I P, letI := plane
        Configuration.ProjectivePlane.order I P = q ∧
        ∀ x i, i ∈ f x ↔ D.inc x i := by
  obtain ⟨R,hinc,_⟩ := ShortLineRestoration.restore_short_lines_equiv D hq hI hX ho f J hJ r hinj hrow
  refine ⟨transportedMembership R,transportedPlane R,?_,?_⟩
  · exact (transported_order R).trans ho
  · intro x i
    exact (hinc i x).symm

/-- Partial embeddings may be specified only on the actual long-label
subtype. The extension to a total assignment does not identify any labels. -/
theorem restore_long_embedding {q : ℕ} {X : Type*} [Fintype X] [Fintype I]
    [Fintype P] [Fintype L] [Configuration.ProjectivePlane P L]
    (D : Erdos60.Embedding.IndexedDesign q X I) (e : ℕ) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hX : q^2-q+2 ≤ Fintype.card X)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (f : X ↪ P) (hJ : q^2+1 ≤ (D.longLines e).card)
    (r : ↥(D.longLines e) ↪ L)
    (hrow : ∀ i : ↥(D.longLines e), ∀ x, D.inc x i.val ↔ f x ∈ r i) :
    ∃ M : Membership I P, letI := M
      ∃ plane : Configuration.ProjectivePlane I P, letI := plane
        Configuration.ProjectivePlane.order I P = q ∧
        ∀ x i, i ∈ f x ↔ D.inc x i := by
  classical
  obtain ⟨_,_,_,l,_,_,_⟩ := Configuration.ProjectivePlane.exists_config (P := P) (L := L)
  let r' : I → L := fun i => if hi : i ∈ D.longLines e then r ⟨i,hi⟩ else l
  have hr (i : I) (hi : i ∈ D.longLines e) : r' i = r ⟨i,hi⟩ := by simp only [r',dif_pos hi]
  apply restore_and_transport D hq hI hX ho f (D.longLines e) hJ r'
  · intro i hi j hj he
    rw [hr i hi,hr j hj] at he
    exact congrArg Subtype.val (r.injective he)
  · intro i hi x
    rw [hr i hi]
    exact hrow ⟨i,hi⟩ x

/-- The literal original-point inclusion in the newly realized point carrier. -/
def oldPointEmbedding {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]
    (D : Erdos60.Embedding.IndexedDesign q X I) (e a : ℕ) : X ↪ D.RealizedPoint e a :=
  ⟨Sum.inl,Sum.inl_injective⟩

/-- Source6.10 fully constructs the plane after the actual source6.9
clique facts: realize new points, dualize, greedily complete, restore every
omitted indexed label, and transport back to the original point carrier. -/
theorem realized_completion_plane {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]
    (D : Erdos60.Embedding.IndexedDesign q X I) (e a s : ℕ) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1)
    (hX : Fintype.card X+s = q^2+q+1) (hXlo : q^2-q+2 ≤ Fintype.card X)
    (hcap : ∀ i, D.lineDegree i ≤ q+1)
    (hlong : q^2+1 ≤ (D.longLines e).card)
    (hcount : (D.goodCliques e a).card = s)
    (hmult : ∀ i, D.Long e i →
      ((D.goodCliques e a).filter fun C => i ∈ C).card = D.lineDeficit i)
    (hpair : ∀ i j, D.Long e i → D.Long e j → D.Parallel i j →
      ∃! C, C ∈ D.goodCliques e a ∧ i ∈ C ∧ j ∈ C) :
    ∃ M : Membership I (D.RealizedPoint e a), letI := M
      ∃ plane : Configuration.ProjectivePlane I (D.RealizedPoint e a), letI := plane
        Configuration.ProjectivePlane.order I (D.RealizedPoint e a) = q ∧
        ∀ x i, i ∈ (Sum.inl x : D.RealizedPoint e a) ↔ D.inc x i := by
  classical
  let A := D.realizedDual e a hcap hmult hpair
  have hA : Fintype.card (D.RealizedPoint e a) = q^2+q+1 :=
    D.realizedPoint_card e a s hX hcount
  have hlarge : q^2 ≤ Fintype.card ↥(D.longLines e) := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨Y,fY,E,f,hY,hinc,hplane⟩ := A.dense_plane_extension hq hA hlarge
  let := fY
  let := E.membership
  obtain ⟨pp,ho⟩ := hplane
  let := pp
  let R : D.RealizedPoint e a ≃ D.RealizedPoint e a := Equiv.refl _
  let : Membership (D.RealizedPoint e a) Y := transportedMembership R
  let : Configuration.ProjectivePlane (D.RealizedPoint e a) Y := transportedPlane R
  have hoDual : Configuration.ProjectivePlane.order (D.RealizedPoint e a) Y = q :=
    (transported_order R).trans ho
  apply restore_long_embedding D e hq hI hXlo hoDual (oldPointEmbedding D e a) hlong f
  intro i x
  exact (hinc i (Sum.inl x)).symm

/-- The actual no-degree-q branch of the frozen source route. All clique
counts and coverage are derived from the original indexed design and density;
no geometric or clique-existence supplier remains a theorem hypothesis. -/
theorem no_degree_q_plane {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]
    (D : Erdos60.Embedding.IndexedDesign q X I) (s : ℕ)
    (hq : 100000000 ≤ q) (hI : Fintype.card I = q^2+q+1)
    (hX : Fintype.card X+s = q^2+q+1) (hs : 500*s ≤ 501*q)
    (hbranch : q+2 ≤ s) (hnone : ∀ i, D.lineDegree i ≠ q) :
    ∃ M : Membership I (D.RealizedPoint (Parameters.cutoff q) (Parameters.allowance q s)), letI := M
      ∃ plane : Configuration.ProjectivePlane I
          (D.RealizedPoint (Parameters.cutoff q) (Parameters.allowance q s)), letI := plane
        Configuration.ProjectivePlane.order I
          (D.RealizedPoint (Parameters.cutoff q) (Parameters.allowance q s)) = q ∧
        ∀ x i, i ∈ (Sum.inl x : D.RealizedPoint (Parameters.cutoff q) (Parameters.allowance q s)) ↔
          D.inc x i := by
  classical
  let e := Parameters.cutoff q
  let a := Parameters.allowance q s
  have hq2 : 2 ≤ q := by omega
  have hqq : q ≤ q^2 := by nlinarith
  have h2q : 2*q ≤ q^2 := by nlinarith
  have hXlo : q^2-q+2 ≤ Fintype.card X := by omega
  have hbig : q+1 < Fintype.card X := by omega
  have hcap : ∀ i, D.lineDegree i ≤ q+1 := D.lineDegree_le (by omega) hI hbig
  obtain ⟨he,_,_,heqmul,_⟩ := Parameters.cutoff_bounds q hq
  have heq : e ≤ q := by change 1000*e ≤ q at heqmul; omega
  have he1 : 1 ≤ e := by change 1000 ≤ e at he; omega
  have hshort : (D.shortLines e).card ≤ q-e :=
    D.shortLines_cutoff_card_le s hq hs hbranch hI hX hcap hnone
  have hstrict : 2*q < 3*(q-1-a) := Parameters.triple_clique_strict q s hq hs hbranch
  have hm := Parameters.strong_clique_union_strict q s hq hs hbranch
  have hmZ : (q : ℤ)+1+((e-1 : ℕ) : ℤ)^2+(e : ℤ)^2 < 2*((q-a : ℕ) : ℤ) := by
    exact_mod_cast hm
  rw [Nat.cast_sub he1,Nat.cast_one] at hmZ
  have hinter : ∀ A B : Finset I, D.GoodClique e a A → D.GoodClique e a B →
      A ≠ B → (A ∩ B).card ≤ 1 := D.good_clique_intersection_le_one e a he1 hI hcap hmZ
  have hconstruct : ∀ L H : I, D.lineDeficit L=2 → D.Long e H → D.Parallel L H →
      ∃ C : Finset I, D.GoodClique e a C ∧ L ∈ C ∧ H ∈ C := by
    intro L H hdef hlong hpar
    exact D.good_clique_for_long_parallel s hq hs hI hX hbranch hcap hnone hdef hpar hlong
  obtain ⟨hcount,hmult,hpair⟩ := D.good_clique_complete_coverage e a s hq hs heq hshort
    hI hX hcap hnone hstrict hinter hconstruct
  have hlong := D.longLines_card_lower e hI (hshort.trans (Nat.sub_le q e))
  exact realized_completion_plane D e a s hq2 hI hX hXlo hcap hlong hcount hmult hpair

#print axioms no_degree_q_plane
#print axioms realized_completion_plane
#print axioms restore_and_transport
#print axioms restore_long_embedding
#print axioms transportedPlane
#print axioms transported_order
end Erdos60.Embedding.PlaneRealization
