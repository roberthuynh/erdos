import Mathlib.Tactic

/-! Indexed incidence designs from Metsch, Linear Spaces with Few Lines (1991),
page 2. Line labels remain a separate finite type: empty lines and repeated
singleton supports are permitted. No embedding or completion is a structure field. -/
namespace Erdos60.Embedding
open Finset
open scoped Classical

structure IndexedDesign (q : ℕ) (X I : Type*) [Fintype X] [Fintype I] where
  inc : X → I → Prop
  point_degree : ∀ x, Nat.card {i : I // inc x i} = q+1
  unique_join : ∀ x y, x ≠ y → ∃! i, inc x i ∧ inc y i

namespace IndexedDesign
variable {q : ℕ} {X I : Type*} [Fintype X] [Fintype I]

noncomputable def pointLines (D : IndexedDesign q X I) (x : X) : Finset I :=
  Finset.univ.filter (D.inc x)

noncomputable def linePoints (D : IndexedDesign q X I) (i : I) : Finset X :=
  Finset.univ.filter (fun x => D.inc x i)

noncomputable def lineDegree (D : IndexedDesign q X I) (i : I) : ℕ := (D.linePoints i).card
noncomputable def lineDeficit (D : IndexedDesign q X I) (i : I) : ℕ := q+1-D.lineDegree i

def Parallel (D : IndexedDesign q X I) (i j : I) : Prop :=
  i ≠ j ∧ ∀ x, ¬(D.inc x i ∧ D.inc x j)

/-- Install explicitly and locally when invoking mathlib configuration APIs. -/
@[instance_reducible] def membership (D : IndexedDesign q X I) : Membership X I := ⟨fun i x => D.inc x i⟩

@[simp] theorem mem_pointLines (D : IndexedDesign q X I) (x : X) (i : I) :
    i ∈ D.pointLines x ↔ D.inc x i := by simp [pointLines]
@[simp] theorem mem_linePoints (D : IndexedDesign q X I) (i : I) (x : X) :
    x ∈ D.linePoints i ↔ D.inc x i := by simp [linePoints]
@[simp] theorem card_pointLines (D : IndexedDesign q X I) (x : X) :
    (D.pointLines x).card = q+1 := by
  simpa [Nat.card_eq_fintype_card,Fintype.card_subtype,pointLines] using D.point_degree x

theorem join_unique (D : IndexedDesign q X I) {x y : X} {i j : I} (hxy : x ≠ y)
    (hxi : D.inc x i) (hyi : D.inc y i) (hxj : D.inc x j) (hyj : D.inc y j) : i=j := by
  obtain ⟨k,hk,hu⟩ := D.unique_join x y hxy
  exact (hu i ⟨hxi,hyi⟩).trans (hu j ⟨hxj,hyj⟩).symm

theorem intersection_unique (D : IndexedDesign q X I) {x y : X} {i j : I}
    (hij : i ≠ j) (hxi : D.inc x i) (hyi : D.inc y i) (hxj : D.inc x j) (hyj : D.inc y j) : x=y := by
  by_contra hxy
  exact hij (D.join_unique hxy hxi hyi hxj hyj)

theorem parallel_symm (D : IndexedDesign q X I) {i j : I} : D.Parallel i j → D.Parallel j i := by
  rintro ⟨hij,h⟩
  exact ⟨hij.symm,fun x hx => h x hx.symm⟩

#print axioms intersection_unique
end IndexedDesign
end Erdos60.Embedding
