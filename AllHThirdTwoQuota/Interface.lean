import AllHThirdFragileFree.Numeric

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdTwoQuota
open QB4 B5 L34 H3Unequal
open AllHThirdFragileFree (Parameters offset constant)
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Original incidence data with NO extra row minimum or supplied fragile family. -/
structure Data (h q a j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Prop where
  parameters : Parameters h q a j
  disjoint : Disjoint A B
  card : #B = #A+j
  minA : ∀ v∈A, q ≤ dg G B v
  capA : ∀ v∈A, dg G B v ≤ 2*q-2
  minB : ∀ v∈B, q ≤ dg G A v
  capB : ∀ v∈B, dg G A v ≤ 2*q-2
  deficient : deficiency (2*(q:ℤ)-2) G B A =
    (h:ℤ)*q-a-((q:ℤ)-1)*j
  sparse : ∀ X⊆A, ∀ Y⊆B, h≤#X+#Y → #X+#Y<#A+#B →
    2*((h:ℤ)*q-a+1) ≤ potential (2*(q:ℤ)-2) G X Y

namespace Data
variable {h q a j : ℕ} {A B : Finset V} (d : Data h q a j G A B)

def fragileRows (_d : Data h q a j G A B) : Finset V :=
  A.filter (fun x => dg G B x≤q+2*h-5)

omit [DecidableEq V] in
lemma fragile_subset : d.fragileRows ⊆ A := filter_subset _ _

omit [DecidableEq V] in
lemma mem_fragile {x : V} : x∈d.fragileRows ↔ x∈A ∧ dg G B x≤q+2*h-5 := mem_filter

def neighbors (_d : Data h q a j G A B) (x : V) : Finset V :=
  B.filter (fun z => G.Adj x z)

omit [DecidableEq V] in
lemma neighbors_subset (x : V) : d.neighbors x ⊆ B := filter_subset _ _

omit [DecidableEq V] in
lemma mem_neighbors {x z : V} : z∈d.neighbors x ↔ z∈B ∧ G.Adj x z := mem_filter

omit [DecidableEq V] in
lemma neighbors_card (x : V) : #(d.neighbors x)=dg G B x := rfl

/-- Union of ALL actual fragile rows' full original neighborhoods. -/
def protectedCols : Finset V := d.fragileRows.biUnion d.neighbors

lemma protected_subset : d.protectedCols ⊆ B := by
  intro z hz
  obtain ⟨x,_,hxz⟩ := mem_biUnion.mp hz
  exact d.neighbors_subset x hxz

lemma mem_protected {z : V} : z∈d.protectedCols ↔
    ∃ x∈d.fragileRows, G.Adj x z ∧ z∈B := by
  simp only [protectedCols, mem_biUnion, mem_neighbors]
  tauto

def QuotaFeasible (O : Finset V) : Prop :=
  O⊆B ∧ #O=j ∧ ∀ x∈d.fragileRows, dg G O x≤dg G B x-q

def PairCondition : Prop := ∀ x∈d.fragileRows, ∀ y∈d.fragileRows, x≠y →
  j≤#(B.filter (fun z => ¬G.Adj x z ∧ ¬G.Adj y z))+(dg G B x-q)+(dg G B y-q)

end Data

def PetalEscapeClaim : Prop :=
  ∀ h q a j (A B K ban : Finset V), Data h q a j G A B →
    K⊆B → q-1≤#K → 2≤thetaJ q j G A B K →
    (∀ T⊆B, K⊆T → K≠T → thetaJ q j G A B T≤thetaJ q j G A B K-1) →
    ban⊆B\K → #ban≤9*h-23 →
    ∃ z∈B\K, z∉ban ∧ ∀ P⊆B\K, z∈P → 2≤extensionCost q j G A B K P

def TopEscapeClaim : Prop :=
  ∀ h q a j (A B K ban : Finset V), Data h q a j G A B →
    K⊆B → q-1≤#K → thetaJ q j G A B K=2*(j:ℤ)+1 →
    (∀ T⊆B, K⊆T → K≠T → thetaJ q j G A B T≤thetaJ q j G A B K-1) →
    ban⊆B\K → #ban≤8*h-20 →
    ∃ z∈B\K, z∉ban ∧ ∀ P⊆B\K, z∈P → 3≤extensionCost q j G A B K P

end Erdos585.AllHThirdTwoQuota
