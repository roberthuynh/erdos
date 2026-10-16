/-
Copyright 2026 Robert Huynh.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil.Linters.CopyrightLinter
import FormalConjecturesUtil.Linters.NamespaceLinter
import FormalConjecturesUtil.Linters.StubLinter
import AllHTopTwo.Selection
import AllHTopTwo.PetalEscape

/-! R280: literal R265 original uniform fragile-quota interface. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
universe u

open Classical in
def constant (h q ξ : ℕ) : ℕ := h * q - ξ

open Classical in
structure Parameters (h q j ξ : ℕ) : Prop where
  height : 3 ≤ h
  large : 1024 * (h + 1) ^ 2 ≤ q
  positive : 1 ≤ j
  surplus : j ≤ h - 1
  lower : h ^ 2 + 3 * h + 8 ≤ ξ
  upper : ξ ≤ h ^ 2 + 5 * h + 8

open Classical in
/-- The complete original graph contract, with the proper floor starting at h. -/
structure Host (h q j ξ : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  parameters : Parameters h q j ξ
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  edges : G.edgeSet.ncard + constant h q ξ = (q - 1) * Fintype.card V
  proper : ∀ X : Finset V, h ≤ #X → #X < Fintype.card V →
    (constant h q ξ : ℤ) ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

open Classical in
/-- Paired original incidence fields, derived from Host rather than supplied at the endpoint. -/
structure Data (h q j ξ : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Prop where
  parameters : Parameters h q j ξ
  disjoint : Disjoint A B
  card : #B = #A + j
  minA : ∀ a ∈ A, q ≤ dg G B a
  capA : ∀ a ∈ A, dg G B a ≤ 2 * q - 2
  minB : ∀ b ∈ B, q ≤ dg G A b
  capB : ∀ b ∈ B, dg G A b ≤ 2 * q - 2
  deficient : deficiency (2 * (q : ℤ) - 2) G B A =
    (h : ℤ) * q - ξ - ((q : ℤ) - 1) * j
  sparse : ∀ X ⊆ A, ∀ Y ⊆ B, h ≤ #X + #Y → #X + #Y < #A + #B →
    2 * ((h : ℤ) * q - ξ) ≤ potential (2 * (q : ℤ) - 2) G X Y

namespace Data
variable {h q j ξ : ℕ} {A B : Finset V} (d : Data h q j ξ G A B)

open Classical in
def fragileRows (_d : Data h q j ξ G A B) : Finset V :=
  A.filter (fun x => dg G B x≤q+2*h-5)

open Classical in
omit [DecidableEq V] in
lemma fragile_subset : d.fragileRows ⊆ A := filter_subset _ _

open Classical in
omit [DecidableEq V] in
lemma mem_fragile {x : V} : x∈d.fragileRows ↔ x∈A ∧ dg G B x≤q+2*h-5 := mem_filter

open Classical in
def neighbors (_d : Data h q j ξ G A B) (x : V) : Finset V :=
  B.filter (fun z => G.Adj x z)

open Classical in
omit [DecidableEq V] in
lemma neighbors_subset (x : V) : d.neighbors x ⊆ B := filter_subset _ _

open Classical in
omit [DecidableEq V] in
lemma mem_neighbors {x z : V} : z∈d.neighbors x ↔ z∈B ∧ G.Adj x z := mem_filter

open Classical in
omit [DecidableEq V] in
lemma neighbors_card (x : V) : #(d.neighbors x)=dg G B x := rfl

open Classical in
/-- Union of ALL actual fragile rows' full original neighborhoods. -/
def protectedCols : Finset V := d.fragileRows.biUnion d.neighbors

open Classical in
lemma protected_subset : d.protectedCols ⊆ B := by
  intro z hz
  obtain ⟨x,_,hxz⟩ := mem_biUnion.mp hz
  exact d.neighbors_subset x hxz

open Classical in
lemma mem_protected {z : V} : z∈d.protectedCols ↔
    ∃ x∈d.fragileRows, G.Adj x z ∧ z∈B := by
  simp only [protectedCols, mem_biUnion, mem_neighbors]
  tauto

open Classical in
def QuotaFeasible (O : Finset V) : Prop :=
  O⊆B ∧ #O=j ∧ ∀ x∈d.fragileRows, dg G O x≤dg G B x-q

end Data

open Classical in
/-- Exact local cost-one escape required from original paired incidence.
The full Data premise is discharged internally from Host. Strict maximum height
is a local selection made inside the proof, not an endpoint premise. -/
def PetalEscapeClaim : Prop :=
  ∀ (h q j ξ : ℕ) (A B K ban : Finset V), Data h q j ξ G A B →
    K ⊆ B → q - 1 ≤ #K → 2 ≤ thetaJ q j G A B K →
    (∀ T ⊆ B, K ⊆ T → K ≠ T → thetaJ q j G A B T ≤ thetaJ q j G A B K - 1) →
    ban ⊆ B \ K → #ban ≤ 4 * h ^ 2 →
    ∃ z ∈ B \ K, z ∉ ban ∧
      ∀ P ⊆ B \ K, z ∈ P → 2 ≤ extensionCost q j G A B K P

end Erdos585.AllHQuotaNonstrict
