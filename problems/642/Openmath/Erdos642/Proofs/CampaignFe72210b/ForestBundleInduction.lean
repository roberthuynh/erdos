import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestBundle

/-! Actual outer forest induction from an explicit single-forest root-avoidance supplier. -/
namespace Erdos642.CampaignFe72210b
variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) (A B : Finset V) (m b : ℕ)

/-- One actual indexed forest; existence is a separate quantitative obligation. -/
structure IndexedForest where
  root : Fin m → V
  leaves : Fin m → Finset V
  root_mem : ∀ j, root j ∈ A
  leaves_subset : ∀ j, leaves j ⊆ B
  leaves_card : ∀ j, (leaves j).card = b
  adjacent : ∀ j v, v ∈ leaves j → G.Adj (root j) v
  root_injective : Function.Injective root
  leaves_disjoint : ∀ j k, j ≠ k → Disjoint (leaves j) (leaves k)

namespace ForestBundle
variable {G A B m b} {n : ℕ}
variable (F : ForestBundle G A B n m b) (H : IndexedForest G A B m b)

def consRoot (i : Fin (n + 1) × Fin m) : V :=
  Fin.cases (H.root i.2) (fun f => F.root (f, i.2)) i.1

def consLeaves (i : Fin (n + 1) × Fin m) : Finset V :=
  Fin.cases (H.leaves i.2) (fun f => F.leaves (f, i.2)) i.1

 theorem oldRoot_mem (f : Fin n) (j : Fin m) : F.root (f, j) ∈ F.roots Finset.univ := by
  exact Finset.mem_image.mpr ⟨(f, j), Finset.mem_univ _, rfl⟩

/-- Add a genuinely new forest while retaining every previous root and forest. -/
def cons (havoid : ∀ j, H.root j ∉ F.roots Finset.univ) : ForestBundle G A B (n + 1) m b where
  root := F.consRoot H
  leaves := F.consLeaves H
  root_mem := by
    rintro ⟨f, j⟩
    cases f using Fin.cases with
    | zero => exact H.root_mem j
    | succ f => exact F.root_mem (f, j)
  leaves_subset := by
    rintro ⟨f, j⟩
    cases f using Fin.cases with
    | zero => exact H.leaves_subset j
    | succ f => exact F.leaves_subset (f, j)
  leaves_card := by
    rintro ⟨f, j⟩
    cases f using Fin.cases with
    | zero => exact H.leaves_card j
    | succ f => exact F.leaves_card (f, j)
  adjacent := by
    rintro ⟨f, j⟩ v hv
    cases f using Fin.cases with
    | zero => exact H.adjacent j v hv
    | succ f => exact F.adjacent (f, j) v hv
  root_injective := by
    rintro ⟨f, j⟩ ⟨g, k⟩ heq
    cases f using Fin.cases with
    | zero =>
      cases g using Fin.cases with
      | zero =>
        have hj : j = k := H.root_injective heq
        subst k
        rfl
      | succ g =>
        have hh : H.root j = F.root (g, k) := heq
        exact False.elim (havoid j (hh.symm ▸ F.oldRoot_mem g k))
    | succ f =>
      cases g using Fin.cases with
      | zero =>
        have hh : F.root (f, j) = H.root k := heq
        exact False.elim (havoid k (hh ▸ F.oldRoot_mem f j))
      | succ g =>
        have hij : (f, j) = (g, k) := F.root_injective heq
        cases hij
        rfl
  leaves_disjoint := by
    intro f j k hjk
    cases f using Fin.cases with
    | zero => exact H.leaves_disjoint j k hjk
    | succ f => exact F.leaves_disjoint f j k hjk
  shores_disjoint := F.shores_disjoint

end ForestBundle

/-- The actual q-forest bundle follows by finite induction; the one-forest supplier is explicit. -/
theorem exists_forestBundle_of_supplier (q : ℕ) (hAB : Disjoint A B)
    (hsupplier : ∀ i : ℕ, i < q → ∀ U : Finset V, U ⊆ A → U.card = i * m →
      ∃ H : IndexedForest G A B m b, ∀ j, H.root j ∉ U) :
    Nonempty (ForestBundle G A B q m b) := by
  have hind : ∀ i : ℕ, i ≤ q → Nonempty (ForestBundle G A B i m b) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨{ root := fun i => Fin.elim0 i.1
                leaves := fun i => Fin.elim0 i.1
                root_mem := fun i => Fin.elim0 i.1
                leaves_subset := fun i => Fin.elim0 i.1
                leaves_card := fun i => Fin.elim0 i.1
                adjacent := fun i => Fin.elim0 i.1
                root_injective := fun i => Fin.elim0 i.1
                leaves_disjoint := fun i => Fin.elim0 i
                shores_disjoint := hAB }⟩
    | succ i ih =>
      intro hi
      obtain ⟨F⟩ := ih (by omega)
      have hcard : (F.roots Finset.univ).card = i * m := by
        rw [F.roots_card]
        simp
      obtain ⟨H, havoid⟩ := hsupplier i (by omega) (F.roots Finset.univ)
        (F.roots_subset Finset.univ) hcard
      exact ⟨F.cons H havoid⟩
  exact hind q (le_refl q)

end Erdos642.CampaignFe72210b
