import Mathlib.Tactic

/-! Coordinates from an actual partition into four-element groups and one distinguished point. -/
set_option autoImplicit false
namespace Erdos643Design.UniformPartitionCoordinates
open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] {p : V}

/-- The displayed finite groups partition every point except `p`. -/
structure Partition (p : V) where
  group : G → Finset V
  disjoint : Pairwise (fun i j => Disjoint (group i) (group j))
  card : ∀ i, (group i).card = 4
  cover : univ.biUnion group = univ.erase p

namespace Partition
variable (P : Partition (G := G) p)

/-- Each actual group is enumerated by exactly four indices. -/
noncomputable def groupEquiv (i : G) : P.group i ≃ Fin 4 :=
  Finset.equivFinOfCardEq (P.card i)

theorem mem_ne_point (i : G) {v : V} (hv : v ∈ P.group i) : v ≠ p := by
  have hm : v ∈ univ.biUnion P.group := mem_biUnion.mpr ⟨i,mem_univ _,hv⟩
  rw [P.cover] at hm
  exact (mem_erase.mp hm).1

/-- Decode the common point or an actual group element. -/
noncomputable def decode : Option (G × Fin 4) → V
  | none => p
  | some (i,a) => ((P.groupEquiv i).symm a).val

theorem decode_mem (i : G) (a : Fin 4) : P.decode (some (i,a)) ∈ P.group i :=
  ((P.groupEquiv i).symm a).property

theorem decode_ne_point (i : G) (a : Fin 4) : P.decode (some (i,a)) ≠ p :=
  P.mem_ne_point i (P.decode_mem i a)

theorem decode_bijective : Function.Bijective P.decode := by
  constructor
  · intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact False.elim (P.decode_ne_point y.1 y.2 h.symm)
    | some x =>
      cases y with
      | none => exact False.elim (P.decode_ne_point x.1 x.2 h)
      | some y =>
        rcases x with ⟨i,a⟩
        rcases y with ⟨j,b⟩
        have hij : i = j := by
          by_contra hij
          exact (Finset.disjoint_left.mp (P.disjoint hij)) (P.decode_mem i a)
            (h.symm ▸ P.decode_mem j b)
        subst j
        have he : (P.groupEquiv i).symm a = (P.groupEquiv i).symm b :=
          Subtype.ext h
        have hab : a = b := (P.groupEquiv i).symm.injective he
        exact congrArg (fun z => some (i,z)) hab
  · intro v
    by_cases hv : v = p
    · subst v
      exact ⟨none,rfl⟩
    · have hm : v ∈ univ.biUnion P.group := by
        rw [P.cover]
        exact mem_erase.mpr ⟨hv,mem_univ _⟩
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hm
      refine ⟨some (i,P.groupEquiv i ⟨v,hi⟩),?_⟩
      change ((P.groupEquiv i).symm (P.groupEquiv i ⟨v,hi⟩)).val = v
      rw [Equiv.symm_apply_apply]

/-- Actual coordinates constructed from the supplied finite partition. -/
noncomputable def coordinates : V ≃ Option (G × Fin 4) :=
  (Equiv.ofBijective P.decode P.decode_bijective).symm

@[simp] theorem inverse_none : P.coordinates.symm none = p := rfl

@[simp] theorem inverse_some (i : G) (a : Fin 4) :
    P.coordinates.symm (some (i,a)) = ((P.groupEquiv i).symm a).val := rfl

@[simp] theorem coordinates_point : P.coordinates p = none := by
  exact P.coordinates.eq_symm_apply.mp rfl

theorem inverse_mem_group (i : G) (a : Fin 4) :
    P.coordinates.symm (some (i,a)) ∈ P.group i := P.decode_mem i a

/-- Membership in an actual group is exactly the corresponding coordinate fiber. -/
theorem mem_group_iff (v : V) (i : G) :
    v ∈ P.group i ↔ ∃ a : Fin 4, P.coordinates v = some (i,a) := by
  constructor
  · intro hv
    refine ⟨P.groupEquiv i ⟨v,hv⟩,P.coordinates.eq_symm_apply.mp ?_⟩
    rw [P.inverse_some, Equiv.symm_apply_apply]
  · rintro ⟨a,ha⟩
    have hv := P.coordinates.eq_symm_apply.mpr ha
    rw [hv]
    exact P.inverse_mem_group i a

/-- Only the distinguished point receives the common-point coordinate. -/
theorem coordinates_eq_none_iff (v : V) : P.coordinates v = none ↔ v = p := by
  rw [← P.coordinates.eq_symm_apply, P.inverse_none]

end Partition
end Erdos643Design.UniformPartitionCoordinates
