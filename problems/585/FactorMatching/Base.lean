import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open SimpleGraph Function

namespace Erdos585.FactorMatching

universe u
variable {V : Type u}

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Vertex (q : ℕ) (G : SimpleGraph V) := (V × Fin q) ⊕ G.Dart

def gadgetAdj (q : ℕ) (G : SimpleGraph V) : Vertex q G → Vertex q G → Prop
  | .inl _, .inl _ => False
  | .inl s, .inr d => d.fst = s.1
  | .inr d, .inl s => d.fst = s.1
  | .inr d, .inr e => e = d.symm

def gadget (q : ℕ) (G : SimpleGraph V) : SimpleGraph (Vertex q G) where
  Adj := gadgetAdj q G
  symm := ⟨by
    intro x y h
    cases x with
    | inl x => cases y <;> simp_all [gadgetAdj]
    | inr d =>
      cases y with
      | inl s => exact h
      | inr e =>
        change e = d.symm at h
        change d = e.symm
        simp [h]⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl s => exact h
    | inr d => exact d.symm_ne h.symm⟩

@[simp] theorem gadget_slot_slot (q : ℕ) (G : SimpleGraph V) (s t : V × Fin q) :
    ¬ (gadget q G).Adj (.inl s) (.inl t) := id

@[simp] theorem gadget_slot_stub (q : ℕ) (G : SimpleGraph V) (s : V × Fin q) (d : G.Dart) :
    (gadget q G).Adj (.inl s) (.inr d) ↔ d.fst = s.1 := Iff.rfl

@[simp] theorem gadget_stub_slot (q : ℕ) (G : SimpleGraph V) (s : V × Fin q) (d : G.Dart) :
    (gadget q G).Adj (.inr d) (.inl s) ↔ d.fst = s.1 := Iff.rfl

@[simp] theorem gadget_stub_stub (q : ℕ) (G : SimpleGraph V) (d e : G.Dart) :
    (gadget q G).Adj (.inr d) (.inr e) ↔ e = d.symm := Iff.rfl

structure LocalSystem (q : ℕ) (G : SimpleGraph V) where
  next : V → Fin q → V
  original : ∀ v i, G.Adj v (next v i)
  injective : ∀ v, Injective (next v)
  reciprocal : ∀ v w, (∃ i, next v i = w) ↔ ∃ j, next w j = v

def LocalSystem.selected {q : ℕ} {G : SimpleGraph V} (L : LocalSystem q G) :
    SimpleGraph V where
  Adj v w := ∃ i, L.next v i = w
  symm := ⟨fun v w h => (L.reciprocal v w).mp h⟩
  loopless := ⟨by
    rintro v ⟨i, h⟩
    exact G.irrefl (h ▸ L.original v i)⟩

theorem LocalSystem.selected_le {q : ℕ} {G : SimpleGraph V} (L : LocalSystem q G) :
    L.selected ≤ G := by
  rintro v w ⟨i, rfl⟩
  exact L.original v i

theorem degree_fintype_irrel (K : SimpleGraph V) (v : V)
    (a b : Fintype (K.neighborSet v)) :
    @SimpleGraph.degree V K v a = @SimpleGraph.degree V K v b := by
  rw [← @SimpleGraph.card_neighborSet_eq_degree V K v a,
    ← @SimpleGraph.card_neighborSet_eq_degree V K v b]
  exact @Fintype.card_congr (K.neighborSet v) (K.neighborSet v) a b (Equiv.refl _)

variable [Fintype V]

def SpanningFactor (q : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ H : G.Subgraph, H.IsSpanning ∧ H.coe.IsRegularOfDegree q

theorem sameCarrier_iff (q : ℕ) (G : SimpleGraph V) :
    SpanningFactor q G ↔ ∃ K : SimpleGraph V, K ≤ G ∧ K.IsRegularOfDegree q := by
  classical
  constructor
  · rintro ⟨H, hs, hr⟩
    refine ⟨H.spanningCoe, H.spanningCoe_le, ?_⟩
    intro v
    rw [H.degree_spanningCoe, ← H.coe_degree ⟨v, hs v⟩]
    convert! hr ⟨v, hs v⟩ using 1
    exact degree_fintype_irrel H.coe ⟨v, hs v⟩ _ _
  · rintro ⟨K, hK, hr⟩
    refine ⟨G.toSubgraph K hK, SimpleGraph.toSubgraph.isSpanning K hK, ?_⟩
    intro v
    rw [Subgraph.coe_degree, ← Subgraph.degree_spanningCoe]
    exact hr v.val

theorem LocalSystem.regular {q : ℕ} {G : SimpleGraph V} (L : LocalSystem q G) :
    L.selected.IsRegularOfDegree q := by
  classical
  intro v
  let f : Fin q → L.selected.neighborSet v := fun i => ⟨L.next v i, ⟨i, rfl⟩⟩
  have hf : Bijective f := by
    constructor
    · intro i j h
      exact L.injective v (congrArg Subtype.val h)
    · rintro ⟨w, i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← Fintype.card_congr (Equiv.ofBijective f hf)]
  exact Fintype.card_fin q

theorem factor_iff_localSystem (q : ℕ) (G : SimpleGraph V) :
    SpanningFactor q G ↔ Nonempty (LocalSystem q G) := by
  classical
  rw [sameCarrier_iff]
  constructor
  · rintro ⟨K, hK, hr⟩
    let e (v : V) : K.neighborSet v ≃ Fin q :=
      Fintype.equivFinOfCardEq ((K.card_neighborSet_eq_degree v).trans (hr v))
    refine ⟨⟨fun v i => (e v).symm i, ?_, ?_, ?_⟩⟩
    · intro v i
      exact hK ((e v).symm i).property
    · intro v i j h
      exact (e v).symm.injective (Subtype.ext h)
    · intro v w
      constructor
      · rintro ⟨i, hi⟩
        have h : K.Adj w v := hi ▸ ((e v).symm i).property.symm
        exact ⟨e w ⟨v, h⟩, congrArg Subtype.val ((e w).symm_apply_apply ⟨v, h⟩)⟩
      · rintro ⟨i, hi⟩
        have h : K.Adj v w := hi ▸ ((e w).symm i).property.symm
        exact ⟨e v ⟨w, h⟩, congrArg Subtype.val ((e v).symm_apply_apply ⟨w, h⟩)⟩
  · rintro ⟨L⟩
    exact ⟨L.selected, L.selected_le, L.regular⟩

end Erdos585.FactorMatching
