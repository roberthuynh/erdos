import FactorMatching.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open SimpleGraph Function

namespace Erdos585.FactorMatching

universe u
variable {V : Type u} {q : ℕ} {G : SimpleGraph V}

def LocalSystem.liftAdj (L : LocalSystem q G) : Vertex q G → Vertex q G → Prop
  | .inl _, .inl _ => False
  | .inl s, .inr d => d.fst = s.1 ∧ d.snd = L.next s.1 s.2
  | .inr d, .inl s => d.fst = s.1 ∧ d.snd = L.next s.1 s.2
  | .inr d, .inr e => e = d.symm ∧ ¬∃ i, L.next d.fst i = d.snd

def LocalSystem.lift (L : LocalSystem q G) : SimpleGraph (Vertex q G) where
  Adj := L.liftAdj
  symm := ⟨by
    intro x y h
    cases x with
    | inl s => cases y <;> simp_all [liftAdj]
    | inr d =>
      cases y with
      | inl s => exact h
      | inr e =>
        obtain ⟨he, hn⟩ := h
        subst e
        refine ⟨by simp, ?_⟩
        change ¬∃ i, L.next d.snd i = d.fst
        intro h
        exact hn ((L.reciprocal d.snd d.fst).mp h)⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl s => exact h
    | inr d => exact d.symm_ne h.1.symm⟩

theorem LocalSystem.lift_le (L : LocalSystem q G) : L.lift ≤ gadget q G := by
  intro x y h
  cases x <;> cases y
  · exact h
  · exact h.1
  · exact h.1
  · exact h.1

def LocalSystem.slotDart (L : LocalSystem q G) (v : V) (i : Fin q) : G.Dart :=
  ⟨(v, L.next v i), L.original v i⟩

theorem LocalSystem.lift_unique (L : LocalSystem q G) (x : Vertex q G) :
    ∃! y, L.lift.Adj x y := by
  classical
  cases x with
  | inl s =>
    refine ⟨.inr (L.slotDart s.1 s.2), ⟨rfl, rfl⟩, ?_⟩
    intro y hy
    cases y with
    | inl t => exact False.elim hy
    | inr d =>
      apply congrArg Sum.inr
      apply SimpleGraph.Dart.ext
      exact Prod.ext hy.1 hy.2
  | inr d =>
    by_cases hn : ∃ i, L.next d.fst i = d.snd
    · obtain ⟨i, hi⟩ := hn
      refine ⟨.inl (d.fst, i), ⟨rfl, hi.symm⟩, ?_⟩
      intro y hy
      cases y with
      | inl s =>
        obtain ⟨v, j⟩ := s
        obtain ⟨hv, hj⟩ := hy
        dsimp at hv hj
        subst v
        have hij : j = i := L.injective d.fst (hj.symm.trans hi.symm)
        simp only [hij]
      | inr e => exact False.elim (hy.2 ⟨i, hi⟩)
    · refine ⟨.inr d.symm, ⟨rfl, hn⟩, ?_⟩
      intro y hy
      cases y with
      | inl s =>
        obtain ⟨v, i⟩ := s
        obtain ⟨hv, hi⟩ := hy
        dsimp at hv hi
        subst v
        exact False.elim (hn ⟨i, hi.symm⟩)
      | inr e => exact congrArg Sum.inr hy.1

theorem matching_of_localSystem (L : LocalSystem q G) :
    ∃ M : (gadget q G).Subgraph, M.IsPerfectMatching := by
  let M := (gadget q G).toSubgraph L.lift L.lift_le
  refine ⟨M, Subgraph.isPerfectMatching_iff.mpr ?_⟩
  exact L.lift_unique

theorem matching_of_factor [Fintype V] (h : SpanningFactor q G) :
    ∃ M : (gadget q G).Subgraph, M.IsPerfectMatching := by
  obtain ⟨L⟩ := (factor_iff_localSystem q G).mp h
  exact matching_of_localSystem L

end Erdos585.FactorMatching
