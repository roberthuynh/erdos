import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Logic.Equiv.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open SimpleGraph Set Function
namespace Erdos585.GadgetNormalization
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) (z : V)

def punctured : SimpleGraph {v : V // v ≠ z} := G.induce {v | v ≠ z}

def punctureInclusion : punctured G z →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

/-- Actual remaining-neighbor components, with no numerical supplier. -/
def pointTouch : Set (punctured G z).ConnectedComponent :=
  {c | ∃ v : {v : V // v ≠ z}, G.Adj z v ∧
    (punctured G z).connectedComponentMk v = c}

lemma reachable_closed {P : V → Prop}
    (hP : ∀ {a b : V}, G.Adj a b → P a → P b)
    {a b : V} (h : G.Reachable a b) (ha : P a) : P b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons h p ih => exact ih (hP h ha)

lemma untouched_image_closed (c : (punctured G z).ConnectedComponent)
    (hc : c ∉ pointTouch G z) {a b : V}
    (ha : a ∈ Subtype.val '' c.supp) (hab : G.Adj a b) :
    b ∈ Subtype.val '' c.supp := by
  obtain ⟨v, hv, rfl⟩ := ha
  have hb : b ≠ z := by
    intro hb
    subst b
    exact hc ⟨v, hab.symm, hv⟩
  refine ⟨⟨b,hb⟩, ?_, rfl⟩
  exact (c.mem_supp_congr_adj (show (punctured G z).Adj v ⟨b,hb⟩ from hab)).mp hv

/-- Untouched components have identical physical support after restoration. -/
lemma untouched_image_supp (c : (punctured G z).ConnectedComponent)
    (hc : c ∉ pointTouch G z) :
    Subtype.val '' c.supp = (c.map (punctureInclusion G z)).supp := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change G.connectedComponentMk v.val = c.map (punctureInclusion G z)
    rw [← hv, ConnectedComponent.map_mk]
    rfl
  · intro hw
    obtain ⟨v,hv⟩ := c.nonempty_supp
    have hv' : v.val ∈ (c.map (punctureInclusion G z)).supp := by
      change G.connectedComponentMk v.val = c.map (punctureInclusion G z)
      rw [← hv, ConnectedComponent.map_mk]
      rfl
    have hr : G.Reachable v.val w :=
      ConnectedComponent.exact (hv'.trans hw.symm)
    exact reachable_closed G (fun hab ha => untouched_image_closed G z c hc ha hab) hr ⟨v,hv,rfl⟩

lemma untouched_support_ncard (c : (punctured G z).ConnectedComponent)
    (hc : c ∉ pointTouch G z) :
    (c.map (punctureInclusion G z)).supp.ncard = c.supp.ncard := by
  rw [← untouched_image_supp G z c hc]
  exact Set.ncard_image_of_injective _ Subtype.val_injective

lemma untouched_map_inj :
    Set.InjOn (fun c => c.map (punctureInclusion G z))
      (pointTouch G z)ᶜ := by
  intro c hc d hd h
  obtain ⟨v,hv⟩ := c.nonempty_supp
  have hv' : v.val ∈ (c.map (punctureInclusion G z)).supp := by
    rw [← untouched_image_supp G z c hc]
    exact ⟨v,hv,rfl⟩
  change c.map (punctureInclusion G z) = d.map (punctureInclusion G z) at h
  rw [h, ← untouched_image_supp G z d hd] at hv'
  obtain ⟨w,hw,he⟩ := hv'
  have hwe : w = v := Subtype.ext he
  subst w
  exact ConnectedComponent.eq_of_common_vertex hv hw

/-- Counting only the physically untouched old odd components. -/
theorem point_odd_bound_two (ht : (pointTouch G z).ncard ≤ 2) :
    (punctured G z).oddComponents.ncard ≤ G.oddComponents.ncard + 2 := by
  have hinj : Set.InjOn (fun c => c.map (punctureInclusion G z))
      ((punctured G z).oddComponents \ pointTouch G z) :=
    (untouched_map_inj G z).mono (fun _ h => h.2)
  have hcard : ((punctured G z).oddComponents \ pointTouch G z).ncard ≤
      G.oddComponents.ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun c => c.map (punctureInclusion G z))
    · intro c hc
      change Odd (c.map (punctureInclusion G z)).supp.ncard
      rw [untouched_support_ncard G z c hc.2]
      exact hc.1
    · exact hinj
  have hsplit := Set.ncard_le_ncard_sdiff_add_ncard
    (punctured G z).oddComponents (pointTouch G z)
  omega

/-- Actual one-vertex order parity removes the possible loss of two. -/
theorem point_odd_bound (ht : (pointTouch G z).ncard ≤ 2) :
    (punctured G z).oddComponents.ncard ≤ G.oddComponents.ncard + 1 := by
  classical
  have h := point_odd_bound_two G z ht
  have hc : Nat.card V = Nat.card {v : V // v ≠ z} + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe z)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  have hp := odd_ncard_oddComponents (punctured G z)
  have hq := odd_ncard_oddComponents G
  simp only [Nat.odd_iff] at hp hq
  have hx := Nat.mod_lt (Nat.card V) (by omega : 0 < 2)
  have hy := Nat.mod_lt (Nat.card {v : V // v ≠ z}) (by omega : 0 < 2)
  omega

end Erdos585.GadgetNormalization
