import Openmath.Erdos643Design.HananiArithmetic
import Openmath.Erdos643Design.TruncatedTransversal
import Openmath.Erdos643Design.WeightedPairwiseConstruction
import Openmath.Erdos643Design.TransversalCoprime

/-! Exact general-existence assembly with finite ingredients left explicit.
No global existence theorem is assumed: the only inputs are the displayed finite seeds. -/
set_option autoImplicit false
namespace Erdos643Design.HananiAssembly
open Finset HananiArithmetic

def DesignExists (n : ℕ) : Prop :=
  ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 5

def ReplicationExists (r : ℕ) : Prop := DesignExists (4*r+1)

theorem step_from_transversal (r k t u : ℕ) (heq : r = k*t+u)
    (hlocal : LocalOrders r k t u) (hu : u ≤ t)
    (T : Foundation.TransversalRows (Fin (k+1)) (Fin t))
    (ih : ∀ j < r, Admissible j → ReplicationExists j) : ReplicationExists r := by
  have hk : 2 ≤ k := by have := hlocal.1.1; omega
  obtain ⟨P,hP,hsupport⟩ := TruncatedTransversal.exists_pbd_fin T hk hu
  have hloc : ∀ b ∈ P, DesignExists (4*b.card+1) := by
    intro b hb
    change ReplicationExists b.card
    exact local_order_paid (R := ReplicationExists) hlocal ih (hP.1 b hb) (hsupport b hb)
  have hex := WeightedPairwiseConstruction.exists_design_fin P hP hloc
  have hc : Fintype.card (Fin (k*t+u)) = r := (Fintype.card_fin _).trans heq.symm
  rw [hc] at hex
  exact hex

theorem ordinary_step (r : ℕ) (hr : Ordinary r)
    (ih : ∀ j < r, Admissible j → ReplicationExists j) : ReplicationExists r := by
  obtain ⟨T⟩ := Foundation.transversalRows_coprime (symbolCount r) hr.1
    (coprime_six_of_residue (symbolCount r) hr.2.1)
  exact step_from_transversal r 5 (symbolCount r) (truncatedCount r)
    hr.2.2.1 hr.2.2.2.2 hr.2.2.2.1 T ih

/-- The three exceptional transversal sizes are separate, finite construction obligations. -/
theorem special_step
    (h16 : Nonempty (Foundation.TransversalRows (Fin 6) (Fin 16)))
    (h11 : Nonempty (Foundation.TransversalRows (Fin 11) (Fin 11)))
    (h25 : Nonempty (Foundation.TransversalRows (Fin 11) (Fin 25)))
    (r : ℕ) (hr : Special r)
    (ih : ∀ j < r, Admissible j → ReplicationExists j) : ReplicationExists r := by
  obtain ⟨hcase,heq,hu,hlocal⟩ := hr
  have ht : Nonempty (Foundation.TransversalRows (Fin (specialK r+1)) (Fin (specialT r))) := by
    rcases hcase with ⟨hk,ht⟩ | ⟨hk,ht⟩ | ⟨hk,ht⟩
    · rw [hk,ht]; exact h16
    · rw [hk,ht]; exact h11
    · rw [hk,ht]; exact h25
  obtain ⟨T⟩ := ht
  exact step_from_transversal r (specialK r) (specialT r) (specialU r) heq hlocal hu T ih

/-- Full infinite recursion follows from exactly the finite base set and three TD witnesses. -/
theorem replication_exists_of_finite_ingredients
    (hbase : ∀ r ∈ baseOrders, ReplicationExists r)
    (h16 : Nonempty (Foundation.TransversalRows (Fin 6) (Fin 16)))
    (h11 : Nonempty (Foundation.TransversalRows (Fin 11) (Fin 11)))
    (h25 : Nonempty (Foundation.TransversalRows (Fin 11) (Fin 25))) :
    ∀ r, Admissible r → ReplicationExists r :=
  replication_induction ReplicationExists hbase ordinary_step (special_step h16 h11 h25)

/-- The exact target statement, conditional only on explicitly named finite ingredients. -/
theorem residue_designs_of_finite_ingredients
    (hOne : DesignExists 1) (hFive : DesignExists 5)
    (hbase : ∀ r ∈ baseOrders, ReplicationExists r)
    (h16 : Nonempty (Foundation.TransversalRows (Fin 6) (Fin 16)))
    (h11 : Nonempty (Foundation.TransversalRows (Fin 11) (Fin 11)))
    (h25 : Nonempty (Foundation.TransversalRows (Fin 11) (Fin 25))) :
    ∀ n : ℕ, (n % 20 = 1 ∨ n % 20 = 5) →
      ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 5 := by
  intro n hn
  rcases residue_to_replication n hn with h | h | ⟨r,hr,rfl⟩
  · subst n; exact hOne
  · subst n; exact hFive
  · exact replication_exists_of_finite_ingredients hbase h16 h11 h25 r hr

end Erdos643Design.HananiAssembly
