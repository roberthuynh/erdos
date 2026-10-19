import Openmath.Erdos643Design.TransversalField
import Openmath.Erdos643Design.TransversalProducts
import Openmath.Erdos643Design.TransversalSymbols
import Mathlib.FieldTheory.Finite.GaloisField

/-! Actual transversal rows from finite fields and products of alphabets. -/
set_option autoImplicit false
namespace Erdos643Design.CompositeSeeds
open Foundation
noncomputable section

/-- Restrict the slope/infinity rows and relabel the alphabet by its size. -/
def fieldRows {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (k q : ℕ) (hc : Fintype.card F = q) (hk : k ≤ q + 1) :
    TransversalRows (Fin k) (Fin q) :=
  let e : Fin k ↪ Option F := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [hc] using hk))
  ((Foundation.FiniteFieldRows.transversal (F := F)).restrict e).symbolEquiv
    (Fintype.equivFinOfCardEq hc)

/-- Finite-field existence provides rows without a finite multiplication table. -/
def galoisRows (p n k : ℕ) [Fact p.Prime] (hn : n ≠ 0) (hk : k ≤ p ^ n + 1) :
    TransversalRows (Fin k) (Fin (p ^ n)) := by
  let : Fintype (GaloisField p n) := Fintype.ofFinite _
  let : DecidableEq (GaloisField p n) := Classical.decEq _
  exact fieldRows (F := GaloisField p n) k (p ^ n)
    (by rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]) hk

/-- Multiply alphabet sizes using actual product rows. -/
def productRows {k a b : ℕ} (T : TransversalRows (Fin k) (Fin a))
    (U : TransversalRows (Fin k) (Fin b)) : TransversalRows (Fin k) (Fin (a * b)) :=
  (T.prod U).symbolEquiv (Fintype.equivFinOfCardEq (by simp))

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def td5_5 : TransversalRows (Fin 5) (Fin 5) := fieldRows (F := ZMod 5) 5 5 (ZMod.card 5) (by decide)
def td5_7 : TransversalRows (Fin 5) (Fin 7) := fieldRows (F := ZMod 7) 5 7 (ZMod.card 7) (by decide)
def td5_17 : TransversalRows (Fin 5) (Fin 17) := fieldRows (F := ZMod 17) 5 17 (ZMod.card 17) (by decide)
def td5_8 : TransversalRows (Fin 5) (Fin 8) := galoisRows 2 3 5 (by decide) (by decide)
def td5_16 : TransversalRows (Fin 5) (Fin 16) := galoisRows 2 4 5 (by decide) (by decide)
def td5_40 : TransversalRows (Fin 5) (Fin 40) := productRows td5_8 td5_5
def td5_56 : TransversalRows (Fin 5) (Fin 56) := productRows td5_8 td5_7
def td5_80 : TransversalRows (Fin 5) (Fin 80) := productRows td5_16 td5_5
def td5_85 : TransversalRows (Fin 5) (Fin 85) := productRows td5_5 td5_17
def td6_16 : TransversalRows (Fin 6) (Fin 16) := galoisRows 2 4 6 (by decide) (by decide)
def td11_11 : TransversalRows (Fin 11) (Fin 11) := fieldRows (F := ZMod 11) 11 11 (ZMod.card 11) (by decide)
def td11_25 : TransversalRows (Fin 11) (Fin 25) := galoisRows 5 2 11 (by decide) (by decide)

end
end Erdos643Design.CompositeSeeds
