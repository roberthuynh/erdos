import Openmath.Erdos643Design.TransversalSymbols
import Openmath.Erdos643Design.TransversalProducts
import Openmath.Erdos643Design.TransversalField
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

/-! Six-column transversal rows on every positive alphabet size coprime to six. -/
set_option autoImplicit false

namespace Erdos643Design.Foundation
noncomputable section

/-- A supplied prime at least five supplies six distinct affine field columns. -/
theorem transversalRows_prime (p : ℕ) (hp : p.Prime) (hfive : 5 ≤ p) :
    Nonempty (TransversalRows (Fin 6) (Fin p)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ : Nonempty (Fin 6 ↪ Option (ZMod p)) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_fin, Fintype.card_option, ZMod.card]
    omega
  exact ⟨((FiniteFieldRows.transversal (F := ZMod p)).restrict e).symbolEquiv
    (Fintype.equivFinOfCardEq (ZMod.card p))⟩

/-- Every prime factor of a number coprime to six is at least five. -/
theorem prime_factor_ge_five {t p : ℕ} (hp : p.Prime) (hpt : p ∣ t)
    (hcop : Nat.Coprime t 6) : 5 ≤ p := by
  have hc : Nat.Coprime p 6 := hcop.of_dvd_left hpt
  have htwo : 2 ≤ p := hp.two_le
  by_contra hn
  have hsmall : p = 2 ∨ p = 3 ∨ p = 4 := by omega
  rcases hsmall with rfl | rfl | rfl
  · norm_num at hc
  · norm_num at hc
  · norm_num at hp

/-- Products of supplied six-column families give the product alphabet size. -/
theorem transversalRows_mul (a b : ℕ)
    (ha : Nonempty (TransversalRows (Fin 6) (Fin a)))
    (hb : Nonempty (TransversalRows (Fin 6) (Fin b))) :
    Nonempty (TransversalRows (Fin 6) (Fin (a*b))) := by
  obtain ⟨A⟩ := ha
  obtain ⟨B⟩ := hb
  exact ⟨(A.prod B).symbolEquiv (Fintype.equivFinOfCardEq (by simp))⟩

/-- Actual transversal rows on every positive symbol count coprime to six. -/
theorem transversalRows_coprime (t : ℕ) (ht : 0 < t) (hcop : Nat.Coprime t 6) :
    Nonempty (TransversalRows (Fin 6) (Fin t)) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases hone : t = 1
    · subst t
      exact ⟨TransversalRows.one⟩
    · obtain ⟨p,hp,hpt⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hone
      have hp1 : 1 < p := hp.one_lt
      have hprod : p * (t/p) = t := Nat.mul_div_cancel' hpt
      have hq0 : 0 < t/p := by
        have : t/p ≠ 0 := by intro hz; rw [hz, mul_zero] at hprod; omega
        exact Nat.pos_of_ne_zero this
      have hqlt : t/p < t := Nat.div_lt_self ht hp1
      have hqcop : Nat.Coprime (t/p) 6 := hcop.of_dvd_left (Nat.div_dvd_of_dvd hpt)
      have hq := ih (t/p) hqlt hq0 hqcop
      have hpRows := transversalRows_prime p hp (prime_factor_ge_five hp hpt hcop)
      simpa only [hprod] using transversalRows_mul p (t/p) hpRows hq

end
end Erdos643Design.Foundation
