import Mathlib.Tactic

/-! Arithmetic coverage of the replication-order recursion.
The mathematical construction and finite seeds are separate obligations. -/
set_option autoImplicit false
namespace Erdos643Design.HananiArithmetic

def Admissible (r : ℕ) : Prop := 5 ≤ r ∧ (r % 5 = 0 ∨ r % 5 = 1)

def baseOrders : Finset ℕ :=
  {5,6,10,11,15,16,20,21,31,35,36,40,41,45,46,50,51,70,71,75,76,100,101,105,106,151}

def specialOrders : Finset ℕ :=
  {80,81,85,86,90,91,95,96,110,111,115,116,120,121,250,251,255,256,260,261,265,266,270,271}

/-- The ordinary six-column branch uses this symbol count. -/
def symbolCount (r : ℕ) : ℕ :=
  let s := r / 150
  let x := r % 150
  if x ≤ 1 then 30*s-5
  else if x ≤ 21 then 30*s+1
  else if x ≤ 51 then 30*s+5
  else if x ≤ 121 then 30*s+11
  else 30*s+25

def truncatedCount (r : ℕ) : ℕ := r - 5 * symbolCount r

/-- All block sizes which survive truncation must be smaller admissible orders. -/
def LocalOrders (r k t u : ℕ) : Prop :=
  Admissible k ∧ Admissible (k+1) ∧ Admissible t ∧
  k < r ∧ k+1 < r ∧ t < r ∧
  (2 ≤ u → Admissible u ∧ u < r)

instance (r : ℕ) : Decidable (Admissible r) := by unfold Admissible; infer_instance
instance (r k t u : ℕ) : Decidable (LocalOrders r k t u) := by
  unfold LocalOrders; infer_instance

def Ordinary (r : ℕ) : Prop :=
  0 < symbolCount r ∧ (symbolCount r % 6 = 1 ∨ symbolCount r % 6 = 5) ∧
  r = 5 * symbolCount r + truncatedCount r ∧ truncatedCount r ≤ symbolCount r ∧
  LocalOrders r 5 (symbolCount r) (truncatedCount r)

instance (r : ℕ) : Decidable (Ordinary r) := by unfold Ordinary; infer_instance

theorem residue_admissible (r : ℕ) (h : Admissible r) :
    r % 150 % 5 = 0 ∨ r % 150 % 5 = 1 := by
  simpa only [Nat.mod_mod_of_dvd r (by decide : 5 ∣ 150)] using h.2

theorem large_ordinary_parameters (r : ℕ) (hr : Admissible r) (hlarge : 300 ≤ r) :
    0 < symbolCount r ∧ (symbolCount r % 6 = 1 ∨ symbolCount r % 6 = 5) ∧
    r = 5 * symbolCount r + truncatedCount r ∧ truncatedCount r ≤ symbolCount r ∧
    LocalOrders r 5 (symbolCount r) (truncatedCount r) := by
  have hx : r % 150 < 150 := Nat.mod_lt r (by omega)
  have hdecomp := Nat.mod_add_div r 150
  have hs : 2 ≤ r / 150 := by omega
  have hres := residue_admissible r hr
  unfold truncatedCount symbolCount LocalOrders Admissible
  dsimp only
  split_ifs <;> omega

/-- The complete finite prefix is checked by ordinary kernel reduction. -/
theorem small_ordinary_certificate :
    ∀ r : Fin 300, Admissible r.val → r.val ∉ baseOrders →
      r.val ∉ specialOrders → Ordinary r.val := by
  intro r
  fin_cases r <;> decide

theorem ordinary_parameters (r : ℕ) (hr : Admissible r)
    (hb : r ∉ baseOrders) (hs : r ∉ specialOrders) : Ordinary r := by
  by_cases hlarge : 300 ≤ r
  · exact large_ordinary_parameters r hr hlarge
  · exact small_ordinary_certificate ⟨r,by omega⟩ hr hb hs

def specialK (r : ℕ) : ℕ := if r ≤ 96 then 5 else 10
def specialT (r : ℕ) : ℕ := if r ≤ 96 then 16 else if r ≤ 121 then 11 else 25
def specialU (r : ℕ) : ℕ := r - specialK r * specialT r

def Special (r : ℕ) : Prop :=
  ((specialK r = 5 ∧ specialT r = 16) ∨
   (specialK r = 10 ∧ specialT r = 11) ∨
   (specialK r = 10 ∧ specialT r = 25)) ∧
  r = specialK r * specialT r + specialU r ∧
  specialU r ≤ specialT r ∧
  LocalOrders r (specialK r) (specialT r) (specialU r)

instance (r : ℕ) : Decidable (Special r) := by unfold Special; infer_instance

theorem special_certificate : ∀ r ∈ specialOrders, Special r := by
  decide

/-- Every admissible replication order is either a finite base or a valid decreasing step. -/
theorem recursion_cases (r : ℕ) (hr : Admissible r) :
    r ∈ baseOrders ∨ Special r ∨ Ordinary r := by
  by_cases hb : r ∈ baseOrders
  · exact Or.inl hb
  · by_cases hs : r ∈ specialOrders
    · exact Or.inr (Or.inl (special_certificate r hs))
    · exact Or.inr (Or.inr (ordinary_parameters r hr hb hs))

/-- Every actual nontrivial block in the truncated PBD can use the strong induction hypothesis. -/
theorem local_order_paid {R : ℕ → Prop} {r k t u a : ℕ}
    (hlocal : LocalOrders r k t u)
    (ih : ∀ j < r, Admissible j → R j)
    (ha : 2 ≤ a) (hsupport : a = k ∨ a = k+1 ∨ a = t ∨ a = u) : R a := by
  rcases hlocal with ⟨hk,hk1,ht,hkr,hk1r,htr,hu⟩
  rcases hsupport with h | h | h | h
  · subst a; exact ih k hkr hk
  · subst a; exact ih (k+1) hk1r hk1
  · subst a; exact ih t htr ht
  · subst a; exact ih u (hu ha).2 (hu ha).1

/-- Arithmetic-only strong-induction interface; construction obligations remain explicit. -/
theorem replication_induction (R : ℕ → Prop)
    (hbase : ∀ r ∈ baseOrders, R r)
    (hordinary : ∀ r, Ordinary r → (∀ j < r, Admissible j → R j) → R r)
    (hspecial : ∀ r, Special r → (∀ j < r, Admissible j → R j) → R r) :
    ∀ r, Admissible r → R r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    rcases recursion_cases r hr with hb | hs | ho
    · exact hbase r hb
    · exact hspecial r hs ih
    · exact hordinary r ho ih

/-- Translate the exact public residue classes into the replication parameter, including bases. -/
theorem residue_to_replication (n : ℕ) (hn : n % 20 = 1 ∨ n % 20 = 5) :
    n = 1 ∨ n = 5 ∨ ∃ r, Admissible r ∧ n = 4*r+1 := by
  by_cases hsmall : n < 21
  · omega
  · refine Or.inr (Or.inr ⟨(n-1)/4, ?_, ?_⟩)
    · unfold Admissible
      omega
    · omega

theorem coprime_six_of_residue (t : ℕ) (ht : t % 6 = 1 ∨ t % 6 = 5) :
    Nat.Coprime t 6 := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
  rcases ht with h | h <;> rw [h] <;> decide

end Erdos643Design.HananiArithmetic
