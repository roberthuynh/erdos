import Openmath.Erdos643Design.TransversalFoundation

/-! Affine rows over an arbitrary finite field, with one column for each slope
and one column recording the first coefficient. -/
set_option autoImplicit false

namespace Erdos643Design.Foundation
namespace FiniteFieldRows

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The infinity column is `none`; finite columns are indexed by their slope. -/
def row (a b : F) : Option F → F
  | none => a
  | some s => s * a + b

omit [Fintype F] [DecidableEq F] in
@[simp] theorem row_none (a b : F) : row a b none = a := rfl
omit [Fintype F] [DecidableEq F] in
@[simp] theorem row_some (a b s : F) : row a b (some s) = s * a + b := rfl

/-- All coefficient pairs give a finite set of actual rows. -/
def rows : Finset (Option F → F) :=
  Finset.univ.image (fun p : F × F => row p.1 p.2)

theorem row_mem (a b : F) : row a b ∈ rows :=
  Finset.mem_image.mpr ⟨(a,b), Finset.mem_univ _, rfl⟩

omit [Fintype F] [DecidableEq F] in
/-- Two different columns determine the coefficients. -/
theorem coefficients_unique (i j : Option F) (hij : i ≠ j)
    (a b c d : F) (hi : row a b i = row c d i)
    (hj : row a b j = row c d j) : a = c ∧ b = d := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some t =>
      simp only [row_none] at hi
      simp only [row_some] at hj
      exact ⟨hi, by rw [hi] at hj; exact add_left_cancel hj⟩
  | some s =>
    cases j with
    | none =>
      simp only [row_none] at hj
      simp only [row_some] at hi
      exact ⟨hj, by rw [hj] at hi; exact add_left_cancel hi⟩
    | some t =>
      have hst : s ≠ t := fun h => hij (congrArg some h)
      simp only [row_some] at hi hj
      have hz : (s-t)*(a-c) = 0 := by linear_combination hi - hj
      have hac : a = c := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
        (sub_ne_zero.mpr hst))
      exact ⟨hac, by rw [hac] at hi; exact add_left_cancel hi⟩

omit [Fintype F] [DecidableEq F] in
/-- For every prescribed pair there is a row, obtained by solving two equations. -/
theorem pair_exists (i j : Option F) (hij : i ≠ j) (x y : F) :
    ∃ a b : F, row a b i = x ∧ row a b j = y := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some t =>
      refine ⟨x, y-t*x, rfl, ?_⟩
      simp only [row_some]
      ring
  | some s =>
    cases j with
    | none =>
      refine ⟨y, x-s*y, ?_, rfl⟩
      simp only [row_some]
      ring
    | some t =>
      have hst : s-t ≠ 0 := sub_ne_zero.mpr (fun h => hij (congrArg some h))
      refine ⟨(x-y)/(s-t), x-s*((x-y)/(s-t)), ?_, ?_⟩
      · simp only [row_some]
        ring
      · simp only [row_some]
        field_simp
        ring

/-- Actual finite-field affine construction of the pair-unique row interface. -/
def transversal : TransversalRows (Option F) F where
  rows := rows
  pair_unique := by
    intro i j hij x y
    obtain ⟨a,b,hi,hj⟩ := pair_exists i j hij x y
    refine ⟨row a b, ⟨row_mem a b, hi, hj⟩, ?_⟩
    intro r hr
    obtain ⟨⟨c,d⟩, _, rfl⟩ := Finset.mem_image.mp hr.1
    obtain ⟨hac,hbd⟩ := coefficients_unique i j hij c d a b
      (hr.2.1.trans hi.symm) (hr.2.2.trans hj.symm)
    rw [hac,hbd]

end FiniteFieldRows
end Erdos643Design.Foundation
