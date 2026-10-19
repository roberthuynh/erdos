import Openmath.Erdos643Design.TransversalFoundation

/-! Elementary constructions from supplied difference matrices.
The matrix property is a hypothesis on the supplied entries, not an existence axiom. -/
set_option autoImplicit false

namespace Erdos643Design.Foundation

/-- A difference matrix of index one: every difference of distinct columns
runs through the additive group exactly once. -/
structure DifferenceMatrix (I G : Type*) [AddCommGroup G] where
  matrix : G → I → G
  difference_bijective : ∀ i j : I, i ≠ j →
    Function.Bijective (fun r => matrix r i - matrix r j)

namespace DifferenceMatrix
variable {I G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Coordinatewise product of supplied difference matrices with the same columns. -/
def product (D : DifferenceMatrix I G) (E : DifferenceMatrix I H) :
    DifferenceMatrix I (G × H) where
  matrix := fun r i => (D.matrix r.1 i, E.matrix r.2 i)
  difference_bijective := by
    intro i j hij
    constructor
    · intro a b hab
      exact Prod.ext ((D.difference_bijective i j hij).1 (congrArg Prod.fst hab))
        ((E.difference_bijective i j hij).1 (congrArg Prod.snd hab))
    · intro z
      obtain ⟨a, ha⟩ := (D.difference_bijective i j hij).2 z.1
      obtain ⟨b, hb⟩ := (E.difference_bijective i j hij).2 z.2
      exact ⟨(a,b), Prod.ext ha hb⟩

/-- The extra column records the matrix row; other columns receive a common translation. -/
def row (D : DifferenceMatrix I G) (r s : G) : Option I → G
  | none => r
  | some i => D.matrix r i + s

@[simp] theorem row_none (D : DifferenceMatrix I G) (r s : G) :
    D.row r s none = r := rfl
@[simp] theorem row_some (D : DifferenceMatrix I G) (r s : G) (i : I) :
    D.row r s (some i) = D.matrix r i + s := rfl

/-- Distinct columns determine both the original row and its common translation. -/
theorem coefficients_unique (D : DifferenceMatrix I G) (i j : Option I) (hij : i ≠ j)
    (r s u v : G) (hi : D.row r s i = D.row u v i)
    (hj : D.row r s j = D.row u v j) : r = u ∧ s = v := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some b =>
      simp only [row_none] at hi
      simp only [row_some] at hj
      exact ⟨hi, by rw [hi] at hj; exact add_left_cancel hj⟩
  | some a =>
    cases j with
    | none =>
      simp only [row_none] at hj
      simp only [row_some] at hi
      exact ⟨hj, by rw [hj] at hi; exact add_left_cancel hi⟩
    | some b =>
      have hab : a ≠ b := fun h => hij (congrArg some h)
      simp only [row_some] at hi hj
      have hd : D.matrix r a - D.matrix r b = D.matrix u a - D.matrix u b := by
        calc
          D.matrix r a - D.matrix r b =
              (D.matrix r a + s) - (D.matrix r b + s) := by abel
          _ = (D.matrix u a + v) - (D.matrix u b + v) := by rw [hi,hj]
          _ = D.matrix u a - D.matrix u b := by abel
      have hru : r = u := (D.difference_bijective a b hab).1 hd
      exact ⟨hru, by rw [hru] at hi; exact add_left_cancel hi⟩

/-- A row attaining any prescribed entries in two distinct columns. -/
theorem pair_exists (D : DifferenceMatrix I G) (i j : Option I) (hij : i ≠ j)
    (x y : G) : ∃ r s : G, D.row r s i = x ∧ D.row r s j = y := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some b =>
      refine ⟨x, y - D.matrix x b, rfl, ?_⟩
      simp only [row_some]
      abel
  | some a =>
    cases j with
    | none =>
      refine ⟨y, x - D.matrix y a, ?_, rfl⟩
      simp only [row_some]
      abel
    | some b =>
      have hab : a ≠ b := fun h => hij (congrArg some h)
      obtain ⟨r, hr⟩ := (D.difference_bijective a b hab).2 (x-y)
      change D.matrix r a - D.matrix r b = x-y at hr
      refine ⟨r, x - D.matrix r a, ?_, ?_⟩
      · simp only [row_some]; abel
      · simp only [row_some]
        calc
          D.matrix r b + (x - D.matrix r a) =
              x - (D.matrix r a - D.matrix r b) := by abel
          _ = x - (x-y) := by rw [hr]
          _ = y := by abel

variable [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- The actual finite family of translated rows of a supplied matrix. -/
def rows (D : DifferenceMatrix I G) : Finset (Option I → G) :=
  Finset.univ.image (fun p : G × G => D.row p.1 p.2)

omit [DecidableEq I] in
theorem row_mem (D : DifferenceMatrix I G) (r s : G) : D.row r s ∈ D.rows :=
  Finset.mem_image.mpr ⟨(r,s), Finset.mem_univ _, rfl⟩

/-- A supplied difference matrix over a finite group gives transversal rows
on its column set with one extra column. -/
def transversal (D : DifferenceMatrix I G) : TransversalRows (Option I) G where
  rows := D.rows
  pair_unique := by
    intro i j hij x y
    obtain ⟨r,s,hi,hj⟩ := D.pair_exists i j hij x y
    refine ⟨D.row r s, ⟨D.row_mem r s, hi, hj⟩, ?_⟩
    intro t ht
    obtain ⟨⟨u,v⟩, _, rfl⟩ := Finset.mem_image.mp ht.1
    obtain ⟨hur,hvs⟩ := D.coefficients_unique i j hij u v r s
      (ht.2.1.trans hi.symm) (ht.2.2.trans hj.symm)
    rw [hur,hvs]

end DifferenceMatrix
end Erdos643Design.Foundation
