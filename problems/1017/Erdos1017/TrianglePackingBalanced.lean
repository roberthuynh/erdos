import Erdos1017.TrianglePackingTransport

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem packing_split_sum (x : ι → ℝ) (g : ι) :
    x g+(∑ i : {i : ι // i ≠ g}, x i)=∑ i,x i := by
  have h := (Equiv.optionSubtypeNe g).sum_comp x
  rw [Fintype.sum_option] at h
  simpa using h

theorem packing_balanced_at (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (g : ι)
    (hg : 2*x g=∑ i,x i) : Nonempty (LocalTrianglePacking x) := by
  let y : {i : ι // i ≠ g} → ℝ := fun i => x i
  let e := Equiv.optionSubtypeNe g
  have hs : (∑ i,y i)=x g := by
    have hh := packing_split_sum x g
    dsimp [y]
    linarith
  let P := balancedTrianglePacking y (fun i => hx i)
  have hw : (fun o : Option {i : ι // i ≠ g} => o.elim (∑ i,y i) y) = fun o => x (e o) := by
    funext o
    cases o with
    | none => exact hs
    | some i => rfl
  have P' : LocalTrianglePacking (fun o => x (e o)) := hw ▸ P
  have Q := LocalTrianglePacking.rename _ e.symm P'
  exact ⟨by simpa using Q⟩

/-- The branch with an already balanced ordinary tail removes the root from induction. -/
theorem packing_extend_balanced_tail (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ℝ) (hh : 0 ≤ h) (hmax : ∀ i,x i ≤ h)
    (hs : h < ∑ i,x i) (P : LocalTrianglePacking x) :
    Nonempty (LocalTrianglePacking (fun o : Option ι => o.elim h x)) := by
  let s := ∑ i,x i
  have hs0 : 0 < s := lt_of_le_of_lt hh hs
  have hQ : (∑ i,(x i)^2) ≤ h*s := by
    calc
      _ ≤ ∑ i,h*x i := Finset.sum_le_sum (fun i _ => by nlinarith [hx i,hmax i])
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hθ : 0 ≤ h/s := div_nonneg hh hs0.le
  have hκ : 0 ≤ 1-h/s := by apply sub_nonneg.mpr; exact (div_le_one hs0).mpr hs.le
  have he : h=(h/s)*s+(1-h/s)*0 := by field_simp; ring
  have hb : (1-h/s)*(0:ℝ)^2+(h/s)*(∑ i,(x i)^2) ≤ h^2 := by
    have hi := mul_le_mul_of_nonneg_left hQ hθ
    have heq : (h/s)*(h*s)=h^2 := by field_simp
    rw [heq] at hi
    simpa using hi
  exact ⟨trianglePackingStep x hx h 0 (h/s) (1-h/s) hθ hκ (by ring) he hb
    (P.addZeroRoot x)⟩

end Erdos1017
