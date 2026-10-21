import Erdos1017.TrianglePackingBalanced

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the ordinary tail is unbalanced, one explicit balanced packing suffices. -/
theorem packing_extend_heavy_tail (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ℝ) (hmax : ∀ i,x i ≤ h) (hs : h < ∑ i,x i)
    (g : ι) (hg : (∑ i,x i)/2 < x g) :
    Nonempty (LocalTrianglePacking (fun o : Option ι => o.elim h x)) := by
  let s := ∑ i,x i
  let v := s-x g
  let κ := (s-h)/(2*v)
  have hv : 0 < v := by dsimp [v,s]; linarith [hmax g]
  have hg0 := hx g
  have hvg : v < x g := by dsimp [v,s]; linarith
  have hk0 : 0 ≤ κ := div_nonneg (sub_nonneg.mpr hs.le) (by positivity)
  have hkh : κ ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ (show 0 < 2*v by positivity)).mpr
    dsimp [v]
    linarith [hmax g]
  have hθ : 0 ≤ 1-κ := by linarith
  have hkv : κ*(2*v)=s-h := by dsimp [κ]; field_simp
  have hsrel : s=x g+v := by dsimp [v]; ring
  have hroot : h=(1-κ)*s+κ*(x g-v) := by nlinarith
  have hQ : (∑ i,(x i)^2) ≤ (x g)^2+v^2 := by
    have he := elementarySum_two_identity (Finset.univ.erase g) x
    have hen := elementarySum_nonneg (Finset.univ.erase g) x (fun i _ => hx i) 2
    have hsum := Finset.sum_erase_add Finset.univ x (Finset.mem_univ g)
    have hsq := Finset.sum_erase_add Finset.univ (fun i => (x i)^2) (Finset.mem_univ g)
    have hsum' : (∑ i ∈ Finset.univ.erase g,x i)=v := by dsimp [v,s]; linarith
    rw [hsum'] at he
    nlinarith
  have hbound : κ*(x g-v)^2+(1-κ)*(∑ i,(x i)^2) ≤ h^2 := by
    have hc := mul_le_mul_of_nonneg_left hQ hθ
    have hid : κ*(x g-v)^2+(1-κ)*((x g)^2+v^2)=x g*h-x g*v+v^2 := by
      nlinarith [congrArg (fun z : ℝ => x g*z) hkv,
        congrArg (fun z : ℝ => x g*z) hsrel]
    have hfac : 0 ≤ (h-v)*(h-x g+v) := mul_nonneg (by linarith [hmax g]) (by linarith [hmax g])
    nlinarith
  let y : Option ι → ℝ := fun o => o.elim (x g-v) x
  have hy : ∀ i,0 ≤ y i := by
    intro i
    cases i with
    | none => dsimp [y]; linarith
    | some i => exact hx i
  have hbal : 2*y (some g)=∑ i,y i := by
    rw [Fintype.sum_option]
    dsimp [y]
    change 2*x g=x g-v+s
    linarith
  obtain ⟨P⟩ := packing_balanced_at y hy (some g) hbal
  exact ⟨trianglePackingStep x hx h (x g-v) (1-κ) κ hθ hk0 (by ring) hroot hbound P⟩

end Erdos1017
