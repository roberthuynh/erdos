import R863.Interface
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R863
namespace Parameters
variable {h q j e : ℕ} (p : Parameters h q j e)
include p
lemma height_int : (6 : ℤ) ≤ h := by exact_mod_cast p.height
lemma error_int : (e : ℤ) ≤ 4*(h : ℤ)^2-10*h+4 := by
  have ht : 10*h ≤ 4*h^2 := by nlinarith [p.height]
  have he := p.error_bound
  have hez : (e : ℤ) ≤ ((4*h^2-10*h+4 : ℕ) : ℤ) := by exact_mod_cast he
  push_cast [Nat.cast_sub ht] at hez
  exact hez
lemma offset_cast : (offset h e : ℤ) = 16*(h : ℤ)^2-e := by
  have he : e ≤ 16*h^2 := by have hb:=p.error_int; have hh:=p.height_int; nlinarith
  simp only [offset, Nat.cast_sub he, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
lemma large_int : 1048576*((h : ℤ)+e+1)^2 ≤ q := by exact_mod_cast p.large
lemma j_pos : 0 < j := by have hj:=p.positive;omega
lemma j_bounds : (1 : ℤ) ≤ j ∧ (j : ℤ) ≤ h-1 := by
  have hj:=p.positive;have hu:=p.surplus;have hh:=p.height;omega
lemma cutoff : 1000*((h : ℤ)+e+1)^2 < q := by
  have hq:=p.large_int
  have hh:=p.height_int
  have he : (0 : ℤ) ≤ e := Nat.cast_nonneg _
  nlinarith [sq_nonneg ((h : ℤ)+e+1)]
lemma numeric :
    4*(offset h e : ℤ)+100*(h : ℤ)^2 ≤ q ∧
    5*(h : ℤ)<offset h e ∧ 3*(j : ℤ)+2<offset h e ∧
    6*(h : ℤ)<q ∧ (offset h e : ℤ)+4*h<q ∧ 40*(h : ℤ)^2<q := by
  have hh:=p.height_int;have he:=p.error_int;have hj:=p.j_bounds
  have hq:=p.cutoff
  have he0 : (0 : ℤ) ≤ e := Nat.cast_nonneg _
  have hsq : (h : ℤ)^2 ≤ ((h : ℤ)+e+1)^2 := by nlinarith
  rw [p.offset_cast]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg (h : ℤ)]
lemma expanded :
    (offset h e : ℤ)+4*h+2*e+50*((h : ℤ)+e+1)^2<q ∧
    100*((h : ℤ)+e+1)^2≤q ∧
    3*(j : ℤ)+h+e<offset h e ∧
    (q : ℤ)-2*h-e-1≥q/2 ∧
    (q : ℤ)-1-(5*h+e)≥h ∧
    20*(h : ℤ)^2-8*h-1<q ∧
    2*((e : ℤ)+5*h)≤q ∧
    4*(h : ℤ)<q+1 := by
  have hh:=p.height_int;have he:=p.error_int;have hj:=p.j_bounds
  have hq:=p.cutoff
  have he0 : (0 : ℤ) ≤ e := Nat.cast_nonneg _
  have hsq : (h : ℤ)^2 ≤ ((h : ℤ)+e+1)^2 := by nlinarith
  have hl : (h : ℤ)+e+1 ≤ ((h : ℤ)+e+1)^2 := by nlinarith
  rw [p.offset_cast]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals omega
lemma geometry_numeric :
    (offset h e : ℤ)+4*h+2*e+50*((h : ℤ)+e+1)^2<q ∧
    100*((h : ℤ)+e+1)^2≤q ∧ 3*(j : ℤ)+h+e<offset h e :=
  ⟨p.expanded.1,p.expanded.2.1,p.expanded.2.2.1⟩
lemma owner_numeric :
    (q : ℤ)≤2*((q : ℤ)-2*h-e-1) ∧
    (q : ℤ)-1-(5*h+e)≥h ∧ 20*(h : ℤ)^2-8*h-1<q ∧
    0≤(offset h e : ℤ) ∧ (offset h e : ℤ)≤16*(h : ℤ)^2 := by
  have hh:=p.height_int;have he:=p.error_int;have hq:=p.cutoff
  have he0 : (0 : ℤ)≤e := Nat.cast_nonneg _
  have hl : (h : ℤ)+e+1≤((h : ℤ)+e+1)^2 := by nlinarith
  have hn:=p.expanded
  rw [p.offset_cast]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg (h : ℤ)]
lemma q_pos : 0<q := by have hn:=p.numeric;have hh:=p.height;omega
lemma q_ge_height : h+3≤q := by have hn:=p.numeric;have hh:=p.height;omega
lemma offset_le_product : offset h e≤h*q := by
  have hn:=p.numeric;have hh:=p.height_int
  have hp : (offset h e : ℤ)≤(h : ℤ)*q := by
    nlinarith [mul_nonneg (show 0≤(h : ℤ)-1 by omega) (show 0≤(q : ℤ) by omega)]
  exact_mod_cast hp
lemma constant_cast : (constant h q e : ℤ)=(h : ℤ)*q-offset h e := by
  unfold constant
  rw [Nat.cast_sub p.offset_le_product,Nat.cast_mul]
lemma scar_lower : (q : ℤ)-offset h e≤(h : ℤ)*q-offset h e-((q : ℤ)-1)*j := by
  have hj:=p.j_bounds;have hq:=p.q_pos
  have hm : 0≤((h : ℤ)-j-1)*q := mul_nonneg (by omega) (by omega)
  nlinarith
end Parameters
end Erdos585.R863
