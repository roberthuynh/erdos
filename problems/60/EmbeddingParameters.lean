import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! A deliberately slack large-order specialization of Metsch's early route.
No geometric existence or incidence conclusion is assumed or asserted here. -/
namespace Erdos60.Embedding.Parameters

def cutoff (q : ℕ) : ℕ := Nat.sqrt q / 10
def allowance (q s : ℕ) : ℕ := 2*(s-q-2)/(cutoff q-1)

theorem cutoff_bounds (q : ℕ) (hq : 10^8 ≤ q) :
    1000 ≤ cutoff q ∧ q ≤ 200*(cutoff q)^2 ∧ 100*(cutoff q)^2 ≤ q ∧
      1000*cutoff q ≤ q ∧ (cutoff q+1)^2 ≤ q+2 := by
  let r := Nat.sqrt q
  let e := cutoff q
  have hr : 10000 ≤ r := (Nat.le_sqrt').mpr hq
  have heL : 10*e ≤ r := by dsimp [e,cutoff,r]; omega
  have heU : r ≤ 10*e+9 := by dsimp [e,cutoff,r]; omega
  have he : 1000 ≤ e := by omega
  have hs := Nat.sqrt_le' q
  have ht := Nat.lt_succ_sqrt' q
  change r^2 ≤ q at hs
  change q < (r+1)^2 at ht
  have hsL : (10*e)^2 ≤ r^2 := by gcongr
  have hsU : (r+1)^2 ≤ (10*e+10)^2 := pow_le_pow_left' (by omega) 2
  have h100 : 100*e^2 ≤ q := by nlinarith
  have h200 : q ≤ 200*e^2 := by nlinarith
  have h1000 : 1000*e ≤ q := by nlinarith
  have hnext : (e+1)^2 ≤ q+2 := by nlinarith
  exact ⟨he,h200,h100,h1000,hnext⟩

theorem allowance_bound (q s : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s) :
    200000*allowance q s ≤ q := by
  let e := cutoff q
  let t := s-q-2
  let a := allowance q s
  have he : 1000 ≤ e := (cutoff_bounds q hq).1
  have hst : s = t+q+2 := by dsimp [t]; omega
  have ht : 500*t ≤ q := by omega
  have hd : a*(e-1) ≤ 2*t := Nat.div_mul_le_self _ _
  have hem : 999 ≤ e-1 := by omega
  have hm := Nat.mul_le_mul_left a hem
  have ha : 999*a ≤ 2*t := by nlinarith
  change 200000*a ≤ q
  omega

/-- All natural differences used in the source clique comparisons are ordinary
nonnegative differences in the required branch. -/
theorem subtraction_bounds (q s : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s) :
    cutoff q ≤ q ∧ 1 ≤ cutoff q ∧ allowance q s+1 ≤ q := by
  have he := cutoff_bounds q hq
  have ha := allowance_bound q s hq hs hbranch
  omega

/-- The moment inequality that forces at most q-e short lines. -/
theorem short_moment_strict (q s : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s) :
    s*(s-q-2) < (q-cutoff q+1)*((cutoff q)^2-1) := by
  let e := cutoff q
  let t := s-q-2
  have he := cutoff_bounds q hq
  have he0 : 1000 ≤ e := he.1
  have he2 : q ≤ 200*e^2 := he.2.1
  have heq : 1000*e ≤ q := he.2.2.2.1
  have hst : s = t+q+2 := by dsimp [t]; omega
  have ht : 500*t ≤ q := by omega
  have hL : 999*q ≤ 1000*(q-e+1) := by omega
  have hR : q ≤ 400*(e^2-1) := by
    have hh : e^2-1+1 = e^2 := by omega
    nlinarith
  have hprodL := Nat.mul_le_mul hL hR
  have hprodR := Nat.mul_le_mul hs ht
  have hqpos : 0 < q := by omega
  change s*t < (q-e+1)*(e^2-1)
  nlinarith

/-- The stronger source remark (5') gives immediate global clique uniqueness. -/
theorem strong_clique_union_strict (q s : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s) :
    q+1+(cutoff q-1)^2+(cutoff q)^2 < 2*(q-allowance q s) := by
  let e := cutoff q
  let a := allowance q s
  have he := cutoff_bounds q hq
  have ha : 200000*a ≤ q := allowance_bound q s hq hs hbranch
  have h100 : 100*e^2 ≤ q := he.2.2.1
  have he1 : 1 ≤ e := by have := he.1; omega
  have hem : (e-1)^2 ≤ e^2 := by gcongr; omega
  have haq : a ≤ q := by omega
  have hsub : q-a+a = q := Nat.sub_add_cancel haq
  change q+1+(e-1)^2+e^2 < 2*(q-a)
  nlinarith

/-- Three good cliques through a deficit-two line would exceed all its parallels. -/
theorem triple_clique_strict (q s : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s) :
    2*q < 3*(q-1-allowance q s) := by
  let a := allowance q s
  have ha : 200000*a ≤ q := allowance_bound q s hq hs hbranch
  have hsub : q-1-a+a+1 = q := by omega
  change 2*q < 3*(q-1-a)
  omega

/-- The source higher-deficit induction works already for d=3 in our range. -/
theorem all_deficits_induction_strict (q s d : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hd : 3 ≤ d) : d*s < 2*(d-1)*q+d^2 := by
  have hdm : d-1+1 = d := by omega
  have hm := Nat.mul_le_mul_left d hs
  have hp : 3*q ≤ d*q := Nat.mul_le_mul_right q hd
  nlinarith

/-- The allowance is the source's maximal integer, not just a loose bound. -/
theorem allowance_spec (q s : ℕ) (hq : 10^8 ≤ q) :
    allowance q s*(cutoff q-1) ≤ 2*(s-q-2) ∧
      2*(s-q-2) < (allowance q s+1)*(cutoff q-1) := by
  have he : 0 < cutoff q-1 := by have := (cutoff_bounds q hq).1; omega
  constructor
  · exact Nat.div_mul_le_self _ _
  · simpa [allowance,Nat.mul_comm] using Nat.lt_mul_div_succ (2*(s-q-2)) he

/-- The original Proposition 6.1 inequalities also hold with wide margins;
the specialized clique proof uses the stronger comparisons above. -/
theorem proposition_numeric (q s : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hbranch : q+2 ≤ s) :
    2*s ≤ 3*q+2 ∧
      (cutoff q)^2-2*cutoff q+5+2*allowance q s ≤ q ∧
      (cutoff q)^2+4+allowance q s ≤ q ∧
      3*cutoff q+1+2*allowance q s ≤ q ∧
      s*(cutoff q+3) ≤ 2*(cutoff q+1)*q-5*cutoff q+32 := by
  let e := cutoff q
  let a := allowance q s
  have he := cutoff_bounds q hq
  have he0 : 1000 ≤ e := he.1
  have h100 : 100*e^2 ≤ q := he.2.2.1
  have h1000 : 1000*e ≤ q := he.2.2.2.1
  have ha : 200000*a ≤ q := allowance_bound q s hq hs hbranch
  have he2 : 2*e ≤ e^2 := by nlinarith
  have hsub : e^2-2*e+2*e = e^2 := Nat.sub_add_cancel he2
  have h2s : 2*s ≤ 3*q+2 := by omega
  have hfirst : e^2-2*e+5+2*a ≤ q := by nlinarith
  have hsecond : e^2+4+a ≤ q := by nlinarith
  have hthird : 3*e+1+2*a ≤ q := by omega
  refine ⟨h2s,hfirst,hsecond,hthird,?_⟩
  have hmul := Nat.mul_le_mul_right (e+3) hs
  have heqmul := Nat.mul_le_mul_right q he0
  have hbase : 5*e ≤ 2*(e+1)*q := by nlinarith
  have hminus : 2*(e+1)*q-5*e+5*e = 2*(e+1)*q := Nat.sub_add_cancel hbase
  change s*(e+3) ≤ 2*(e+1)*q-5*e+32
  nlinarith

/-- The weighted-line induction comparison in its original product form. -/
theorem all_deficits_product_strict (q s d : ℕ) (hq : 10^8 ≤ q)
    (hs : 500*s ≤ 501*q) (hd : 3 ≤ d) :
    (d-1)*q*(d-2) < d*((d-1)*q+d-s) := by
  have hh := all_deficits_induction_strict q s d hq hs hd
  have hd1 : d-1+1 = d := by omega
  have hd2 : d-2+2 = d := by omega
  have hm := Nat.mul_le_mul_right q hd
  have hpositive : s ≤ (d-1)*q+d := by nlinarith
  have hsub : (d-1)*q+d-s+s = (d-1)*q+d := Nat.sub_add_cancel hpositive
  nlinarith

#print axioms allowance_spec
#print axioms proposition_numeric
#print axioms all_deficits_product_strict
#print axioms cutoff_bounds
#print axioms allowance_bound
#print axioms short_moment_strict
#print axioms strong_clique_union_strict
#print axioms triple_clique_strict
#print axioms all_deficits_induction_strict
end Erdos60.Embedding.Parameters
