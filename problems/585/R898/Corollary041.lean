import R898.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Erdos585.R898
universe u

/-- The existing height choice supports the three-halves allowance from 200704. -/
theorem quantitative_numeric_200704 (q : ℕ) (hq : 200704 ≤ q) :
    6 ≤ height q ∧ 4096*(height q+1)^2 ≤ q ∧
    Real.rpow (q:ℝ) (3/2:ℝ)/128 ≤ (height q:ℝ)*q-16*(height q:ℝ)^2 := by
  let x : ℝ := Real.sqrt (q:ℝ)
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2 = (q:ℝ) := Real.sq_sqrt hq0
  have hqbig : (448:ℝ)^2 ≤ (q:ℝ) := by norm_num; exact hq
  have hxbig : 448 ≤ x := by nlinarith
  have hf7 : 7 ≤ ⌊x/64⌋₊ := Nat.le_floor (by linarith)
  have hheight : height q + 1 = ⌊x/64⌋₊ := by
    change ⌊x/64⌋₊ - 1 + 1 = ⌊x/64⌋₊
    omega
  have hfloor : (height q:ℝ)+1 ≤ x/64 := by
    have hf := Nat.floor_le (show 0 ≤ x/64 by positivity)
    rw [← hheight] at hf
    exact_mod_cast hf
  have hnext : x/64 < (height q:ℝ)+2 := by
    have hf := Nat.lt_floor_add_one (x/64)
    rw [← hheight] at hf
    exact_mod_cast hf
  have hh6 : 6 ≤ height q := by omega
  have hupper : (height q:ℝ) ≤ x/64 := by linarith
  have hlow : x/64-2 ≤ (height q:ℝ) := by linarith
  have hcutreal : (4096:ℝ)*((height q:ℝ)+1)^2 ≤ q := calc
    (4096:ℝ)*((height q:ℝ)+1)^2 ≤ 4096*(x/64)^2 := by gcongr
    _ = x^2 := by ring
    _ = q := hx2
  have hcut : 4096*(height q+1)^2 ≤ q := by exact_mod_cast hcutreal
  have hp3 : Real.rpow (q:ℝ) (3/2:ℝ) = x*q := by
    change (q:ℝ) ^ (3/2:ℝ) = x*q
    rw [show (3/2:ℝ) = 1/2+1 by norm_num,
      Real.rpow_add (show (0:ℝ) < q by exact_mod_cast (show 0 < q by omega)),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsquare : 16*(height q:ℝ)^2 ≤ x^2/256 := by
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ height q) hupper 2
    nlinarith
  have hlinear : (x/64-2)*q ≤ (height q:ℝ)*q := by
    exact mul_le_mul_of_nonneg_right hlow hq0
  have hreserve : (513/256:ℝ)*x^2 ≤ x^3/128 := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x-513/2 by linarith)]
  refine ⟨hh6, hcut, ?_⟩
  rw [hp3]
  nlinarith [show x*q = x^3 by rw [← hx2]; ring]

open scoped Classical in
/-- A separate smaller-cutoff corollary with the same literal original-subgraph conclusion.
The parameterized theorem and the earlier `superlinear_forcing` endpoint are unchanged. -/
theorem superlinear_forcing_200704 (q : ℕ) (hq : 200704 ≤ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hn : 2*q ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2*q-2)
    (he : ((q:ℝ)-1)*Fintype.card V-(G.edgeSet.ncard:ℝ) ≤
      Real.rpow (q:ℝ) (3/2:ℝ)/128) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨hh,hcut,hdef⟩ := quantitative_numeric_200704 q hq
  apply every_h_forcing (height q) q hh hcut G hbip hn hcap
  exact_mod_cast he.trans hdef

#print axioms quantitative_numeric_200704
#print axioms superlinear_forcing_200704
end Erdos585.R898
