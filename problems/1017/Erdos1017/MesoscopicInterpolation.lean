import Erdos1017.MesoscopicParameters

namespace Erdos1017.Mesoscopic

theorem baseEdges_lower_estimate (n s : ℕ) (hn : 100 ≤ n) (hs : 10*s ≤ n) :
    (n:ℝ)*s/2 - 13*(s:ℝ)^2/36 - 7*s/6 - 1 ≤
      (baseEdges n s:ℝ) - (n*n/4:ℕ) := by
  obtain ⟨_,_,_,hlo,hhi⟩ := part_bounds n s hn hs
  have hl : 3*(partB n s:ℝ)+2*s < 3*(partA n s:ℝ) := by exact_mod_cast hlo
  have hh : 3*(partA n s:ℝ) ≤ 3*(partB n s:ℝ)+2*s+6 := by exact_mod_cast hhi
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg s
  have hpos : 0 ≤ ((2:ℝ)*s/3+2)-((partA n s:ℝ)-partB n s-2) := by linarith
  have hneg : 0 ≤ ((2:ℝ)*s/3+2)+((partA n s:ℝ)-partB n s-2) := by linarith
  have hsq := mul_nonneg hpos hneg
  have hq := (quarter_bounds n).1
  rw [baseEdges_identity n s hn hs]
  nlinarith

theorem baseEdges_endpoint (n : ℕ) (hn : 100 ≤ n) :
    (n:ℝ)^2/100 < (baseEdges n (n/10):ℝ)-(n*n/4:ℕ) := by
  have hk0 : 10*(n/10) ≤ n := by omega
  have hk1 : n ≤ 10*(n/10)+9 := by omega
  have h0 : (0:ℝ) ≤ n/10 := by positivity
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hn100 : (100:ℝ) ≤ n := by exact_mod_cast hn
  have hklo : (n:ℝ)/10-1 ≤ (n/10:ℕ) := by
    have h : (n:ℝ) ≤ 10*(n/10:ℕ)+9 := by exact_mod_cast hk1
    linarith
  have hkhi : ((n/10:ℕ):ℝ) ≤ (n:ℝ)/10 := by
    have h : 10*((n/10:ℕ):ℝ) ≤ n := by exact_mod_cast hk0
    linarith
  have hk_nonneg : (0:ℝ) ≤ (n/10:ℕ) := Nat.cast_nonneg _
  have hmul := mul_nonneg hn0 (sub_nonneg.mpr hklo)
  have hsquare := mul_nonneg (sub_nonneg.mpr hkhi) (add_nonneg h0 hk_nonneg)
  have hquad := mul_nonneg hn0 (sub_nonneg.mpr hn100)
  have hE := baseEdges_lower_estimate n (n/10) hn hk0
  nlinarith

theorem baseEdges_upper_estimate (n s : ℕ) (hn : 100 ≤ n)
    (hs : 10*s ≤ n) (hs1 : 1 ≤ s) :
    (baseEdges n s:ℝ)-(n*n/4:ℕ) ≤ (n:ℝ)*s/2 := by
  have hsreal : (1:ℝ) ≤ s := by exact_mod_cast hs1
  have hq := (quarter_bounds n).2
  rw [baseEdges_identity n s hn hs]
  nlinarith [sq_nonneg ((partA n s:ℝ)-partB n s-2), sq_nonneg (s:ℝ)]

/-- Every required edge count lies in one of the neutral-edge intervals.
The returned s is strictly below floor(n/10), leaving the next interval
available for the quantitative estimate. -/
theorem interpolate (n m : ℕ) (hn : 100 ≤ n) (hm : 100*m ≤ n*n) :
    ∃ s t : ℕ, 10*(s+1) ≤ n ∧ t ≤ 2*partB n s ∧
      baseEdges n s+t=n*n/4+m ∧ (m:ℝ) < (n:ℝ)*(s+1)/2 := by
  have hend : n*n/4+m < baseEdges n (n/10) := by
    have he := baseEdges_endpoint n hn
    have hmreal : 100*(m:ℝ) ≤ (n:ℝ)^2 := by
      rw [pow_two]
      exact_mod_cast hm
    have h : (n*n/4:ℕ)+(m:ℝ) < (baseEdges n (n/10):ℝ) := by linarith
    exact_mod_cast h
  have hex : ∃ k : ℕ, k ≤ n/10 ∧ n*n/4+m < baseEdges n k :=
    ⟨n/10,le_rfl,hend⟩
  let k := Nat.find hex
  have hk : k ≤ n/10 ∧ n*n/4+m < baseEdges n k := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra h
    have hz : k=0 := by omega
    rw [hz,baseEdges_zero n hn] at hk
    omega
  let s := k-1
  have hsucc : s+1=k := by omega
  have hs : 10*(s+1) ≤ n := by omega
  have hsmall : baseEdges n s ≤ n*n/4+m := by
    have hmin := Nat.find_min hex (show s<k by omega)
    have hle : s ≤ n/10 := by omega
    omega
  let t := n*n/4+m-baseEdges n s
  have ht : baseEdges n s+t=n*n/4+m := by omega
  have hstep := (baseEdges_step n s hn hs).2
  have hnext : n*n/4+m < baseEdges n (s+1) := by simpa only [hsucc] using hk.2
  have htbound : t ≤ 2*partB n s := by omega
  refine ⟨s,t,hs,htbound,ht,?_⟩
  have hup := baseEdges_upper_estimate n (s+1) hn hs (by omega)
  have hnextreal : (n*n/4:ℕ)+(m:ℝ) < (baseEdges n (s+1):ℝ) := by exact_mod_cast hnext
  push_cast at hup
  linarith

end Erdos1017.Mesoscopic
