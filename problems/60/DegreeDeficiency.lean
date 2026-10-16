import GraphStatistics
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Actual degree deficiency/surplus balance and source §1 equation (2).
Deficiency is truncated at zero, as in the frozen proof, not signed. -/
namespace Erdos60.Statistics
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def degreeDeficiency (G : SimpleGraph V) (q : ℕ) (x : V) : ℕ :=
  q + 1 - G.degree x
noncomputable def degreeSurplus (G : SimpleGraph V) (q : ℕ) (x : V) : ℕ :=
  G.degree x - (q + 1)
noncomputable def totalDeficiency (G : SimpleGraph V) (q : ℕ) : ℕ :=
  ∑ x : V, degreeDeficiency G q x
noncomputable def totalSurplus (G : SimpleGraph V) (q : ℕ) : ℕ :=
  ∑ x : V, degreeSurplus G q x
noncomputable def deficiencyOn (G : SimpleGraph V) (q : ℕ) (A : Finset V) : ℕ :=
  ∑ x ∈ A, degreeDeficiency G q x

omit [DecidableEq V] in
theorem degree_add_deficiency (G : SimpleGraph V) (q : ℕ) (x : V) :
    G.degree x + degreeDeficiency G q x = q + 1 + degreeSurplus G q x := by
  unfold degreeDeficiency degreeSurplus
  omega

omit [DecidableEq V] in
theorem total_degree_balance (G : SimpleGraph V) (q : ℕ) :
    2 * G.edgeFinset.card + totalDeficiency G q =
      Fintype.card V * (q + 1) + totalSurplus G q := by
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
    (fun x hx => degree_add_deficiency G q x)
  simpa [Finset.sum_add_distrib,G.sum_degrees_eq_twice_card_edges,
    totalDeficiency,totalSurplus] using hs

omit [DecidableEq V] in
/-- Source exact deficiency identity, under the actual edge-count hypothesis
used by the localization modules. No parity is needed once this real count is supplied. -/
theorem totalDeficiency_eq (G : SimpleGraph V) (q : ℕ) (hq : 1 ≤ q)
    (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1) :
    totalDeficiency G q = q - 1 + totalSurplus G q := by
  have hb := total_degree_balance G q
  rw [hN] at hb
  have hbr : 2*(G.edgeFinset.card : ℝ) + totalDeficiency G q =
      ((q : ℝ)^2+q+1)*(q+1) + totalSurplus G q := by exact_mod_cast hb
  rw [hE] at hbr
  have heq : totalDeficiency G q + 1 = q + totalSurplus G q := by
    have hr : (totalDeficiency G q : ℝ)+1 = q + totalSurplus G q := by nlinarith
    exact_mod_cast hr
  omega

omit [DecidableEq V] in
/-- The natural edge formula agrees with the localization edge hypothesis for
even q; its division by two is exact, rather than silently truncated. -/
theorem edge_count_real_of_even (G : SimpleGraph V) (q : ℕ) (heven : Even q)
    (hE : G.edgeFinset.card = q*(q+1)^2/2+1) :
    (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1 := by
  rcases heven with ⟨k,hk⟩
  have hq : q = 2*k := by omega
  have hdiv : 2 ∣ q*(q+1)^2 := ⟨k*(q+1)^2,by rw [hq]; ring⟩
  have htwice : 2*(q*(q+1)^2/2) = q*(q+1)^2 := Nat.mul_div_cancel' hdiv
  have hn : 2*G.edgeFinset.card = q*(q+1)^2+2 := by rw [hE]; omega
  have hr : 2*(G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2+2 := by exact_mod_cast hn
  linarith

omit [DecidableEq V] in
theorem totalDeficiency_eq_of_even (G : SimpleGraph V) (q : ℕ) (hq : 1 ≤ q)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : G.edgeFinset.card = q*(q+1)^2/2+1) :
    totalDeficiency G q = q - 1 + totalSurplus G q :=
  totalDeficiency_eq G q hq hN (edge_count_real_of_even G q heven hE)

omit [DecidableEq V] in
/-- Actual neighborhood degree lower bound, retaining all truncated deficiencies. -/
theorem neighbor_degree_deficiency_lower (G : SimpleGraph V) (q : ℕ) (x : V) :
    G.degree x * q ≤
      (∑ w ∈ G.neighborFinset x, (G.degree w - 1)) +
        deficiencyOn G q (G.neighborFinset x) := by
  classical
  have hs : (∑ w ∈ G.neighborFinset x, q) ≤
      ∑ w ∈ G.neighborFinset x, ((G.degree w - 1) + degreeDeficiency G q w) := by
    apply Finset.sum_le_sum
    intro w hw
    have hd : 1 ≤ G.degree w := by
      exact (G.degree_pos_iff_exists_adj w).mpr
        ⟨x,((G.mem_neighborFinset x w).mp hw).symm⟩
    unfold degreeDeficiency
    omega
  simpa [Finset.sum_add_distrib,deficiencyOn,G.card_neighborFinset_eq_degree] using hs

/-- Source equation (2), written without subtraction on its left side.
The RHS uses signed real degree excess; c(x) is the actual ordinary C4 count
through x and d0(x) counts actual zero-codegree vertices. -/
theorem vertex_cycle_deficiency_lower (G : SimpleGraph V) (q : ℕ)
    (hN : Fintype.card V = q^2+q+1) (x : V) :
    (vertexCycleStatistic G x : ℝ) + deficiencyOn G q (G.neighborFinset x) ≥
      ((G.degree x : ℝ)-q-1)*q + zeroCodegreeCount G x := by
  have hn := neighbor_degree_deficiency_lower G q x
  have hc := vertexCycleStatistic_lower G x
  have hn' : G.degree x * q + zeroCodegreeCount G x ≤
      vertexCycleStatistic G x + (q^2+q) + deficiencyOn G q (G.neighborFinset x) := by
    rw [hN] at hc
    omega
  have hr : (G.degree x : ℝ)*q + zeroCodegreeCount G x ≤
      vertexCycleStatistic G x + ((q : ℝ)^2+q) + deficiencyOn G q (G.neighborFinset x) := by
    exact_mod_cast hn'
  nlinarith

end Erdos60.Statistics
