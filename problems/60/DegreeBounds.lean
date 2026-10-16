import GraphStatistics
import SubsetPathCount
import Parameters
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Cast

namespace Erdos60.DegreeBounds
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem vertex_count_le_total (G : SimpleGraph V) (x : V) :
    Statistics.vertexCycleStatistic G x ≤ Counting.cycleCount G := by
  rw [Statistics.vertexCycleStatistic_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Source §2's initial codegree-row estimate, on the actual host graph. -/
theorem codegree_row_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hN : Fintype.card V = q^2+q+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) (x : V) :
    (∑ y ∈ Finset.univ.erase x, Statistics.codegree G x y : ℕ) <
      (q : ℝ)^2 + (T+1)*q := by
  have hb := Statistics.vertexCycleStatistic_lower G x
  have hc := vertex_count_le_total G x
  have hn : (∑ y ∈ Finset.univ.erase x, Statistics.codegree G x y) ≤
      Counting.cycleCount G + q^2 + q := by
    rw [← Statistics.twoPath_count] at hb
    rw [hN] at hb
    omega
  have hr : ((∑ y ∈ Finset.univ.erase x, Statistics.codegree G x y : ℕ) : ℝ) ≤
      (Counting.cycleCount G : ℝ) + (q : ℝ)^2 + q := by
    exact_mod_cast hn
  linarith

 theorem choose_tangent (r b : ℕ) :
    ((b.choose 2 : ℕ) : ℝ) + b*((r : ℝ)-b) ≤ (r.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  rcases le_or_gt r b with h | h
  · have hc : (r : ℝ) ≤ b := by exact_mod_cast h
    nlinarith [mul_nonneg (show 0 ≤ (b : ℝ)-r by linarith)
      (show 0 ≤ (b : ℝ)-r+1 by linarith)]
  · have hc : (b : ℝ)+1 ≤ r := by exact_mod_cast h
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ)-b by linarith)
      (show 0 ≤ (r : ℝ)-b-1 by linarith)]

noncomputable def exteriorCount (G : SimpleGraph V) (v i : V) : ℕ :=
  (G.neighborFinset i \ G.neighborFinset v).card

 theorem exterior_add_codegree (G : SimpleGraph V) (v i : V) :
    exteriorCount G v i + Statistics.codegree G v i = G.degree i := by
  classical
  unfold exteriorCount Statistics.codegree
  rw [Finset.inter_comm, Finset.card_sdiff_add_card_inter,
    G.card_neighborFinset_eq_degree]

 theorem exterior_self (G : SimpleGraph V) (v : V) : exteriorCount G v v = 0 := by
  classical
  simp [exteriorCount]

 theorem exterior_sum (G : SimpleGraph V) (v : V) :
    ((∑ i ∈ Finset.univ.erase v, exteriorCount G v i : ℕ) : ℝ) =
      2*(G.edgeFinset.card : ℝ) - G.degree v -
      (∑ i ∈ Finset.univ.erase v, Statistics.codegree G v i : ℕ) := by
  classical
  have hsum : (∑ i ∈ Finset.univ.erase v, exteriorCount G v i) +
      (∑ i ∈ Finset.univ.erase v, Statistics.codegree G v i) =
        ∑ i ∈ Finset.univ.erase v, G.degree i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact exterior_add_codegree G v i
  have hhand := G.sum_degrees_eq_twice_card_edges
  have herase := Finset.sum_erase_add Finset.univ (fun i => G.degree i) (by simp : v ∈ Finset.univ)
  have hn : (∑ i ∈ Finset.univ.erase v, exteriorCount G v i) +
      (∑ i ∈ Finset.univ.erase v, Statistics.codegree G v i) + G.degree v =
        2*G.edgeFinset.card := by omega
  have hr : ((∑ i ∈ Finset.univ.erase v, exteriorCount G v i : ℕ) : ℝ) +
      (∑ i ∈ Finset.univ.erase v, Statistics.codegree G v i : ℕ) + G.degree v =
        2*(G.edgeFinset.card : ℝ) := by exact_mod_cast hn
  linarith

 theorem sum_choose_tangent {I : Type*} (s : Finset I) (r : I → ℕ) (b : ℕ) :
    (s.card : ℝ)*(b.choose 2 : ℝ) +
      b*((∑ i ∈ s, (r i : ℝ)) - (s.card : ℝ)*b) ≤
        ∑ i ∈ s, ((r i).choose 2 : ℝ) := by
  calc
    _ = ∑ i ∈ s, ((b.choose 2 : ℝ) + b*((r i : ℝ)-b)) := by
      simp_rw [mul_sub]
      simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_sub_distrib]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ => choose_tangent (r i) b)

 theorem exterior_tangent (G : SimpleGraph V) (q : ℕ)
    (hq : 1 ≤ q) (hN : Fintype.card V = q^2+q+1) (v : V) :
    ((q : ℝ)^2+q)*((q : ℝ)-1)*((q : ℝ)-2)/2 +
      ((q : ℝ)-1)*(((∑ i ∈ Finset.univ.erase v, exteriorCount G v i : ℕ) : ℝ) -
        ((q : ℝ)^2+q)*((q : ℝ)-1)) ≤
      ∑ i ∈ Finset.univ.erase v, ((exteriorCount G v i).choose 2 : ℝ) := by
  have ht := sum_choose_tangent (Finset.univ.erase v) (exteriorCount G v) (q-1)
  have hs : ((Finset.univ.erase v).card : ℝ) = (q : ℝ)^2+q := by
    simp [hN]
  rw [hs, Nat.cast_choose_two, Nat.cast_sub hq] at ht
  push_cast at ht
  simp only [Nat.cast_sum]
  nlinarith [ht]

 theorem exterior_budget (G : SimpleGraph V) (q : ℕ)
    (hN : Fintype.card V = q^2+q+1) (v : V) :
    (∑ i ∈ Finset.univ.erase v, ((exteriorCount G v i).choose 2 : ℝ)) ≤
      2*(Counting.cycleCount G : ℝ) +
        ((q : ℝ)^2+q+1-G.degree v)*((q : ℝ)^2+q-G.degree v)/2 := by
  classical
  let A := Finset.univ \ G.neighborFinset v
  have h := Statistics.subset_path_bound G A
  have hcount (w : V) : (G.neighborFinset w ∩ A).card = exteriorCount G v w := by
    congr 1
    ext z
    simp [A]
  simp_rw [hcount] at h
  have hsum : (∑ i ∈ Finset.univ.erase v, (exteriorCount G v i).choose 2) =
      ∑ i : V, (exteriorCount G v i).choose 2 := by
    have he := Finset.sum_erase_add Finset.univ
      (fun i => (exteriorCount G v i).choose 2) (by simp : v ∈ Finset.univ)
    simpa [exterior_self] using he
  rw [← hsum] at h
  have hAc : A.card + G.degree v = Fintype.card V := by
    simpa [A, G.card_neighborFinset_eq_degree] using
      Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) (G.neighborFinset v)
  have hAcr : (A.card : ℝ) = (q : ℝ)^2+q+1-G.degree v := by
    rw [hN] at hAc
    have hr : (A.card : ℝ) + G.degree v = (q : ℝ)^2+q+1 := by
      exact_mod_cast hAc
    linarith
  have hr : (∑ i ∈ Finset.univ.erase v, ((exteriorCount G v i).choose 2 : ℝ)) ≤
      2*(Counting.cycleCount G : ℝ) + (A.card.choose 2 : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_choose_two, hAcr] at hr
  linarith

/-- The lower endpoint polynomial is derived from actual subset path counts,
not supplied as a hypothesis. -/
theorem degree_polynomial_lower (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : 1 ≤ q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) (v : V) :
    Parameters.degreeF q T ((G.degree v : ℝ)-q) ≤ 2*(Counting.cycleCount G : ℝ) := by
  have ht := exterior_tangent G q hq hN v
  have hb := exterior_budget G q hN v
  rw [exterior_sum, hE] at ht
  have hr := codegree_row_bound G q T hN hZ v
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp := mul_nonneg (show 0 ≤ (q : ℝ)-1 by linarith)
    (show 0 ≤ (q : ℝ)^2+(T+1)*q-
      ((∑ y ∈ Finset.univ.erase v, Statistics.codegree G v y : ℕ) : ℝ) by linarith)
  unfold Parameters.degreeF
  nlinarith

/-- Maximum degree from source §2, with the exact strict cutoff. Hypotheses
refer to one actual graph with M+1 edges and its ordinary edge-set C4 count. -/
theorem maximum_degree (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) (v : V) :
    (G.degree v : ℝ) < q+T+3 := by
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hl := degree_polynomial_lower G q T hq1 hN hE hZ v
  by_contra hn
  have hk : T+3 ≤ (G.degree v : ℝ)-q := by linarith
  have hd := G.degree_lt_card_verts v
  rw [hN] at hd
  have hdr : (G.degree v : ℝ) < (q : ℝ)^2+q+1 := by exact_mod_cast hd
  have hdn : G.degree v ≤ q^2+q := by omega
  have hdr' : (G.degree v : ℝ) ≤ (q : ℝ)^2+q := by exact_mod_cast hdn
  have hk' : (G.degree v : ℝ)-q ≤ (q : ℝ)^2 := by linarith
  have hp := Parameters.degree_interval hq hT hr hk hk'
  linarith

end Erdos60.DegreeBounds
