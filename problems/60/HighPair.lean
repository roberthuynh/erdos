import DegreeBounds

namespace Erdos60.HighPair
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def otherVertices (u v : V) : Finset V := Finset.univ \ {u,v}
noncomputable def unionCount (G : SimpleGraph V) (u v i : V) : ℕ :=
  (G.neighborFinset i ∩ (G.neighborFinset u ∪ G.neighborFinset v)).card
noncomputable def outsideCount (G : SimpleGraph V) (u v i : V) : ℕ :=
  (G.neighborFinset i \ (G.neighborFinset u ∪ G.neighborFinset v)).card

 theorem row_on_other (G : SimpleGraph V) (u v : V) :
    (∑ i ∈ otherVertices u v, Statistics.codegree G u i) ≤
      Statistics.vertexCycleStatistic G u + (otherVertices u v).card := by
  classical
  have hs : (∑ i ∈ otherVertices u v, Statistics.codegree G u i) ≤
      (∑ i ∈ otherVertices u v, (Statistics.codegree G u i).choose 2) +
        (otherVertices u v).card := by
    have h := Finset.sum_le_sum (s := otherVertices u v)
      (fun i _ => show Statistics.codegree G u i ≤
        (Statistics.codegree G u i).choose 2 + 1 by
          have hh := Statistics.choose_two_lower (Statistics.codegree G u i)
          omega)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Nat.smul_one_eq_cast,
      Nat.cast_id] using h
  have hw : (∑ i ∈ otherVertices u v, (Statistics.codegree G u i).choose 2) ≤
      Statistics.vertexCycleStatistic G u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [otherVertices, Finset.mem_sdiff, Finset.mem_univ,
        Finset.mem_insert, Finset.mem_singleton, true_and, not_or] at hi
      simp [hi.1]
    · intro i hi hn; exact Nat.zero_le _
  omega

 theorem union_add_intersection (G : SimpleGraph V) (u v i : V) :
    unionCount G u v i +
      (G.neighborFinset i ∩ (G.neighborFinset u ∩ G.neighborFinset v)).card =
        Statistics.codegree G u i + Statistics.codegree G v i := by
  classical
  have h := Finset.card_union_add_card_inter (G.neighborFinset i ∩ G.neighborFinset u)
    (G.neighborFinset i ∩ G.neighborFinset v)
  simpa [unionCount, Statistics.codegree, Finset.inter_union_distrib_left,
    Finset.inter_assoc, Finset.inter_left_comm, Finset.inter_comm] using h

 theorem outside_add_union (G : SimpleGraph V) (u v i : V) :
    outsideCount G u v i + unionCount G u v i = G.degree i := by
  classical
  exact (Finset.card_sdiff_add_card_inter _ _).trans (G.card_neighborFinset_eq_degree i)

 theorem sum_other_add {M : Type*} [AddCommMonoid M] (f : V → M)
    {u v : V} (huv : u ≠ v) :
    (∑ i ∈ otherVertices u v, f i) + f u + f v = ∑ i : V, f i := by
  classical
  have he : otherVertices u v = (Finset.univ.erase u).erase v := by
    ext i
    simp [otherVertices, and_comm]
  rw [he]
  have h1 := Finset.sum_erase_add (Finset.univ.erase u) f (by simp [huv.symm] : v ∈ Finset.univ.erase u)
  have h2 := Finset.sum_erase_add Finset.univ f (by simp : u ∈ Finset.univ)
  calc
    _ = ((∑ i ∈ (Finset.univ.erase u).erase v, f i) + f v) + f u := by ac_rfl
    _ = _ := by rw [h1,h2]

 theorem other_card {u v : V} (huv : u ≠ v) :
    (otherVertices u v).card + 2 = Fintype.card V := by
  have h := sum_other_add (fun _ : V => (1 : ℕ)) huv
  simpa using h

 theorem union_row_bound (G : SimpleGraph V) (u v : V) :
    (∑ i ∈ otherVertices u v, unionCount G u v i) ≤
      Statistics.vertexCycleStatistic G u + Statistics.vertexCycleStatistic G v +
        2*(otherVertices u v).card := by
  have h1 := row_on_other G u v
  have h2 := row_on_other G v u
  have hr : otherVertices v u = otherVertices u v := by
    simp [otherVertices, Finset.pair_comm]
  rw [hr] at h2
  have h3 : (∑ i ∈ otherVertices u v, unionCount G u v i) ≤
      (∑ i ∈ otherVertices u v, Statistics.codegree G u i) +
        (∑ i ∈ otherVertices u v, Statistics.codegree G v i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := union_add_intersection G u v i
    omega
  omega

 theorem outside_sum_balance (G : SimpleGraph V) {u v : V} (huv : u ≠ v) :
    (∑ i ∈ otherVertices u v, outsideCount G u v i) +
      (∑ i ∈ otherVertices u v, unionCount G u v i) + G.degree u + G.degree v =
        2*G.edgeFinset.card := by
  have h := sum_other_add (fun i => G.degree i) huv
  rw [G.sum_degrees_eq_twice_card_edges] at h
  have hs : (∑ i ∈ otherVertices u v, outsideCount G u v i) +
      (∑ i ∈ otherVertices u v, unionCount G u v i) =
        ∑ i ∈ otherVertices u v, G.degree i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => outside_add_union G u v i)
  omega

 theorem outside_subset_budget (G : SimpleGraph V) (u v : V) (R : Finset V) :
    (∑ i ∈ R, ((outsideCount G u v i).choose 2 : ℝ)) ≤
      2*(Counting.cycleCount G : ℝ) +
        ((Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card.choose 2 : ℝ) := by
  classical
  let A := Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)
  have h := Statistics.subset_path_bound G A
  have hi (i : V) : (G.neighborFinset i ∩ A).card = outsideCount G u v i := by
    congr 1
    ext z
    simp [A]
  simp_rw [hi] at h
  have hs : (∑ i ∈ R, (outsideCount G u v i).choose 2) ≤
      ∑ i : V, (outsideCount G u v i).choose 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) (fun i _ _ => Nat.zero_le _)
  have hn := hs.trans h
  exact_mod_cast hn

 theorem complement_card (G : SimpleGraph V) (u v : V) :
    (Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card +
      G.degree u + G.degree v = Fintype.card V + Statistics.codegree G u v := by
  classical
  have h1 := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h2 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V)
    (G.neighborFinset u ∪ G.neighborFinset v)
  simp only [Finset.univ_inter, Finset.card_univ, G.card_neighborFinset_eq_degree] at h1 h2
  unfold Statistics.codegree
  omega

/-- Actual source equation (8), before invoking the parameter contradiction. -/
theorem disjoint_polynomial_lower (G : SimpleGraph V) (q : ℕ)
    (hq : 1 ≤ q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    {u v : V} (huv : u ≠ v) (hcodeg : Statistics.codegree G u v = 0)
    (hcu : (Statistics.vertexCycleStatistic G u : ℝ) < (q : ℝ)/5)
    (hcv : (Statistics.vertexCycleStatistic G v : ℝ) < (q : ℝ)/5) :
    Parameters.disjointLower q ((G.degree u : ℝ)+G.degree v-2*q-2) ≤
      2*(Counting.cycleCount G : ℝ) := by
  classical
  let R := otherVertices u v
  have hRc : (R.card : ℝ) = (q : ℝ)^2+q-1 := by
    have hn := other_card huv
    rw [hN] at hn
    have hr : (R.card : ℝ)+2 = (q : ℝ)^2+q+1 := by exact_mod_cast hn
    linarith
  have hrow := union_row_bound G u v
  have hrowr : ((∑ i ∈ R, unionCount G u v i : ℕ) : ℝ) ≤
      Statistics.vertexCycleStatistic G u + Statistics.vertexCycleStatistic G v +
        2*(R.card : ℝ) := by exact_mod_cast hrow
  rw [hRc] at hrowr
  have hbal := outside_sum_balance G huv
  have hbalr : ((∑ i ∈ R, outsideCount G u v i : ℕ) : ℝ) +
      (∑ i ∈ R, unionCount G u v i : ℕ) + G.degree u + G.degree v =
        2*(G.edgeFinset.card : ℝ) := by exact_mod_cast hbal
  rw [hE] at hbalr
  have hlo : ((q : ℝ)^2+q-1)*((q : ℝ)-1)-(q : ℝ)+1-
      ((G.degree u : ℝ)+G.degree v-2*q-2)-2*q/5 ≤
        ((∑ i ∈ R, outsideCount G u v i : ℕ) : ℝ) := by nlinarith
  have ht := DegreeBounds.sum_choose_tangent R (outsideCount G u v) (q-1)
  rw [hRc,Nat.cast_choose_two,Nat.cast_sub hq] at ht
  push_cast at ht
  have hb := outside_subset_budget G u v R
  have hac := complement_card G u v
  rw [hN,hcodeg] at hac
  have hacr : ((Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card : ℝ) =
      (q : ℝ)^2+q+1-G.degree u-G.degree v := by
    have hc : ((Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card : ℝ) +
        G.degree u+G.degree v = (q : ℝ)^2+q+1 := by exact_mod_cast hac
    linarith
  rw [Nat.cast_choose_two,hacr] at hb
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp := mul_nonneg (show 0 ≤ (q : ℝ)-1 by linarith) (sub_nonneg.mpr hlo)
  simp only [Nat.cast_sum] at hp
  unfold Parameters.disjointLower
  nlinarith

 theorem high_pair_not_disjoint (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    {u v : V} (huv : u ≠ v) (hdu : q+2 ≤ G.degree u) (hdv : q+2 ≤ G.degree v)
    (hcu : (Statistics.vertexCycleStatistic G u : ℝ) < (q : ℝ)/5)
    (hcv : (Statistics.vertexCycleStatistic G v : ℝ) < (q : ℝ)/5) :
    Statistics.codegree G u v ≠ 0 := by
  intro hzero
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hlo := disjoint_polynomial_lower G q hq1 hN hE huv hzero hcu hcv
  have hmu := DegreeBounds.maximum_degree G q T hq hT hr hN hE hZ u
  have hmv := DegreeBounds.maximum_degree G q T hq hT hr hN hE hZ v
  have hdu' : (q : ℝ)+2 ≤ G.degree u := by exact_mod_cast hdu
  have hdv' : (q : ℝ)+2 ≤ G.degree v := by exact_mod_cast hdv
  have hD : (2 : ℝ) ≤ (G.degree u : ℝ)+G.degree v-2*q-2 := by linarith
  have hD' : (G.degree u : ℝ)+G.degree v-2*q-2 ≤ 2*T+4 := by linarith
  have hp := Parameters.high_pair_interval hq hT hr hD hD'
  linarith [hp.2]

 theorem unique_union_row_bound (G : SimpleGraph V) {u v w : V}
    (huv : u ≠ v)
    (hinter : G.neighborFinset u ∩ G.neighborFinset v = {w}) :
    (∑ i ∈ otherVertices u v, unionCount G u v i) + G.degree w ≤
      Statistics.vertexCycleStatistic G u + Statistics.vertexCycleStatistic G v +
        2*(otherVertices u v).card+2 := by
  classical
  have hw : w ∈ G.neighborFinset u ∩ G.neighborFinset v := by rw [hinter]; simp
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
  have hp (i : V) : unionCount G u v i + (if G.Adj i w then 1 else 0) =
      Statistics.codegree G u i + Statistics.codegree G v i := by
    have h := union_add_intersection G u v i
    rw [hinter] at h
    by_cases hi : G.Adj i w <;> simpa [Finset.inter_singleton,hi] using h
  have hs : (∑ i ∈ otherVertices u v, unionCount G u v i) +
      (∑ i ∈ otherVertices u v, if G.Adj i w then 1 else 0) =
      (∑ i ∈ otherVertices u v, Statistics.codegree G u i) +
      (∑ i ∈ otherVertices u v, Statistics.codegree G v i) := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hp i)
  have hind : (∑ i : V, if G.Adj i w then 1 else 0) = G.degree w := by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    have he : Finset.univ.filter (fun i => G.Adj i w) = G.neighborFinset w := by
      ext i
      simp [SimpleGraph.adj_comm]
    rw [he,G.card_neighborFinset_eq_degree]
  have he := sum_other_add (fun i => if G.Adj i w then (1 : ℕ) else 0) huv
  rw [hind] at he
  simp only [hw.1,hw.2,ite_true] at he
  have hu := row_on_other G u v
  have hv := row_on_other G v u
  have hr : otherVertices v u = otherVertices u v := by simp [otherVertices,Finset.pair_comm]
  rw [hr] at hv
  omega

/-- Actual source equation (7), including the discarded unique common neighbor. -/
theorem unique_polynomial_lower (G : SimpleGraph V) (q : ℕ)
    (hq : 1 ≤ q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    {u v w : V} (huv : u ≠ v)
    (hinter : G.neighborFinset u ∩ G.neighborFinset v = {w})
    (hcu : (Statistics.vertexCycleStatistic G u : ℝ) < (q : ℝ)/5)
    (hcv : (Statistics.vertexCycleStatistic G v : ℝ) < (q : ℝ)/5) :
    Parameters.unionLower q ((G.degree u : ℝ)+G.degree v-2*q-2) ≤
      2*(Counting.cycleCount G : ℝ) := by
  classical
  let R := otherVertices u v
  let R' := R.erase w
  have hw : w ∈ G.neighborFinset u ∩ G.neighborFinset v := by rw [hinter]; simp
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
  have hwR : w ∈ R := by simp [R,otherVertices,hw.1.ne.symm,hw.2.ne.symm]
  have hRc : (R.card : ℝ) = (q : ℝ)^2+q-1 := by
    have hn := other_card huv
    rw [hN] at hn
    have hr : (R.card : ℝ)+2 = (q : ℝ)^2+q+1 := by exact_mod_cast hn
    linarith
  have hR'c : (R'.card : ℝ) = (q : ℝ)^2+q-2 := by
    have he := Finset.card_erase_add_one hwR
    have her : (R'.card : ℝ)+1 = R.card := by exact_mod_cast he
    linarith
  have hrow := unique_union_row_bound G huv hinter
  have hrowr : ((∑ i ∈ R, unionCount G u v i : ℕ) : ℝ) + G.degree w ≤
      Statistics.vertexCycleStatistic G u + Statistics.vertexCycleStatistic G v +
        2*(R.card : ℝ)+2 := by exact_mod_cast hrow
  rw [hRc] at hrowr
  have hbal := outside_sum_balance G huv
  have hbalr : ((∑ i ∈ R, outsideCount G u v i : ℕ) : ℝ) +
      (∑ i ∈ R, unionCount G u v i : ℕ) + G.degree u + G.degree v =
        2*(G.edgeFinset.card : ℝ) := by exact_mod_cast hbal
  rw [hE] at hbalr
  have he := Finset.sum_erase_add R (outsideCount G u v) hwR
  have her : ((∑ i ∈ R', outsideCount G u v i : ℕ) : ℝ) + outsideCount G u v w =
      (∑ i ∈ R, outsideCount G u v i : ℕ) := by exact_mod_cast he
  have houtw : outsideCount G u v w ≤ G.degree w := by
    have hh := outside_add_union G u v w
    omega
  have houtwr : (outsideCount G u v w : ℝ) ≤ G.degree w := by exact_mod_cast houtw
  have hlo : ((q : ℝ)^2+q-2)*((q : ℝ)-1)-
      ((G.degree u : ℝ)+G.degree v-2*q-2)-2-2*q/5 ≤
        ((∑ i ∈ R', outsideCount G u v i : ℕ) : ℝ) := by nlinarith
  have ht := DegreeBounds.sum_choose_tangent R' (outsideCount G u v) (q-1)
  rw [hR'c,Nat.cast_choose_two,Nat.cast_sub hq] at ht
  push_cast at ht
  have hb := outside_subset_budget G u v R'
  have hac := complement_card G u v
  have hcodeg : Statistics.codegree G u v = 1 := by simp [Statistics.codegree,hinter]
  rw [hN,hcodeg] at hac
  have hacr : ((Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card : ℝ) =
      (q : ℝ)^2+q+2-G.degree u-G.degree v := by
    have hc : ((Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card : ℝ) +
        G.degree u+G.degree v = (q : ℝ)^2+q+2 := by exact_mod_cast hac
    linarith
  rw [Nat.cast_choose_two,hacr] at hb
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp := mul_nonneg (show 0 ≤ (q : ℝ)-1 by linarith) (sub_nonneg.mpr hlo)
  simp only [Nat.cast_sum] at hp
  unfold Parameters.unionLower
  nlinarith

/-- Source §3 high-pair localization, both disjoint and unique-common-neighbor
cases derived on the same actual host graph. -/
theorem high_pair_opposite (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    {u v : V} (huv : u ≠ v) (hdu : q+2 ≤ G.degree u) (hdv : q+2 ≤ G.degree v)
    (hcu : (Statistics.vertexCycleStatistic G u : ℝ) < (q : ℝ)/5)
    (hcv : (Statistics.vertexCycleStatistic G v : ℝ) < (q : ℝ)/5) :
    2 ≤ Statistics.codegree G u v := by
  classical
  have hnz := high_pair_not_disjoint G q T hq hT hr hN hE hZ huv hdu hdv hcu hcv
  by_contra hn
  have hone : Statistics.codegree G u v = 1 := by omega
  obtain ⟨w,hinter⟩ := Finset.card_eq_one.mp hone
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hlo := unique_polynomial_lower G q hq1 hN hE huv hinter hcu hcv
  have hmu := DegreeBounds.maximum_degree G q T hq hT hr hN hE hZ u
  have hmv := DegreeBounds.maximum_degree G q T hq hT hr hN hE hZ v
  have hdu' : (q : ℝ)+2 ≤ G.degree u := by exact_mod_cast hdu
  have hdv' : (q : ℝ)+2 ≤ G.degree v := by exact_mod_cast hdv
  have hD : (2 : ℝ) ≤ (G.degree u : ℝ)+G.degree v-2*q-2 := by linarith
  have hD' : (G.degree u : ℝ)+G.degree v-2*q-2 ≤ 2*T+4 := by linarith
  have hp := Parameters.high_pair_interval hq hT hr hD hD'
  linarith [hp.1]

end Erdos60.HighPair
