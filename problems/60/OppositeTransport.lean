import SurplusRows

namespace Erdos60.Transport
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def zeroCommonVertices (G : SimpleGraph V) (u : V) : Finset V :=
  Finset.univ.filter fun z => Statistics.codegree G u z = 0
noncomputable def cleanNeighbors (G : SimpleGraph V) (v : V) : Finset V :=
  (G.neighborFinset v).filter fun x => Statistics.vertexCycleStatistic G x = 0
noncomputable def neighborCycleCount (G : SimpleGraph V) (v : V) : ℕ :=
  ((G.neighborFinset v).filter fun x => 0 < Statistics.vertexCycleStatistic G x).card

 theorem clean_codegree_le_one (G : SimpleGraph V) {x y : V}
    (hz : Statistics.vertexCycleStatistic G x = 0) (hxy : x ≠ y) :
    Statistics.codegree G x y ≤ 1 := by
  have hl := Finset.single_le_sum (f := fun y => (Statistics.codegree G x y).choose 2)
    (fun y _ => Nat.zero_le _) (by simp [hxy.symm] : y ∈ Finset.univ.erase x)
  change (Statistics.codegree G x y).choose 2 ≤ Statistics.vertexCycleStatistic G x at hl
  have hc : (Statistics.codegree G x y).choose 2 = 0 := by omega
  have hn := Nat.choose_eq_zero_iff.mp hc
  omega

 theorem clean_neighbor_avoids_origin (G : SimpleGraph V) {u v x : V}
    (huv : u ≠ v) (hopp : 2 ≤ Statistics.codegree G u v)
    (hxv : G.Adj x v) (hz : Statistics.vertexCycleStatistic G x = 0) :
    x ≠ u ∧ ¬G.Adj u x := by
  classical
  have hxu : x ≠ u := by
    intro he
    subst x
    have hh := clean_codegree_le_one G hz huv
    omega
  refine ⟨hxu,?_⟩
  intro hux
  have hcard : (G.neighborFinset u ∩ G.neighborFinset v).card ≥ 2 := hopp
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hcard
  have hxa : a ≠ x ∨ b ≠ x := by
    by_contra hn
    simp only [not_or,not_not] at hn
    exact hab (hn.1.trans hn.2.symm)
  rcases hxa with hax | hbx
  · have hau : G.Adj a u := ((G.mem_neighborFinset u a).mp (Finset.mem_inter.mp ha).1).symm
    have hav : G.Adj a v := ((G.mem_neighborFinset v a).mp (Finset.mem_inter.mp ha).2).symm
    exact huv (Statistics.common_neighbor_unique_of_cycle_statistic_zero G hz hax.symm hux.symm hau hxv hav)
  · have hbu : G.Adj b u := ((G.mem_neighborFinset u b).mp (Finset.mem_inter.mp hb).1).symm
    have hbv : G.Adj b v := ((G.mem_neighborFinset v b).mp (Finset.mem_inter.mp hb).2).symm
    exact huv (Statistics.common_neighbor_unique_of_cycle_statistic_zero G hz hbx.symm hux.symm hbu hxv hbv)

 theorem neighbor_codegree_exchange (G : SimpleGraph V) (u x : V) :
    (∑ z ∈ G.neighborFinset x, Statistics.codegree G u z) =
      ∑ y ∈ G.neighborFinset u, Statistics.codegree G x y := by
  simp_rw [Statistics.codegree_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [SimpleGraph.adj_comm]

/-- A clean nondeficient neighbor must contribute at least a+1 actual points
with no common neighbor with u. This is the source N3 pigeonhole argument. -/
theorem clean_neighbor_zeroCommon_lower (G : SimpleGraph V) (q a : ℕ)
    {u v x : V} (huv : u ≠ v) (hopp : 2 ≤ Statistics.codegree G u v)
    (hdu : G.degree u+a=q+1) (hdx : q+1 ≤ G.degree x)
    (hxv : G.Adj x v) (hz : Statistics.vertexCycleStatistic G x = 0) :
    a+1 ≤ (G.neighborFinset x ∩ zeroCommonVertices G u).card := by
  classical
  have hx := clean_neighbor_avoids_origin G huv hopp hxv hz
  have hup : (∑ z ∈ G.neighborFinset x, Statistics.codegree G u z) ≤ G.degree u := by
    rw [neighbor_codegree_exchange]
    calc
      _ ≤ ∑ y ∈ G.neighborFinset u, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro y hy
        have hxy : x ≠ y := by
          intro h
          subst y
          exact hx.2 ((G.mem_neighborFinset u x).mp hy)
        exact clean_codegree_le_one G hz hxy
      _ = _ := by simp
  have hpoint (z : V) : (if z ∉ zeroCommonVertices G u then 1 else 0) +
      (if z = v then 1 else 0) ≤ Statistics.codegree G u z := by
    by_cases he : z = v
    · subst z
      have hv : v ∉ zeroCommonVertices G u := by simp [zeroCommonVertices]; omega
      simp only [hv,not_false_eq_true,ite_true]
      omega
    · by_cases hzero : z ∈ zeroCommonVertices G u
      · simp only [hzero,not_true_eq_false,he,ite_false,add_zero]
        omega
      · have hp : Statistics.codegree G u z ≠ 0 := by
          simpa [zeroCommonVertices] using hzero
        simp only [hzero,not_false_eq_true,he,ite_true,ite_false,add_zero]
        omega
  have hlo := Finset.sum_le_sum (s := G.neighborFinset x) (fun z _ => hpoint z)
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id] at hlo
  have hf : (G.neighborFinset x).filter (fun z => z ∉ zeroCommonVertices G u) =
      G.neighborFinset x \ zeroCommonVertices G u := by ext z; simp
  have hvf : (G.neighborFinset x).filter (fun z => z = v) = {v} := by
    ext z
    simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    constructor
    · exact And.right
    · intro h; subst z; exact ⟨hxv,rfl⟩
  rw [hf,hvf] at hlo
  simp only [Finset.card_singleton] at hlo
  have hp := Finset.card_sdiff_add_card_inter (G.neighborFinset x) (zeroCommonVertices G u)
  rw [G.card_neighborFinset_eq_degree] at hp
  omega

noncomputable def cleanNondefNeighbors (G : SimpleGraph V) (q : ℕ) (v : V) : Finset V :=
  cleanNeighbors G v \ SurplusRows.deficientVertices G q

 theorem clean_zeroCommon_disjoint (G : SimpleGraph V) {u v x y : V}
    (hopp : 2 ≤ Statistics.codegree G u v) (hxy : x ≠ y)
    (hxv : G.Adj x v) (hyv : G.Adj y v)
    (hxz : Statistics.vertexCycleStatistic G x = 0) :
    Disjoint (G.neighborFinset x ∩ zeroCommonVertices G u)
      (G.neighborFinset y ∩ zeroCommonVertices G u) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz1 hz2
  have hxz' := (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hz1).1
  have hyz' := (G.mem_neighborFinset y z).mp (Finset.mem_inter.mp hz2).1
  have he : v = z := Statistics.common_neighbor_unique_of_cycle_statistic_zero G hxz hxy hxv hyv hxz' hyz'
  have hz0 := (Finset.mem_inter.mp hz1).2
  simp only [zeroCommonVertices,Finset.mem_filter,Finset.mem_univ,true_and] at hz0
  rw [← he] at hz0
  omega

 theorem cleanNondef_transport_count (G : SimpleGraph V) (q a : ℕ)
    {u v : V} (huv : u ≠ v) (hopp : 2 ≤ Statistics.codegree G u v)
    (hdu : G.degree u+a=q+1) :
    (a+1)*(cleanNondefNeighbors G q v).card ≤ (zeroCommonVertices G u).card := by
  classical
  let C := cleanNondefNeighbors G q v
  let F := fun x => G.neighborFinset x ∩ zeroCommonVertices G u
  have hsub : C.biUnion F ⊆ zeroCommonVertices G u := by
    intro z hz
    obtain ⟨x,hx,hz⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_inter.mp hz).2
  have hdis : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (F x) (F y) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1
    have hy' := Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1
    exact clean_zeroCommon_disjoint G hopp hxy
      ((G.mem_neighborFinset v x).mp hx'.1).symm
      ((G.mem_neighborFinset v y).mp hy'.1).symm hx'.2
  have hlow : ∀ x ∈ C, a+1 ≤ (F x).card := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hclean := Finset.mem_filter.mp hx'.1
    have hd : q+1 ≤ G.degree x := by
      have hf := hx'.2
      simp only [SurplusRows.deficientVertices,Finset.mem_filter,Finset.mem_univ,true_and] at hf
      unfold Statistics.degreeDeficiency at hf
      omega
    exact clean_neighbor_zeroCommon_lower G q a huv hopp hdu hd
      ((G.mem_neighborFinset v x).mp hclean.1).symm hclean.2
  calc
    _ = ∑ x ∈ C, (a+1) := by simp [Nat.mul_comm,C]
    _ ≤ ∑ x ∈ C, (F x).card := Finset.sum_le_sum hlow
    _ = (C.biUnion F).card := (Finset.card_biUnion hdis).symm
    _ ≤ _ := Finset.card_le_card hsub

 theorem clean_neighbors_decompose (G : SimpleGraph V) (v : V) :
    (cleanNeighbors G v).card + neighborCycleCount G v = G.degree v := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v)
    (p := fun x => Statistics.vertexCycleStatistic G x = 0)
  simpa [cleanNeighbors,neighborCycleCount,Nat.pos_iff_ne_zero] using h

/-- Actual transport counting before the parameter estimates, including the
shared zero-common-neighbor support and pairwise disjointness. -/
theorem transport_count (G : SimpleGraph V) (q a : ℕ)
    {u v : V} (huv : u ≠ v) (hopp : 2 ≤ Statistics.codegree G u v)
    (hdu : G.degree u+a=q+1) :
    (a+1)*G.degree v ≤ (a+1)*neighborCycleCount G v +
      (a+1)*(G.neighborFinset v ∩ SurplusRows.deficientVertices G q).card +
        (zeroCommonVertices G u).card := by
  classical
  have hl := cleanNondef_transport_count G q a huv hopp hdu
  have hd := Finset.card_sdiff_add_card_inter (cleanNeighbors G v) (SurplusRows.deficientVertices G q)
  have hs : (cleanNeighbors G v ∩ SurplusRows.deficientVertices G q).card ≤
      (G.neighborFinset v ∩ SurplusRows.deficientVertices G q).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).1,(Finset.mem_inter.mp hx).2⟩
  have hclean : (cleanNeighbors G v).card ≤
      (cleanNondefNeighbors G q v).card +
        (G.neighborFinset v ∩ SurplusRows.deficientVertices G q).card := by
    change (cleanNeighbors G v).card ≤
      (cleanNeighbors G v \ SurplusRows.deficientVertices G q).card + _
    omega
  have hm := Nat.mul_le_mul_left (a+1) hclean
  have hpart := clean_neighbors_decompose G v
  nlinarith

 theorem zeroCommon_card (G : SimpleGraph V) {u : V} (hdu : 0 < G.degree u) :
    (zeroCommonVertices G u).card = Statistics.zeroCodegreeCount G u := by
  classical
  have hself : Statistics.codegree G u u ≠ 0 := by
    simpa [Statistics.codegree,G.card_neighborFinset_eq_degree] using Nat.ne_of_gt hdu
  unfold zeroCommonVertices Statistics.zeroCodegreeCount
  congr 1
  ext z
  by_cases hzu : z = u
  · subst z; simp [hself]
  · simp [hzu]

/-- Source transport equations (19) and (20), using actual small deficient
neighborhoods at u and v. These premises are supplied by the actual dichotomy. -/
theorem opposite_transport_density (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    {u v : V} (huv : u ≠ v) (hopp : 2 ≤ Statistics.codegree G u v)
    (hdu : G.degree u=q ∨ G.degree u=q+1) (hdv : q ≤ G.degree v)
    (hcu : (Statistics.vertexCycleStatistic G u : ℝ) ≤ (q : ℝ)*4/5)
    (hNu : ((G.neighborFinset u ∩ SurplusRows.deficientVertices G q).card : ℝ) ≤ 50*T)
    (hNv : ((G.neighborFinset v ∩ SurplusRows.deficientVertices G q).card : ℝ) ≤ 50*T) :
    (Statistics.vertexCycleStatistic G u : ℝ)+2*neighborCycleCount G v ≥ (q : ℝ)-175*T ∧
      (q : ℝ)/20 ≤ neighborCycleCount G v := by
  let a := Statistics.degreeDeficiency G q u
  have ha : a ≤ 1 := by unfold a Statistics.degreeDeficiency; rcases hdu with h | h <;> omega
  have hda : G.degree u+a=q+1 := by
    unfold a Statistics.degreeDeficiency
    rcases hdu with h | h <;> omega
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hdu0 : 0 < G.degree u := by rcases hdu with h | h <;> omega
  have hcount := transport_count G q a huv hopp hda
  have hcr : ((a : ℝ)+1)*G.degree v ≤ ((a : ℝ)+1)*neighborCycleCount G v +
      ((a : ℝ)+1)*(G.neighborFinset v ∩ SurplusRows.deficientVertices G q).card +
        (zeroCommonVertices G u).card := by exact_mod_cast hcount
  have hf := SurplusRows.deficiencyOn_le_support_add_excess G q (G.neighborFinset u)
  have hfr : (Statistics.deficiencyOn G q (G.neighborFinset u) : ℝ) ≤
      (G.neighborFinset u ∩ SurplusRows.deficientVertices G q).card +
        (SurplusRows.excessDeficiency G q : ℝ) := by exact_mod_cast hf
  have hbounds := SurplusRows.localized_deficit_bounds G q T hq hT hr heven hN hE hZ
  have hfu : (Statistics.deficiencyOn G q (G.neighborFinset u) : ℝ) ≤ 75*T := by
    linarith [hbounds.2.2.1]
  have hrow := Statistics.vertex_cycle_deficiency_lower G q hN u
  rw [← zeroCommon_card G hdu0] at hrow
  have hdr : (G.degree u : ℝ)+a=(q : ℝ)+1 := by exact_mod_cast hda
  have hmul := congrArg (fun z : ℝ => z*q) hdr
  have hVu : ((zeroCommonVertices G u).card : ℝ) ≤
      Statistics.vertexCycleStatistic G u+(a : ℝ)*q+75*T := by nlinarith
  have har : (a : ℝ) ≤ 1 := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hv0 : (0 : ℝ) ≤ neighborCycleCount G v := Nat.cast_nonneg _
  have hdvr : (q : ℝ) ≤ G.degree v := by exact_mod_cast hdv
  have hmNv := mul_le_mul_of_nonneg_left hNv (show (0 : ℝ) ≤ (a : ℝ)+1 by positivity)
  have hmDeg := mul_le_mul_of_nonneg_left hdvr (show (0 : ℝ) ≤ (a : ℝ)+1 by positivity)
  have hmT := mul_le_mul_of_nonneg_right har (show (0 : ℝ) ≤ 50*T by linarith)
  have hmC := mul_le_mul_of_nonneg_right har hv0
  have htransport : (q : ℝ)-175*T ≤
      (Statistics.vertexCycleStatistic G u : ℝ)+2*neighborCycleCount G v := by nlinarith
  refine ⟨htransport,?_⟩
  have hqT : 1750*T ≤ (q : ℝ) := by linarith
  exact Parameters.transport_parameter hq hr (by nlinarith : (Statistics.vertexCycleStatistic G u : ℝ) ≤ 4*(q : ℝ)/5) htransport

end Erdos60.Transport
