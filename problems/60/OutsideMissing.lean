import LocalizedPaths
import PolarityAbsoluteBound

namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [DecidableEq P]
  [Configuration.ProjectivePlane P L] [Finite L]

/-- Outside a core that retains every host adjacency in the polarity, a
vertex of host degree at least q has at most one missing polarity neighbor.
If it has any, it is a nonabsolute host degree-q vertex. -/
theorem Polarity.outside_missing_neighbor_control
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P)
    (hcontain : ∀ v ∉ S, ∀ w, G.Adj v w → π.graph.Adj v w)
    (hmin : ∀ v ∉ S, Configuration.ProjectivePlane.order P L ≤ G.degree v)
    {v : P} (hv : v ∉ S) :
    (π.graph.neighborFinset v \ G.neighborFinset v).card ≤ 1 ∧
    (∀ w ∈ π.graph.neighborFinset v \ G.neighborFinset v,
      G.degree v ≤ Configuration.ProjectivePlane.order P L ∧ ¬π.Absolute v) := by
  classical
  have hs : G.neighborFinset v ⊆ π.graph.neighborFinset v := by
    intro w hw
    simpa only [SimpleGraph.mem_neighborFinset] using
      hcontain v hv w (by simpa only [SimpleGraph.mem_neighborFinset] using hw)
  have hsum := Finset.card_sdiff_add_card_eq_card hs
  rw [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have hd := π.degree_eq_order_or_succ v
  have hm := hmin v hv
  refine ⟨by rcases hd with hd | hd <;> omega, ?_⟩
  intro w hw
  have hp : 0 < (π.graph.neighborFinset v \ G.neighborFinset v).card :=
    Finset.card_pos.mpr ⟨w,hw⟩
  refine ⟨by rcases hd with hd | hd <;> omega, ?_⟩
  intro ha
  have hdq := (π.degree_eq_order_iff_absolute v).mpr ha
  omega

theorem Polarity.outside_missing_le_outside_low_nonabsolute
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P)
    (hcontain : ∀ v ∉ S, ∀ w, G.Adj v w → π.graph.Adj v w)
    (hmin : ∀ v ∉ S, Configuration.ProjectivePlane.order P L ≤ G.degree v) :
    (outsideMissing G π.graph S).card ≤
      (Finset.univ.filter (fun v => v ∉ S ∧
        G.degree v ≤ Configuration.ProjectivePlane.order P L ∧ ¬π.Absolute v)).card := by
  classical
  let D := outsideMissing G π.graph S
  let U := Finset.univ.filter (fun v => v ∉ S ∧
    G.degree v ≤ Configuration.ProjectivePlane.order P L ∧ ¬π.Absolute v)
  have hex : ∀ e : D, ∃ v : U, v.val ∈ e.val := by
    intro e
    have he := Finset.mem_filter.mp e.property
    obtain ⟨v,hve,hvS⟩ := Finset.not_subset.mp he.2
    have hvE : v ∈ e.val := Sym2.mem_toFinset.mp hve
    obtain ⟨w,hew⟩ := Sym2.mem_iff_exists.mp hvE
    have hQ : π.graph.Adj v w := by
      have hh := (Finset.mem_sdiff.mp he.1).1
      rw [hew] at hh
      simpa using hh
    have hG : ¬G.Adj v w := by
      have hh := (Finset.mem_sdiff.mp he.1).2
      rw [hew] at hh
      simpa using hh
    have hw : w ∈ π.graph.neighborFinset v \ G.neighborFinset v := by
      simpa only [Finset.mem_sdiff,SimpleGraph.mem_neighborFinset] using And.intro hQ hG
    have hc := (π.outside_missing_neighbor_control G S hcontain hmin hvS).2 w hw
    exact ⟨⟨v,by simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hvS,hc⟩⟩,hvE⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro e r h
    apply Subtype.ext
    have hvS : (f e).val ∉ S := (Finset.mem_filter.mp (f e).property).2.1
    have hr : (f e).val ∈ r.val := by rw [h]; exact hf r
    obtain ⟨w,hew⟩ := Sym2.mem_iff_exists.mp (hf e)
    obtain ⟨z,hrz⟩ := Sym2.mem_iff_exists.mp hr
    have hw : w ∈ π.graph.neighborFinset (f e).val \ G.neighborFinset (f e).val := by
      have hh := (Finset.mem_filter.mp e.property).1
      rw [hew] at hh
      simpa only [Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hh
    have hz : z ∈ π.graph.neighborFinset (f e).val \ G.neighborFinset (f e).val := by
      have hh := (Finset.mem_filter.mp r.property).1
      rw [hrz] at hh
      simpa only [Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hh
    have hc := (π.outside_missing_neighbor_control G S hcontain hmin hvS).1
    have hwz := Finset.card_le_one.mp hc w hw z hz
    exact hew.trans ((congrArg (fun z => s((f e).val,z)) hwz).trans hrz.symm)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Exact support accounting: outside missing edges plus q+1 are paid by
the actual deficient-vertex set plus the core. -/
theorem Polarity.outside_missing_add_order_le_deficient_add_core
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P)
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hcontain : ∀ v ∉ S, ∀ w, G.Adj v w → π.graph.Adj v w)
    (hmin : ∀ v ∉ S, Configuration.ProjectivePlane.order P L ≤ G.degree v) :
    (outsideMissing G π.graph S).card + (Configuration.ProjectivePlane.order P L + 1) ≤
      (Finset.univ.filter (fun v : P => G.degree v ≤ Configuration.ProjectivePlane.order P L)).card +
        S.card := by
  classical
  let U := Finset.univ.filter (fun v => v ∉ S ∧
    G.degree v ≤ Configuration.ProjectivePlane.order P L ∧ ¬π.Absolute v)
  let B := Finset.univ.filter (fun v => v ∉ S ∧ π.Absolute v)
  let A := Finset.univ.filter π.Absolute
  let D := Finset.univ.filter (fun v : P => G.degree v ≤ Configuration.ProjectivePlane.order P L)
  have hU := π.outside_missing_le_outside_low_nonabsolute G S hcontain hmin
  change (outsideMissing G π.graph S).card ≤ U.card at hU
  have hdis : Disjoint U B := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvB
    exact (Finset.mem_filter.mp hvU).2.2.2 (Finset.mem_filter.mp hvB).2.2
  have hsub : U ∪ B ⊆ D := by
    intro v hv
    simp only [D,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_filter.mp hv).2.2.1
    · have hv' := (Finset.mem_filter.mp hv).2
      have hs : G.neighborFinset v ⊆ π.graph.neighborFinset v := by
        intro w hw
        simpa only [SimpleGraph.mem_neighborFinset] using hcontain v hv'.1 w
          (by simpa only [SimpleGraph.mem_neighborFinset] using hw)
      have hc := Finset.card_le_card hs
      rw [SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree] at hc
      rwa [(π.degree_eq_order_iff_absolute v).mpr hv'.2] at hc
  have hUB : U.card + B.card ≤ D.card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card hsub
  have hAsub : A ⊆ B ∪ S := by
    intro v hv
    by_cases hvS : v ∈ S
    · exact Finset.mem_union.mpr (Or.inr hvS)
    · exact Finset.mem_union.mpr (Or.inl (by
        simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨hvS,(Finset.mem_filter.mp hv).2⟩))
  have hAc := Finset.card_le_card hAsub
  have hBS := Finset.card_union_le B S
  have ha : Configuration.ProjectivePlane.order P L + 1 ≤ A.card := by
    simpa only [A,Nat.card_eq_fintype_card,Fintype.card_subtype] using π.absolute_count_lower heven
  change (outsideMissing G π.graph S).card + (Configuration.ProjectivePlane.order P L + 1) ≤
    D.card + S.card
  omega

theorem Polarity.outside_missing_count_bound
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P) (n : ℕ)
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hcontain : ∀ v ∉ S, ∀ w, G.Adj v w → π.graph.Adj v w)
    (hmin : ∀ v ∉ S, Configuration.ProjectivePlane.order P L ≤ G.degree v)
    (hdef : (Finset.univ.filter (fun v : P => G.degree v ≤ Configuration.ProjectivePlane.order P L)).card ≤
      Configuration.ProjectivePlane.order P L - 1 + n) :
    (outsideMissing G π.graph S).card ≤ S.card + n := by
  have h := π.outside_missing_add_order_le_deficient_add_core G S heven hcontain hmin
  omega

theorem Polarity.outside_missing_real_bound
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P) (T : ℝ)
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hcontain : ∀ v ∉ S, ∀ w, G.Adj v w → π.graph.Adj v w)
    (hmin : ∀ v ∉ S, Configuration.ProjectivePlane.order P L ≤ G.degree v)
    (hdef : ((Finset.univ.filter (fun v : P => G.degree v ≤
      Configuration.ProjectivePlane.order P L)).card : ℝ) ≤
        (Configuration.ProjectivePlane.order P L : ℝ) - 1 + 20 * T) :
    ((outsideMissing G π.graph S).card : ℝ) ≤ (S.card : ℝ) + 20 * T := by
  have h := π.outside_missing_add_order_le_deficient_add_core G S heven hcontain hmin
  have hr : ((outsideMissing G π.graph S).card : ℝ) +
      ((Configuration.ProjectivePlane.order P L : ℝ) + 1) ≤
      ((Finset.univ.filter (fun v : P => G.degree v ≤
        Configuration.ProjectivePlane.order P L)).card : ℝ) + (S.card : ℝ) := by exact_mod_cast h
  linarith

/-- First-excess sparse-edit conclusion from actual core containment and the
actual degree/deficient-vertex support controls. The plane/core producer is
explicit; neither outside-missing accounting nor retained paths are assumed. -/
theorem Polarity.first_excess_edit_bound
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P) (T : ℝ)
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hcontain : ∀ v ∉ S, ∀ w, G.Adj v w → π.graph.Adj v w)
    (hmin : ∀ v ∉ S, Configuration.ProjectivePlane.order P L ≤ G.degree v)
    (hdef : ((Finset.univ.filter (fun v : P => G.degree v ≤
      Configuration.ProjectivePlane.order P L)).card : ℝ) ≤
        (Configuration.ProjectivePlane.order P L : ℝ) - 1 + 20 * T)
    (hcore : (S.card : ℝ) ≤ 292 * T)
    (hq : (10^16 : ℝ) ≤ (Configuration.ProjectivePlane.order P L : ℝ))
    (_hT : 1 ≤ T) (hrange : T ≤ (Configuration.ProjectivePlane.order P L : ℝ) / 10^8)
    (hZ : (Counting.cycleCount G : ℝ) < T * (Configuration.ProjectivePlane.order P L : ℝ)) :
    ((G.edgeFinset \ π.graph.edgeFinset).card : ℝ) < 2 * T := by
  classical
  let q := Configuration.ProjectivePlane.order P L
  let j := (G.edgeFinset \ π.graph.edgeFinset).card
  let d := (outsideMissing G π.graph S).card
  have hd : (d : ℝ) ≤ (S.card : ℝ) + 20 * T :=
    π.outside_missing_real_bound G S T heven hcontain hmin hdef
  have hqpos : (0 : ℝ) < q := by dsimp [q]; linarith
  have hden : (q : ℝ) - 1 - 2 * (S.card : ℝ) - (d : ℝ) > (q : ℝ) / 2 := by
    dsimp [q] at *
    linarith
  have hsmall : 1 + 2 * S.card + d ≤ q := by
    have hsmallR : (1 : ℝ) + 2 * (S.card : ℝ) + (d : ℝ) ≤ (q : ℝ) := by linarith
    exact_mod_cast hsmallR
  have hk : q - 1 - 2 * S.card - d = q - (1 + 2 * S.card + d) := by omega
  have hkR : ((q - 1 - 2 * S.card - d : ℕ) : ℝ) =
      (q : ℝ) - 1 - 2 * (S.card : ℝ) - (d : ℝ) := by
    rw [hk,Nat.cast_sub hsmall]
    push_cast
    ring
  have hc := π.localized_cycle_lower G S
  have hcR : (j : ℝ) * ((q - 1 - 2 * S.card - d : ℕ) : ℝ) ≤
      (Counting.cycleCount G : ℝ) := by exact_mod_cast hc
  rw [hkR] at hcR
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hhalf := (mul_le_mul_of_nonneg_left (le_of_lt hden) hj0).trans hcR
  have hjq : (j : ℝ) * (q : ℝ) < (2 * T) * (q : ℝ) := by
    change (Counting.cycleCount G : ℝ) < T * (q : ℝ) at hZ
    nlinarith
  exact (mul_lt_mul_iff_left₀ hqpos).mp hjq

#print axioms Polarity.outside_missing_neighbor_control
#print axioms Polarity.outside_missing_le_outside_low_nonabsolute
#print axioms Polarity.outside_missing_add_order_le_deficient_add_core
#print axioms Polarity.outside_missing_count_bound
#print axioms Polarity.outside_missing_real_bound
#print axioms Polarity.first_excess_edit_bound

end Erdos60.Geometry
