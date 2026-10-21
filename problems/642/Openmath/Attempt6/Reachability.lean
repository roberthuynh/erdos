import Openmath.Attempt6.RobustCore
import Openmath.Attempt6.ReservoirDegree

/-!
Concrete finite reservoir balls, original-edge path extraction, and one-step
random expansion. The radius and ambient logarithmic scale L are separate
parameters. CJMM Lemma 7.2 and Proposition 7.3 are NOT supplied by this module.
The probability estimate below applies to a fixed set and fixed deletion,
not to a set selected after observing the same reservoir sample.
-/
namespace Erdos585.Attempt6.Reachability

open SimpleGraph MeasureTheory Real
open RobustCore OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Literal reservoir ball, defined using actual original-edge walks.
Repeated vertices can be bypassed, as `mem_reservoirBall_path` proves. -/
noncomputable def reservoirBall (G : SimpleGraph V) (U Q : Finset V) (r : ℕ) : Finset V := by
  classical
  exact Q.filter (fun v => ∃ u ∈ U, ∃ w : G.Walk u v,
    w.length ≤ r ∧ ∀ x ∈ w.support, x = u ∨ x ∈ Q)

omit [Fintype V] [DecidableEq V] in
theorem mem_reservoirBall {G : SimpleGraph V} {U Q : Finset V} {r : ℕ} {v : V} :
    v ∈ reservoirBall G U Q r ↔ v ∈ Q ∧ ∃ u ∈ U, ∃ w : G.Walk u v,
      w.length ≤ r ∧ ∀ x ∈ w.support, x = u ∨ x ∈ Q := by
  classical
  simp [reservoirBall]

omit [Fintype V] [DecidableEq V] in
theorem reservoirBall_subset (G : SimpleGraph V) (U Q : Finset V) (r : ℕ) :
    reservoirBall G U Q r ⊆ Q := fun _ h => (mem_reservoirBall.mp h).1


/-- Finite, radius-explicit form of reservoir reachability. Seeds are nonempty;
the empty seed cannot reach more than half of any reservoir. This definition
uses literal graph walks, and radius r is independent of ambient L. -/
noncomputable def ReservoirReachableAt (G : SimpleGraph V) (Q : Finset V)
    (r : ℕ) (lambda : ℝ) : Prop := by
  classical
  exact ∀ U : Finset V, U.Nonempty → ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset →
    (F.card : ℝ) ≤ lambda * U.card →
    (Q.card : ℝ) / 2 < (reservoirBall (G.deleteEdges F) U Q r).card

omit [Fintype V] in
/-- Membership has a genuine simple path witness of no greater length. -/
theorem mem_reservoirBall_path {G : SimpleGraph V} {U Q : Finset V} {r : ℕ} {v : V}
    (hv : v ∈ reservoirBall G U Q r) :
    ∃ u ∈ U, ∃ w : G.Walk u v, w.IsPath ∧ w.length ≤ r ∧
      ∀ x ∈ w.support, x ≠ u → x ∈ Q := by
  obtain ⟨_, u, hu, w, hw, hs⟩ := mem_reservoirBall.mp hv
  refine ⟨u, hu, w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans hw, ?_⟩
  intro x hx hxu
  exact (hs x (w.support_bypass_subset_support hx)).resolve_left hxu

omit [Fintype V] [DecidableEq V] in
theorem reservoirBall_mono_radius (G : SimpleGraph V) (U Q : Finset V)
    {r t : ℕ} (hrt : r ≤ t) : reservoirBall G U Q r ⊆ reservoirBall G U Q t := by
  intro v hv
  obtain ⟨hvQ, u, hu, w, hw, hs⟩ := mem_reservoirBall.mp hv
  exact mem_reservoirBall.mpr ⟨hvQ, u, hu, w, hw.trans hrt, hs⟩

omit [Fintype V] [DecidableEq V] in
theorem reservoirBall_start {G : SimpleGraph V} {U Q : Finset V} {v : V}
    (hvU : v ∈ U) (hvQ : v ∈ Q) (r : ℕ) : v ∈ reservoirBall G U Q r := by
  refine mem_reservoirBall.mpr ⟨hvQ, v, hvU, .nil, Nat.zero_le _, ?_⟩
  intro x hx
  exact Or.inl (by simpa using hx)

omit [Fintype V] [DecidableEq V] in
/-- One actual surviving edge extends a reservoir walk. -/
theorem reservoirBall_extend {G : SimpleGraph V} {U Q : Finset V} {r : ℕ} {v x : V}
    (hv : v ∈ reservoirBall G U Q r) (hvx : G.Adj v x) (hxQ : x ∈ Q) :
    x ∈ reservoirBall G U Q (r + 1) := by
  obtain ⟨_, u, hu, w, hw, hs⟩ := mem_reservoirBall.mp hv
  refine mem_reservoirBall.mpr ⟨hxQ, u, hu, w.concat hvx, ?_, ?_⟩
  · simpa only [Walk.length_concat] using Nat.add_le_add_right hw 1
  · intro y hy
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hs y hy
    · exact Or.inr hxQ

/-- The actual external boundary of the current ball supplies new vertices. -/
theorem externalNeighbors_inter_subset_next (G : SimpleGraph V) (U Q : Finset V) (r : ℕ) :
    externalNeighbors G (reservoirBall G U Q r) ∩ Q ⊆ reservoirBall G U Q (r + 1) := by
  classical
  intro x hx
  obtain ⟨hxN, hxQ⟩ := Finset.mem_inter.mp hx
  obtain ⟨_, v, hv, hvx⟩ := Finset.mem_filter.mp hxN
  exact reservoirBall_extend hv hvx hxQ

/-- Actual growth of full-reservoir balls after an affordable fixed original
edge deletion. L remains independent of the core order. -/
theorem robust_full_ball_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset) (r : ℕ)
    (hnonempty : 1 ≤ (reservoirBall (G.deleteEdges F) U Finset.univ r).card)
    (hsmall : ((reservoirBall (G.deleteEdges F) U Finset.univ r).card : ℝ) ≤
      2 * (Fintype.card V : ℝ) / 3)
    (hF : (F.card : ℝ) ≤ s * (reservoirBall (G.deleteEdges F) U Finset.univ r).card) :
    (1 + epsilon / L ^ 2) * (reservoirBall (G.deleteEdges F) U Finset.univ r).card ≤
      ((reservoirBall (G.deleteEdges F) U Finset.univ (r + 1)).card : ℝ) := by
  classical
  let B := reservoirBall (G.deleteEdges F) U Finset.univ r
  let N := externalNeighbors (G.deleteEdges F) B
  have hexpand := hG B hnonempty hsmall F (by
    simpa only [Finset.subset_iff, SimpleGraph.mem_edgeFinset] using hFG) hF
  have hdisj : Disjoint B N := by
    apply Finset.disjoint_left.mpr
    intro v hv hn
    have hmem : v ∉ B ∧ ∃ u ∈ B, (G.deleteEdges F).Adj u v := by
      simpa only [N, externalNeighbors, Finset.mem_filter, Finset.mem_compl] using hn
    have hnot := hmem.1
    exact hnot hv
  have hsub : B ∪ N ⊆ reservoirBall (G.deleteEdges F) U Finset.univ (r + 1) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact reservoirBall_mono_radius _ _ _ (by omega) hv
    · exact externalNeighbors_inter_subset_next _ U Finset.univ r (by simpa using hv)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hc : (B.card : ℝ) + N.card ≤
      (reservoirBall (G.deleteEdges F) U Finset.univ (r + 1)).card := by exact_mod_cast hcard
  change epsilon * B.card / L ^ 2 ≤ (N.card : ℝ) at hexpand
  change (1 + epsilon / L ^ 2) * B.card ≤ _
  calc
    _ = (B.card : ℝ) + epsilon * B.card / L ^ 2 := by ring
    _ ≤ (B.card : ℝ) + N.card := by linarith
    _ ≤ _ := hc


/-- Iterating genuine robust ball growth forces a ball past two thirds of the
core order once the explicit geometric bound crosses that threshold. No
identification of L with the logarithm of the core order occurs. -/
theorem robust_full_ball_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s)
    (U : Finset V) (hU : U.Nonempty) (F : Finset (Sym2 V))
    (hFG : F ⊆ G.edgeFinset) (hF : (F.card : ℝ) ≤ s * U.card)
    (k : ℕ) (hk : 2 * (Fintype.card V : ℝ) / 3 <
      (1 + epsilon / L ^ 2) ^ k * U.card) :
    2 * (Fintype.card V : ℝ) / 3 <
      ((reservoirBall (G.deleteEdges F) U Finset.univ k).card : ℝ) := by
  classical
  let B := fun i => reservoirBall (G.deleteEdges F) U Finset.univ i
  have hUB (i : ℕ) : U ⊆ B i := fun v hv => reservoirBall_start hv (Finset.mem_univ _) i
  have hcard (i : ℕ) : U.card ≤ (B i).card := Finset.card_le_card (hUB i)
  have hcardR (i : ℕ) : (U.card : ℝ) ≤ (B i).card := by exact_mod_cast hcard i
  have ha : 0 ≤ 1 + epsilon / L ^ 2 := by positivity
  by_contra hn
  have hsmall : ((B k).card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3 := le_of_not_gt hn
  have hgrowth : ∀ i, i ≤ k → (1 + epsilon / L ^ 2) ^ i * U.card ≤ ((B i).card : ℝ) := by
    intro i hi
    induction i with
    | zero => simpa using hcardR 0
    | succ i ih =>
      have hik : i ≤ k := by omega
      have hstep := robust_full_ball_step G L epsilon s hG U F hFG i
        (by change 1 ≤ (B i).card; have := hcard i; have := hU.card_pos; omega)
        ((show ((B i).card : ℝ) ≤ (B k).card from by
          exact_mod_cast Finset.card_le_card (reservoirBall_mono_radius _ _ _ hik)).trans hsmall)
        (hF.trans (mul_le_mul_of_nonneg_left (hcardR i) hs))
      calc
        _ = (1 + epsilon / L ^ 2) * ((1 + epsilon / L ^ 2) ^ i * U.card) := by
          rw [pow_succ]; ring
        _ ≤ (1 + epsilon / L ^ 2) * (B i).card := mul_le_mul_of_nonneg_left (ih hik) ha
        _ ≤ _ := hstep
  exact (not_lt_of_ge ((hgrowth k le_rfl).trans hsmall)) hk


/-- The full vertex set is genuinely reachable at an explicit radius under
the robust certificate. This conclusion does not assert that a small random
reservoir inherits the property. -/
theorem robust_full_reservoir_reachable (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s)
    (k : ℕ) (hk : 2 * (Fintype.card V : ℝ) / 3 < (1 + epsilon / L ^ 2) ^ k) :
    ReservoirReachableAt G Finset.univ k s := by
  classical
  intro U hU F hFG hF
  have hUone : (1 : ℝ) ≤ U.card := by exact_mod_cast (show 1 ≤ U.card from hU.card_pos)
  have ha : 0 ≤ (1 + epsilon / L ^ 2) ^ k := by positivity
  have hkU : 2 * (Fintype.card V : ℝ) / 3 < (1 + epsilon / L ^ 2) ^ k * U.card :=
    hk.trans_le (by nlinarith)
  have hlarge := robust_full_ball_large G L epsilon s hG hepsilon hs U hU F
    (by simpa only [Finset.subset_iff, SimpleGraph.mem_edgeFinset] using hFG) hF k hkU
  simp only [Finset.card_univ]
  nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)]

omit [Fintype V] in
                                                                          
                                                                                
theorem intersecting_balls_path (G : SimpleGraph V) (A B Q : Finset V) (r t : ℕ)
    (hinter : (reservoirBall G A Q r ∩ reservoirBall G B Q t).Nonempty) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ w : G.Walk a b,
      w.IsPath ∧ w.length ≤ r + t ∧
      ∀ x ∈ w.support, x ≠ a → x ≠ b → x ∈ Q := by
  classical
  obtain ⟨v, hv⟩ := hinter
  obtain ⟨_, a, ha, wa, hla, hsa⟩ := mem_reservoirBall.mp (Finset.mem_inter.mp hv).1
  obtain ⟨_, b, hb, wb, hlb, hsb⟩ := mem_reservoirBall.mp (Finset.mem_inter.mp hv).2
  let w := wa.append wb.reverse
  refine ⟨a, ha, b, hb, w.bypass, w.bypass_isPath, ?_, ?_⟩
  · apply w.length_bypass_le_length.trans
    simpa only [w, Walk.length_append, Walk.length_reverse] using Nat.add_le_add hla hlb
  · intro x hx hxa hxb
    have hxw := w.support_bypass_subset_support hx
    rcases (Walk.mem_support_append_iff wa wb.reverse).mp hxw with hxwa | hxwb
    · exact (hsa x hxwa).resolve_left hxa
    · have hxwb' : x ∈ wb.support := by simpa using hxwb
      exact (hsb x hxwb').resolve_left hxb

/-- More-than-half balls intersect by finite counting, so their endpoints
are connected through the actual reservoir. This is the single-pair case,
not the simultaneous-pair conclusion of CJMM Proposition 7.3. -/
theorem majority_balls_path (G : SimpleGraph V) (A B Q : Finset V) (r t : ℕ)
    (hA : (Q.card : ℝ) / 2 < (reservoirBall G A Q r).card)
    (hB : (Q.card : ℝ) / 2 < (reservoirBall G B Q t).card) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ w : G.Walk a b,
      w.IsPath ∧ w.length ≤ r + t ∧
      ∀ x ∈ w.support, x ≠ a → x ≠ b → x ∈ Q := by
  apply intersecting_balls_path
  by_contra hn
  have he : reservoirBall G A Q r ∩ reservoirBall G B Q t = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hn
  have hc := Finset.card_union_add_card_inter (reservoirBall G A Q r) (reservoirBall G B Q t)
  rw [he, Finset.card_empty, Nat.add_zero] at hc
  have hsub : reservoirBall G A Q r ∪ reservoirBall G B Q t ⊆ Q :=
    Finset.union_subset (reservoirBall_subset _ _ _ _) (reservoirBall_subset _ _ _ _)
  have hle := Finset.card_le_card hsub
  have hsum : (reservoirBall G A Q r).card + (reservoirBall G B Q t).card ≤ Q.card := by omega
  have hsumR : ((reservoirBall G A Q r).card : ℝ) + (reservoirBall G B Q t).card ≤ Q.card := by
    exact_mod_cast hsum
  linarith


/-- A concrete deterministic supplier: sufficiently grown robust balls give
an actual short simple path after any affordable original-edge deletion.
This uses the full core as reservoir, not a sampled small reservoir. -/
theorem robust_deleted_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset) (hF : (F.card : ℝ) ≤ s)
    (k : ℕ) (hk : 2 * (Fintype.card V : ℝ) / 3 < (1 + epsilon / L ^ 2) ^ k)
    (x y : V) : ∃ w : (G.deleteEdges F).Walk x y, w.IsPath ∧ w.length ≤ 2 * k := by
  classical
  have hx := robust_full_ball_large G L epsilon s hG hepsilon hs {x}
    (Finset.singleton_nonempty _) F hFG (by simpa using hF) k (by simpa using hk)
  have hy := robust_full_ball_large G L epsilon s hG hepsilon hs {y}
    (Finset.singleton_nonempty _) F hFG (by simpa using hF) k (by simpa using hk)
  have hmajorx : ((Finset.univ : Finset V).card : ℝ) / 2 <
      (reservoirBall (G.deleteEdges F) {x} Finset.univ k).card := by
    simp only [Finset.card_univ]
    nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)]
  have hmajory : ((Finset.univ : Finset V).card : ℝ) / 2 <
      (reservoirBall (G.deleteEdges F) {y} Finset.univ k).card := by
    simp only [Finset.card_univ]
    nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)]
  obtain ⟨a, ha, b, hb, w, hw, hl, _⟩ :=
    majority_balls_path (G.deleteEdges F) {x} {y} Finset.univ k k hmajorx hmajory
  have hax : a = x := Finset.mem_singleton.mp ha
  have hby : b = y := Finset.mem_singleton.mp hb
  subst a
  subst b
  exact ⟨w, hw, by omega⟩

/-- Every sampled surviving boundary vertex is genuinely reached in one edge,
including when the starting vertex lies outside the sample. -/
theorem externalNeighbors_inter_subset_ball_one (G : SimpleGraph V) (U Q : Finset V) :
    externalNeighbors G U ∩ Q ⊆ reservoirBall G U Q 1 := by
  classical
  intro v hv
  obtain ⟨hvN, hvQ⟩ := Finset.mem_inter.mp hv
  have hvN' : v ∉ U ∧ ∃ u ∈ U, G.Adj u v := by
    simpa only [externalNeighbors, Finset.mem_filter, Finset.mem_compl] using hvN
  obtain ⟨u, hu, huv⟩ := hvN'.2
  refine mem_reservoirBall.mpr ⟨hvQ, u, hu, .cons huv .nil, by simp, ?_⟩
  intro x hx
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hvQ

/-- Fixed-set sampling consequence of robust expansion. This is not the
adaptive, uniform random reachability theorem. -/
theorem sampled_robust_boundary_lower_tail (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card) (p : unitInterval) :
    (sampleMeasure V p).real
      {ω | ((externalNeighbors (G.deleteEdges F) U ∩ sampleVertices ω).card : ℝ) ≤
        (p : ℝ) * (epsilon * U.card / L ^ 2) / 2} ≤
      exp (-(p : ℝ) * (epsilon * U.card / L ^ 2) / 8) := by
  let N := externalNeighbors (G.deleteEdges F) U
  have hN := hG U hU hsmall F (by
    simpa only [Finset.subset_iff, SimpleGraph.mem_edgeFinset] using hFG) hF
  have hp := p.property.1
  calc
    _ ≤ (sampleMeasure V p).real
        {ω | ((N ∩ sampleVertices ω).card : ℝ) ≤ (p : ℝ) * N.card / 2} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      exact hω.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hN hp) (by norm_num))
    _ ≤ exp (-(p : ℝ) * N.card / 8) := sample_card_lower_tail p N
    _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hN hp])

/-- A genuine one-step random-reservoir reachability bound, derived from
original edges and robust expansion. It applies to fixed U and F only. -/
theorem sampled_ball_one_lower_tail (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card) (p : unitInterval) :
    (sampleMeasure V p).real
      {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) 1).card : ℝ) ≤
        (p : ℝ) * (epsilon * U.card / L ^ 2) / 2} ≤
      exp (-(p : ℝ) * (epsilon * U.card / L ^ 2) / 8) := by
  apply le_trans _ (sampled_robust_boundary_lower_tail G L epsilon s hG U hU hsmall F hFG hF p)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  have hc := Finset.card_le_card (externalNeighbors_inter_subset_ball_one
    (G.deleteEdges F) U (sampleVertices ω))
  have hcR : ((externalNeighbors (G.deleteEdges F) U ∩ sampleVertices ω).card : ℝ) ≤
      (reservoirBall (G.deleteEdges F) U (sampleVertices ω) 1).card := by exact_mod_cast hc
  exact hcR.trans hω

end Erdos585.Attempt6.Reachability
