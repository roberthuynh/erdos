import Openmath.Attempt6.Reachability

/-!
Deterministic prescribed-pair routing from actual reservoir-ball expansion.
Proof adapted mathematically from Bucić--Montgomery, arXiv:2211.07689,
Proposition 8 (arXiv v2, 2023-11-14, public PDF page 8), cited as CJMM Proposition 7.3.
The binary partition implementation uses an explicit integer radius before
any conversion to a base-two logarithm. No random-reservoir supplier is assumed.
-/
namespace Erdos585.Attempt6.PairedRouting

open SimpleGraph Reachability
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ball_mono_source (G : SimpleGraph V) {A B : Finset V} (Q : Finset V) (r : ℕ)
    (hAB : A ⊆ B) : reservoirBall G A Q r ⊆ reservoirBall G B Q r := by
  intro v hv
  obtain ⟨hvQ, u, hu, w, hw, hs⟩ := mem_reservoirBall.mp hv
  exact mem_reservoirBall.mpr ⟨hvQ, u, hAB hu, w, hw, hs⟩

theorem ball_union (G : SimpleGraph V) (A B Q : Finset V) (r : ℕ) :
    reservoirBall G (A ∪ B) Q r = reservoirBall G A Q r ∪ reservoirBall G B Q r := by
  classical
  ext v
  simp only [mem_reservoirBall, Finset.mem_union]
  constructor
  · rintro ⟨hvQ, u, hu, w, hw, hs⟩
    rcases hu with hu | hu
    · exact Or.inl ⟨hvQ, u, hu, w, hw, hs⟩
    · exact Or.inr ⟨hvQ, u, hu, w, hw, hs⟩
  · rintro (⟨hvQ, u, hu, w, hw, hs⟩ | ⟨hvQ, u, hu, w, hw, hs⟩)
    · exact ⟨hvQ, u, Or.inl hu, w, hw, hs⟩
    · exact ⟨hvQ, u, Or.inr hu, w, hw, hs⟩

theorem ball_compose (G : SimpleGraph V) (A Q : Finset V) (r s : ℕ) :
    reservoirBall G (reservoirBall G A Q r) Q s ⊆ reservoirBall G A Q (r + s) := by
  intro v hv
  obtain ⟨hvQ, x, hx, w, hw, hws⟩ := mem_reservoirBall.mp hv
  obtain ⟨hxQ, a, ha, p, hp, hps⟩ := mem_reservoirBall.mp hx
  refine mem_reservoirBall.mpr ⟨hvQ, a, ha, p.append w, ?_, ?_⟩
  · simpa only [Walk.length_append] using Nat.add_le_add hp hw
  · intro y hy
    rcases (Walk.mem_support_append_iff p w).mp hy with hy | hy
    · exact hps y hy
    · rcases hws y hy with rfl | hyQ
      · exact Or.inr hxQ
      · exact Or.inr hyQ

/-- A t-subset of an actual ball activates the given t-set expansion property. -/
theorem expand_large_ball (G : SimpleGraph V) (Q : Finset V) (ell t : ℕ)
    (hexpand : ∀ U : Finset V, U.card = t →
      (Q.card : ℝ) / 2 < (reservoirBall G U Q ell).card)
    (A : Finset V) (r : ℕ) (hcard : t ≤ (reservoirBall G A Q r).card) :
    (Q.card : ℝ) / 2 < (reservoirBall G A Q (r + ell)).card := by
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hcard
  have hs := (ball_mono_source G Q ell hUsub).trans (ball_compose G A Q r ell)
  have hc : ((reservoirBall G U Q ell).card : ℝ) ≤
      (reservoirBall G A Q (r + ell)).card := by exact_mod_cast Finset.card_le_card hs
  exact (hexpand U hUcard).trans_le hc

/-- Every finite set of size at most twice c has a partition with both parts
of size at most c. The selected parts are actual subsets of the seed set. -/
theorem partition_card_le (X : Finset V) (c : ℕ) (hc : X.card ≤ 2 * c) :
    ∃ A B : Finset V, A ⊆ X ∧ B ⊆ X ∧ A ∪ B = X ∧ A.card ≤ c ∧ B.card ≤ c := by
  obtain ⟨A, hAX, hA⟩ := Finset.exists_subset_card_eq (Nat.min_le_left X.card c)
  refine ⟨A, X \ A, hAX, Finset.sdiff_subset, Finset.union_sdiff_of_subset hAX, ?_, ?_⟩
  · omega
  · rw [Finset.card_sdiff_of_subset hAX]
    omega

/-- Binary compression of a majority-reaching seed set. Each stage uses
actual t-set expansion and adds ell graph edges to the radius. -/
theorem compress_majority_seed (G : SimpleGraph V) (Q : Finset V) (ell t : ℕ)
    (ht : 1 ≤ t) (hQ : 4 * t - 2 ≤ Q.card)
    (hexpand : ∀ U : Finset V, U.card = t →
      (Q.card : ℝ) / 2 < (reservoirBall G U Q ell).card)
    (k : ℕ) (X : Finset V) (r : ℕ) (hX : X.card ≤ 2 ^ k)
    (hmajor : (Q.card : ℝ) / 2 < (reservoirBall G X Q r).card) :
    ∃ x ∈ X, (Q.card : ℝ) / 2 < (reservoirBall G {x} Q (r + k * ell)).card := by
  classical
  induction k generalizing X r with
  | zero =>
    have hnonempty : (reservoirBall G X Q r).Nonempty := by
      apply Finset.card_pos.mp
      have : (0 : ℝ) < (reservoirBall G X Q r).card := by
        have hnonneg : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
        linarith
      exact_mod_cast this
    obtain ⟨v, hv⟩ := hnonempty
    obtain ⟨_, x, hx, _, _, _⟩ := mem_reservoirBall.mp hv
    have hsub : X ⊆ {x} := by
      intro y hy
      apply Finset.mem_singleton.mpr
      exact Finset.card_le_one.mp (by simpa using hX) y hy x hx
    have hc : ((reservoirBall G X Q r).card : ℝ) ≤ (reservoirBall G {x} Q r).card := by
      exact_mod_cast Finset.card_le_card (ball_mono_source G Q r hsub)
    exact ⟨x, hx, by simpa using hmajor.trans_le hc⟩
  | succ k ih =>
    obtain ⟨A, B, hAX, hBX, hAB, hA, hB⟩ := partition_card_le X (2 ^ k)
      (by simpa [pow_succ, Nat.mul_comm] using hX)
    have hsum : (Q.card : ℝ) / 2 <
        ((reservoirBall G A Q r).card : ℝ) + (reservoirBall G B Q r).card := by
      rw [← hAB, ball_union] at hmajor
      have hc : ((reservoirBall G A Q r ∪ reservoirBall G B Q r).card : ℝ) ≤
          (reservoirBall G A Q r).card + (reservoirBall G B Q r).card := by
        exact_mod_cast Finset.card_union_le (reservoirBall G A Q r) (reservoirBall G B Q r)
      exact hmajor.trans_le hc
    have hlarge : t ≤ (reservoirBall G A Q r).card ∨ t ≤ (reservoirBall G B Q r).card := by
      have hQR : (4 : ℝ) * t - 2 ≤ Q.card := by
        have hQ' : 4 * t ≤ Q.card + 2 := by omega
        have hcast : (4 : ℝ) * t ≤ Q.card + 2 := by exact_mod_cast hQ'
        linarith
      by_contra hn
      push Not at hn
      have haR : ((reservoirBall G A Q r).card : ℝ) ≤ t - 1 := by
        have haN : (reservoirBall G A Q r).card + 1 ≤ t := by omega
        have : ((reservoirBall G A Q r).card : ℝ) + 1 ≤ t := by exact_mod_cast haN
        linarith
      have hbR : ((reservoirBall G B Q r).card : ℝ) ≤ t - 1 := by
        have hbN : (reservoirBall G B Q r).card + 1 ≤ t := by omega
        have : ((reservoirBall G B Q r).card : ℝ) + 1 ≤ t := by exact_mod_cast hbN
        linarith
      linarith
    rcases hlarge with ha | hb
    · obtain ⟨x, hx, hm⟩ := ih A (r + ell) hA (expand_large_ball G Q ell t hexpand A r ha)
      refine ⟨x, hAX hx, ?_⟩
      simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
    · obtain ⟨x, hx, hm⟩ := ih B (r + ell) hB (expand_large_ball G Q ell t hexpand B r hb)
      refine ⟨x, hBX hx, ?_⟩
      simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm


/-- Among any injectively indexed terminals, fewer than t have a small ball
at the logarithmic integer radius. -/
theorem bad_terminal_count {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (Q : Finset V) (ell t : ℕ) (ht : 1 ≤ t)
    (hQ : 4 * t - 2 ≤ Q.card)
    (hexpand : ∀ U : Finset V, U.card = t →
      (Q.card : ℝ) / 2 < (reservoirBall G U Q ell).card)
    (f : I → V) (hf : Function.Injective f) :
    (Finset.univ.filter (fun i => ((reservoirBall G {f i} Q
      ((Nat.clog 2 t + 1) * ell)).card : ℝ) ≤ (Q.card : ℝ) / 2)).card < t := by
  classical
  let R := (Nat.clog 2 t + 1) * ell
  let bad := Finset.univ.filter (fun i => ((reservoirBall G {f i} Q R).card : ℝ) ≤ (Q.card : ℝ) / 2)
  change bad.card < t
  by_contra hn
  obtain ⟨J, hJbad, hJcard⟩ := Finset.exists_subset_card_eq (le_of_not_gt hn)
  have hXcard : (J.image f).card = t := by rw [Finset.card_image_of_injective J hf, hJcard]
  obtain ⟨x, hx, hmajor⟩ := compress_majority_seed G Q ell t ht hQ hexpand
    (Nat.clog 2 t) (J.image f) ell (by rw [hXcard]; exact Nat.le_pow_clog (by norm_num) t)
    (hexpand _ hXcard)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hbad := (Finset.mem_filter.mp (hJbad hi)).2
  have hr : ell + Nat.clog 2 t * ell = R := by dsimp [R]; ring
  rw [hr] at hmajor
  exact (not_lt_of_ge hbad) hmajor

/-- Genuine prescribed-pair routing, with no substitution of an arbitrary
cross-pair. The integer radius is explicit, and every path edge belongs to G.
Only injectivity within each terminal list is needed. -/
theorem paired_routing_integer {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (Q : Finset V) (ell t : ℕ) (ht : 1 ≤ t)
    (hQ : 4 * t - 2 ≤ Q.card)
    (hexpand : ∀ U : Finset V, U.card = t →
      (Q.card : ℝ) / 2 < (reservoirBall G U Q ell).card)
    (z w : I → V) (hz : Function.Injective z) (hw : Function.Injective w)
    (hI : 2 * t - 1 ≤ Fintype.card I) :
    ∃ i, ∃ p : G.Walk (z i) (w i), p.IsPath ∧
      p.length ≤ 2 * ((Nat.clog 2 t + 1) * ell) ∧
      ∀ x ∈ p.support, x ≠ z i → x ≠ w i → x ∈ Q := by
  classical
  let R := (Nat.clog 2 t + 1) * ell
  let Bz := Finset.univ.filter (fun i => ((reservoirBall G {z i} Q R).card : ℝ) ≤ (Q.card : ℝ) / 2)
  let Bw := Finset.univ.filter (fun i => ((reservoirBall G {w i} Q R).card : ℝ) ≤ (Q.card : ℝ) / 2)
  have hzbad : Bz.card < t := bad_terminal_count G Q ell t ht hQ hexpand z hz
  have hwbad : Bw.card < t := bad_terminal_count G Q ell t ht hQ hexpand w hw
  have hex : ∃ i, i ∉ Bz ∧ i ∉ Bw := by
    by_contra hn
    push Not at hn
    have hcover : (Finset.univ : Finset I) ⊆ Bz ∪ Bw := by
      intro i hi
      by_cases hzmem : i ∈ Bz
      · exact Finset.mem_union_left _ hzmem
      · exact Finset.mem_union_right _ (hn i hzmem)
    have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le Bz Bw)
    simp only [Finset.card_univ] at hc
    omega
  obtain ⟨i, hiz, hiw⟩ := hex
  have hmajorz : (Q.card : ℝ) / 2 < (reservoirBall G {z i} Q R).card := by
    apply lt_of_not_ge
    intro hn
    exact hiz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  have hmajorw : (Q.card : ℝ) / 2 < (reservoirBall G {w i} Q R).card := by
    apply lt_of_not_ge
    intro hn
    exact hiw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  obtain ⟨a, ha, b, hb, p, hp, hlen, hins⟩ :=
    majority_balls_path G {z i} {w i} Q R R hmajorz hmajorw
  have haz : a = z i := Finset.mem_singleton.mp ha
  have hbw : b = w i := Finset.mem_singleton.mp hb
  subst a
  subst b
  exact ⟨i, p, hp, by change p.length ≤ 2 * R; omega, hins⟩


/-- Integer-radius to real logarithm conversion. The upper bound n is not
identified with the cardinality of a smaller core or reservoir. -/
theorem integer_radius_le_log_bound (ell t n : ℕ) (ht : 1 ≤ t) (hn : 2 * t ≤ n) :
    (2 * ((Nat.clog 2 t + 1) * ell) : ℝ) ≤ 4 * ell * Real.logb 2 n := by
  have hn2 : 2 ≤ n := by omega
  have hpow : 2 ^ Nat.clog 2 t ≤ n := by
    by_cases ht1 : t = 1
    · subst t
      simp only [Nat.clog_one_right, pow_zero]
      omega
    · have htgt : 1 < t := by omega
      have hk := Nat.clog_pos (by norm_num : 1 < 2) htgt
      have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) htgt
      have he : 2 ^ Nat.clog 2 t = 2 ^ (Nat.clog 2 t).pred * 2 := by
        rw [← pow_succ]
        congr 1
        exact (Nat.succ_pred_eq_of_pos hk).symm
      rw [he]
      omega
  have hpowR : (2 : ℝ) ^ Nat.clog 2 t ≤ n := by exact_mod_cast hpow
  have hklog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2 ^ Nat.clog 2 t) hpowR
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hklog
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogone := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) hnR
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlogone
  have he : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hklog he,
    mul_le_mul_of_nonneg_right hlogone he]

                                                                           
                                                                            
                                                                        
                                                                          
                                              
theorem paired_routing {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (Q : Finset V) (ell t n : ℕ) (ht : 1 ≤ t)
    (hQ : 4 * t - 2 ≤ Q.card) (horder : Fintype.card V ≤ n)
    (hexpand : ∀ U : Finset V, U.card = t →
      (Q.card : ℝ) / 2 < (reservoirBall G U Q ell).card)
    (z w : I → V) (hz : Function.Injective z) (hw : Function.Injective w)
    (hI : 2 * t - 1 ≤ Fintype.card I) :
    ∃ i, ∃ p : G.Walk (z i) (w i), p.IsPath ∧
      (p.length : ℝ) ≤ 4 * ell * logTwo (n : ℝ) ∧
      ∀ x ∈ p.support, x ≠ z i → x ≠ w i → x ∈ Q := by
  obtain ⟨i, p, hp, hlen, hins⟩ := paired_routing_integer G Q ell t ht hQ hexpand z w hz hw hI
  have hQn : Q.card ≤ n := (Finset.card_le_univ Q).trans horder
  have htn : 2 * t ≤ n := by omega
  have hlenR : (p.length : ℝ) ≤ 2 * ((Nat.clog 2 t + 1) * ell) := by exact_mod_cast hlen
  exact ⟨i, p, hp, hlenR.trans (integer_radius_le_log_bound ell t n ht htn), hins⟩

end Erdos585.Attempt6.PairedRouting
