import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphParityOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreDensity
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathSplit
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents

/-! Deterministic occupation comparison and exact original-walk interval integration. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix Erdos642.FiniteMarkov Erdos642.OccupationTail
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
 theorem occupation_nonneg (S : Finset V) {n : ℕ} (x : V) (p : Path V n) :
    0 ≤ occupation S x p := by
  induction n generalizing x with
  | zero => simp only [occupation, Chain.vertexSum]; split_ifs <;> norm_num
  | succ n ih =>
    change 0 ≤ (if x ∈ S then 1 else 0) + occupation S p.1 p.2
    have hi := ih p.1 p.2
    split_ifs <;> linarith

omit [Fintype V] in
 theorem occupation_initial_le (S : Finset V) {n : ℕ} (x : V) (p : Path V n) :
    (if x ∈ S then (1 : ℝ) else 0) ≤ occupation S x p := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    change _ ≤ (if x ∈ S then 1 else 0) + occupation S p.1 p.2
    linarith [occupation_nonneg S p.1 p.2]

 theorem occupation_append_ge (C : Chain V) (S : Finset V)
    {m n : ℕ} (x : V) (p : Path V m) (q : Path V n) :
    occupation S x p ≤ occupation S x (C.append p q) := by
  induction m generalizing x with
  | zero => exact occupation_initial_le S x q
  | succ m ih =>
    change (if x ∈ S then 1 else 0) + occupation S p.1 p.2 ≤
      (if x ∈ S then 1 else 0) + occupation S p.1 (C.append p.2 q)
    exact add_le_add le_rfl (ih p.1 p.2)

 theorem occupation_prefix_le (C : Chain V) (S : Finset V)
    (m n : ℕ) (x : V) (p : Path V (n + m)) :
    occupation S x (PathSplit.split m n p).1 ≤ occupation S x p := by
  have h := occupation_append_ge C S x (PathSplit.split m n p).1 (PathSplit.split m n p).2
  simpa only [C.append_split] using h

omit [Fintype V] in
 theorem occupation_interleave_le (S : Finset V) {n : ℕ}
    (x : V) (p q : Path V n) :
    occupation S x q ≤ occupation S x (interleave p q) := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
    change (if x ∈ S then 1 else 0) + occupation S q.1 q.2 ≤
      (if x ∈ S then 1 else 0) + ((if p.1 ∈ S then 1 else 0) +
        occupation S q.1 (interleave p.2 q.2))
    have hh := ih q.1 p.2 q.2
    split_ifs <;> linarith

omit [Fintype V] in
 theorem occupation_cast {a b : ℕ} (h : a = b) (S : Finset V) (x : V) (p : Path V a) :
    occupation S x (cast (congrArg (Path V) h) p) = occupation S x p := by
  cases h
  rfl

omit [Fintype V] in
 theorem occupation_even_sample_le (S : Finset V) (n : ℕ)
    (x : V) (p : Path V (2 * n)) :
    occupation S x (sampleEvenTwoMul n p) ≤ occupation S x p := by
  let pq := (interleaveTwoMulEquiv n).symm p
  have he : p = interleaveTwoMulEquiv n pq := ((interleaveTwoMulEquiv n).apply_symm_apply p).symm
  rw [he, sampleEvenTwoMul_interleave]
  change occupation S x pq.2 ≤ occupation S x
    (cast (congrArg (Path V) (doubleLength_eq_two_mul n)) (interleave pq.1 pq.2))
  rw [occupation_cast (doubleLength_eq_two_mul n)]
  exact occupation_interleave_le S x pq.1 pq.2

 theorem occupation_tail_prefix_le (C : Chain V) (S : Finset V)
    (m n : ℕ) (a : ℝ) (x : V) :
    C.eventMass (n + m) (fun y p => occupation S y p < a) x ≤
      C.eventMass m (fun y p => occupation S y p < a) x := by
  calc
    _ ≤ C.eventMass (n + m)
      (fun y p => occupation S y (PathSplit.split m n p).1 < a) x :=
        C.eventMass_mono _ _ (fun y p hp => lt_of_le_of_lt (occupation_prefix_le C S m n y p) hp) x
    _ = _ := C.eventMass_prefix m n (fun y p => occupation S y p < a) x

omit [DecidableEq V] in
 theorem eventMass_succ (C : Chain V) (n : ℕ) (E : V → Path V (n + 1) → Prop) (x : V) :
    C.eventMass (n + 1) E x = ∑ y, C.transition x y *
      C.eventMass n (fun _ q => E x (y, q)) y := by
  classical
  unfold Chain.eventMass
  change (∑ p : V × Path V n, if E x p then C.transition x p.1 * C.weight p.1 p.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp

 theorem occupation_tail_succ_le (C : Chain V) (S : Finset V)
    (n : ℕ) (a : ℝ) (x : V) :
    C.eventMass (n + 1) (fun y p => occupation S y p < a) x ≤
      ∑ y, C.transition x y * C.eventMass n (fun z q => occupation S z q < a) y := by
  calc
    _ ≤ C.eventMass (n + 1) (fun _ p => occupation S p.1 p.2 < a) x := by
      apply C.eventMass_mono
      intro y p hp
      change (if y ∈ S then 1 else 0) + occupation S p.1 p.2 < a at hp
      split_ifs at hp <;> linarith
    _ = _ := by rw [eventMass_succ]; rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)] [Nonempty s]

 theorem same_shore_occupation_sample_bound (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (d : ℝ) (hd : 0 < d) (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (S : Finset s) (n L : ℕ) (hfit : 2 * n ≤ L) (a : ℝ)
    (ha : a ≤ ((n + 1 : ℕ) : ℝ) * Erdos642.TiltedOperator.mass S (shoreRoot G s) / 2)
    (x : s) :
    (graphChain G hdeg).eventMass L (fun y p => occupation (ambientShoreSet s S) y p < a) x.val ≤
      (100 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * Erdos642.TiltedOperator.mass S (shoreRoot G s) * ((n + 1 : ℕ) : ℝ) / 64) := by
  have hp := occupation_tail_prefix_le (graphChain G hdeg) (ambientShoreSet s S)
    (2 * n) (L - 2 * n) a x.val
  have hp' : (graphChain G hdeg).eventMass L
      (fun y p => occupation (ambientShoreSet s S) y p < a) x.val ≤
      (graphChain G hdeg).eventMass (2 * n)
        (fun y p => occupation (ambientShoreSet s S) y p < a) x.val := by
    have he : L - 2 * n + 2 * n = L := Nat.sub_add_cancel hfit
    rw [he] at hp
    exact hp
  have hm := (graphChain G hdeg).eventMass_mono
    (fun y p => occupation (ambientShoreSet s S) y p < a)
    (fun y p => occupation (ambientShoreSet s S) y (sampleEvenTwoMul n p) ≤
      ((n + 1 : ℕ) : ℝ) * Erdos642.TiltedOperator.mass S (shoreRoot G s) / 2)
    (fun y p h => (occupation_even_sample_le (ambientShoreSet s S) n y p).trans
      (le_trans (le_of_lt h) ha)) x.val
  have ht := graph_even_shore_occupation_tail s G t hbi hdeg γ hgap S n x
  exact (hp'.trans (hm.trans ht)).trans
    (mul_le_mul_of_nonneg_right (shoreRoot_prefactor_upper G s t hbi hdeg d hd hmin hmax x)
      (le_of_lt (Real.exp_pos _)))

/-- An arbitrary original starting vertex, using actual first-step averaging if needed. -/
theorem graph_occupation_sample_bound (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (d : ℝ) (hd : 0 < d) (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (S : Finset s) (n L : ℕ) (hfit : 2 * n + 1 ≤ L) (a : ℝ)
    (ha : a ≤ ((n + 1 : ℕ) : ℝ) * Erdos642.TiltedOperator.mass S (shoreRoot G s) / 2)
    (x : V) :
    (graphChain G hdeg).eventMass L (fun y p => occupation (ambientShoreSet s S) y p < a) x ≤
      (100 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * Erdos642.TiltedOperator.mass S (shoreRoot G s) * ((n + 1 : ℕ) : ℝ) / 64) := by
  by_cases hx : x ∈ s
  · exact same_shore_occupation_sample_bound G s t hbi hdeg d hd hmin hmax γ hgap S n L
      (by omega) a ha ⟨x, hx⟩
  · let B := (100 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * Erdos642.TiltedOperator.mass S (shoreRoot G s) * ((n + 1 : ℕ) : ℝ) / 64)
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hstep := occupation_tail_succ_le (graphChain G hdeg) (ambientShoreSet s S) (L - 1) a x
    have hL : L - 1 + 1 = L := by omega
    rw [hL] at hstep
    refine hstep.trans ?_
    calc
      _ ≤ ∑ y, (graphChain G hdeg).transition x y * B := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hy : y ∈ s
        · exact mul_le_mul_of_nonneg_left
            (same_shore_occupation_sample_bound G s t hbi hdeg d hd hmin hmax γ hgap S n (L - 1)
              (by omega) a ha ⟨y, hy⟩) ((graphChain G hdeg).nonneg x y)
        · have hxy : ¬G.Adj x y := by
            intro hadj
            rcases hbi.mem_of_adj hadj with h | h
            · exact hx h.1
            · exact hy h.2
          have hz : (graphChain G hdeg).transition x y = 0 := by
            simp [graphChain, graphTransition, SimpleGraph.adjMatrix_apply, hxy]
          simp [hz]
      _ = B := by rw [← Finset.sum_mul, (graphChain G hdeg).row_sum, one_mul]

omit [Nonempty s] in
/-- Actual full-interval occupation bound, uniform in the original starting vertex. -/
theorem graph_occupation_tail (r : Set V)
    (hbi : G.IsBipartiteWith s r) (hdeg : ∀ x : V, 0 < G.degree x)
    (d : ℝ) (hd : 0 < d) (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (S : Finset s) (t : ℕ) (ht : 2 ≤ t) (x : V) :
    (graphChain G hdeg).eventMass (t - 1)
      (fun y p => occupation (ambientShoreSet s S) y p <
        (t : ℝ) * (S.card : ℝ) / (300 * (Fintype.card V : ℝ))) x ≤
      (200 * (Fintype.card V : ℝ)) * Real.exp
        (-γ * (t : ℝ) * (S.card : ℝ) / (10000 * (Fintype.card V : ℝ))) := by
  have : Nonempty V := ⟨x⟩
  have : Nonempty s := by
    obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (hdeg x)
    rcases hbi.mem_of_adj hxy with h | h
    · exact ⟨⟨x, h.1⟩⟩
    · exact ⟨⟨y, h.2⟩⟩
  let N : ℝ := Fintype.card V
  let μ : ℝ := Erdos642.TiltedOperator.mass S (shoreRoot G s)
  let n : ℕ := t / 2 - 1
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hμ : 0 ≤ μ := Erdos642.TiltedOperator.mass_nonneg S (shoreRoot G s)
  have hn : 1 ≤ t / 2 := by omega
  have hfit : 2 * n + 1 ≤ t - 1 := by dsimp [n]; omega
  have hcount : (t : ℝ) ≤ 3 * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show t ≤ 3 * (n + 1) by dsimp [n]; omega)
  have hsample : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hS : 0 ≤ (S.card : ℝ) := by positivity
  have hmass : (S.card : ℝ) / (50 * N) ≤ μ :=
    shore_mass_lower G s r hbi hdeg d hd hmin hmax S
  have hs : (S.card : ℝ) ≤ μ * (50 * N) :=
    (div_le_iff₀ (by positivity : 0 < 50 * N)).mp hmass
  have hts := mul_le_mul_of_nonneg_right hcount hS
  have hns := mul_le_mul_of_nonneg_left hs hsample
  have hprod : (t : ℝ) * (S.card : ℝ) ≤ 150 * N * ((n + 1 : ℕ) : ℝ) * μ := by
    nlinarith
  have ha : (t : ℝ) * (S.card : ℝ) / (300 * N) ≤
      ((n + 1 : ℕ) : ℝ) * μ / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 300 * N)).2
    nlinarith
  have hb := graph_occupation_sample_bound G s r hbi hdeg d hd hmin hmax γ hgap S n (t - 1)
    hfit ((t : ℝ) * (S.card : ℝ) / (300 * N)) ha x
  have hexp : Real.exp (-γ * μ * ((n + 1 : ℕ) : ℝ) / 64) ≤
      Real.exp (-γ * (t : ℝ) * (S.card : ℝ) / (10000 * N)) := by
    apply Real.exp_le_exp.mpr
    have hγ : 0 < γ := hgap.1
    have hg := mul_le_mul_of_nonneg_left hprod hγ.le
    have hzero : 0 ≤ γ * N * ((n + 1 : ℕ) : ℝ) * μ := by positivity
    have hratio : γ * (t : ℝ) * (S.card : ℝ) / (10000 * N) ≤
        γ * μ * ((n + 1 : ℕ) : ℝ) / 64 := by
      apply (div_le_iff₀ (by positivity : 0 < 10000 * N)).2
      nlinarith
    simpa only [neg_mul, neg_div] using neg_le_neg hratio
  calc
    _ ≤ (100 * N) * Real.exp (-γ * μ * ((n + 1 : ℕ) : ℝ) / 64) := hb
    _ ≤ (100 * N) * Real.exp (-γ * (t : ℝ) * (S.card : ℝ) / (10000 * N)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by change 100 * N ≤ 200 * N; nlinarith) (Real.exp_pos _).le

end Erdos642.CampaignFe72210b
