import Openmath.Erdos642.Proofs.DenseMask20261019.CutEscape
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutExtractSubtype

                                                             
                                        

                                                                                    
                                                                       
                                                    
                                                                                    
                                                                      
                                                                  
                                                                                  
                             
                                                                                       
                                                                                      
                                                                                  
                                                                              
                                                             
                                                                               
                                                                 

                                                                      
                                                                        
                                                                          
                                                                                   
                                                                                     
                                   

                                                                    
                                                                                   
                                                                                    
                                                                      
  
noncomputable section
namespace Erdos642.DenseMask20261019.MaskCore
open Finset SimpleGraph MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.CampaignFe72210bContinuation3.GraphExpansionConductance
open Erdos642.DenseMask20261019

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The sets whose sampled sizes are controlled: all of `W`, and every neighborhood. -/
def centerSet (H : SimpleGraph W) [DecidableRel H.Adj] (o : Option W) : Finset W :=
  o.elim Finset.univ (fun v => H.neighborFinset v)

/-- Lower and upper tail failure events for each controlled set. -/
def badEvent (H : SimpleGraph W) [DecidableRel H.Adj] (p : unitInterval) :
    Option W × Bool → Set (W → Bool)
  | (o, false) => {ω | ((centerSet H o ∩ sampleVertices ω).card : ℝ) ≤
      (p : ℝ) * (centerSet H o).card / 2}
  | (o, true) => {ω | 2 * (p : ℝ) * (centerSet H o).card ≤
      ((centerSet H o ∩ sampleVertices ω).card : ℝ)}

omit [DecidableEq W] in
theorem centerSet_card (H : SimpleGraph W) [DecidableRel H.Adj] (d : ℝ)
    (hN : 0 < Fintype.card W) (hlo : ∀ v, d ≤ (H.degree v : ℝ)) (o : Option W) :
    d ≤ ((centerSet H o).card : ℝ) := by
  cases o with
  | none =>
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hN
    have h : d ≤ (Fintype.card W : ℝ) :=
      (hlo v).trans (by exact_mod_cast (H.degree_lt_card_verts v).le)
    simpa [centerSet] using h
  | some v =>
    simpa [centerSet, H.card_neighborFinset_eq_degree] using hlo v

theorem budget_lt_one (N : ℕ) (hN : 0 < N) (rho L : ℝ)
    (hL : log (2*(N : ℝ)) ≤ L) (hr : 64*L ≤ rho) :
    2*((N : ℝ)+1)*exp (-rho/8) < 1 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ log (2*(N : ℝ)) := log_nonneg (by linarith)
  have he : (2*(N : ℝ))^3 ≤ exp (rho/8) := by
    calc
      (2*(N : ℝ))^3 = exp (3*log (2*(N : ℝ))) := by
        rw [show (3 : ℝ)*log (2*(N : ℝ)) = ((3 : ℕ) : ℝ)*log (2*(N : ℝ)) by norm_num,
          exp_nat_mul, exp_log (by positivity)]
      _ ≤ exp (rho/8) := exp_le_exp.mpr (by linarith)
  have hN2 : (1 : ℝ) ≤ (N : ℝ)*N := by nlinarith
  have hN3 : (N : ℝ) ≤ (N : ℝ)*N*N := by nlinarith
  have h3 : 2*((N : ℝ)+1) < (2*(N : ℝ))^3 := by nlinarith
  rw [show -rho/8 = -(rho/8) by ring, exp_neg, ← div_eq_mul_inv,
    div_lt_one (exp_pos _)]
  linarith

/-- A positive-probability sample: every neighborhood and the whole vertex set are
sampled within a factor two of their means, simultaneously. -/
theorem exists_good_mask (H : SimpleGraph W) [DecidableRel H.Adj] (p d : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < Fintype.card W) (hlo : ∀ v, d ≤ (H.degree v : ℝ))
    (hbudget : 2*((Fintype.card W : ℝ)+1) * exp (-(p*d)/8) < 1) :
    ∃ Q : Finset W,
      (∀ v, p*(H.degree v : ℝ)/2 < ((H.neighborFinset v ∩ Q).card : ℝ) ∧
        ((H.neighborFinset v ∩ Q).card : ℝ) < 2*p*(H.degree v : ℝ)) ∧
      p*(Fintype.card W : ℝ)/2 < (Q.card : ℝ) ∧ (Q.card : ℝ) < 2*p*(Fintype.card W : ℝ) := by
  let pu : unitInterval := ⟨p, hp0, hp1⟩
  have hev : ∀ i, (sampleMeasure W pu).real (badEvent H pu i) ≤ exp (-(p*d)/8) := by
    rintro ⟨o, b⟩
    have hc := centerSet_card H d hN hlo o
    have hpc : p*d ≤ p*(centerSet H o).card := mul_le_mul_of_nonneg_left hc hp0
    have hpc0 : 0 ≤ p*(centerSet H o).card := mul_nonneg hp0 (Nat.cast_nonneg _)
    cases b with
    | false =>
      refine (sample_card_lower_tail pu (centerSet H o)).trans (exp_le_exp.mpr ?_)
      change -p*(centerSet H o).card/8 ≤ -(p*d)/8
      linarith
    | true =>
      refine (sample_card_upper_tail pu (centerSet H o)).trans (exp_le_exp.mpr ?_)
      change -p*(centerSet H o).card/3 ≤ -(p*d)/8
      linarith
  have hsum : ∑ i ∈ (Finset.univ : Finset (Option W × Bool)),
      (sampleMeasure W pu).real (badEvent H pu i) < 1 := by
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Option W × Bool)), exp (-(p*d)/8) :=
        Finset.sum_le_sum (fun i _ => hev i)
      _ = 2*((Fintype.card W : ℝ)+1) * exp (-(p*d)/8) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_option, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
      _ < 1 := hbudget
  obtain ⟨ω, hω⟩ := exists_avoiding_finite_events _ _ hsum
  refine ⟨sampleVertices ω, fun v => ⟨?_, ?_⟩, ?_, ?_⟩
  · have h : ¬ (((H.neighborFinset v ∩ sampleVertices ω).card : ℝ) ≤
        p*(H.neighborFinset v).card/2) := hω (some v, false) (Finset.mem_univ _)
    rw [H.card_neighborFinset_eq_degree] at h
    exact not_le.mp h
  · have h : ¬ (2*p*(H.neighborFinset v).card ≤
        ((H.neighborFinset v ∩ sampleVertices ω).card : ℝ)) :=
      hω (some v, true) (Finset.mem_univ _)
    rw [H.card_neighborFinset_eq_degree] at h
    exact not_le.mp h
  · have h : ¬ ((((Finset.univ : Finset W) ∩ sampleVertices ω).card : ℝ) ≤
        p*(Finset.univ : Finset W).card/2) := hω (none, false) (Finset.mem_univ _)
    rw [Finset.univ_inter, Finset.card_univ] at h
    exact not_le.mp h
  · have h : ¬ (2*p*(Finset.univ : Finset W).card ≤
        (((Finset.univ : Finset W) ∩ sampleVertices ω).card : ℝ)) :=
      hω (none, true) (Finset.mem_univ _)
    rw [Finset.univ_inter, Finset.card_univ] at h
    exact not_le.mp h

theorem filter_adj_eq (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) (a : W) :
    S.filter (H.Adj a) = H.neighborFinset a ∩ S := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, and_comm]

/-- Residual cut, counted in the host: a set `X` avoiding `Q` loses at most `φd|X|/4`
cut edges into `Q`, so its new neighbors outside `Q` number at least `3φ|X|/400`. -/
theorem residual_boundary (H : SimpleGraph W) [DecidableRel H.Adj] (Q X : Finset W)
    (hXQ : Disjoint X Q) (φ d : ℝ) (hd : 0 < d)
    (hhi : ∀ v, (H.degree v : ℝ) ≤ 100*d)
    (hcap : ∀ v, ((H.neighborFinset v ∩ Q).card : ℝ) ≤ φ*d/4)
    (hcutX : φ*d*(X.card : ℝ) ≤ crossing H X) :
    3*φ*(X.card : ℝ)/400 ≤
      (((Qᶜ \ X).filter (fun y => ∃ x ∈ X, H.Adj x y)).card : ℝ) := by
  set B := (Qᶜ \ X).filter (fun y => ∃ x ∈ X, H.Adj x y) with hBdef
  have hQX : Q ⊆ Xᶜ := fun y hy =>
    Finset.mem_compl.mpr (fun hx => Finset.disjoint_left.mp hXQ hx hy)
  have hsplit := count_partition_right H Xᶜ Q X hQX
  have hset : Xᶜ \ Q = Qᶜ \ X := by
    ext y
    simp [and_comm]
  have hQpart : (IncidenceCounts.count H X Q : ℝ) ≤ X.card * (φ*d/4) := by
    unfold IncidenceCounts.count
    push_cast
    calc
      (∑ a ∈ X, ((Q.filter (H.Adj a)).card : ℝ)) ≤ ∑ _a ∈ X, φ*d/4 :=
        Finset.sum_le_sum (fun a _ => by rw [filter_adj_eq]; exact hcap a)
      _ = _ := by simp
  have hBpart : IncidenceCounts.count H X (Qᶜ \ X) ≤ IncidenceCounts.count H X B := by
    unfold IncidenceCounts.count
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_filter.mpr ⟨hy.1, a, ha, hy.2⟩, hy.2⟩
  have hBdeg : (IncidenceCounts.count H X B : ℝ) ≤ B.card * (100*d) := by
    rw [IncidenceCounts.count_swap]
    have h1 := IncidenceCounts.count_le_sum_degree H B X
    have h2 : ((IncidenceCounts.count H B X : ℕ) : ℝ) ≤ ∑ b ∈ B, (H.degree b : ℝ) := by
      exact_mod_cast h1
    calc
      _ ≤ ∑ b ∈ B, (H.degree b : ℝ) := h2
      _ ≤ ∑ _b ∈ B, 100*d := Finset.sum_le_sum (fun b _ => hhi b)
      _ = _ := by simp
  rw [crossing_eq_incidence, hsplit, hset] at hcutX
  push_cast at hcutX
  have hBpartR : (IncidenceCounts.count H X (Qᶜ \ X) : ℝ) ≤ IncidenceCounts.count H X B := by
    exact_mod_cast hBpart
  have hmain : d*(3*φ*(X.card : ℝ)/400) ≤ d*(B.card : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_left hmain hd

/-- The residual induced graph expands at rate `3φ/1600`, for every choice of the
subtype instances. -/
theorem residual_expands (H : SimpleGraph W) [DecidableRel H.Adj] (Q R : Finset W)
    (hR : R = Qᶜ) (φ d : ℝ) (hd : 0 < d) (hφ : 0 ≤ φ)
    (hhi : ∀ v, (H.degree v : ℝ) ≤ 100*d)
    (hcap : ∀ v, ((H.neighborFinset v ∩ Q).card : ℝ) ≤ φ*d/4)
    (hcut : ∀ X : Finset W, (X.card : ℝ) ≤ (Fintype.card W : ℝ)/2 →
      φ*d*(X.card : ℝ) ≤ crossing H X)
    [Fintype (Set.Elem (R : Set W))] [DecidableEq (Set.Elem (R : Set W))]
    [DecidableRel (H.induce (R : Set W)).Adj] :
    CutEscape.Expands (H.induce (R : Set W)) (3*φ/1600) := by
  intro U hU
  let X : Finset W := U.map (Function.Embedding.subtype _)
  have hXc : X.card = U.card := Finset.card_map _
  have hXR : ∀ x ∈ X, x ∈ R := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_coe.mp u.2
  have hXQ : Disjoint X Q := by
    rw [Finset.disjoint_left]
    intro x hx hxQ
    have h := hXR x hx
    rw [hR, Finset.mem_compl] at h
    exact h hxQ
  have hRc : Fintype.card (Set.Elem (R : Set W)) = R.card :=
    (Fintype.card_congr (Equiv.refl _ : Set.Elem (R : Set W) ≃ {x // x ∈ R})).trans
      (Fintype.card_coe R)
  have hRN : R.card ≤ Fintype.card W := Finset.card_le_univ R
  have hXN : (X.card : ℝ) ≤ (Fintype.card W : ℝ)/2 := by
    have h1 : 2*X.card ≤ Fintype.card W := by omega
    have h2 : ((2*X.card : ℕ) : ℝ) ≤ Fintype.card W := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hB := residual_boundary H Q X hXQ φ d hd hhi hcap (hcut X hXN)
  have hsub : (Qᶜ \ X).filter (fun y => ∃ x ∈ X, H.Adj x y) ⊆
      (ComponentObstruction.closedNeighborhood (H.induce (R : Set W)) U \ U).map
        (Function.Embedding.subtype _) := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_compl] at hy
    obtain ⟨⟨hyQ, hyX⟩, x, hxX, hxy⟩ := hy
    have hyR : y ∈ (R : Set W) := by
      rw [Finset.mem_coe, hR, Finset.mem_compl]
      exact hyQ
    obtain ⟨u, huU, rfl⟩ := Finset.mem_map.mp hxX
    rw [Finset.mem_map]
    refine ⟨⟨y, hyR⟩, ?_, rfl⟩
    rw [Finset.mem_sdiff]
    constructor
    · unfold ComponentObstruction.closedNeighborhood
      rw [Finset.mem_union, Finset.mem_biUnion]
      right
      exact ⟨u, huU, (SimpleGraph.mem_neighborFinset _ _ _).mpr hxy⟩
    · intro hyU
      exact hyX (Finset.mem_map.mpr ⟨⟨y, hyR⟩, hyU, rfl⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  have hcardR : (((Qᶜ \ X).filter (fun y => ∃ x ∈ X, H.Adj x y)).card : ℝ) ≤
      ((ComponentObstruction.closedNeighborhood (H.induce (R : Set W)) U \ U).card : ℝ) := by
    exact_mod_cast hcard
  rw [hXc] at hB
  have hφU := mul_nonneg hφ (Nat.cast_nonneg (α := ℝ) U.card)
  linarith

/-- **§3 dense mask.** One fixed sample `Q` at rate `p = 1/(C0 L)` has two-sided
sampled degrees at every original center, two-sided size, at least `2N` induced edges,
and a complement `R = Qᶜ` with residual degree `3d/4`, expansion `3φ/1600` and
`2|R| ≥ N`. -/
theorem exists_dense_mask (H : SimpleGraph W) [DecidableRel H.Adj]
    (a C0 K L φ d p : ℝ) (hN : 0 < Fintype.card W)
    (hlo : ∀ v, d ≤ (H.degree v : ℝ)) (hhi : ∀ v, (H.degree v : ℝ) ≤ 100*d)
    (hcut : ∀ X : Finset W, (X.card : ℝ) ≤ (Fintype.card W : ℝ)/2 →
      φ*d*(X.card : ℝ) ≤ crossing H X)
    (hp : p = 1/(C0*L)) (ha : 0 < a) (hC0 : 800/a ≤ C0)
    (hK1 : 16*C0^2 ≤ K) (hK2 : 64*C0 ≤ K) (hdK : K*L^2 ≤ d)
    (hφa : a/L ≤ φ) (hφ1 : φ ≤ 1) (hL : log (2*(Fintype.card W : ℝ)) ≤ L) :
    ∃ Q R : Finset W, R = Qᶜ ∧
      (∀ v, p*(H.degree v : ℝ)/2 ≤ ((H.neighborFinset v ∩ Q).card : ℝ) ∧
        ((H.neighborFinset v ∩ Q).card : ℝ) ≤ 2*p*(H.degree v : ℝ)) ∧
      (p*(Fintype.card W : ℝ)/2 ≤ (Q.card : ℝ) ∧
        (Q.card : ℝ) ≤ 2*p*(Fintype.card W : ℝ) ∧ 2 ≤ Q.card) ∧
      2*Fintype.card W ≤ inducedEdges H Q ∧
      (∀ v, 3*d/4 ≤ ((H.neighborFinset v ∩ R).card : ℝ)) ∧
      (∀ [Fintype (Set.Elem (R : Set W))] [DecidableEq (Set.Elem (R : Set W))]
        [DecidableRel (H.induce (R : Set W)).Adj],
        CutEscape.Expands (H.induce (R : Set W)) (3*φ/1600)) ∧
      Fintype.card W ≤ 2*R.card := by
  have hNR : (1 : ℝ) ≤ Fintype.card W := by exact_mod_cast hN
  have hL0 : 0 < L := lt_of_lt_of_le (log_pos (by linarith)) hL
  have haL : a ≤ φ*L := (div_le_iff₀ hL0).mp hφa
  have hC0pos : 0 < C0 := lt_of_lt_of_le (by positivity) hC0
  have hC0a : 800 ≤ C0*a := by
    have h := (div_le_iff₀ ha).mp hC0
    linarith
  have hCL : 0 < C0*L := mul_pos hC0pos hL0
  have hpCL : p*(C0*L) = 1 := by
    rw [hp]
    field_simp
  have hp0 : 0 < p := by
    rw [hp]
    positivity
  have hφCL : 800 ≤ φ*(C0*L) := by
    have h := mul_le_mul_of_nonneg_left haL hC0pos.le
    nlinarith
  have hp800 : 800*p ≤ φ := by
    have h := mul_le_mul_of_nonneg_left hφCL hp0.le
    have e : p*(φ*(C0*L)) = φ*(p*(C0*L)) := by ring
    rw [e, hpCL] at h
    linarith
  have hp1 : p ≤ 1 := by linarith
  have hφ0 : 0 ≤ φ := by linarith
  have hL2 : 0 ≤ L^2 := sq_nonneg L
  have hd64 : 64*C0*L^2 ≤ d := le_trans (mul_le_mul_of_nonneg_right hK2 hL2) hdK
  have hd16 : 16*C0^2*L^2 ≤ d := le_trans (mul_le_mul_of_nonneg_right hK1 hL2) hdK
  have hpd : 64*L ≤ p*d := by
    have e : p*(64*C0*L^2) = 64*L := by
      calc
        p*(64*C0*L^2) = 64*L*(p*(C0*L)) := by ring
        _ = 64*L := by rw [hpCL, mul_one]
    calc
      64*L = p*(64*C0*L^2) := e.symm
      _ ≤ p*d := mul_le_mul_of_nonneg_left hd64 hp0.le
  have hp2d : 16 ≤ p^2*d := by
    have e : p^2*(16*C0^2*L^2) = 16 := by
      calc
        p^2*(16*C0^2*L^2) = 16*(p*(C0*L))^2 := by ring
        _ = 16 := by rw [hpCL]; norm_num
    calc
      (16 : ℝ) = p^2*(16*C0^2*L^2) := e.symm
      _ ≤ p^2*d := mul_le_mul_of_nonneg_left hd16 (sq_nonneg p)
  have hd0 : 0 < d := by
    by_contra hneg
    have h := mul_nonpos_of_nonneg_of_nonpos hp0.le (not_lt.mp hneg)
    linarith
  have hbudget := budget_lt_one (Fintype.card W) hN (p*d) L hL hpd
  obtain ⟨Q, hdeg, hQlo, hQhi⟩ := exists_good_mask H p d hp0.le hp1 hN hlo hbudget
  have hcap : ∀ v, ((H.neighborFinset v ∩ Q).card : ℝ) ≤ φ*d/4 := by
    intro v
    have h1 := (hdeg v).2
    have h2 := mul_le_mul_of_nonneg_left (hhi v) hp0.le
    have h3 := mul_le_mul_of_nonneg_right hp800 hd0.le
    linarith
  refine ⟨Q, Qᶜ, rfl, fun v => ⟨(hdeg v).1.le, (hdeg v).2.le⟩, ⟨hQlo.le, hQhi.le, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · -- two sampled vertices: one center already has more than one sampled neighbor
    obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hN
    have h1 := (hdeg v0).1
    have h2 := mul_le_mul_of_nonneg_left (hlo v0) hp0.le
    have hlog2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hL1 : log 2 ≤ L := (log_le_log (by norm_num) (by linarith)).trans hL
    have h3 : (1 : ℝ) < ((H.neighborFinset v0 ∩ Q).card : ℝ) := by linarith
    have h4 : 1 < (H.neighborFinset v0 ∩ Q).card := by exact_mod_cast h3
    exact (show 2 ≤ (H.neighborFinset v0 ∩ Q).card by omega).trans
      (Finset.card_le_card Finset.inter_subset_right)
  · -- (1): e(H[Q]) ≥ (p d/2)|Q|/2 ≥ p² d N/8 ≥ 2N
    have h2 := count_self_eq_twice_edges H Q
    have hcnt : (Q.card : ℝ)*(p*d/2) ≤ (IncidenceCounts.count H Q Q : ℝ) := by
      unfold IncidenceCounts.count
      push_cast
      calc
        (Q.card : ℝ)*(p*d/2) = ∑ _x ∈ Q, p*d/2 := by simp
        _ ≤ ∑ x ∈ Q, ((Q.filter (H.Adj x)).card : ℝ) := Finset.sum_le_sum (fun x _ => by
            rw [filter_adj_eq]
            have := (hdeg x).1
            have := mul_le_mul_of_nonneg_left (hlo x) hp0.le
            linarith)
    have hpd2 : 0 ≤ p*d/2 := by positivity
    have hA := mul_le_mul_of_nonneg_right hQlo.le hpd2
    have hB := mul_le_mul_of_nonneg_right hp2d (Nat.cast_nonneg (α := ℝ) (Fintype.card W))
    have h4 : (4 : ℝ)*Fintype.card W ≤ (IncidenceCounts.count H Q Q : ℝ) := by
      nlinarith
    rw [h2] at h4
    have h5 : 4*Fintype.card W ≤ 2*edges H Q := by exact_mod_cast h4
    change 2*Fintype.card W ≤ edges H Q
    omega
  · -- every original center keeps at least 3d/4 neighbors in R
    intro v
    have hs := Finset.card_sdiff_add_card_inter (H.neighborFinset v) Q
    rw [H.card_neighborFinset_eq_degree, Finset.sdiff_eq_inter_compl] at hs
    have hsR : (((H.neighborFinset v ∩ Qᶜ).card : ℕ) : ℝ) +
        ((H.neighborFinset v ∩ Q).card : ℝ) = (H.degree v : ℝ) := by
      exact_mod_cast hs
    have h1 := hcap v
    have h2 := hlo v
    have h3 := mul_le_mul_of_nonneg_right hφ1 hd0.le
    linarith
  · intro _ _ _
    exact residual_expands H Q Qᶜ rfl φ d hd0 hφ0 hhi hcap hcut
  · -- |Q| < 2pN ≤ N/400, so 2|R| ≥ N
    have hs := Finset.card_compl_add_card Q
    have hsR : ((Qᶜ.card : ℕ) : ℝ) + (Q.card : ℝ) = (Fintype.card W : ℝ) := by
      exact_mod_cast hs
    have h1 := mul_le_mul_of_nonneg_right hp800 (Nat.cast_nonneg (α := ℝ) (Fintype.card W))
    have h2 : (Fintype.card W : ℝ) ≤ 2*(Qᶜ.card : ℝ) := by nlinarith
    exact_mod_cast h2

end Erdos642.DenseMask20261019.MaskCore
