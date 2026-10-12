import AllHTopTwo.Geometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHTopTwo
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A forbidden set comes from at most one actual original weak row. -/
structure Neighborhood (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B N : Finset V) : Prop where
  subset : N ⊆ B
  size : #N ≤ q + j - 1
  covers : ∀ a ∈ A, dg G B a ≤ q + j - 1 → ∀ b ∈ B, G.Adj a b → b ∈ N
  origin : N = ∅ ∨ ∃ a ∈ A, dg G B a ≤ q + j - 1 ∧ N = B.filter (G.Adj a)

namespace Data
variable {h q j : ℕ} {A B : Finset V} (d : Data h q j G A B)
include d

omit [DecidableEq V] in
lemma theta_small_bound {T : Finset V} (hsize : #T ≤ q - 2) :
    thetaJ q j G A B T ≤ (h : ℤ) * q - offset h + j - q * #T := by
  have hq := d.parameters.q_ge_height
  have hphi : ∀ a ∈ A, max 0 (row q G B T a) ≤ 2 * (q : ℤ) - 2 - dg G B a := by
    intro a ha
    have hd := dg_le_card (G := G) T a
    have hc := d.capA_int ha
    unfold row
    omega
  have hsum : (∑ a ∈ A, max 0 (row q G B T a)) ≤
      (h : ℤ) * q - offset h - ((q : ℤ) - 1) * j := by
    calc
      _ ≤ deficiency (2 * (q : ℤ) - 2) G B A := sum_le_sum hphi
      _ = _ := d.deficient
  unfold thetaJ theta
  nlinarith

omit [DecidableEq V] in
lemma theta_intermediate {T : Finset V} (hlo : h ≤ #T) (hhi : #T ≤ q - 2) :
    thetaJ q j G A B T ≤ (j : ℤ) - offset h := by
  have hh := d.theta_small_bound hhi
  have hp : 0 ≤ (q : ℤ) * ((#T : ℤ) - h) :=
    mul_nonneg (Nat.cast_nonneg _) (by omega)
  nlinarith

lemma tiny_card {T : Finset V} (hsize : #T < h) : #(canonical q G A B T) ≤ 1 := by
  have hq := d.parameters.q_ge_height
  have hs := d.parameters.scar_tiny
  have hc := canonical_subset (G := G) q A B T
  have hrow : ∀ a ∈ canonical q G A B T,
      (q : ℤ) - h ≤ 2 * (q : ℤ) - 2 - dg G B a := by
    intro a ha
    have hp := (mem_filter.mp ha).2
    have hd := dg_le_card (G := G) T a
    unfold row at hp
    omega
  have hlo : ((q : ℤ) - h) * #(canonical q G A B T) ≤
      deficiency (2 * (q : ℤ) - 2) G B (canonical q G A B T) := by
    calc
      _ = ∑ _a ∈ canonical q G A B T, ((q : ℤ) - h) := by
        simp only [sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := sum_le_sum hrow
  have hhi := d.scar_le hc
  by_contra! hbad
  have hm : 0 ≤ ((q : ℤ) - h) * ((#(canonical q G A B T) : ℤ) - 2) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

lemma theta_tiny_bound {T : Finset V} (hsize : #T < h) :
    thetaJ q j G A B T ≤ (q : ℤ) * j - q * #T + #T := by
  have hc := d.tiny_card hsize
  have hs : (∑ a ∈ canonical q G A B T, row q G B T a) ≤
      (#T : ℤ) * #(canonical q G A B T) := by
    calc
      _ ≤ ∑ _a ∈ canonical q G A B T, (#T : ℤ) := by
        apply sum_le_sum
        intro a ha
        have hm := d.minA a ((canonical_subset q A B T) ha)
        have hd := dg_le_card (G := G) T a
        unfold row
        omega
      _ = _ := by simp [mul_comm]
  have hmul : (#T : ℤ) * #(canonical q G A B T) ≤ #T := by
    nlinarith [mul_nonneg (Nat.cast_nonneg #T : (0 : ℤ) ≤ #T)
      (show 0 ≤ 1 - (#(canonical q G A B T) : ℤ) by omega)]
  rw [thetaJ_canonical]
  omega

lemma theta_tiny_le {T : Finset V} (hsize : #T < h) :
    thetaJ q j G A B T ≤ (q : ℤ) * j := by
  have ht := d.theta_tiny_bound hsize
  have hq := d.parameters.q_pos
  have hm : 0 ≤ ((q : ℤ) - 1) * #T :=
    mul_nonneg (by omega) (Nat.cast_nonneg _)
  nlinarith

lemma weak_unique {a b : V} (ha : a ∈ A) (hb : b ∈ A)
    (hda : dg G B a ≤ q + j - 1) (hdb : dg G B b ≤ q + j - 1) : a = b := by
  by_contra hne
  have hs := d.scar_le (show ({a, b} : Finset V) ⊆ A from
    insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩)
  have hq := d.parameters.q_pos
  have hj := d.parameters.j_pos
  have hΔ := d.parameters.scar_weak
  simp [deficiency, hne] at hs
  have hsa : (q : ℤ) - j - 1 ≤ 2 * (q : ℤ) - 2 - dg G B a := by omega
  have hsb : (q : ℤ) - j - 1 ≤ 2 * (q : ℤ) - 2 - dg G B b := by omega
  omega

lemma exists_neighborhood : ∃ N : Finset V, Neighborhood q j G A B N := by
  by_cases hw : ∃ a ∈ A, dg G B a ≤ q + j - 1
  · obtain ⟨a, ha, hda⟩ := hw
    let N := B.filter (G.Adj a)
    refine ⟨N, filter_subset _ _, ?_, ?_, Or.inr ⟨a, ha, hda, rfl⟩⟩
    · exact hda
    · intro b hb hdb z hz hadj
      have he := d.weak_unique hb ha hdb hda
      subst b
      exact mem_filter.mpr ⟨hz, hadj⟩
  · refine ⟨∅, empty_subset _, by simp, ?_, Or.inl rfl⟩
    intro a ha hda
    exact False.elim (hw ⟨a, ha, hda⟩)

lemma neighborhood_available {N : Finset V} (hn : Neighborhood q j G A B N) : j ≤ #(B \ N) := by
  have hb := d.shore_near_double
  have hc := card_sdiff_add_card_eq_card hn.subset
  have hN := hn.size
  have hq := d.parameters.numeric
  have hj := d.parameters.j_bounds
  omega

omit [DecidableEq V] in
lemma neighborhood_cut {N T : Finset V} (hn : Neighborhood q j G A B N)
    (hT : T ⊆ B) (hsize : #T = j) (hdis : Disjoint T N) : thetaJ q j G A B T = 0 := by
  have hrow : ∀ a ∈ A, max 0 (row q G B T a) = 0 := by
    intro a ha
    apply max_eq_left
    by_contra! hp
    have hd := dg_le_card (G := G) T a
    have hq := d.parameters.q_pos
    have hj := d.parameters.j_pos
    have hweak : dg G B a ≤ q + j - 1 := by unfold row at hp; omega
    have hz : dg G T a = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨hbt, hadj⟩ := mem_filter.mp hb
      exact disjoint_left.mp hdis hbt (hn.covers a ha hweak b (hT hbt) hadj)
    have hm := d.minA a ha
    unfold row at hp
    omega
  unfold thetaJ theta
  rw [sum_eq_zero hrow, hsize]
  ring

lemma small_good {N O T : Finset V} (hn : Neighborhood q j G A B N)
    (hO : O ⊆ B \ N) (hOj : #O = j) (hT : T ⊆ B) (hOT : O ⊆ T)
    (hsmall : #T ≤ q - 2) : thetaJ q j G A B T ≤ 0 := by
  have hjt : j ≤ #T := by rw [← hOj]; exact card_le_card hOT
  by_cases htiny : #T < h
  · by_cases heq : #T = j
    · have hot : O = T := eq_of_subset_of_card_le hOT (by omega)
      have hdis : Disjoint T N := by
        rw [← hot]
        exact disjoint_left.mpr fun _ hv hN => (mem_sdiff.mp (hO hv)).2 hN
      rw [d.neighborhood_cut hn hT heq hdis]
    · have ht := d.theta_tiny_bound htiny
      have hq := d.parameters.q_ge_height
      have hm : 0 ≤ (q : ℤ) * ((#T : ℤ) - j - 1) :=
        mul_nonneg (Nat.cast_nonneg _) (by omega)
      nlinarith
  · have ht := d.theta_intermediate (by omega) hsmall
    have hn := d.parameters.numeric
    have hj := d.parameters.j_bounds
    omega

lemma row_scar_le_set {X : Finset V} (hX : X ⊆ A) {a : V} (ha : a ∈ X) :
    2 * (q : ℤ) - 2 - dg G B a ≤ deficiency (2 * (q : ℤ) - 2) G B X := by
  have hs := deficiency_le_subset (2 * (q : ℤ) - 2) (singleton_subset_iff.mpr ha)
    (fun b hb => d.capA_int (hX hb))
  simpa [deficiency] using hs

lemma neighborhood_residual {N K : Finset V} (hn : Neighborhood q j G A B N)
    (hK : K ⊆ B) (hlarge : q - 1 ≤ #K) (hp : 0 < thetaJ q j G A B K) :
    #(N \ K) ≤ 3 * h := by
  rcases hn.origin with hz | ⟨a, ha, hda, hN⟩
  · simp [hz]
  · have hC : a ∈ weakCore q G A B K := by
      by_contra hbad
      have haL : a ∈ A \ weakCore q G A B K := mem_sdiff.mpr ⟨ha, hbad⟩
      have hs := d.row_scar_le_set (sdiff_subset : A \ weakCore q G A B K ⊆ A) haL
      have hhi := d.outside_scar_le (weak_optimizer q A B K) hK hlarge hp
      have hq := d.parameters.numeric
      have hj := d.parameters.j_bounds
      have hq0 := d.parameters.q_pos
      have hj0 := d.parameters.j_pos
      omega
    have hd := d.optimizer_internal_min_coarse (weak_optimizer q A B K) hK hlarge hp hC
    have he := dg_sdiff_add (G := G) hK a
    have hj := d.parameters.j_bounds
    have hq0 := d.parameters.q_pos
    have hj0 := d.parameters.j_pos
    have heN : N \ K = (B \ K).filter (G.Adj a) := by
      rw [hN]
      ext b
      simp only [mem_sdiff, mem_filter]
      tauto
    rw [heN]
    change dg G (B \ K) a ≤ 3 * h
    omega

end Data
end Erdos585.AllHTopTwo
