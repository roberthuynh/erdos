import ActualSupport
import SurplusRows
import DeficientNeighborhood
import Parameters

namespace Erdos60.Localization
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def residualFinset (G : SimpleGraph V) (X : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∈ residual G (↑X : Set V)

@[simp] theorem mem_residualFinset (G : SimpleGraph V) (X : Finset V) (v : V) :
    v ∈ residualFinset G X ↔ v ∈ residual G (↑X : Set V) := by
  classical
  simp [residualFinset]

/-- The exact aggregate selection error from source §7 is below Tq. -/
theorem selection_error {q T : ℝ} {m Z : ℕ} (hq : 10^16 ≤ q)
    (hT : 1 ≤ T) (hr : T ≤ q/10^8) (hm : (m : ℝ) ≤ 201*T)
    (hZ : (Z : ℝ) < T*q) :
    (m.choose 2 : ℝ)+2*Real.sqrt ((m.choose 2 : ℝ)*Z) < T*q := by
  have hK0 : (0:ℝ) ≤ m.choose 2 := by positivity
  have hZ0 : (0:ℝ) ≤ Z := by positivity
  have hT0 : 0 ≤ T := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hK : (m.choose 2 : ℝ) ≤ 20201*T^2 := by
    rw [Nat.cast_choose_two]
    have h0 : (0:ℝ) ≤ m := by positivity
    nlinarith [mul_nonneg (show 0 ≤ 201*T-(m : ℝ) by linarith)
      (show 0 ≤ 201*T+(m : ℝ) by positivity)]
  have hprod : (m.choose 2 : ℝ)*Z ≤ 20201*T^2*(T*q) := by
    have h1 := mul_nonneg hZ0 (show 0 ≤ 20201*T^2-(m.choose 2 : ℝ) by linarith)
    have h2 := mul_nonneg (show 0 ≤ 20201*T^2 by positivity)
      (show 0 ≤ T*q-(Z : ℝ) by linarith)
    nlinarith
  have hs0 := Real.sqrt_nonneg ((m.choose 2 : ℝ)*Z)
  have hs2 := Real.sq_sqrt (mul_nonneg hK0 hZ0)
  have ht0 := Real.sqrt_nonneg (T*q)
  have ht2 := Real.sq_sqrt (mul_nonneg hT0 hq0)
  have hscale := congrArg (fun a : ℝ => 81225*T^2*a) ht2
  have hs : 2*Real.sqrt ((m.choose 2 : ℝ)*Z) ≤ 285*T*Real.sqrt (T*q) := by
    have hu0 : 0 ≤ 285*T*Real.sqrt (T*q) := by positivity
    nlinarith [mul_nonneg (show 0 ≤ T^2 by positivity) (show 0 ≤ T*q by positivity)]
  have he := Erdos60.Parameters.aggregate_parameter hq hT hr
  linarith

/-- Actual residual endpoint selection. The transport input is a bound on
neighbors lying in actual C4s, not the number of C4s through the endpoint.
No cardinality bound on the residual set is assumed. -/
theorem residual_card_lt_ceil (G : SimpleGraph V) (X : Finset V) (q T : ℝ)
    (hq : 10^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ q/10^8)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    (htransport : ∀ v ∈ residualFinset G X,
      q/20 ≤ ((G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card : ℝ)) :
    (residualFinset G X).card < ⌈200*T⌉₊ := by
  classical
  by_contra hn
  have hbig : ⌈200*T⌉₊ ≤ (residualFinset G X).card := by omega
  obtain ⟨I, hI, hcard⟩ := Finset.exists_subset_card_eq hbig
  have hmlo : 200*T ≤ (I.card : ℝ) := by
    rw [hcard]
    exact Nat.le_ceil (200*T)
  have hmhi : (I.card : ℝ) ≤ 201*T := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 200*T by linarith)
    rw [hcard]
    linarith
  have hlo : 10*T*q ≤ ∑ v ∈ I,
      ((G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card : ℝ) := by
    have hh := Finset.sum_le_sum (s := I) (fun v hv => htransport v (hI hv))
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    have hp := mul_nonneg (show 0 ≤ (I.card : ℝ)-200*T by linarith)
      (show 0 ≤ q by linarith)
    nlinarith
  have hu := SurplusRows.neighbor_union_bound G I (Statistics.positiveCycleVertices G)
  have hu' : (∑ v ∈ I, ((G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card : ℝ)) ≤
      (Statistics.positiveCycleVertices G).card+
      ∑ p ∈ Statistics.subsetPairs I, (Statistics.pairCodegree G p : ℝ) := by
    exact_mod_cast hu
  have hp := Statistics.positiveCycleVertices_card G
  have hp' : ((Statistics.positiveCycleVertices G).card : ℝ) ≤ 4*Counting.cycleCount G := by
    exact_mod_cast hp
  have ho := Statistics.subset_codegree_overlap G I
  have he := selection_error hq hT hr hmhi hZ
  have hpos : 0 < T*q := mul_pos (by linarith) (by linarith)
  linarith

/-- The same actual support X∪R has the promised 252T vertices. -/
theorem residual_support_card (G : SimpleGraph V) (X : Finset V) (q T : ℝ)
    (hq : 10^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ q/10^8)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    (hX : (X.card : ℝ) ≤ 51*T)
    (htransport : ∀ v ∈ residualFinset G X,
      q/20 ≤ ((G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card : ℝ)) :
    ((X ∪ residualFinset G X).card : ℝ) ≤ 252*T := by
  have hR := residual_card_lt_ceil G X q T hq hT hr hZ htransport
  have hR' : ((residualFinset G X).card : ℝ) < ⌈200*T⌉₊ := by exact_mod_cast hR
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 200*T by linarith)
  have hU := Finset.card_union_le X (residualFinset G X)
  have hU' : ((X ∪ residualFinset G X).card : ℝ) ≤ X.card+(residualFinset G X).card := by
    exact_mod_cast hU
  linarith

theorem opposite_symm (G : SimpleGraph V) {u v : V} (h : Opposite G u v) :
    Opposite G v u := by
  obtain ⟨hne,a,b,hab,hua,hva,hub,hvb⟩ := h
  exact ⟨hne.symm,a,b,hab,hva,hua,hvb,hub⟩

/-- The ordered-pair transport theorem feeds the actual residual selection.
The opposite mate is chosen from the definition of R, on the same graph. -/
theorem residual_support_of_opposite_transport (G : SimpleGraph V) (X : Finset V) (q T : ℝ)
    (hq : 10^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ q/10^8)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) (hX : (X.card : ℝ) ≤ 51*T)
    (htransport : ∀ u v : V, u ∉ X → v ∉ X → Opposite G u v →
      q/20 ≤ ((G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card : ℝ)) :
    ((X ∪ residualFinset G X).card : ℝ) ≤ 252*T := by
  apply residual_support_card G X q T hq hT hr hZ hX
  intro v hv
  obtain ⟨hvX,u,huX,hop⟩ := (mem_residualFinset G X v).mp hv
  exact htransport u v huX hvX (opposite_symm G hop)

/-- Quantitative version of the actual support theorem: the one selected
set has at most 252T vertices and meets every ordinary C4 in an actual edge. -/
theorem quantitative_cycle_support (G : SimpleGraph V) (X : Finset V) (q T : ℝ)
    (hq : 10^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ q/10^8)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) (hX : (X.card : ℝ) ≤ 51*T)
    (htransport : ∀ u v : V, u ∉ X → v ∉ X → Opposite G u v →
      q/20 ≤ ((G.neighborFinset v ∩ Statistics.positiveCycleVertices G).card : ℝ)) :
    ∃ S0 : Finset V, (S0.card : ℝ) ≤ 252*T ∧
      ∀ a b c d : V, a ≠ c → b ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
        (a ∈ S0 ∧ b ∈ S0) ∨ (b ∈ S0 ∧ c ∈ S0) ∨
        (c ∈ S0 ∧ d ∈ S0) ∨ (d ∈ S0 ∧ a ∈ S0) := by
  refine ⟨X ∪ residualFinset G X,
    residual_support_of_opposite_transport G X q T hq hT hr hZ hX htransport, ?_⟩
  intro a b c d hac hbd hab hbc hcd hda
  have hh := cycle_has_support_edge G (↑X : Set V) hac hbd hab hbc hcd hda
  simpa only [support, Set.mem_union, Finset.mem_union, mem_residualFinset,
    Finset.mem_coe] using hh

#print axioms residual_card_lt_ceil
#print axioms residual_support_card
#print axioms quantitative_cycle_support
end Erdos60.Localization
