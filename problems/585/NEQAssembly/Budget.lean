import NEQAssembly.Components

/-! Original component boundary/parity/budget.
No generic factor criterion or normalization premise is invoked. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.NEQAssembly
open QB4 B5 NEQ
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma disjoint_shore_remainder (S T : Finset V) :
    Disjoint S (univ \ (S ∪ T)) ∧ Disjoint T (univ \ (S ∪ T)) ∧
      (S ∪ T) ∪ (univ \ (S ∪ T)) = univ := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hv hvR
    exact (mem_sdiff.mp hvR).2 (mem_union_left T hv)
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hv hvR
    exact (mem_sdiff.mp hvR).2 (mem_union_right S hv)
  · ext v
    simp only [mem_union, mem_sdiff, mem_univ, true_and, iff_true]
    exact Classical.em _

lemma component_boundary (D : ℤ) (S T R : Finset V)
    (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (hcover : (S ∪ T) ∪ R = univ)
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    D * (#(componentVerts G R C) : ℤ) - ec G (componentVerts G R C) (componentVerts G R C) =
      deficiency D G univ (componentVerts G R C) +
      ec G (componentVerts G R C) S + ec G (componentVerts G R C) T := by
  have hUR : Disjoint (S ∪ T) R := Finset.disjoint_union_left.mpr ⟨hSR, hTR⟩
  have hsplit : ec G (componentVerts G R C) univ =
      ec G (componentVerts G R C) S + ec G (componentVerts G R C) T +
      ec G (componentVerts G R C) (componentVerts G R C) := by
    rw [← hcover, ec_union_right hUR, ec_union_right hST, component_internal_eq]
  have hsplitZ : (ec G (componentVerts G R C) univ : ℤ) =
      (ec G (componentVerts G R C) S : ℤ) + ec G (componentVerts G R C) T +
      ec G (componentVerts G R C) (componentVerts G R C) := by exact_mod_cast hsplit
  have hdef := deficiency_eq (G := G) D univ (componentVerts G R C)
  linarith

lemma count_mod_two (a : ℕ) :
    (0 : ℤ) ≤ (a % 2 : ℕ) ∧ (a % 2 : ℤ) ≤ 1 ∧
      0 ≤ (a : ℤ) - (a % 2 : ℕ) ∧ Even ((a : ℤ) - (a % 2 : ℕ)) := by
  refine ⟨by positivity, by omega, by omega, ?_⟩
  refine ⟨(a / 2 : ℕ), ?_⟩
  omega

lemma mod_two_indicator (a : ℕ) : a % 2 = if Odd a then 1 else 0 := by
  by_cases ha : Odd a
  · simp only [ha, if_true]
    exact Nat.odd_iff.mp ha
  · simp only [ha, if_false]
    have h := Nat.odd_iff.not.mp ha
    omega

lemma oddCount_eq_sum_mod (S R : Finset V)
    [Fintype (G.induce (R : Set V)).ConnectedComponent] :
    oddCount G S R = ∑ C : (G.induce (R : Set V)).ConnectedComponent,
      ec G (componentVerts G R C) S % 2 := by
  unfold oddCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [mod_two_indicator]
  simp

lemma component_charge_nonneg (q : ℕ) (hq : 6 ≤ q)
    (hcap : G.maxDegree ≤ 2 * q - 2) (S T R : Finset V)
    (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (hcover : (S ∪ T) ∪ R = univ)
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    Even (deficiency (2 * (q : ℤ) - 2) G univ (componentVerts G R C) +
      (ec G (componentVerts G R C) T : ℤ) - (ec G (componentVerts G R C) S % 2 : ℕ)) ∧
    0 ≤ deficiency (2 * (q : ℤ) - 2) G univ (componentVerts G R C) +
      (ec G (componentVerts G R C) T : ℤ) - (ec G (componentVerts G R C) S % 2 : ℕ) := by
  have hbound : ∀ v : V, (dg G univ v : ℤ) ≤ 2 * (q : ℤ) - 2 := by
    intro v
    have h := (dg_le_maxDegree univ v).trans hcap
    omega
  have hd : 0 ≤ deficiency (2 * (q : ℤ) - 2) G univ (componentVerts G R C) :=
    deficiency_nonneg (2 * (q : ℤ) - 2) (fun v _ => hbound v)
  have hboundary := component_boundary (G := G) (2 * (q : ℤ) - 2) S T R hST hSR hTR hcover C
  obtain ⟨b, hb⟩ := ec_self_even (G := G) (componentVerts G R C)
  have hbZ : (ec G (componentVerts G R C) (componentVerts G R C) : ℤ) = (b : ℤ) + b :=
    by exact_mod_cast hb
  have heven : Even (deficiency (2 * (q : ℤ) - 2) G univ (componentVerts G R C) +
      (ec G (componentVerts G R C) S : ℤ) + ec G (componentVerts G R C) T) := by
    refine ⟨((q : ℤ) - 1) * #(componentVerts G R C) - b, ?_⟩
    nlinarith
  have hp := count_mod_two (ec G (componentVerts G R C) S)
  exact NEQ.component_charge_nonnegative hd (by positivity) hp.1 hp.2.1 heven hp.2.2.2

lemma component_residual_sum (S R : Finset V)
    [Fintype (G.induce (R : Set V)).ConnectedComponent] :
    (∑ C : (G.induce (R : Set V)).ConnectedComponent,
      ((ec G (componentVerts G R C) S : ℤ) - (ec G (componentVerts G R C) S % 2 : ℕ))) =
      (ec G S R : ℤ) - oddCount G S R := by
  rw [sum_sub_distrib, sum_component_ec, oddCount_eq_sum_mod, Nat.cast_sum,
    ec_comm (G := G) R S]

lemma oddCount_le_ec (S R : Finset V)
    [Fintype (G.induce (R : Set V)).ConnectedComponent] :
    oddCount G S R ≤ ec G S R := by
  have hs := sum_nonneg (s := (univ : Finset (G.induce (R : Set V)).ConnectedComponent))
    (fun C _ => (count_mod_two (ec G (componentVerts G R C) S)).2.2.1)
  rw [component_residual_sum] at hs
  omega

lemma barrier_even (q : ℕ) (heven : Even q) (S T : Finset V)
    [Fintype (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent] :
    Even (NEQ.delta q G univ S T) := by
  let R : Finset V := univ \ (S ∪ T)
  have hres : Even ((ec G S R : ℤ) - oddCount G S R) := by
    rw [← component_residual_sum]
    refine ⟨∑ C : (G.induce (R : Set V)).ConnectedComponent,
      ((ec G (componentVerts G R C) S / 2 : ℕ) : ℤ), ?_⟩
    rw [← two_mul, mul_sum]
    apply sum_congr rfl
    intro C _
    omega
  obtain ⟨j, hj⟩ := heven
  obtain ⟨a, ha⟩ := ec_self_even (G := G) S
  obtain ⟨b, hb⟩ := hres
  have hjZ : (q : ℤ) = (j : ℤ) + j := by exact_mod_cast hj
  have haZ : (ec G S S : ℤ) = (a : ℤ) + a := by exact_mod_cast ha
  refine ⟨(j : ℤ) * ((#T : ℤ) - #S) + a + b, ?_⟩
  change (q : ℤ) * ((#T : ℤ) - #S) + ec G S S + ec G S R - oddCount G S R = _
  nlinarith

lemma negative_barrier_bounds (q : ℕ) (heven : Even q) (S T : Finset V)
    [Fintype (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent]
    (hnegative : NEQ.delta q G univ S T < 0) :
    NEQ.delta q G univ S T ≤ -2 ∧ 1 ≤ (#S : ℤ) - #T := by
  have he := barrier_even (G := G) q heven S T
  obtain ⟨j, hj⟩ := he
  have hdelta : NEQ.delta q G univ S T ≤ -2 := by omega
  refine ⟨hdelta, ?_⟩
  have htau := oddCount_le_ec (G := G) S (univ \ (S ∪ T))
  have hSS : 0 ≤ (ec G S S : ℤ) := by positivity
  by_contra! hsmall
  have hp : 0 ≤ (q : ℤ) * ((#T : ℤ) - #S) :=
    mul_nonneg (by positivity) (by omega)
  unfold NEQ.delta at hdelta
  omega

lemma original_component_budget (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (hexact : G.edgeSet.ncard + q / 2 = (q - 1) * Fintype.card V)
    (S T : Finset V) (hST : Disjoint S T)
    [Fintype (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent] :
    (q : ℤ) = ((q : ℤ) - 2) * ((#S : ℤ) - #T) - NEQ.delta q G univ S T +
      2 * deficiency (2 * (q : ℤ) - 2) G univ T + (ec G T T : ℤ) +
      ∑ C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent,
        (deficiency (2 * (q : ℤ) - 2) G univ (componentVerts G (univ \ (S ∪ T)) C) +
          (ec G (componentVerts G (univ \ (S ∪ T)) C) T : ℤ) -
          (ec G (componentVerts G (univ \ (S ∪ T)) C) S % 2 : ℕ)) := by
  let R : Finset V := univ \ (S ∪ T)
  let D : ℤ := 2 * (q : ℤ) - 2
  have hp := disjoint_shore_remainder S T
  have hSR : Disjoint S R := hp.1
  have hTR : Disjoint T R := hp.2.1
  have hcover : (S ∪ T) ∪ R = univ := hp.2.2
  have hUR : Disjoint (S ∪ T) R := Finset.disjoint_union_left.mpr ⟨hSR, hTR⟩
  have htotal : deficiency D G univ univ = q := exact_density_deficiency q hq heven hexact
  have hparts : deficiency D G univ S + deficiency D G univ T + deficiency D G univ R = q := by
    have h := deficiency_union (G := G) D univ hUR
    rw [hcover, deficiency_union (G := G) D univ hST] at h
    exact h.symm.trans htotal
  have hSU : ec G S univ = ec G S S + ec G S T + ec G S R := by
    rw [← hcover, ec_union_right hUR S, ec_union_right hST S]
  have hTU : ec G T univ = ec G S T + ec G T T + ec G T R := by
    rw [← hcover, ec_union_right hUR T, ec_union_right hST T,
      ec_comm (G := G) T S]
  have hSUZ : (ec G S univ : ℤ) = (ec G S S : ℤ) + ec G S T + ec G S R := by exact_mod_cast hSU
  have hTUZ : (ec G T univ : ℤ) = (ec G S T : ℤ) + ec G T T + ec G T R := by exact_mod_cast hTU
  have hsum : (∑ C : (G.induce (R : Set V)).ConnectedComponent,
      (deficiency D G univ (componentVerts G R C) + (ec G (componentVerts G R C) T : ℤ) -
        (ec G (componentVerts G R C) S % 2 : ℕ))) =
      deficiency D G univ R + (ec G T R : ℤ) - oddCount G S R := by
    rw [sum_sub_distrib, sum_add_distrib, sum_component_deficiency, sum_component_ec,
      ← Nat.cast_sum, ← oddCount_eq_sum_mod, ec_comm (G := G) R T]
  rw [hsum]
  have hdefS := deficiency_eq (G := G) D univ S
  have hdefT := deficiency_eq (G := G) D univ T
  dsimp [D] at hparts hdefS hdefT
  unfold NEQ.delta
  nlinarith

#print axioms disjoint_shore_remainder
#print axioms component_boundary
#print axioms count_mod_two
#print axioms mod_two_indicator
#print axioms oddCount_eq_sum_mod
#print axioms component_charge_nonneg
#print axioms component_residual_sum
#print axioms oddCount_le_ec
#print axioms barrier_even
#print axioms negative_barrier_bounds
#print axioms original_component_budget
end Erdos585.NEQAssembly
