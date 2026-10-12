import NEQAssembly.Budget

/-! Actual component-empty theorem and factor caller.
Proper original floors and actual negative cut are explicit intermediate
premises, not hidden bare endpoint inputs or supplied factor success. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.NEQAssembly
open QB4 B5 NEQ
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem component_empty (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (hcap : G.maxDegree ≤ 2 * q - 2)
    (hexact : G.edgeSet.ncard + q / 2 = (q - 1) * Fintype.card V)
    (hfloor : ∀ X : Finset V, X.Nonempty → X ≠ univ →
      (q : ℤ) + 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec G X X : ℤ))
    (S T : Finset V) (hST : Disjoint S T) (hnegative : NEQ.delta q G univ S T < 0) :
    S ∪ T = univ ∧ (q : ℤ) * ((#T : ℤ) - #S) + (ec G S S : ℤ) ≤ -2 := by
  let R : Finset V := univ \ (S ∪ T)
  let D : ℤ := 2 * (q : ℤ) - 2
  letI : Fintype (G.induce (R : Set V)).ConnectedComponent := Fintype.ofFinite _
  let charge (C : (G.induce (R : Set V)).ConnectedComponent) : ℤ :=
    deficiency D G univ (componentVerts G R C) + (ec G (componentVerts G R C) T : ℤ) -
      (ec G (componentVerts G R C) S % 2 : ℕ)
  have hp := disjoint_shore_remainder S T
  have hSR : Disjoint S R := hp.1
  have hTR : Disjoint T R := hp.2.1
  have hcover : (S ∪ T) ∪ R = univ := hp.2.2
  have hall : ∀ C : (G.induce (R : Set V)).ConnectedComponent, 0 ≤ charge C := by
    intro C
    exact (component_charge_nonneg q hq hcap S T R hST hSR hTR hcover C).2
  have hsum : 0 ≤ ∑ C, charge C := sum_nonneg (fun C _ => hall C)
  have hTT : 0 ≤ (ec G T T : ℤ) := by positivity
  have hbound : ∀ v : V, (dg G univ v : ℤ) ≤ D := by
    intro v
    have h := (dg_le_maxDegree univ v).trans hcap
    dsimp [D]
    omega
  have hDT : 0 ≤ deficiency D G univ T := deficiency_nonneg D (fun v _ => hbound v)
  have hneg := negative_barrier_bounds (G := G) q heven S T hnegative
  have hid : (q : ℤ) = ((q : ℤ) - 2) * ((#S : ℤ) - #T) - NEQ.delta q G univ S T +
      2 * deficiency D G univ T + (ec G T T : ℤ) + ∑ C, charge C :=
    original_component_budget q hq heven hexact S T hST
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  have hb := budget_classification hqZ hneg.2 hneg.1 hDT (by norm_num : (0 : ℤ) ≤ 0)
    (add_nonneg hTT hsum) (by simpa only [mul_zero, add_zero, add_assoc] using hid)
  have hk1 : (#S : ℤ) - #T = 1 := hb.1
  have hdelta : NEQ.delta q G univ S T = -2 := hb.2.1
  have hzero : (ec G T T : ℤ) + ∑ C, charge C = 0 := hb.2.2.2.2
  have hsumzero : ∑ C, charge C = 0 := by omega
  have hchargezero : ∀ C, charge C = 0 := by
    intro C
    exact (sum_eq_zero_iff_of_nonneg (fun E _ => hall E)).mp hsumzero C (mem_univ _)
  have hres : (ec G S S : ℤ) +
      ∑ C : (G.induce (R : Set V)).ConnectedComponent,
        ((ec G (componentVerts G R C) S : ℤ) - (ec G (componentVerts G R C) S % 2 : ℕ)) =
      (q : ℤ) - 2 := by
    rw [component_residual_sum]
    unfold NEQ.delta at hdelta
    nlinarith
  have hSnonempty : S.Nonempty := card_pos.mp (by omega)
  have hRempty : R = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    let C := (G.induce (R : Set V)).connectedComponentMk ⟨v, hv⟩
    have hCnonempty := componentVerts_nonempty C
    have hCproper : componentVerts G R C ≠ univ := by
      intro heq
      obtain ⟨s, hs⟩ := hSnonempty
      have hsC : s ∈ componentVerts G R C := by rw [heq]; exact mem_univ _
      exact Finset.disjoint_left.mp hSR hs (componentVerts_subset C hsC)
    have hf := hfloor (componentVerts G R C) hCnonempty hCproper
    have hc := component_boundary (G := G) D S T R hST hSR hTR hcover C
    have hfloorC : (q : ℤ) + 2 ≤ deficiency D G univ (componentVerts G R C) +
        (ec G (componentVerts G R C) S : ℤ) + ec G (componentVerts G R C) T := by
      dsimp [D] at hc
      linarith
    have heps := count_mod_two (ec G (componentVerts G R C) S)
    have ha : (q : ℤ) ≤ (ec G (componentVerts G R C) S : ℤ) -
        (ec G (componentVerts G R C) S % 2 : ℕ) :=
      component_exceeds_residual heps.1 heps.2.1 hfloorC (hchargezero C)
    have hs := single_le_sum
      (s := (univ : Finset (G.induce (R : Set V)).ConnectedComponent))
      (fun E _ => (count_mod_two (ec G (componentVerts G R E) S)).2.2.1) (mem_univ C)
    have hSS : 0 ≤ (ec G S S : ℤ) := by positivity
    linarith
  have hfull : S ∪ T = univ := by
    apply eq_univ_of_forall
    intro v
    by_contra hv
    have hr : v ∈ R := mem_sdiff.mpr ⟨mem_univ _, hv⟩
    rw [hRempty] at hr
    exact Finset.notMem_empty _ hr
  have hSRzero : ec G S R = 0 := by rw [hRempty]; simp [ec, dg]
  have htau := oddCount_le_ec (G := G) S R
  have htauzero : oddCount G S R = 0 := by omega
  have hdeltaEq : NEQ.delta q G univ S T =
      (q : ℤ) * ((#T : ℤ) - #S) + (ec G S S : ℤ) := by
    unfold NEQ.delta
    change (q : ℤ) * ((#T : ℤ) - #S) + ec G S S + ec G S R - oddCount G S R = _
    rw [hSRzero, htauzero]
    ring
  exact ⟨hfull, by rw [← hdeltaEq]; exact hneg.1⟩

theorem regular_of_critical_barrier (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (hexact : G.edgeSet.ncard + q / 2 = (q - 1) * Fintype.card V)
    (hfloor : ∀ X : Finset V, X.Nonempty → X ≠ univ →
      (q : ℤ) + 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec G X X : ℤ))
    (S T : Finset V) (hST : Disjoint S T) (hnegative : NEQ.delta q G univ S T < 0) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  have h := component_empty q hq heven hcap hexact hfloor S T hST hnegative
  exact neq_of_empty_barrier q hq heven G hn hcap hexact S T hST h.1 h.2

#print axioms component_empty
#print axioms regular_of_critical_barrier
end Erdos585.NEQAssembly
