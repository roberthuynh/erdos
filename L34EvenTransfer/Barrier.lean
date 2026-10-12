import NEQAssembly.Budget
import L34.Main

/- 

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.L34EvenTransfer
open QB4 B5 NEQ NEQAssembly
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exact_density_deficiency (q : ℕ) (hq : 6 ≤ q)
    (he : G.edgeSet.ncard + (q - 2) = (q - 1) * Fintype.card V) :
    deficiency (2 * (q : ℤ) - 2) G univ univ = 2 * (q : ℤ) - 4 := by
  rw [total_deficiency]
  have hp := Bq.pred_cast (by omega : 5 ≤ q)
  have hc : ((q - 2 : ℕ) : ℤ) = (q : ℤ) - 2 := by omega
  zify at he
  rw [hp, hc] at he
  nlinarith

lemma original_component_budget (q : ℕ) (hq : 6 ≤ q)
    (hexact : G.edgeSet.ncard + (q - 2) = (q - 1) * Fintype.card V)
    (S T : Finset V) (hST : Disjoint S T)
    [Fintype (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent] :
    2 * (q : ℤ) - 4 = ((q : ℤ) - 2) * ((#S : ℤ) - #T) - NEQ.delta q G univ S T +
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
  have htotal : deficiency D G univ univ = 2 * (q : ℤ) - 4 :=
    exact_density_deficiency q hq hexact
  have hparts : deficiency D G univ S + deficiency D G univ T +
      deficiency D G univ R = 2 * (q : ℤ) - 4 := by
    have h := deficiency_union (G := G) D univ hUR
    rw [hcover, deficiency_union (G := G) D univ hST] at h
    exact h.symm.trans htotal
  have hSU : ec G S univ = ec G S S + ec G S T + ec G S R := by
    rw [← hcover, ec_union_right hUR S, ec_union_right hST S]
  have hTU : ec G T univ = ec G S T + ec G T T + ec G T R := by
    rw [← hcover, ec_union_right hUR T, ec_union_right hST T, ec_comm (G := G) T S]
  have hSUZ : (ec G S univ : ℤ) = (ec G S S : ℤ) + ec G S T + ec G S R :=
    by exact_mod_cast hSU
  have hTUZ : (ec G T univ : ℤ) = (ec G S T : ℤ) + ec G T T + ec G T R :=
    by exact_mod_cast hTU
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

theorem component_empty (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (hcap : G.maxDegree ≤ 2 * q - 2)
    (hexact : G.edgeSet.ncard + (q - 2) = (q - 1) * Fintype.card V)
    (hfloor : ∀ X : Finset V, X.Nonempty → X ≠ univ →
      2 * (q : ℤ) - 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec G X X : ℤ))
    (S T : Finset V) (hST : Disjoint S T) (hnegative : NEQ.delta q G univ S T < 0) :
    S ∪ T = univ ∧ #S = #T + 1 ∧
      (ec G S S : ℤ) ≤ (q : ℤ) - 2 ∧
      2 * deficiency (2 * (q : ℤ) - 2) G univ T + (ec G T T : ℤ) ≤ (q : ℤ) - 4 := by
  let R : Finset V := univ \ (S ∪ T)
  let D : ℤ := 2 * (q : ℤ) - 2
  letI : Fintype (G.induce (R : Set V)).ConnectedComponent := Fintype.ofFinite _
  let charge (C : (G.induce (R : Set V)).ConnectedComponent) : ℤ :=
    deficiency D G univ (componentVerts G R C) + (ec G (componentVerts G R C) T : ℤ) -
      (ec G (componentVerts G R C) S % 2 : ℕ)
  let residual (C : (G.induce (R : Set V)).ConnectedComponent) : ℤ :=
    (ec G (componentVerts G R C) S : ℤ) - (ec G (componentVerts G R C) S % 2 : ℕ)
  have hp := disjoint_shore_remainder S T
  have hSR : Disjoint S R := hp.1
  have hTR : Disjoint T R := hp.2.1
  have hcover : (S ∪ T) ∪ R = univ := hp.2.2
  have hall : ∀ C : (G.induce (R : Set V)).ConnectedComponent, 0 ≤ charge C := by
    intro C
    exact (component_charge_nonneg q hq hcap S T R hST hSR hTR hcover C).2
  have hresall : ∀ C : (G.induce (R : Set V)).ConnectedComponent, 0 ≤ residual C := by
    intro C
    exact (count_mod_two (ec G (componentVerts G R C) S)).2.2.1
  have hsum : 0 ≤ ∑ C, charge C := sum_nonneg (fun C _ => hall C)
  have hressum : 0 ≤ ∑ C, residual C := sum_nonneg (fun C _ => hresall C)
  have hTT : 0 ≤ (ec G T T : ℤ) := by positivity
  have hSS : 0 ≤ (ec G S S : ℤ) := by positivity
  have hbound : ∀ v : V, (dg G univ v : ℤ) ≤ D := by
    intro v
    have h := (dg_le_maxDegree univ v).trans hcap
    dsimp [D]
    omega
  have hDT : 0 ≤ deficiency D G univ T := deficiency_nonneg D (fun v _ => hbound v)
  have hneg := negative_barrier_bounds (G := G) q heven S T hnegative
  have hid : 2 * (q : ℤ) - 4 = ((q : ℤ) - 2) * ((#S : ℤ) - #T) -
      NEQ.delta q G univ S T + 2 * deficiency D G univ T + (ec G T T : ℤ) +
      ∑ C, charge C := original_component_budget q hq hexact S T hST
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  have hk1 : (#S : ℤ) - #T = 1 := by
    by_contra hk
    have hk2 : 2 ≤ (#S : ℤ) - #T := by omega
    have hm : 0 ≤ ((q : ℤ) - 2) * (((#S : ℤ) - #T) - 2) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [hneg.1]
  have hgamma : 2 * deficiency D G univ T + (ec G T T : ℤ) +
      ∑ C, charge C ≤ (q : ℤ) - 4 := by
    rw [hk1] at hid
    nlinarith [hneg.1]
  have hresid : (ec G S S : ℤ) + ∑ C, residual C =
      (q : ℤ) + NEQ.delta q G univ S T := by
    change (ec G S S : ℤ) + (∑ C : (G.induce (R : Set V)).ConnectedComponent,
      ((ec G (componentVerts G R C) S : ℤ) - (ec G (componentVerts G R C) S % 2 : ℕ))) = _
    rw [component_residual_sum]
    unfold NEQ.delta
    nlinarith
  have hbeta : (ec G S S : ℤ) + ∑ C, residual C ≤ (q : ℤ) - 2 :=
    by linarith [hneg.1]
  have hjoint : (∑ C, charge C) + ∑ C, residual C ≤ 2 * (q : ℤ) - 6 := by
    linarith
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
    have heps := count_mod_two (ec G (componentVerts G R C) S)
    have hlarge : 2 * (q : ℤ) - 4 ≤ charge C + residual C := by
      dsimp [charge, residual, D] at *
      linarith [heps.2.1]
    have hs1 := single_le_sum
      (s := (univ : Finset (G.induce (R : Set V)).ConnectedComponent))
      (fun E _ => hall E) (mem_univ C)
    have hs2 := single_le_sum
      (s := (univ : Finset (G.induce (R : Set V)).ConnectedComponent))
      (fun E _ => hresall E) (mem_univ C)
    linarith
  have hfull : S ∪ T = univ := by
    apply eq_univ_of_forall
    intro v
    by_contra hv
    have hr : v ∈ R := mem_sdiff.mpr ⟨mem_univ _, hv⟩
    rw [hRempty] at hr
    exact Finset.notMem_empty _ hr
  refine ⟨hfull, by omega, ?_, ?_⟩
  · linarith
  · dsimp [D] at hgamma
    linarith

theorem regular_of_critical_barrier (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (hexact : G.edgeSet.ncard + (q - 2) = (q - 1) * Fintype.card V)
    (hfloor : ∀ X : Finset V, X.Nonempty → X ≠ univ →
      2 * (q : ℤ) - 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec G X X : ℤ))
    (S T : Finset V) (hST : Disjoint S T) (hnegative : NEQ.delta q G univ S T < 0) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨hcover, hcard, hSS, hbudget⟩ :=
    component_empty q hq heven hcap hexact hfloor S T hST hnegative
  let D : ℤ := 2 * (q : ℤ) - 2
  have hcapI : ∀ v : V, (dg G univ v : ℤ) ≤ D := by
    intro v
    have h := (dg_le_maxDegree univ v).trans hcap
    dsimp [D]
    omega
  have hDT : 0 ≤ deficiency D G univ T := deficiency_nonneg D (fun v _ => hcapI v)
  have horder : #S + #T = Fintype.card V := by
    rw [← card_union_of_disjoint hST, hcover, card_univ]
  have hTnonempty : T.Nonempty := card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hTnonempty
  have hsingle : D - (dg G univ v : ℤ) ≤ deficiency D G univ T := by
    exact single_le_sum (s := T) (fun a _ => sub_nonneg.mpr (hcapI a)) hv
  have hdgT : dg G T v ≤ ec G T T :=
    single_le_sum (s := T) (fun a _ => Nat.zero_le (dg G T a)) hv
  have hdg : dg G univ v = dg G S v + dg G T v := by
    rw [← hcover]
    exact dg_union_of_disjoint (G := G) hST v
  have hdgZ : (dg G univ v : ℤ) = (dg G S v : ℤ) + dg G T v := by exact_mod_cast hdg
  have hcross : (q : ℤ) + 2 ≤ (dg G S v : ℤ) := by
    dsimp [D] at hsingle hDT
    have htZ : (dg G T v : ℤ) ≤ ec G T T := by exact_mod_cast hdgT
    linarith
  have hSlarge : q + 2 ≤ #S := by
    have hh := dg_le_card (G := G) S v
    omega
  have hlarge : 2 * q ≤ #S + #T := by omega
  have hSU : ec G S univ = ec G S S + ec G S T := by
    rw [← hcover, ec_union_right hST S]
  have hTU : ec G T univ = ec G S T + ec G T T := by
    rw [← hcover, ec_union_right hST T, ec_comm (G := G) T S]
  have hUU : ec G univ univ = ec G S S + 2 * ec G S T + ec G T T := by
    calc
      ec G univ univ = ec G univ S + ec G univ T := by
        have hh := ec_union_right (G := G) hST (univ : Finset V)
        rw [hcover] at hh
        exact hh
      _ = ec G S univ + ec G T univ := by rw [ec_comm (G := G) univ S, ec_comm (G := G) univ T]
      _ = _ := by rw [hSU, hTU]; omega
  have heUU := ec_univ_eq_twice_edges (G := G)
  have hinternal : (ec G S S : ℤ) + ec G T T ≤ 2 * (q : ℤ) - 6 := by
    dsimp [D] at hDT
    linarith
  have hePair : (q - 1) * (#S + #T) ≤ ec G S T + (2 * q - 5) := by
    rw [horder]
    have hp := Bq.pred_cast (by omega : 5 ≤ q)
    have hc : ((q - 2 : ℕ) : ℤ) = (q : ℤ) - 2 := by omega
    have hb : ((2 * q - 5 : ℕ) : ℤ) = 2 * (q : ℤ) - 5 := by omega
    have heZ := hexact
    zify at heZ
    rw [hp, hc] at heZ
    have hUUint : (ec G univ univ : ℤ) =
        (ec G S S : ℤ) + 2 * (ec G S T : ℤ) + ec G T T := by exact_mod_cast hUU
    have heUUint : (ec G univ univ : ℤ) = 2 * (G.edgeSet.ncard : ℤ) := by exact_mod_cast heUU
    have hresult : ((q : ℤ) - 1) * Fintype.card V ≤ (ec G S T : ℤ) + (2 * (q : ℤ) - 5) :=
      by nlinarith
    have hnat : (((q - 1) * Fintype.card V : ℕ) : ℤ) ≤
        (ec G S T : ℤ) + ((2 * q - 5 : ℕ) : ℤ) := by
      push_cast
      rw [hp, hb]
      exact hresult
    exact_mod_cast hnat
  have hpairs : RegularPairs q G S T :=
    L34.dense_pair hq S T hST hlarge
      (fun s _ => (dg_le_maxDegree T s).trans hcap)
      (fun t _ => (dg_le_maxDegree S t).trans hcap) hePair
  exact exists_subgraph_of_regularPairs hST hpairs

end Erdos585.L34EvenTransfer
