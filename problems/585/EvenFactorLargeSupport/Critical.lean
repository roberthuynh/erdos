import EvenFactorLargeSupport.Support

/- 

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.EvenFactorLargeSupport
open QB4 B5 NEQ NEQAssembly L34EvenTransfer
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem barrier_large_support (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (hexact : G.edgeSet.ncard + (q - 2) = (q - 1) * Fintype.card V)
    (hfloor : ∀ X : Finset V, X.Nonempty → X ≠ univ →
      2 * (q : ℤ) - 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec G X X : ℤ))
    (S T : Finset V) (hST : Disjoint S T) (hnegative : NEQ.delta q G univ S T < 0) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      2 * q ≤ H.verts.ncard := by
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
  exact regularPairs_large_support hST hpairs

theorem critical_large_support (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (hexact : G.edgeSet.ncard + (q - 2) = (q - 1) * Fintype.card V)
    (hfloor : ∀ X : Finset V, X.Nonempty → X ≠ univ →
      2 * (q : ℤ) - 2 ≤ (2 * (q : ℤ) - 2) * #X - (ec G X X : ℤ)) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      2 * q - 1 ≤ H.verts.ncard := by
  classical
  by_cases hspan : ∃ H : G.Subgraph, H.IsSpanning ∧ H.coe.IsRegularOfDegree q
  · obtain ⟨H, hspan, hreg⟩ := hspan
    have hverts : H.verts = Set.univ := hspan.verts_eq_univ
    have hnpos : 0 < Fintype.card V := by omega
    have : Nonempty V := Fintype.card_pos_iff.mp hnpos
    refine ⟨H, ?_, hreg, ?_⟩
    · rw [hverts]
      exact Set.univ_nonempty
    · rw [hverts, Set.ncard_univ, Nat.card_eq_fintype_card]
      exact dense_order_lower q hq G hn hexact.ge
  · obtain ⟨S, T, hST, hnegative⟩ :=
      EvenFactorCriterion.even_no_spanning_factor_barrier q G hq heven hcap hspan
    have hnegativeNEQ : NEQ.delta q G univ T S < 0 := by
      rw [← criterion_original_delta_alignment q G S T]
      exact hnegative
    obtain ⟨H, hne, hreg, hsize⟩ :=
      barrier_large_support q hq heven G hn hcap hexact hfloor T S hST.symm hnegativeNEQ
    exact ⟨H, hne, hreg, by omega⟩

end Erdos585.EvenFactorLargeSupport
