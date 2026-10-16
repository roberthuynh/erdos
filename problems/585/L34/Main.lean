import L34.Critical

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.L34
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The induction ranges over all original graphs and actual finite shores.
Neither degree minima, sparsity, critical signatures nor factors are supplied. -/
theorem dense_pair_aux (q : ℕ) (hq : 6 ≤ q) (n : ℕ) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V),
      #U + #W = n → Disjoint U W → 2 * q ≤ #U + #W →
      (∀ a ∈ U, dg G W a ≤ 2 * q - 2) →
      (∀ w ∈ W, dg G U w ≤ 2 * q - 2) →
      (q - 1) * (#U + #W) ≤ ec G U W + (2 * q - 5) → RegularPairs q G U W := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ U W hnum hUW hn hcapU hcapW he
    classical
    by_contra hnone
    have hlarge := boundary_order (G := G) hq hn he
    have hnontrunc : (2 * q - 5) ≤ (q - 1) * (#U + #W) := by
      have hm := Nat.mul_le_mul_right (#U + #W) (by omega : 1 ≤ q - 1)
      simp only [one_mul] at hm
      omega
    let m := (q - 1) * (#U + #W) - (2 * q - 5)
    have hm : m ≤ ec G U W := by dsimp [m]; omega
    obtain ⟨K, hKG, hmK⟩ := thin_pair (G := G) hUW m hm
    let _ : DecidableRel K.Adj := Classical.decRel _
    have heK : ec K U W + (2 * q - 5) = (q - 1) * (#U + #W) := by
      rw [hmK]
      dsimp [m]
      omega
    have hnoneK : ¬ RegularPairs q K U W := fun h => hnone (h.mono_graph hKG)
    have hcapUK : ∀ a ∈ U, dg K W a ≤ 2 * q - 2 := fun a ha =>
      (dg_mono_graph hKG W a).trans (hcapU a ha)
    have hcapWK : ∀ w ∈ W, dg K U w ≤ 2 * q - 2 := fun w hw =>
      (dg_mono_graph hKG U w).trans (hcapW w hw)
    have hsmaller : ∀ X ⊆ U, ∀ Y ⊆ W, 2 * q ≤ #X + #Y →
        #X + #Y < #U + #W → (q - 1) * (#X + #Y) ≤ ec K X Y + (2 * q - 5) → False := by
      intro X hX Y hY horder hlt hdense
      have hf := ih (#X + #Y) (by omega) K X Y rfl (hUW.mono hX hY) horder
        (fun x hx => (dg_mono (G := K) hY x).trans (hcapUK x (hX hx)))
        (fun y hy => (dg_mono (G := K) hX y).trans (hcapWK y (hY hy))) hdense
      exact hnoneK (hf.mono_sets hX hY)
    have hminU : ∀ a ∈ U, q ≤ dg K W a := by
      intro a ha
      by_contra! hlow
      have hcard := card_erase_add_one ha
      have hec := Bq.ec_erase_add (G := K) (W := W) ha
      have hprod : (q - 1) * (#(U.erase a) + #W) + (q - 1) =
          (q - 1) * (#U + #W) := by
        calc _ = (q - 1) * ((#(U.erase a) + #W) + 1) := by ring
          _ = _ := by congr 1; omega
      exact hsmaller (U.erase a) (erase_subset a U) W (Subset.refl W)
        (by omega) (by omega) (by omega)
    have hminW : ∀ w ∈ W, q ≤ dg K U w := by
      intro w hw
      by_contra! hlow
      have hcard := card_erase_add_one hw
      have hec := Bq.ec_erase_add (G := K) (W := U) hw
      rw [ec_comm (G := K) (W.erase w) U, ec_comm (G := K) W U] at hec
      have hprod : (q - 1) * (#U + #(W.erase w)) + (q - 1) =
          (q - 1) * (#U + #W) := by
        calc _ = (q - 1) * ((#U + #(W.erase w)) + 1) := by ring
          _ = _ := by congr 1; omega
      exact hsmaller U (Subset.refl U) (W.erase w) (erase_subset w W)
        (by omega) (by omega) (by omega)
    have hs : Sparse q K U W := by
      intro X hX Y hY hthree hlt
      by_cases hsmall : #X + #Y ≤ 2 * q - 1
      · exact small_potential (G := K) hq hthree hsmall
      · by_contra! hfail
        have hpot : potential (2 * (q : ℤ) - 2) K X Y =
            2 * (((q - 1) * (#X + #Y) : ℕ) : ℤ) - 2 * (ec K X Y : ℤ) := by
          unfold potential
          push_cast
          rw [Bq.pred_cast (by omega)]
          ring
        rw [hpot] at hfail
        have heXY : (q - 1) * (#X + #Y) ≤ ec K X Y + (2 * q - 5) := by omega
        exact hsmaller X hX Y hY (by omega) hlt heXY
    exact hnoneK (critical_pair hq hUW hn hminU hcapUK hminW hcapWK heK hs)

theorem dense_pair {q : ℕ} (hq : 6 ≤ q) (U W : Finset V)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W)
    (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : (q - 1) * (#U + #W) ≤ ec G U W + (2 * q - 5)) : RegularPairs q G U W := by
  exact dense_pair_aux q hq (#U + #W) G U W rfl hUW hn hcapU hcapW he

open scoped Classical in
/-- Every natural q>=5; the literal nontruncated edge threshold; actual
nonempty q-regular original subgraph on arbitrary support. -/
theorem l34 (q : ℕ) (hq : 5 ≤ q) {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 2 * q - 2)
    (hn : 2 * q ≤ Fintype.card V)
    (he : (q - 1) * Fintype.card V - (2 * q - 5) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  by_cases hq5 : q = 5
  · subst q
    exact Bq.bq 5 (by omega) G hbip hdeg hn (by simpa using he)
  have hq6 : 6 ≤ q := by omega
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U, W, _, hUW, hcov, hbw⟩ := exists_sides hbip o
  have hcard : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcov, card_univ]
  have hec := ec_eq_ncard hbw
  have hnontrunc : (2 * q - 5) ≤ (q - 1) * Fintype.card V := by
    have hm := Nat.mul_le_mul_right (Fintype.card V) (by omega : 1 ≤ q - 1)
    simp only [one_mul] at hm
    omega
  have hePair : (q - 1) * (#U + #W) ≤ ec G U W + (2 * q - 5) := by
    rw [hcard, hec]
    omega
  have hr : RegularPairs q G U W :=
    dense_pair hq6 U W hUW (by omega)
      (fun a _ => (dg_le_maxDegree W a).trans hdeg)
      (fun w _ => (dg_le_maxDegree U w).trans hdeg) hePair
  exact exists_subgraph_of_regularPairs hUW hr


end Erdos585.L34
