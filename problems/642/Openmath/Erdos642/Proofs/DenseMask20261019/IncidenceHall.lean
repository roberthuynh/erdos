import Mathlib

/-! Actual covering injections from incidence bounds, including two tokens per isolate. -/
namespace Erdos642.DenseMask20261019.IncidenceHall

open scoped BigOperators

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

omit [DecidableEq I] [Fintype V] in
/-- Double counting pays every Hall subset; no law for the chosen injection is used. -/
theorem injective_of_load_bounds (neighbors : I → Finset V) (h : ℝ) (hh : 0 < h)
    (hleft : ∀ i, h ≤ ((neighbors i).card : ℝ))
    (hright : ∀ v, ((Finset.univ.filter fun i => v ∈ neighbors i).card : ℝ) ≤ h) :
    ∃ f : I → V, Function.Injective f ∧ ∀ i, f i ∈ neighbors i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective neighbors).mp
  intro S
  let T := S.biUnion neighbors
  have hsmall : ∀ i ∈ S, T.bipartiteAbove (fun i v => v ∈ neighbors i) i = neighbors i := by
    intro i hi
    ext v
    simp only [Finset.mem_bipartiteAbove]
    exact ⟨fun hv => hv.2, fun hv => ⟨Finset.mem_biUnion.mpr ⟨i, hi, hv⟩, hv⟩⟩
  have hcount := Finset.card_nsmul_le_card_nsmul (R := ℝ)
    (r := fun i v => v ∈ neighbors i) (s := S) (t := T)
    (m := h) (n := h)
    (fun i hi => by rw [hsmall i hi]; exact hleft i)
    (fun v _ => (show ((S.bipartiteBelow (fun i v => v ∈ neighbors i) v).card : ℝ) ≤
        (Finset.univ.filter fun i => v ∈ neighbors i).card by
      exact_mod_cast Finset.card_le_card (by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)).trans
      (hright v))
  have hreal : (S.card : ℝ) ≤ T.card := by
    apply (mul_le_mul_iff_left₀ hh).mp
    simpa only [nsmul_eq_mul, mul_comm] using hcount
  exact_mod_cast hreal

/-- Every isolated mask vertex contributes two separate original endpoint occurrences. -/
theorem isolate_tokens_match_layer (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q R : Finset V) (h : ℝ) (hh : 0 < h)
    (hleft : ∀ x ∈ Q, h ≤ ((G.neighborFinset x ∩ R).card : ℝ))
    (hload : ∀ v, 2 * ((Q.filter fun x => G.Adj x v).card : ℝ) ≤ h) :
    ∃ f : (↥(Q : Set V) × Bool) → V, Function.Injective f ∧
      ∀ z, f z ∈ R ∧ G.Adj z.1.val (f z) := by
  classical
  let neighbors : (↥(Q : Set V) × Bool) → Finset V :=
    fun z => G.neighborFinset z.1.val ∩ R
  have hright : ∀ v,
      ((Finset.univ.filter fun z => v ∈ neighbors z).card : ℝ) ≤ h := by
    intro v
    let E := {z : (↥(Q : Set V) × Bool) // v ∈ neighbors z}
    let T := ↥(Q.filter fun x => G.Adj x v : Set V) × Bool
    let g : E → T := fun z =>
      (⟨z.val.1.val, Finset.mem_filter.mpr
        ⟨z.val.1.property, by
          have hadj := (Finset.mem_inter.mp z.property).1
          simpa only [SimpleGraph.mem_neighborFinset] using hadj⟩⟩, z.val.2)
    have hg : Function.Injective g := by
      intro z w hzw
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun t : T => t.1.val) hzw
      · exact congrArg (fun t : T => t.2) hzw
    have hcard := Fintype.card_le_of_injective g hg
    have hE : Fintype.card E = (Finset.univ.filter fun z => v ∈ neighbors z).card := by
      simp only [E, Fintype.card_subtype]
    have hT : Fintype.card T = 2 * (Q.filter fun x => G.Adj x v).card := by
      simp [T, Nat.mul_comm]
    have hnat : (Finset.univ.filter fun z => v ∈ neighbors z).card ≤
        2 * (Q.filter fun x => G.Adj x v).card := by
      rwa [hE, hT] at hcard
    exact (show ((Finset.univ.filter fun z => v ∈ neighbors z).card : ℝ) ≤
      2 * ((Q.filter fun x => G.Adj x v).card : ℝ) by exact_mod_cast hnat).trans (hload v)
  obtain ⟨f, hf, hadj⟩ := injective_of_load_bounds neighbors h hh
    (fun z => hleft z.1.val z.1.property) hright
  refine ⟨f, hf, fun z => ?_⟩
  have hz := Finset.mem_inter.mp (hadj z)
  exact ⟨hz.2, by simpa only [SimpleGraph.mem_neighborFinset] using hz.1⟩

end Erdos642.DenseMask20261019.IncidenceHall
