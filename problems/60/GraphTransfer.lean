import Transfer
import C4Counting

/-! Transfer on actual finite graphs. The edit-radius and polarity path-family
producers are explicit premises and remain obligations for the headline. -/
set_option autoImplicit false
namespace Erdos60.Transfer
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact natural edge balance on the two actual edge sets. -/
theorem graph_edge_balance (G Q : SimpleGraph V) (M t δ : ℕ)
    (hG : G.edgeFinset.card = M + t) (hQ : Q.edgeFinset.card + δ = M) :
    (Q.edgeFinset \ G.edgeFinset).card + t + δ =
      (G.edgeFinset \ Q.edgeFinset).card := by
  classical
  have h₁ := Finset.card_sdiff_add_card_inter G.edgeFinset Q.edgeFinset
  have h₂ := Finset.card_sdiff_add_card_inter Q.edgeFinset G.edgeFinset
  rw [Finset.inter_comm Q.edgeFinset G.edgeFinset] at h₂
  omega

/-- Full lower-bound transfer step from actual short edit radius and actual
edge-disjoint path families. This does not supply those two producers. -/
theorem graph_transfer (G Q : SimpleGraph V) (M q t δ : ℕ)
    (hG : G.edgeFinset.card = M + t) (hQ : Q.edgeFinset.card + δ = M)
    (hsmall : (G.edgeFinset \ Q.edgeFinset).card ≤ q - 1)
    (P : Sym2 V → Finset (Finset (Sym2 V)))
    (hpath : ∀ e ∈ G.edgeFinset \ Q.edgeFinset, ∀ p ∈ P e,
      Counting.IsThreePath e p ∧ p ⊆ Q.edgeFinset)
    (hdis : ∀ e ∈ G.edgeFinset \ Q.edgeFinset, ∀ p ∈ P e,
      ∀ r ∈ P e, p ≠ r → Disjoint p r)
    (hnum : ∀ e ∈ G.edgeFinset \ Q.edgeFinset, q - 1 ≤ (P e).card) :
    t * (q - 1) ≤ Counting.cycleCount G := by
  classical
  have hc := Counting.retained_path_count G Q (G.edgeFinset \ Q.edgeFinset)
    P (q - 1) (fun _ he => Finset.mem_sdiff.mp he) hpath hdis hnum
  exact natural_transfer q t _ δ _ _ (graph_edge_balance G Q M t δ hG hQ) hsmall hc

/-- Equality at the transfer threshold removes all missing edges and polarity deficit.
It does not yet identify absolute endpoints or prove the matching classification. -/
theorem graph_transfer_equality (G Q : SimpleGraph V) (M q t δ : ℕ)
    (ht : 1 ≤ t) (hG : G.edgeFinset.card = M + t)
    (hQ : Q.edgeFinset.card + δ = M)
    (hsmall : (G.edgeFinset \ Q.edgeFinset).card < q - 1)
    (P : Sym2 V → Finset (Finset (Sym2 V)))
    (hpath : ∀ e ∈ G.edgeFinset \ Q.edgeFinset, ∀ p ∈ P e,
      Counting.IsThreePath e p ∧ p ⊆ Q.edgeFinset)
    (hdis : ∀ e ∈ G.edgeFinset \ Q.edgeFinset, ∀ p ∈ P e,
      ∀ r ∈ P e, p ≠ r → Disjoint p r)
    (hnum : ∀ e ∈ G.edgeFinset \ Q.edgeFinset, q - 1 ≤ (P e).card)
    (heq : Counting.cycleCount G = t * (q - 1)) :
    (G.edgeFinset \ Q.edgeFinset).card = t ∧ δ = 0 ∧
      (Q.edgeFinset \ G.edgeFinset).card = 0 := by
  classical
  let j := (G.edgeFinset \ Q.edgeFinset).card
  let d := (Q.edgeFinset \ G.edgeFinset).card
  have hb : d + t + δ = j := graph_edge_balance G Q M t δ hG hQ
  have hd : d ≤ q - 1 := by dsimp [j] at hb; omega
  have hc := Counting.retained_path_count G Q (G.edgeFinset \ Q.edgeFinset)
    P (q - 1) (fun _ he => Finset.mem_sdiff.mp he) hpath hdis hnum
  change j * (q - 1 - d) ≤ Counting.cycleCount G at hc
  have hcZ : (j : ℤ) * (((q - 1 : ℕ) : ℤ) - d) ≤ (Counting.cycleCount G : ℤ) := by
    have hh : (j : ℤ) * ((q - 1 - d : ℕ) : ℤ) ≤ (Counting.cycleCount G : ℤ) := by
      exact_mod_cast hc
    rwa [Nat.cast_sub hd] at hh
  have hbZ : (d : ℤ) = j - t - δ := by omega
  have hsZ : (j : ℤ) < ((q - 1 : ℕ) : ℤ) := by exact_mod_cast hsmall
  have heqZ : (Counting.cycleCount G : ℤ) = (t : ℤ) * ((q - 1 : ℕ) : ℤ) := by
    exact_mod_cast heq
  have hh := equality_counts (((q - 1 : ℕ) : ℤ) + 1) t j δ d
    (Counting.cycleCount G) (by exact_mod_cast ht) (by positivity)
    (by positivity) hbZ (by simpa using hsZ) (by simpa using hcZ)
    (by simpa using heqZ)
  exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2.1, by exact_mod_cast hh.2.2⟩

end Erdos60.Transfer
