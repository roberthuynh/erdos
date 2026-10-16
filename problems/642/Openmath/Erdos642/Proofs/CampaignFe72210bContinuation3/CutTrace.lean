import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutOperations

/-! Finite cut descent with an explicit integer charge count.

The terminal conditions use actual restricted degrees and crossing-edge counts.
Only choosing the smaller cut side incurs a density charge; deletion of a low
degree vertex and retention of a dense complement do not incur a charge.
No logarithmic estimate or final almost-regular extraction is assumed here.
-/
namespace Erdos642.CampaignFe72210bContinuation3.CutExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two actual stopping conditions of cut descent. -/
def Terminal (lam : ℝ) (S : Finset V) : Prop :=
  (∀ x ∈ S, average G S / 2 ≤ (restrictedDegree G S x : ℝ)) ∧
  (∀ U ⊆ S, 2 * U.card ≤ S.card →
    (lam / 3) * average G S * (U.card : ℝ) ≤ (cross G S U : ℝ))

/-- Strong induction constructs a terminal induced vertex set. The natural
number `r` counts only smaller-side choices and records their halving cost. -/
theorem exists_terminal_with_charge (S : Finset V) (lam : ℝ)
    (hpos : 0 < average G S) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    ∃ W : Finset V, W ⊆ S ∧ ∃ r : ℕ,
      0 < average G W ∧ Terminal G lam W ∧
      (1 - lam) ^ r * average G S ≤ average G W ∧
      2 ^ r * W.card ≤ S.card := by
  have hbase : 0 ≤ 1 - lam := by linarith
  have descent : ∀ m : ℕ, ∀ S : Finset V, S.card = m → 0 < average G S →
      ∃ W : Finset V, W ⊆ S ∧ ∃ r : ℕ,
        0 < average G W ∧ Terminal G lam W ∧
        (1 - lam) ^ r * average G S ≤ average G W ∧
        2 ^ r * W.card ≤ S.card := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro S hcard hpos
      by_cases hlow : ∃ x ∈ S, (restrictedDegree G S x : ℝ) < average G S / 2
      · obtain ⟨x, hx, hl⟩ := hlow
        obtain ⟨_, hlt, havg⟩ := average_erase_gt G S x hx hpos hl
        obtain ⟨W, hW, r, hWpos, hterm, hret, hcharge⟩ :=
          ih (S.erase x).card (by omega) (S.erase x) rfl (hpos.trans havg)
        refine ⟨W, hW.trans (Finset.erase_subset x S), r, hWpos, hterm, ?_, ?_⟩
        · exact (mul_le_mul_of_nonneg_left havg.le (pow_nonneg hbase r)).trans hret
        · exact hcharge.trans (Finset.card_le_card (Finset.erase_subset x S))
      · have hdegrees : ∀ x ∈ S, average G S / 2 ≤ (restrictedDegree G S x : ℝ) := by
          intro x hx
          exact le_of_not_gt fun hl => hlow ⟨x, hx, hl⟩
        by_cases hcuts : ∀ U ⊆ S, 2 * U.card ≤ S.card →
            (lam / 3) * average G S * (U.card : ℝ) ≤ (cross G S U : ℝ)
        · refine ⟨S, Finset.Subset.refl S, 0, hpos, ⟨hdegrees, hcuts⟩, ?_, ?_⟩
          · simp
          · simp
        · push Not at hcuts
          obtain ⟨U, hUS, hhalf, hsparse⟩ := hcuts
          have hsparse' : (cross G S U : ℝ) <
              lam * average G S * (U.card : ℝ) / 3 := by
            calc
              _ < (lam / 3) * average G S * (U.card : ℝ) := hsparse
              _ = _ := by ring
          rcases sparse_cut_alternative G S U lam hUS hpos hhalf hlam hlamhalf hsparse' with
            hcomplement | hsmaller
          · obtain ⟨_, hlt, havg⟩ := hcomplement
            obtain ⟨W, hW, r, hWpos, hterm, hret, hcharge⟩ :=
              ih (S \ U).card (by omega) (S \ U) rfl (hpos.trans_le havg)
            refine ⟨W, hW.trans Finset.sdiff_subset, r, hWpos, hterm, ?_, ?_⟩
            · exact (mul_le_mul_of_nonneg_left havg (pow_nonneg hbase r)).trans hret
            · exact hcharge.trans (Finset.card_le_card Finset.sdiff_subset)
          · obtain ⟨_, hlt, hhalf, hUpos, havg⟩ := hsmaller
            obtain ⟨W, hW, r, hWpos, hterm, hret, hcharge⟩ :=
              ih U.card (by omega) U rfl hUpos
            refine ⟨W, hW.trans hUS, r + 1, hWpos, hterm, ?_, ?_⟩
            · calc
                (1 - lam) ^ (r + 1) * average G S =
                    (1 - lam) ^ r * ((1 - lam) * average G S) := by
                  rw [pow_succ]
                  ring
                _ ≤ (1 - lam) ^ r * average G U :=
                  mul_le_mul_of_nonneg_left havg (pow_nonneg hbase r)
                _ ≤ average G W := hret
            · calc
                2 ^ (r + 1) * W.card = 2 * (2 ^ r * W.card) := by
                  rw [pow_succ]
                  ring
                _ ≤ 2 * U.card := Nat.mul_le_mul_left 2 hcharge
                _ ≤ S.card := hhalf
  exact descent S.card S rfl hpos

end Erdos642.CampaignFe72210bContinuation3.CutExtraction
