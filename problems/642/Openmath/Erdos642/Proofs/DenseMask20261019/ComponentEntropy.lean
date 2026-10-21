import Openmath.Erdos642.Proofs.DenseMask20261019.ComponentObstruction

/-! Counting actual unions of original induced components. -/
noncomputable section
namespace Erdos642.DenseMask20261019.ComponentEntropy
open Finset SimpleGraph Real
open Erdos642.CampaignFe72210b
open Erdos642.DenseMask20261019.ComponentObstruction
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def unionVertices (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (F : Finset (mask G Q).ConnectedComponent) : Finset V :=
  F.biUnion (componentVertices G Q)

theorem support_disjoint (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (c d : (mask G Q).ConnectedComponent) (hcd : c ≠ d) :
    Disjoint (componentVertices G Q c) (componentVertices G Q d) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  have hc := ((mem_componentVertices G Q c v).mp hvC).2
  have hd := ((mem_componentVertices G Q d v).mp hvD).2
  change (mask G Q).connectedComponentMk v = c at hc
  change (mask G Q).connectedComponentMk v = d at hd
  exact hcd (hc.symm.trans hd)

theorem union_card (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (F : Finset (mask G Q).ConnectedComponent) :
    (unionVertices G Q F).card = ∑ c ∈ F, (componentVertices G Q c).card := by
  unfold unionVertices
  apply Finset.card_biUnion
  intro c _ d _ hcd
  exact support_disjoint G Q c d hcd

def collections (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (m k : ℝ) : Finset (Finset (mask G Q).ConnectedComponent) :=
  Finset.univ.powerset.filter (fun F =>
    (∀ c ∈ F, m ≤ ((componentVertices G Q c).card : ℝ)) ∧
      ((unionVertices G Q F).card : ℝ) ≤ k)

theorem collection_size (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (m k : ℝ) (hm : 0 < m) (F : Finset (mask G Q).ConnectedComponent)
    (hF : F ∈ collections G Q m k) : F.card ≤ ⌊k/m⌋₊ := by
  obtain ⟨_, hmin, hsize⟩ := Finset.mem_filter.mp hF
  have hs : (F.card : ℝ)*m ≤ ((unionVertices G Q F).card : ℝ) := by
    calc
      _ = ∑ c ∈ F, m := by simp [mul_comm]
      _ ≤ ∑ c ∈ F, ((componentVertices G Q c).card : ℝ) := Finset.sum_le_sum hmin
      _ = _ := by exact_mod_cast (union_card G Q F).symm
  apply Nat.le_floor
  exact (le_div_iff₀ hm).mpr (by nlinarith [hs])

private theorem component_count (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V) :
    Fintype.card (mask G Q).ConnectedComponent ≤ Fintype.card V := by
  classical
  apply Fintype.card_le_of_surjective (mask G Q).connectedComponentMk
  intro c
  induction c using ConnectedComponent.ind with
  | _ v => exact ⟨v, rfl⟩

/-- A finite count of actual component collections, not a scalar entropy assumption. -/
theorem collections_card_choose (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (m k : ℝ) (hm : 0 < m) :
    (collections G Q m k).card ≤
      ∑ j ∈ Finset.range (⌊k/m⌋₊+1), (Fintype.card V).choose j := by
  classical
  let S : Finset (mask G Q).ConnectedComponent := Finset.univ
  let h := ⌊k/m⌋₊
  have hsub : collections G Q m k ⊆
      (Finset.range (h+1)).biUnion (fun j => S.powersetCard j) := by
    intro F hF
    have hsize := collection_size G Q m k hm F hF
    exact Finset.mem_biUnion.mpr ⟨F.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  calc
    _ ≤ ((Finset.range (h+1)).biUnion (fun j => S.powersetCard j)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (h+1), (S.powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (h+1), (Fintype.card (mask G Q).ConnectedComponent).choose j := by
      simp only [Finset.card_powersetCard, S, Finset.card_univ]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => Nat.choose_le_choose j (component_count G Q))

private theorem power_sum_bound (n h : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (h+1), n^j) ≤ n^(h+1) := by
  induction h with
  | zero => simp; omega
  | succ h ih =>
    change (∑ j ∈ Finset.range ((h+1)+1), n^j) ≤ n^((h+1)+1)
    rw [Finset.sum_range_succ]
    calc
      _ ≤ 2*n^(h+1) := by omega
      _ ≤ n*n^(h+1) := Nat.mul_le_mul_right _ hn
      _ = _ := by simpa only [mul_comm] using (pow_succ n (h+1)).symm

/-- The full entropy bound for actual original component unions. -/
theorem collections_card_exp (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (m k : ℝ) (hm : 0 < m) (hk : m ≤ k) (hn : 2 ≤ Fintype.card V) :
    ((collections G Q m k).card : ℝ) ≤
      exp (2*k*log (Fintype.card V)/m) := by
  let n := Fintype.card V
  let h := ⌊k/m⌋₊
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hchoose : (collections G Q m k).card ≤ n^(h+1) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (h+1), n.choose j := collections_card_choose G Q m k hm
      _ ≤ ∑ j ∈ Finset.range (h+1), n^j :=
        Finset.sum_le_sum (fun j _ => Nat.choose_le_pow n j)
      _ ≤ _ := power_sum_bound n h hn
  have hkm : 1 ≤ k/m := (le_div_iff₀ hm).mpr (by linarith)
  have hfloor : (h : ℝ) ≤ k/m := Nat.floor_le (by linarith : 0 ≤ k/m)
  have he : (h : ℝ)+1 ≤ 2*k/m := by
    calc
      _ ≤ k/m+k/m := add_le_add hfloor hkm
      _ = _ := by ring
  calc
    _ ≤ (n : ℝ)^(h+1) := by exact_mod_cast hchoose
    _ = exp (((h : ℝ)+1)*log n) := by
      rw [show (h : ℝ)+1 = ((h+1 : ℕ) : ℝ) by simp, exp_nat_mul, exp_log hnpos]
    _ ≤ _ := exp_le_exp.mpr (by
      change ((h : ℝ)+1)*log (n : ℝ) ≤ 2*k*log (n : ℝ)/m
      calc
        _ ≤ (2*k/m)*log (n : ℝ) := mul_le_mul_of_nonneg_right he (log_nonneg hnR)
        _ = _ := by ring)

theorem collections_card_rpow (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V)
    (m k : ℝ) (hm : 0 < m) (hk : m ≤ k) (hn : 2 ≤ Fintype.card V) :
    ((collections G Q m k).card : ℝ) ≤ (Fintype.card V : ℝ)^(2*k/m) := by
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  rw [Real.rpow_def_of_pos hnpos]
  convert collections_card_exp G Q m k hm hk hn using 1 <;> congr 1 <;> ring

end Erdos642.DenseMask20261019.ComponentEntropy
