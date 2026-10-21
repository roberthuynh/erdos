import Erdos1017.BinomialDefs

namespace Erdos1017.Binomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def elementary (w : V → ℕ) (s : Finset V) (k : ℕ) : ℕ :=
  ∑ B ∈ s.powersetCard k, ∏ i ∈ B,w i

theorem elementary_zero (w : V → ℕ) (s : Finset V) : elementary w s 0=1 := by
  simp [elementary]

theorem elementary_insert (w : V → ℕ) (s : Finset V) (a : V) (ha : a ∉ s) (k : ℕ) :
    elementary w (insert a s) (k+1)=
      elementary w s (k+1)+w a*elementary w s k := by
  have hn (B : Finset V) (hB : B ⊆ s) : a ∉ B := fun h => ha (hB h)
  have hd : Disjoint (s.powersetCard (k+1)) ((s.powersetCard k).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro B hB hBi
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hBi
    exact ha ((Finset.mem_powersetCard.mp hB).1 (Finset.mem_insert_self a C))
  have hinj : ∀ B ∈ s.powersetCard k, ∀ C ∈ s.powersetCard k,
      insert a B=insert a C → B=C := by
    intro B hB C hC he
    have hb := hn B (Finset.mem_powersetCard.mp hB).1
    have hc := hn C (Finset.mem_powersetCard.mp hC).1
    simpa [hb,hc] using congrArg (fun T : Finset V => T.erase a) he
  unfold elementary
  rw [Finset.powersetCard_succ_insert ha,Finset.sum_union hd,Finset.sum_image hinj]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  exact Finset.prod_insert (hn B (Finset.mem_powersetCard.mp hB).1)

theorem choose_add_lower (N a k : ℕ) :
    N.choose (k+1)+a*N.choose k ≤ (N+a).choose (k+1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    change N.choose (k+1)+(a+1)*N.choose k ≤ (N+a+1).choose (k+1)
    rw [Nat.choose_succ_succ']
    have hm : N.choose k ≤ (N+a).choose k := Nat.choose_mono k (by omega)
    nlinarith

/-- Integer multiplicities count a subfamily of subsets of their total size. -/
theorem elementary_le_choose (w : V → ℕ) (s : Finset V) (k : ℕ) :
    elementary w s k ≤ (∑ i ∈ s,w i).choose k := by
  induction s using Finset.induction_on generalizing k with
  | empty => cases k <;> simp [elementary]
  | @insert a s ha ih =>
    cases k with
    | zero => simp [elementary_zero]
    | succ k =>
      rw [elementary_insert w s a ha,Finset.sum_insert ha]
      calc
        _ ≤ (∑ i ∈ s,w i).choose (k+1)+w a*(∑ i ∈ s,w i).choose k :=
          Nat.add_le_add (ih (k+1)) (Nat.mul_le_mul_left _ (ih k))
        _ ≤ _ := by simpa [Nat.add_comm] using choose_add_lower (∑ i ∈ s,w i) (w a) k

noncomputable def maximumCost (n t : ℕ) : ℕ :=
  (Finset.range (n+1)).sup (fun a => a*(n-a).choose (t-1))

theorem maximumCost_zero (t : ℕ) : maximumCost 0 t=0 := by simp [maximumCost]

theorem le_maximumCost (n t a : ℕ) (ha : a ≤ n) :
    a*(n-a).choose (t-1) ≤ maximumCost n t := by
  exact Finset.le_sup (f := fun a => a*(n-a).choose (t-1)) (Finset.mem_range.mpr (by omega))

end Erdos1017.Binomial
