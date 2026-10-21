import Erdos1017.BinomialCount

namespace Erdos1017.Binomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integer-weighted reduction, preserving every original higher clique load.
The base case is an explicit constructor, not a symmetrization axiom. -/
theorem reduce_to_clique_support (G : SimpleGraph V) (t : ℕ) (bound : ℕ → ℝ)
    (base : ∀ w : V → ℕ, G.IsClique (support w : Set V) →
      ∃ P : Partition G w t, P.cost ≤ bound (∑ i,w i)) (w : V → ℕ) :
    ∃ P : Partition G w t, P.cost ≤ bound (∑ i,w i) := by
  classical
  have main : ∀ k : ℕ, ∀ y : V → ℕ, (support y).card=k →
      ∃ P : Partition G y t, P.cost ≤ bound (∑ i,y i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro y hy
      by_cases hc : G.IsClique (support y : Set V)
      · exact base y hc
      · change ¬ (∀ i,i ∈ support y → ∀ j,j ∈ support y → i ≠ j → G.Adj i j) at hc
        push_neg at hc
        obtain ⟨u,hu,v,hv,huv,hnon⟩ := hc
        have hu' : 0 < y u := (Finset.mem_filter.mp hu).2
        have hv' : 0 < y v := (Finset.mem_filter.mp hv).2
        have h0 : (support (merge y u v)).card < k := by
          rw [← hy]; exact merge_support_lt y u v huv hu' hv'
        have h1 : (support (merge y v u)).card < k := by
          rw [← hy]; exact merge_support_lt y v u huv.symm hv' hu'
        obtain ⟨P,hP⟩ := ih _ h0 (merge y u v) rfl
        obtain ⟨Q,hQ⟩ := ih _ h1 (merge y v u) rfl
        let a : ℝ := y u/(y u+y v)
        let b : ℝ := y v/(y u+y v)
        have hd : (0:ℝ) < y u+y v := by positivity
        have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hd.le
        have hb : 0 ≤ b := div_nonneg (Nat.cast_nonneg _) hd.le
        have hab : a+b=1 := by dsimp [a,b]; rw [← add_div,div_self (ne_of_gt hd)]
        have hp : ∀ B : Finset V, G.IsClique (B : Set V) → B.card=t →
            a*(∏ i ∈ B,(merge y u v i : ℝ))+b*(∏ i ∈ B,(merge y v u i : ℝ))=
              ∏ i ∈ B,(y i : ℝ) :=
          fun B hB _ => merge_product_average G y u v huv hnon hu' hv' B hB
        refine ⟨P.mix Q a b ha hb hp,?_⟩
        rw [Partition.mix_cost]
        rw [merge_sum y u v huv] at hP
        rw [merge_sum y v u huv.symm] at hQ
        calc
          _ ≤ a*bound (∑ i,y i)+b*bound (∑ i,y i) :=
            add_le_add (mul_le_mul_of_nonneg_left hP ha) (mul_le_mul_of_nonneg_left hQ hb)
          _ = _ := by rw [← add_mul,hab,one_mul]
  exact main (support w).card w rfl

end Erdos1017.Binomial
