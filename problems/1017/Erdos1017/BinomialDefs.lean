import Erdos1017.DenseWeights
import Mathlib.Data.Finset.Max

/-! Higher-clique product demands and binomial costs. The graph is fixed;
nonadjacent weight merging is the attributed Zykov averaging construction. -/
namespace Erdos1017.Binomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cliqueCost (t : ℕ) (S : Finset V) : ℝ :=
  ((S.card - 1).choose (t - 1) : ℝ)

structure Partition (G : SimpleGraph V) (w : V → ℕ) (t : ℕ) where
  mass : Finset V → ℝ
  nonneg : ∀ S, 0 ≤ mass S
  supported : ∀ S, mass S ≠ 0 → G.IsClique (S : Set V)
  load : ∀ B : Finset V, G.IsClique (B : Set V) → B.card = t →
    subsetMoment mass B = ∏ i ∈ B, (w i : ℝ)

noncomputable def Partition.cost {G : SimpleGraph V} {w : V → ℕ} {t : ℕ}
    (P : Partition G w t) : ℝ := ∑ S, P.mass S * cliqueCost t S

noncomputable def Partition.mix {G : SimpleGraph V} {w y z : V → ℕ} {t : ℕ}
    (P : Partition G y t) (Q : Partition G z t) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : ∀ B : Finset V, G.IsClique (B : Set V) → B.card=t →
      a*(∏ i ∈ B,(y i : ℝ))+b*(∏ i ∈ B,(z i : ℝ))=∏ i ∈ B,(w i : ℝ)) :
    Partition G w t where
  mass S := a*P.mass S+b*Q.mass S
  nonneg S := add_nonneg (mul_nonneg ha (P.nonneg S)) (mul_nonneg hb (Q.nonneg S))
  supported S h := by
    by_cases hP : P.mass S=0
    · apply Q.supported S
      intro hQ
      exact h (by simp [hP,hQ])
    · exact P.supported S hP
  load B hB hcard := by
    rw [subsetMoment_add,subsetMoment_mul,subsetMoment_mul,P.load B hB hcard,
      Q.load B hB hcard]
    exact hp B hB hcard

theorem Partition.mix_cost {G : SimpleGraph V} {w y z : V → ℕ} {t : ℕ}
    (P : Partition G y t) (Q : Partition G z t) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : ∀ B : Finset V, G.IsClique (B : Set V) → B.card=t →
      a*(∏ i ∈ B,(y i : ℝ))+b*(∏ i ∈ B,(z i : ℝ))=∏ i ∈ B,(w i : ℝ)) :
    (P.mix Q a b ha hb hp).cost=a*P.cost+b*Q.cost := by
  simp [Partition.cost,Partition.mix,add_mul,mul_assoc,Finset.sum_add_distrib,
    Finset.mul_sum]

def merge (w : V → ℕ) (u v i : V) : ℕ :=
  if i=u then w u+w v else if i=v then 0 else w i

theorem merge_cast (w : V → ℕ) (u v i : V) :
    (merge w u v i : ℝ)=Dense.mergeWeight (fun i => (w i : ℝ)) u v i := by
  simp only [merge,Dense.mergeWeight]
  split_ifs <;> simp

theorem merge_sum (w : V → ℕ) (u v : V) (huv : u ≠ v) :
    (∑ i,merge w u v i)=∑ i,w i := by
  have h := Dense.mergeWeight_sum (fun i => (w i : ℝ)) u v huv
  simp only [← merge_cast] at h
  exact_mod_cast h

noncomputable def support (w : V → ℕ) : Finset V :=
  Finset.univ.filter (fun i => 0 < w i)

theorem support_real (w : V → ℕ) :
    support w=Dense.positiveSupport (fun i => (w i : ℝ)) := by
  ext i
  simp [support,Dense.positiveSupport]

theorem merge_support_lt (w : V → ℕ) (u v : V) (huv : u ≠ v)
    (hu : 0 < w u) (hv : 0 < w v) :
    (support (merge w u v)).card < (support w).card := by
  rw [support_real,support_real]
  simp_rw [merge_cast]
  exact Dense.mergeWeight_card_lt _ u v huv (by exact_mod_cast hu) (by exact_mod_cast hv)

/-- Any clique omits at least one of two nonadjacent vertices. Product demands
therefore average exactly, in every clique size, under the two merges. -/
theorem merge_product_average (G : SimpleGraph V) (w : V → ℕ)
    (u v : V) (huv : u ≠ v) (hnon : ¬ G.Adj u v)
    (hu : 0 < w u) (hv : 0 < w v) (B : Finset V)
    (hB : G.IsClique (B : Set V)) :
    ((w u : ℝ)/(w u+w v))*(∏ i ∈ B,(merge w u v i : ℝ))+
      ((w v : ℝ)/(w u+w v))*(∏ i ∈ B,(merge w v u i : ℝ))=
      ∏ i ∈ B,(w i : ℝ) := by
  have hden : (w u : ℝ)+w v ≠ 0 := by positivity
  have one (r s : V) (hrs : r ≠ s) (hr : r ∈ B) (hs : s ∉ B) :
      (∏ i ∈ B,(merge w r s i : ℝ))=
        ((w r : ℝ)+w s)*(∏ i ∈ B.erase r,(w i : ℝ)) := by
    rw [← Finset.mul_prod_erase B (fun i => (merge w r s i : ℝ)) hr]
    congr 1
    · simp [merge]
    · apply Finset.prod_congr rfl
      intro i hi
      obtain ⟨hir,hiB⟩ := Finset.mem_erase.mp hi
      have his : i ≠ s := fun h => hs (h ▸ hiB)
      simp [merge,hir,his]
  have zero (r s : V) (hrs : r ≠ s) (hs : s ∈ B) :
      (∏ i ∈ B,(merge w r s i : ℝ))=0 := by
    apply Finset.prod_eq_zero hs
    simp [merge,hrs.symm]
  by_cases huB : u ∈ B
  · have hvB : v ∉ B := fun h => hnon (hB huB h huv)
    rw [one u v huv huB hvB,zero v u huv.symm huB]
    rw [← Finset.mul_prod_erase B (fun i => (w i : ℝ)) huB]
    field_simp
    <;> ring
  · by_cases hvB : v ∈ B
    · rw [zero u v huv hvB,one v u huv.symm hvB huB]
      rw [← Finset.mul_prod_erase B (fun i => (w i : ℝ)) hvB]
      field_simp
      <;> ring
    · have he (i : V) (hi : i ∈ B) : i ≠ u ∧ i ≠ v :=
        ⟨fun h => huB (h ▸ hi),fun h => hvB (h ▸ hi)⟩
      have hp : (∏ i ∈ B,(merge w u v i : ℝ))=∏ i ∈ B,(w i : ℝ) :=
        Finset.prod_congr rfl (fun i hi => by simp [merge,(he i hi).1,(he i hi).2])
      have hq : (∏ i ∈ B,(merge w v u i : ℝ))=∏ i ∈ B,(w i : ℝ) :=
        Finset.prod_congr rfl (fun i hi => by simp [merge,(he i hi).1,(he i hi).2])
      rw [hp,hq]
      field_simp
      <;> ring

end Erdos1017.Binomial
