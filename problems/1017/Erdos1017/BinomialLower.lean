import Erdos1017.BinomialUpper

namespace Erdos1017.Binomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

structure Cover (G : SimpleGraph V) (t : ℕ) where
  mass : Finset V → ℝ
  nonneg : ∀ S,0 ≤ mass S
  supported : ∀ S,mass S ≠ 0 → G.IsClique (S : Set V)
  load : ∀ B : Finset V,G.IsClique (B : Set V) → B.card=t → 1 ≤ subsetMoment mass B

noncomputable def Cover.cost {G : SimpleGraph V} {t : ℕ} (P : Cover G t) : ℝ :=
  ∑ S,P.mass S*cliqueCost t S

noncomputable def Partition.toCover {G : SimpleGraph V} {t : ℕ}
    (P : Partition G (fun _ => 1) t) : Cover G t where
  mass := P.mass
  nonneg := P.nonneg
  supported := P.supported
  load B hB hcard := by rw [P.load B hB hcard]; simp

theorem count_subsets_inter (C S : Finset V) (k : ℕ) :
    (∑ B ∈ C.powersetCard k,if B ⊆ S then (1:ℝ) else 0)=((C ∩ S).card.choose k : ℝ) := by
  have he : (C.powersetCard k).filter (fun B => B ⊆ S)=(C ∩ S).powersetCard k := by
    ext B
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_inter_iff]
    tauto
  rw [Finset.sum_boole,he,Finset.card_powersetCard]

noncomputable def starCount (I C S : Finset V) (k : ℕ) : ℝ :=
  ∑ r ∈ I,∑ B ∈ C.powersetCard k,if insert r B ⊆ S then 1 else 0

theorem starCount_le_cost (G : SimpleGraph V) (I C S : Finset V) (t : ℕ)
    (hdis : Disjoint I C)
    (hind : ∀ u ∈ I,∀ v ∈ I,¬ G.Adj u v)
    (hS : G.IsClique (S : Set V)) : starCount I C S (t-1) ≤ cliqueCost t S := by
  classical
  by_cases hex : ∃ r,r ∈ I ∧ r ∈ S
  · obtain ⟨r,hrI,hrS⟩ := hex
    have hother : ∀ u ∈ I,u ≠ r → u ∉ S := by
      intro u hu hur huS
      exact hind u hu r hrI (hS huS hrS hur)
    have he : starCount I C S (t-1)=
        ∑ B ∈ C.powersetCard (t-1),if B ⊆ S then (1:ℝ) else 0 := by
      unfold starCount
      rw [Finset.sum_eq_single r]
      · simp [Finset.insert_subset_iff,hrS]
      · intro u hu hur
        have hn := hother u hu hur
        simp [Finset.insert_subset_iff,hn]
      · exact fun h => (h hrI).elim
    rw [he,count_subsets_inter]
    have hsub : C ∩ S ⊆ S.erase r := by
      intro i hi
      obtain ⟨hiC,hiS⟩ := Finset.mem_inter.mp hi
      refine Finset.mem_erase.mpr ⟨?_,hiS⟩
      intro hir
      subst i
      exact Finset.disjoint_left.mp hdis hrI hiC
    have hn := Nat.choose_mono (t-1) (Finset.card_le_card hsub)
    rw [Finset.card_erase_of_mem hrS] at hn
    unfold cliqueCost
    exact_mod_cast hn
  · have hn : ∀ r ∈ I,r ∉ S := by
      intro r hr hs
      exact hex ⟨r,hr,hs⟩
    have hz : starCount I C S (t-1)=0 := by
      unfold starCount
      apply Finset.sum_eq_zero
      intro r hr
      simp [Finset.insert_subset_iff,hn r hr]
    rw [hz]
    exact Nat.cast_nonneg _

/-- Star-counting dual lower bound on the original vertex set. -/
theorem star_cover_lower (G : SimpleGraph V) (I C : Finset V) (t : ℕ) (ht : 2 ≤ t)
    (hdis : Disjoint I C)
    (hind : ∀ u ∈ I,∀ v ∈ I,¬ G.Adj u v)
    (hcl : ∀ r ∈ I,∀ B ∈ C.powersetCard (t-1),G.IsClique ((insert r B : Finset V) : Set V))
    (P : Cover G t) : (I.card*C.card.choose (t-1) : ℕ) ≤ P.cost := by
  classical
  have hl : ∀ r ∈ I,∀ B ∈ C.powersetCard (t-1),1 ≤ subsetMoment P.mass (insert r B) := by
    intro r hr B hB
    have hn : r ∉ B := by
      intro hb
      exact Finset.disjoint_left.mp hdis hr ((Finset.mem_powersetCard.mp hB).1 hb)
    apply P.load (insert r B) (hcl r hr B hB)
    rw [Finset.card_insert_of_notMem hn,(Finset.mem_powersetCard.mp hB).2]
    omega
  have hlow : (I.card*C.card.choose (t-1) : ℕ) ≤
      ∑ r ∈ I,∑ B ∈ C.powersetCard (t-1),subsetMoment P.mass (insert r B) := by
    calc
      _ = ∑ r ∈ I,∑ B ∈ C.powersetCard (t-1),(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun B hB => hl r hr B hB))
  have he : (∑ r ∈ I,∑ B ∈ C.powersetCard (t-1),subsetMoment P.mass (insert r B))=
      ∑ S,P.mass S*starCount I C S (t-1) := by
    simp only [subsetMoment,starCount,Finset.mul_sum,mul_ite,mul_one,mul_zero]
    calc
      _ = ∑ r ∈ I,∑ S,∑ B ∈ C.powersetCard (t-1),if insert r B ⊆ S then P.mass S else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [he] at hlow
  apply hlow.trans
  apply Finset.sum_le_sum
  intro S _
  by_cases hz : P.mass S=0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (starCount_le_cost G I C S t hdis hind (P.supported S hz)) (P.nonneg S)

end Erdos1017.Binomial
