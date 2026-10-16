import Openmath.Proofs.PaperSupport.QB6Assembly

/-! Actual original-neighbor incidence for a family meeting exactly at one row.
The written five-D4 argument is credited; no maximality, cover or theta input
is supplied. The defining actual dg/cpr/C02Input imports are unchanged.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
namespace Erdos585.QB6C02PointIncidence
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma erased_neighbors_disjoint (F : Finset (Finset V)) (p c : V)
    (hmeet : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T ∩ U = {p}) :
    (F : Set (Finset V)).PairwiseDisjoint
      (fun T => (T.erase p).filter fun a => G.Adj c a) := by
  intro T hT U hU hTU
  apply disjoint_left.mpr
  intro a haT haU
  have hTa := (mem_erase.mp (mem_filter.mp haT).1).2
  have hUa := (mem_erase.mp (mem_filter.mp haU).1).2
  have hi : a ∈ T ∩ U := mem_inter.mpr ⟨hTa, hUa⟩
  rw [hmeet T hT U hU hTU] at hi
  exact (mem_erase.mp (mem_filter.mp haT).1).1 (mem_singleton.mp hi)

lemma erased_neighbor_sum_le_five {A C : Finset V} (h : C02Input G A C)
    {p : V} (hpA : p ∈ A) (F : Finset (Finset V))
    (hsub : ∀ T ∈ F, T ⊆ A)
    (hmeet : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T ∩ U = {p})
    {c : V} (hc : c ∈ C) (hadj : G.Adj p c) :
    (∑ T ∈ F, dg G (T.erase p) c) ≤ 5 := by
  have hcontain : F.biUnion (fun T => (T.erase p).filter fun a => G.Adj c a) ⊆
      (A.erase p).filter (fun a => G.Adj c a) := by
    intro a ha
    obtain ⟨T, hT, haT⟩ := mem_biUnion.mp ha
    obtain ⟨haerase, hadja⟩ := mem_filter.mp haT
    obtain ⟨hap, haT'⟩ := mem_erase.mp haerase
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨hap, hsub T hT haT'⟩, hadja⟩
  have hsum := card_le_card hcontain
  rw [card_biUnion (erased_neighbors_disjoint (G := G) F p c hmeet)] at hsum
  have hdegree : dg G (A.erase p) c = 5 := by
    have hd := dg_erase_add (G := G) hpA c (G.adj_symm hadj)
    rw [h.satC c hc] at hd
    omega
  change (∑ T ∈ F, dg G (T.erase p) c) ≤ dg G (A.erase p) c at hsum
  simpa only [hdegree] using hsum

lemma canonical_members_at_neighbor_le_two {A C : Finset V} (h : C02Input G A C)
    {p : V} (hpA : p ∈ A) (F : Finset (Finset V))
    (hsub : ∀ T ∈ F, T ⊆ A) (hpoint : ∀ T ∈ F, p ∈ T)
    (hmeet : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T ∩ U = {p})
    {c : V} (hc : c ∈ C) (hadj : G.Adj p c) :
    #(F.filter fun T => c ∈ cpr G C T) ≤ 2 := by
  let J := F.filter fun T => c ∈ cpr G C T
  have hJ : ∀ T ∈ J, T ∈ F := fun T hT => (mem_filter.mp hT).1
  have hsum := erased_neighbor_sum_le_five h hpA J
    (fun T hT => hsub T (hJ T hT))
    (fun T hT U hU hTU => hmeet T (hJ T hT) U (hJ U hU) hTU) hc hadj
  have htwo : ∀ T ∈ J, 2 ≤ dg G (T.erase p) c := by
    intro T hT
    have hcanon := (mem_cpr.mp (mem_filter.mp hT).2).2
    have hd := dg_erase_add (G := G) (hpoint T (hJ T hT)) c (G.adj_symm hadj)
    omega
  have hbound : 2 * #J ≤ ∑ T ∈ J, dg G (T.erase p) c := by
    simpa only [sum_const, smul_eq_mul, mul_comm] using sum_le_sum htwo
  change #J ≤ 2
  omega

lemma canonical_incidence_double_count (C : Finset V) (p : V)
    (F : Finset (Finset V)) :
    (∑ T ∈ F, dg G (cpr G C T) p) =
      ∑ c ∈ C.filter (fun c => G.Adj p c), #(F.filter fun T => c ∈ cpr G C T) := by
  let N := C.filter fun c => G.Adj p c
  have hdegree (T : Finset V) : dg G (cpr G C T) p =
      ∑ c ∈ N, if c ∈ cpr G C T then (1 : ℕ) else 0 := by
    have hfilter : N.filter (fun c => c ∈ cpr G C T) =
        (cpr G C T).filter (fun c => G.Adj p c) := by
      ext c
      simp [N, cpr, and_left_comm, and_comm, and_assoc]
    rw [← sum_filter]
    simp only [sum_const, smul_eq_mul, Nat.mul_one]
    exact congrArg Finset.card hfilter.symm
  calc
    _ = ∑ T ∈ F, ∑ c ∈ N, if c ∈ cpr G C T then (1 : ℕ) else 0 :=
      sum_congr rfl (fun T _ => hdegree T)
    _ = ∑ c ∈ N, ∑ T ∈ F, if c ∈ cpr G C T then (1 : ℕ) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro c _
      rw [← sum_filter]
      simp

/-- Actual incidence on the original C02 graph, for every arbitrary point-meeting family. -/
theorem point_incidence_eight {A C : Finset V} (h : C02Input G A C)
    {p : V} (hpA : p ∈ A) (hp4 : dg G C p = 4) (F : Finset (Finset V))
    (hsub : ∀ T ∈ F, T ⊆ A) (hpoint : ∀ T ∈ F, p ∈ T)
    (hmeet : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T ∩ U = {p}) :
    (∑ T ∈ F, dg G (cpr G C T) p) ≤ 8 := by
  rw [canonical_incidence_double_count]
  have hbound : ∀ c ∈ C.filter (fun c => G.Adj p c),
      #(F.filter fun T => c ∈ cpr G C T) ≤ 2 := by
    intro c hc
    exact canonical_members_at_neighbor_le_two h hpA F hsub hpoint hmeet
      (mem_filter.mp hc).1 (mem_filter.mp hc).2
  have hs := sum_le_sum hbound
  have hN : #(C.filter fun c => G.Adj p c) = 4 := hp4
  simpa only [sum_const, smul_eq_mul, hN] using hs

end Erdos585.QB6C02PointIncidence
