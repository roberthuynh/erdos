import R704.Base
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1UniqueR704
open QB4 B5 H3Unequal AllHTopCritical Omit1PrefixR691
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ} {A B U : Finset V}

/-- Every A vertex in a tiny original zero source cut has original degree exactly q. -/
theorem tiny_zero_degree (host : Omit1Q0CutChainR699.Host q G A B)
    (zU : g q G A B U = 0) (tiny : #U ≤ 2) {x : V} (hx : x ∈ A∩U) :
    G.degree x = q := by
  have cs := support_card host.toHost U
  have lower := Bq.ec_lower_of_min (G := G) (inter_subset_left : A∩U ⊆ A) host.minA
  have simple := AllHTopCritical.ec_le_product (G := G) (A∩U) (B∩U)
  have split := ec_sdiff_add_right (G := G) (inter_subset_left : B∩U ⊆ B) (A∩U)
  have bs : B\(B∩U)=B\U := by ext v; simp
  rw [bs] at split
  have nb : #(B∩U)=0 := by
    by_contra! hn
    have hq := host.large
    have pp : (0 : ℤ) ≤ ((q : ℤ)-2) * #(B∩U) :=
      mul_nonneg (by omega) (Nat.cast_nonneg _)
    have pp' : (q : ℤ)-2 ≤ ((q : ℤ)-2) * #(B∩U) := by
      have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ)-2 by omega)
        (show 0 ≤ (#(B∩U) : ℤ)-1 by omega)
      nlinarith
    have ac : #(A∩U) ≤ 2 := by omega
    have product : (#(A∩U) : ℤ)*#(B∩U) ≤ 2*#(B∩U) := by
      have hm := mul_nonneg (show (0 : ℤ) ≤ 2-#(A∩U) by omega)
        (show (0 : ℤ) ≤ #(B∩U) by positivity)
      nlinarith
    unfold g k at zU
    zify at lower split simple
    nlinarith
  have be : B∩U=∅ := card_eq_zero.mp nb
  have ze : ec G (A∩U) (B∩U)=0 := by rw [be]; simp [ec,dg]
  have exactsum : ec G (A∩U) B = q*#(A∩U) := by
    unfold g k at zU
    rw [nb] at zU
    zify at split ⊢
    nlinarith
  have rem := Bq.ec_lower_of_min (G := G)
    ((erase_subset x (A∩U)).trans inter_subset_left) host.minA
  have er : ec G ((A∩U).erase x) B + dg G B x = ec G (A∩U) B := sum_erase_add _ _ hx
  have cr := card_erase_add_one hx
  have lo := host.minA x (mem_inter.mp hx).1
  rw [dg_eq_degree host.bipartite (mem_inter.mp hx).1] at er lo
  rw [exactsum] at er
  zify at rem er cr lo ⊢
  nlinarith

#print axioms tiny_zero_degree
end Erdos585.Omit1UniqueR704
