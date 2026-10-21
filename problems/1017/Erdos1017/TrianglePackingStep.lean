import Erdos1017.TrianglePacking

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Add a first star, then a scaled local packing with a smaller root weight. -/
noncomputable def trianglePackingStep (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h h' θ κ : ℝ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (hcoef : θ+κ=1)
    (hroot : h=θ*(∑ i,x i)+κ*h')
    (hbound : κ*h'^2+θ*(∑ i,(x i)^2) ≤ h^2)
    (P : LocalTrianglePacking (fun o : Option ι => o.elim h' x)) :
    LocalTrianglePacking (fun o : Option ι => o.elim h x) where
  mass T := θ*starTriangleMass x T+κ*P.mass T
  nonneg T := add_nonneg (mul_nonneg hθ ((balancedTrianglePacking x hx).nonneg T))
    (mul_nonneg hκ (P.nonneg T))
  supported T hT := by rw [starTriangleMass_supported x T hT,P.supported T hT]; ring
  pair_cap B hB := by
    rw [subsetMoment_add,subsetMoment_mul,subsetMoment_mul]
    have hp := mul_le_mul_of_nonneg_left (P.pair_cap B hB) hκ
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hB
    rw [Finset.prod_pair hij] at hp ⊢
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        rw [starTriangleMass_root_pair]
        simp only [Option.elim_none,Option.elim_some] at hp ⊢
        have hs := congrArg (fun z : ℝ => z*x j) hroot
        nlinarith [mul_nonneg hθ (sq_nonneg (x j))]
    | some i =>
      cases j with
      | none =>
        rw [Finset.pair_comm,starTriangleMass_root_pair]
        simp only [Option.elim_none,Option.elim_some] at hp ⊢
        have hs := congrArg (fun z : ℝ => z*x i) hroot
        have hm : subsetMoment P.mass {none,some i}=subsetMoment P.mass {some i,none} := by rw [Finset.pair_comm]
        rw [hm]
        nlinarith [mul_nonneg hθ (sq_nonneg (x i))]
      | some j =>
        rw [starTriangleMass_minor_pair x i j (fun h => hij (congrArg some h))]
        simp only [Option.elim_some] at hp ⊢
        nlinarith [congrArg (fun z : ℝ => z*(x i*x j)) hcoef]
  leave i := by
    rw [subsetMoment_add,subsetMoment_mul,subsetMoment_mul]
    have hp := mul_le_mul_of_nonneg_left (P.leave i) hκ
    rw [Fintype.sum_option] at hp ⊢
    simp only [Option.elim_none,Option.elim_some] at hp ⊢
    cases i with
    | none =>
      rw [starTriangleMass_root]
      simp only [Option.elim_none] at hp ⊢
      have he := elementarySum_two_identity Finset.univ x
      have heθ := congrArg (fun z : ℝ => θ*z) he
      have hs := congrArg (fun z : ℝ => z*(∑ i,x i)) hroot
      nlinarith
    | some i =>
      rw [starTriangleMass_singleton]
      simp only [Option.elim_some] at hp ⊢
      have hs := congrArg (fun z : ℝ => z*x i) hroot
      have hc := congrArg (fun z : ℝ => z*(x i)^2) hcoef
      have hcs := congrArg (fun z : ℝ => z*(x i*(∑ j,x j))) hcoef
      nlinarith

end Erdos1017
