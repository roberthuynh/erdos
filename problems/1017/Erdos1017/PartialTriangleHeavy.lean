import Erdos1017.PartialTriangleSupply

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem starTriangleMass_total (x : ι → ℝ) :
    (∑ T,starTriangleMass x T)=elementarySum Finset.univ x 2 := by
  have h := aggregate_observable rootedPartSet (weightedLayer x 2) (fun _ => (1:ℝ))
  simp only [mul_one] at h
  exact h.trans (weightedLayer_total x 2)

/-- An explicit star supplies the quotas when one minor weight is at least half. -/
noncomputable def heavyPartialTriangleSupply (x : ι → ℝ) (hx : ∀ i,0 ≤ x i)
    (h a : ℝ) (hs : 0 < ∑ i,x i) (hheavy : (∑ i,x i) ≤ h)
    (hah : h ≤ a) (hab : a ≤ h+∑ i,x i) :
    PartialTriangleSupply a (fun o : Option ι => o.elim h x) := by
  let s := ∑ i,x i
  let b := h+s
  let d := b-a
  let θ := d/s
  have hs0 : 0 < s := hs
  have hb : 0 < b := by dsimp [b]; linarith
  have hd : 0 ≤ d := sub_nonneg.mpr hab
  have hd1 : d ≤ s := by dsimp [d,b]; linarith
  have hdh : d ≤ h := hd1.trans hheavy
  have hh : 0 ≤ h := hs0.le.trans hheavy
  have hθ : 0 ≤ θ := div_nonneg hd hs0.le
  have hθ1 : θ ≤ 1 := (div_le_one hs0).mpr hd1
  have hθs : θ*s=d := by dsimp [θ]; field_simp
  have hmass : ∀ T,0 ≤ starTriangleMass x T := (balancedTrianglePacking x hx).nonneg
  have hsum : (∑ o : Option ι,o.elim h x)=b := by rw [Fintype.sum_option]; rfl
  have hsq : (∑ o : Option ι,(o.elim h x)^2)=h^2+∑ i,(x i)^2 := by rw [Fintype.sum_option]; rfl
  refine {
    mass := fun T => θ*starTriangleMass x T
    supported := ?_
    nonneg := fun T => mul_nonneg hθ (hmass T)
    pair_cap := ?_
    quota := ?_
    total := ?_ }
  · intro T hT
    rw [starTriangleMass_supported x T hT,mul_zero]
  · intro B hB
    rw [subsetMoment_mul]
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hB
    rw [Finset.prod_pair hij]
    have hrootcap (i : ι) : θ*(x i*(s-x i)) ≤ h*x i := by
      have hxi : x i ≤ s := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      have hc := mul_le_of_le_one_left (mul_nonneg (hx i) (sub_nonneg.mpr hxi)) hθ1
      nlinarith [mul_le_mul_of_nonneg_right hheavy (hx i),sq_nonneg (x i)]
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => simpa only [starTriangleMass_root_pair,Option.elim_none,Option.elim_some] using hrootcap j
    | some i =>
      cases j with
      | none =>
        rw [Finset.pair_comm,starTriangleMass_root_pair]
        simpa only [Option.elim_none,Option.elim_some,mul_comm h] using hrootcap i
      | some j =>
        rw [starTriangleMass_minor_pair x i j (fun h => hij (congrArg some h))]
        exact mul_le_of_le_one_left (mul_nonneg (hx i) (hx j)) hθ1
  · intro i
    rw [subsetMoment_mul,hsum]
    cases i with
    | none =>
      rw [starTriangleMass_root]
      simp only [Option.elim_none]
      exact (mul_nonpos_of_nonneg_of_nonpos hh (by dsimp [d] at hdh; linarith)).trans
        (mul_nonneg hθ (elementarySum_nonneg Finset.univ x (fun i _ => hx i) 2))
    | some i =>
      rw [starTriangleMass_singleton]
      simp only [Option.elim_some]
      have hsq := mul_le_mul_of_nonneg_right hθ1 (sq_nonneg (x i))
      have he := congrArg (fun z : ℝ => z*x i) hθs
      change x i*(d-x i) ≤ θ*(x i*(s-x i))
      nlinarith
  · rw [← Finset.mul_sum,starTriangleMass_total,hsum,hsq]
    let Q := ∑ i,(x i)^2
    let E := elementarySum Finset.univ x 2
    have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    have he : 2*E=s^2-Q := elementarySum_two_identity Finset.univ x
    have hbase : 3*b*E ≤ s*(b^2-h^2-Q) := by
      have hh1 : 0 ≤ (h-s)*s^2 := mul_nonneg (sub_nonneg.mpr hheavy) (sq_nonneg s)
      have hh2 : 0 ≤ (3*h+s)*Q := mul_nonneg (by linarith) hQ
      have he' := congrArg (fun z : ℝ => (3*b)*z) he
      dsimp [b] at *
      nlinarith
    apply (le_div_iff₀ (show 0 < 3*b by positivity)).mpr
    have hc := mul_le_mul_of_nonneg_left hbase hθ
    have heq := congrArg (fun z : ℝ => z*(b^2-h^2-Q)) hθs
    change (θ*E)*(3*b) ≤ d*(b^2-(h^2+Q))
    nlinarith

end Erdos1017
