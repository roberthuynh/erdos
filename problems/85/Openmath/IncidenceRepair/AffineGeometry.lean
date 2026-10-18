import Openmath.IncidenceRepair.GeometryIntersection
import Openmath.IncidenceRepair.CertificateGeometry

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def affineVector (x : Fin n → K) : Coordinates K n := Fin.cons 1 x

lemma affineVector_ne_zero (x : Fin n → K) : affineVector x ≠ 0 := by
  intro h
  have := congr_fun h 0
  simpa [affineVector] using this

def affinePoint (x : Fin n → K) : Point K n :=
  Projectivization.mk K (affineVector x) (affineVector_ne_zero x)

def infinityHyperplane : Hyperplane K n := coordinateHyperplane 0

lemma affinePoint_injective : Function.Injective (affinePoint (K := K) (n := n)) := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).1 h
  have h0 := congr_fun ha 0
  have ha1 : a = 1 := by simpa [affineVector] using h0
  funext i
  have hi := congr_fun ha i.succ
  simpa [affineVector, ha1] using hi.symm

lemma affinePoint_not_infinity (x : Fin n → K) :
    ¬ Incident (affinePoint x) (infinityHyperplane (K := K)) := by
  unfold affinePoint infinityHyperplane coordinateHyperplane coordinatePoint Incident
  rw [Projectivization.orthogonal_mk]
  simp [affineVector]

/-- Every non-infinity projective point has its unique X₀=1 representative. -/
def affinePointEquiv : (Fin n → K) ≃ {p : Point K n // ¬ Incident p infinityHyperplane} := by
  refine Equiv.ofBijective (fun x => ⟨affinePoint x, affinePoint_not_infinity x⟩) ⟨?_, ?_⟩
  · intro x y h
    exact affinePoint_injective (congrArg Subtype.val h)
  · intro p
    have hp : p.val.rep 0 ≠ 0 := by
      simpa [infinityHyperplane, coordinateHyperplane_incident] using p.property
    refine ⟨fun i => p.val.rep i.succ / p.val.rep 0, ?_⟩
    apply Subtype.ext
    conv_rhs => rw [← Projectivization.mk_rep p.val]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨(p.val.rep 0)⁻¹, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [affineVector, hp]
    · simp [affineVector, div_eq_mul_inv, mul_comm]

lemma affine_points_card [Finite K] :
    Nat.card {p : Point K n // ¬ Incident p infinityHyperplane} = Nat.card K ^ n := by
  rw [← Nat.card_congr (affinePointEquiv (K := K) (n := n))]
  simp [Nat.card_fun]

lemma infinity_points_card [Finite K] :
    Nat.card {p : Point K n // Incident p infinityHyperplane} =
      (Nat.card K ^ n - 1) / (Nat.card K - 1) := incident_points_card _

lemma pointEmbedding_affine (σ : K →+* L) (x : Fin n → K) :
    pointEmbedding σ (LinearEquiv.refl L (Coordinates L n)) (affinePoint x) =
      affinePoint (fun i => σ (x i)) := by
  unfold affinePoint pointEmbedding
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' L _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [affineVector, semilinearVector, coordinateMap]
  · simp [affineVector, semilinearVector, coordinateMap]

lemma dualCoordinates_refl :
    dualCoordinates (LinearEquiv.refl L (Coordinates L n)) =
      LinearEquiv.refl L (Coordinates L n) := by
  simp [dualCoordinates, LinearEquiv.dualMap_refl]

lemma hyperplaneEmbedding_infinity (σ : K →+* L) :
    hyperplaneEmbedding σ (LinearEquiv.refl L (Coordinates L n)) infinityHyperplane =
      infinityHyperplane := by
  simp only [hyperplaneEmbedding, dualCoordinates_refl, infinityHyperplane,
    coordinateHyperplane, coordinatePoint, pointEmbedding, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' L _ _ _ _).2
  refine ⟨1, ?_⟩
  simpa only [one_smul, semilinearVector, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_apply, LinearMap.id_apply] using (coordinateMap_single σ 0).symm

lemma affine_hyperplanes_through_infinity_card [Finite K] (p : Point K n)
    (hp : Incident p infinityHyperplane) :
    Nat.card {H : Hyperplane K n // Incident p H ∧ H ≠ infinityHyperplane} =
      (Nat.card K ^ n - 1) / (Nat.card K - 1) - 1 := by
  classical
  let S := {H : Hyperplane K n // Incident p H}
  let H0 : S := ⟨infinityHyperplane, hp⟩
  let e : {H : Hyperplane K n // Incident p H ∧ H ≠ infinityHyperplane} ≃
      {H : S // H ≠ H0} := {
    toFun := fun H => ⟨⟨H.val, H.property.1⟩, fun he => H.property.2 (congrArg Subtype.val he)⟩
    invFun := fun H => ⟨H.val.val, H.val.property, fun he => H.property (Subtype.ext he)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  have hc : Nat.card {H : S // H ≠ H0} = Nat.card S - 1 := by
    letI : Fintype S := Fintype.ofFinite S
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [hc]
  exact congrArg (fun a : ℕ => a - 1) (incident_hyperplanes_card p)

def linearFiberEquivKernel {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] K) (b : K) (u : V) (hu : f u = b) :
    {v : V // f v = b} ≃ f.ker where
  toFun v := ⟨v.val - u, by simp [LinearMap.mem_ker, map_sub, v.property, hu]⟩
  invFun k := ⟨k.val + u, by
    have hk : f k.val = 0 := k.property
    simp [map_add, hk, hu]⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv k := by apply Subtype.ext; simp

lemma linear_fiber_card {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (hf : f ≠ 0) (b : K) :
    Nat.card {v : V // f v = b} = Nat.card K ^ (Module.finrank K V - 1) := by
  obtain ⟨u, hu⟩ := LinearMap.surjective hf b
  rw [Nat.card_congr (linearFiberEquivKernel f b u hu), Module.natCard_eq_pow_finrank (K := K)]
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  congr 1
  omega

lemma linear_fiber_one_card_le {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] K) :
    Nat.card {v : V // f v = 1} ≤ Nat.card K ^ (Module.finrank K V - 1) := by
  by_cases hf : f = 0
  · subst f
    have : IsEmpty {v : V // (0 : V →ₗ[K] K) v = 1} :=
      ⟨fun v => (zero_ne_one : (0 : K) ≠ 1) (by simpa using v.property)⟩
    simp only [Nat.card_of_isEmpty, Nat.zero_le]
  · exact (linear_fiber_card f hf 1).le

def affineFunctional (H : Hyperplane K n) : (Fin n → K) →ₗ[K] K :=
  dotProductBilin K K (fun i => H.rep i.succ)

lemma affinePoint_incident (x : Fin n → K) (H : Hyperplane K n) :
    Incident (affinePoint x) H ↔ affineFunctional H x = -H.rep 0 := by
  rw [affinePoint, incident_mk_iff]
  change (∑ i, affineVector x i * H.rep i = 0) ↔ _
  rw [Fin.sum_univ_succ]
  simp only [affineVector, Fin.cons_zero, Fin.cons_succ, one_mul]
  change H.rep 0 + ∑ i, x i * H.rep i.succ = 0 ↔
    (∑ i, H.rep i.succ * x i) = -H.rep 0
  simp_rw [mul_comm]
  rw [eq_neg_iff_add_eq_zero, add_comm]

lemma affineFunctional_ne_zero (H : Hyperplane K n) (hne : H ≠ infinityHyperplane) :
    affineFunctional H ≠ 0 := by
  intro hz
  apply hne
  apply hyperplane_forced_by_basis H 0
  intro i hi
  rw [coordinatePoint_incident]
  revert hi
  refine Fin.cases ?_ (fun j _ => ?_) i
  · intro hc
    exact False.elim (hc rfl)
  · have h := LinearMap.congr_fun hz (Pi.single j 1)
    simpa [affineFunctional] using h

/-- Every affine source hyperplane contains exactly q^(n-1) affine points. -/
lemma affine_hyperplane_points_card (H : Hyperplane K n) (hne : H ≠ infinityHyperplane) :
    Nat.card {x : Fin n → K // Incident (affinePoint x) H} = Nat.card K ^ (n - 1) := by
  let e : {x : Fin n → K // Incident (affinePoint x) H} ≃
      {x : Fin n → K // affineFunctional H x = -H.rep 0} :=
    Equiv.subtypeEquivRight (fun x => affinePoint_incident x H)
  rw [Nat.card_congr e, linear_fiber_card _ (affineFunctional_ne_zero H hne)]
  simp

lemma affine_hyperplane_infinity_points_card [Finite K]
    (H : Hyperplane K n) (hne : H ≠ infinityHyperplane) :
    Nat.card {p : Point K n // Incident p H ∧ Incident p infinityHyperplane} =
      (Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) :=
  common_incident_points_card H infinityHyperplane hne

lemma wrong_affine_hyperplane_intersection_card [Finite K] (hn : 2 ≤ n)
    (σ : K →+* L) (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (H : Hyperplane K n) (J : Hyperplane L n)
    (hne : J ≠ hyperplaneEmbedding σ A H) :
    Nat.card {x : Fin n → K // Incident (affinePoint x) H ∧
      Incident (pointEmbedding σ A (affinePoint x)) J} ≤ Nat.card K ^ (n - 2) := by
  let S := hyperplaneSubspace H ⊓ (pulledFunctional σ A J).ker
  let f : S →ₗ[K] K := (LinearMap.proj 0).comp S.subtype
  let g : {x : Fin n → K // Incident (affinePoint x) H ∧
      Incident (pointEmbedding σ A (affinePoint x)) J} → {v : S // f v = 1} := fun x =>
    ⟨⟨affineVector x.val, by
      constructor
      · exact (incident_mk_iff _ _ H).1 x.property.1
      · have hx := x.property.2
        simp only [affinePoint, pointEmbedding, Projectivization.map_mk, incident_mk_iff,
          hyperplaneSubspace_eq_ker] at hx
        exact hx⟩, by simp [f, affineVector]⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    have hv := congrArg (fun z : {v : S // f v = 1} => (z.val : Coordinates K n)) h
    funext i
    exact congr_fun hv i.succ
  have hcard := Nat.card_le_card_of_injective g hg
  have hbound := linear_fiber_one_card_le f
  have hdim : Module.finrank K S - 1 ≤ n - 2 := by
    have hd := wrong_hyperplane_intersection_finrank σ A H J hne
    change Module.finrank K S ≤ n - 1 at hd
    omega
  exact hcard.trans (hbound.trans (Nat.pow_le_pow_right (Finite.one_lt_card (α := K)).le hdim))

end Erdos85.IncidenceRepair
