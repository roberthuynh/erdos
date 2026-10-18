import Openmath.IncidenceRepair.Geometry

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair
variable {K : Type*} [Field K] {n : ℕ}

/-- Projectivizing a submodule is equivalent to ambient projective points lying in it. -/
def submodulePointEquiv (S : Submodule K (Coordinates K n)) :
    Projectivization K S ≃ {p : Point K n // p.rep ∈ S} := by
  let f : Projectivization K S → Point K n :=
    Projectivization.map S.subtype S.subtype_injective
  have hf : Function.Injective f := Projectivization.map_injective _ _
  have hmem (p : Projectivization K S) : (f p).rep ∈ S := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [f, Projectivization.map_mk]
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K (v : Coordinates K n)
        (by simpa using hv)
      change (Projectivization.mk K (v : Coordinates K n) _).rep ∈ S
      rw [← ha]
      exact S.smul_mem _ v.property
  refine Equiv.ofBijective (fun p => ⟨f p, hmem p⟩) ⟨?_, ?_⟩
  · intro p q h
    exact hf (congrArg Subtype.val h)
  · intro p
    let v : S := ⟨p.val.rep, p.property⟩
    have hv : v ≠ 0 := by
      intro h
      exact p.val.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    simp only [f, Projectivization.map_mk]
    exact Projectivization.mk_rep p.val

def coefficientFunctional (H : Hyperplane K n) : Coordinates K n →ₗ[K] K :=
  dotProductBilin K K H.rep

lemma coefficientFunctional_ne_zero (H : Hyperplane K n) :
    coefficientFunctional H ≠ 0 := by
  intro h
  apply H.rep_nonzero
  funext i
  have hi := LinearMap.congr_fun h (Pi.single i 1)
  simpa [coefficientFunctional] using hi

lemma hyperplaneSubspace_eq_ker (H : Hyperplane K n) :
    hyperplaneSubspace H = LinearMap.ker (coefficientFunctional H) := by
  ext v
  change (∑ i, v i * H.rep i = 0) ↔ dotProduct H.rep v = 0
  simp only [dotProduct, mul_comm]

lemma hyperplane_finrank (H : Hyperplane K n) :
    Module.finrank K (hyperplaneSubspace H) = n := by
  rw [hyperplaneSubspace_eq_ker]
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (coefficientFunctional_ne_zero H)
  have h' : Module.finrank K (coefficientFunctional H).ker + 1 = n + 1 := by
    simpa [Coordinates] using h
  omega

/-- Actual point degree in one source hyperplane, in geometric-series form. -/
lemma incident_points_card_sum [Finite K] (H : Hyperplane K n) :
    Nat.card {p : Point K n // Incident p H} = ∑ i ∈ Finset.range n, Nat.card K ^ i := by
  have e : {p : Point K n // Incident p H} ≃
      {p : Point K n // p.rep ∈ hyperplaneSubspace H} :=
    Equiv.subtypeEquivRight (fun p => incident_iff_rep_mem p H)
  rw [Nat.card_congr e, ← Nat.card_congr (submodulePointEquiv (hyperplaneSubspace H))]
  exact Projectivization.card_of_finrank K (hyperplaneSubspace H) (hyperplane_finrank H)

lemma functional_eq_smul_of_ker_eq {V : Type*} [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) (hf : f ≠ 0) (hker : f.ker = g.ker) :
    ∃ c : K, g = c • f := by
  obtain ⟨u, hu⟩ := LinearMap.surjective hf 1
  refine ⟨g u, ?_⟩
  ext x
  have hx : x - f x • u ∈ f.ker := by
    simp [LinearMap.mem_ker, hu]
  rw [hker] at hx
  have hg : g x - f x * g u = 0 := by
    simpa [LinearMap.mem_ker] using hx
  simpa [mul_comm] using sub_eq_zero.mp hg

lemma hyperplaneSubspace_injective :
    Function.Injective (hyperplaneSubspace : Hyperplane K n → Submodule K (Coordinates K n)) := by
  intro H J h
  have hk : (coefficientFunctional H).ker = (coefficientFunctional J).ker := by
    simpa only [← hyperplaneSubspace_eq_ker] using h
  obtain ⟨c, hc⟩ := functional_eq_smul_of_ker_eq _ _ (coefficientFunctional_ne_zero H) hk
  have hv : c • H.rep = J.rep := by
    funext i
    have hi := LinearMap.congr_fun hc (Pi.single i 1)
    simpa [coefficientFunctional] using hi.symm
  rw [← Projectivization.mk_rep H, ← Projectivization.mk_rep J]
  exact ((Projectivization.mk_eq_mk_iff' K _ _ _ _).2 ⟨c, hv⟩).symm

lemma distinct_hyperplanes_sup (H J : Hyperplane K n) (hne : H ≠ J) :
    hyperplaneSubspace H ⊔ hyperplaneSubspace J = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hdim := Submodule.finrank_le (hyperplaneSubspace H ⊔ hyperplaneSubspace J)
  have hstrict : hyperplaneSubspace H < hyperplaneSubspace H ⊔ hyperplaneSubspace J := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hj : hyperplaneSubspace J ≤ hyperplaneSubspace H := by
      rw [he]
      exact le_sup_right
    have heq : hyperplaneSubspace J = hyperplaneSubspace H :=
      Submodule.eq_of_le_of_finrank_eq hj (by rw [hyperplane_finrank, hyperplane_finrank])
    exact hne (hyperplaneSubspace_injective heq.symm)
  have hlt := Submodule.finrank_lt_finrank_of_lt hstrict
  rw [hyperplane_finrank] at hlt
  have hamb : Module.finrank K (Coordinates K n) = n + 1 := by simp [Coordinates]
  rw [hamb] at hdim ⊢
  omega

lemma hyperplane_intersection_finrank (H J : Hyperplane K n) (hne : H ≠ J) :
    Module.finrank K ↥(hyperplaneSubspace H ⊓ hyperplaneSubspace J) = n - 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (hyperplaneSubspace H) (hyperplaneSubspace J)
  rw [distinct_hyperplanes_sup H J hne, finrank_top,
    hyperplane_finrank, hyperplane_finrank] at h
  have hamb : Module.finrank K (Coordinates K n) = n + 1 := by simp [Coordinates]
  rw [hamb] at h
  omega

lemma incident_points_card [Finite K] (H : Hyperplane K n) :
    Nat.card {p : Point K n // Incident p H} =
      (Nat.card K ^ n - 1) / (Nat.card K - 1) := by
  rw [incident_points_card_sum]
  exact Nat.geomSum_eq (Finite.one_lt_card (α := K)) n

lemma incident_symm (p H : Point K n) : Incident p H ↔ Incident H p := by
  rw [incident_iff_rep_mem, incident_iff_rep_mem]
  change (∑ i, p.rep i * H.rep i = 0) ↔ (∑ i, H.rep i * p.rep i = 0)
  simp only [mul_comm]

lemma incident_hyperplanes_card [Finite K] (p : Point K n) :
    Nat.card {H : Hyperplane K n // Incident p H} =
      (Nat.card K ^ n - 1) / (Nat.card K - 1) := by
  let e : {H : Hyperplane K n // Incident p H} ≃ {H : Point K n // Incident H p} :=
    Equiv.subtypeEquivRight (fun H => incident_symm p H)
  rw [Nat.card_congr e, incident_points_card]

lemma common_incident_points_card [Finite K] (H J : Hyperplane K n) (hne : H ≠ J) :
    Nat.card {p : Point K n // Incident p H ∧ Incident p J} =
      (Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) := by
  let S := hyperplaneSubspace H ⊓ hyperplaneSubspace J
  let e : {p : Point K n // Incident p H ∧ Incident p J} ≃
      {p : Point K n // p.rep ∈ S} :=
    Equiv.subtypeEquivRight (fun p => by
      simp only [S, Submodule.mem_inf, incident_iff_rep_mem])
  rw [Nat.card_congr e, ← Nat.card_congr (submodulePointEquiv S)]
  rw [Projectivization.card_of_finrank K S (hyperplane_intersection_finrank H J hne)]
  exact Nat.geomSum_eq (Finite.one_lt_card (α := K)) (n - 1)

lemma common_incident_hyperplanes_card [Finite K] (p q : Point K n) (hne : p ≠ q) :
    Nat.card {H : Hyperplane K n // Incident p H ∧ Incident q H} =
      (Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) := by
  let e : {H : Hyperplane K n // Incident p H ∧ Incident q H} ≃
      {H : Point K n // Incident H p ∧ Incident H q} :=
    Equiv.subtypeEquivRight (fun H => by rw [incident_symm p H, incident_symm q H])
  rw [Nat.card_congr e, common_incident_points_card p q hne]

end Erdos85.IncidenceRepair
