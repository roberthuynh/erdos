import Openmath.IncidenceRepair.GeometryCoupling
import Openmath.IncidenceRepair.GeometryCounts

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

lemma equiv_matching_pair {I J : Type*} (e : I ≃ J) (i j : I) (i' j' : J)
    (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ e' : I ≃ J, e' i = i' ∧ e' j = j' := by
  classical
  let e₁ := e.trans (Equiv.swap (e i) i')
  have hi : e₁ i = i' := by simp [e₁]
  have hj : e₁ j ≠ i' := by
    rw [← hi]
    exact e₁.injective.ne hij.symm
  refine ⟨e₁.trans (Equiv.swap (e₁ j) j'), ?_, ?_⟩
  · simp [hi, Equiv.swap_apply_of_ne_of_ne hj.symm hij']
  · simp

variable {K : Type*} [Field K] {n : ℕ}

abbrev SourceFlag (K : Type*) [Field K] (n : ℕ) :=
  {pH : Point K n × Hyperplane K n // Incident pH.1 pH.2}

lemma pointEmbedding_id_eq_smul (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (p : Point K n) : pointEmbedding (RingHom.id K) A p = A • p := by
  induction p using Projectivization.ind with
  | h v hv => rfl

lemma dualCoordinates_one :
    dualCoordinates (1 : Coordinates K n ≃ₗ[K] Coordinates K n) = 1 := by
  apply LinearEquiv.ext
  intro h
  funext i
  have he := dualCoordinates_eval (1 : Coordinates K n ≃ₗ[K] Coordinates K n) h (Pi.single i 1)
  change dualCoordinates 1 h ⬝ᵥ Pi.single i 1 = h ⬝ᵥ Pi.single i 1 at he
  simpa using he

lemma dualCoordinates_mul (A B : Coordinates K n ≃ₗ[K] Coordinates K n) :
    dualCoordinates (A * B) = dualCoordinates A * dualCoordinates B := by
  apply LinearEquiv.ext
  intro h
  have he (v : Coordinates K n) :
      dualCoordinates (A * B) h ⬝ᵥ v =
        dualCoordinates A (dualCoordinates B h) ⬝ᵥ v := by
    simp only [dualCoordinates_eval]
    rfl
  funext i
  simpa using he (Pi.single i 1)

def mapSourceFlag (A : Coordinates K n ≃ₗ[K] Coordinates K n) (F : SourceFlag K n) :
    SourceFlag K n :=
  ⟨(A • F.1.1, dualCoordinates A • F.1.2), by
    have h := (embedding_incident_iff (RingHom.id K) A F.1.1 F.1.2).2 F.2
    simpa only [hyperplaneEmbedding, pointEmbedding_id_eq_smul] using h⟩

instance sourceFlagMulAction :
    MulAction (Coordinates K n ≃ₗ[K] Coordinates K n) (SourceFlag K n) where
  smul := mapSourceFlag
  one_smul F := by
    apply Subtype.ext
    change ((1 : Coordinates K n ≃ₗ[K] Coordinates K n) • F.1.1,
      dualCoordinates 1 • F.1.2) = F.1
    simp only [dualCoordinates_one, one_smul]
  mul_smul A B F := by
    apply Subtype.ext
    change ((A * B) • F.1.1, dualCoordinates (A * B) • F.1.2) =
      (A • B • F.1.1, dualCoordinates A • dualCoordinates B • F.1.2)
    simp only [dualCoordinates_mul, mul_smul]

lemma exists_flag_transport (F G : SourceFlag K n) :
    ∃ A : Coordinates K n ≃ₗ[K] Coordinates K n, A • F = G := by
  classical
  let f := coefficientFunctional F.1.2
  let g := coefficientFunctional G.1.2
  have hfv : f F.1.1.rep = 0 := by
    have h := (incident_iff_rep_mem F.1.1 F.1.2).1 F.2
    rw [hyperplaneSubspace_eq_ker] at h
    exact h
  have hgv : g G.1.1.rep = 0 := by
    have h := (incident_iff_rep_mem G.1.1 G.1.2).1 G.2
    rw [hyperplaneSubspace_eq_ker] at h
    exact h
  obtain ⟨I, b, i, j, hij, hp, hf⟩ := exists_basis_of_pairing_eq_zero hfv
    (coefficientFunctional_ne_zero F.1.2) F.1.1.rep_nonzero
  obtain ⟨J, c, i', j', hij', hq, hg⟩ := exists_basis_of_pairing_eq_zero hgv
    (coefficientFunctional_ne_zero G.1.2) G.1.1.rep_nonzero
  obtain ⟨e, hei, hej⟩ := equiv_matching_pair (b.indexEquiv c) i j i' j' hij hij'
  let A := b.equiv c e
  have hpoint : A F.1.1.rep = G.1.1.rep := by
    rw [hp, hq]
    simp [A, hei]
  have hfunctional : g.comp A.toLinearMap = f := by
    apply b.ext
    intro k
    change g (A (b k)) = f (b k)
    simp only [A, Module.Basis.equiv_apply, hf, hg,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, ← hej, e.injective.eq_iff]
  have hdual : dualCoordinates A F.1.2.rep = G.1.2.rep := by
    funext k
    have he := LinearMap.congr_fun hfunctional (A.symm (Pi.single k 1))
    have hd := dualCoordinates_eval A F.1.2.rep (Pi.single k 1)
    change g (A (A.symm (Pi.single k 1))) = f (A.symm (Pi.single k 1)) at he
    rw [A.apply_symm_apply] at he
    change G.1.2.rep ⬝ᵥ Pi.single k 1 = F.1.2.rep ⬝ᵥ A.symm (Pi.single k 1) at he
    rw [← he] at hd
    simpa using hd
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change A • F.1.1 = G.1.1
    rw [← Projectivization.mk_rep F.1.1, Projectivization.smul_mk]
    change Projectivization.mk K (A F.1.1.rep) _ = G.1.1
    simpa only [hpoint] using Projectivization.mk_rep G.1.1
  · change dualCoordinates A • F.1.2 = G.1.2
    rw [← Projectivization.mk_rep F.1.2, Projectivization.smul_mk]
    change Projectivization.mk K (dualCoordinates A F.1.2.rep) _ = G.1.2
    simpa only [hdual] using Projectivization.mk_rep G.1.2

instance sourceFlagPretransitive :
    MulAction.IsPretransitive (Coordinates K n ≃ₗ[K] Coordinates K n) (SourceFlag K n) where
  exists_smul_eq := exists_flag_transport

end Erdos85.IncidenceRepair
