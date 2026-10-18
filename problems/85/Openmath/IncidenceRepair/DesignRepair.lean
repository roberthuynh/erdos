import Openmath.IncidenceRepair.ErrorCounting
import Openmath.IncidenceRepair.PairedGap
import Openmath.IncidenceRepair.NumericBounds

/-! Integration of actual mixed-error counts, design variance and scalar repair.
This is a local theorem for a supplied close pair of reference maps. Constructing
the projective-semilinear reference maps remains a separate obligation. -/
noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

theorem design_local_repair
    {P H P' H' : Type*} [Fintype P] [Fintype H] [Nonempty P]
    [DecidableEq P] [DecidableEq H]
    (I : P → H → Prop) (J : P' → H' → Prop)
    (phi Gp : P → P') (psi Gh : H → H') (S : Finset P) (B : Finset H)
    (hS : ∀ p, p ∈ S ↔ phi p ≠ Gp p)
    (hB : ∀ h, h ∈ B ↔ psi h ≠ Gh h)
    (a d lam N : ℝ) (ha : 2 ≤ a) (hd : 0 < d) (hda : d ≤ 2*a)
    (halam : d - lam = a)
    (hNP : N = Fintype.card P) (hNH : N = Fintype.card H) (hN : 0 < N)
    (hdegree : ∀ p, ∑ h, incidence I p h = d)
    (hdual : ∀ h, ∑ p, incidence I p h = d)
    (hpair : ∀ p q, ∑ h, incidence I p h * incidence I q h =
      (if p = q then a else 0) + lam)
    (hpoint : ∀ p ∈ S,
      ∑ h, incidence (fun p h => I p h ∧ J (phi p) (Gh h)) p h ≤ lam)
    (hhyper : ∀ h ∈ B,
      ∑ p, incidence (fun p h => I p h ∧ J (Gp p) (psi h)) p h ≤ lam)
    (hclose : (S.card : ℝ) + B.card ≤ N / 20) :
    (S.card : ℝ) + B.card ≤ 5 * brokenFlagSum I J phi psi / a ∧
      5 * brokenFlagSum I J phi psi / a ≤ 10 * brokenFlagSum I J phi psi / d := by
  have herr := disjoint_error_count I J phi Gp psi Gh S B hS hB d lam
    hdegree hdual hpoint hhyper
  rw [halam] at herr
  have hparams := design_parameters I a d lam N hNP hdegree hdual hpair
  have hgap := paired_gap I S B a d lam N (brokenFlagSum I J phi psi)
    (by linarith) hd.le hNH hN hdegree hpair hparams herr
  have hT : 0 ≤ brokenFlagSum I J phi psi := by
    unfold brokenFlagSum
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro h _
    unfold incidence
    split_ifs <;> norm_num
  exact ⟨local_repair_bound ha hda hN (by positivity) hclose hgap,
    degree_repair_bound (by linarith) hd hda hT le_rfl⟩

end Erdos85.IncidenceRepair
