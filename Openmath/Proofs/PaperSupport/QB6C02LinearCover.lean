import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

universe u
namespace Erdos585.QB6C02LinearCover

open Finset

/-- Actual finite proper-block linear pair-cover counting helper. -/
def FisherLinearPairCover : Prop :=
  ∀ {V : Type u} [DecidableEq V] (A : Finset V) (F : Finset (Finset V)),
    3 ≤ A.card →
    (∀ T ∈ F, T ⊆ A ∧ 2 ≤ T.card ∧ T ≠ A) →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ T ∈ F, a ∈ T ∧ b ∈ T) →
    (∀ T ∈ F, ∀ U ∈ F, T ≠ U → (T ∩ U).card ≤ 1) →
    A.card ≤ F.card

variable {V : Type u} [DecidableEq V]

def pointDegree (F : Finset (Finset V)) (a : V) : ℕ :=
  (F.filter (fun T => a ∈ T)).card

noncomputable def incidence (A : Finset V) (F : Finset (Finset V)) : Matrix A F ℝ :=
  fun a T => if a.val ∈ T.val then 1 else 0

theorem point_degree_at_least_two {A : Finset V} {F : Finset (Finset V)}
    (hA : 3 ≤ A.card)
    (hblocks : ∀ T ∈ F, T ⊆ A ∧ 2 ≤ T.card ∧ T ≠ A)
    (hcover : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ T ∈ F, a ∈ T ∧ b ∈ T)
    {a : V} (ha : a ∈ A) : 2 ≤ pointDegree F a := by
  classical
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < A.card) a
  obtain ⟨T, hTF, haT, _⟩ := hcover a ha b hb hba.symm
  have hproper : T ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨(hblocks T hTF).1,
    (hblocks T hTF).2.2⟩
  obtain ⟨c, hc, hcT⟩ := (Finset.ssubset_iff_of_subset (hblocks T hTF).1).mp hproper
  have hac : a ≠ c := by
    intro heq
    exact hcT (heq ▸ haT)
  obtain ⟨U, hUF, haU, hcU⟩ := hcover a ha c hc hac
  have hTU : T ≠ U := by
    intro heq
    exact hcT (heq ▸ hcU)
  have hs : ({T, U} : Finset (Finset V)) ⊆ F.filter (fun R => a ∈ R) := by
    intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact Finset.mem_filter.mpr ⟨hTF, haT⟩
    · have heq : R = U := Finset.mem_singleton.mp hR
      subst R
      exact Finset.mem_filter.mpr ⟨hUF, haU⟩
  have hcard : ({T, U} : Finset (Finset V)).card = 2 := by simp [hTU]
  unfold pointDegree
  rw [← hcard]
  exact Finset.card_le_card hs

theorem common_block_count_one {A : Finset V} {F : Finset (Finset V)}
    (hcover : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ T ∈ F, a ∈ T ∧ b ∈ T)
    (hlinear : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → (T ∩ U).card ≤ 1)
    {a b : V} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    (F.filter (fun T => a ∈ T ∧ b ∈ T)).card = 1 := by
  classical
  obtain ⟨T, hTF, haT, hbT⟩ := hcover a ha b hb hab
  have huniq : ∀ U ∈ F, a ∈ U → b ∈ U → U = T := by
    intro U hUF haU hbU
    by_contra hUT
    have hs : ({a, b} : Finset V) ⊆ T ∩ U := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_inter.mpr ⟨haT, haU⟩
      · have hxb : x = b := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_inter.mpr ⟨hbT, hbU⟩
    have htwo : 2 ≤ (T ∩ U).card := by
      have := Finset.card_le_card hs
      simpa [hab] using this
    have hone := hlinear T hTF U hUF (fun hTU => hUT hTU.symm)
    omega
  have heq : F.filter (fun U => a ∈ U ∧ b ∈ U) = {T} := by
    ext U
    constructor
    · intro hU
      obtain ⟨hUF, haU, hbU⟩ := Finset.mem_filter.mp hU
      exact Finset.mem_singleton.mpr (huniq U hUF haU hbU)
    · intro hU
      have hUT : U = T := Finset.mem_singleton.mp hU
      subst U
      exact Finset.mem_filter.mpr ⟨hTF, haT, hbT⟩
  rw [heq]
  simp

theorem incidence_gram_entry (A : Finset V) (F : Finset (Finset V)) (a b : A) :
    (incidence A F * (incidence A F).transpose) a b =
      ((F.filter (fun T => a.val ∈ T ∧ b.val ∈ T)).card : ℝ) := by
  classical
  rw [Matrix.mul_apply]
  change (∑ T : F, (if a.val ∈ T.val then (1 : ℝ) else 0) *
      (if b.val ∈ T.val then (1 : ℝ) else 0)) = _
  rw [Finset.sum_coe_sort F (fun T : Finset V =>
    (if a.val ∈ T then (1 : ℝ) else 0) * (if b.val ∈ T then (1 : ℝ) else 0))]
  calc
    (∑ T ∈ F, (if a.val ∈ T then (1 : ℝ) else 0) *
      (if b.val ∈ T then (1 : ℝ) else 0)) =
      ∑ T ∈ F, if a.val ∈ T ∧ b.val ∈ T then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro T _
        by_cases haT : a.val ∈ T <;> by_cases hbT : b.val ∈ T <;> simp [haT, hbT]
    _ = _ := Finset.sum_boole _ _

theorem fisher_linear_pair_cover : FisherLinearPairCover.{u} := by
  classical
  intro V inst A F hA hblocks hcover hlinear
  let M : Matrix A F ℝ := incidence A F
  let d : A → ℝ := fun a => (pointDegree F a.val : ℝ) - 1
  have hd : ∀ a : A, 0 < d a := by
    intro a
    have htwo := point_degree_at_least_two hA hblocks hcover a.property
    have ht : (2 : ℝ) ≤ (pointDegree F a.val : ℝ) := by exact_mod_cast htwo
    dsimp [d]
    linarith
  have hgram : M * M.transpose =
      Matrix.diagonal d + Matrix.vecMulVec (fun _ : A => (1 : ℝ)) (star (fun _ : A => (1 : ℝ))) := by
    ext a b
    change (incidence A F * (incidence A F).transpose) a b = _
    rw [incidence_gram_entry]
    by_cases hab : a = b
    · subst b
      simp [Matrix.diagonal, Matrix.vecMulVec, d, pointDegree]
    · have habval : a.val ≠ b.val := by
        intro heq
        exact hab (Subtype.ext heq)
      rw [common_block_count_one hcover hlinear a.property b.property habval]
      simp [Matrix.diagonal, Matrix.vecMulVec, hab]
  have hpos : (M * M.transpose).PosDef := by
    rw [hgram]
    exact (Matrix.PosDef.diagonal hd).add_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : A => (1 : ℝ)))
  have hrank : (M * M.transpose).rank = Fintype.card A :=
    Matrix.rank_of_isUnit _ hpos.isUnit
  have hle : Fintype.card A ≤ Fintype.card F := by
    calc
      Fintype.card A = (M * M.transpose).rank := hrank.symm
      _ ≤ M.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card F := Matrix.rank_le_card_width _
  simpa using hle

#print axioms fisher_linear_pair_cover
#check fisher_linear_pair_cover

end Erdos585.QB6C02LinearCover
