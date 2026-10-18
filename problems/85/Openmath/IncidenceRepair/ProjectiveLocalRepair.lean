import Openmath.IncidenceRepair.Target
import Openmath.IncidenceRepair.GeometryDesign
import Openmath.IncidenceRepair.GeometryIntersection
import Openmath.IncidenceRepair.SourceNumerics
import Openmath.IncidenceRepair.DesignRepair

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

/-- Section 8 for the actual canonical spaces, arbitrary source and target fields,
and the actual coupled semilinear action. Only closeness is an input here;
constructing a close embedding is the remaining global theorem. -/
theorem projective_local_repair
    {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}
    (hn : 2 ≤ n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hclose : (repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) : ℝ) ≤
      (pointCount K n : ℝ) / 20) :
    (repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) : ℝ) ≤
      5 * (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ)^(n-1) ∧
    5 * (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ)^(n-1) ≤
      10 * (brokenFlags φ ψ : ℝ) / (flagDegree K n : ℝ) := by
  classical
  letI : Fintype (Point K n) := Fintype.ofFinite _
  let S := Finset.univ.filter (fun p : Point K n => φ p ≠ pointEmbedding σ A p)
  let B := Finset.univ.filter (fun H : Hyperplane K n => ψ H ≠ hyperplaneEmbedding σ A H)
  let a : ℝ := (Nat.card K : ℝ)^(n-1)
  let d : ℝ := flagDegree K n
  let lam : ℝ := ((Nat.card K ^ (n-1)-1)/(Nat.card K-1) : ℕ)
  let N : ℝ := pointCount K n
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have ha : 2 ≤ a := by
    dsimp [a]
    exact_mod_cast source_gap_ge_two (Nat.card K) n hq hn
  have hsplit : d = a + lam := by
    dsimp [d, a, lam, flagDegree]
    exact_mod_cast source_degree_split (Nat.card K) n hq (by omega)
  have hlam0 : 0 ≤ lam := by positivity
  have hd : 0 < d := by linarith
  have hda : d ≤ 2*a := by
    dsimp [d, a, flagDegree]
    exact_mod_cast source_degree_le_twice_gap (Nat.card K) n hq (by omega)
  have hN : N = Fintype.card (Point K n) := by
    dsimp [N, pointCount]
    rw [← point_card (K := K) (n := n), Nat.card_eq_fintype_card]
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hdist : (repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) : ℝ) =
      (S.card : ℝ) + B.card := by
    simp [repairDistance, S, B, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS : ∀ p, p ∈ S ↔ φ p ≠ pointEmbedding σ A p := by simp [S]
  have hB : ∀ H, H ∈ B ↔ ψ H ≠ hyperplaneEmbedding σ A H := by simp [B]
  have hpoint : ∀ p ∈ S,
      ∑ H, incidence (fun p H => Incident p H ∧ Incident (φ p) (hyperplaneEmbedding σ A H)) p H ≤ lam := by
    intro p hp
    have hb := wrong_point_intersection_card σ A p (φ p) ((hS p).1 hp)
    have he := sum_indicator_eq_natCard (fun H : Hyperplane K n => Incident p H ∧ Incident (φ p) (hyperplaneEmbedding σ A H))
    have hs : (∑ H, incidence (fun p H => Incident p H ∧ Incident (φ p) (hyperplaneEmbedding σ A H)) p H) =
        (Nat.card {H : Hyperplane K n // Incident p H ∧ Incident (φ p) (hyperplaneEmbedding σ A H)} : ℝ) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro H _
      dsimp [incidence]
      split_ifs <;> rfl
    rw [hs]
    dsimp [lam]
    exact_mod_cast hb
  have hhyper : ∀ H ∈ B,
      ∑ p, incidence (fun p H => Incident p H ∧ Incident (pointEmbedding σ A p) (ψ H)) p H ≤ lam := by
    intro H hH
    have hb := wrong_hyperplane_intersection_card σ A H (ψ H) ((hB H).1 hH)
    have he := sum_indicator_eq_natCard (fun p : Point K n => Incident p H ∧ Incident (pointEmbedding σ A p) (ψ H))
    have hs : (∑ p, incidence (fun p H => Incident p H ∧ Incident (pointEmbedding σ A p) (ψ H)) p H) =
        (Nat.card {p : Point K n // Incident p H ∧ Incident (pointEmbedding σ A p) (ψ H)} : ℝ) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro p _
      dsimp [incidence]
      split_ifs <;> rfl
    rw [hs]
    dsimp [lam]
    exact_mod_cast hb
  have h := design_local_repair Incident Incident φ (pointEmbedding σ A) ψ
    (hyperplaneEmbedding σ A) S B hS hB a d lam N ha hd hda (by linarith)
    hN hN hNpos projective_degree projective_dual_degree
    (projective_pair_design a d lam rfl rfl hsplit) hpoint hhyper (by rwa [hdist] at hclose)
  rw [brokenFlagSum_eq_card] at h
  simpa only [brokenFlags, hdist, a, d] using h

end Erdos85.IncidenceRepair
