import Openmath.IncidenceRepair.Geometry

/-! Exact target statement. This file DEFINES the proposition to prove; it does
not claim the main theorem. Counts are on original points, hyperplanes, flags,
and ordered full frames, with each original object counted once. -/

noncomputable section
namespace Erdos85.IncidenceRepair

variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}

/-- Number of original source flags broken by the two arbitrary maps. -/
def brokenFlags (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) : ℕ :=
  Nat.card {pH : Point K n × Hyperplane K n // Incident pH.1 pH.2 ∧
    ¬ Incident (φ pH.1) (ψ pH.2)}

/-- Proportion of uniform ordered source frames whose point images remain frames. -/
def frameSurvival (φ : Point K n → Point L n) : ℝ :=
  (Nat.card {F : Frame K n // IsFrame (φ ∘ F.1)} : ℝ) / Nat.card (Frame K n)

def pointCount (K : Type*) [Field K] (n : ℕ) : ℕ :=
  (Nat.card K ^ (n + 1) - 1) / (Nat.card K - 1)

def flagDegree (K : Type*) [Field K] (n : ℕ) : ℕ :=
  (Nat.card K ^ n - 1) / (Nat.card K - 1)

/-- The error density has the exact denominator N d from the published theorem. -/
def errorDensity (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) : ℝ :=
  (brokenFlags φ ψ : ℝ) / ((pointCount K n : ℝ) * (flagDegree K n : ℝ))

/-- Paired Hamming distance counts points AND hyperplanes. -/
def repairDistance (φ Gp : Point K n → Point L n)
    (ψ Gh : Hyperplane K n → Hyperplane L n) : ℕ :=
  Nat.card {p : Point K n // φ p ≠ Gp p} +
  Nat.card {H : Hyperplane K n // ψ H ≠ Gh H}

/-- The full published projective-incidence repair claim, with no supplier hypotheses.
Finite fields are arbitrary and need not share cardinality or characteristic.
A target linear equivalence is exactly an invertible (n+1) by (n+1) matrix.
The hyperplane map is constrained to its coupled target-field span action. -/
def RepairClaim (K L : Type*) [Field K] [Field L] [Finite K] [Finite L] (n : ℕ) : Prop :=
  2 ≤ n →
  ∀ (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n),
    0 < frameSurvival φ →
    errorDensity φ ψ ≤ frameSurvival φ / (10 ^ 9 * (n : ℝ) ^ 2) →
    ∃ (σ : K →+* L) (A : Coordinates L n ≃ₗ[L] Coordinates L n)
      (Gh : Hyperplane K n → Hyperplane L n),
      Coupled σ A Gh ∧
      (repairDistance φ (pointEmbedding σ A) ψ Gh : ℝ) ≤
        5 * (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ) ^ (n - 1) ∧
      5 * (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ) ^ (n - 1) ≤
        10 * (brokenFlags φ ψ : ℝ) / (flagDegree K n : ℝ)

end Erdos85.IncidenceRepair
