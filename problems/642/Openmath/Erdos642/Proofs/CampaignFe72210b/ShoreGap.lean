import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreNormalization
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphEigenvectors
import Openmath.Erdos642.Proofs.CampaignFe72210b.BipartiteSigns
import Openmath.Erdos642.Proofs.CampaignFe72210b.SquaredSpectralGap

/-! The genuine shore gap derived from both exceptional full-graph eigenspaces. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (s : Set V) [DecidablePred (· ∈ s)]

noncomputable def shoreExtend (f : s → ℝ) (x : V) : ℝ :=
  if hx : x ∈ s then f ⟨x, hx⟩ else 0

omit [DecidableEq V] in
theorem shoreExtend_sum_mul (f : s → ℝ) (g : V → ℝ) :
    (∑ x, shoreExtend s f x * g x) = ∑ x : s, f x * g x.val := by
  exact Finset.sum_congr_set s (fun x => shoreExtend s f x * g x)
    (fun x : s => f x * g x.val)
    (fun x hx => by simp [shoreExtend, hx]) (fun x hx => by simp [shoreExtend, hx])

omit [DecidableEq V] in
theorem shoreExtend_sq_sum (f : s → ℝ) :
    (∑ x, shoreExtend s f x ^ 2) = ∑ x : s, f x ^ 2 := by
  exact Finset.sum_congr_set s (fun x => shoreExtend s f x ^ 2)
    (fun x : s => f x ^ 2)
    (fun x hx => by simp [shoreExtend, hx]) (fun x hx => by simp [shoreExtend, hx])

omit [DecidableEq V] in
theorem shoreExtend_mulVec (B : Matrix V V ℝ) (f : s → ℝ) (x : V) :
    (B *ᵥ shoreExtend s f) x = ∑ y : s, B x y.val * f y := by
  change (∑ y, B x y * shoreExtend s f y) = _
  exact Finset.sum_congr_set s (fun y => B x y * shoreExtend s f y)
    (fun y : s => B x y.val * f y)
    (fun y hy => by simp [shoreExtend, hy]) (fun y hy => by simp [shoreExtend, hy])

omit [DecidableEq V] in
theorem shoreExtend_quadratic (B : Matrix V V ℝ) (f : s → ℝ) :
    dotProduct (shoreExtend s f) (B *ᵥ shoreExtend s f) =
      dotProduct f ((B.submatrix Subtype.val Subtype.val) *ᵥ f) := by
  change (∑ x, shoreExtend s f x * (B *ᵥ shoreExtend s f) x) = _
  rw [shoreExtend_sum_mul]
  simp_rw [shoreExtend_mulVec]
  rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem shoreExtend_unitRoot_orthogonal [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (f : s → ℝ) (hf : dotProduct f (shoreRoot G s) = 0) :
    dotProduct (shoreExtend s f) (unitDegreeRoot G) = 0 := by
  have he := ne_of_gt (Real.sqrt_pos.2 (shore_edge_pos G s t hbi hdeg))
  have hdiv : (∑ x : s, f x * degreeRoot G x.val) /
      Real.sqrt (G.edgeFinset.card : ℝ) = 0 := by
    simpa only [dotProduct, shoreRoot, degreeRoot, mul_div_assoc, Finset.sum_div] using hf
  have hsum : (∑ x : s, f x * degreeRoot G x.val) = 0 := by
    exact (div_eq_zero_iff).mp hdiv |>.resolve_right he
  change (∑ x, shoreExtend s f x * unitDegreeRoot G x) = 0
  rw [shoreExtend_sum_mul]
  simp_rw [unitDegreeRoot, ← mul_div_assoc]
  rw [← Finset.sum_div, hsum, zero_div]

omit [DecidableEq V] in
theorem shoreExtend_signedRoot_orthogonal [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (f : s → ℝ) (hf : dotProduct f (shoreRoot G s) = 0) :
    dotProduct (shoreExtend s f) (signedUnitDegreeRoot G (bipartiteSign s)) = 0 := by
  have hz := shoreExtend_unitRoot_orthogonal s G t hbi hdeg f hf
  change (∑ x, shoreExtend s f x * signedUnitDegreeRoot G (bipartiteSign s) x) = 0
  rw [shoreExtend_sum_mul]
  change (∑ x, shoreExtend s f x * unitDegreeRoot G x) = 0 at hz
  rw [shoreExtend_sum_mul] at hz
  simpa only [signedUnitDegreeRoot, bipartiteSign, Subtype.property, if_true, one_mul] using hz

/-- The actual shore quadratic gap follows from the original full spectral premises. -/
theorem shore_quadratic_gap [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (f : s → ℝ) (hf : dotProduct f (shoreRoot G s) = 0) :
    dotProduct f (((normalizedAdjacency G ^ 2).submatrix Subtype.val Subtype.val) *ᵥ f) ≤
      (1 - γ) * ∑ x : s, f x ^ 2 := by
  have : Nonempty V := ⟨(Classical.choice (inferInstance : Nonempty s)).val⟩
  rcases hgap with ⟨hγ, hγ1, _, _, hplus, hminus, hrest⟩
  have hb := hermitian_squared_gap (normalizedAdjacency G)
    (normalizedAdjacency_isHermitian G) (unitDegreeRoot G)
    (signedUnitDegreeRoot G (bipartiteSign s))
    (unitDegreeRoot_sum_sq G hdeg)
    (signedUnitDegreeRoot_sum_sq G hdeg (bipartiteSign s) (bipartiteSign_sq s))
    (normalizedAdjacency_unitDegreeRoot G hdeg)
    (normalizedAdjacency_signedUnitDegreeRoot G hdeg (bipartiteSign s)
      (bipartiteSign_flip G hbi))
    hplus hminus (1 - γ) (by linarith) hrest (shoreExtend s f)
    (shoreExtend_unitRoot_orthogonal s G t hbi hdeg f hf)
    (shoreExtend_signedRoot_orthogonal s G t hbi hdeg f hf)
  rw [shoreExtend_quadratic, shoreExtend_sq_sum] at hb
  have hs : 0 ≤ ∑ x : s, f x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc : (1 - γ) ^ 2 ≤ 1 - γ := by nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_right hc hs)

/-- The same derived gap in the exact chain interface consumed by SpectralMoment. -/
theorem shore_chain_gap [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x)
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (f : s → ℝ) (hf : dotProduct f (shoreRoot G s) = 0) :
    dotProduct f (((shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s)) *ᵥ f) ≤
      (1 - γ) * ∑ x : s, f x ^ 2 := by
  rw [shore_similarTransition G s t hbi hdeg]
  exact shore_quadratic_gap s G t hbi hdeg γ hgap f hf

end Erdos642.CampaignFe72210b
