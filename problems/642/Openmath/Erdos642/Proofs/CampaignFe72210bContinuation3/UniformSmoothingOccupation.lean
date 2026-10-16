import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.PoissonTilt
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CoordinateGrid
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.LevelSetOccupation

/-! Actual fixed-family occupation from derived finite coordinates and bounded Poisson tails. -/
namespace Erdos642.CampaignFe72210bContinuation3.UniformSmoothingOccupation
open Erdos642.FiniteMarkov Matrix
open Erdos642.CampaignFe72210bContinuation3
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def mean (u f : V → ℝ) : ℝ := ∑ x, u x ^ 2 * f x

omit [DecidableEq V] in
theorem average_mean (C : Chain V) (u f : V → ℝ)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2) :
    mean u (PoissonTilt.average C f) = mean u f := by
  unfold mean PoissonTilt.average
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (∑ x, u x ^ 2 * C.transition x y) * f y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hstat]

theorem smooth_mean (C : Chain V) (u f : V → ℝ)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2) (r : ℕ) :
    mean u (PoissonTilt.smooth C r f) = mean u f := by
  induction r with
  | zero => rw [PoissonTilt.smooth_zero]
  | succ r ih =>
    have he : PoissonTilt.smooth C (r+1) f = PoissonTilt.average C (PoissonTilt.smooth C r f) := by
      funext x
      exact PoissonTilt.smooth_succ C r f x
    rw [he, average_mean C u _ hstat, ih]

theorem projected_mean (C : Chain V) (u : V → ℝ) (huPos : ∀ x, 0 < u x)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2)
    (E : Submodule ℝ (EuclideanSpace ℝ V)) (hroot : WithLp.toLp 2 u ∈ E)
    (r : ℕ) (f : V → ℝ) :
    mean u (CoordinateGrid.projectedFunction C u E r f) = mean u f := by
  have hi : inner ℝ (CoordinateGrid.weightedVec u (CoordinateGrid.projectedFunction C u E r f))
      (WithLp.toLp 2 u) =
      inner ℝ (CoordinateGrid.weightedVec u ((C.transition ^ r) *ᵥ f)) (WithLp.toLp 2 u) := by
    rw [CoordinateGrid.weightedVec_projectedFunction C u huPos]
    exact E.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨WithLp.toLp 2 u, hroot⟩ _
  have hm : mean u (CoordinateGrid.projectedFunction C u E r f) =
      mean u (PoissonTilt.smooth C r f) := by
    change (∑ x, u x ^ 2 * CoordinateGrid.projectedFunction C u E r f x) =
      ∑ x, u x ^ 2 * PoissonTilt.smooth C r f x
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, CoordinateGrid.weightedVec,
      WithLp.ofLp_toLp, Pi.star_apply, star_trivial, PoissonTilt.smooth, pow_two, mul_assoc] using hi
  exact hm.trans (smooth_mean C u f hstat r)

omit [Fintype V] [DecidableEq V] in
theorem vertexSum_comparison (f h v : V → ℝ) (δ : ℝ)
    (hpoint : ∀ z, h z + v z - 2*δ ≤ f z) {n : ℕ} (x : V) (p : Path V n) :
    Chain.vertexSum h x p + Chain.vertexSum v x p - 2*δ*((n+1:ℕ):ℝ) ≤
      Chain.vertexSum f x p := by
  induction n generalizing x with
  | zero => simpa only [Chain.vertexSum, Nat.cast_zero, Nat.cast_one, zero_add, mul_one] using hpoint x
  | succ n ih =>
    rcases p with ⟨y,p⟩
    simp only [Chain.vertexSum, Nat.cast_add, Nat.cast_one]
    have hh := ih y p
    push_cast at hh
    have hx := hpoint x
    nlinarith

/-- Raw generic supplier. The spectral subspace/tail are structural inputs; the finite cover,
projected means/norms, signed-center tails, and actual family concentration are all derived. -/
theorem fixed_family_tail (C : Chain V) (u : V → ℝ)
    (huPos : ∀ x, 0 < u x) (hu : (∑ x, u x ^ 2) = 1)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hA : (C.similarTransition u).IsHermitian)
    (hAu : C.similarTransition u *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (C.similarTransition u *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (C.similarTransition u *ᵥ h) ≤ (1-γ)*∑ y, h y^2)
    (N D : ℕ) (hN : 1 ≤ N) (hDN : D ≤ N)
    (hatom : ∀ x, 1/(50*(N:ℝ)) ≤ u x^2)
    (E : Submodule ℝ (EuclideanSpace ℝ V)) (e : OrthonormalBasis (Fin D) ℝ E)
    (hroot : WithLp.toLp 2 u ∈ E)
    (F : Finset (V → ℝ)) (hf : ∀ f ∈ F, ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hmean : ∀ f ∈ F, μ ≤ mean u f)
    (r : ℕ) (hr : 1 ≤ r)
    (htail : ∀ f ∈ F, ∀ x,
      |PoissonTilt.smooth C r f x - CoordinateGrid.projectedFunction C u E r f x| ≤ μ/1024)
    (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n-1)
      (fun y p => ∃ f ∈ F, Chain.vertexSum f y p ≤ μ*(n:ℝ)/4) x ≤
      (F.card:ℝ)*(1+μ/16)*Real.exp (-μ^2*(n:ℝ)/(256*(r:ℝ))) +
      (CoordinateGrid.alphabet N μ ^ D : ℕ)*(⌈2/(μ/1024)⌉₊:ℝ)*(2/u x^2)*
        Real.exp (-γ*μ*(n:ℝ)/65536) := by
  classical
  obtain ⟨R,hRF,hR,hcover⟩ := CoordinateGrid.exists_projected_coordinate_net hN hDN hμ
    C u huPos hu hstat hatom E e r F hf
  let fast : V → Path V (n-1) → Prop := fun y p => ∃ f ∈ F,
    Chain.vertexSum (fun z => f z - PoissonTilt.smooth C r f z) y p ≤ -(μ/8)*(n:ℝ)
  let slow : V → Path V (n-1) → Prop := fun y p => ∃ v ∈ R,
    Chain.vertexSum v y p < 255*μ*(n:ℝ)/512
  have hfast : C.eventMass (n-1) fast x ≤
      (F.card:ℝ)*(1+μ/16)*Real.exp (-μ^2*(n:ℝ)/(256*(r:ℝ))) := by
    apply (C.eventMass_biUnion_le F _ x).trans
    calc
      _ ≤ ∑ _f ∈ F, (1+μ/16)*Real.exp (-μ^2*(n:ℝ)/(256*(r:ℝ))) := by
        apply Finset.sum_le_sum
        intro f hff
        have hh := PoissonTilt.smoothing_lower_tail C f (fun z => (hf f hff z).1)
          (fun z => (hf f hff z).2) r hr (μ/8) (by positivity) n hn x
        have hpref : 1 + (μ/8)/2 = 1+μ/16 := by ring
        have hexp : -(μ/8)^2*(n:ℝ)/(4*(r:ℝ)) = -μ^2*(n:ℝ)/(256*(r:ℝ)) := by ring
        rw [hpref, hexp] at hh
        exact hh
      _ = _ := by simp; ring
  have hslow : C.eventMass (n-1) slow x ≤
      (CoordinateGrid.alphabet N μ ^ D : ℕ)*(⌈2/(μ/1024)⌉₊:ℝ)*(2/u x^2)*
        Real.exp (-γ*μ*(n:ℝ)/65536) := by
    apply (C.eventMass_biUnion_le R _ x).trans
    calc
      _ ≤ ∑ _v ∈ R, (⌈2/(μ/1024)⌉₊:ℝ)*(2/u x^2)*Real.exp (-γ*μ*(n:ℝ)/65536) := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨f,hff,rfl⟩ := Finset.mem_image.mp (hRF hv)
        apply Erdos642.Continuation3.LevelSetOccupation.signed_center_tail C u huPos hu
          γ hγ hγ1 hA hAu hpos hgap _ μ (μ/1024) hμ hμ1 (by positivity) le_rfl ?_ ?_ n hn x
        · intro z
          have hb := PoissonTilt.smooth_bounds C f (fun y => (hf f hff y).1)
            (fun y => (hf f hff y).2) r z
          have he := abs_le.mp (htail f hff z)
          constructor <;> linarith
        · change μ ≤ mean u (CoordinateGrid.projectedFunction C u E r f)
          rw [projected_mean C u huPos hstat E hroot r f]
          exact hmean f hff
      _ = (R.card:ℝ)*((⌈2/(μ/1024)⌉₊:ℝ)*(2/u x^2)*Real.exp (-γ*μ*(n:ℝ)/65536)) := by simp
      _ ≤ _ := by
        have hc : (R.card:ℝ) ≤ (CoordinateGrid.alphabet N μ ^ D : ℕ) := by exact_mod_cast hR
        have hh := mul_le_mul_of_nonneg_right hc
          (show 0 ≤ (⌈2/(μ/1024)⌉₊:ℝ)*(2/u x^2)*Real.exp (-γ*μ*(n:ℝ)/65536) by positivity)
        simpa only [mul_assoc, Nat.cast_pow] using hh
  have hcontain := C.eventMass_mono
    (fun y p => ∃ f ∈ F, Chain.vertexSum f y p ≤ μ*(n:ℝ)/4)
    (fun y p => fast y p ∨ slow y p) (by
      intro y p hp
      by_contra hbad
      have hnot := not_or.mp hbad
      obtain ⟨f,hff,hlow⟩ := hp
      obtain ⟨v,hv,hvapprox⟩ := hcover f hff
      have hfastgood : -(μ/8)*(n:ℝ) <
          Chain.vertexSum (fun z => f z - PoissonTilt.smooth C r f z) y p := by
        by_contra hh
        exact hnot.1 ⟨f,hff,not_lt.mp hh⟩
      have hslowgood : 255*μ*(n:ℝ)/512 ≤ Chain.vertexSum v y p := by
        by_contra hh
        exact hnot.2 ⟨v,hv,not_le.mp hh⟩
      have hpoint : ∀ z, (f z - PoissonTilt.smooth C r f z) + v z - 2*(μ/1024) ≤ f z := by
        intro z
        have he := abs_le.mp (htail f hff z)
        have hg := abs_le.mp (hvapprox z)
        change -CoordinateGrid.eta μ ≤ _ ∧ _ ≤ CoordinateGrid.eta μ at hg
        unfold CoordinateGrid.eta at hg
        linarith
      have hh := vertexSum_comparison f (fun z => f z-PoissonTilt.smooth C r f z) v
        (μ/1024) hpoint y p
      have he : ((n-1+1:ℕ):ℝ) = (n:ℝ) := by congr 1; omega
      rw [he] at hh
      have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      nlinarith [mul_pos hμ hnpos]) x
  exact hcontain.trans ((C.eventMass_union_le fast slow x).trans (add_le_add hfast hslow))

end Erdos642.CampaignFe72210bContinuation3.UniformSmoothingOccupation
