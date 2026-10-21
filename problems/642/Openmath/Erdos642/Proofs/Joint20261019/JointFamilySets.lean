import Openmath.Erdos642.Proofs.Joint20261019.JointFamilySpectral

namespace Erdos642.Joint20261019.JointFamilySets
open JointFamilyGeometry JointFamilySpectral
open Erdos642.CampaignFe72210bContinuation3 MomentSmoothing
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def mean (f q : V→ℝ) : ℝ := ∑x,q x*f x

theorem mean_mix (f p q : V→ℝ) (a b : ℝ) :
    mean f (a • p+b • q)=a*mean f p+b*mean f q := by
  simp only [mean,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]
  simp_rw [mul_assoc,←Finset.mul_sum]

theorem continuous_mean (f : V→ℝ) : Continuous (mean f) := by unfold mean; fun_prop

theorem convex_mean_le (f : V→ℝ) (c : ℝ) : Convex ℝ {q | mean f q≤c} := by
  intro p hp q hq a b ha hb hab
  change mean f (a • p+b • q)≤c
  rw [mean_mix]
  have h1 := mul_le_mul_of_nonneg_left hp ha
  have h2 := mul_le_mul_of_nonneg_left hq hb
  calc
    _ ≤ a*c+b*c := add_le_add h1 h2
    _ = c := by rw [←add_mul,hab,one_mul]

theorem convex_mean_ge (f : V→ℝ) (c : ℝ) : Convex ℝ {q | c≤ mean f q} := by
  intro p hp q hq a b ha hb hab
  change c≤ mean f (a • p+b • q)
  rw [mean_mix]
  have h1 := mul_le_mul_of_nonneg_left hp ha
  have h2 := mul_le_mul_of_nonneg_left hq hb
  calc
    c = a*c+b*c := by rw [←add_mul,hab,one_mul]
    _ ≤ _ := add_le_add h1 h2

noncomputable def indicator (S : Finset V) : V→ℝ := fun x=>if x∈S then 1 else 0

theorem mean_indicator (S : Finset V) (q : V→ℝ) : mean (indicator S) q=mass q S := by
  simp [mean,indicator,mass,←Finset.sum_filter]

noncomputable def testSet {E : Submodule ℝ (EuclideanSpace ℝ V)} (pi : V→ℝ) (w:E) : Finset V :=
  excessSet (squares (w : EuclideanSpace ℝ V)) pi

noncomputable def goodSet (E : Submodule ℝ (EuclideanSpace ℝ V)) (W : Finset E) (pi : V→ℝ) (μ : ℝ) : Set (V→ℝ) :=
  {q | q∈stdSimplex ℝ V ∧ ∀w∈W,mass q (testSet pi w)-mass pi (testSet pi w)≤μ/4}

noncomputable def familySet (E : Submodule ℝ (EuclideanSpace ℝ V)) (W : Finset E) (pi f : V→ℝ) (μ : ℝ) : Set (V→ℝ) :=
  goodSet E W pi μ ∩ {q | mean f q≤μ/4}

noncomputable def badSet (S : Finset V) (pi : V→ℝ) (μ : ℝ) : Set (V→ℝ) :=
  stdSimplex ℝ V ∩ {q | μ/4+mass pi S≤ mean (indicator S) q}

theorem goodSet_closed (E : Submodule ℝ (EuclideanSpace ℝ V)) (W : Finset E) (pi : V→ℝ) (μ : ℝ) :
    IsClosed (goodSet E W pi μ) := by
  have he : goodSet E W pi μ = stdSimplex ℝ V ∩ ⋂w∈W,{q | mean (indicator (testSet pi w)) q≤μ/4+mass pi (testSet pi w)} := by
    ext q
    simp only [goodSet,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter,mean_indicator]
    constructor
    · rintro ⟨hq,hh⟩; exact ⟨hq,fun w hw=>by linarith [hh w hw]⟩
    · rintro ⟨hq,hh⟩; exact ⟨hq,fun w hw=>by linarith [hh w hw]⟩
  rw [he]
  exact (isCompact_stdSimplex ℝ V).isClosed.inter (isClosed_iInter fun w=>isClosed_iInter fun _=>isClosed_le (continuous_mean _) continuous_const)

theorem goodSet_convex (E : Submodule ℝ (EuclideanSpace ℝ V)) (W : Finset E) (pi : V→ℝ) (μ : ℝ) :
    Convex ℝ (goodSet E W pi μ) := by
  intro p hp q hq a b ha hb hab
  refine ⟨convex_stdSimplex ℝ V hp.1 hq.1 ha hb hab,?_⟩
  intro w hw
  have hpw : mean (indicator (testSet pi w)) p≤μ/4+mass pi (testSet pi w) := by rw [mean_indicator]; linarith [hp.2 w hw]
  have hqw : mean (indicator (testSet pi w)) q≤μ/4+mass pi (testSet pi w) := by rw [mean_indicator]; linarith [hq.2 w hw]
  have hh := convex_mean_le (indicator (testSet pi w)) (μ/4+mass pi (testSet pi w)) hpw hqw ha hb hab
  change mean (indicator (testSet pi w)) (a • p+b • q)≤_ at hh
  rw [mean_indicator] at hh
  linarith

theorem familySet_compact (E : Submodule ℝ (EuclideanSpace ℝ V)) (W : Finset E) (pi f : V→ℝ) (μ : ℝ) :
    IsCompact (familySet E W pi f μ) :=
  (isCompact_stdSimplex ℝ V).of_isClosed_subset
    ((goodSet_closed E W pi μ).inter (isClosed_le (continuous_mean f) continuous_const)) (fun _ h=>h.1.1)

theorem familySet_convex (E : Submodule ℝ (EuclideanSpace ℝ V)) (W : Finset E) (pi f : V→ℝ) (μ : ℝ) :
    Convex ℝ (familySet E W pi f μ) := (goodSet_convex E W pi μ).inter (convex_mean_le f _)

theorem badSet_compact (S : Finset V) (pi : V→ℝ) (μ : ℝ) : IsCompact (badSet S pi μ) :=
  (isCompact_stdSimplex ℝ V).inter_right (isClosed_le continuous_const (continuous_mean _))

theorem badSet_convex (S : Finset V) (pi : V→ℝ) (μ : ℝ) : Convex ℝ (badSet S pi μ) :=
  (convex_stdSimplex ℝ V).inter (convex_mean_ge _ _)

theorem familySet_energy (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (heig : ∀j,hA.eigenvalues j≤1) (W : Finset (slowSpace A hA))
    (pi : V→ℝ) (hpi : pi∈stdSimplex ℝ V) (μ : ℝ) (hμ : 0<μ) (hμ1 : μ≤1)
    (hunit : ∀w∈W,‖w‖=1)
    (hcover : ∀v:slowSpace A hA,‖v‖=1 → ∃w∈W,‖v-w‖≤μ/32)
    (f : V→ℝ) (hf : ∀x,0≤f x ∧ f x≤1) (hmean : μ≤ mean f pi)
    (q : V→ℝ) (hq : q∈familySet (slowSpace A hA) W pi f μ) :
    μ^2/4096≤Energy.energy A q := by
  by_contra hbad
  have he : Energy.energy A q≤μ^2/4096 := (lt_of_not_ge hbad).le
  have hp := low_energy_near_slow A hA heig q hq.1.1 μ hμ he
  obtain ⟨w,hw,hdist⟩ := net_near_root (slowSpace A hA) W μ hμ hμ1 hcover q hq.1.1
    ((slowSpace A hA).orthogonalProjectionOnto (root q)) hp
  have hl := l1_squares (root q) (w : EuclideanSpace ℝ V) (norm_root q hq.1.1) (hunit w hw)
  rw [squares_root q hq.1.1] at hl
  have hclose : l1 q (squares (w : EuclideanSpace ℝ V))≤3*μ/16 := by linarith
  have hsame := (squares_simplex (w : EuclideanSpace ℝ V) (hunit w hw)).2.trans hpi.2.symm
  have hdetect := excess_detects_mean q pi (squares (w : EuclideanSpace ℝ V)) f μ (3*μ/16) hsame hf hmean hq.2 hclose
  have hgood := hq.1.2 w hw
  change mass q (excessSet (squares (w : EuclideanSpace ℝ V)) pi)-mass pi (excessSet (squares (w : EuclideanSpace ℝ V)) pi)≤μ/4 at hgood
  linarith

end Erdos642.Joint20261019.JointFamilySets
