import Openmath.Erdos642.Proofs.Joint20261019.JointFamilySets
import Openmath.Erdos642.Proofs.Joint20261019.ConvexTail
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents

namespace Erdos642.Joint20261019.JointFamily
open Matrix Erdos642.FiniteMarkov
open Erdos642.CampaignFe72210bContinuation3 MomentSmoothing
open JointFamilyGeometry JointFamilySpectral JointFamilySets
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common-net occupation bound has dimension-only entropy and the original path law. -/
theorem fixed_family_tail (C : Chain V) (u : V→ℝ) (hu : ∀x,0<u x)
    (hun : ∑x,u x^2=1) (hA : (C.similarTransition u).IsHermitian)
    (hpos : ∀f,0≤dotProduct f (C.similarTransition u*ᵥf))
    (γ : ℝ) (hγ : 0≤γ)
    (hgap : ∀f:V→ℝ,dotProduct f u=0 → dotProduct f (C.similarTransition u*ᵥf)≤(1-γ)*∑x,f x^2)
    (F : Finset (V→ℝ)) (hf : ∀f∈F,∀x,0≤f x ∧ f x≤1)
    (μ : ℝ) (hμ : 0<μ) (hμ1 : μ≤1)
    (hmean : ∀f∈F,μ≤∑x,u x^2*f x)
    (n : ℕ) (hn : 1≤n) (x : V) :
    C.eventMass (n-1) (fun y p=>∃f∈F,Chain.vertexSum f y p≤μ*(n:ℝ)/4) x ≤
      (F.card:ℝ)*(1/(u x)^2)*Real.exp (-μ^2*(n:ℝ)/4096)+
      (65/μ)^Module.finrank ℝ (slowSpace (C.similarTransition u) hA)*(1/(u x)^2)*
        Real.exp (-γ*μ^2*(n:ℝ)/32) := by
  classical
  let A := C.similarTransition u
  let E := slowSpace A hA
  let pi : V→ℝ := fun y=>u y^2
  have hpi : pi∈stdSimplex ℝ V := ⟨fun y=>sq_nonneg _,hun⟩
  have hAu : A*ᵥu=u := MomentSmoothingMean.similarTransition_fixes_root C u hu
  have hAnonneg : ∀y z,0≤A y z := by
    intro y z
    exact div_nonneg (mul_nonneg (hu y).le (C.nonneg y z)) (hu z).le
  have hupper : ∀f:V→ℝ,dotProduct f (A*ᵥf)≤1*∑y,f y^2 := by
    intro f
    simpa using ConvexTailMatrix.schur_upper A hA hAnonneg u hu hAu f
  have heig : ∀j,hA.eigenvalues j≤1 := fun j=>(Erdos642.QuadraticPower.eigenvalue_bounds A hA 1 hpos hupper j).2
  obtain ⟨W,hunit,hcover,hcard⟩ := SphereNet.exists_mu_net (E:=E) μ hμ hμ1
  let fast : V→Path V (n-1)→Prop := fun y p=>∃f∈F,ConvexTail.empirical y p∈familySet E W pi f μ
  let slow : V→Path V (n-1)→Prop := fun y p=>∃w∈W,ConvexTail.empirical y p∈badSet (testSet pi w) pi μ
  have hfast : C.eventMass (n-1) fast x≤(F.card:ℝ)*(1/(u x)^2)*Real.exp (-μ^2*(n:ℝ)/4096) := by
    calc
      _ ≤ ∑f∈F,C.eventMass (n-1) (fun y p=>ConvexTail.empirical y p∈familySet E W pi f μ) x :=
        C.eventMass_biUnion_le F _ x
      _ ≤ ∑_f∈F,(1/(u x)^2)*Real.exp (-(μ^2/4096)*(n:ℝ)) := by
        apply Finset.sum_le_sum
        intro f hff
        exact ConvexTail.convex_occupation_tail C u hu hun hA hpos _
          (familySet_compact E W pi f μ) (familySet_convex E W pi f μ) (fun q hq=>hq.1.1)
          (μ^2/4096) (fun q hq=>familySet_energy A hA heig W pi hpi μ hμ hμ1 hunit hcover f (hf f hff) (hmean f hff) q hq) n hn x
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [show -(μ^2/4096)*(n:ℝ) = -μ^2*(n:ℝ)/4096 by ring]
        ring
  have hslow : C.eventMass (n-1) slow x≤(65/μ)^Module.finrank ℝ E*(1/(u x)^2)*Real.exp (-γ*μ^2*(n:ℝ)/32) := by
    calc
      _ ≤ ∑w∈W,C.eventMass (n-1) (fun y p=>ConvexTail.empirical y p∈badSet (testSet pi w) pi μ) x :=
        C.eventMass_biUnion_le W _ x
      _ ≤ ∑_w∈W,(1/(u x)^2)*Real.exp (-(γ*μ^2/32)*(n:ℝ)) := by
        apply Finset.sum_le_sum
        intro w hw
        apply ConvexTail.convex_occupation_tail C u hu hun hA hpos _
          (badSet_compact _ pi μ) (badSet_convex _ pi μ) (fun q hq=>hq.1) (γ*μ^2/32) _ n hn x
        intro q hq
        apply event_energy A hA u (fun y=>(hu y).le) hun hAu γ hγ hgap q hq.1 (testSet pi w) μ hμ.le
        have hh := hq.2
        change μ/4+mass pi (testSet pi w)≤ mean (indicator (testSet pi w)) q at hh
        rw [mean_indicator] at hh
        linarith
      _ ≤ (65/μ)^Module.finrank ℝ E*((1/(u x)^2)*Real.exp (-(γ*μ^2/32)*(n:ℝ))) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by
        rw [show -(γ*μ^2/32)*(n:ℝ) = -γ*μ^2*(n:ℝ)/32 by ring]
        ring
  have hcontain := C.eventMass_mono
    (fun y p=>∃f∈F,Chain.vertexSum f y p≤μ*(n:ℝ)/4)
    (fun y p=>fast y p ∨ slow y p) (by
      intro y p hbad
      obtain ⟨f,hff,hlow⟩ := hbad
      by_cases hg : ConvexTail.empirical y p∈goodSet E W pi μ
      · left
        refine ⟨f,hff,hg,?_⟩
        have he := ConvexTail.empirical_dot_observations n hn y p f
        have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
        change mean f (ConvexTail.empirical y p)≤μ/4
        unfold mean
        nlinarith
      · right
        have hsimplex := ConvexTail.empirical_mem_simplex y p
        have hw : ∃w∈W,μ/4 < mass (ConvexTail.empirical y p) (testSet pi w)-mass pi (testSet pi w) := by
          simpa only [goodSet,Set.mem_setOf_eq,hsimplex,true_and,not_forall,not_le,exists_prop] using hg
        obtain ⟨w,hwW,hw⟩ := hw
        refine ⟨w,hwW,hsimplex,?_⟩
        change μ/4+mass pi (testSet pi w)≤ mean (indicator (testSet pi w)) (ConvexTail.empirical y p)
        rw [mean_indicator]
        linarith) x
  exact hcontain.trans ((C.eventMass_union_le fast slow x).trans (add_le_add hfast hslow))

end Erdos642.Joint20261019.JointFamily
