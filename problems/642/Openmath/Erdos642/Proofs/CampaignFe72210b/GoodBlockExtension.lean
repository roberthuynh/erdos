import Openmath.Erdos642.Proofs.CampaignFe72210b.GoodStartMixing
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathAvoidance

namespace Erdos642.FiniteMarkov.Chain
open PathCoordinates PathAvoidance
variable {V : Type*} [Fintype V] [DecidableEq V] (C : Chain V)

/-- Actual one-block success from good older exposure and local failure bounds. -/
theorem good_block_extension (k q r : ℕ) (β H J M N R : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (hcollision : ∀ v, C.eventMass k (fun z s => ¬ actualSA z s) v ≤ J)
    (hHJ : H+J ≤ β)
    (hcol : ∀ t ∈ Finset.Icc 1 k, ∀ a, ∑ v, (C.transition^t) v a ≤ R)
    (hmix : ∀ x y, (C.transition^k) x y ≤ M/N)
    (horder : M*R*(k:ℝ)*((q*k+1:ℕ):ℝ) ≤ β^2*N)
    (x : V) (p : Path V (r*k)) (hp : actualSA x p) (O : Finset V)
    (hO : O ⊆ visited x p) (hsmall : ((visited x p) \ O).card ≤ k)
    (hgood : C.Good k β H O (C.endpoint x p))
    (hsize : (visited x p).card ≤ q*k+1) :
    1-3*β ≤ C.eventMass k
      (fun z s => actualSA x (C.append p s) ∧
        C.Good k β H (visited x p) (C.endpoint z s)) (C.endpoint x p) := by
  classical
  let E := visited x p
  let u := C.endpoint x p
  have havoid := hgood (E \ O) hsmall
  rw [Finset.union_sdiff_of_subset hO, C.eventMass_compl] at havoid
  have hhit : C.eventMass k (actualHit E) u ≤ β+H := by linarith
  have hcoll : C.eventMass k (fun _ s => ¬ actualSA u s) u ≤ J := by
    simpa only [eventMass] using hcollision u
  have hend : C.eventMass k (fun z s => ¬ C.Good k β H E (C.endpoint z s)) u ≤ β :=
    C.endpoint_bad_mass_le_beta k q β H M N R hβ hN hM hR hlocal hcol hmix horder E hsize u
  let B1 : V → Path V k → Prop := actualHit E
  let B2 : V → Path V k → Prop := fun _ s => ¬ actualSA u s
  let B3 : V → Path V k → Prop := fun z s => ¬ C.Good k β H E (C.endpoint z s)
  let B : V → Path V k → Prop := fun z s => (B1 z s ∨ B2 z s) ∨ B3 z s
  have hb : C.eventMass k B u ≤ 3*β := by
    have h12 := C.eventMass_union_le B1 B2 u
    have h123 := C.eventMass_union_le (fun z s => B1 z s ∨ B2 z s) B3 u
    change C.eventMass k (fun z s => (B1 z s ∨ B2 z s) ∨ B3 z s) u ≤ 3*β
    change C.eventMass k B1 u ≤ β+H at hhit
    change C.eventMass k B2 u ≤ J at hcoll
    change C.eventMass k B3 u ≤ β at hend
    linarith
  have hsuccess : 1-3*β ≤ C.eventMass k (fun z s => ¬ B z s) u := by
    rw [C.eventMass_compl]
    linarith
  apply hsuccess.trans
  apply C.eventMass_mono
  intro z s hB
  have h1 : ¬ actualHit E u s := by
    intro hh
    exact hB (Or.inl (Or.inl hh))
  have h2 : actualSA u s := by
    by_contra hh
    exact hB (Or.inl (Or.inr hh))
  have h3 : C.Good k β H E (C.endpoint z s) := by
    by_contra hh
    exact hB (Or.inr hh)
  refine ⟨?_, h3⟩
  exact (C.actualSA_append_iff x p s).mpr ⟨hp, h2, h1⟩
end Erdos642.FiniteMarkov.Chain
