import PlaneRealization

namespace Erdos60.Embedding.IndexedDesign
open scoped Classical
universe u
variable {q : ℕ} {I X : Type u} [Fintype I] [Fintype X]

/-- Actual plane on the original indexed-line carrier, with an injective old
point-to-line assignment and exact incidence. This is a conclusion predicate. -/
def HasPlaneEmbedding (D : IndexedDesign q X I) : Prop :=
  ∃ (Y : Type u) (fY : Fintype Y) (M : Membership I Y), letI := fY; letI := M
    ∃ pp : Configuration.ProjectivePlane I Y, letI := pp
      Configuration.ProjectivePlane.order I Y = q ∧
      ∃ f : X ↪ Y, ∀ x i, i ∈ f x ↔ D.inc x i

theorem dense_hasPlaneEmbedding (D : IndexedDesign q X I) (hq : 2 ≤ q)
    (hI : Fintype.card I = q^2+q+1) (hlo : q^2 ≤ Fintype.card X) :
    D.HasPlaneEmbedding := by
  classical
  obtain ⟨Y,fY,E,f,hY,hinc,hplane⟩ := D.dense_plane_extension hq hI hlo
  let : Fintype Y := fY
  let : Membership Y I := E.membership
  obtain ⟨pp,ho⟩ := hplane
  let : Configuration.ProjectivePlane Y I := pp
  let R : I ≃ I := Equiv.refl _
  refine ⟨Y,fY,PlaneRealization.transportedMembership R,
    PlaneRealization.transportedPlane R,?_,f,?_⟩
  · exact (PlaneRealization.transported_order R).trans ho
  · intro x i
    exact hinc x i

theorem pullback_planeEmbedding {Z : Type u} [Fintype Z]
    (D : IndexedDesign q X I) (E : IndexedDesign q Z I) (g : X ↪ Z)
    (hinc : ∀ x i, E.inc (g x) i ↔ D.inc x i) (hE : E.HasPlaneEmbedding) :
    D.HasPlaneEmbedding := by
  obtain ⟨Y,fY,M,pp,ho,f,hf⟩ := hE
  let : Fintype Y := fY
  let : Membership I Y := M
  let : Configuration.ProjectivePlane I Y := pp
  let fg : X ↪ Y := ⟨fun x => f (g x),fun _ _ h => g.injective (f.injective h)⟩
  refine ⟨Y,fY,M,pp,ho,fg,?_⟩
  intro x i
  exact (hf (g x) i).trans (hinc x i)

/-- The actual outer induction. The named remaining no-degree-q source
branch is a continuation parameter here, never an axiom or a final endpoint. -/
theorem degree_q_extension_induction
    (hq : 10^8 ≤ q) (hI : Fintype.card I = q^2+q+1)
    (hbranch : ∀ (Z : Type u) [Fintype Z] (E : IndexedDesign q Z I) (s : ℕ),
      Fintype.card Z+s=q^2+q+1 → 500*s ≤ 501*q → q+2 ≤ s →
      (∀ i, E.lineDegree i ≠ q) → E.HasPlaneEmbedding) (s : ℕ) :
    ∀ (X : Type u) [Fintype X] (D : IndexedDesign q X I),
      Fintype.card X+s=q^2+q+1 → 500*s ≤ 501*q → D.HasPlaneEmbedding := by
  have hq2 : 2 ≤ q := by omega
  induction s with
  | zero =>
    intro X _ D hs hd
    apply D.dense_hasPlaneEmbedding hq2 hI
    omega
  | succ s ih =>
    intro X _ D hs hd
    by_cases hlo : q^2 ≤ Fintype.card X
    · exact D.dense_hasPlaneEmbedding hq2 hI hlo
    · by_cases hex : ∃ i, D.lineDegree i = q
      · obtain ⟨i,hi⟩ := hex
        let E := D.extendAtDegreeQ hI i hi
        have hs' : Fintype.card (Option X)+s=q^2+q+1 := by simp; omega
        have hd' : 500*s ≤ 501*q := by omega
        have hE := ih (Option X) E hs' hd'
        exact D.pullback_planeEmbedding E ⟨Option.some,Option.some_injective X⟩
          (D.extendAtDegreeQ_old hI i hi) hE
      · exact hbranch X D (s+1) hs hd (by omega) (by simpa only [not_exists] using hex)

/-- Actual near-dense indexed-design embedding. All source suppliers are
proved: greedy extension handles degree-q lines; the source6.10 branch handles
the no-degree-q case. No abstract embedding supplier remains a hypothesis. -/
theorem near_dense_hasPlaneEmbedding (D : IndexedDesign q X I) (s : ℕ)
    (hq : 10^8 ≤ q) (hI : Fintype.card I = q^2+q+1)
    (hX : Fintype.card X+s=q^2+q+1) (hs : 500*s ≤ 501*q) :
    D.HasPlaneEmbedding := by
  classical
  apply degree_q_extension_induction hq hI ?_ s X D hX hs
  intro Z _ E t hZ ht hbranch hnone
  obtain ⟨M,pp,ho,hinc⟩ := PlaneRealization.no_degree_q_plane E t hq hI hZ ht hbranch hnone
  exact ⟨E.RealizedPoint (Parameters.cutoff q) (Parameters.allowance q t),inferInstance,
    M,pp,ho,PlaneRealization.oldPointEmbedding E _ _,hinc⟩

/-- Expanded actual plane endpoint on the original indexed line carrier.
Its old point-to-line map is injective and preserves incidence in both
directions, including original empty and singleton line labels. -/
theorem near_dense_plane (D : IndexedDesign q X I) (s : ℕ)
    (hq : 10^8 ≤ q) (hI : Fintype.card I = q^2+q+1)
    (hX : Fintype.card X+s=q^2+q+1) (hs : 500*s ≤ 501*q) :
    ∃ (Y : Type u) (fY : Fintype Y) (M : Membership I Y), letI := fY; letI := M
      ∃ pp : Configuration.ProjectivePlane I Y, letI := pp
        Configuration.ProjectivePlane.order I Y = q ∧
        ∃ f : X ↪ Y, ∀ x i, i ∈ f x ↔ D.inc x i :=
  D.near_dense_hasPlaneEmbedding s hq hI hX hs

#print axioms dense_hasPlaneEmbedding
#print axioms pullback_planeEmbedding
#print axioms degree_q_extension_induction
#print axioms near_dense_hasPlaneEmbedding
#print axioms near_dense_plane
end Erdos60.Embedding.IndexedDesign
