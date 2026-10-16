import OutsideMissing
import ActualCore

/-! Exact quantitative edit bound from actual retained-path and missing-edge
accounting. Actual containing polarity/core are explicit inputs; this module
does not supply the remaining projective embedding producer. -/
namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [DecidableEq P]
  [Configuration.ProjectivePlane P L] [Finite L]

/-- The exact coefficient in the structural headline, with no assumed path
or outside-missing count. The actual core/polarity inputs discharge both. -/
theorem Polarity.first_excess_quantitative_edit_bound
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P) (T : ℝ)
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hcontain : ∀ v ∉ S, ∀ w, G.Adj v w → π.graph.Adj v w)
    (hmin : ∀ v ∉ S, Configuration.ProjectivePlane.order P L ≤ G.degree v)
    (hdef : ((Finset.univ.filter (fun v : P => G.degree v ≤
      Configuration.ProjectivePlane.order P L)).card : ℝ) ≤
        (Configuration.ProjectivePlane.order P L : ℝ)-1+20*T)
    (hcore : (S.card : ℝ) ≤ 292*T)
    (hq : (10^16 : ℝ) ≤ (Configuration.ProjectivePlane.order P L : ℝ))
    (hT : 1 ≤ T) (hrange : T ≤ (Configuration.ProjectivePlane.order P L : ℝ)/10^8)
    (hZ : (Counting.cycleCount G : ℝ) < T*(Configuration.ProjectivePlane.order P L : ℝ)) :
    0 < (Configuration.ProjectivePlane.order P L : ℝ)-1-896*T ∧
    ((G.edgeFinset \ π.graph.edgeFinset).card : ℝ)*
      ((Configuration.ProjectivePlane.order P L : ℝ)-1-896*T) ≤ Counting.cycleCount G ∧
    ((G.edgeFinset \ π.graph.edgeFinset).card : ℝ) ≤
      (Counting.cycleCount G : ℝ)/((Configuration.ProjectivePlane.order P L : ℝ)-1-896*T) ∧
    (Counting.cycleCount G : ℝ)/((Configuration.ProjectivePlane.order P L : ℝ)-1-896*T) < 2*T := by
  classical
  let q := Configuration.ProjectivePlane.order P L
  let j := (G.edgeFinset \ π.graph.edgeFinset).card
  let d := (outsideMissing G π.graph S).card
  have hd : (d : ℝ) ≤ (S.card : ℝ)+20*T :=
    π.outside_missing_real_bound G S T heven hcontain hmin hdef
  have hhalf : (q : ℝ)/2 < (q : ℝ)-1-896*T := by
    dsimp [q] at *
    linarith
  have hqpos : (0 : ℝ) < q := by dsimp [q]; linarith
  have hpos : 0 < (q : ℝ)-1-896*T := by linarith
  have hcoef : (q : ℝ)-1-896*T ≤ (q : ℝ)-1-2*(S.card : ℝ)-(d : ℝ) := by linarith
  have hsmall : 1+2*S.card+d ≤ q := by
    have hh : (1:ℝ)+2*(S.card : ℝ)+(d : ℝ) ≤ q := by linarith
    exact_mod_cast hh
  have hk : q-1-2*S.card-d = q-(1+2*S.card+d) := by omega
  have hkR : ((q-1-2*S.card-d : ℕ) : ℝ) = (q : ℝ)-1-2*(S.card : ℝ)-(d : ℝ) := by
    rw [hk,Nat.cast_sub hsmall]
    push_cast
    ring
  have hc := π.localized_cycle_lower G S
  have hcR : (j : ℝ)*((q-1-2*S.card-d : ℕ) : ℝ) ≤ (Counting.cycleCount G : ℝ) := by
    exact_mod_cast hc
  rw [hkR] at hcR
  have hj0 : (0:ℝ) ≤ j := by positivity
  have hbound : (j : ℝ)*((q : ℝ)-1-896*T) ≤ Counting.cycleCount G :=
    (mul_le_mul_of_nonneg_left hcoef hj0).trans hcR
  refine ⟨hpos,hbound,(le_div_iff₀ hpos).mpr hbound,?_⟩
  apply (div_lt_iff₀ hpos).mpr
  have hmul := mul_lt_mul_of_pos_left hhalf (by linarith : 0 < 2*T)
  change (Counting.cycleCount G : ℝ) < T*(q : ℝ) at hZ
  nlinarith

#print axioms Polarity.first_excess_quantitative_edit_bound
end Erdos60.Geometry

namespace Erdos60.Localization
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]
  [Configuration.ProjectivePlane P L]

/-- The same exact coefficient for one actual original-host core and an
actual polarity containing its retained graph. No core statistics are assumed
separately from the verified ActualCoreData fields. -/
theorem ActualCoreData.quantitative_polarity_edit_bound
    {G : SimpleGraph P} {q : ℕ} {T : ℝ} (C : ActualCoreData G q T)
    (π : Geometry.Polarity (P := P) (L := L))
    (ho : Configuration.ProjectivePlane.order P L = q) (hcontain : C.retained ≤ π.graph)
    (hq : (10:ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q:ℝ)/10^8)
    (heven : Even q) (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    0 < (q:ℝ)-1-896*T ∧
    ((G.edgeFinset \ π.graph.edgeFinset).card : ℝ)*((q:ℝ)-1-896*T) ≤ Counting.cycleCount G ∧
    ((G.edgeFinset \ π.graph.edgeFinset).card : ℝ) ≤
      (Counting.cycleCount G : ℝ)/((q:ℝ)-1-896*T) ∧
    (Counting.cycleCount G : ℝ)/((q:ℝ)-1-896*T) < 2*T := by
  classical
  have hc : ∀ v ∉ C.core, ∀ w, G.Adj v w → π.graph.Adj v w := by
    intro v hv w hvw
    exact hcontain ((C.outsideAdj v w hv).mpr hvw)
  have hm : ∀ v ∉ C.core, q ≤ G.degree v := by
    intro v hv
    obtain ⟨hd,hor⟩ := C.outsideDegree v hv
    omega
  have hd : ((Finset.univ.filter (fun v : P => G.degree v ≤ q)).card : ℝ) ≤
      (q:ℝ)-1+20*T := by simpa only [Core.deficientVertices] using C.originalDeficient
  have hh := π.first_excess_quantitative_edit_bound G C.core T
    (by simpa only [ho] using heven) hc (by simpa only [ho] using hm)
    (by simpa only [ho] using hd) C.size (by simpa only [ho] using hq) hT
    (by simpa only [ho] using hr) (by simpa only [ho] using hZ)
  simpa only [ho] using hh

#print axioms ActualCoreData.quantitative_polarity_edit_bound
end Erdos60.Localization
