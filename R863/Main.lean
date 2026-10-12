import R863.Original
import R863.ActualSelection

/-! R863: complete R851 error-floor positive-terminal selector.
One internally selected omission pays every original cut and determines
the exact support of the returned original regular subgraph. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.R863
open QB4 B5 L34 H3Unequal
universe u

open Classical in
/-- The full-C endpoint on the original finite host. -/
theorem error_floor_positive_surplus (h q j e : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q j e G A B) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
      (∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0) ∧
      ∃ H : G.Subgraph, H.verts = (↑(A ∪ (B \ O)) : Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  have d := host.to_data
  obtain ⟨O, hOB, hOj, hcuts⟩ := ActualSelection.common_omission d
  have hfactor := factor_of_common_omission q j host.card hOB hOj hcuts
  have hq := host.parameters.q_pos
  have hA : A.Nonempty := card_pos.mp (by have hh := d.shores_large.1; omega)
  obtain ⟨H, hverts, hnonempty, hregular⟩ :=
    factor_exact_subgraph hq hA (host.disjoint.mono_right sdiff_subset) hfactor
  exact ⟨O, hOB, hOj, hcuts, H, hverts, hnonempty, hregular⟩

open Classical in
/-- Literal original hypotheses, including the original F0+1 floor rather than
an offset window or a supplied selector/factor. -/
theorem error_floor_positive_selector (h q j e : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V)
    (hh : 6 ≤ h) (he : e ≤ 4*h^2-10*h+4)
    (hq : 2^20*(h+e+1)^2 ≤ q) (hj : 1 ≤ j) (hju : j ≤ h-1)
    (hdis : Disjoint A B) (hcover : A∪B=univ)
    (hbip : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcard : #B=#A+j) (horder : 2*q≤Fintype.card V)
    (hmin : ∀ v : V, q≤G.degree v)
    (hcap : ∀ v : V, G.degree v≤2*q-2)
    (hhigh : ∀ v∈A, q+2*h-4≤G.degree v)
    (htotal : ((q : ℤ)-1)*Fintype.card V-(G.edgeSet.ncard : ℤ)=
      (h : ℤ)*q-16*h^2+e)
    (hproper : ∀ U : Finset V, h≤#U → #U<Fintype.card V →
      (h : ℤ)*q-16*h^2+1≤((q : ℤ)-1)*#U-
        ((G.induce (U : Set V)).edgeSet.ncard : ℤ)) :
    ∃ O : Finset V, O⊆B ∧ #O=j ∧
      (∀ T⊆B, O⊆T → thetaJ q j G A B T≤0) ∧
      ∃ H : G.Subgraph, H.verts=(↑(A∪(B\O)) : Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  let p : Parameters h q j e := ⟨hh,he,hq,hj,hju⟩
  have host : Host h q j e G A B := by
    refine ⟨p,hdis,hcover,hbip,hcard,horder,hmin,hcap,hhigh,?_,?_⟩
    · have hc:=p.constant_cast
      have ha:=p.offset_cast
      have hqm : (q-1 : ℕ)+1=q := by have hp:=p.q_pos;omega
      have heq : (G.edgeSet.ncard : ℤ)+(constant h q e : ℤ)=
          ((q-1 : ℕ) : ℤ)*Fintype.card V := by
        have hcast : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
        rw [hcast]
        nlinarith only [htotal,hc,ha]
      exact_mod_cast heq
    · intro U hu hup
      have hc:=p.constant_cast
      have ha:=p.offset_cast
      have hf:=hproper U hu hup
      nlinarith only [hc,ha,hf]
  exact error_floor_positive_surplus h q j e G A B host

end Erdos585.R863
