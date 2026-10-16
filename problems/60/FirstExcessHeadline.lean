import ActualCore
import ActualCompletion
import QuantitativeEdit
import GraphTransfer

/-! Full first-excess structural theorem on the original vertex carrier.
Every localization, degree-cap, incidence completion, polarity, missing-edge,
and retained-path supplier is proved in the imported dependency chain.
No plane, row assignment, polarity, or target edit bound is a premise. -/
namespace Erdos60.Headline
open scoped Classical
universe u
variable {P : Type u} [Fintype P]

/-- Convert the real first-excess edge premise to the exact natural M+1
count using the even-order divisibility, without rounding the extremal count. -/
theorem first_excess_edges_nat (G : SimpleGraph P) (q : ℕ) (heven : Even q)
    (hE : (G.edgeFinset.card : ℝ) = (q:ℝ)*((q:ℝ)+1)^2/2+1) :
    G.edgeFinset.card = q*(q+1)^2/2+1 := by
  have hdiv : 2 ∣ q*(q+1)^2 := dvd_mul_of_dvd_left (even_iff_two_dvd.mp heven) _
  have hm := Nat.mul_div_cancel' hdiv
  have hmR : (2:ℝ)*((q*(q+1)^2/2 : ℕ) : ℝ) = (q:ℝ)*((q:ℝ)+1)^2 := by
    exact_mod_cast hm
  have hh : (G.edgeFinset.card : ℝ) = ((q*(q+1)^2/2 : ℕ) : ℝ)+1 := by linarith
  exact_mod_cast hh

/-- Full first-excess structural headline, including the exact 896T edit
coefficient and the actual edge-balance identity. The produced projective
plane and polarity use the ORIGINAL graph vertex carrier P. -/
theorem first_excess_structural (G : SimpleGraph P) (q : ℕ) (T : ℝ)
    (heven : Even q) (hq : (10:ℝ)^16 ≤ q) (hT : 1 ≤ T)
    (hrange : T ≤ (q:ℝ)/10^8) (hN : Fintype.card P = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q:ℝ)*((q:ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ∃ (L : Type u) (fL : Fintype L) (mem : Membership P L), letI := fL; letI := mem
      ∃ pp : Configuration.ProjectivePlane P L, letI := pp
        Configuration.ProjectivePlane.order P L = q ∧
        ∃ π : Geometry.Polarity (P := P) (L := L),
          let j := (G.edgeFinset \ π.graph.edgeFinset).card
          let M := q*(q+1)^2/2
          let δ := M-π.graph.edgeFinset.card
          let d := (π.graph.edgeFinset \ G.edgeFinset).card
          0 < (q:ℝ)-1-896*T ∧
          (j:ℝ)*((q:ℝ)-1-896*T) ≤ Counting.cycleCount G ∧
          (j:ℝ) ≤ (Counting.cycleCount G : ℝ)/((q:ℝ)-1-896*T) ∧
          (Counting.cycleCount G : ℝ)/((q:ℝ)-1-896*T) < 2*T ∧
          π.graph.edgeFinset.card ≤ M ∧ d+1+δ = j := by
  classical
  obtain ⟨C⟩ := Localization.actual_completion_core G q T hq hT hrange heven hN hE hZ
  have hs : 1000*(Finset.univ.filter (fun v : P => C.retained.degree v ≤ q)).card ≤ 1001*q := by
    simpa only [Core.deficientVertices] using C.completionDeficient
  obtain ⟨L,fL,mem,pp,ho,π,hπ⟩ := Completion.actual_count_based_completion C.retained
    C.noFourCycle q heven C.orderLarge hN C.completionMinimum C.cap hs C.completionDeep
  let : Fintype L := fL
  let : Membership P L := mem
  let : Configuration.ProjectivePlane P L := pp
  have heven' : Even (Configuration.ProjectivePlane.order P L) := by simpa only [ho] using heven
  have hedges : π.graph.edgeFinset.card ≤ q*(q+1)^2/2 := by
    simpa only [ho] using π.edge_count_upper heven'
  have hbalance : (π.graph.edgeFinset \ G.edgeFinset).card+1+
      (q*(q+1)^2/2-π.graph.edgeFinset.card) = (G.edgeFinset \ π.graph.edgeFinset).card := by
    apply Transfer.graph_edge_balance G π.graph (q*(q+1)^2/2) 1
      (q*(q+1)^2/2-π.graph.edgeFinset.card)
    · exact first_excess_edges_nat G q heven hE
    · omega
  have hquant := C.quantitative_polarity_edit_bound π ho hπ hq hT hrange heven hZ
  exact ⟨L,fL,mem,pp,ho,π,hquant.1,hquant.2.1,hquant.2.2.1,hquant.2.2.2,hedges,hbalance⟩

#print axioms first_excess_edges_nat
#print axioms first_excess_structural
end Erdos60.Headline
