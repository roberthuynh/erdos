import FirstExcessHeadline
import SurplusPolarityTransfer

namespace Erdos60.Headline
open scoped Classical
universe u
variable {P : Type u} [Fintype P]

/-- The original surplus host itself is near an actual polarity whenever
its cycle count is at most the claimed threshold. -/
theorem nearby_polarity_of_few_cycles (G : SimpleGraph P) (q t : ℕ)
    (heven : Even q) (hq : 10^16 ≤ q) (ht : 1 ≤ t) (hr : 10^8*t ≤ q)
    (hN : Fintype.card P = q^2+q+1) (hE : G.edgeFinset.card = q*(q+1)^2/2+t)
    (hZ : Counting.cycleCount G ≤ t*(q-1)) :
    ∃ (L : Type u) (fL : Fintype L) (mem : Membership P L), letI := fL; letI := mem
      ∃ pp : Configuration.ProjectivePlane P L, letI := pp
        Configuration.ProjectivePlane.order P L = q ∧
        ∃ π : Geometry.Polarity (P := P) (L := L),
          (G.edgeFinset \ π.graph.edgeFinset).card < q-1 := by
  classical
  obtain ⟨H,hHG,hHE,_,hHC⟩ := Transfer.first_excess_subgraph G (q*(q+1)^2/2) t ht hE
  have hqR : (10:ℝ)^16 ≤ q := by exact_mod_cast hq
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hrR : (t:ℝ) ≤ (q:ℝ)/10^8 := by
    have hh : (10:ℝ)^8*t ≤ q := by exact_mod_cast hr
    linarith
  have hdiv : 2 ∣ q*(q+1)^2 := dvd_mul_of_dvd_left (even_iff_two_dvd.mp heven) _
  have hmR : (2:ℝ)*((q*(q+1)^2/2:ℕ):ℝ) = (q:ℝ)*((q:ℝ)+1)^2 := by
    exact_mod_cast Nat.mul_div_cancel' hdiv
  have hHER : (H.edgeFinset.card:ℝ) = (q:ℝ)*((q:ℝ)+1)^2/2+1 := by
    rw [hHE,Nat.cast_add,Nat.cast_one]
    linarith
  have hHZ : (Counting.cycleCount H:ℝ) < (t:ℝ)*q := by
    have hle := hHC.trans hZ
    have hh : Counting.cycleCount H < t*q := by
      have hq1 : 1 ≤ q := by omega
      have hmul := Nat.mul_lt_mul_of_pos_left (show q-1 < q by omega) (by omega : 0<t)
      omega
    exact_mod_cast hh
  obtain ⟨L,fL,mem,pp,ho,π,hπ⟩ := first_excess_structural H q t heven hqR htR hrR hN hHER hHZ
  let : Fintype L := fL
  let : Membership P L := mem
  let : Configuration.ProjectivePlane P L := pp
  have hj : ((H.edgeFinset \ π.graph.edgeFinset).card:ℝ) < 2*t :=
    hπ.2.2.1.trans_lt hπ.2.2.2.1
  have hsmall := π.surplus_edit_radius G H t ht
    (by simpa only [ho] using hqR) (by simpa only [ho] using hrR) hHG
    (by simpa only [ho] using hE) (by simpa only [ho] using hHE) hj
  exact ⟨L,fL,mem,pp,ho,π,by simpa only [ho] using hsmall⟩

/-- Full universal linear-range lower bound for ordinary unlabelled C4s. -/
theorem linear_range_lower (G : SimpleGraph P) (q t : ℕ)
    (heven : Even q) (hq : 10^16 ≤ q) (ht : 1 ≤ t) (hr : 10^8*t ≤ q)
    (hN : Fintype.card P = q^2+q+1) (hE : G.edgeFinset.card = q*(q+1)^2/2+t) :
    t*(q-1) ≤ Counting.cycleCount G := by
  classical
  by_cases hz : Counting.cycleCount G ≤ t*(q-1)
  · obtain ⟨L,fL,mem,pp,ho,π,hs⟩ := nearby_polarity_of_few_cycles G q t heven hq ht hr hN hE hz
    let : Fintype L := fL
    let : Membership P L := mem
    let : Configuration.ProjectivePlane P L := pp
    have hh := π.nearby_lower_bound G t (by simpa only [ho] using heven)
      (by simpa only [ho] using hE) (by simpa only [ho] using hs.le)
    simpa only [ho] using hh
  · omega

#print axioms nearby_polarity_of_few_cycles
#print axioms linear_range_lower
end Erdos60.Headline
