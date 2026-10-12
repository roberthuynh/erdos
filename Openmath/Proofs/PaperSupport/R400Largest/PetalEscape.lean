import Openmath.Proofs.PaperSupport.R400Largest.Geometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHLargestH3R400
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace PetalEscape

/-- One shared ORIGINAL unit-edge/scar pool, with actual columns AND strict rows disjoint. -/
lemma pool {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (F : Finset (Finset V)) (hF : ∀ P ∈ F, P ⊆ B \ K)
    (hPdis : (F : Set (Finset V)).PairwiseDisjoint id)
    (hJdis : (F : Set (Finset V)).PairwiseDisjoint (residualRows q G A B K C)) :
    (∑ P ∈ F, petalWeight q G A B K C P) ≤ (ec G C (B \ K) : ℤ) +
      ec G (A \ C) K + deficiency (2 * (q : ℤ) - 2) G B (A \ C) := by
  let JP := residualRows q G A B K C
  have hsubP : F.biUnion id ⊆ B \ K := by
    intro v hv
    obtain ⟨P, hPF, hvP⟩ := mem_biUnion.mp hv
    exact hF P hPF hvP
  have hsubJ : F.biUnion JP ⊆ A \ C := by
    intro a ha
    obtain ⟨P, _, haJ⟩ := mem_biUnion.mp ha
    exact (mem_filter.mp haJ).1
  have hsP : (∑ P ∈ F, (ec G C P : ℤ)) = ec G C (F.biUnion id) := by
    simp_rw [ec_comm (G := G) C, ec, Nat.cast_sum]
    exact (sum_biUnion hPdis).symm
  have hsJ : (∑ P ∈ F, ((ec G (JP P) K : ℤ) +
      deficiency (2 * (q : ℤ) - 2) G B (JP P))) =
      ∑ a ∈ F.biUnion JP, ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a)) := by
    simp_rw [ec, Nat.cast_sum, deficiency, ← sum_add_distrib]
    exact (sum_biUnion hJdis).symm
  have hlP : (ec G C (F.biUnion id) : ℤ) ≤ ec G C (B \ K) := by
    exact_mod_cast ec_mono_right (G := G) C hsubP
  have hlJ : (∑ a ∈ F.biUnion JP, ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a))) ≤
      ec G (A \ C) K + deficiency (2 * (q : ℤ) - 2) G B (A \ C) := by
    have hh := sum_le_sum_of_subset_of_nonneg
      (f := fun a => ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a))) hsubJ (fun a ha _ => by
        have hc := d.capA_int (mem_sdiff.mp ha).1
        have hd : (0 : ℤ) ≤ dg G K a := Nat.cast_nonneg _
        omega)
    calc
      _ ≤ ∑ a ∈ A \ C, ((dg G K a : ℤ) + (2 * (q : ℤ) - 2 - dg G B a)) := hh
      _ = _ := by rw [sum_add_distrib]; simp only [ec, Nat.cast_sum, deficiency]
  unfold petalWeight
  change (∑ P ∈ F, ((ec G C P : ℤ) + (ec G (JP P) K : ℤ) +
    deficiency (2 * (q : ℤ) - 2) G B (JP P))) ≤ _
  simp_rw [add_assoc]
  rw [sum_add_distrib, hsP, hsJ]
  linarith

lemma weight_nonneg {h q a₀ j : ℕ} {A B K C P : Finset V} (d : Data h q a₀ j G A B) :
    0 ≤ petalWeight q G A B K C P := by
  have hs := d.scar_nonneg (show residualRows q G A B K C P ⊆ A from
    (filter_subset _ _).trans sdiff_subset)
  dsimp only [petalWeight]
  omega

/-- Exact original Gamma identity for cost one, including every strict residual row. -/
lemma gamma_identity {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C) (hP : P ⊆ B \ K)
    (hc : extensionCost q j G A B K P = 1) :
    petalWeight q G A B K C P =
      (q : ℤ) * #P + ((q : ℤ) - 2) * #(residualRows q G A B K C P) -
        ec G (residualRows q G A B K C P) P - 1 := by
  have hi := petal_resource_identity (j := j) opt hP
  dsimp only at hi
  rw [hc, coreDefect] at hi
  dsimp only [petalWeight]
  nlinarith

/-- Below-h supports are charged by incidence, never by an ineligible floor. -/
lemma small_weight {h q a₀ j : ℕ} {A B K C P : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hP : MaxPetal q j G A B K 1 P)
    (hsmall : #P + #(residualRows q G A B K C P) < h) :
    ((q : ℤ) - 1) * #P ≤ petalWeight q G A B K C P := by
  let J := residualRows q G A B K C P
  have hi := gamma_identity opt hP.1 hP.2.2.1
  change petalWeight q G A B K C P = (q : ℤ) * #P + ((q : ℤ) - 2) * #J - ec G J P - 1 at hi
  have hp : 1 ≤ #P := card_pos.mpr hP.2.1
  have hq := d.parameters.q_ge_height
  have he : (ec G J P : ℤ) ≤ (#J : ℤ) * #P := by
    rw [ec, Nat.cast_sum]
    calc
      _ ≤ ∑ _a ∈ J, (#P : ℤ) := by
        apply sum_le_sum
        intro a _
        exact_mod_cast dg_le_card (G := G) P a
      _ = _ := by simp [mul_comm]
  have hprod : 0 ≤ (#J : ℤ) * ((q : ℤ) - 2 - #P) :=
    mul_nonneg (Nat.cast_nonneg _) (by omega)
  nlinarith

/-- The cost-one expansion is positive and its optimizing imbalance is bounded. -/
lemma expanded_difference {h q a₀ j : ℕ} {A B K C P : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hlarge : q - 1 ≤ #K)
    (hp : 2 ≤ thetaJ q j G A B K) (hP : MaxPetal q j G A B K 1 P) :
    ((#C : ℤ) - #K) - h + 1 ≤ (#P : ℤ) - #(residualRows q G A B K C P) := by
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A \ C := filter_subset _ _
  have hCJ : Disjoint C J := disjoint_left.mpr fun _ hc hj => (mem_sdiff.mp (hJ hj)).2 hc
  have hKP : Disjoint K P := disjoint_left.mpr fun _ hk hpa => (mem_sdiff.mp (hP.1 hpa)).2 hk
  have hext : 0 < thetaJ q j G A B (K ∪ P) := by
    have hc := hP.2.2.1
    unfold extensionCost at hc
    omega
  have hs := d.positive_shape (expanded_optimizer opt hP.1)
    (union_subset hK (hP.1.trans sdiff_subset))
    (hlarge.trans (card_le_card subset_union_left)) hext
  dsimp only at hs
  have hcJ := card_union_of_disjoint hCJ
  have hcP := card_union_of_disjoint hKP
  have hu : ((#(C ∪ J) : ℤ) - #(K ∪ P)) ≤ (h : ℤ) - 1 := hs.2.2.2.1
  zify at hcJ hcP
  change _ ≤ (#P : ℤ) - #J
  omega

/-- NONSTRICT eligible charge, one unit weaker than the strict-floor ancestor. -/
lemma large_weight {h q a₀ j : ℕ} {A B K C P : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hlarge : q - 1 ≤ #K)
    (hp : 2 ≤ thetaJ q j G A B K) (hP : MaxPetal q j G A B K 1 P)
    (hel : h ≤ #P + #(residualRows q G A B K C P)) :
    (h : ℤ) * q - a₀ + ((#C : ℤ) - #K) - h ≤
      petalWeight q G A B K C P := by
  let J := residualRows q G A B K C P
  change h ≤ #P + #J at hel
  have hJ : J ⊆ A := (filter_subset _ _).trans sdiff_subset
  have hpc := card_le_card hP.1
  have hkc := card_sdiff_add_card_eq_card hK
  have hka : 0 < #K := by have hq := d.parameters.q_ge_height; omega
  have hjc := card_le_card hJ
  have hs := d.sparse J hJ P (hP.1.trans sdiff_subset) (by omega) (by omega)
  have ht := twice_coreDefect (G := G) q J P
  have hi := petal_resource_identity (j := j) opt hP.1
  dsimp only at hi
  change coreDefect q G J P = _ at hi
  rw [hP.2.2.1] at hi
  change coreDefect q G J P = (ec G C P : ℤ) + ec G J K +
    deficiency (2 * (q : ℤ) - 2) G B J + 1 - ((#P : ℤ) - #J) at hi
  have hd := expanded_difference d opt hK hlarge hp hP
  change ((#C : ℤ) - #K) - h + 1 ≤ (#P : ℤ) - #J at hd
  dsimp only [petalWeight]
  change _ ≤ (ec G C P : ℤ) + ec G J K + deficiency (2 * (q : ℤ) - 2) G B J
  omega

lemma pool_bound {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) :
    (ec G C (B \ K) : ℤ) + ec G (A \ C) K + deficiency (2 * (q : ℤ) - 2) G B (A \ C) ≤
      ((h : ℤ) + j) * q - a₀ + j + 2 * ((#C : ℤ) - #K) - 2 * thetaJ q j G A B K := by
  have he := opt.outward_edges (j := j) hK
  have hc := opt.cross_scar_identity (j := j)
  have hs := d.scar_split opt.subset
  have hb : 0 ≤ deficiency (2 * (q : ℤ) - 2) G A K :=
    deficiency_nonneg _ fun _b hb => d.capB_int (hK hb)
  nlinarith

lemma numeric {h q a₀ j : ℕ} (p : Parameters h q a₀ j) {k t : ℤ}
    (hk : k ≤ (h : ℤ) - 1) (ht : 2 ≤ t) :
    let H := ((h : ℤ) + j) * q - a₀ + j + 2*k - 2*t
    let L := (h : ℤ)*q - a₀ + k - h
    0 < (q : ℤ) - 1 ∧ H < 2*L ∧
      H < ((q : ℤ)-1)*(h+j) ∧ H-L < ((q : ℤ)-1)*(j+1) ∧
      h+j+3*h < q+1 ∧ j+3*h < q+1 := by
  have hh := p.height_int
  have hj := p.j_bounds
  have hn := p.numeric
  have hq := p.q_pos
  have hb : 0 ≤ ((h : ℤ) - j - 1) * q :=
    mul_nonneg (by omega) (Nat.cast_nonneg _)
  dsimp only
  refine ⟨by omega, ?_, ?_, ?_, by omega, by omega⟩ <;> nlinarith

end PetalEscape

/-- Complete actual cost-one escape under the NONSTRICT floor, no ban or supplied family. -/
theorem petal_escape : PetalEscapeClaim (G := G) := by
  intro h q a₀ j A B K d hK hlarge hp hstrict
  let C := weakCore q G A B K
  let R := B \ K
  let F := R.powerset.filter fun P => MaxPetal q j G A B K 1 P
  let w := petalWeight q G A B K C
  let large := fun P : Finset V => h ≤ #P + #(residualRows q G A B K C P)
  let k : ℤ := (#C : ℤ) - #K
  let t : ℤ := thetaJ q j G A B K
  let H : ℤ := ((h : ℤ) + j) * q - a₀ + j + 2*k - 2*t
  let L : ℤ := (h : ℤ)*q - a₀ + k - h
  let r : ℤ := (q : ℤ) - 1
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hmin : ∀ P ⊆ B \ K, P.Nonempty → 1 ≤ extensionCost q j G A B K P :=
    strict_extension_cost_min hK hstrict
  have hthreshold : ∀ v ∈ A \ C, (1 : ℤ) ≤ -row q G B K v := by
    intro v hv
    have hs := weak_outside_strict (G := G) q A B K hv
    omega
  have hf : ∀ P ∈ F, MaxPetal q j G A B K 1 P := fun _ hP => (mem_filter.mp hP).2
  have hFsub : ∀ P ∈ F, P ⊆ B \ K := fun P hP => (hf P hP).1
  have hdisP : (F : Set (Finset V)).PairwiseDisjoint id := by
    intro P hPF Q hQF hPQ
    exact (hf P hPF).disjoint hmin (hf Q hQF) hPQ
  have hdisJ : (F : Set (Finset V)).PairwiseDisjoint (residualRows q G A B K C) := by
    intro P hPF Q hQF hPQ
    exact (hf P hPF).rows_disjoint hmin hthreshold (hf Q hQF) hPQ
  have hsum : (∑ P ∈ F, w P) ≤ H :=
    (PetalEscape.pool d F hFsub hdisP hdisJ).trans (PetalEscape.pool_bound d opt hK)
  have hweight : ∀ P ∈ F, 0 ≤ w P := fun _ _ => PetalEscape.weight_nonneg d
  have hsmall : ∀ P ∈ F, ¬large P → r * #P ≤ w P := by
    intro P hPF hn
    exact PetalEscape.small_weight d opt (hf P hPF) (Nat.lt_of_not_ge hn)
  have hbig : ∀ P ∈ F, large P → L ≤ w P := by
    intro P hPF hel
    exact PetalEscape.large_weight d opt hK hlarge hp (hf P hPF) hel
  have hshape := d.positive_shape opt hK hlarge (by omega)
  have hk : k ≤ (h : ℤ) - 1 := hshape.2.2.2.1
  have hn := PetalEscape.numeric d.parameters (k := k) (t := t) hk hp
  change 0 < r ∧ H < 2*L ∧ H < r*(h+j) ∧ H-L < r*(j+1) ∧
    h+j+3*h < q+1 ∧ j+3*h < q+1 at hn
  have hunique := AllHTopTwo.PetalEscape.one_large F w large L H hweight hbig hsum hn.2.1
  have hR : q+1 ≤ #R := d.positive_complement hK (by omega)
  have escape : ∃ z ∈ R, ∀ P ∈ F, z ∉ P := by
    by_cases hex : ∃ P ∈ F, large P
    · obtain ⟨P, hPF, hPl⟩ := hex
      have hothers : ∀ Q ∈ F.erase P, ¬large Q := by
        intro Q hQ hQl
        obtain ⟨hQP, hQF⟩ := mem_erase.mp hQ
        exact hQP (hunique Q hQF hQl P hPF hPl)
      have hsrest : (∑ Q ∈ F.erase P, w Q) ≤ H-L := by
        have hs := sum_erase_add F w hPF
        have hPweight := hbig P hPF hPl
        linarith
      have hrest : #((F.erase P).biUnion id) < j+1 :=
        AllHTopTwo.PetalEscape.columns_lt (F.erase P) w r (H-L) (j+1) hn.1
          (fun Q hQ => hsmall Q (mem_erase.mp hQ).2 (hothers Q hQ)) hsrest hn.2.2.2.1
      have hpos : 0 < thetaJ q j G A B (K ∪ P) := by
        have hc := (hf P hPF).2.2.1
        unfold extensionCost at hc
        omega
      have hcomp := d.positive_complement (union_subset hK ((hf P hPF).1.trans sdiff_subset)) hpos
      have heq : B \ (K ∪ P) = R \ P := by
        ext v
        simp only [R, mem_sdiff, mem_union]
        tauto
      rw [heq] at hcomp
      have hcard : #((F.erase P).biUnion id) < #(R \ P) := by omega
      obtain ⟨z, hz, hzE⟩ := AllHTopTwo.PetalEscape.exists_outside (R \ P) ((F.erase P).biUnion id) hcard
      refine ⟨z, (mem_sdiff.mp hz).1, ?_⟩
      intro Q hQ hzQ
      by_cases he : Q = P
      · exact (mem_sdiff.mp hz).2 (he ▸ hzQ)
      · have hQE : Q ∈ F.erase P := mem_erase.mpr ⟨he, hQ⟩
        exact hzE (mem_biUnion.mpr ⟨Q, hQE, hzQ⟩)
    · have hnone : ∀ P ∈ F, ¬large P := by simpa only [not_exists, not_and] using hex
      have hcardF : #(F.biUnion id) < h+j :=
        AllHTopTwo.PetalEscape.columns_lt F w r H (h+j) hn.1
          (fun P hPF => hsmall P hPF (hnone P hPF)) hsum hn.2.2.1
      have hcard : #(F.biUnion id) < #R := by omega
      obtain ⟨z, hzR, hzE⟩ := AllHTopTwo.PetalEscape.exists_outside R (F.biUnion id) hcard
      refine ⟨z, hzR, ?_⟩
      intro P hPF hzP
      exact hzE (mem_biUnion.mpr ⟨P, hPF, hzP⟩)
  obtain ⟨z, hzR, hzF⟩ := escape
  refine ⟨z, hzR, ?_⟩
  intro P hP hzP
  have hne : P.Nonempty := ⟨z, hzP⟩
  have hc := hmin P hP hne
  by_contra! hbad
  have hone : extensionCost q j G A B K P = 1 := by omega
  obtain ⟨Q, hPQ, hQ⟩ := exists_max_petal_extension hmin hP hne hone
  have hQF : Q ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩
  exact hzF Q hQF (hPQ hzP)

end Erdos585.AllHLargestH3R400
