import ExceptionalSet
import HighIncidenceNeighbor
import NeighborhoodAssignment

/-! Source correspondence: COUNT-BASED-COMPLETION.md §§1, 4–7,
Historical source SHA256 (before public exposition edits): d07eaa46889ac5a9808a097f281e43c25a768e5057e19ddefe5b72952d9eacbb.
This conditional completion theorem retains an ACTUAL finite projective plane
of order q on the graph's vertex type and actual incidence representations of
all good full rows. Plane existence/embedding is not proved or postulated by
an axiom. Actual exceptional-set, good-row, missing-line and high-incidence
bounds are derived internally from the original graph contract. -/
namespace Erdos60.Completion
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]
variable [Configuration.ProjectivePlane P L]

/-- Conditional completion with the actual embedding explicitly supplied.
All other numerical and graph suppliers follow from the original contract.
The evenness hypothesis is retained for the original contract; after an actual
embedding is supplied, this downstream step no longer needs parity. -/
theorem embedded_good_rows_complete_graph
    (G : SimpleGraph P) (hG : NoFourCycle G) (q : ℕ)
    (_heven : Even q) (hq : 100000000 ≤ q)
    (hN : Fintype.card P = q^2+q+1)
    (hmin : ∀ v, 999*q ≤ 1000*G.degree v)
    (hcap : ∀ v, G.degree v ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun v : P => G.degree v ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun v : P => G.degree v ≤ q-1)).card ≤ q)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (row : P → L)
    (hrow : ∀ a ∈ goodFullVertices G q
        (Finset.univ.filter (fun v : P => G.degree v ≤ q)),
      ∀ x, x ∈ row a ↔ G.Adj a x) :
    ∃ π : Erdos60.Geometry.Polarity (P := P) (L := L), G ≤ π.graph := by
  classical
  let S := Finset.univ.filter (fun v : P => G.degree v ≤ q)
  let D := Finset.univ.filter (fun v : P => G.degree v ≤ q-1)
  let B := exceptionalVertices G q S
  let A := goodFullVertices G q S
  have hSc : 1000*S.card ≤ 1001*q := hS
  have hDc : 1000*D.card ≤ q := hD
  have hBc : B.card ≤ 11000 := exceptionalVertices_card G hG q hq S hSc
  have hfull : ∀ a ∈ A, G.degree a = q+1 := by
    intro a ha
    exact ((mem_goodFullVertices G q S a).mp ha).1
  have hA : ∀ a, a ∈ A ↔ G.degree a = q+1 ∧ a ∉ B := by
    intro a
    exact mem_goodFullVertices G q S a
  have hhigh : ∀ v, ∃ u, G.Adj v u ∧ q-2 ≤ (G.neighborFinset u ∩ A).card := by
    intro v
    exact high_incidence_neighbor G hG q hq hmin hcap S D B A
      (fun x => by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and])
      (fun x => by simp only [D,Finset.mem_filter,Finset.mem_univ,true_and])
      hA hSc hDc hBc v
  have hAlower : (q:ℝ)^2-(q:ℝ)/1000+1-11000 ≤ A.card :=
    goodFullVertices_card_lower G hG q hq hN hcap hS
  have hqr : (100000000:ℝ) ≤ q := by exact_mod_cast hq
  have hqq : q ≤ q^2 := by nlinarith
  have hAsize : q^2-q+4 ≤ A.card := by
    have hh : ((q^2-q+4 : ℕ):ℝ) ≤ A.card := by
      rw [Nat.cast_add,Nat.cast_sub hqq,Nat.cast_pow,Nat.cast_ofNat]
      linarith
    exact_mod_cast hh
  have hrowA : ∀ a ∈ A, ∀ x, x ∈ row a ↔ G.Adj a x := hrow
  have hinj := actual_full_rows_injOn G hG A row q (by omega) hfull hrowA
  have hIcard : (A.image row).card = A.card := Finset.card_image_iff.mpr hinj
  have hLcard : Fintype.card L = q^2+q+1 := by
    rw [Configuration.ProjectivePlane.card_lines P L,ho]
  have hpart : (Finset.univ \ A.image row).card + A.card = q^2+q+1 := by
    have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset L) (A.image row)
    simpa only [Finset.univ_inter,Finset.card_univ,hIcard,hLcard] using hh
  have hpartR : ((Finset.univ \ A.image row).card : ℝ)+A.card = (q:ℝ)^2+q+1 := by
    exact_mod_cast hpart
  have hmissing : ((Finset.univ \ A.image row).card : ℝ) ≤ (1002:ℝ)*q/1000 := by
    linarith
  have hminR : ∀ v, (999:ℝ)*q/1000 ≤ G.degree v := by
    intro v
    have hm : (999:ℝ)*q ≤ 1000*G.degree v := by exact_mod_cast hmin v
    linarith
  exact embedded_rows_produce_polarity G hG A row q hq ho hfull hrowA hminR hmissing hhigh hAsize

#print axioms embedded_good_rows_complete_graph
end Erdos60.Completion
