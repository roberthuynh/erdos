import Openmath.Proofs.PaperSupport.Cascade29.SeedMatrixBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

/-- Handshaking counts actual selected cross edges, with arbitrary active support. -/
theorem matrix_balance (F : Finset (Fin 12 × Fin 13))
    (hrow : ∀ i, matrixRowDegree F i = 0 ∨ matrixRowDegree F i = 7)
    (hcol : ∀ j, matrixColumnDegree F j = 0 ∨ matrixColumnDegree F j = 7) :
    (univ.filter fun i => 0 < matrixRowDegree F i).card =
      (univ.filter fun j => 0 < matrixColumnDegree F j).card := by
  let P := univ.filter fun i => 0 < matrixRowDegree F i
  let Q := univ.filter fun j => 0 < matrixColumnDegree F j
  have hP (i : Fin 12) : i ∈ P ↔ 0 < matrixRowDegree F i := by simp [P]
  have hQ (j : Fin 13) : j ∈ Q ↔ 0 < matrixColumnDegree F j := by simp [Q]
  have hFrow : F.card = ∑ i : Fin 12, matrixRowDegree F i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := F) (t := univ) (by simp)
  have hFcol : F.card = ∑ j : Fin 13, matrixColumnDegree F j :=
    card_eq_sum_card_fiberwise (f := Prod.snd) (s := F) (t := univ) (by simp)
  have hsumP : (∑ i : Fin 12, matrixRowDegree F i) = 7 * P.card := by
    calc
      _ = ∑ i : Fin 12, if i ∈ P then 7 else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ P
        · have hd := (hrow i).resolve_left (Nat.ne_of_gt ((hP i).mp hi))
          simp [hi, hd]
        · have hz : matrixRowDegree F i = 0 := by
            have hn := mt (hP i).mpr hi
            omega
          simp [hi, hz]
      _ = 7 * P.card := by simp [mul_comm]
  have hsumQ : (∑ j : Fin 13, matrixColumnDegree F j) = 7 * Q.card := by
    calc
      _ = ∑ j : Fin 13, if j ∈ Q then 7 else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ Q
        · have hd := (hcol j).resolve_left (Nat.ne_of_gt ((hQ j).mp hj))
          simp [hj, hd]
        · have hz : matrixColumnDegree F j = 0 := by
            have hn := mt (hQ j).mpr hj
            omega
          simp [hj, hz]
      _ = 7 * Q.card := by simp [mul_comm]
  change P.card = Q.card
  nlinarith

theorem edge_row_positive (F : Finset (Fin 12 × Fin 13)) (i : Fin 12) (j : Fin 13)
    (h : (i,j) ∈ F) : 0 < matrixRowDegree F i :=
  card_pos.mpr ⟨(i,j), mem_filter.mpr ⟨h, rfl⟩⟩

theorem edge_column_positive (F : Finset (Fin 12 × Fin 13)) (i : Fin 12) (j : Fin 13)
    (h : (i,j) ∈ F) : 0 < matrixColumnDegree F j :=
  card_pos.mpr ⟨(i,j), mem_filter.mpr ⟨h, rfl⟩⟩

/-- An active original degree-seven row forces EVERY original incident edge. -/
theorem active_new_row_full (F : Finset (Fin 12 × Fin 13))
    (hsub : ∀ x ∈ F, seedRel x.1 x.2) (i : Fin 12) (hi : 9 ≤ i.val)
    (hdeg : matrixRowDegree F i = 7) (j : Fin 13) (hij : seedRel i j) :
    (i,j) ∈ F := by
  let R := univ.filter fun x : Fin 12 × Fin 13 => seedRel x.1 x.2
  have hfull : matrixRowDegree R i = 7 := by
    dsimp [R]
    rw [row_card_matrix]
    have h : ∀ i : Fin 12, 9 ≤ i.val → (univ.filter fun j => seedRel i j).card = 7 := by decide
    exact h i hi
  have hsubset : F.filter (fun x => x.1 = i) ⊆ R.filter (fun x => x.1 = i) := by
    intro x hx
    obtain ⟨hxF, hxi⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsub x hxF⟩, hxi⟩
  have heq : F.filter (fun x => x.1 = i) = R.filter (fun x => x.1 = i) :=
    eq_of_subset_of_card_le hsubset (by change matrixRowDegree R i ≤ matrixRowDegree F i; omega)
  have hx : (i,j) ∈ R.filter (fun x => x.1 = i) := by simp [R, hij]
  rw [← heq] at hx
  exact (mem_filter.mp hx).1

/-- The active original degree-seven column24 forces its seven real neighbors. -/
theorem active_last_column_full (F : Finset (Fin 12 × Fin 13))
    (hsub : ∀ x ∈ F, seedRel x.1 x.2)
    (hdeg : matrixColumnDegree F 12 = 7) (i : Fin 12) (hij : seedRel i 12) :
    (i,12) ∈ F := by
  let R := univ.filter fun x : Fin 12 × Fin 13 => seedRel x.1 x.2
  have hfull : matrixColumnDegree R 12 = 7 := by
    dsimp [R]
    rw [column_card_matrix]
    decide
  have hsubset : F.filter (fun x => x.2 = 12) ⊆ R.filter (fun x => x.2 = 12) := by
    intro x hx
    obtain ⟨hxF, hxi⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsub x hxF⟩, hxi⟩
  have heq : F.filter (fun x => x.2 = 12) = R.filter (fun x => x.2 = 12) :=
    eq_of_subset_of_card_le hsubset (by change matrixColumnDegree R 12 ≤ matrixColumnDegree F 12; omega)
  have hx : (i,12) ∈ R.filter (fun x => x.2 = 12) := by simp [R, hij]
  rw [← heq] at hx
  exact (mem_filter.mp hx).1

/-- An actual factor cannot activate column24: that would activate all13 columns. -/
theorem last_column_zero (F : Finset (Fin 12 × Fin 13))
    (hsub : ∀ x ∈ F, seedRel x.1 x.2)
    (hrow : ∀ i, matrixRowDegree F i = 0 ∨ matrixRowDegree F i = 7)
    (hcol : ∀ j, matrixColumnDegree F j = 0 ∨ matrixColumnDegree F j = 7) :
    matrixColumnDegree F 12 = 0 := by
  rcases hcol 12 with hzero | hseven
  · exact hzero
  · have h9 : (9,12) ∈ F := active_last_column_full F hsub hseven 9 (by decide)
    have h10 : (10,12) ∈ F := active_last_column_full F hsub hseven 10 (by decide)
    have hd9 : matrixRowDegree F 9 = 7 :=
      (hrow 9).resolve_left (Nat.ne_of_gt (edge_row_positive F 9 12 h9))
    have hd10 : matrixRowDegree F 10 = 7 :=
      (hrow 10).resolve_left (Nat.ne_of_gt (edge_row_positive F 10 12 h10))
    have hall (j : Fin 13) : 0 < matrixColumnDegree F j := by
      have cover : seedRel 9 j ∨ seedRel 10 j := by
        have h : ∀ j : Fin 13, seedRel 9 j ∨ seedRel 10 j := by decide
        exact h j
      rcases cover with hj | hj
      · exact edge_column_positive F 9 j (active_new_row_full F hsub 9 (by decide) hd9 j hj)
      · exact edge_column_positive F 10 j (active_new_row_full F hsub 10 (by decide) hd10 j hj)
    have hQ : (univ.filter fun j => 0 < matrixColumnDegree F j) = univ := by
      ext j
      simp [hall]
    have hb := matrix_balance F hrow hcol
    rw [hQ, card_univ, Fintype.card_fin] at hb
    have hp := card_le_univ (univ.filter fun i => 0 < matrixRowDegree F i)
    simp only [Fintype.card_fin] at hp
    omega

/-- Every selected original edge is in the literal old9-by-12 graph. -/
theorem selected_edge_old (F : Finset (Fin 12 × Fin 13))
    (hsub : ∀ x ∈ F, seedRel x.1 x.2)
    (hrow : ∀ i, matrixRowDegree F i = 0 ∨ matrixRowDegree F i = 7)
    (hcol : ∀ j, matrixColumnDegree F j = 0 ∨ matrixColumnDegree F j = 7)
    (x : Fin 12 × Fin 13) (hx : x ∈ F) : x.1.val < 9 ∧ x.2.val < 12 := by
  have hz := last_column_zero F hsub hrow hcol
  have hj : x.2.val < 12 := by
    by_contra hj
    have hj12 : x.2 = 12 := Fin.ext (by have hi := x.2.isLt; omega)
    have hp := edge_column_positive F x.1 x.2 hx
    rw [hj12, hz] at hp
    omega
  have hi : x.1.val < 9 := by
    by_contra hi
    have hi9 : 9 ≤ x.1.val := by omega
    have hd : matrixRowDegree F x.1 = 7 :=
      (hrow x.1).resolve_left (Nat.ne_of_gt (edge_row_positive F x.1 x.2 hx))
    have hr : seedRel x.1 12 := by simp [seedRel, hi9]
    have he := active_new_row_full F hsub x.1 hi9 hd 12 hr
    have hp := edge_column_positive F x.1 12 he
    rw [hz] at hp
    omega
  exact ⟨hi,hj⟩

def oldRow (i : Fin 9) : Fin 12 := ⟨i.val, by have hi := i.isLt; omega⟩
def oldColumn (j : Fin 12) : Fin 13 := ⟨j.val, by have hj := j.isLt; omega⟩
def oldPair (x : Fin 9 × Fin 12) : Fin 12 × Fin 13 := (oldRow x.1, oldColumn x.2)
def restrictOld (F : Finset (Fin 12 × Fin 13)) : Finset (Fin 9 × Fin 12) :=
  univ.filter fun x => oldPair x ∈ F

theorem oldPair_injective : Function.Injective oldPair := by
  intro x y h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun z => z.1.val) h
  · exact congrArg (fun z => z.2.val) h

theorem old_relation (i : Fin 9) (j : Fin 12) :
    seedRel (oldRow i) (oldColumn j) ↔ Erdos585.Star21.seedRel i j := by
  simp [seedRel, oldRow, oldColumn, i.isLt, j.isLt,
    Erdos585.Star21.seedRel, Erdos585.Star21.holes]

theorem restriction_row (F : Finset (Fin 12 × Fin 13))
    (hbound : ∀ x ∈ F, x.1.val < 9 ∧ x.2.val < 12) (i : Fin 9) :
    Erdos585.Star21.matrixRowDegree (restrictOld F) i = matrixRowDegree F (oldRow i) := by
  unfold Erdos585.Star21.matrixRowDegree matrixRowDegree
  apply card_bij (fun x _ => oldPair x)
  · intro x hx
    obtain ⟨hxF,hxi⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hxF).2, congrArg oldRow hxi⟩
  · intro x hx y hy hxy
    exact oldPair_injective hxy
  · intro y hy
    obtain ⟨hyF,hyi⟩ := mem_filter.mp hy
    obtain ⟨hr,hc⟩ := hbound y hyF
    let x : Fin 9 × Fin 12 := (⟨y.1.val,hr⟩,⟨y.2.val,hc⟩)
    have heq : oldPair x = y := by apply Prod.ext <;> apply Fin.ext <;> rfl
    refine ⟨x, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩, heq⟩
    · rwa [heq]
    · apply Fin.ext
      exact congrArg (fun z : Fin 12 => z.val) hyi

theorem restriction_column (F : Finset (Fin 12 × Fin 13))
    (hbound : ∀ x ∈ F, x.1.val < 9 ∧ x.2.val < 12) (j : Fin 12) :
    Erdos585.Star21.matrixColumnDegree (restrictOld F) j = matrixColumnDegree F (oldColumn j) := by
  unfold Erdos585.Star21.matrixColumnDegree matrixColumnDegree
  apply card_bij (fun x _ => oldPair x)
  · intro x hx
    obtain ⟨hxF,hxj⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hxF).2, congrArg oldColumn hxj⟩
  · intro x hx y hy hxy
    exact oldPair_injective hxy
  · intro y hy
    obtain ⟨hyF,hyj⟩ := mem_filter.mp hy
    obtain ⟨hr,hc⟩ := hbound y hyF
    let x : Fin 9 × Fin 12 := (⟨y.1.val,hr⟩,⟨y.2.val,hc⟩)
    have heq : oldPair x = y := by apply Prod.ext <;> apply Fin.ext <;> rfl
    refine ⟨x, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩, heq⟩
    · rwa [heq]
    · apply Fin.ext
      exact congrArg (fun z : Fin 13 => z.val) hyj

/-- Actual seed exclusion; its old-seed supplier is an exact source-rebuilt theorem. -/
theorem seed_no_regular_matrix (F : Finset (Fin 12 × Fin 13))
    (hne : F.Nonempty) (hsub : ∀ x ∈ F, seedRel x.1 x.2)
    (hrow : ∀ i, matrixRowDegree F i = 0 ∨ matrixRowDegree F i = 7)
    (hcol : ∀ j, matrixColumnDegree F j = 0 ∨ matrixColumnDegree F j = 7) : False := by
  have hbound : ∀ x ∈ F, x.1.val < 9 ∧ x.2.val < 12 :=
    selected_edge_old F hsub hrow hcol
  have hne0 : (restrictOld F).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨hr,hc⟩ := hbound x hx
    let y : Fin 9 × Fin 12 := (⟨x.1.val,hr⟩,⟨x.2.val,hc⟩)
    have hy : oldPair y = x := by apply Prod.ext <;> apply Fin.ext <;> rfl
    exact ⟨y, mem_filter.mpr ⟨mem_univ _, by rwa [hy]⟩⟩
  apply Erdos585.Star21.seed_no_regular_matrix (restrictOld F) hne0
  · intro x hx
    exact (old_relation x.1 x.2).mp (hsub (oldPair x) (mem_filter.mp hx).2)
  · intro i
    rw [restriction_row F hbound i]
    exact hrow _
  · intro j
    rw [restriction_column F hbound j]
    exact hcol _

end Erdos585.Cascade29
