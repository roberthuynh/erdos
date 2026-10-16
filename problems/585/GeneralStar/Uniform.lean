import GeneralStar.Transfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

def hole (h b i : ℕ) : Finset (Fin b) :=
  univ.filter fun j => i*h ≤ j.val ∧ j.val < (i+1)*h

theorem hole_card (h b i : ℕ) (hb : (i+1)*h ≤ b) : (hole h b i).card=h := by
  have he : hole h b i=
      (univ.filter fun j : Fin b => j.val < (i+1)*h) \ (univ.filter fun j : Fin b => j.val < i*h) := by
    ext j;simp [hole];omega
  have hsub : (univ.filter fun j : Fin b => j.val < i*h) ⊆
      univ.filter fun j : Fin b => j.val < (i+1)*h := by
    intro j hj
    simp only [mem_filter,mem_univ,true_and] at hj ⊢
    nlinarith
  rw [he,card_sdiff_of_subset hsub,L17HCq.fin_lt_card,L17HCq.fin_lt_card,
    Nat.min_eq_right hb,Nat.min_eq_right (by nlinarith)]
  have he : (i+1)*h=i*h+h := by ring
  rw [he,Nat.add_sub_cancel_left]

theorem hole_disjoint (h b i j : ℕ) (hne : i ≠ j) : Disjoint (hole h b i) (hole h b j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := (mem_filter.mp hxi).2
  have hj := (mem_filter.mp hxj).2
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hm := Nat.mul_le_mul_right h (show i+1 ≤ j by omega)
    omega
  · have hm := Nat.mul_le_mul_right h (show j+1 ≤ i by omega)
    omega

theorem uniform_row (q s p h b : ℕ) (hp : p*h ≤ b) (i : Fin (q+s)) :
    L17HCq.rowDegree (uniformRel q s p h b) univ i=b-if i.val < p then h else 0 := by
  unfold L17HCq.rowDegree
  by_cases hi : i.val < p
  · have he : (univ.filter (uniformRel q s p h b i))=univ \ hole h b i.val := by
      ext j;simp [uniformRel,hole,hi]
    rw [he,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,
      hole_card h b i.val (by nlinarith)]
    rw [if_pos hi]
  · have he : (univ.filter (uniformRel q s p h b i))=univ := by
      ext j;simp [uniformRel,hi]
    simp [he,hi]

theorem uniform_column_bounds (q s p h b : ℕ) (j : Fin b) :
    q+s-1 ≤ L17HCq.columnDegree (uniformRel q s p h b) univ j ∧
    L17HCq.columnDegree (uniformRel q s p h b) univ j ≤ q+s := by
  let E := (univ : Finset (Fin (q+s))).filter fun i => ¬uniformRel q s p h b i j
  have hE : E.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi k hk
    by_contra hne
    have hi' : j ∈ hole h b i.val := by
      have := (mem_filter.mp hi).2
      simp only [uniformRel,not_not] at this
      exact mem_filter.mpr ⟨mem_univ _,this.2⟩
    have hk' : j ∈ hole h b k.val := by
      have := (mem_filter.mp hk).2
      simp only [uniformRel,not_not] at this
      exact mem_filter.mpr ⟨mem_univ _,this.2⟩
    have hval : i.val ≠ k.val := fun he => hne (Fin.ext he)
    exact Finset.disjoint_left.mp (hole_disjoint h b i.val k.val hval) hi' hk'
  have he := card_filter_add_card_filter_not (s := (univ : Finset (Fin (q+s))))
    (fun i => uniformRel q s p h b i j)
  change (univ.filter fun i => uniformRel q s p h b i j).card+E.card= _ at he
  simp only [card_univ,Fintype.card_fin] at he
  unfold L17HCq.columnDegree
  omega

theorem uniform_noRegular (q s p h b : ℕ) (hq : 5 ≤ q) (hp : UParams q s p h b) :
    BqLowerFamily.NoRegular q (uniformSeed q s p h b).graph := by
  rcases hp with ⟨hs,hps,hhs,hpa,hab,hbr,hph,hrh,hend0,hends⟩
  apply L17HCq.noRegular_crossGraph _ q (by omega)
  intro P Q hP hbal hrow _hcol
  obtain ⟨i,hi⟩ := hP
  have hqk : q ≤ P.card := by
    have hl := hrow i hi
    have hc := card_filter_le Q (uniformRel q s p h b i)
    unfold L17HCq.rowDegree at hl
    omega
  have hka : P.card ≤ q+s := by simpa using card_le_univ P
  let x := P.card-q
  have hx : x ≤ s := by dsimp [x];omega
  have heK : P.card=q+x := by dsimp [x];omega
  let S := P.filter fun i => i.val < p
  have hSc : p-s+x ≤ S.card := by
    have hpart := card_filter_add_card_filter_not (s := P) (fun i => i.val < p)
    have hc : (P.filter fun i => ¬i.val < p).card ≤ q+s-p := by
      have hsub : P.filter (fun i => ¬i.val < p) ⊆
          univ.filter fun i : Fin (q+s) => p ≤ i.val := by
        intro i hi
        have hip := (mem_filter.mp hi).2
        simp only [mem_filter,mem_univ,true_and];omega
      have hc := card_le_card hsub
      rw [L17HCq.fin_ge_card,Nat.min_eq_right hpa] at hc
      exact hc
    change S.card+(P.filter fun i => ¬i.val < p).card=P.card at hpart
    omega
  have outside (i : Fin (q+s)) (hi : i ∈ S) : h-x ≤ (hole h b i.val \ Q).card := by
    have hip : i.val < p := (mem_filter.mp hi).2
    have hc := hole_card h b i.val (by nlinarith)
    have hsplit := card_sdiff_add_card_inter (hole h b i.val) Q
    have hmiss : hole h b i.val ∩ Q=Q.filter fun j => ¬uniformRel q s p h b i j := by
      ext j;simp [uniformRel,hole,hip,and_comm]
    rw [hmiss] at hsplit
    have hpart := card_filter_add_card_filter_not (s := Q) (uniformRel q s p h b i)
    have hl := hrow i (mem_filter.mp hi).1
    unfold L17HCq.rowDegree at hl
    rw [← hbal,heK] at hpart
    omega
  have hdis : (S : Set (Fin (q+s))).PairwiseDisjoint (fun i => hole h b i.val \ Q) := by
    intro i _ j _ hij
    apply (hole_disjoint h b i.val j.val (fun he => hij (Fin.ext he))).mono
    · exact sdiff_subset
    · exact sdiff_subset
  have hsub : S.biUnion (fun i => hole h b i.val \ Q) ⊆ univ \ Q := by
    intro j hj
    obtain ⟨i,_,hij⟩ := mem_biUnion.mp hj
    exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hij).2⟩
  have hc := card_le_card hsub
  rw [card_biUnion hdis,card_sdiff_of_subset (subset_univ Q),card_univ,Fintype.card_fin,
    ←hbal,heK] at hc
  have hsum : S.card*(h-x) ≤ ∑ i ∈ S, (hole h b i.val \ Q).card := by
    calc
      _ = ∑ _i ∈ S, (h-x) := by simp
      _ ≤ _ := sum_le_sum (fun i hi => outside i hi)
  have hnec : (p-s+x)*(h-x) ≤ b-q-x := by
    have hm := Nat.mul_le_mul_right (h-x) hSc
    omega
  have hxs : x=s ∨ x<s := by omega
  have hbq : q+s ≤ b := hab
  have hp0 : s ≤ p := by omega
  have hh0 : s ≤ h := by omega
  have hpq : p-s+x+s=p+x := by omega
  have hhx : h-x+x=h := by omega
  have hb0 : b-q-x+q+x=b := by omega
  have hbb : b-q+q=b := by omega
  have hbs : b-q-s+q+s=b := by omega
  rcases hxs with hex | hlt
  · rw [hex] at hnec
    have he : p-s+s=p := by omega
    rw [he] at hnec
    omega
  · have hxnon : 0 ≤ (x : ℤ) := by positivity
    have hspos : 0 < (s : ℤ) := by omega
    have hgap : 0 < (s : ℤ)-x := by omega
    have hidentity :
      (s : ℤ)*(((p-s+x : ℕ):ℤ)*((h-x : ℕ):ℤ)-((b-q-x : ℕ):ℤ)) =
      ((s:ℤ)-x)*(((p-s : ℕ):ℤ)*h-((b-q : ℕ):ℤ))+
      (x:ℤ)*((p:ℤ)*((h-s : ℕ):ℤ)-((b-q-s : ℕ):ℤ))+
      (s:ℤ)*x*((s:ℤ)-x) := by
      have hpZ : ((p-s:ℕ):ℤ)=(p:ℤ)-s := by omega
      have hhZ : ((h-x:ℕ):ℤ)=(h:ℤ)-x := by omega
      have hhsZ : ((h-s:ℕ):ℤ)=(h:ℤ)-s := by omega
      have hbZ : ((b-q:ℕ):ℤ)=(b:ℤ)-q := by omega
      have hbxZ : ((b-q-x:ℕ):ℤ)=(b:ℤ)-q-x := by omega
      have hbsZ : ((b-q-s:ℕ):ℤ)=(b:ℤ)-q-s := by omega
      have hpxZ : ((p-s+x:ℕ):ℤ)=(p:ℤ)-s+x := by omega
      rw [hpZ,hhZ,hhsZ,hbZ,hbxZ,hbsZ,hpxZ]
      ring
    have h0Z : 0 < (((p-s:ℕ):ℤ)*h-((b-q:ℕ):ℤ)) := by
      have hc : ((b-q:ℕ):ℤ) < (((p-s:ℕ):ℤ)*h) := by exact_mod_cast hend0
      omega
    have hsZ : 0 < ((p:ℤ)*((h-s:ℕ):ℤ)-((b-q-s:ℕ):ℤ)) := by
      have hc : ((b-q-s:ℕ):ℤ) < ((p:ℤ)*((h-s:ℕ):ℤ)) := by exact_mod_cast hends
      omega
    have hnZ : (((p-s+x:ℕ):ℤ)*((h-x:ℕ):ℤ)-((b-q-x:ℕ):ℤ)) ≤ 0 := by
      have hc : (((p-s+x:ℕ):ℤ)*((h-x:ℕ):ℤ)) ≤ ((b-q-x:ℕ):ℤ) := by exact_mod_cast hnec
      omega
    have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hspos) hnZ
    have hp1 := mul_pos hgap h0Z
    have hp2 := mul_nonneg hxnon (le_of_lt hsZ)
    have hp3 := mul_nonneg (mul_nonneg (le_of_lt hspos) hxnon) (le_of_lt hgap)
    linarith

end Erdos585.GeneralStar
