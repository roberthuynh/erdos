import R863.Resources

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.R863
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
open Resources
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Owners

/-- Every shared strict original row is paid by the exact original convex gap. -/
lemma shared_threshold {q j : ℕ} {A B K C P Q : Finset V}
    (hP : P⊆B\K) {v : V}
    (hvP : v∈residualRows q G A B K C P)
    (hvQ : v∈residualRows q G A B K C Q) :
    -row q G B K v≤(dg G (P∩Q) v : ℤ)+
      (extensionCost q j G A B K P+extensionCost q j G A B K Q-
        extensionCost q j G A B K (P∪Q)-extensionCost q j G A B K (P∩Q)) := by
  classical
  have hvA := (mem_sdiff.mp (mem_filter.mp hvP).1).1
  have hvcan : v∈canonical q G A B (K∪P)∩canonical q G A B (K∪Q) :=
    mem_inter.mpr ⟨mem_filter.mpr ⟨hvA,(mem_filter.mp hvP).2⟩,
      mem_filter.mpr ⟨hvA,(mem_filter.mp hvQ).2⟩⟩
  have hi : (K∪P)∩(K∪Q)=K∪(P∩Q) := (union_inter_distrib_left K P Q).symm
  have hu : (K∪P)∪(K∪Q)=K∪(P∪Q) := by ext w; simp only [mem_union]; tauto
  have hb := bonus_shared (G:=G) q hvcan
  rw [hi] at hb
  have hdis : Disjoint K (P∩Q) := disjoint_left.mpr fun w hwK hwI =>
    (mem_sdiff.mp (hP (mem_inter.mp hwI).1)).2 hwK
  have hd := dg_union_of_disjoint (G:=G) hdis v
  have hsum : bonus q G B (K∪P) (K∪Q) v≤∑ w∈A, bonus q G B (K∪P) (K∪Q) w :=
    single_le_sum (fun w _ => bonus_nonneg q B (K∪P) (K∪Q) w) hvA
  have hid := bonus_sum (G:=G) q A B (K∪P) (K∪Q)
  rw [hi,hu] at hid
  have hmax := le_max_right (0 : ℤ) ((dg G B v : ℤ)-q-dg G (K∪(P∩Q)) v)
  rw [←hb] at hmax
  unfold row extensionCost thetaJ
  zify at hd
  linarith


/-- Big owners retain more than h original columns after deleting any shared rows. -/
lemma big_columns {h q j s : ℕ} {A B K C P : Finset V}
    (hP : P ⊆ B\K)
    (hbig : ∃ v ∈ residualRows q G A B K C P, (h+j+s : ℤ) < -row q G B K v) :
    h+j+s+2 ≤ #P := by
  classical
  obtain ⟨v,hv,ht⟩ := hbig
  have hr := (mem_filter.mp hv).2
  rw [residual_row_add q hP v] at hr
  have hd := dg_le_card (G:=G) P v
  omega

/-- A big owner must have at least q-1 columns, using only the original pool. -/
lemma big_columns_large {h q j e s : ℕ} {A B K C P : Finset V}
    (d : Data h q j e G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1)
    (hP : P ⊆ B\K) (hc : extensionCost q j G A B K P ≤ s)
    (hbig : ∃ v ∈ residualRows q G A B K C P, (h+j+s : ℤ) < -row q G B K v) :
    q-1 ≤ #P := by
  classical
  have hcols := big_columns hP hbig
  have hshape := d.positive_shape opt hK hl (by have hj:=d.parameters.j_pos; omega)
  have hpool := PetalEscape.pool_bound d opt hK
  have hweight : petalWeight q G A B K C P ≤
      (ec G C (B\K) : ℤ)+ec G (A\C) K+deficiency (2*(q : ℤ)-2) G B (A\C) := by
    have he := ec_mono_right (G:=G) C hP
    have hJ : residualRows q G A B K C P ⊆ A\C := filter_subset _ _
    have hi := ec_mono_right (G:=G) K hJ
    have ha := deficiency_le_subset (2*(q : ℤ)-2) hJ
      (fun v hv => d.capA_int (mem_sdiff.mp hv).1)
    simp only [ec_comm (G:=G) K] at hi
    unfold petalWeight
    dsimp only
    zify at he hi
    omega
  have hid := petal_resource_identity (j:=j) opt hP
  dsimp only at hid hshape
  have hn := d.parameters.numeric
  have hj := d.parameters.j_bounds
  have hh := d.parameters.height_int
  by_contra! hbad
  have hpc : (#P : ℤ) ≤ (q : ℤ)-2 := by omega
  have he : (ec G (residualRows q G A B K C P) P : ℤ) ≤
      (#(residualRows q G A B K C P) : ℤ)*#P := by
    rw [ec,Nat.cast_sum]
    calc
      _ ≤ ∑ _v∈residualRows q G A B K C P, (#P : ℤ) :=
        sum_le_sum fun v _ => by exact_mod_cast dg_le_card (G:=G) P v
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hm := mul_nonneg (Nat.cast_nonneg #(residualRows q G A B K C P) : (0 : ℤ) ≤ _)
    (show 0 ≤ (q : ℤ)-2-#P by omega)
  have hpq := mul_nonneg (show 0 ≤ (#P : ℤ)-(h+j+s+2) by omega)
    (Nat.cast_nonneg q : (0 : ℤ)≤q)
  have hsq := mul_nonneg (Nat.cast_nonneg s : (0 : ℤ)≤s)
    (show 0 ≤ (q : ℤ)-1 by omega)
  unfold coreDefect at hid
  have hGamma : (q : ℤ)*#P-s ≤ petalWeight q G A B K C P := by
    dsimp only [petalWeight]
    nlinarith only [hid,he,hm,hc]
  have hk := hshape.2.2.2.1
  have ha := hn.2.1
  have hjb := hj.2
  have hqpos := d.parameters.q_pos
  have hbudget : petalWeight q G A B K C P < ((h : ℤ)+j)*q := by
    nlinarith only [hweight,hpool,hk,ha,hjb,hp,
      (Nat.cast_nonneg s : (0 : ℤ)≤s)]
  nlinarith only [hGamma,hbudget,hpq,hsq,hqpos]

/-- Delete ALL repeated rows, with literal original proper-support guards. -/
lemma charge_delete {h q j e : ℕ} {A B K C P Y : Finset V}
    (d : Data h q j e G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K) (hP : P ⊆ B\K)
    (hlarge : h ≤ #P) (hY : Y ⊆ residualRows q G A B K C P) :
    (h : ℤ)*q-offset h e-e+1-extensionCost q j G A B K P+
      ((#P : ℤ)-#(residualRows q G A B K C P))+
      ((q : ℤ)-1)*#Y-ec G Y P ≤ petalWeight q G A B K C P := by
  classical
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A := (filter_subset _ _).trans sdiff_subset
  have hpc := card_le_card hP
  have hkc := card_sdiff_add_card_eq_card hK
  have hjc := card_le_card (sdiff_subset : J\Y ⊆ J)
  have hja := card_le_card hJ
  have hq := d.parameters.q_ge_height
  have hf := d.sparse (J\Y) (sdiff_subset.trans hJ) P (hP.trans sdiff_subset)
    (by omega) (by omega)
  have hh := twice_coreDefect (G:=G) q (J\Y) P
  have hi := petal_resource_identity (j:=j) opt hP
  dsimp only at hi
  change coreDefect q G J P=petalWeight q G A B K C P+
    extensionCost q j G A B K P-((#P : ℤ)-#J) at hi
  have hc := card_sdiff_add_card_eq_card hY
  have he := ec_sdiff_add_left (G:=G) hY P
  unfold coreDefect at hi hh
  zify at hc he
  dsimp only [J] at hf hh hi hc he ⊢
  nlinarith

/-- Delete all shared rows and columns; both exclusive supports pay the original floor. -/
lemma exclusive_charge {h q j e : ℕ} {A B K C P Y I : Finset V}
    (d : Data h q j e G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K) (hP : P ⊆ B\K)
    (hI : I ⊆ P) (hlarge : h ≤ #(P\I))
    (hY : Y ⊆ residualRows q G A B K C P) :
    (h : ℤ)*q-offset h e-e+1-extensionCost q j G A B K P+
      ((#P : ℤ)-#(residualRows q G A B K C P))+
      ((q : ℤ)-1)*#Y-ec G Y P+
      ((q : ℤ)-1)*#I-ec G (residualRows q G A B K C P\Y) I ≤
      petalWeight q G A B K C P := by
  classical
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A := (filter_subset _ _).trans sdiff_subset
  have hpc := card_le_card hP
  have hkc := card_sdiff_add_card_eq_card hK
  have hjc := card_le_card (sdiff_subset : J\Y ⊆ J)
  have hja := card_le_card hJ
  have hpi := card_le_card (sdiff_subset : P\I ⊆ P)
  have hq := d.parameters.q_ge_height
  have hf := d.sparse (J\Y) (sdiff_subset.trans hJ) (P\I)
    (sdiff_subset.trans (hP.trans sdiff_subset)) (by omega) (by omega)
  have hh := twice_coreDefect (G:=G) q (J\Y) (P\I)
  have hi := petal_resource_identity (j:=j) opt hP
  dsimp only at hi
  change coreDefect q G J P=petalWeight q G A B K C P+
    extensionCost q j G A B K P-((#P : ℤ)-#J) at hi
  have hc := card_sdiff_add_card_eq_card hY
  have he := ec_sdiff_add_left (G:=G) hY P
  have hci := card_sdiff_add_card_eq_card hI
  have hei := ec_sdiff_add_right (G:=G) hI (J\Y)
  unfold coreDefect at hi hh
  zify at hc he hci hei
  dsimp only [J] at hf hh hi hc he hei ⊢
  nlinarith

/-- Four disjoint original row classes share the original cap on common columns. -/
lemma four_row_cap {h q j e : ℕ} {A B C JP JQ I : Finset V}
    (d : Data h q j e G A B) (hC : C ⊆ A)
    (hJP : JP ⊆ A\C) (hJQ : JQ ⊆ A\C) (hI : I ⊆ B) :
    (ec G C I : ℤ)+ec G (JP∩JQ) I+ec G (JP\(JP∩JQ)) I+
      ec G (JQ\(JP∩JQ)) I ≤ (2*(q : ℤ)-2)*#I := by
  classical
  have hp := ec_sdiff_add_left (G:=G) (inter_subset_left : JP∩JQ ⊆ JP) I
  have hq := ec_sdiff_add_left (G:=G) (inter_subset_right : JP∩JQ ⊆ JQ) I
  have hu := ec_modular (G:=G) I JP JQ
  rw [ec_comm (G:=G) I (JP∪JQ),ec_comm (G:=G) I (JP∩JQ),
    ec_comm (G:=G) I JP,ec_comm (G:=G) I JQ] at hu
  have hd : Disjoint C (JP∪JQ) := disjoint_left.mpr fun v hv hw => by
    rcases mem_union.mp hw with hp|hq
    · exact (mem_sdiff.mp (hJP hp)).2 hv
    · exact (mem_sdiff.mp (hJQ hq)).2 hv
  have he := ec_union_left (G:=G) hd I
  have hsub : C∪(JP∪JQ) ⊆ A := union_subset hC
    (union_subset (hJP.trans sdiff_subset) (hJQ.trans sdiff_subset))
  have hcap := d.edge_cap_T hsub hI
  zify at hp hq hu he
  omega

/-- Both original charges use one pool, with every repeated unit explicit. -/
lemma pair_pool {h q j e : ℕ} {A B K C P Q : Finset V}
    (d : Data h q j e G A B) (hP : P ⊆ B\K) (hQ : Q ⊆ B\K) :
    let Y := residualRows q G A B K C P ∩ residualRows q G A B K C Q
    petalWeight q G A B K C P+petalWeight q G A B K C Q ≤
      (ec G C (B\K) : ℤ)+ec G (A\C) K+deficiency (2*(q : ℤ)-2) G B (A\C)+
      ec G C (P∩Q)+ec G Y K+deficiency (2*(q : ℤ)-2) G B Y := by
  classical
  dsimp only
  let JP := residualRows q G A B K C P
  let JQ := residualRows q G A B K C Q
  have hJP : JP ⊆ A\C := filter_subset _ _
  have hJQ : JQ ⊆ A\C := filter_subset _ _
  have he := ec_modular (G:=G) C P Q
  have hi := ec_modular (G:=G) K JP JQ
  have hs : deficiency (2*(q : ℤ)-2) G B (JP∪JQ)+
      deficiency (2*(q : ℤ)-2) G B (JP∩JQ)=
      deficiency (2*(q : ℤ)-2) G B JP+deficiency (2*(q : ℤ)-2) G B JQ := sum_union_inter
  have hE := ec_mono_right (G:=G) C (union_subset hP hQ)
  have hI := ec_mono_right (G:=G) K (union_subset hJP hJQ)
  have hscar := deficiency_le_subset (2*(q : ℤ)-2) (union_subset hJP hJQ)
    (fun v hv => d.capA_int (mem_sdiff.mp hv).1)
  simp only [ec_comm (G:=G) K] at hi hI
  unfold petalWeight
  zify at he hi hE hI
  dsimp only [JP,JQ] at *
  linarith

/-- Literal rowwise identity pays repeated incoming units and scars in full. -/
lemma repeated_row_refund {q : ℕ} {B K P Q : Finset V}
    (hK : K ⊆ B) (hPQ : P∪Q ⊆ B\K) (v : V) :
    (2*((q : ℤ)-1)-dg G P v-dg G Q v)-dg G K v-
      (2*(q : ℤ)-2-dg G B v) ≥ -(dg G (P∩Q) v : ℤ) := by
  classical
  have hd := dg_union_add_dg_inter (G:=G) P Q v
  have hm := dg_mono (G:=G) hPQ v
  have hs := dg_sdiff_add (G:=G) hK v
  zify at hd hm hs
  linarith

/-- The sum of ALL repeated original row units is paid, with no weak-row choice. -/
lemma repeated_refund {q : ℕ} {B K P Q Y : Finset V}
    (hK : K ⊆ B) (hP : P ⊆ B\K) (hQ : Q ⊆ B\K) :
    2*((q : ℤ)-1)*#Y-ec G Y P-ec G Y Q-ec G Y K-
      deficiency (2*(q : ℤ)-2) G B Y ≥ -(ec G Y (P∩Q) : ℤ) := by
  classical
  have hs := sum_le_sum (s:=Y) (fun v _ => repeated_row_refund (G:=G) (q:=q) hK (union_subset hP hQ) v)
  simp only [ec,Nat.cast_sum,deficiency] at *
  simp only [sum_sub_distrib,sum_neg_distrib,sum_const,nsmul_eq_mul] at *
  nlinarith


/-- Deleting one actual column loses at most one unit per actual strict row. -/
lemma deletion_marginal {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C) (hP : P ⊆ B\K) {v : V} (hv : v ∈ P) :
    (q : ℤ)-dg G C v ≤ extensionCost q j G A B K P-
      extensionCost q j G A B K (P.erase v)+#(residualRows q G A B K C P) := by
  classical
  let f := fun a => max 0 (row q G B K a+dg G P a)
  let g := fun a => max 0 (row q G B K a+dg G (P.erase v) a)
  have hsplit : ∀ a, dg G (P.erase v) a+dg G {v} a=dg G P a := by
    intro a
    have hd : Disjoint (P.erase v) {v} := disjoint_singleton_right.mpr (notMem_erase _ _)
    have hset : P.erase v ∪ {v}=P := by
      ext w
      simp only [mem_union,mem_erase,mem_singleton]
      constructor
      · rintro (⟨_,hw⟩|rfl)
        · exact hw
        · exact hv
      · intro hw
        by_cases he : w=v
        · exact Or.inr he
        · exact Or.inl ⟨he,hw⟩
    simpa only [hset] using (dg_union_of_disjoint (G:=G) hd a).symm
  have hsum : (∑ a∈A\C, (f a-g a)) ≤ #(residualRows q G A B K C P) := by
    calc
      _ ≤ ∑ a∈A\C, if 0 < row q G B (K∪P) a then (1 : ℤ) else 0 := by
        apply sum_le_sum
        intro a _
        have hd := hsplit a
        have h1 := dg_le_card (G:=G) ({v} : Finset V) a
        simp only [card_singleton] at h1
        have hrow := residual_row_add (G:=G) q hP a
        dsimp [f,g]
        split_ifs with hh <;> omega
      _ = _ := by
        simp only [residualRows,card_eq_sum_ones,sum_filter,Nat.cast_sum,
          Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hu := extensionCost_units (j:=j) opt hP
  have he := extensionCost_units (j:=j) opt ((erase_subset v P).trans hP)
  have hcard : #(P.erase v)+1=#P := by rw [card_erase_of_mem hv];have hh:=card_pos.mpr ⟨v,hv⟩;omega
  have hne : 0<#P := card_pos.mpr ⟨v,hv⟩
  have hec : ec G C (P.erase v)+dg G C v=ec G C P := by
    rw [ec_comm (G:=G) C (P.erase v),ec_comm (G:=G) C P,ec,ec]
    exact sum_erase_add P (fun w => dg G C w) hv
  rw [sum_sub_distrib] at hsum
  zify at hcard hec
  dsimp only [f,g] at hsum
  nlinarith

/-- ALL nonbig bad sets are covered by the one fixed heavy-column family. -/
lemma nonbig_heavy {h q j e s : ℕ} {A B K P : Finset V}
    (d : Data h q j e G A B) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B\K) (hc : extensionCost q j G A B K P ≤ s)
    (hnb : ∀ v ∈ residualRows q G A B K (weakCore q G A B K) P,
      -row q G B K v ≤ h+j+s) :
    ∀ v ∈ P, (q : ℤ)-dg G (weakCore q G A B K) v ≤ (e : ℤ)+5*h := by
  classical
  let C := weakCore q G A B K
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hs := weak_count d opt hK hl hp
  have hJ : residualRows q G A B K C P ⊆ weakRows q (h+j+s) G A B K C := by
    intro v hv
    exact mem_filter.mpr ⟨(mem_filter.mp hv).1,hnb v hv⟩
  have hjc := card_le_card hJ
  have hshape := high_shape d opt hK hl hp
  intro v hv
  by_cases he : P={v}
  · have hrows : residualRows q G A B K C {v}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hh := weak_outside_strict (G:=G) q A B K (mem_filter.mp ha).1
      have hp' := (mem_filter.mp ha).2
      rw [residual_row_add q (singleton_subset_iff.mpr (hP hv)) a] at hp'
      have hd := dg_le_card (G:=G) ({v} : Finset V) a
      simp only [card_singleton] at hd
      omega
    have hu := extensionCost_linear_of_no_rows (j:=j) opt
      (singleton_subset_iff.mpr (hP hv)) hrows
    have hec : ec G C {v}=dg G C v := by rw [ec_comm];simp [ec]
    rw [he] at hc
    simp only [card_singleton,Nat.cast_one,mul_one,hec] at hu
    dsimp only at hs hshape
    change (q : ℤ)-dg G C v ≤ _
    omega
  · have hne : (P.erase v).Nonempty := by
      by_contra hn
      have hz := not_nonempty_iff_eq_empty.mp hn
      apply he
      ext w
      simp only [mem_singleton]
      constructor
      · intro hw
        by_contra hwv
        have hh : w ∈ P.erase v := mem_erase.mpr ⟨hwv,hw⟩
        rw [hz] at hh
        exact notMem_empty _ hh
      · rintro rfl
        exact hv
    have hm := hmin (P.erase v) ((erase_subset _ _).trans hP) hne
    have hd := deletion_marginal (j:=j) opt hP hv
    dsimp only at hs hshape
    change (q : ℤ)-dg G C v ≤ _
    omega

end Owners
end Erdos585.R863
