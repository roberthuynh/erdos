import AllHNextNonstrict.PetalEscape

/-! Exact R117/R121 highest-height escape. All owners and units are original. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHNextNonstrict
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace TopEscape

/-- An actual maximal nonempty original residual set of cost at most two. -/
def Owner (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K P : Finset V) : Prop :=
  P ⊆ B \ K ∧ P.Nonempty ∧ extensionCost q j G A B K P ≤ 2 ∧
    ∀ Q ⊆ B \ K, P ⊆ Q → P ≠ Q → 3 ≤ extensionCost q j G A B K Q

lemma exists_owner {q j : ℕ} {A B K P : Finset V} (hP : P ⊆ B \ K)
    (hne : P.Nonempty) (hc : extensionCost q j G A B K P ≤ 2) :
    ∃ Q, P ⊆ Q ∧ Owner q j G A B K Q := by
  let F := (B \ K).powerset.filter fun Q => P ⊆ Q ∧ extensionCost q j G A B K Q ≤ 2
  have hF : F.Nonempty := ⟨P, mem_filter.mpr ⟨mem_powerset.mpr hP, Subset.rfl, hc⟩⟩
  obtain ⟨Q,hQ,hmax⟩ := exists_max_image F Finset.card hF
  obtain ⟨hqr,hpq,hqc⟩ := mem_filter.mp hQ
  have hQr := mem_powerset.mp hqr
  refine ⟨Q,hpq,hQr,hne.mono hpq,hqc,?_⟩
  intro Z hZ hQZ hneQZ
  by_contra! hbad
  have hzF : Z ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hZ,hpq.trans hQZ,by omega⟩
  have hle := hmax Z hzF
  have hlt : #Q < #Z := card_lt_card ⟨hQZ,fun hZQ => hneQZ (Subset.antisymm hQZ hZQ)⟩
  omega

lemma Owner.not_subset {q j : ℕ} {A B K P Q : Finset V}
    (hP : Owner q j G A B K P) (hQ : Owner q j G A B K Q) (hne : P ≠ Q) : ¬P ⊆ Q := by
  intro hPQ
  have hh := hP.2.2.2 Q hQ.1 hPQ hne
  have hc := hQ.2.2.1
  omega

lemma residualRows_mono {q : ℕ} {A B K C P Q : Finset V} (hPQ : P ⊆ Q) :
    residualRows q G A B K C P ⊆ residualRows q G A B K C Q := by
  intro v hv
  obtain ⟨hvL,hvP⟩ := mem_filter.mp hv
  have hd := dg_mono (G := G) (union_subset_union (show K ⊆ K from Subset.rfl) hPQ) v
  refine mem_filter.mpr ⟨hvL,?_⟩
  unfold row at *
  omega

lemma cost_nonneg {q j : ℕ} {A B K P : Finset V}
    (hmin : ∀ P ⊆ B \ K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B \ K) : 0 ≤ extensionCost q j G A B K P := by
  by_cases he : P = ∅
  · simp [he,extensionCost]
  · have hp := hmin P hP (nonempty_iff_ne_empty.mpr he)
    omega

lemma singleton_weight_pos {q j : ℕ} {A B K C : Finset V}
    (opt : Optimizer q G A B K C)
    (hmin : ∀ P ⊆ B \ K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    {v : V} (hv : v ∈ B \ K) : 1 ≤ (q : ℤ) - dg G C v := by
  have hm := hmin {v} (singleton_subset_iff.mpr hv) (singleton_nonempty v)
  have hl := extensionCost_le_linear (j := j) opt (singleton_subset_iff.mpr hv)
  have he : ec G C {v} = dg G C v := by rw [ec_comm]; simp [ec]
  simp only [card_singleton,Nat.cast_one,mul_one,he] at hl
  omega

lemma no_rows_sum {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C) (hP : P ⊆ B \ K)
    (hJ : residualRows q G A B K C P = ∅) :
    extensionCost q j G A B K P = ∑ v ∈ P, ((q : ℤ) - dg G C v) := by
  rw [extensionCost_linear_of_no_rows opt hP hJ,ec_comm,ec,Nat.cast_sum,
    sum_sub_distrib,sum_const,nsmul_eq_mul]
  ring

lemma no_rows_card {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C)
    (hmin : ∀ P ⊆ B \ K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B \ K) (hJ : residualRows q G A B K C P = ∅) :
    (#P : ℤ) ≤ extensionCost q j G A B K P := by
  rw [no_rows_sum opt hP hJ]
  calc
    _ = ∑ _v ∈ P, (1 : ℤ) := by simp
    _ ≤ _ := sum_le_sum fun v hv => singleton_weight_pos opt hmin (hP hv)

lemma no_rows_point {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C)
    (hmin : ∀ P ⊆ B \ K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B \ K) (hJ : residualRows q G A B K C P = ∅)
    {v : V} (hv : v ∈ P) :
    (q : ℤ) - dg G C v ≤ extensionCost q j G A B K P := by
  rw [no_rows_sum opt hP hJ]
  exact single_le_sum (fun w hw => le_trans (by omega) (singleton_weight_pos opt hmin (hP hw))) hv

lemma cost_contract {q j : ℕ} {A B K H P : Finset V} :
    extensionCost q j G A B (K ∪ H) P =
      extensionCost q j G A B K (H ∪ P) - extensionCost q j G A B K H := by
  unfold extensionCost
  rw [union_assoc]
  ring

lemma ec_modular (C P Q : Finset V) :
    ec G C (P ∪ Q) + ec G C (P ∩ Q) = ec G C P + ec G C Q := by
  simpa only [ec,sum_add_distrib] using
    (sum_congr rfl fun v (_hv : v ∈ C) => dg_union_add_dg_inter (G := G) P Q v)

/-- Cost-two owners may overlap in a column; their actual strict rows cannot share
the original convex-gap resource when the intersection has at most one column. -/
lemma rows_disjoint_from_gap {q j : ℕ} {A B K C P Q : Finset V}
    (hP : P ⊆ B \ K) (_hQ : Q ⊆ B \ K)
    (hthreshold : ∀ v ∈ A \ C, (3 : ℤ) ≤ -row q G B K v)
    (hI : #(P ∩ Q) ≤ 1)
    (hgap : extensionCost q j G A B K P + extensionCost q j G A B K Q -
      extensionCost q j G A B K (P ∪ Q) - extensionCost q j G A B K (P ∩ Q) ≤ 1) :
    Disjoint (residualRows q G A B K C P) (residualRows q G A B K C Q) := by
  apply Finset.disjoint_left.mpr
  intro v hvP hvQ
  have hvL := (mem_filter.mp hvP).1
  have hvA := (mem_sdiff.mp hvL).1
  have hvcan : v ∈ canonical q G A B (K ∪ P) ∩ canonical q G A B (K ∪ Q) :=
    mem_inter.mpr ⟨mem_filter.mpr ⟨hvA,(mem_filter.mp hvP).2⟩,
      mem_filter.mpr ⟨hvA,(mem_filter.mp hvQ).2⟩⟩
  have hi : (K ∪ P) ∩ (K ∪ Q) = K ∪ (P ∩ Q) := (union_inter_distrib_left K P Q).symm
  have hu : (K ∪ P) ∪ (K ∪ Q) = K ∪ (P ∪ Q) := by ext w; simp only [mem_union]; tauto
  have hb := bonus_shared (G := G) q hvcan
  rw [hi] at hb
  have hKI : Disjoint K (P ∩ Q) := disjoint_left.mpr fun w hwK hwI =>
    (mem_sdiff.mp (hP (mem_inter.mp hwI).1)).2 hwK
  have hd := dg_union_of_disjoint (G := G) hKI v
  have hdi := dg_le_card (G := G) (P ∩ Q) v
  have hthr := hthreshold v hvL
  have hbonus : (2 : ℤ) ≤ bonus q G B (K ∪ P) (K ∪ Q) v := by
    rw [hb]
    unfold row at hthr
    omega
  have hsum : bonus q G B (K ∪ P) (K ∪ Q) v ≤
      ∑ w ∈ A, bonus q G B (K ∪ P) (K ∪ Q) w :=
    single_le_sum (fun w _ => bonus_nonneg q B (K ∪ P) (K ∪ Q) w) hvA
  have hid := bonus_sum (G := G) q A B (K ∪ P) (K ∪ Q)
  rw [hi,hu] at hid
  unfold extensionCost thetaJ at hgap
  linarith

/-- At actual top height every optimizing core has exact imbalance and zero slack. -/
lemma top_shape {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1) :
    ((#C : ℤ)-#K) = (h : ℤ)-1 ∧
      coreDefect q G C K = (h : ℤ)*q-a₀ ∧
      deficiency (2*(q : ℤ)-2) G B (A\C) = 0 := by
  have hj := d.parameters.surplus_int
  have hp : 0 < thetaJ q j G A B K := by rw [htop]; omega
  have hs := d.positive_shape opt hK hl hp
  have hn := d.scar_nonneg (sdiff_subset : A\C ⊆ A)
  dsimp only at hs
  omega

lemma outside_regular {h q a₀ j : ℕ} {A B C : Finset V} (d : Data h q a₀ j G A B)
    (hz : deficiency (2*(q : ℤ)-2) G B (A\C) = 0)
    {v : V} (hv : v ∈ A\C) : (dg G B v : ℤ) = 2*(q : ℤ)-2 := by
  have hn : 0 ≤ 2*(q : ℤ)-2-dg G B v := by have hc := d.capA_int (mem_sdiff.mp hv).1; omega
  have hs := single_le_sum (f := fun w => 2*(q : ℤ)-2-dg G B w)
    (fun w hw => by have hc := d.capA_int (mem_sdiff.mp hw).1; omega) hv
  change 2*(q : ℤ)-2-dg G B v ≤ deficiency (2*(q : ℤ)-2) G B (A\C) at hs
  omega

lemma subset_scar_zero {h q a₀ j : ℕ} {A B C J : Finset V} (d : Data h q a₀ j G A B)
    (hz : deficiency (2*(q : ℤ)-2) G B (A\C) = 0) (hJ : J ⊆ A\C) :
    deficiency (2*(q : ℤ)-2) G B J = 0 := by
  have hlo := d.scar_nonneg (hJ.trans sdiff_subset)
  have hhi := deficiency_le_subset (2*(q : ℤ)-2) hJ
    (fun v hv => d.capA_int (mem_sdiff.mp hv).1)
  omega

lemma weight_zero_scar {h q a₀ j : ℕ} {A B K C P : Finset V} (d : Data h q a₀ j G A B)
    (hz : deficiency (2*(q : ℤ)-2) G B (A\C) = 0) :
    petalWeight q G A B K C P = (ec G C P : ℤ) + ec G (residualRows q G A B K C P) K := by
  have hs := subset_scar_zero d hz (filter_subset _ _ : residualRows q G A B K C P ⊆ A\C)
  change deficiency (2*(q : ℤ)-2) G B (residualRows q G A B K C P) = 0 at hs
  change (ec G C P : ℤ) + ec G (residualRows q G A B K C P) K +
    deficiency (2*(q : ℤ)-2) G B (residualRows q G A B K C P) = _
  rw [hs,add_zero]

/-- The original top outgoing and incoming resources share one pool. -/
lemma top_resources {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1) :
    (ec G C (B\K) : ℤ) = (2*(j : ℤ)+1)*((q : ℤ)-1) ∧
      (ec G (A\C) K : ℤ) ≤ (q : ℤ)+j+1-a₀ ∧
      (ec G C (B\K) : ℤ) + ec G (A\C) K ≤
        (h : ℤ)*q-a₀+(q : ℤ)*j-j := by
  have hs := top_shape d opt hK hl htop
  have he := opt.outward_edges (j := j) hK
  have hc := opt.cross_scar_identity (j := j)
  have hsplit := d.scar_split opt.subset
  have hj := d.parameters.surplus_int
  have hsig : 0 ≤ deficiency (2*(q : ℤ)-2) G A K :=
    deficiency_nonneg _ fun v hv => d.capB_int (hK hv)
  refine ⟨?_,?_,?_⟩ <;> nlinarith

/-- Top thresholds come from actual outside degree and incoming original units. -/
lemma top_threshold {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1) {v : V} (hv : v ∈ A\C) :
    (a₀ : ℤ)-j-3 ≤ -row q G B K v ∧ (3 : ℤ) ≤ -row q G B K v := by
  have hs := top_shape d opt hK hl htop
  have hd := outside_regular d hs.2.2 hv
  have hr := top_resources d opt hK hl htop
  have hi := dg_le_ec_left (G := G) hv (Y := K)
  have hj := d.parameters.surplus_int
  have ha := d.parameters.lower_int
  have hh := d.parameters.height_int
  unfold row
  omega

/-- Every nonempty strict-row residual of cost at most two has an eligible original
paired support. Its full original resource costs at least c minus that cost. -/
lemma big_charge {h q a₀ j : ℕ} {A B K C P : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1) (hP : P ⊆ B\K)
    (hc : extensionCost q j G A B K P ≤ 2)
    (hbig : (residualRows q G A B K C P).Nonempty) :
    (h : ℤ)*q-a₀-extensionCost q j G A B K P ≤ petalWeight q G A B K C P := by
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A\C := filter_subset _ _
  obtain ⟨v,hv⟩ := hbig
  have hvL := hJ hv
  have hthr := top_threshold d opt hK hl htop hvL
  have hpos := (mem_filter.mp hv).2
  rw [residual_row_add q hP v] at hpos
  have hd := dg_le_card (G := G) P v
  have hj := d.parameters.surplus_int
  have ha := d.parameters.lower_int
  have hh := d.parameters.height_int
  have hel : h ≤ #P + #J := by omega
  have hKpos : 0 < #K := by have hq := d.parameters.q_ge_height; omega
  have hpc := card_le_card hP
  have hkc := card_sdiff_add_card_eq_card hK
  have hjc := card_le_card (hJ.trans sdiff_subset)
  have hf := d.sparse J (hJ.trans sdiff_subset) P (hP.trans sdiff_subset) (by omega) (by omega)
  have hdef := twice_coreDefect (G := G) q J P
  have hr := petal_resource_identity (j := j) opt hP
  dsimp only at hr
  have hxp : 0 < thetaJ q j G A B (K∪P) := by
    unfold extensionCost at hc
    omega
  have hshape := d.positive_shape (expanded_optimizer opt hP)
    (union_subset hK (hP.trans sdiff_subset))
    (hl.trans (card_le_card subset_union_left)) hxp
  have htopshape := top_shape d opt hK hl htop
  have hCJ : Disjoint C J := disjoint_left.mpr fun w hwC hwJ => (mem_sdiff.mp (hJ hwJ)).2 hwC
  have hKP : Disjoint K P := disjoint_left.mpr fun w hwK hwP => (mem_sdiff.mp (hP hwP)).2 hwK
  have hcc := card_union_of_disjoint hCJ
  have hcp := card_union_of_disjoint hKP
  dsimp only at hshape
  have hku : ((#(C∪J) : ℤ)-#(K∪P)) ≤ (h : ℤ)-1 := hshape.2.2.2.1
  have hccz : (#(C∪J) : ℤ) = (#C : ℤ)+#J := by exact_mod_cast hcc
  have hcpz : (#(K∪P) : ℤ) = (#K : ℤ)+#P := by exact_mod_cast hcp
  have ht : (0 : ℤ) ≤ (#P : ℤ)-#J := by omega
  change coreDefect q G J P = petalWeight q G A B K C P +
    extensionCost q j G A B K P - ((#P : ℤ)-#J) at hr
  omega

/-- Overlap is paid only once in the original column pool; strict rows are disjoint. -/
lemma pair_pool {h q a₀ j : ℕ} {A B K C P Q : Finset V} (d : Data h q a₀ j G A B)
    (hz : deficiency (2*(q : ℤ)-2) G B (A\C) = 0)
    (hP : P ⊆ B\K) (hQ : Q ⊆ B\K)
    (hJ : Disjoint (residualRows q G A B K C P) (residualRows q G A B K C Q)) :
    petalWeight q G A B K C P + petalWeight q G A B K C Q ≤
      (ec G C (B\K) : ℤ)+ec G (A\C) K+ec G C (P∩Q) := by
  let JP := residualRows q G A B K C P
  let JQ := residualRows q G A B K C Q
  have hJP : JP ⊆ A\C := filter_subset _ _
  have hJQ : JQ ⊆ A\C := filter_subset _ _
  have hjadd := ec_union_left (G := G) hJ K
  have hjle : ec G (JP∪JQ) K ≤ ec G (A\C) K := by
    rw [ec_comm (G := G) (JP∪JQ) K,ec_comm (G := G) (A\C) K]
    exact ec_mono_right (G := G) K (union_subset hJP hJQ)
  have hmod := ec_modular (G := G) C P Q
  have hule := ec_mono_right (G := G) C (union_subset hP hQ)
  rw [weight_zero_scar d hz,weight_zero_scar d hz]
  change _ ≤ _ at hjle
  change ec G (JP∪JQ) K = ec G JP K+ec G JQ K at hjadd
  change (ec G C P : ℤ)+ec G JP K+((ec G C Q : ℤ)+ec G JQ K) ≤ _
  zify at hjadd hjle hmod hule
  linarith

/-- A large owner's charge and disjoint tiny columns use the SAME original pool. -/
lemma owner_plus_columns {h q a₀ j : ℕ} {A B K C P S : Finset V}
    (d : Data h q a₀ j G A B)
    (hz : deficiency (2*(q : ℤ)-2) G B (A\C) = 0)
    (hP : P ⊆ B\K) (hS : S ⊆ (B\K)\P) :
    petalWeight q G A B K C P+(ec G C S : ℤ) ≤
      (ec G C (B\K) : ℤ)+ec G (A\C) K := by
  have hdis : Disjoint P S := disjoint_left.mpr fun v hvP hvS => (mem_sdiff.mp (hS hvS)).2 hvP
  have hsub := union_subset hP (hS.trans sdiff_subset)
  have hadd := ec_union_right (G := G) hdis C
  have hle := ec_mono_right (G := G) C hsub
  have hJ : residualRows q G A B K C P ⊆ A\C := filter_subset _ _
  have hJle : ec G (residualRows q G A B K C P) K ≤ ec G (A\C) K := by
    rw [ec_comm (G := G) (residualRows q G A B K C P) K,ec_comm (G := G) (A\C) K]
    exact ec_mono_right (G := G) K hJ
  rw [weight_zero_scar d hz]
  zify at hadd hle hJle
  linarith

def tiny (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (B K C : Finset V) : Finset V :=
  (B\K).filter fun v => (q : ℤ)-dg G C v ≤ 2

lemma no_rows_subset_tiny {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B\K) (hJ : residualRows q G A B K C P = ∅)
    (hc : extensionCost q j G A B K P ≤ 2) : P ⊆ tiny q G B K C := by
  intro v hv
  exact mem_filter.mpr ⟨hP hv,(no_rows_point opt hmin hP hJ hv).trans hc⟩

omit [DecidableEq V] in
lemma outgoing_lower {q : ℕ} {C S : Finset V}
    (hw : ∀ v ∈ S, (q : ℤ)-2 ≤ dg G C v) :
    ((q : ℤ)-2)*#S ≤ (ec G C S : ℤ) := by
  rw [ec_comm,ec,Nat.cast_sum]
  calc
    _ = ∑ _v ∈ S, ((q : ℤ)-2) := by rw [sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum hw

lemma numeric {h q a₀ j : ℕ} (p : Parameters h q a₀ j) :
    (3 : ℤ) ≤ q ∧
    ((h : ℤ)*q-a₀+(q : ℤ)*j-j)+((q : ℤ)-1) < 2*((h : ℤ)*q-a₀-2) ∧
    ((h : ℤ)*q-a₀+(q : ℤ)*j-j) < 2*((h : ℤ)*q-a₀-1) ∧
    ((h : ℤ)*q-a₀+(q : ℤ)*j-j) < ((h : ℤ)*q-a₀-1)+((h : ℤ)*q-a₀-2) ∧
    (2*(j : ℤ)+1)*((q : ℤ)-1) < (2*(j : ℤ)+2)*((q : ℤ)-2) ∧
    ((h : ℤ)*q-a₀+(q : ℤ)*j-j)-((h : ℤ)*q-a₀-1) < ((j : ℤ)+1)*((q : ℤ)-2) ∧
    3*j+1 < q+1 ∧ 2*j ≤ 3*h := by
  have hn := p.numeric
  have hh := p.height_int
  have hj := p.surplus_int
  have ha := p.lower_int
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

lemma tiny_count {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1) : #(tiny q G B K C) ≤ 2*j+1 := by
  have hw := outgoing_lower (G := G) (q := q) (S := tiny q G B K C) (C := C)
    (fun v hv => by have hh := (mem_filter.mp hv).2; omega)
  have hm := ec_mono_right (G := G) C (filter_subset _ _ : tiny q G B K C ⊆ B\K)
  have hr := top_resources d opt hK hl htop
  have hn := numeric d.parameters
  by_contra! hbad
  have hc : (2*(j : ℤ)+2) ≤ #(tiny q G B K C) := by omega
  have hp := mul_le_mul_of_nonneg_left hc (show 0 ≤ (q : ℤ)-2 by omega)
  have hE := hn.2.2.2.2.1
  change ec G C (tiny q G B K C) ≤ ec G C (B\K) at hm
  have he := hr.1
  zify at hm
  linarith

lemma tiny_outside_big_one {h q a₀ j : ℕ} {A B K C H : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1)
    (hH : MaxPetal q j G A B K 1 H)
    (hbig : (residualRows q G A B K C H).Nonempty) : #(tiny q G B K C\H) ≤ j := by
  have hz := (top_shape d opt hK hl htop).2.2
  have hs := owner_plus_columns d hz hH.1
    (sdiff_subset_sdiff_left H (filter_subset _ _) : tiny q G B K C\H ⊆ (B\K)\H)
  have hw := outgoing_lower (G := G) (q := q) (C := C) (S := tiny q G B K C\H)
    (fun v hv => by have hh := (mem_filter.mp (mem_sdiff.mp hv).1).2; omega)
  have hg := big_charge d opt hK hl htop hH.1 (by rw [hH.2.2.1]; omega) hbig
  rw [hH.2.2.1] at hg
  have hr := (top_resources d opt hK hl htop).2.2
  have hn := numeric d.parameters
  by_contra! hbad
  have hc : (j : ℤ)+1 ≤ #(tiny q G B K C\H) := by omega
  have hp := mul_le_mul_of_nonneg_left hc (show 0 ≤ (q : ℤ)-2 by omega)
  have hmargin := hn.2.2.2.2.2.1
  linarith

lemma Owner.union_cost {q j : ℕ} {A B K P Q : Finset V}
    (hP : Owner q j G A B K P) (hQ : Owner q j G A B K Q) (hne : P ≠ Q) :
    3 ≤ extensionCost q j G A B K (P∪Q) := by
  have hneU : P ≠ P∪Q := by
    intro he
    exact hQ.not_subset hP hne.symm (by simpa only [←he] using (subset_union_right : Q ⊆ P∪Q))
  exact hP.2.2.2 (P∪Q) (union_subset hP.1 hQ.1) subset_union_left hneU

/-- With no big cost-one set, actual cost-two owner intersections have at most
one column, carrying at most q-1 original outgoing units. -/
lemma owner_intersection {q j : ℕ} {A B K C P Q : Finset V}
    (opt : Optimizer q G A B K C)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hno : ∀ P ⊆ B\K, extensionCost q j G A B K P = 1 → residualRows q G A B K C P = ∅)
    (hP : Owner q j G A B K P) (hQ : Owner q j G A B K Q) (hne : P ≠ Q) :
    #(P∩Q) ≤ 1 ∧ (ec G C (P∩Q) : ℤ) ≤ (q : ℤ)-1 := by
  have hi : P∩Q ⊆ B\K := inter_subset_left.trans hP.1
  by_cases he : P∩Q = ∅
  · have hw := singleton_weight_pos opt hmin (hP.1 (hP.2.1.choose_spec))
    have hq : (1 : ℤ) ≤ q := by omega
    constructor
    · simp [he]
    · simpa [he,ec,dg] using (show (0 : ℤ) ≤ (q : ℤ)-1 by omega)
  · have hiN := nonempty_iff_ne_empty.mpr he
    have hI := hmin (P∩Q) hi hiN
    have hU := hP.union_cost hQ hne
    have hS := extensionCost_submod (G := G) q j A B K P Q
    have hcp := hP.2.2.1
    have hcq := hQ.2.2.1
    have hone : extensionCost q j G A B K (P∩Q) = 1 := by omega
    have hJ := hno (P∩Q) hi hone
    have hcard := no_rows_card opt hmin hi hJ
    have hlin := extensionCost_linear_of_no_rows (j := j) opt hi hJ
    have hpos : 0 < #(P∩Q) := card_pos.mpr hiN
    have hceq : #(P∩Q) = 1 := by omega
    rw [hone,hceq] at hlin
    norm_num at hlin
    exact ⟨by omega,by omega⟩

lemma big_owners_unique {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hno : ∀ P ⊆ B\K, extensionCost q j G A B K P = 1 → residualRows q G A B K C P = ∅)
    {P Q : Finset V} (hP : Owner q j G A B K P) (hQ : Owner q j G A B K Q)
    (hpbig : (residualRows q G A B K C P).Nonempty)
    (hqbig : (residualRows q G A B K C Q).Nonempty) : P = Q := by
  by_contra hne
  have hI := owner_intersection opt hmin hno hP hQ hne
  have hU := hP.union_cost hQ hne
  have hIn := cost_nonneg (P := P∩Q) hmin (inter_subset_left.trans hP.1)
  have hcp := hP.2.2.1
  have hcq := hQ.2.2.1
  have hJ := rows_disjoint_from_gap (j := j) hP.1 hQ.1
    (fun v hv => (top_threshold d opt hK hl htop hv).2) hI.1 (by omega)
  have hpool := pair_pool d (top_shape d opt hK hl htop).2.2 hP.1 hQ.1 hJ
  have hpw := big_charge d opt hK hl htop hP.1 hcp hpbig
  have hqw := big_charge d opt hK hl htop hQ.1 hcq hqbig
  have hr := (top_resources d opt hK hl htop).2.2
  have hn := (numeric d.parameters).2.1
  linarith

/-- Distinct actual cost-one owners with strict rows would exhaust more than the
entire original pool. -/
lemma big_one_unique {h q a₀ j : ℕ} {A B K C : Finset V} (d : Data h q a₀ j G A B)
    (opt : Optimizer q G A B K C) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    {P Q : Finset V} (hP : MaxPetal q j G A B K 1 P) (hQ : MaxPetal q j G A B K 1 Q)
    (hpbig : (residualRows q G A B K C P).Nonempty)
    (hqbig : (residualRows q G A B K C Q).Nonempty) : P = Q := by
  by_contra hne
  have hd := hP.disjoint hmin hQ hne
  have hj := hP.rows_disjoint hmin
    (fun v hv => le_trans (by norm_num) (top_threshold d opt hK hl htop hv).2) hQ hne
  have hs := pair_pool d (top_shape d opt hK hl htop).2.2 hP.1 hQ.1 hj
  have hi : P∩Q = ∅ := disjoint_iff_inter_eq_empty.mp hd
  have hei : ec G C (P∩Q) = 0 := by simp [hi,ec,dg]
  rw [hei,Nat.cast_zero,add_zero] at hs
  have hpw := big_charge d opt hK hl htop hP.1 (by rw [hP.2.2.1]; omega) hpbig
  have hqw := big_charge d opt hK hl htop hQ.1 (by rw [hQ.2.2.1]; omega) hqbig
  rw [hP.2.2.1] at hpw
  rw [hQ.2.2.1] at hqw
  have hr := (top_resources d opt hK hl htop).2.2
  have hn := (numeric d.parameters).2.2.1
  linarith

/-- Every actual cost-at-most-two owner with strict rows contains the unique
large cost-one owner, whenever that owner exists. -/
lemma owner_contains_big_one {h q a₀ j : ℕ} {A B K C H P : Finset V}
    (d : Data h q a₀ j G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hH : MaxPetal q j G A B K 1 H)
    (hhbig : (residualRows q G A B K C H).Nonempty)
    (hP : Owner q j G A B K P)
    (hpbig : (residualRows q G A B K C P).Nonempty) : H ⊆ P := by
  by_contra hnsub
  have hneU : P ≠ P∪H := by
    intro he
    exact hnsub (by simpa only [←he] using (subset_union_right : H ⊆ P∪H))
  have hu := hP.2.2.2 (P∪H) (union_subset hP.1 hH.1) subset_union_left hneU
  have hs := extensionCost_submod (G := G) q j A B K P H
  have hcp := hP.2.2.1
  rw [hH.2.2.1] at hs
  have hi : P∩H = ∅ := by
    by_contra hneI
    have hm := hmin (P∩H) (inter_subset_left.trans hP.1) (nonempty_iff_ne_empty.mpr hneI)
    omega
  have hch := hH.2.2.1
  have hIn := cost_nonneg (P := P∩H) hmin (inter_subset_left.trans hP.1)
  have hJ := rows_disjoint_from_gap (j := j) hP.1 hH.1
    (fun v hv => (top_threshold d opt hK hl htop hv).2)
    (by simp [hi]) (by omega)
  have hpool := pair_pool d (top_shape d opt hK hl htop).2.2 hP.1 hH.1 hJ
  have hei : ec G C (P∩H) = 0 := by simp [hi,ec,dg]
  rw [hei,Nat.cast_zero,add_zero] at hpool
  have hpw := big_charge d opt hK hl htop hP.1 hcp hpbig
  have hhw := big_charge d opt hK hl htop hH.1 (by rw [hH.2.2.1]; omega) hhbig
  rw [hH.2.2.1] at hhw
  have hr := (top_resources d opt hK hl htop).2.2
  have hn := (numeric d.parameters).2.2.2.1
  linarith

/-- In the absence of a large cost-one owner, at most one cost-two owner is
large; the other original columns are all charged to the same tiny pool. -/
lemma no_big_one_escape {h q a₀ j : ℕ} {A B K C ban : Finset V}
    (d : Data h q a₀ j G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hno : ∀ P ⊆ B\K, extensionCost q j G A B K P = 1 → residualRows q G A B K C P = ∅)
    (_hban : ban ⊆ B\K) (hbanc : #ban ≤ j) :
    ∃ z ∈ B\K, z ∉ ban ∧ ∀ P ⊆ B\K, z ∈ P → 3 ≤ extensionCost q j G A B K P := by
  have htiny := tiny_count d opt hK hl htop
  have hn := numeric d.parameters
  have hcard : #(tiny q G B K C∪ban) ≤ 3*j+1 := by
    have hu := card_union_le (tiny q G B K C) ban
    omega
  have escape : ∃ z ∈ B\K, z ∉ ban ∧ ∀ P, Owner q j G A B K P → z ∉ P := by
    by_cases hex : ∃ P, Owner q j G A B K P ∧ (residualRows q G A B K C P).Nonempty
    · obtain ⟨P,hP,hbig⟩ := hex
      have hpos : 0 < thetaJ q j G A B (K∪P) := by
        have hc := hP.2.2.1
        have hj := d.parameters.surplus_int
        have hh := d.parameters.height_int
        unfold extensionCost at hc
        omega
      have hcomp := d.positive_complement (union_subset hK (hP.1.trans sdiff_subset)) hpos
      have heq : B\(K∪P) = (B\K)\P := by
        ext v
        simp only [mem_sdiff,mem_union]
        tauto
      rw [heq] at hcomp
      have hc : #(tiny q G B K C∪ban) < #((B\K)\P) := by omega
      obtain ⟨z,hz,hzE⟩ := AllHTopTwo.PetalEscape.exists_outside ((B\K)\P) (tiny q G B K C∪ban) hc
      refine ⟨z,(mem_sdiff.mp hz).1,fun hb => hzE (mem_union_right _ hb),?_⟩
      intro Q hQ hzQ
      by_cases hQbig : (residualRows q G A B K C Q).Nonempty
      · have he := big_owners_unique d opt hK hl htop hmin hno hQ hP hQbig hbig
        exact (mem_sdiff.mp hz).2 (he ▸ hzQ)
      · have he := not_nonempty_iff_eq_empty.mp hQbig
        have hs := no_rows_subset_tiny opt hmin hQ.1 he hQ.2.2.1
        exact hzE (mem_union_left _ (hs hzQ))
    · have hpos : 0 < thetaJ q j G A B K := by
        have hj := d.parameters.surplus_int
        have hh := d.parameters.height_int
        omega
      have hcomp := d.positive_complement hK hpos
      have hc : #(tiny q G B K C∪ban) < #(B\K) := by omega
      obtain ⟨z,hz,hzE⟩ := AllHTopTwo.PetalEscape.exists_outside (B\K) (tiny q G B K C∪ban) hc
      refine ⟨z,hz,fun hb => hzE (mem_union_right _ hb),?_⟩
      intro Q hQ hzQ
      have hQbig : ¬(residualRows q G A B K C Q).Nonempty := fun hb => hex ⟨Q,hQ,hb⟩
      have he := not_nonempty_iff_eq_empty.mp hQbig
      have hs := no_rows_subset_tiny opt hmin hQ.1 he hQ.2.2.1
      exact hzE (mem_union_left _ (hs hzQ))
  obtain ⟨z,hz,hzb,hzO⟩ := escape
  refine ⟨z,hz,hzb,?_⟩
  intro P hP hzP
  by_contra! hc
  obtain ⟨Q,hPQ,hQ⟩ := exists_owner (G := G) (q := q) (j := j) (A := A) hP ⟨z,hzP⟩ (by omega)
  exact hzO Q hQ (hPQ hzP)

/-- Contract the actual large cost-one owner. The remaining original tiny
columns and the prescribed ban fit the proved local two-unit escape budget. -/
lemma big_one_escape {h q a₀ j : ℕ} {A B K C H ban : Finset V}
    (d : Data h q a₀ j G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (htop : thetaJ q j G A B K = 2*(j : ℤ)+1)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hH : MaxPetal q j G A B K 1 H)
    (hbig : (residualRows q G A B K C H).Nonempty)
    (hban : ban ⊆ B\K) (hbanc : #ban ≤ j) :
    ∃ z ∈ B\K, z ∉ ban ∧ ∀ P ⊆ B\K, z ∈ P → 3 ≤ extensionCost q j G A B K P := by
  let newban := (ban\H) ∪ (tiny q G B K C\H)
  have hnewban : newban ⊆ B\(K∪H) := by
    intro v hv
    have hh : v ∈ B\K ∧ v ∉ H := by
      rcases mem_union.mp hv with hv | hv
      · exact ⟨hban (mem_sdiff.mp hv).1,(mem_sdiff.mp hv).2⟩
      · exact ⟨(mem_filter.mp (mem_sdiff.mp hv).1).1,(mem_sdiff.mp hv).2⟩
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hh.1).1,fun hu =>
      (mem_union.mp hu).elim (mem_sdiff.mp hh.1).2 hh.2⟩
  have htiny := tiny_outside_big_one d opt hK hl htop hH hbig
  have hn := numeric d.parameters
  have hnewcard : #newban ≤ 3*h := by
    have hu := card_union_le (ban\H) (tiny q G B K C\H)
    have hb := card_le_card (sdiff_subset : ban\H ⊆ ban)
    change #((ban\H) ∪ (tiny q G B K C\H)) ≤ 3*h
    omega
  have hK1 : K∪H ⊆ B := union_subset hK (hH.1.trans sdiff_subset)
  have hl1 : q-1 ≤ #(K∪H) := hl.trans (card_le_card subset_union_left)
  have ht1 : thetaJ q j G A B (K∪H) = thetaJ q j G A B K-1 := by
    have hc := hH.2.2.1
    unfold extensionCost at hc
    omega
  have hp1 : 2 ≤ thetaJ q j G A B (K∪H) := by
    have hj := d.parameters.surplus_int
    have hh := d.parameters.height_int
    omega
  have hstrict1 : ∀ T ⊆ B, K∪H ⊆ T → K∪H ≠ T →
      thetaJ q j G A B T ≤ thetaJ q j G A B (K∪H)-1 := by
    intro T hT hKT hne
    have hs := MaxPetal.strict_theta hK hH T hT hKT hne
    omega
  obtain ⟨z,hz,hzb,hzgood⟩ := petal_escape (G := G) h q a₀ j A B (K∪H) newban d
    hK1 hl1 hp1 hstrict1 hnewban hnewcard
  have hzBH := mem_sdiff.mp hz
  have hzK : z ∉ K := fun hk => hzBH.2 (mem_union_left _ hk)
  have hzH : z ∉ H := fun hh => hzBH.2 (mem_union_right _ hh)
  have hzR : z ∈ B\K := mem_sdiff.mpr ⟨hzBH.1,hzK⟩
  have hzban : z ∉ ban := fun hb => hzb (mem_union_left _ (mem_sdiff.mpr ⟨hb,hzH⟩))
  have hztiny : z ∉ tiny q G B K C := fun hh => hzb (mem_union_right _ (mem_sdiff.mpr ⟨hh,hzH⟩))
  refine ⟨z,hzR,hzban,?_⟩
  intro P hP hzP
  by_contra! hc
  obtain ⟨Q,hPQ,hQ⟩ := exists_owner (G := G) (q := q) (j := j) (A := A) hP ⟨z,hzP⟩ (by omega)
  have hzQ := hPQ hzP
  by_cases hQbig : (residualRows q G A B K C Q).Nonempty
  · have hHQ := owner_contains_big_one d opt hK hl htop hmin hH hbig hQ hQbig
    have hs : Q\H ⊆ B\(K∪H) := by
      intro v hv
      have hvR := mem_sdiff.mp (hQ.1 (mem_sdiff.mp hv).1)
      exact mem_sdiff.mpr ⟨hvR.1,fun hu => (mem_union.mp hu).elim hvR.2 (mem_sdiff.mp hv).2⟩
    have hzQH : z ∈ Q\H := mem_sdiff.mpr ⟨hzQ,hzH⟩
    have hg := hzgood (Q\H) hs hzQH
    have he := cost_contract (G := G) (q := q) (j := j) (A := A) (B := B) (K := K) (H := H) (P := Q\H)
    rw [union_sdiff_of_subset hHQ,hH.2.2.1] at he
    have hqc := hQ.2.2.1
    omega
  · have he := not_nonempty_iff_eq_empty.mp hQbig
    exact hztiny ((no_rows_subset_tiny opt hmin hQ.1 he hQ.2.2.1) hzQ)

end TopEscape

/-- Exact highest-height three-unit escape, derived only from original Data. -/
theorem top_escape : TopEscapeClaim (G := G) := by
  intro h q a₀ j A B K ban d hK hl htop hstrict hban hbanc
  let C := weakCore q G A B K
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P :=
    strict_extension_cost_min hK hstrict
  by_cases hex : ∃ H, MaxPetal q j G A B K 1 H ∧ (residualRows q G A B K C H).Nonempty
  · obtain ⟨H,hH,hbig⟩ := hex
    exact TopEscape.big_one_escape d opt hK hl htop hmin hH hbig hban hbanc
  · have hno : ∀ P ⊆ B\K, extensionCost q j G A B K P = 1 → residualRows q G A B K C P = ∅ := by
      intro P hP hc
      by_contra hneJ
      have hne : P.Nonempty := by
        by_contra hne
        have he := not_nonempty_iff_eq_empty.mp hne
        simp [he,extensionCost] at hc
      obtain ⟨Q,hPQ,hQ⟩ := exists_max_petal_extension hmin hP hne hc
      have hbig := (nonempty_iff_ne_empty.mpr hneJ).mono (TopEscape.residualRows_mono hPQ)
      exact hex ⟨Q,hQ,hbig⟩
    exact TopEscape.no_big_one_escape d opt hK hl htop hmin hno hban hbanc

end Erdos585.AllHNextNonstrict
