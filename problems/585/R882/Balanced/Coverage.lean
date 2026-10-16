import R882.Balanced.Hazard
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R882.Balanced
open QB4 B5 H3Unequal Omit1PrefixR691 GeneralSelectorR783
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {h epsilon q : ℕ} {F : ℤ}
  {A B M P S T : Finset V}
variable (host : Host h epsilon q F G A B)
include host

lemma band_bounds (band : g q G A B S ≤ (q : ℤ)-1) :
    0 ≤ k A B S ∧ k A B S ≤ h := by
  have scars := Erdos585.R882.Balanced.scar_bounds host S
  have ident := Erdos585.R882.Balanced.cut_identity (q := q) (G := G) (A := A) (B := B) S
  have capf := Erdos585.R882.Balanced.cap_potential host S
  have num := Erdos585.R882.Balanced.numeric host
  have hq := Erdos585.R882.Balanced.q_large host
  constructor
  · by_contra! hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ q by positivity)
      (show k A B S+1 ≤ 0 by omega)
    have he : 0 ≤ (ec G (A∩S) (B\S) : ℤ) := by positivity
    unfold g at band
    nlinarith only [band,hm,he]
  · by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ)-2 by omega)
      (show 0 ≤ k A B S-((h : ℤ)+1) by omega)
    have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
    nlinarith only [hm,ident,capf,scars.2.1,band,num.2.2.2.2,hh]

lemma localization_numeric : (q : ℤ)+2*(h : ℤ)-5+2*(epsilon : ℤ) < F := by
  have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
  have he : (0 : ℤ) ≤ epsilon := by positivity
  have hq := reserve host
  have physical := host.physical
  have prod := mul_nonneg (show (0 : ℤ) ≤ (h : ℤ)-2 by omega)
    (show 0 ≤ (q : ℤ) by positivity)
  nlinarith [sq_nonneg (h : ℤ)]

/-- Every original band cut is tiny on one of the two literal differences. -/
theorem band_localization (neg : g q G A B M < 0)
    (band : g q G A B S ≤ (q : ℤ)-1) : #(M\S)<h ∨ #(S\M)<h := by
  by_contra! hn
  have id := Erdos585.R882.Balanced.pair_identity host M S
  have bm := Erdos585.R882.Balanced.negative_bounds host neg
  have bs := band_bounds host band
  have si := (Erdos585.R882.Balanced.scar_bounds host (M∩S)).2.2.1
  have so := (Erdos585.R882.Balanced.scar_bounds host (univ\(M∪S))).1
  have e0 : (0 : ℤ) ≤ ec G (M∩S) (univ\(M∪S)) := by positivity
  have proper1 := Erdos585.R882.Balanced.proper_of_subset_negative host neg
    (sdiff_subset : M\S ⊆ M)
  have el := Erdos585.R882.Balanced.negative_eligible host neg
  have sub : S\M ⊆ univ\M := sdiff_subset_sdiff_left M (subset_univ S)
  have proper2 := (card_le_card sub).trans_lt el.2.2.2
  have f1 := Erdos585.R882.Balanced.floor host (M\S) hn.1 proper1
  have f2 := Erdos585.R882.Balanced.floor host (S\M) hn.2 proper2
  have gap := localization_numeric host
  omega
/-- Disjoint original supports pay their full unoriented cross incidence once. -/
lemma g_disjoint {S T : Finset V} (hd : Disjoint S T) :
    g q G A B (S∪T)=g q G A B S+g q G A B T-(ec G S T : ℤ) := by
  have fp := Erdos585.R882.Balanced.f_disjoint host hd
  have cs := Erdos585.R882.Balanced.cut_identity (q := q) (G := G) (A := A) (B := B) S
  have ct := Erdos585.R882.Balanced.cut_identity (q := q) (G := G) (A := A) (B := B) T
  have cu := Erdos585.R882.Balanced.cut_identity (q := q) (G := G) (A := A) (B := B) (S∪T)
  have dA : Disjoint (A∩S) (A∩T) := hd.mono inter_subset_right inter_subset_right
  have dB : Disjoint (B∩S) (B∩T) := hd.mono inter_subset_right inter_subset_right
  have sa := sum_union dA (f := fun v => 2*(q : ℤ)-2-(dg G B v : ℤ))
  have ca := card_union_of_disjoint dA
  have cb := card_union_of_disjoint dB
  rw [← inter_union_distrib_left] at sa ca cb
  zify at ca cb
  unfold sA deficiency k at cs ct cu
  omega

/-- A singleton on B has slack q in the original graph. -/
lemma right_singleton {b : V} (hb : b ∈ B) : g q G A B {b}=(q : ℤ) := by
  have ba : b ∉ A := disjoint_right.mp host.disjoint hb
  have ae : A∩{b}=∅ := by ext v; simp only [mem_inter,mem_singleton,notMem_empty]; aesop
  have be : B∩{b}={b} := inter_eq_right.mpr (singleton_subset_iff.mpr hb)
  simp [g,k,ae,be,ec]

/-- Exact original insertion residual, with no lost orientation of the Q,H incidence. -/
lemma insertion_identity {b : V} (hb : b ∈ B) (bE : b ∈ T)
    (disjoint : Disjoint M T) (hP : P ⊆ M) :
    g q G A B (P∪T)=g q G A B P+(q : ℤ)-(dg G P b : ℤ)+
      (g q G A B (M∪(T.erase b))-g q G A B M+
        ec G (M\P) (T.erase b)-(dg G (T.erase b) b : ℤ)) := by
  have dp : Disjoint P T := disjoint.mono_left hP
  have ep := g_disjoint host dp
  have de : Disjoint M (T.erase b) := disjoint.mono_right (erase_subset b T)
  have em := g_disjoint host de
  have dv : Disjoint (T.erase b) {b} := by simp
  have ee := g_disjoint host dv
  have u : T.erase b∪{b}=T := by
    ext v; simp only [mem_union,mem_erase,mem_singleton]
    by_cases he : v=b <;> simp_all
  rw [u,right_singleton host hb] at ee
  have split := ec_sdiff_add_left (G := G) hP (T.erase b)
  have et := ec_union_right (G := G) (Z := P) dv
  rw [u] at et
  have e1 : ec G (T.erase b) {b}=dg G (T.erase b) b := by rw [ec_comm]; simp [ec]
  have e2 : ec G P {b}=dg G P b := by rw [ec_comm]; simp [ec]
  rw [e1] at ee
  rw [e2] at et
  zify at split et
  omega

omit host in
/-- Tiny-cell scalar guard, valid exactly throughout the h=3,4 range. -/
lemma tiny_mixed_nonnegative (small_height : h=3 ∨ h=4)
    {x y : ℕ} (tiny : x+y+1<h) : 0 ≤ (y : ℤ)*(1-(x : ℤ)) := by
  have types : x ≤ 1 ∨ y=0 := by rcases small_height with rfl|rfl <;> omega
  rcases types with hx|rfl
  · apply mul_nonneg (by positivity)
    omega
  · simp

/-- Every nonempty outside insertion strictly raises a greatest global minimizer. -/
lemma greatest_insertion_positive
    (lower : ∀ S : Finset V, g q G A B M ≤ g q G A B S)
    (greatest : ∀ S : Finset V, g q G A B S=g q G A B M → S ⊆ M)
    (disjoint : Disjoint M T) (nonempty : T.Nonempty) :
    g q G A B M+1 ≤ g q G A B (M∪T) := by
  have lo := lower (M∪T)
  by_contra! hn
  have eq : g q G A B (M∪T)=g q G A B M := by omega
  have sub := (subset_union_right : T ⊆ M∪T).trans (greatest _ eq)
  obtain ⟨v,hv⟩ := nonempty
  exact disjoint_left.mp disjoint (sub hv) hv

/-- Additions from A have no internal-edge tax. -/
lemma all_left_insertion (T : Finset V) (subA : T ⊆ A) (disjoint : Disjoint M T) :
    g q G A B (M∪T)-g q G A B M =
      (ec G T (B\M) : ℤ)-(q : ℤ)*#T := by
  have bt : B∩T=∅ := by
    apply eq_empty_of_forall_notMem
    intro v hv
    exact disjoint_left.mp host.disjoint (subA (mem_inter.mp hv).2) (mem_inter.mp hv).1
  have au : A∩(M∪T)=(A∩M)∪T := by rw [inter_union_distrib_left,inter_eq_right.mpr subA]
  have bu : B∩(M∪T)=B∩M := by rw [inter_union_distrib_left,bt,union_empty]
  have bout : B\(M∪T)=B\M := by
    ext v; simp only [mem_sdiff,mem_union]
    constructor
    · tauto
    · rintro ⟨hb,hm⟩
      exact ⟨hb,fun hv => hv.elim hm (fun ht => disjoint_left.mp host.disjoint (subA ht) hb)⟩
  have dd : Disjoint (A∩M) T := disjoint.mono_left inter_subset_right
  have ee := ec_union_left (G := G) (Z := B\M) dd
  have cc := card_union_of_disjoint dd
  zify at ee cc
  unfold g k
  rw [au,bu,bout]
  nlinarith

lemma all_left_insertion_lower (subA : T ⊆ A) (disjoint : Disjoint M T)
    (lower : ∀ S : Finset V, g q G A B M ≤ g q G A B S)
    (greatest : ∀ S : Finset V, g q G A B S=g q G A B M → S ⊆ M) :
    (#T : ℤ) ≤ g q G A B (M∪T)-g q G A B M := by
  have id := all_left_insertion host T subA disjoint
  have every : ∀ v ∈ T, (q : ℤ)+1 ≤ dg G (B\M) v := by
    intro v hv
    have dd : Disjoint M {v} := disjoint.mono_right (singleton_subset_iff.mpr hv)
    have pos := greatest_insertion_positive host lower greatest dd (singleton_nonempty v)
    have sing := all_left_insertion host {v} (singleton_subset_iff.mpr (subA hv)) dd
    simp only [card_singleton,ec,sum_singleton] at sing
    omega
  have bound : ((q : ℤ)+1)*#T ≤ (ec G T (B\M) : ℤ) := by
    rw [ec,Nat.cast_sum]
    calc
      _ = ∑ _v ∈ T, ((q : ℤ)+1) := by simp only [sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum every
  nlinarith

/-- The literal omitted anchor part is eligible for its original strict floor.
The retained part's boundary is then charged with all floor excess retained. -/
theorem original_floor_tiny_boundary (neg : g q G A B M < 0)
    {a b : V} (ha : a ∈ A∩M) (common : CommonLeft q G A B a)
    (lightA : dg G (B\M) a ≤ 3*h-4)
    (hb : b ∈ B) (outside : b ∉ M) (lightB : dg G (A∩M) b ≤ 3*h-4)
    (avoid : a ∉ S) (inside : b ∈ S)
    (lower : ∀ W : Finset V, g q G A B M ≤ g q G A B W)
    (tiny : #(S\M)<h) (band : g q G A B S ≤ (q : ℤ)-1) :
    0 ≤ g q G A B (S∩M) ∧ g q G A B (S∩M) ≤ 4*(h : ℤ)-7 ∧
    h ≤ #(M\(S∩M)) ∧ (ec G (S∩M) (univ\M) : ℤ) ≤ 6*(h : ℤ)-10+(epsilon : ℤ) := by
  let P := S∩M
  let E := S\M
  have bE : b ∈ E := mem_sdiff.mpr ⟨inside,outside⟩
  have disj : Disjoint M E := disjoint_sdiff_self_right
  have sub : P ⊆ M := inter_subset_right
  have av : a ∉ P := fun hv => avoid (mem_inter.mp hv).1
  have gp0 := avoiding_nonnegative common av
  have id := insertion_identity host hb bE disj sub
  have union : P∪E=S := by
    ext v; simp only [P,E,mem_union,mem_inter,mem_sdiff]; tauto
  rw [union] at id
  have lo := lower (M∪E.erase b)
  have nonneg : (0 : ℤ) ≤ ec G (M\P) (E.erase b) := by positivity
  have dt := dg_le_card (G := G) (E.erase b) b
  have card := card_erase_of_mem bE
  have dp : dg G P b ≤ 3*h-4 := by
    have deg := Erdos585.R882.Balanced.original_left_degree (Erdos585.R882.Balanced.swap host) M hb
    have mono := dg_mono (G := G) sub b
    omega
  have hh := host.height
  have upper : g q G A B P ≤ 4*(h : ℤ)-7 := by
    change #E<h at tiny
    omega
  have eligible : h ≤ #(M\P) := by
    by_contra! small
    have low := cotiny_value_lower host neg ha lightA sub av (by omega)
    have hq := reserve host
    have he : (0 : ℤ) ≤ epsilon := by positivity
    have cross := mul_nonneg (show (0 : ℤ) ≤ h by omega) he
    have hhZ : (6 : ℤ) ≤ h := by exact_mod_cast hh
    nlinarith
  have boundary := outer_boundary_bound host neg sub eligible
  have qband : g q G A B P ≤ (q : ℤ)-1 := by
    have hq := reserve host
    have he : (0 : ℤ) ≤ epsilon := by positivity
    have cross := mul_nonneg (show (0 : ℤ) ≤ h by omega) he
    have hhZ : (6 : ℤ) ≤ h := by exact_mod_cast hh
    nlinarith
  have kp := (band_bounds host qband).2
  change 0 ≤ g q G A B P ∧ g q G A B P ≤ 4*(h : ℤ)-7 ∧
    h ≤ #(M\P) ∧ (ec G P (univ\M) : ℤ) ≤ 6*(h : ℤ)-10+(epsilon : ℤ)
  exact ⟨gp0,upper,eligible,by omega⟩

/-- Inserting original B vertices has the literal degree tax into the retained A part. -/
lemma all_right_insertion (T : Finset V) (subB : T ⊆ B) (disjoint : Disjoint P T) :
    g q G A B (P∪T)-g q G A B P =
      (q : ℤ)*#T-(ec G (A∩P) T : ℤ) := by
  have aempty : A∩T=∅ := by
    apply eq_empty_of_forall_notMem
    intro v hv
    exact disjoint_left.mp host.disjoint (mem_inter.mp hv).1 (subB (mem_inter.mp hv).2)
  have au : A∩(P∪T)=A∩P := by rw [inter_union_distrib_left,aempty,union_empty]
  have bu : B∩(P∪T)=(B∩P)∪T := by rw [inter_union_distrib_left,inter_eq_right.mpr subB]
  have bout : B\P=(B\(P∪T))∪T := by
    ext v
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨bv,np⟩
      by_cases tv : v ∈ T
      · exact Or.inr tv
      · exact Or.inl ⟨bv,by tauto⟩
    · rintro (⟨bv,npt⟩|tv)
      · exact ⟨bv,by tauto⟩
      · exact ⟨subB tv,fun pv => disjoint_left.mp disjoint pv tv⟩
  have dd : Disjoint (B\(P∪T)) T := by
    apply Finset.disjoint_left.mpr
    intro v hv ht
    exact (mem_sdiff.mp hv).2 (mem_union_right _ ht)
  have ee := ec_union_right (G := G) (Z := A∩P) dd
  rw [← bout] at ee
  have db : Disjoint (B∩P) T := disjoint.mono_left inter_subset_right
  have cc := card_union_of_disjoint db
  zify at ee cc
  unfold g k
  rw [au,bu]
  nlinarith

/-- Submodularity transports the tax-free left insertion lower bound to every retained part. -/
lemma left_insertion_retained (sub : P ⊆ M) (subA : T ⊆ A) (disjoint : Disjoint M T)
    (lower : ∀ W : Finset V, g q G A B M ≤ g q G A B W)
    (greatest : ∀ W : Finset V, g q G A B W=g q G A B M → W ⊆ M) :
    (#T : ℤ) ≤ g q G A B (P∪T)-g q G A B P := by
  have lo := all_left_insertion_lower host subA disjoint lower greatest
  have sm := g_submodular (q := q) (G := G) (A := A) (B := B) M (P∪T)
  have un : M∪(P∪T)=M∪T := by ext v; simp only [mem_union]; constructor <;> aesop
  have inter : M∩(P∪T)=P := by
    ext v; simp only [mem_inter,mem_union]
    constructor
    · rintro ⟨mv,pv|tv⟩
      · exact pv
      · exact False.elim (disjoint_left.mp disjoint mv tv)
    · intro pv; exact ⟨sub pv,Or.inl pv⟩
  rw [un,inter] at sm
  omega


/-- The full original boundary payment covers every mixed tiny insertion. -/
lemma retained_insertion_payment {b : V} (hb : b ∈ B) (sub : P ⊆ M)
    (disjoint : Disjoint M T) (tiny : #T ≤ h-2)
    (boundary : (ec G P (univ\M) : ℤ) ≤ 6*(h : ℤ)-10+(epsilon : ℤ))
    (lower : ∀ W : Finset V, g q G A B M ≤ g q G A B W)
    (greatest : ∀ W : Finset V, g q G A B W=g q G A B M → W ⊆ M) :
    (dg G T b : ℤ) ≤ g q G A B (P∪T)-g q G A B P := by
  let X := A∩T
  let Y := B∩T
  have union : X∪Y=T := Erdos585.R882.Balanced.support_partition host T
  have disXY : Disjoint X Y := host.disjoint.mono inter_subset_left inter_subset_left
  have disMX : Disjoint M X := disjoint.mono_right inter_subset_right
  have disPY : Disjoint P Y := disjoint.mono sub inter_subset_right
  have disUXY : Disjoint (P∪X) Y := disjoint_union_left.mpr ⟨disPY,disXY⟩
  have lo := left_insertion_retained host sub (inter_subset_left : X ⊆ A) disMX lower greatest
  change (#X : ℤ) ≤ g q G A B (P∪X)-g q G A B P at lo
  have right := all_right_insertion host Y (inter_subset_left : Y ⊆ B) disUXY
  have au : A∩(P∪X)=(A∩P)∪X := by
    rw [inter_union_distrib_left,inter_eq_right.mpr (inter_subset_left : X ⊆ A)]
  have dd : Disjoint (A∩P) X := (disjoint.mono_left sub).mono inter_subset_right inter_subset_right
  have split := ec_union_left (G := G) (Z := Y) dd
  rw [au] at right
  have every : ∀ v ∈ Y, (dg G (A∩P) v : ℤ) ≤ 6*(h : ℤ)-10+(epsilon : ℤ) := by
    intro v hv
    have out : v ∈ univ\M := mem_sdiff.mpr ⟨mem_univ v,fun vm =>
      disjoint_left.mp disjoint vm (mem_inter.mp hv).2⟩
    have mono := ec_mono_right (G := G) P (singleton_subset_iff.mpr out)
    have single : ec G P {v}=dg G P v := by rw [ec_comm]; simp [ec]
    rw [single] at mono
    have dmono := dg_mono (G := G) (inter_subset_right : A∩P ⊆ P) v
    omega
  have bound : (ec G (A∩P) Y : ℤ) ≤ (6*(h : ℤ)-10+(epsilon : ℤ))*#Y := by
    rw [ec_comm,ec,Nat.cast_sum]
    calc
      _ ≤ ∑ _v ∈ Y, (6*(h : ℤ)-10+(epsilon : ℤ)) := sum_le_sum every
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have tax := QB4.ec_le_card_mul (G := G) X Y
  have cards := Erdos585.R882.Balanced.support_card host T
  have hh := host.height
  have degree := Erdos585.R882.Balanced.original_left_degree (Erdos585.R882.Balanced.swap host) T hb
  have db := dg_le_card (G := G) X b
  have hq := reserve host
  have he : (0 : ℤ) ≤ epsilon := by positivity
  have cross := mul_nonneg (show (0 : ℤ) ≤ h by omega) he
  have hhZ : (6 : ℤ) ≤ h := by exact_mod_cast hh
  have xsmall : (#X : ℤ) ≤ (h : ℤ)-2 := by
    have c : #X ≤ #T := card_le_card (inter_subset_right : X ⊆ T)
    omega
  have coef : 0 ≤ (q : ℤ)-(6*(h : ℤ)-10+(epsilon : ℤ))-#X := by nlinarith
  have prod := mul_nonneg (show (0 : ℤ) ≤ #Y by positivity) coef
  have assoc : (P∪X)∪Y=P∪T := by rw [union_assoc,union]
  rw [assoc] at right
  change dg G T b=dg G X b at degree
  zify at split tax
  nlinarith only [lo,right,split,bound,tax,prod,degree,db]

/-- Every actual tiny killer at the greatest minimizer is an exact hazard, for all h>=3. -/
theorem tiny_killer_hazard (neg : g q G A B M < 0)
    {a b : V} (ha : a ∈ A∩M) (common : CommonLeft q G A B a)
    (lightA : dg G (B\M) a ≤ 3*h-4)
    (hb : b ∈ B) (outside : b ∉ M) (lightB : dg G (A∩M) b ≤ 3*h-4)
    (avoid : a ∉ S) (inside : b ∈ S)
    (lower : ∀ W : Finset V, g q G A B M ≤ g q G A B W)
    (greatest : ∀ W : Finset V, g q G A B W=g q G A B M → W ⊆ M)
    (tiny : #(S\M)<h) (band : g q G A B S ≤ (q : ℤ)-1) :
    Hazard q G A B M a b := by
  let P := S∩M
  let E := S\M
  have bE : b ∈ E := mem_sdiff.mpr ⟨inside,outside⟩
  have disj : Disjoint M E := disjoint_sdiff_self_right
  have sub : P ⊆ M := inter_subset_right
  have bound := (original_floor_tiny_boundary host neg ha common lightA hb outside lightB
    avoid inside lower tiny band).2.2.2
  have small : #(E.erase b) ≤ h-2 := by
    have ce := card_erase_of_mem bE
    change #E<h at tiny
    omega
  have payment := retained_insertion_payment host hb sub
    (disj.mono_right (erase_subset b E)) small bound lower greatest
  have insP := g_disjoint host ((disj.mono_left sub).mono_right (erase_subset b E))
  have insM := g_disjoint host (disj.mono_right (erase_subset b E))
  have split := ec_sdiff_add_left (G := G) sub (E.erase b)
  zify at split
  have id := insertion_identity host hb bE disj sub
  have union : P∪E=S := by
    ext v; simp only [P,E,mem_union,mem_inter,mem_sdiff]; tauto
  rw [union] at id
  refine ⟨P,sub,fun hv => avoid (mem_inter.mp hv).1,?_⟩
  omega

#print axioms original_floor_tiny_boundary
#print axioms retained_insertion_payment
#print axioms tiny_killer_hazard
end Erdos585.R882.Balanced
