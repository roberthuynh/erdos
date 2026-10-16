import R783.Hazard
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.GeneralSelectorR783
open QB4 B5 H3Unequal Omit1PrefixR691
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {h q : ℕ} {F : ℤ}
  {A B M P S T : Finset V}
variable (host : OriginalHost h q F G A B)
include host

lemma band_bounds (band : g q G A B S ≤ (q : ℤ)-1) :
    0 ≤ k A B S ∧ k A B S ≤ h := by
  have scars := AllHCommonPinsR773.scar_bounds host S
  have ident := AllHCommonPinsR773.cut_identity (q := q) (G := G) (A := A) (B := B) S
  have capf := AllHCommonPinsR773.cap_potential host S
  have num := AllHCommonPinsR773.numeric host
  have hq := AllHCommonPinsR773.q_large host
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
    have hh : (3 : ℤ) ≤ h := by exact_mod_cast host.height
    nlinarith only [hm,ident,capf,scars.2.1,band,num.2.2.2.2,hh]

lemma localization_numeric : (q : ℤ)+2*(h : ℤ)-5 < F := by
  have hh : (3 : ℤ) ≤ h := by exact_mod_cast host.height
  have hq : 1024*((h : ℤ)+1)^2 ≤ q := by exact_mod_cast host.large
  have hr := host.range.1
  unfold AllHCommonPinsR773.baseDeficit AllHCommonPinsR773.constant at hr
  have hp := mul_nonneg (show (0 : ℤ) ≤ (h : ℤ)-3 by omega)
    (show (0 : ℤ) ≤ q by positivity)
  nlinarith only [hh,hq,hr,hp]

/-- Every original band cut is tiny on one of the two literal differences. -/
theorem band_localization (neg : g q G A B M < 0)
    (band : g q G A B S ≤ (q : ℤ)-1) : #(M\S)<h ∨ #(S\M)<h := by
  by_contra! hn
  have id := AllHCommonPinsR773.pair_identity host M S
  have bm := AllHCommonPinsR773.negative_bounds host neg
  have bs := band_bounds host band
  have si := (AllHCommonPinsR773.scar_bounds host (M∩S)).2.2.1
  have so := (AllHCommonPinsR773.scar_bounds host (univ\(M∪S))).1
  have e0 : (0 : ℤ) ≤ ec G (M∩S) (univ\(M∪S)) := by positivity
  have proper1 := AllHCommonPinsR773.proper_of_subset_negative host neg
    (sdiff_subset : M\S ⊆ M)
  have el := AllHCommonPinsR773.negative_eligible host neg
  have sub : S\M ⊆ univ\M := sdiff_subset_sdiff_left M (subset_univ S)
  have proper2 := (card_le_card sub).trans_lt el.2.2.2
  have f1 := AllHCommonPinsR773.floor host (M\S) hn.1 proper1
  have f2 := AllHCommonPinsR773.floor host (S\M) hn.2 proper2
  have gap := localization_numeric host
  omega

omit host in
/-- Submodularity closes the finite family of global minimizers. -/
lemma minimum_closed {mu : ℤ} (lower : ∀ S : Finset V, mu ≤ g q G A B S)
    (hs : g q G A B S=mu) (ht : g q G A B T=mu) :
    g q G A B (S∩T)=mu ∧ g q G A B (S∪T)=mu := by
  have sm := g_submodular (q := q) (G := G) (A := A) (B := B) S T
  have lo1 := lower (S∩T)
  have lo2 := lower (S∪T)
  omega

omit host in
/-- The least and greatest global minimizers are chosen internally. -/
theorem global_extrema (exists_negative : ∃ S : Finset V, g q G A B S < 0) :
    ∃ Mlo Mhi : Finset V, Mlo ⊆ Mhi ∧ g q G A B Mlo < 0 ∧ g q G A B Mhi < 0 ∧
      (∀ S : Finset V, g q G A B Mlo ≤ g q G A B S) ∧
      g q G A B Mlo=g q G A B Mhi ∧
      (∀ S : Finset V, g q G A B S=g q G A B Mhi → S ⊆ Mhi) ∧
      (∀ S : Finset V, g q G A B S=g q G A B Mlo → Mlo ⊆ S) := by
  obtain ⟨M0,_,least⟩ := exists_min_image (univ : Finset (Finset V))
    (fun S => g q G A B S) (by exact ⟨∅,mem_univ _⟩)
  let mu := g q G A B M0
  have lower : ∀ S : Finset V, mu ≤ g q G A B S := fun S => least S (mem_univ _)
  have mu_neg : mu < 0 := by
    obtain ⟨S,hs⟩ := exists_negative
    exact (lower S).trans_lt hs
  let family := (univ : Finset (Finset V)).filter (fun S => g q G A B S=mu)
  have nonempty : family.Nonempty := ⟨M0,by simp [family,mu]⟩
  obtain ⟨Mlo,hlo,lo⟩ := exists_min_image family (fun S : Finset V => #S) nonempty
  obtain ⟨Mhi,hhi,hi⟩ := exists_max_image family (fun S : Finset V => #S) nonempty
  have vlo : g q G A B Mlo=mu := (mem_filter.mp hlo).2
  have vhi : g q G A B Mhi=mu := (mem_filter.mp hhi).2
  have incl_hi : ∀ S : Finset V, g q G A B S=mu → S ⊆ Mhi := by
    intro S hs
    have closed := (minimum_closed lower vhi hs).2
    have hc := hi (Mhi∪S) (by simpa [family] using closed)
    have eq := eq_of_subset_of_card_le (subset_union_left : Mhi ⊆ Mhi∪S) hc
    rw [eq]
    exact subset_union_right
  have incl_lo : ∀ S : Finset V, g q G A B S=mu → Mlo ⊆ S := by
    intro S hs
    have closed := (minimum_closed lower vlo hs).1
    have hc := lo (Mlo∩S) (by simpa [family] using closed)
    have eq := eq_of_subset_of_card_le (inter_subset_left : Mlo∩S ⊆ Mlo) hc
    rw [← eq]
    exact inter_subset_right
  exact ⟨Mlo,Mhi,incl_hi Mlo vlo,by omega,by omega,by simpa [vlo] using lower,
    by omega,fun S hs => incl_hi S (hs.trans vhi),fun S hs => incl_lo S (hs.trans vlo)⟩

/-- Disjoint original supports pay their full unoriented cross incidence once. -/
lemma g_disjoint {S T : Finset V} (hd : Disjoint S T) :
    g q G A B (S∪T)=g q G A B S+g q G A B T-(ec G S T : ℤ) := by
  have fp := AllHCommonPinsR773.f_disjoint host hd
  have cs := AllHCommonPinsR773.cut_identity (q := q) (G := G) (A := A) (B := B) S
  have ct := AllHCommonPinsR773.cut_identity (q := q) (G := G) (A := A) (B := B) T
  have cu := AllHCommonPinsR773.cut_identity (q := q) (G := G) (A := A) (B := B) (S∪T)
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

/-- With at most two extra vertices, positivity pays every edge toward b. -/
lemma tiny_insertion_lower {b : V} (hb : b ∈ B) (small : #T ≤ 2)
    (disjoint : Disjoint M T)
    (lower : ∀ S : Finset V, g q G A B M ≤ g q G A B S)
    (greatest : ∀ S : Finset V, g q G A B S=g q G A B M → S ⊆ M) :
    (dg G T b : ℤ) ≤ g q G A B (M∪T)-g q G A B M := by
  have degree := AllHCommonPinsR773.original_left_degree
    (AllHCommonPinsR773.swap host) T hb
  have dc := dg_le_card (G := G) (A∩T) b
  rw [← degree] at dc
  by_cases empty : T=∅
  · subst T
    simp [dg]
  have nonempty : T.Nonempty := nonempty_iff_ne_empty.mpr empty
  by_cases one : #(A∩T) ≤ 1
  · have pos := greatest_insertion_positive host lower greatest disjoint nonempty
    omega
  · have card : #T ≤ #(A∩T) := by omega
    have eq := eq_of_subset_of_card_le (inter_subset_right : A∩T ⊆ T) card
    have subA : T ⊆ A := by rw [← eq]; exact inter_subset_left
    have lo := all_left_insertion_lower host subA disjoint lower greatest
    have dt := dg_le_card (G := G) T b
    omega

/-- An actual tiny addition at the greatest minimizer supplies an exact hazard. -/
lemma tiny_killer_hazard (small_height : h=3 ∨ h=4)
    {a b : V} (hb : b ∈ B) (outside : b ∉ M) (avoid : a ∉ S) (inside : b ∈ S)
    (lower : ∀ W : Finset V, g q G A B M ≤ g q G A B W)
    (greatest : ∀ W : Finset V, g q G A B W=g q G A B M → W ⊆ M)
    (tiny : #(S\M)<h) (band : g q G A B S ≤ (q : ℤ)-1) :
    Hazard q G A B M a b := by
  let P := S∩M
  let E := S\M
  have bE : b ∈ E := mem_sdiff.mpr ⟨inside,outside⟩
  have disj : Disjoint M E := disjoint_sdiff_self_right
  have sub : P ⊆ M := inter_subset_right
  have id := insertion_identity host hb bE disj sub
  have union : P∪E=S := by
    ext v; simp only [P,E,mem_union,mem_inter,mem_sdiff]; tauto
  rw [union] at id
  have small : #(E.erase b) ≤ 2 := by
    have ce := card_erase_of_mem bE
    change #E<h at tiny
    rcases small_height with rfl|rfl <;> omega
  have lo := tiny_insertion_lower host hb small
    (disj.mono_right (erase_subset b E)) lower greatest
  have nonneg : (0 : ℤ) ≤ ec G (M\P) (E.erase b) := by positivity
  refine ⟨P,sub,fun ha => avoid (mem_inter.mp ha).1,?_⟩
  omega

#print axioms band_localization
#print axioms global_extrema
#print axioms insertion_identity
#print axioms tiny_killer_hazard
end Erdos585.GeneralSelectorR783
