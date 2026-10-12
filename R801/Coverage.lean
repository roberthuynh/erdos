import R783.Coverage
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHBalancedSelectorR801
open QB4 B5 H3Unequal Omit1PrefixR691 GeneralSelectorR783
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {h q : ℕ} {F : ℤ}
  {A B M P S T : Finset V}
variable (host : OriginalHost h q F G A B)
include host

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
    h ≤ #(M\(S∩M)) ∧ (ec G (S∩M) (univ\M) : ℤ) ≤ 6*(h : ℤ)-10 := by
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
    have deg := AllHCommonPinsR773.original_left_degree (AllHCommonPinsR773.swap host) M hb
    have mono := dg_mono (G := G) sub b
    omega
  have hh := host.height
  have upper : g q G A B P ≤ 4*(h : ℤ)-7 := by
    change #E<h at tiny
    omega
  have eligible : h ≤ #(M\P) := by
    by_contra! small
    have low := cotiny_value_lower host neg ha lightA sub av (by omega)
    have hq : 1024*((h : ℤ)+1)^2 ≤ q := by exact_mod_cast host.large
    have hhZ : (3 : ℤ) ≤ h := by exact_mod_cast hh
    nlinarith
  have boundary := outer_boundary_bound host neg sub eligible
  have qband : g q G A B P ≤ (q : ℤ)-1 := by
    have hq : 1024*((h : ℤ)+1)^2 ≤ q := by exact_mod_cast host.large
    have hhZ : (3 : ℤ) ≤ h := by exact_mod_cast hh
    nlinarith
  have kp := (band_bounds host qband).2
  change 0 ≤ g q G A B P ∧ g q G A B P ≤ 4*(h : ℤ)-7 ∧
    h ≤ #(M\P) ∧ (ec G P (univ\M) : ℤ) ≤ 6*(h : ℤ)-10
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
    (boundary : (ec G P (univ\M) : ℤ) ≤ 6*(h : ℤ)-10)
    (lower : ∀ W : Finset V, g q G A B M ≤ g q G A B W)
    (greatest : ∀ W : Finset V, g q G A B W=g q G A B M → W ⊆ M) :
    (dg G T b : ℤ) ≤ g q G A B (P∪T)-g q G A B P := by
  let X := A∩T
  let Y := B∩T
  have union : X∪Y=T := AllHCommonPinsR773.support_partition host T
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
  have every : ∀ v ∈ Y, (dg G (A∩P) v : ℤ) ≤ 6*(h : ℤ)-10 := by
    intro v hv
    have out : v ∈ univ\M := mem_sdiff.mpr ⟨mem_univ v,fun vm =>
      disjoint_left.mp disjoint vm (mem_inter.mp hv).2⟩
    have mono := ec_mono_right (G := G) P (singleton_subset_iff.mpr out)
    have single : ec G P {v}=dg G P v := by rw [ec_comm]; simp [ec]
    rw [single] at mono
    have dmono := dg_mono (G := G) (inter_subset_right : A∩P ⊆ P) v
    omega
  have bound : (ec G (A∩P) Y : ℤ) ≤ (6*(h : ℤ)-10)*#Y := by
    rw [ec_comm,ec,Nat.cast_sum]
    calc
      _ ≤ ∑ _v ∈ Y, (6*(h : ℤ)-10) := sum_le_sum every
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have tax := QB4.ec_le_card_mul (G := G) X Y
  have cards := AllHCommonPinsR773.support_card host T
  have hh := host.height
  have degree := AllHCommonPinsR773.original_left_degree (AllHCommonPinsR773.swap host) T hb
  have db := dg_le_card (G := G) X b
  have hq : 1024*((h : ℤ)+1)^2 ≤ q := by exact_mod_cast host.large
  have hhZ : (3 : ℤ) ≤ h := by exact_mod_cast hh
  have xsmall : (#X : ℤ) ≤ (h : ℤ)-2 := by
    have c : #X ≤ #T := card_le_card (inter_subset_right : X ⊆ T)
    omega
  have coef : 0 ≤ (q : ℤ)-(6*(h : ℤ)-10)-#X := by nlinarith
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
end Erdos585.AllHBalancedSelectorR801
