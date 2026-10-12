import R691.Main
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R882.Balanced
open QB4 B5 H3Unequal Omit1PrefixR691
universe u
variable {V : Type u} [Fintype V]
structure Host (h epsilon q : ℕ) (F : ℤ) (G : SimpleGraph V) (A B : Finset V) : Prop where
  height : 6 ≤ h
  large : 4096*(h+1)^2 ≤ q
  cost_bound : (epsilon : ℤ) ≤ 4*(h : ℤ)^2-10*(h : ℤ)+4
  physical : F = (h : ℤ)*q-16*(h : ℤ)^2+epsilon
  cubic : 12*(h : ℤ)^3-40*(h : ℤ)^2+42*(h : ℤ)-15 ≤ q
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  balanced : #A = #B
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  order : 2*q ≤ Fintype.card V
  min_degree : ∀ v, q ≤ G.degree v
  cap : ∀ v, G.degree v ≤ 2*q-2
  total : coreDefect q G A B = F
  range : 2*(q : ℤ) ≤ F ∧ F ≤ (h : ℤ)*q-12*(h : ℤ)^2
  proper : ∀ S : Finset V, h ≤ #S → #S < Fintype.card V →
    F+1-(epsilon : ℤ) ≤ ((q : ℤ)-1)*#S-((G.induce (S : Set V)).edgeSet.ncard : ℤ)
def Conclusion (h q : ℕ) (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ S T : Finset V, g q G A B S < 0 → g q G A B T < 0 →
    ¬S ⊆ T → ¬T ⊆ S → #(S\T)+#(T\S) ≤ h-1) ∧
  ∃ LA LB : Finset V, LA ⊆ A ∧ LB ⊆ B ∧ q < 2*#LA ∧ q < 2*#LB ∧
    ∀ M : Finset V, g q G A B M < 0 →
      LA ⊆ M ∧ Disjoint LB M ∧
      (∀ v ∈ LA, dg G (B\M) v ≤ 3*h-4) ∧
      (∀ v ∈ LB, dg G (A∩M) v ≤ 3*h-4)
variable {G : SimpleGraph V} {h epsilon q : ℕ} {F : ℤ} {A B S T : Finset V}
variable (host : Host h epsilon q F G A B)
include host
lemma q_large : 3 ≤ q := by
  have hh := host.height
  have hq := host.large
  have hx : 1 ≤ (h+1)^2 := by nlinarith
  nlinarith
lemma support_partition (S : Finset V) : (A ∩ S) ∪ (B ∩ S) = S := by
  rw [← union_inter_distrib_right, host.cover, univ_inter]
lemma support_card (S : Finset V) : #(A ∩ S) + #(B ∩ S) = #S := by
  rw [← card_union_of_disjoint (host.disjoint.mono inter_subset_left inter_subset_left),
    support_partition host]
lemma f_actual (S : Finset V) : f q G A B S =
    ((q : ℤ) - 1) * #S - ((G.induce (S : Set V)).edgeSet.ncard : ℤ) := by
  have he := induced_edges_eq_ec host.disjoint host.bipartite
    (inter_subset_left : A ∩ S ⊆ A) (inter_subset_left : B ∩ S ⊆ B)
  rw [support_partition host] at he
  unfold f coreDefect
  rw [he, ← support_card host S, Nat.cast_add]
lemma floor (S : Finset V) (hs : h ≤ #S) (hp : #S < Fintype.card V) :
    F + 1-(epsilon : ℤ) ≤ f q G A B S := by
  rw [f_actual host]
  exact host.proper S hs hp
lemma capA {v : V} (hv : v ∈ A) : (dg G B v : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  rw [dg_eq_degree host.bipartite hv]
  have hc := host.cap v
  have hq := q_large host
  omega
lemma capB {v : V} (hv : v ∈ B) : (dg G A v : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  rw [dg_eq_degree host.bipartite.symm hv]
  have hc := host.cap v
  have hq := q_large host
  omega
lemma scar_bounds (S : Finset V) :
    0 ≤ sA q G A B S ∧ sA q G A B S ≤ F ∧
    0 ≤ sB q G A B S ∧ sB q G A B S ≤ F := by
  have da : deficiency (2 * (q : ℤ) - 2) G B A = F := by
    rw [deficiency_eq]
    have ht := host.total
    unfold coreDefect at ht
    have hb := host.balanced
    zify at hb
    nlinarith
  have db : deficiency (2 * (q : ℤ) - 2) G A B = F := by
    rw [deficiency_eq, ec_comm (G := G) B A, ← host.balanced]
    rw [deficiency_eq] at da
    exact da
  refine ⟨deficiency_nonneg _ (fun v hv => capA host (inter_subset_left hv)), ?_,
    deficiency_nonneg _ (fun v hv => capB host (inter_subset_left hv)), ?_⟩
  · exact (deficiency_le_subset _ inter_subset_left (fun v hv => capA host hv)).trans_eq da
  · exact (deficiency_le_subset _ inter_subset_left (fun v hv => capB host hv)).trans_eq db

omit [Fintype V] host in
lemma cut_identity (S : Finset V) :
    g q G A B S = f q G A B S - sA q G A B S - k A B S := by
  have he := ec_sdiff_add_right (G := G) (inter_subset_left : B ∩ S ⊆ B) (A ∩ S)
  have hs : B \ (B ∩ S) = B \ S := by ext x; simp
  rw [hs] at he
  zify at he
  unfold g f sA k coreDefect
  rw [deficiency_eq]
  nlinarith

lemma f_twice (S : Finset V) : 2 * f q G A B S =
    2 * ((q : ℤ) - 1) * #S - (ec G S S : ℤ) := by
  have he := NEQAssembly.ec_self_eq_twice_induced_edges (G := G) S
  rw [f_actual host]
  zify at he
  rw [he]
  ring_nf
  rfl

lemma f_disjoint {S T : Finset V} (hd : Disjoint S T) :
    f q G A B S + f q G A B T =
      f q G A B (S ∪ T) + (ec G S T : ℤ) := by
  have he : ec G (S ∪ T) (S ∪ T) =
      ec G S S + ec G S T + ec G T S + ec G T T := by
    rw [ec_union_left hd, ec_union_right hd, ec_union_right hd]
    omega
  rw [ec_comm (G := G) T S] at he
  have hc := card_union_of_disjoint hd
  have h1 := f_twice host S
  have h2 := f_twice host T
  have h3 := f_twice host (S ∪ T)
  zify at he hc
  nlinarith

lemma f_univ : f q G A B univ = F := by
  simpa [f] using host.total
lemma complementary (S : Finset V) :
    f q G A B S + f q G A B (univ \ S) =
      F + (ec G S (univ \ S) : ℤ) := by
  have he := f_disjoint host (disjoint_sdiff_self_right : Disjoint S (univ \ S))
  rw [union_sdiff_of_subset (subset_univ S), f_univ host] at he
  exact he

lemma boundary_identity (S : Finset V) :
    (ec G S (univ \ S) : ℤ) =
      2 * f q G A B S - sA q G A B S - sB q G A B S := by
  have he := ec_sdiff_add_right (G := G) (subset_univ S) S
  have hpart := support_partition host S
  have hdeg : ec G S univ = ec G (A ∩ S) B + ec G (B ∩ S) A := by
    conv_lhs => rw [← hpart]
    rw [ec_union_left (host.disjoint.mono inter_subset_left inter_subset_left)]
    have ha : ec G (A ∩ S) univ = ec G (A ∩ S) B := by
      rw [← host.cover, ec_union_right host.disjoint]
      have hz : ec G (A ∩ S) A = 0 := by
        have hm := ec_mono_left (G := G) (inter_subset_left : A ∩ S ⊆ A) A
        have hz := ec_internal_zero host.disjoint host.bipartite (Subset.refl A)
        omega
      omega
    have hb : ec G (B ∩ S) univ = ec G (B ∩ S) A := by
      rw [← host.cover, ec_union_right host.disjoint]
      have hz : ec G (B ∩ S) B = 0 := by
        have hm := ec_mono_left (G := G) (inter_subset_left : B ∩ S ⊆ B) B
        have hz := ec_internal_zero host.disjoint.symm host.bipartite.symm (Subset.refl B)
        omega
      omega
    rw [ha, hb]
  rw [hdeg] at he
  have hf := f_twice host S
  have hc := support_card host S
  zify at he hc
  unfold sA sB
  rw [deficiency_eq, deficiency_eq]
  nlinarith

lemma complement_identity (S : Finset V) :
    f q G A B (univ \ S) = F +
      g q G A B S + k A B S - sB q G A B S := by
  have h1 := complementary host S
  have h2 := boundary_identity host S
  have h3 := cut_identity (q := q) (G := G) (A := A) (B := B) S
  omega

lemma cap_potential (S : Finset V) :
    ((q : ℤ) - 1) * k A B S ≤ f q G A B S := by
  have he : (ec G (A ∩ S) (B ∩ S) : ℤ) ≤
      (2 * (q : ℤ) - 2) * #(B ∩ S) := by
    rw [ec_comm]
    have hm := deficiency_nonneg (W := A ∩ S) (X := B ∩ S) (2 * (q : ℤ) - 2)
      (fun v hv => show (dg G (A ∩ S) v : ℤ) ≤ 2 * (q : ℤ) - 2 from
        (by have hh := dg_mono (G := G) (inter_subset_left : A ∩ S ⊆ A) v
            have hc := capB host (inter_subset_left hv)
            exact (show (dg G (A ∩ S) v : ℤ) ≤ dg G A v by exact_mod_cast hh).trans hc))
    rw [deficiency_eq] at hm
    omega
  unfold f k coreDefect
  nlinarith




lemma reserve : 100*((h : ℤ)^2+(epsilon : ℤ)+(h : ℤ)+1) < q := by
  have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
  have he : (0 : ℤ) ≤ epsilon := by positivity
  have hc := host.cost_bound
  have hq : 4096*((h : ℤ)+1)^2 ≤ q := by exact_mod_cast host.large
  nlinarith [sq_nonneg (h : ℤ)]
lemma numeric : (h : ℤ) ≤ q ∧ (h : ℤ)+2 ≤ q ∧
    4*(h : ℤ)-6+(epsilon : ℤ) < q ∧ 2*(h : ℤ)-6+2*(epsilon : ℤ) < F ∧
    F ≤ (h : ℤ)*q-12*(h : ℤ)^2 := by
  have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
  have he : (0 : ℤ) ≤ epsilon := by positivity
  have hq := reserve host
  have hr := host.range
  have cross := mul_nonneg (show (0 : ℤ) ≤ h by omega) he
  constructor
  · nlinarith [sq_nonneg ((h : ℤ)-1),sq_nonneg (epsilon : ℤ)]
  constructor
  · nlinarith [sq_nonneg ((h : ℤ)-1),sq_nonneg (epsilon : ℤ)]
  constructor
  · nlinarith [sq_nonneg ((h : ℤ)-1),sq_nonneg ((epsilon : ℤ)-1)]
  constructor
  · nlinarith [sq_nonneg ((h : ℤ)-1),sq_nonneg ((epsilon : ℤ)-1)]
  · exact hr.2
lemma minA (v : V) (hv : v ∈ A) : q ≤ dg G B v := by
  rw [dg_eq_degree host.bipartite hv]; exact host.min_degree v
lemma minB (v : V) (hv : v ∈ B) : q ≤ dg G A v := by
  rw [dg_eq_degree host.bipartite.symm hv]; exact host.min_degree v
lemma ec_lower {X : Finset V} (hx : X ⊆ A) : q*#X ≤ ec G X B := by
  unfold ec
  calc
    _ = ∑ _v ∈ X, q := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum (fun v hv => minA host v (hx hv))
lemma endpoint_order (neg : g q G A B S < 0) :
    q+1 ≤ #(A∩S) ∧ q+1 ≤ #(B\S) := by
  have ca := card_sdiff_add_card_eq_card (inter_subset_left : A∩S ⊆ A)
  have cb := card_sdiff_add_card_eq_card (inter_subset_left : B∩S ⊆ B)
  have ae : A\(A∩S)=A\S := by ext v; simp
  have be : B\(B∩S)=B\S := by ext v; simp
  rw [ae] at ca
  rw [be] at cb
  have bal := host.balanced
  zify at ca cb bal
  have e1 := ec_lower host (inter_subset_left : A∩S ⊆ A)
  have sp1 := ec_sdiff_add_right (G := G) (inter_subset_left : B∩S ⊆ B) (A∩S)
  rw [be] at sp1
  have upper1 := QB4.ec_le_card_mul (G := G) (A∩S) (B∩S)
  have e2 : q*#(B\S) ≤ ec G (B\S) A := by
    unfold ec
    calc
      _ = ∑ _v ∈ B\S, q := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => minB host v (sdiff_subset hv))
  have sp2 := ec_sdiff_add_right (G := G) (inter_subset_left : A∩S ⊆ A) (B\S)
  rw [ae, ec_comm (G := G) (B\S) (A∩S)] at sp2
  have upper2 := QB4.ec_le_card_mul (G := G) (B\S) (A\S)
  zify at e1 e2 sp1 sp2 upper1 upper2
  unfold g k at neg
  constructor
  · by_contra! hn
    have small : (#(A∩S) : ℤ) ≤ q := by omega
    have prod := mul_nonneg (show (0 : ℤ) ≤ #(B∩S) by positivity)
      (show 0 ≤ (q : ℤ)-#(A∩S) by omega)
    nlinarith only [prod,e1,sp1,upper1,neg]
  · by_contra! hn
    have small : (#(B\S) : ℤ) ≤ q := by omega
    have prod := mul_nonneg (show (0 : ℤ) ≤ #(A\S) by positivity)
      (show 0 ≤ (q : ℤ)-#(B\S) by omega)
    nlinarith only [prod,e2,sp2,upper2,neg,ca,cb,bal]
lemma negative_eligible (neg : g q G A B S < 0) :
    h+1 ≤ #S ∧ h+1 ≤ #(univ\S) ∧
    #S < Fintype.card V ∧ #(univ\S) < Fintype.card V := by
  have ep := endpoint_order host neg
  have a := card_le_card (inter_subset_right : A∩S ⊆ S)
  have b : #(B\S) ≤ #(univ\S) := card_le_card (sdiff_subset_sdiff_left S (subset_univ B))
  have total := card_sdiff_add_card_eq_card (subset_univ S)
  rw [card_univ] at total
  have num := numeric host
  have qh : h+2 ≤ q := by omega
  omega
lemma negative_bounds (neg : g q G A B S < 0) :
    1 ≤ k A B S ∧ k A B S ≤ (h : ℤ)-1 ∧
    1-k A B S-(epsilon : ℤ) ≤ g q G A B S ∧
    f q G A B S ≤ F+(h : ℤ)-2 ∧
    f q G A B (univ\S) ≤ F+(h : ℤ)-2 := by
  have el := negative_eligible host neg
  have fs := floor host S (by omega) el.2.2.1
  have ft := floor host (univ\S) (by omega) el.2.2.2
  have scar := scar_bounds host S
  have id := cut_identity (q := q) (G := G) (A := A) (B := B) S
  have co := complement_identity host S
  have cp := cap_potential host S
  have num := numeric host
  have ku : k A B S ≤ (h : ℤ)-1 := by
    by_contra! hn
    have prod := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ)-2 by have l:=q_large host; omega)
      (show 0 ≤ k A B S-(h : ℤ) by omega)
    nlinarith only [prod,cp,id,scar.2.1,neg,num.2.2.2.2]
  have positive : 1 ≤ k A B S := by
    have nonneg : (0 : ℤ) ≤ ec G (A∩S) (B\S) := by positivity
    have qp : (0 : ℤ) < q := by have qq := q_large host; omega
    by_contra! hk
    have prod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt qp) (show k A B S ≤ 0 by omega)
    unfold g at neg
    omega
  omega


lemma pair_identity (S T : Finset V) :
    f q G A B (S\T)+f q G A B (T\S) =
      F+g q G A B S+g q G A B T+k A B S+k A B T -
        sB q G A B (S∩T)-sA q G A B (univ\(S∪T)) -
        ec G (S∩T) (univ\(S∪T)) := by
  have dp : Disjoint (S∩T) (S\T) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).2
  have dq : Disjoint (S∩T) (T\S) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).1
  have us : (S∩T) ∪ (S\T) = S := by ext v; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  have ut : (S∩T) ∪ (T\S) = T := by ext v; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  have ps := f_disjoint host dp
  have pt := f_disjoint host dq
  rw [us] at ps
  rw [ut] at pt
  have cs := cut_identity (q := q) (G := G) (A := A) (B := B) S
  have ct := cut_identity (q := q) (G := G) (A := A) (B := B) T
  have bi := boundary_identity host (S∩T)
  have asums := sum_union_inter (s₁ := A∩S) (s₂ := A∩T)
    (f := fun v => 2*(q : ℤ)-2-(dg G B v : ℤ))
  have ai : (A∩S)∩(A∩T)=A∩(S∩T) := by ext v; simp only [mem_inter]; tauto
  rw [← inter_union_distrib_left, ai] at asums
  have ao := sum_sdiff (s₁ := A∩(S∪T)) (s₂ := A)
    (f := fun v => 2*(q : ℤ)-2-(dg G B v : ℤ)) inter_subset_left
  have ae : A\(A∩(S∪T))=A∩(univ\(S∪T)) := by ext v; simp
  rw [ae] at ao
  have scarTotal : deficiency (2*(q : ℤ)-2) G B A = F := by
    rw [deficiency_eq]
    have ht := host.total
    have hb := host.balanced
    unfold coreDefect at ht
    zify at hb
    nlinarith
  have scarEq : sA q G A B S+sA q G A B T =
    F+sA q G A B (S∩T)-sA q G A B (univ\(S∪T)) := by
    unfold sA deficiency at *
    omega
  have dpq : Disjoint (S\T) (T\S) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hv).2 (mem_sdiff.mp hw).1
  have dpo : Disjoint ((S\T) ∪ (T\S)) (univ\(S∪T)) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    simp only [mem_union,mem_sdiff,mem_univ] at hv hw
    tauto
  have out : (S\T) ∪ (T\S) ∪ (univ\(S∪T)) = univ\(S∩T) := by
    ext v; simp only [mem_union,mem_sdiff,mem_univ,mem_inter]; tauto
  have ee := ec_union_right (G := G) (Z := S∩T) dpo
  rw [ec_union_right dpq, out] at ee
  zify at ee
  omega
lemma pair_bound (hs : g q G A B S < 0) (ht : g q G A B T < 0) :
    f q G A B (S\T)+f q G A B (T\S) ≤ F+2*(h : ℤ)-4 := by
  have id := pair_identity host S T
  have bs := negative_bounds host hs
  have bt := negative_bounds host ht
  have si := (scar_bounds host (S∩T)).2.2.1
  have so := (scar_bounds host (univ\(S∪T))).1
  have e0 : (0 : ℤ) ≤ ec G (S∩T) (univ\(S∪T)) := by positivity
  omega


lemma erase_identity {v : V} (hv : v ∈ S) :
    f q G A B (S.erase v)=f q G A B S-((q : ℤ)-1)+dg G S v := by
  have dj : Disjoint (S.erase v) {v} := by simp
  have uu : S.erase v ∪ {v}=S := by ext w; simp only [mem_union,mem_erase,mem_singleton]; by_cases hw : w=v <;> simp_all
  have fs := f_disjoint host dj
  rw [uu] at fs
  have fv := f_twice host {v}
  have ee : ec G {v} {v}=0 := by simp [ec,dg]
  rw [ee,card_singleton] at fv
  have dgErase : dg G (S.erase v) v=dg G S v := by
    unfold dg
    congr 1
    ext w
    simp only [mem_filter,mem_erase]
    constructor
    · tauto
    · rintro ⟨hw,hadj⟩
      exact ⟨⟨fun he => by subst w; exact G.irrefl hadj,hw⟩,hadj⟩
  rw [ec_comm (G := G) (S.erase v) {v}] at fs
  simp only [ec,sum_singleton] at fs
  rw [dgErase] at fs
  norm_num at fv
  omega
lemma internal_lower (D : Finset V) (eligible : h+1 ≤ #D)
    (proper : #D < Fintype.card V) (upper : f q G A B D ≤ F+(h : ℤ)-2)
    {v : V} (hv : v ∈ D) : (q : ℤ)-(h : ℤ)+2-(epsilon : ℤ) ≤ dg G D v := by
  have ce := card_erase_of_mem hv
  have small := card_le_card (erase_subset v D)
  have floorE := floor host (D.erase v) (by omega) (by omega)
  have id := erase_identity host hv
  omega
lemma negative_internal (neg : g q G A B S < 0) :
    (∀ v ∈ S, (q : ℤ)-(h : ℤ)+2-(epsilon : ℤ) ≤ dg G S v) ∧
    (∀ v ∈ univ\S, (q : ℤ)-(h : ℤ)+2-(epsilon : ℤ) ≤ dg G (univ\S) v) := by
  have el := negative_eligible host neg
  have bd := negative_bounds host neg
  exact ⟨fun v hv => internal_lower host S el.1 el.2.2.1 bd.2.2.2.1 hv,
    fun v hv => internal_lower host (univ\S) el.2.1 el.2.2.2 bd.2.2.2.2 hv⟩


lemma small_potential (D : Finset V) (pos : 1 ≤ #D) (small : #D ≤ h-1) :
    (q : ℤ)-1 ≤ f q G A B D := by
  have card := support_card host D
  have e := QB4.ec_le_card_mul (G := G) (A∩D) (B∩D)
  have a := card_le_card (inter_subset_right : A∩D ⊆ D)
  have b := card_le_card (inter_subset_right : B∩D ⊆ D)
  have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
  have hq := reserve host
  have he : (0 : ℤ) ≤ epsilon := by positivity
  have cross := mul_nonneg (show (0 : ℤ) ≤ h by omega) he
  zify at card e a b pos small
  have smallZ : (#D : ℤ) ≤ (h : ℤ)-1 := by omega
  unfold f coreDefect
  by_cases one : (#D : ℤ)=1
  · have prod : (#(A∩D) : ℤ)*#(B∩D)=0 := by
      have a0 : (0 : ℤ) ≤ #(A∩D) := by positivity
      have b0 : (0 : ℤ) ≤ #(B∩D) := by positivity
      have ai : (#(A∩D) : ℤ)=0 ∨ (#(A∩D) : ℤ)=1 := by omega
      rcases ai with ai | ai <;> rw [ai] <;> nlinarith
    nlinarith
  · have two : (2 : ℤ) ≤ #D := by omega
    have qp : 0 ≤ (q : ℤ)-1-(#D : ℤ)^2 := by nlinarith
    have prod := mul_nonneg (show (0 : ℤ) ≤ (#D : ℤ)-2 by omega)
      (show 0 ≤ (q : ℤ)-1 by nlinarith)
    have density : (#(A∩D) : ℤ)*#(B∩D) ≤ (#D : ℤ)^2 := by
      have ap := mul_nonneg (show (0 : ℤ) ≤ #(A∩D) by positivity)
        (show 0 ≤ (#D : ℤ)-#(B∩D) by omega)
      have bp := mul_nonneg (show (0 : ℤ) ≤ #D by positivity)
        (show 0 ≤ (#D : ℤ)-#(A∩D) by omega)
      nlinarith
    nlinarith
lemma proper_of_subset_negative (neg : g q G A B S < 0) {D : Finset V} (sub : D ⊆ S) :
    #D < Fintype.card V :=
  (card_le_card sub).trans_lt (negative_eligible host neg).2.2.1
lemma negative_differences_small (hs : g q G A B S < 0) (ht : g q G A B T < 0)
    (st : ¬S ⊆ T) (ts : ¬T ⊆ S) : #(S\T) ≤ h-1 ∧ #(T\S) ≤ h-1 := by
  have ps : 1 ≤ #(S\T) := card_pos.mpr (sdiff_nonempty.mpr st)
  have pt : 1 ≤ #(T\S) := card_pos.mpr (sdiff_nonempty.mpr ts)
  have properP := proper_of_subset_negative host hs (sdiff_subset : S\T ⊆ S)
  have properQ := proper_of_subset_negative host ht (sdiff_subset : T\S ⊆ T)
  have bound := pair_bound host hs ht
  have num := numeric host
  have gap : 2*(h : ℤ)-4+(epsilon : ℤ) < q := by
    have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
    omega
  have cases : ¬(h ≤ #(S\T) ∧ h ≤ #(T\S)) := by
    rintro ⟨hp,hq⟩
    have fp := floor host (S\T) hp properP
    have fq := floor host (T\S) hq properQ
    omega
  have first : #(S\T) ≤ h-1 := by
    by_contra! hn
    have hp : h ≤ #(S\T) := by omega
    have hq : #(T\S) ≤ h-1 := by omega
    have fp := floor host (S\T) hp properP
    have fq := small_potential host (T\S) pt hq
    omega
  have second : #(T\S) ≤ h-1 := by
    by_contra! hn
    have hq : h ≤ #(T\S) := by omega
    have fp := small_potential host (S\T) ps first
    have fq := floor host (T\S) hq properQ
    omega
  exact ⟨first,second⟩
/-- Incomparable geometry for EVERY original pair, with no chain premise. -/
theorem negative_diameter (hs : g q G A B S < 0) (ht : g q G A B T < 0)
    (st : ¬S ⊆ T) (ts : ¬T ⊆ S) : #(S\T)+#(T\S) ≤ h-1 := by
  have small := negative_differences_small host hs ht st ts
  have bound := pair_bound host hs ht
  have cp := support_card host (S\T)
  have cq := support_card host (T\S)
  have ep := QB4.ec_le_card_mul (G := G) (A∩(S\T)) (B∩(S\T))
  have eq := QB4.ec_le_card_mul (G := G) (A∩(T\S)) (B∩(T\S))
  have cross1 := mul_nonneg (show (0 : ℤ) ≤ #(A∩(S\T)) by positivity)
    (show (0 : ℤ) ≤ #(B∩(T\S)) by positivity)
  have cross2 := mul_nonneg (show (0 : ℤ) ≤ #(A∩(T\S)) by positivity)
    (show (0 : ℤ) ≤ #(B∩(S\T)) by positivity)
  let a : ℤ := #(A∩(S\T)) + #(A∩(T\S))
  let b : ℤ := #(B∩(S\T)) + #(B∩(T\S))
  have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
  have num := numeric host
  have qpos : 0 ≤ (q : ℤ)-1 := by have qq:=q_large host; omega
  by_contra! hn
  have large : h ≤ #(S\T)+#(T\S) := by omega
  zify at cp cq ep eq small large
  have sum : a+b = (#(S\T) : ℤ)+#(T\S) := by dsimp [a,b]; omega
  have abpos : 0 ≤ a+b := by dsimp [a,b]; positivity
  have sumUpper : a+b ≤ 2*((h : ℤ)-1) := by omega
  have square := sq_nonneg (a-b)
  have maxsquare := mul_nonneg (show (0 : ℤ) ≤ 2*((h : ℤ)-1)-(a+b) by omega)
    (show (0 : ℤ) ≤ 2*((h : ℤ)-1)+(a+b) by omega)
  have density : (ec G (A∩(S\T)) (B∩(S\T)) : ℤ)+
      ec G (A∩(T\S)) (B∩(T\S)) ≤ ((h : ℤ)-1)^2 := by
    dsimp [a,b] at square maxsquare
    nlinarith only [ep,eq,cross1,cross2,square,maxsquare]
  have product := mul_nonneg (show (0 : ℤ) ≤ (#(S\T) : ℤ)+#(T\S)-(h : ℤ) by omega) qpos
  unfold f coreDefect at bound
  nlinarith only [bound,num.2.2.2.2,cp,cq,density,product,hh]


omit host [Fintype V] in
lemma dg_difference_bound (X Y : Finset V) (v : V) :
    dg G X v ≤ dg G Y v + #(X\Y) := by
  have hd := dg_sdiff_add (G := G) (inter_subset_left : X∩Y ⊆ X) v
  have he : X\(X∩Y)=X\Y := by ext w; simp
  rw [he] at hd
  have hm := dg_mono (G := G) (inter_subset_right : X∩Y ⊆ Y) v
  have hc := dg_le_card (G := G) (X\Y) v
  omega
lemma original_left_degree (D : Finset V) {v : V} (hv : v ∈ A) :
    dg G D v=dg G (B∩D) v := by
  have zero : dg G (A∩D) v=0 := by
    unfold dg
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro w hw
    have hw' := mem_filter.mp hw
    exact Finset.disjoint_left.mp host.disjoint (mem_inter.mp hw'.1).1
      (host.bipartite.mem_of_mem_adj hv hw'.2)
  have eq := dg_union_of_disjoint (G := G)
    (host.disjoint.mono (inter_subset_left : A∩D ⊆ A) (inter_subset_left : B∩D ⊆ B)) v
  rw [support_partition host D,zero,zero_add] at eq
  exact eq
omit host [Fintype V] in
lemma forward_degree_comparison (S M : Finset V) (v : V) :
    dg G (B\M) v ≤ dg G (B\S) v + #(S\M) := by
  have hd := dg_difference_bound (G := G) (B\M) (B\S) v
  have sub : (B\M)\(B\S) ⊆ S\M := by
    intro w hw
    simp only [mem_sdiff] at hw ⊢
    tauto
  have hc := card_le_card sub
  omega
lemma forward_count (neg : g q G A B S < 0) :
    (ec G (A∩S) (B\S) : ℤ) ≤ ((h : ℤ)-1)*q-1 := by
  have b := negative_bounds host neg
  have qp : (0 : ℤ) ≤ q := by positivity
  have prod := mul_nonneg (show (0 : ℤ) ≤ (h : ℤ)-1-k A B S by omega) qp
  unfold g at neg
  nlinarith
lemma light_count (X Y : Finset V) (order : q+1 ≤ #X)
    (forward : (ec G X Y : ℤ) ≤ ((h : ℤ)-1)*q-1) :
    q < 2*#(X.filter (fun v => dg G Y v ≤ 2*h-2)) := by
  let L := X.filter (fun v => dg G Y v ≤ 2*h-2)
  let H := X\L
  have counts := card_sdiff_add_card_eq_card (filter_subset (fun v => dg G Y v ≤ 2*h-2) X)
  change #H+#L=#X at counts
  have hh := host.height
  have threshold : ∀ v ∈ H, 2*h-1 ≤ dg G Y v := by
    intro v hv
    have hs := mem_sdiff.mp hv
    have heavy : ¬dg G Y v ≤ 2*h-2 := by
      intro hl
      exact hs.2 (mem_filter.mpr ⟨hs.1,hl⟩)
    omega
  have lower : (2*h-1)*#H ≤ ec G H Y := by
    unfold ec
    calc
      _ = ∑ _v ∈ H, (2*h-1) := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum threshold
  have upper := ec_mono_left (G := G) (sdiff_subset : H ⊆ X) Y
  change q < 2*#L
  by_contra! hn
  have qpos := q_large host
  zify at counts order lower upper hn
  have heavy : (q : ℤ) ≤ 2*#H := by omega
  have th : ((2*h-1 : ℕ) : ℤ)=2*(h : ℤ)-1 := by omega
  rw [th] at lower
  have prod := mul_nonneg (show (0 : ℤ) ≤ 2*#H-(q : ℤ) by omega)
    (show 0 ≤ 2*(h : ℤ)-1 by omega)
  nlinarith only [forward,lower,upper,prod]
lemma minimal_difference (negS : g q G A B S < 0)
    (minimal : ∀ M : Finset V, g q G A B M < 0 → #S ≤ #M)
    (negM : g q G A B T < 0) : #(S\T) ≤ h-2 := by
  by_cases sub : S ⊆ T
  · rw [sdiff_eq_empty_iff_subset.mpr sub,card_empty]
    exact Nat.zero_le _
  · have reverse : ¬T ⊆ S := by
      intro rev
      have eq := eq_of_subset_of_card_le rev (minimal T negM)
      exact sub (eq ▸ Subset.refl S)
    have diameter := negative_diameter host negS negM sub reverse
    have positive : 1 ≤ #(T\S) := card_pos.mpr (sdiff_nonempty.mpr reverse)
    omega


/-- Original common left pins are selected internally from the finite negative family. -/
theorem common_left (exists_negative : ∃ M : Finset V, g q G A B M < 0) :
    ∃ LA : Finset V, LA ⊆ A ∧ q < 2*#LA ∧
      ∀ M : Finset V, g q G A B M < 0 →
        LA ⊆ M ∧ ∀ v ∈ LA, dg G (B\M) v ≤ 3*h-4 := by
  let family : Finset (Finset V) := univ.filter (fun M => g q G A B M < 0)
  have family_nonempty : family.Nonempty := by
    obtain ⟨M,hm⟩ := exists_negative
    exact ⟨M,by simpa [family] using hm⟩
  obtain ⟨S,hs,least⟩ := exists_min_image family (fun M : Finset V => #M) family_nonempty
  have negS : g q G A B S < 0 := by simpa [family] using hs
  have minimal : ∀ M : Finset V, g q G A B M < 0 → #S ≤ #M := by
    intro M hm
    exact least M (by simpa [family] using hm)
  let LA := (A∩S).filter (fun v => dg G (B\S) v ≤ 2*h-2)
  have count : q < 2*#LA := light_count host (A∩S) (B\S)
    (endpoint_order host negS).1 (forward_count host negS)
  refine ⟨LA,fun v hv => (mem_inter.mp (mem_filter.mp hv).1).1,count,?_⟩
  intro M negM
  have difference := minimal_difference host negS minimal negM
  have all_degree : ∀ v ∈ LA, dg G (B\M) v ≤ 3*h-4 := by
    intro v hv
    have light := (mem_filter.mp hv).2
    have comp := forward_degree_comparison (G := G) (B := B) S M v
    have hh := host.height
    omega
  refine ⟨?_,all_degree⟩
  intro v hv
  by_contra! outside
  have ha := (mem_inter.mp (mem_filter.mp hv).1).1
  have inside := (negative_internal host negM).2 v (by simp [outside])
  have degree := original_left_degree host (univ\M) ha
  have bs : B∩(univ\M)=B\M := by ext w; simp
  rw [bs] at degree
  rw [degree] at inside
  have upper := all_degree v hv
  have num := numeric host
  have hh := host.height
  omega
lemma swap : Host h epsilon q F G B A where
  height := host.height
  large := host.large
  cost_bound := host.cost_bound
  physical := host.physical
  cubic := host.cubic
  disjoint := host.disjoint.symm
  cover := by rw [union_comm]; exact host.cover
  balanced := host.balanced.symm
  bipartite := host.bipartite.symm
  order := host.order
  min_degree := host.min_degree
  cap := host.cap
  total := by
    have ht := host.total
    unfold coreDefect at ht ⊢
    rw [ec_comm (G := G) B A]
    nlinarith
  range := host.range
  proper := host.proper
lemma swapped_complement (S : Finset V) :
    g q G B A (univ\S)=g q G A B S := by
  have ca := card_sdiff_add_card_eq_card (inter_subset_left : A∩S ⊆ A)
  have cb := card_sdiff_add_card_eq_card (inter_subset_left : B∩S ⊆ B)
  have ae : A\(A∩S)=A\S := by ext v; simp
  have be : B\(B∩S)=B\S := by ext v; simp
  rw [ae] at ca
  rw [be] at cb
  have bal := host.balanced
  have ao : A\(univ\S)=A∩S := by ext v; simp
  have bo : B∩(univ\S)=B\S := by ext v; simp
  have ac : A∩(univ\S)=A\S := by ext v; simp
  zify at ca cb bal
  unfold g k
  rw [ao,bo,ac,ec_comm (G := G) (B\S) (A∩S)]
  nlinarith
/-- Full endpoint, including construction of both common original pin sets. -/
theorem full_common_pins (exists_negative : ∃ M : Finset V, g q G A B M < 0) :
    Conclusion h q G A B := by
  have geometry := fun S T (hs : g q G A B S < 0) (ht : g q G A B T < 0)
    (st : ¬S ⊆ T) (ts : ¬T ⊆ S) => negative_diameter host hs ht st ts
  obtain ⟨LA,ha,ca,pa⟩ := common_left host exists_negative
  have exswap : ∃ M : Finset V, g q G B A M < 0 := by
    obtain ⟨M,hm⟩ := exists_negative
    exact ⟨univ\M,by rw [swapped_complement host]; exact hm⟩
  obtain ⟨LB,hb,cb,pb⟩ := common_left (swap host) exswap
  refine ⟨geometry,LA,LB,ha,hb,ca,cb,?_⟩
  intro M hm
  have left := pa M hm
  have right := pb (univ\M) (by rw [swapped_complement host]; exact hm)
  refine ⟨left.1,?_,left.2,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hm'
    exact (mem_sdiff.mp (right.1 hv)).2 hm'
  · intro v hv
    have degree := right.2 v hv
    have ae : A\(univ\M)=A∩M := by ext w; simp
    rwa [ae] at degree


#print axioms full_common_pins
end Erdos585.R882.Balanced
