import R898.Balanced.MinimalUnion
import R801.Main
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R898.Balanced
open QB4 B5 H3Unequal Omit1PrefixR691 GeneralSelectorR783
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {h epsilon q : ℕ} {F : ℤ}
  {A B M P S T : Finset V}
variable (host : Host h epsilon q F G A B)
include host
lemma forward_cap (neg : g q G A B M < 0)
    {v : V} (hv : v ∈ A∩M) : (dg G (B\M) v : ℤ) ≤ (q : ℤ)+(h : ℤ)-4+(epsilon : ℤ) := by
  have split := dg_sdiff_add (G := G) (inter_subset_left : B∩M ⊆ B) v
  have eq : B\(B∩M)=B\M := by ext w; simp
  rw [eq,dg_eq_degree host.bipartite (mem_inter.mp hv).1] at split
  have hc := host.cap v
  have hm := (Erdos585.R898.Balanced.negative_internal host neg).1 v (mem_inter.mp hv).2
  have deg := Erdos585.R898.Balanced.original_left_degree host M (mem_inter.mp hv).1
  rw [deg] at hm
  have hq := Erdos585.R898.Balanced.q_large host
  omega

lemma internal_B (neg : g q G A B M < 0) {v : V} (hv : v ∈ B∩M) :
    (q : ℤ)-(h : ℤ)+2-(epsilon : ℤ) ≤ dg G (A∩M) v := by
  have hm := (Erdos585.R898.Balanced.negative_internal host neg).1 v (mem_inter.mp hv).2
  have degree := Erdos585.R898.Balanced.original_left_degree
    (Erdos585.R898.Balanced.swap host) M (mem_inter.mp hv).1
  rwa [degree] at hm

omit [Fintype V] host in
/-- Exact simultaneous removal identity in the original graph. -/
lemma removal_identity (hP : P ⊆ M) :
    g q G A B P = g q G A B M + (q : ℤ)*
      ((#(A∩(M\P)) : ℤ)-#(B∩(M\P))) - ec G (A∩(M\P)) (B\M) +
        ec G (A∩P) (B∩(M\P)) := by
  have asub : A∩P ⊆ A∩M := inter_subset_inter_left hP
  have bsub : B∩P ⊆ B∩M := inter_subset_inter_left hP
  have ae : (A∩M)\(A∩P)=A∩(M\P) := by ext v; simp only [mem_sdiff,mem_inter]; tauto
  have be : (B∩M)\(B∩P)=B∩(M\P) := by ext v; simp only [mem_sdiff,mem_inter]; tauto
  have ca := card_sdiff_add_card_eq_card asub
  have cb := card_sdiff_add_card_eq_card bsub
  rw [ae] at ca
  rw [be] at cb
  have ee := ec_sdiff_add_left (G := G) asub (B\M)
  rw [ae] at ee
  have bu : B\P = (B\M) ∪ (B∩(M\P)) := by
    ext v
    simp only [mem_sdiff,mem_inter,mem_union]
    constructor
    · rintro ⟨hb,hp⟩
      by_cases hm : v ∈ M
      · exact Or.inr ⟨hb,hm,hp⟩
      · exact Or.inl ⟨hb,hm⟩
    · rintro (⟨hb,hm⟩ | ⟨hb,hm,hp⟩)
      · exact ⟨hb,fun hp => hm (hP hp)⟩
      · exact ⟨hb,hp⟩
  have bd : Disjoint (B\M) (B∩(M\P)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp hv).2 (mem_sdiff.mp (mem_inter.mp hw).2).1
  have ep := ec_union_right (G := G) (Z := A∩P) bd
  rw [← bu] at ep
  zify at ca cb ee ep
  unfold g k
  nlinarith


/-- One retained eligible cell spends the inherited floor error exactly once. -/
theorem cotiny_value_lower (neg : g q G A B M < 0)
    {a : V} (ha : a ∈ A∩M) (light : dg G (B\M) a ≤ 3*h-4)
    (hP : P ⊆ M) (avoid : a ∉ P) (tiny : #(M\P) ≤ h-1) :
    (q : ℤ)-(epsilon : ℤ)-6*(h : ℤ)+10 ≤ g q G A B P := by
  let N := insert a P
  have aA : a ∈ A := (mem_inter.mp ha).1
  have aM : a ∈ M := (mem_inter.mp ha).2
  have aB : a ∉ B := disjoint_left.mp host.disjoint aA
  have nsub : N ⊆ M := insert_subset aM hP
  have pn : P ⊆ N := subset_insert a P
  have rem : M\N = (M\P).erase a := by ext v; simp [N]; tauto
  have amr : a ∈ M\P := mem_sdiff.mpr ⟨aM,avoid⟩
  have remcard : #(M\N) ≤ h-2 := by
    rw [rem,card_erase_of_mem amr]
    have hh := host.height
    omega
  have ep := endpoint_order host neg
  have bd := negative_bounds host neg
  have mc := support_card host M
  have morder : (2*(q : ℤ)+3-(h : ℤ)) ≤ #M := by
    unfold k at bd
    zify at ep mc
    omega
  have split := card_sdiff_add_card_eq_card nsub
  have eligible : h ≤ #N := by
    have num := reserve host
    have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
    have rz : (#(M\N) : ℤ) ≤ (h : ℤ)-2 := by omega
    have qh : 3*(h : ℤ) ≤ 2*(q : ℤ)+5 := by nlinarith [sq_nonneg (h : ℤ)]
    zify at split
    have en : (h : ℤ) ≤ #N := by omega
    exact_mod_cast en
  have fp := floor host N eligible (proper_of_subset_negative host neg nsub)
  have sc := (scar_bounds host N).2.1
  have ident := cut_identity (q := q) (G := G) (A := A) (B := B) N
  have ca := card_sdiff_add_card_eq_card (inter_subset_inter_left nsub : A∩N ⊆ A∩M)
  have cb := card_sdiff_add_card_eq_card (inter_subset_inter_left nsub : B∩N ⊆ B∩M)
  have be : (B∩M)\(B∩N)=B∩(M\N) := by ext v; simp only [mem_inter,mem_sdiff]; tauto
  rw [be] at cb
  have bc := card_le_card (inter_subset_right : B∩(M\N) ⊆ M\N)
  have ac := card_le_card (inter_subset_inter_left nsub : A∩N ⊆ A∩M)
  have kn : k A B N ≤ (h : ℤ)-1+#(M\N) := by
    unfold k at bd ⊢
    zify at cb bc ac
    omega
  have forward := forward_degree_comparison (G := G) (B := B) M N a
  have loss : (dg G (B\N) a : ℤ) ≤ 3*(h : ℤ)-4+#(M\N) := by
    have hh := host.height
    omega
  have diff : N\P={a} := by ext v; simp [N,avoid]
  have aid : A∩{a}={a} := by simp [aA]
  have bid : B∩{a}=∅ := by simp [aB]
  have ri := removal_identity (q := q) (G := G) (A := A) (B := B) pn
  rw [diff,aid,bid] at ri
  simp only [card_singleton,card_empty,Nat.cast_one,Nat.cast_zero,sub_zero,
    mul_one,ec,sum_singleton,sum_empty] at ri
  have hh := host.height
  zify at remcard
  omega

/-- No floor on U is assumed; only its guarded complement inside M is used. -/
lemma outer_boundary_bound (neg : g q G A B M < 0)
    (hP : P ⊆ M) (hc : h ≤ #(M\P)) :
    (ec G P (univ\M) : ℤ) ≤ g q G A B P+k A B P+(h : ℤ)-3+(epsilon : ℤ) := by
  have fp := Erdos585.R898.Balanced.f_disjoint host
    (disjoint_sdiff_self_right : Disjoint P (M\P))
  rw [union_sdiff_of_subset hP] at fp
  have bi := Erdos585.R898.Balanced.boundary_identity host P
  have ci := Erdos585.R898.Balanced.cut_identity (q := q) (G := G) (A := A) (B := B) P
  have e1 := ec_sdiff_add_right (G := G) hP P
  have e2 := ec_sdiff_add_right (G := G) (subset_univ M) P
  have e3 := ec_sdiff_add_right (G := G) (subset_univ P) P
  have fr := Erdos585.R898.Balanced.floor host (M\P) hc
    (Erdos585.R898.Balanced.proper_of_subset_negative host neg sdiff_subset)
  have tm := (Erdos585.R898.Balanced.negative_bounds host neg).2.2.2.1
  have sc := (Erdos585.R898.Balanced.scar_bounds host P).2.2.1
  zify at e1 e2 e3
  omega

lemma incidence_bound (P : Finset V) :
    ((q : ℤ)-2)*k A B P ≤ F+g q G A B P := by
  have cp := Erdos585.R898.Balanced.cap_potential host P
  have ci := Erdos585.R898.Balanced.cut_identity (q := q) (G := G) (A := A) (B := B) P
  have sc := (Erdos585.R898.Balanced.scar_bounds host P).2.1
  nlinarith

lemma hazard_value_upper {b : V} (hb : b ∈ B) (hP : P ⊆ M)
    (light : dg G (A∩M) b ≤ 3*h-4)
    (haz : g q G A B P+1 ≤ (dg G P b : ℤ)) :
    g q G A B P ≤ 3*(h : ℤ)-5 := by
  have count : dg G P b ≤ dg G (A∩M) b := by
    unfold dg
    apply card_le_card
    intro v hv
    obtain ⟨vp,adj⟩ := mem_filter.mp hv
    have va : v ∈ A := host.bipartite.symm.mem_of_mem_adj hb adj
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨va,hP vp⟩,adj⟩
  have hh := host.height
  omega

lemma hazard_numeric :
    (h:ℤ)^2-(h:ℤ)-2 < (q:ℤ)-(epsilon:ℤ)-6*(h:ℤ)+10 ∧
    F+((h:ℤ)^2-(h:ℤ)-2) < ((q:ℤ)-2)*((h:ℤ)+1) := by
  have hh : (6:ℤ) ≤ h := by exact_mod_cast host.height
  have he : (0:ℤ) ≤ epsilon := by positivity
  have hc := host.cost_bound
  have rr := reserve host
  have phy := host.physical
  have ql := q_large host
  constructor
  · nlinarith [sq_nonneg (h:ℤ)]
  · nlinarith [sq_nonneg (h:ℤ)]

/-- Exactly 2h-2+C distinct heads contradict the original boundary charge. -/
theorem no_exact_many_hazards (neg : g q G A B M < 0)
    {a : V} (ha : a ∈ A∩M) (common : CommonLeft q G A B a)
    (light : dg G (B\M) a ≤ 3*h-4)
    (I : Finset V) (cardI : #I=2*h-2+epsilon) (heads : I ⊆ B\M)
    (headlight : ∀ b ∈ I, dg G (A∩M) b ≤ 3*h-4)
    (hazards : ∀ b ∈ I, Hazard q G A B M a b) : False := by
  have nonempty : I.Nonempty := by
    have hh := host.height
    apply card_pos.mp
    omega
  obtain ⟨cuts,hc,avoid,gu0,guLambda,vu⟩ :=
    minimal_union_bound host neg ha common I nonempty heads headlight hazards
  let U := I.biUnion cuts
  let Gamma : ℤ := ∑ b ∈ I, g q G A B (cuts b)
  change a ∉ U at avoid
  change 0 ≤ g q G A B U at gu0
  change g q G A B U ≤ (h:ℤ)^2-(h:ℤ)-2 at guLambda
  change g q G A B U ≤ Gamma at vu
  have hUM : U ⊆ M := by
    intro v hv
    obtain ⟨b,hb,hv⟩ := mem_biUnion.mp hv
    exact (hc b hb).1 hv
  have hh := host.height
  have cardZ : (#I : ℤ)=2*(h : ℤ)-2+(epsilon : ℤ) := by omega
  have rem : h ≤ #(M\U) := by
    by_contra! small
    have tiny : #(M\U) ≤ h-1 := by omega
    have lo := cotiny_value_lower host neg ha light hUM avoid tiny
    have num := (hazard_numeric host).1
    omega
  have bound := outer_boundary_bound host neg hUM rem
  have charge : Gamma+(2*(h : ℤ)-2+(epsilon : ℤ)) ≤ (ec G U (univ\M) : ℤ) := by
    have HI : I ⊆ univ\M := by
      intro v hv
      exact mem_sdiff.mpr ⟨mem_univ v,(mem_sdiff.mp (heads hv)).2⟩
    have count : Gamma+(2*(h : ℤ)-2+(epsilon : ℤ)) ≤ (ec G I U : ℤ) := by
      calc
        _ = ∑ b ∈ I, (g q G A B (cuts b)+1) := by simp [Gamma,sum_add_distrib,cardZ]
        _ ≤ ∑ b ∈ I, (dg G U b : ℤ) := sum_le_sum (fun b hb =>
          (hc b hb).2.2.trans (by exact_mod_cast (dg_mono (G := G)
            (subset_biUnion_of_mem cuts hb) b)))
        _ = _ := by simp [ec]
    have mono := ec_mono_left (G := G) HI U
    rw [ec_comm (G := G) (univ\M) U] at mono
    exact count.trans (by exact_mod_cast mono)
  have ku : (h : ℤ)+1 ≤ k A B U := by omega
  have incidence := incidence_bound host U
  have num := (hazard_numeric host).2
  have product := mul_nonneg
    (show (0 : ℤ) ≤ (q : ℤ)-2 by have nn := Erdos585.R898.Balanced.q_large host; omega)
    (show 0 ≤ k A B U-((h : ℤ)+1) by omega)
  nlinarith only [incidence,num,product,vu,guLambda]

/-- Reusable all-h exact-hazard bound with common-pin membership and bounded defects. -/
theorem exact_hazard_card (neg : g q G A B M < 0)
    {a : V} (ha : a ∈ A∩M) (common : CommonLeft q G A B a)
    (light : dg G (B\M) a ≤ 3*h-4)
    (heads : Finset V) (hheads : heads ⊆ B\M)
    (headlight : ∀ b ∈ heads, dg G (A∩M) b ≤ 3*h-4) :
    #(heads.filter (Hazard q G A B M a)) ≤ 2*h-3+epsilon := by
  by_contra! many
  have hh := host.height
  have count : 2*h-2+epsilon ≤ #(heads.filter (Hazard q G A B M a)) := by omega
  obtain ⟨I,sub,cardI⟩ := exists_subset_card_eq count
  apply no_exact_many_hazards host neg ha common light I cardI
  · exact sub.trans (filter_subset _ _ |>.trans hheads)
  · intro b hb
    exact headlight b (mem_filter.mp (sub hb)).1
  · intro b hb
    exact (mem_filter.mp (sub hb)).2

#print axioms cotiny_value_lower
#print axioms exact_hazard_card
end Erdos585.R898.Balanced
