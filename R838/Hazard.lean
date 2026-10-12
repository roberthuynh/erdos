import R838.CommonPins
import R801.Main
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.RobustBalancedSelectorR838
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
  have hm := (RobustBalancedSelectorR838.negative_internal host neg).1 v (mem_inter.mp hv).2
  have deg := RobustBalancedSelectorR838.original_left_degree host M (mem_inter.mp hv).1
  rw [deg] at hm
  have hq := RobustBalancedSelectorR838.q_large host
  omega

lemma internal_B (neg : g q G A B M < 0) {v : V} (hv : v ∈ B∩M) :
    (q : ℤ)-(h : ℤ)+2-(epsilon : ℤ) ≤ dg G (A∩M) v := by
  have hm := (RobustBalancedSelectorR838.negative_internal host neg).1 v (mem_inter.mp hv).2
  have degree := RobustBalancedSelectorR838.original_left_degree
    (RobustBalancedSelectorR838.swap host) M (mem_inter.mp hv).1
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


/-- The complementary floor is guarded by original removals, retaining all defects. -/
theorem cotiny_value_lower (neg : g q G A B M < 0)
    {a : V} (ha : a ∈ A∩M) (light : dg G (B\M) a ≤ 3*h-4)
    (hP : P ⊆ M) (avoid : a ∉ P) (tiny : #(M\P) ≤ h-1) :
    (q : ℤ)-2*(h : ℤ)^2+6-((h : ℤ)-1)*(epsilon : ℤ) ≤ g q G A B P := by
  let C := M\P
  have hac : a ∈ A∩C := mem_inter.mpr ⟨(mem_inter.mp ha).1,
    mem_sdiff.mpr ⟨(mem_inter.mp ha).2,avoid⟩⟩
  have xp : 1 ≤ #(A∩C) := card_pos.mpr ⟨a,hac⟩
  change #C ≤ h-1 at tiny
  have card := RobustBalancedSelectorR838.support_card host C
  have eaf := sum_erase_add (A∩C) (fun v => (dg G (B\M) v : ℤ)) hac
  have capsum : (∑ v ∈ (A∩C).erase a, (dg G (B\M) v : ℤ)) ≤
      ∑ _v ∈ (A∩C).erase a, ((q : ℤ)+(h : ℤ)-4+(epsilon : ℤ)) := by
    apply sum_le_sum
    intro v hv
    apply forward_cap host neg
    exact mem_inter.mpr ⟨(mem_inter.mp (mem_erase.mp hv).2).1,
      (mem_sdiff.mp (mem_inter.mp (mem_erase.mp hv).2).2).1⟩
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem hac] at capsum
  have cx : ((#(A∩C)-1 : ℕ) : ℤ) = (#(A∩C) : ℤ)-1 := by omega
  rw [cx] at capsum
  have hh := host.height
  have la : (dg G (B\M) a : ℤ) ≤ 3*(h : ℤ)-4 := by omega
  have fa : (ec G (A∩C) (B\M) : ℤ) ≤
      3*(h : ℤ)-4+((#(A∩C) : ℤ)-1)*((q : ℤ)+(h : ℤ)-4+(epsilon : ℤ)) := by
    rw [ec,Nat.cast_sum]
    nlinarith
  have lower : ((q : ℤ)-(h : ℤ)+2-(epsilon : ℤ))*#(B∩C) ≤
      (ec G (A∩M) (B∩C) : ℤ) := by
    rw [ec_comm,ec,Nat.cast_sum]
    calc
      _ = ∑ _v ∈ B∩C, ((q : ℤ)-(h : ℤ)+2-(epsilon : ℤ)) := by simp only [sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum (fun v hv => internal_B host neg
        (mem_inter.mpr ⟨(mem_inter.mp hv).1,
          (mem_sdiff.mp (mem_inter.mp hv).2).1⟩))
  have upper := QB4.ec_le_card_mul (G := G) (A∩C) (B∩C)
  have ee := ec_sdiff_add_left (G := G)
    (inter_subset_inter_left hP : A∩P ⊆ A∩M) (B∩C)
  have ae : (A∩M)\(A∩P)=A∩C := by ext v; simp only [C,mem_sdiff,mem_inter]; tauto
  rw [ae] at ee
  have id := removal_identity (q := q) (G := G) (A := A) (B := B) hP
  change g q G A B P = g q G A B M + (q : ℤ)*
    ((#(A∩C) : ℤ)-#(B∩C)) - ec G (A∩C) (B\M) + ec G (A∩P) (B∩C) at id
  have gm := RobustBalancedSelectorR838.negative_bounds host neg
  zify at ee upper card xp tiny hh
  have small : (#(A∩C) : ℤ)+#(B∩C) ≤ (h : ℤ)-1 := by omega
  have p1 := mul_nonneg (show (0 : ℤ) ≤ #(A∩C)-1 by omega)
    (show 0 ≤ 2*(h : ℤ)+(epsilon : ℤ)-((h : ℤ)-4+(epsilon : ℤ)) by omega)
  have p2 := mul_nonneg (show (0 : ℤ) ≤ #(B∩C) by positivity)
    (show 0 ≤ 2*(h : ℤ)+(epsilon : ℤ)-((h : ℤ)-2+(epsilon : ℤ)+#(A∩C)) by omega)
  have p3 := mul_nonneg (show (0 : ℤ) ≤ (h : ℤ)-2-((#(A∩C) : ℤ)-1+#(B∩C)) by omega)
    (show 0 ≤ 2*(h : ℤ)+(epsilon : ℤ) by omega)
  nlinarith only [id,fa,lower,upper,ee,gm.2.1,gm.2.2.1,p1,p2,p3]

/-- No floor on U is assumed; only its guarded complement inside M is used. -/
lemma outer_boundary_bound (neg : g q G A B M < 0)
    (hP : P ⊆ M) (hc : h ≤ #(M\P)) :
    (ec G P (univ\M) : ℤ) ≤ g q G A B P+k A B P+(h : ℤ)-3+(epsilon : ℤ) := by
  have fp := RobustBalancedSelectorR838.f_disjoint host
    (disjoint_sdiff_self_right : Disjoint P (M\P))
  rw [union_sdiff_of_subset hP] at fp
  have bi := RobustBalancedSelectorR838.boundary_identity host P
  have ci := RobustBalancedSelectorR838.cut_identity (q := q) (G := G) (A := A) (B := B) P
  have e1 := ec_sdiff_add_right (G := G) hP P
  have e2 := ec_sdiff_add_right (G := G) (subset_univ M) P
  have e3 := ec_sdiff_add_right (G := G) (subset_univ P) P
  have fr := RobustBalancedSelectorR838.floor host (M\P) hc
    (RobustBalancedSelectorR838.proper_of_subset_negative host neg sdiff_subset)
  have tm := (RobustBalancedSelectorR838.negative_bounds host neg).2.2.2.1
  have sc := (RobustBalancedSelectorR838.scar_bounds host P).2.2.1
  zify at e1 e2 e3
  omega

lemma incidence_bound (P : Finset V) :
    ((q : ℤ)-2)*k A B P ≤ F+g q G A B P := by
  have cp := RobustBalancedSelectorR838.cap_potential host P
  have ci := RobustBalancedSelectorR838.cut_identity (q := q) (G := G) (A := A) (B := B) P
  have sc := (RobustBalancedSelectorR838.scar_bounds host P).2.1
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

lemma hazard_numeric : (2*(h : ℤ)-2+(epsilon : ℤ))*(3*(h : ℤ)-5) <
      (q : ℤ)-2*(h : ℤ)^2+6-((h : ℤ)-1)*(epsilon : ℤ) ∧
    F+(2*(h : ℤ)-2+(epsilon : ℤ))*(3*(h : ℤ)-5) < ((q : ℤ)-2)*((h : ℤ)+1) := by
  have hh : (3 : ℤ) ≤ h := by exact_mod_cast host.height
  have he : (0 : ℤ) ≤ epsilon := by positivity
  have hq := reserve host
  have hr := host.range.2
  have cross := mul_nonneg (show (0 : ℤ) ≤ h by omega) he
  constructor <;> nlinarith [sq_nonneg (epsilon : ℤ)]

/-- Exactly 2h-2 distinct original heads contradict the nonsaturated boundary charge. -/
theorem no_exact_many_hazards (neg : g q G A B M < 0)
    {a : V} (ha : a ∈ A∩M) (common : CommonLeft q G A B a)
    (light : dg G (B\M) a ≤ 3*h-4)
    (I : Finset V) (cardI : #I=2*h-2+epsilon) (heads : I ⊆ B\M)
    (headlight : ∀ b ∈ I, dg G (A∩M) b ≤ 3*h-4)
    (hazards : ∀ b ∈ I, Hazard q G A B M a b) : False := by
  have chosen : ∀ b : V, ∃ P : Finset V, b ∈ I →
      P ⊆ M ∧ a ∉ P ∧ g q G A B P+1 ≤ (dg G P b : ℤ) := by
    intro b
    by_cases hb : b ∈ I
    · obtain ⟨P,hp⟩ := hazards b hb
      exact ⟨P,fun _ => hp⟩
    · exact ⟨∅,fun hn => (hb hn).elim⟩
  choose cuts hc using chosen
  let U := I.biUnion cuts
  let Gamma : ℤ := ∑ b ∈ I, g q G A B (cuts b)
  have hUM : U ⊆ M := by
    intro v hv
    obtain ⟨b,hb,hv⟩ := mem_biUnion.mp hv
    exact (hc b hb).1 hv
  have vu := union_value_bound common I cuts (fun b hb => (hc b hb).2.1)
  change a ∉ U ∧ g q G A B U ≤ Gamma at vu
  have gu0 := avoiding_nonnegative common vu.1
  have hh := host.height
  have cardZ : (#I : ℤ)=2*(h : ℤ)-2+(epsilon : ℤ) := by omega
  have gub : Gamma ≤ (2*(h : ℤ)-2+(epsilon : ℤ))*(3*(h : ℤ)-5) := by
    calc
      _ ≤ ∑ _b ∈ I, (3*(h : ℤ)-5) := sum_le_sum (fun b hb =>
        hazard_value_upper host (mem_sdiff.mp (heads hb)).1 (hc b hb).1
          (headlight b hb) (hc b hb).2.2)
      _ = _ := by simp only [sum_const,nsmul_eq_mul,cardZ]
  have rem : h ≤ #(M\U) := by
    by_contra! small
    have tiny : #(M\U) ≤ h-1 := by omega
    have lo := cotiny_value_lower host neg ha light hUM vu.1 tiny
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
    (show (0 : ℤ) ≤ (q : ℤ)-2 by have nn := RobustBalancedSelectorR838.q_large host; omega)
    (show 0 ≤ k A B U-((h : ℤ)+1) by omega)
  nlinarith only [incidence,num,product,vu.2,gub]

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
end Erdos585.RobustBalancedSelectorR838
