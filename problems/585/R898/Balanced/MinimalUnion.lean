import R898.Balanced.LowSlack
import R801.Main
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R898.Balanced
open QB4 B5 H3Unequal Omit1PrefixR691 GeneralSelectorR783
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {h epsilon q : ℕ} {F : ℤ}
  {A B M P : Finset V}
variable (host : Host h epsilon q F G A B)

def MinimalWitness (M : Finset V) (a b : V) (P : Finset V) : Prop :=
  P ⊆ M ∧ a ∉ P ∧ g q G A B P+1 ≤ (dg G P b : ℤ) ∧
    ∀ Q : Finset V, Q ⊂ P → (dg G Q b : ℤ) ≤ g q G A B Q

omit [Fintype V] in
lemma exists_minimal_witness {a b : V} (haz : Hazard q G A B M a b) :
    ∃ P : Finset V, MinimalWitness (q := q) (G := G) (A := A) (B := B) M a b P := by
  let family := M.powerset.filter (fun P => a ∉ P ∧ g q G A B P+1 ≤ (dg G P b : ℤ))
  have nonempty : family.Nonempty := by
    obtain ⟨P,hp,ha,hg⟩ := haz
    exact ⟨P,mem_filter.mpr ⟨mem_powerset.mpr hp,ha,hg⟩⟩
  obtain ⟨P,hp,least⟩ := exists_min_image family (fun P : Finset V => #P) nonempty
  have data := mem_filter.mp hp
  refine ⟨P,mem_powerset.mp data.1,data.2.1,data.2.2,?_⟩
  intro Q sub
  by_contra! bad
  have hq : Q ∈ family := mem_filter.mpr ⟨mem_powerset.mpr
    (sub.1.trans (mem_powerset.mp data.1)),fun ha => data.2.1 (sub.1 ha),by omega⟩
  have sz := least Q hq
  have lt := card_lt_card sub
  omega

omit [Fintype V] in
lemma witness_erase_failure {a b v : V}
    (minimal : MinimalWitness (q := q) (G := G) (A := A) (B := B) M a b P)
    (hv : v ∈ P) : (dg G (P.erase v) b : ℤ) ≤ g q G A B (P.erase v) :=
  minimal.2.2.2 _ (erase_ssubset hv)

include host
/-- Removing one A vertex loses at most one unit of head incidence. -/
lemma witness_left_marginal {a b v : V} (_hb : b ∈ B)
    (minimal : MinimalWitness (q := q) (G := G) (A := A) (B := B) M a b P)
    (hv : v ∈ A∩P) : (dg G (B\P) v : ℤ) ≤ q := by
  have vp := (mem_inter.mp hv).2
  have va := (mem_inter.mp hv).1
  have vb : v ∉ B := disjoint_left.mp host.disjoint va
  have failure := witness_erase_failure minimal vp
  have id := GeneralSelectorR783.removal_identity (q := q) (G := G) (A := A) (B := B)
    (erase_subset v P)
  have diff : P\P.erase v={v} := by
    ext w
    by_cases eq : w=v <;> simp [eq,vp]
  have aa : A∩{v}={v} := by simp [va]
  have bb : B∩{v}=∅ := by simp [vb]
  rw [diff,aa,bb] at id
  simp only [card_singleton,card_empty,Nat.cast_one,Nat.cast_zero,sub_zero,mul_one,
    ec,sum_singleton] at id
  have dz : ∀ w : V, dg G ∅ w=0 := by intro w; simp [dg]
  simp only [dz,sum_const_zero,Nat.cast_zero,add_zero] at id
  have degree := dg_difference_bound (G := G) P (P.erase v) b
  have singleton : #(P\P.erase v)=1 := by rw [diff]; simp
  rw [singleton] at degree
  have haz := minimal.2.2.1
  omega

/-- Removing a B vertex leaves same-shore head incidence unchanged. -/
lemma witness_right_internal {a b v : V} (hb : b ∈ B)
    (minimal : MinimalWitness (q := q) (G := G) (A := A) (B := B) M a b P)
    (hv : v ∈ B∩P) : (q : ℤ)+1 ≤ dg G (A∩P) v := by
  have vp := (mem_inter.mp hv).2
  have vb := (mem_inter.mp hv).1
  have va : v ∉ A := disjoint_left.mp host.disjoint.symm vb
  have failure := witness_erase_failure minimal vp
  have same : dg G (P.erase v) b=dg G P b := by
    unfold dg
    congr 1
    ext w
    simp only [mem_filter,mem_erase]
    constructor
    · tauto
    · rintro ⟨wp,adj⟩
      have wa := host.bipartite.symm.mem_of_mem_adj hb adj
      exact ⟨⟨fun eq => va (eq ▸ wa),wp⟩,adj⟩
  rw [same] at failure
  have id := GeneralSelectorR783.removal_identity (q := q) (G := G) (A := A) (B := B)
    (erase_subset v P)
  have diff : P\P.erase v={v} := by
    ext w
    by_cases eq : w=v <;> simp [eq,vp]
  have aa : A∩{v}=∅ := by simp [va]
  have bb : B∩{v}={v} := by simp [vb]
  have ae : A∩P.erase v=A∩P := by
    ext w
    simp only [mem_inter,mem_erase]
    constructor
    · tauto
    · rintro ⟨wa,wp⟩
      exact ⟨wa,fun eq => va (eq ▸ wa),wp⟩
  rw [diff,aa,bb,ae] at id
  rw [ec_comm (G := G) (A∩P) {v}] at id
  simp only [card_singleton,card_empty,Nat.cast_one,Nat.cast_zero,zero_sub,mul_neg,mul_one,
    ec,sum_singleton,sum_empty] at id
  simp only [sub_zero] at id
  have haz := minimal.2.2.1
  omega

lemma minimal_slack_upper {a b : V} (hb : b ∈ B)
    (minimal : MinimalWitness (q := q) (G := G) (A := A) (B := B) M a b P)
    (light : dg G (A∩M) b ≤ 3*h-4) : g q G A B P ≤ 3*(h : ℤ)-5 := by
  have count : dg G P b ≤ dg G (A∩M) b := by
    unfold dg
    apply card_le_card
    intro v hv
    obtain ⟨vp,adj⟩ := mem_filter.mp hv
    have va := host.bipartite.symm.mem_of_mem_adj hb adj
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨va,minimal.1 vp⟩,adj⟩
  have hh := host.height
  have haz := minimal.2.2.1
  omega

/-- The entire original union spends the boundary of one largest witness. -/
theorem minimal_cuts_union_bound (neg : g q G A B M < 0)
    {a : V} (common : CommonLeft q G A B a)
    (I : Finset V) (nonempty : I.Nonempty) (heads : I ⊆ B\M)
    (headlight : ∀ b ∈ I, dg G (A∩M) b ≤ 3*h-4)
    (cuts : V → Finset V)
    (hc : ∀ b ∈ I, MinimalWitness (q := q) (G := G) (A := A) (B := B) M a b (cuts b)) :
    a ∉ I.biUnion cuts ∧ 0 ≤ g q G A B (I.biUnion cuts) ∧
    g q G A B (I.biUnion cuts) ≤ (h : ℤ)^2-(h : ℤ)-2 ∧
    g q G A B (I.biUnion cuts) ≤ ∑ b ∈ I, g q G A B (cuts b) := by
  let U := I.biUnion cuts
  obtain ⟨b0,hb0,maximal⟩ := exists_max_image I (fun b => #(cuts b)) nonempty
  let P0 := cuts b0
  let Z := B∩(U\P0)
  have P0U : P0 ⊆ U := subset_biUnion_of_mem cuts hb0
  have slack : ∀ b ∈ I, 0 ≤ g q G A B (cuts b) ∧ g q G A B (cuts b) ≤ 3*(h : ℤ)-5 := by
    intro b hb
    exact ⟨avoiding_nonnegative common (hc b hb).2.1,
      minimal_slack_upper host (mem_sdiff.mp (heads hb)).1 (hc b hb) (headlight b hb)⟩
  have slack0 := slack b0 hb0
  have k0 := low_slack_imbalance host slack0.2
  change 0 ≤ g q G A B P0 ∧ g q G A B P0 ≤ 3*(h : ℤ)-5 at slack0
  change k A B P0 ≤ (h : ℤ)-1 at k0
  have newB : ∀ y ∈ Z, (q : ℤ)-(h : ℤ)+3 ≤ dg G (A∩P0) y := by
    intro y hy
    obtain ⟨yb,yrest⟩ := mem_inter.mp hy
    obtain ⟨yu,yn⟩ := mem_sdiff.mp yrest
    obtain ⟨b,hb,yp⟩ := mem_biUnion.mp yu
    have st : ¬cuts b ⊆ P0 := fun sub => yn (sub yp)
    have ts : ¬P0 ⊆ cuts b := by
      intro sub
      have eq : P0=cuts b := eq_of_subset_of_card_le sub (maximal b hb)
      exact st (by rw [← eq])
    have diameter := low_slack_diameter host neg (hc b hb).1 (hc b0 hb0).1
      (slack b hb) slack0 st ts
    change #(cuts b\P0)+#(P0\cuts b) ≤ h-1 at diameter
    have other : 1 ≤ #(P0\cuts b) := card_pos.mpr (sdiff_nonempty.mpr ts)
    have bound : #((A∩cuts b)\(A∩P0)) ≤ h-2 := by
      have sub : (A∩cuts b)\(A∩P0) ⊆ cuts b\P0 := by
        intro v hv
        simp only [mem_sdiff,mem_inter] at hv ⊢
        tauto
      have le := card_le_card sub
      omega
    have internal := witness_right_internal host (mem_sdiff.mp (heads hb)).1 (hc b hb)
      (mem_inter.mpr ⟨yb,yp⟩)
    have compare := dg_difference_bound (G := G) (A∩cuts b) (A∩P0) y
    have hh := host.height
    omega
  have charge : ((q : ℤ)-(h : ℤ)+3)*#Z ≤ (ec G (A∩P0) Z : ℤ) := by
    rw [ec_comm (G := G) (A∩P0) Z]
    calc
      _ = ∑ _y ∈ Z, ((q : ℤ)-(h : ℤ)+3) := by simp [mul_comm]
      _ ≤ ∑ y ∈ Z, (dg G (A∩P0) y : ℤ) := sum_le_sum newB
      _ = _ := by simp [ec]
  have zsub : Z ⊆ B\P0 := by
    intro y hy
    exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1,(mem_sdiff.mp (mem_inter.mp hy).2).2⟩
  have boundary := ec_mono_right (G := G) (A∩P0) zsub
  have boundaryZ : (ec G (A∩P0) Z : ℤ) ≤ ec G (A∩P0) (B\P0) := by exact_mod_cast boundary
  have capboundary : (ec G (A∩P0) Z : ℤ) ≤ (q : ℤ)*((h : ℤ)-1)+3*(h : ℤ)-5 := by
    have id : (ec G (A∩P0) (B\P0) : ℤ)=(q : ℤ)*k A B P0+g q G A B P0 := by unfold g; ring
    have mul := mul_le_mul_of_nonneg_left k0 (show (0 : ℤ) ≤ q by positivity)
    rw [id] at boundaryZ
    omega
  have hh : (6 : ℤ) ≤ h := by exact_mod_cast host.height
  have reserve := Erdos585.R898.Balanced.reserve host
  have zp : (0 : ℤ) ≤ (q : ℤ)-(h : ℤ)+3 := by nlinarith [sq_nonneg (h : ℤ)]
  have smallZ : #Z ≤ h-1 := by
    by_contra! large
    have zlarge : (h : ℤ) ≤ #Z := by omega
    have mul := mul_le_mul_of_nonneg_left zlarge zp
    nlinarith [sq_nonneg (h : ℤ)]
  have leftcharge : (ec G (A∩(U\P0)) (B\U) : ℤ) ≤ (q : ℤ)*#(A∩(U\P0)) := by
    calc
      _ = ∑ x ∈ A∩(U\P0), (dg G (B\U) x : ℤ) := by simp [ec]
      _ ≤ ∑ _x ∈ A∩(U\P0), (q : ℤ) := by
        apply sum_le_sum
        intro x hx
        have xa := (mem_inter.mp hx).1
        have xu := (mem_sdiff.mp (mem_inter.mp hx).2).1
        obtain ⟨b,hb,xp⟩ := mem_biUnion.mp xu
        have marginal := witness_left_marginal host (mem_sdiff.mp (heads hb)).1
          (hc b hb) (mem_inter.mpr ⟨xa,xp⟩)
        have sub : B\U ⊆ B\cuts b := sdiff_subset_sdiff Subset.rfl (subset_biUnion_of_mem cuts hb)
        have mono := dg_mono (G := G) sub x
        omega
      _ = _ := by simp [mul_comm]
  -- One simultaneous identity combines all B additions and the nonpositive A additions.
  have removal := GeneralSelectorR783.removal_identity (q := q) (G := G) (A := A) (B := B) P0U
  have unionbound : g q G A B U ≤ (h : ℤ)^2-(h : ℤ)-2 := by
    have sz : (#Z : ℤ) ≤ (h : ℤ)-1 := by omega
    have prod := mul_nonneg (show (0 : ℤ) ≤ (h : ℤ)-3 by omega)
      (show (0 : ℤ) ≤ (h : ℤ)-1-(#Z : ℤ) by omega)
    change g q G A B P0 = g q G A B U + (q : ℤ)*
      ((#(A∩(U\P0)) : ℤ)-#Z) - ec G (A∩(U\P0)) (B\U) +
        ec G (A∩P0) Z at removal
    nlinarith only [removal,leftcharge,charge,slack0.2,prod]
  have vu := union_value_bound common I cuts (fun b hb => (hc b hb).2.1)
  exact ⟨vu.1,avoiding_nonnegative common vu.1,unionbound,vu.2⟩

/-- Minimal choices retain both the quadratic union bound and the independent sum bound. -/
theorem minimal_union_bound (neg : g q G A B M < 0)
    {a : V} (_ha : a ∈ A∩M) (common : CommonLeft q G A B a)
    (I : Finset V) (nonempty : I.Nonempty) (heads : I ⊆ B\M)
    (headlight : ∀ b ∈ I, dg G (A∩M) b ≤ 3*h-4)
    (hazards : ∀ b ∈ I, Hazard q G A B M a b) :
    ∃ cuts : V → Finset V,
      (∀ b ∈ I, cuts b ⊆ M ∧ a ∉ cuts b ∧ g q G A B (cuts b)+1 ≤ (dg G (cuts b) b : ℤ)) ∧
      a ∉ I.biUnion cuts ∧ 0 ≤ g q G A B (I.biUnion cuts) ∧
      g q G A B (I.biUnion cuts) ≤ (h : ℤ)^2-(h : ℤ)-2 ∧
      g q G A B (I.biUnion cuts) ≤ ∑ b ∈ I, g q G A B (cuts b) := by
  have chosen : ∀ b : V, ∃ P : Finset V, b ∈ I →
      MinimalWitness (q := q) (G := G) (A := A) (B := B) M a b P := by
    intro b
    by_cases hb : b ∈ I
    · obtain ⟨P,hp⟩ := exists_minimal_witness (hazards b hb)
      exact ⟨P,fun _ => hp⟩
    · exact ⟨∅,fun hn => (hb hn).elim⟩
  choose cuts hc using chosen
  refine ⟨cuts,?_,minimal_cuts_union_bound host neg common I nonempty heads headlight cuts hc⟩
  intro b hb
  exact ⟨(hc b hb).1,(hc b hb).2.1,(hc b hb).2.2.1⟩

#print axioms minimal_union_bound
#print axioms witness_left_marginal
#print axioms witness_right_internal
end Erdos585.R898.Balanced
