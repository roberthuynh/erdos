import R898.Balanced.CommonPins
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R898.Balanced
open QB4 B5 H3Unequal Omit1PrefixR691
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {h epsilon q : ℕ} {F : ℤ}
  {A B M S T : Finset V}
variable (host : Host h epsilon q F G A B)
include host
lemma low_slack_imbalance (hs : g q G A B S ≤ 3*(h:ℤ)-5) :
    k A B S ≤ (h:ℤ)-1 := by
  have cp := cap_potential host S
  have ci := cut_identity (q:=q) (G:=G) (A:=A) (B:=B) S
  have sc := (scar_bounds host S).2.1
  have hh : (6:ℤ) ≤ h := by exact_mod_cast host.height
  have he : (0:ℤ) ≤ epsilon := by positivity
  have phy := host.physical
  have cost := host.cost_bound
  have ql := q_large host
  by_contra! high
  have kh : (h:ℤ) ≤ k A B S := by omega
  have prod := mul_nonneg (show 0 ≤ (q:ℤ)-2 by omega) (show 0 ≤ k A B S-(h:ℤ) by omega)
  nlinarith [sq_nonneg (h:ℤ)]
lemma low_slack_pair_bound (hs : g q G A B S ≤ 3*(h:ℤ)-5)
    (ht : g q G A B T ≤ 3*(h:ℤ)-5) :
    f q G A B (S\T)+f q G A B (T\S) ≤ F+8*(h:ℤ)-10 := by
  have id := pair_identity host S T
  have ks := low_slack_imbalance host hs
  have kt := low_slack_imbalance host ht
  have si := (scar_bounds host (S∩T)).2.2.1
  have so := (scar_bounds host (univ\(S∪T))).1
  have e0 : (0:ℤ) ≤ ec G (S∩T) (univ\(S∪T)) := by positivity
  omega
lemma low_slack_differences_small (neg : g q G A B M < 0) (hS : S ⊆ M) (hT : T ⊆ M)
    (hs : g q G A B S ≤ 3*(h:ℤ)-5) (ht : g q G A B T ≤ 3*(h:ℤ)-5)
    (st : ¬S ⊆ T) (ts : ¬T ⊆ S) : #(S\T) ≤ h-1 ∧ #(T\S) ≤ h-1 := by
  have ps : 1 ≤ #(S\T) := card_pos.mpr (sdiff_nonempty.mpr st)
  have pt : 1 ≤ #(T\S) := card_pos.mpr (sdiff_nonempty.mpr ts)
  have properP := proper_of_subset_negative host neg ((sdiff_subset : S\T ⊆ S).trans hS)
  have properQ := proper_of_subset_negative host neg ((sdiff_subset : T\S ⊆ T).trans hT)
  have bound := low_slack_pair_bound host hs ht
  have rr := reserve host
  have hh : (6:ℤ) ≤ h := by exact_mod_cast host.height
  have gap : 8*(h:ℤ)-10+(epsilon:ℤ) < q := by nlinarith [sq_nonneg (h:ℤ)]
  have num : 2*(epsilon:ℤ)+8*(h:ℤ)-12 < F := by
    have fr := host.range
    nlinarith [sq_nonneg (h:ℤ)]
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
theorem low_slack_diameter (neg : g q G A B M < 0) (hS : S ⊆ M) (hT : T ⊆ M)
    (hs : 0 ≤ g q G A B S ∧ g q G A B S ≤ 3*(h:ℤ)-5)
    (ht : 0 ≤ g q G A B T ∧ g q G A B T ≤ 3*(h:ℤ)-5)
    (st : ¬S ⊆ T) (ts : ¬T ⊆ S) : #(S\T)+#(T\S) ≤ h-1 := by
  have small := low_slack_differences_small host neg hS hT hs.2 ht.2 st ts
  have bound := low_slack_pair_bound host hs.2 ht.2
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

#print axioms low_slack_diameter
end Erdos585.R898.Balanced
