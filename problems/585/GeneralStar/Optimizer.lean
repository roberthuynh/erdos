import GeneralStar.Closed
import Mathlib.Data.Prod.Lex

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

abbrev OptKey := ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ

def optimizerB (q s p h : ℕ) : ℕ :=
  min (2*(q-1)) (min ((q-1)+(p-s)*h) (q+s-1+p*(h-s)))
def restrictedDeficit (q s p h b : ℕ) : ℕ := (q-1)*(q+s)-(s+1)*b+p*h

def makeOptKey (q s p h b : ℕ) : OptKey :=
  toLex (restrictedDeficit q s p h b,toLex (q+s+b,toLex (s,toLex (p,toLex (h,b)))))
def OptKey.deficit (k : OptKey) : ℕ := (ofLex k).1
def OptKey.start (k : OptKey) : ℕ := (ofLex (ofLex k).2).1
def OptKey.s (k : OptKey) : ℕ := (ofLex (ofLex (ofLex k).2).2).1
def OptKey.p (k : OptKey) : ℕ := (ofLex (ofLex (ofLex (ofLex k).2).2).2).1
def OptKey.h (k : OptKey) : ℕ := (ofLex (ofLex (ofLex (ofLex (ofLex k).2).2).2).2).1
def OptKey.b (k : OptKey) : ℕ := (ofLex (ofLex (ofLex (ofLex (ofLex k).2).2).2).2).2

def OptimizerDomain (q s p h : ℕ) : Prop :=
  1 ≤ s ∧ s ≤ q-2 ∧ s+1 ≤ p ∧ p ≤ q+s ∧ s+1 ≤ h ∧ h ≤ 2*(q-1) ∧
    max (q+s) (max (p*h) ((q-1)+h)) ≤ optimizerB q s p h
instance (q s p h : ℕ) : Decidable (OptimizerDomain q s p h) := by
  unfold OptimizerDomain;infer_instance

def optimizerKeys (q : ℕ) : Finset OptKey :=
  (range (q-1)).biUnion fun s => (range (q+s+1)).biUnion fun p =>
    (((range (2*(q-1)+1)).filter (OptimizerDomain q s p)).image fun h =>
      makeOptKey q s p h (optimizerB q s p h))

noncomputable def optimizerKey (q : ℕ) : OptKey :=
  if hn : (optimizerKeys q).Nonempty then (optimizerKeys q).min' hn else
    makeOptKey q 0 0 0 0
noncomputable def optimizerTuple (q : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((optimizerKey q).s,(optimizerKey q).p,(optimizerKey q).h,(optimizerKey q).b)
noncomputable def optimumStart (q : ℕ) : ℕ := (optimizerKey q).start
noncomputable def optimumDeficit (q : ℕ) : ℕ := (optimizerKey q).deficit
noncomputable def optimumFamily (q n : ℕ) : GraphData :=
  uniformFamily q (optimizerKey q).s (optimizerKey q).p (optimizerKey q).h (optimizerKey q).b n

theorem optimizer_to_U (q s p h : ℕ) (hq : 7 ≤ q) (ho : OptimizerDomain q s p h) :
    UParams q s p h (optimizerB q s p h) := by
  rcases ho with ⟨hs,_hsq,hps,hpa,hhs,_hhr,hmin⟩
  have ha : q+s ≤ optimizerB q s p h := (le_max_left _ _).trans hmin
  have hp : p*h ≤ optimizerB q s p h := (le_max_left _ _).trans ((le_max_right _ _).trans hmin)
  have hh : q-1+h ≤ optimizerB q s p h := (le_max_right _ _).trans ((le_max_right _ _).trans hmin)
  have hb : optimizerB q s p h ≤ 2*(q-1) := min_le_left _ _
  have hf : optimizerB q s p h ≤ (q-1)+(p-s)*h := (min_le_right _ _).trans (min_le_left _ _)
  have hl : optimizerB q s p h ≤ q+s-1+p*(h-s) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hs,hps,hhs,hpa,ha,hb,hp,?_,?_,?_⟩ <;> omega

theorem U_to_optimizer (q s p h b : ℕ) (hq : 7 ≤ q) (hu : UParams q s p h b) :
    OptimizerDomain q s p h ∧ b ≤ optimizerB q s p h := by
  rcases hu with ⟨hs,hps,hhs,hpa,ha,hb,hp,hr,hf,hl⟩
  have hbq : q ≤ b := by omega
  have hbs : q+s ≤ b := ha
  have hb0 : b ≤ optimizerB q s p h := by
    unfold optimizerB
    apply le_min hb
    apply le_min <;> omega
  have hsmall : s ≤ q-2 := by omega
  have hhr : h ≤ 2*(q-1) := by
    have hple : h ≤ p*h := by nlinarith
    omega
  refine ⟨⟨hs,hsmall,hps,hpa,hhs,hhr,?_⟩,hb0⟩
  apply max_le
  · exact ha.trans hb0
  · apply max_le
    · exact hp.trans hb0
    · have hg : q-1+h ≤ b := by omega
      exact hg.trans hb0

theorem restricted_eq_uniform (q s p h b : ℕ) (hq : 5 ≤ q) (hu : UParams q s p h b) :
    restrictedDeficit q s p h b=uniformDeficit q s p h b := by
  rcases hu with ⟨_hs,_hps,_hhs,_hpa,ha,hb,_hp,_hr,_hf,_hl⟩
  have hqsub : q-1+1=q := by omega
  have hsr : s+1 ≤ q-1 := by omega
  have hmul := Nat.mul_le_mul_left (s+1) hb
  have hneed : (s+1)*b ≤ (q-1)*(q+s) := by nlinarith
  have hsub : (q-1)*(q+s)-(s+1)*b+(s+1)*b=(q-1)*(q+s) := by omega
  have he : (q-1)*(q+s+b)=(q+s)*b+((q-1)*(q+s)-(s+1)*b) := by nlinarith
  unfold restrictedDeficit uniformDeficit
  rw [he,Nat.add_sub_cancel_left]

theorem optimizer_key_mem (q s p h : ℕ) (hq : 7 ≤ q) (ho : OptimizerDomain q s p h) :
    makeOptKey q s p h (optimizerB q s p h) ∈ optimizerKeys q := by
  rcases ho with ⟨hs,hsq,hps,hpa,hhs,hhr,hmin⟩
  apply mem_biUnion.mpr
  refine ⟨s,mem_range.mpr (by omega),mem_biUnion.mpr ?_⟩
  refine ⟨p,mem_range.mpr (by omega),mem_image.mpr ?_⟩
  exact ⟨h,mem_filter.mpr ⟨mem_range.mpr (by omega),⟨hs,hsq,hps,hpa,hhs,hhr,hmin⟩⟩,rfl⟩

theorem optimizer_mem_iff (q : ℕ) (k : OptKey) : k ∈ optimizerKeys q ↔
    ∃ s p h, OptimizerDomain q s p h ∧ k=makeOptKey q s p h (optimizerB q s p h) := by
  constructor
  · intro hk
    obtain ⟨s,_,hsk⟩ := mem_biUnion.mp hk
    obtain ⟨p,_,hpk⟩ := mem_biUnion.mp hsk
    obtain ⟨h,hh,hke⟩ := mem_image.mp hpk
    exact ⟨s,p,h,(mem_filter.mp hh).2,hke.symm⟩
  · rintro ⟨s,p,h,ho,rfl⟩
    rcases ho with ⟨hs,hsq,hps,hpa,hhs,hhr,hmin⟩
    apply mem_biUnion.mpr
    refine ⟨s,mem_range.mpr (by omega),mem_biUnion.mpr ?_⟩
    refine ⟨p,mem_range.mpr (by omega),mem_image.mpr ?_⟩
    exact ⟨h,mem_filter.mpr ⟨mem_range.mpr (by omega),⟨hs,hsq,hps,hpa,hhs,hhr,hmin⟩⟩,rfl⟩

theorem optimizer_nonempty (q : ℕ) (hq : 7 ≤ q) : (optimizerKeys q).Nonempty := by
  have hd := (U_to_optimizer q (closedS q) (closedP q) (closedH q) (closedB q) hq
    (closed_params q hq)).1
  exact ⟨_,optimizer_key_mem q (closedS q) (closedP q) (closedH q) hq hd⟩

theorem optimizerKey_mem (q : ℕ) (hq : 7 ≤ q) : optimizerKey q ∈ optimizerKeys q := by
  have hn := optimizer_nonempty q hq
  unfold optimizerKey
  rw [dif_pos hn]
  exact min'_mem _ hn

/-- The actual selected key is the first element of the ascending six-coordinate lex sort. -/
theorem optimizerKey_sorted (q : ℕ) (hq : 7 ≤ q) :
    optimizerKey q=(optimizerKeys q).sort[0]'(by rw [length_sort];exact card_pos.mpr (optimizer_nonempty q hq)) := by
  unfold optimizerKey
  rw [dif_pos (optimizer_nonempty q hq)]
  exact min'_eq_sorted_zero

theorem optimizerKey_spec (q : ℕ) (hq : 7 ≤ q) :
    UParams q (optimizerKey q).s (optimizerKey q).p (optimizerKey q).h (optimizerKey q).b ∧
    (optimizerKey q).start=q+(optimizerKey q).s+(optimizerKey q).b ∧
    (optimizerKey q).deficit=uniformDeficit q (optimizerKey q).s (optimizerKey q).p (optimizerKey q).h (optimizerKey q).b := by
  obtain ⟨s,p,h,ho,he⟩ := (optimizer_mem_iff q _).mp (optimizerKey_mem q hq)
  rw [he]
  change UParams q s p h (optimizerB q s p h) ∧
    q+s+optimizerB q s p h=q+s+optimizerB q s p h ∧
    restrictedDeficit q s p h (optimizerB q s p h)=uniformDeficit q s p h (optimizerB q s p h)
  have hu := optimizer_to_U q s p h hq ho
  exact ⟨hu,rfl,restricted_eq_uniform q s p h _ (by omega) hu⟩

/-- O24: the deterministic finite restricted seed optimizer, transported at every later order. -/
theorem o24 (q n : ℕ) (hq : 7 ≤ q) (hn : optimumStart q ≤ n) :
    FamilyConclusion q n (optimumDeficit q) (optimumFamily q n) := by
  obtain ⟨hu,ho,hc⟩ := optimizerKey_spec q hq
  have ht := u24 q (optimizerKey q).s (optimizerKey q).p (optimizerKey q).h (optimizerKey q).b n
    (by omega) hu (by change (optimizerKey q).start ≤ n at hn;omega)
  change FamilyConclusion q n (optimizerKey q).deficit _
  rw [hc]
  exact ht

theorem o24_start (q : ℕ) (hq : 7 ≤ q) : optimumStart q ≤ 4*q-4 := by
  obtain ⟨hu,ho,_hc⟩ := optimizerKey_spec q hq
  change (optimizerKey q).start ≤ 4*q-4
  rcases hu with ⟨_hs,_hps,_hhs,_hpa,ha,hb,_hp,_hr,_hf,_hl⟩
  omega

theorem closed_uniform_deficit (q : ℕ) (hq : 7 ≤ q) :
    uniformDeficit q (closedS q) (closedP q) (closedH q) (closedB q)=closedDeficit q := by
  by_cases hq7 : q=7
  · subst q;norm_num [uniformDeficit,closedS,closedP,closedH,closedB,closedDeficit]
  by_cases hq8 : q=8
  · subst q;norm_num [uniformDeficit,closedS,closedP,closedH,closedB,closedDeficit]
  exact closed_uniform_deficit_ge9 q (by omega)

theorem o24_compare (q : ℕ) (hq : 7 ≤ q) : optimumDeficit q ≤ closedDeficit q := by
  have hu := closed_params q hq
  have hdom := U_to_optimizer q (closedS q) (closedP q) (closedH q) (closedB q) hq hu
  have hkey := optimizer_key_mem q (closedS q) (closedP q) (closedH q) hq hdom.1
  have hmin : optimizerKey q ≤ makeOptKey q (closedS q) (closedP q) (closedH q)
      (optimizerB q (closedS q) (closedP q) (closedH q)) := by
    unfold optimizerKey
    rw [dif_pos (optimizer_nonempty q hq)]
    exact min'_le _ _ hkey
  have hfirst := Prod.Lex.monotone_fst _ _ hmin
  change optimumDeficit q ≤ restrictedDeficit q (closedS q) (closedP q) (closedH q)
    (optimizerB q (closedS q) (closedP q) (closedH q)) at hfirst
  have hmono : restrictedDeficit q (closedS q) (closedP q) (closedH q)
      (optimizerB q (closedS q) (closedP q) (closedH q)) ≤
      restrictedDeficit q (closedS q) (closedP q) (closedH q) (closedB q) := by
    have hm := Nat.mul_le_mul_left (closedS q+1) hdom.2
    unfold restrictedDeficit
    exact Nat.add_le_add_right (Nat.sub_le_sub_left hm _) _
  have he := restricted_eq_uniform q (closedS q) (closedP q) (closedH q) (closedB q) (by omega) hu
  rw [he,closed_uniform_deficit q hq] at hmono
  exact hfirst.trans hmono

end Erdos585.GeneralStar
