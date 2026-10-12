import GeneralStar.Parameters
import GeneralStar.HCqSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

def edgeCount (D : GraphData) : ℕ := D.graph.edgeFinset.card

theorem closed_seedHyp (q : ℕ) (hq : 5 ≤ q) : SeedHyp q (closedSeed q) := by
  by_cases hlow : q=5 ∨ q=6
  · simp only [closedSeed,if_pos hlow]
    exact hcq_seedHyp q hq
  · simp only [closedSeed,if_neg hlow]
    exact uniform_seedHyp q (closedS q) (closedP q) (closedH q) (closedB q) hq
      (closed_params q (by omega))

theorem closed_order (q : ℕ) : (closedSeed q).order=closedStart q := by
  by_cases hlow : q=5 ∨ q=6
  · simp only [closedSeed,closedStart,if_pos hlow]
    exact hcq_order q
  · simp only [closedSeed,closedStart,if_neg hlow]
    exact uniform_order q (closedS q) (closedP q) (closedH q) (closedB q)

theorem closed_uniform_deficit_ge9 (q : ℕ) (hq : 9 ≤ q) :
    uniformDeficit q (closedS q) (closedP q) (closedH q) (closedB q)=closedDeficit q := by
  have hq7 : ¬ (q=7 ∨ q=8) := by omega
  have hq7' : q ≠ 7 := by omega
  have hq8 : q ≠ 8 := by omega
  have hlow : ¬ (q=5 ∨ q=6) := by omega
  obtain ⟨hd,hl,_hu⟩ := closedD_bounds q hq
  let d := closedD q
  let r := q-1
  have hr : r+1=q := by dsimp [r];omega
  have hdr : 2*d^2 ≤ r := hl
  have hd' : 2 ≤ d := hd
  have hparams := closed_params_ge9 q hq
  have he := uniform_edges q (closedS q) (closedP q) (closedH q) (closedB q) hparams
  have heD := uniform_deficit q (closedS q) (closedP q) (closedH q) (closedB q) (by omega) hparams
  rw [← heD]
  change (q-1)*(uniformSeed q (closedS q) (closedP q) (closedH q) (closedB q)).order-edgeCount (uniformSeed q (closedS q) (closedP q) (closedH q) (closedB q))=closedDeficit q
  change edgeCount (uniformSeed q (closedS q) (closedP q) (closedH q) (closedB q))+(closedP q)*(closedH q)=(q+closedS q)*(closedB q) at he
  by_cases hex : exceptional q
  · simp only [closedS,closedP,closedH,closedB,closedDeficit,if_neg hq7,if_neg hq7',if_neg hq8,
      if_neg hlow,if_pos hex] at he ⊢
    change r*(uniformSeed q d (2*d) (2*d) (r+2*d^2)).order-
      edgeCount (uniformSeed q d (2*d) (2*d) (r+2*d^2))=r^2-2*d^2*(d-1)
    rw [uniform_order]
    have hdl : d-1 ≤ r := by
      have hdl' : d ≤ r := by nlinarith only [hdr,hd']
      omega
    have hc : 2*d^2*(d-1) ≤ r^2 := by
      have hm := Nat.mul_le_mul hdr hdl
      simpa only [pow_two] using hm
    have hsub : r^2-2*d^2*(d-1)+2*d^2*(d-1)=r^2 := by omega
    have hdsub : d-1+1=d := by omega
    have hadd : edgeCount (uniformSeed q d (2*d) (2*d) (r+2*d^2))+
        (r^2-2*d^2*(d-1))=r*(q+d+(r+2*d^2)) := by
      change edgeCount (uniformSeed q d (2*d) (2*d) (r+2*d^2))+(2*d)*(2*d)=
        (q+d)*(r+2*d^2) at he
      nlinarith only [hr,hsub,hdsub,he]
    omega
  · simp only [closedS,closedP,closedH,closedB,closedDeficit,if_neg hq7,if_neg hq7',if_neg hq8,
      if_neg hlow,if_neg hex] at he ⊢
    let p := max (d+ceilDiv r (2*d)) (ceilDiv r d-1)
    change r*(uniformSeed q d p (2*d) (2*r)).order-
      edgeCount (uniformSeed q d p (2*d) (2*r))=r^2-r*(d+1)+2*d*p
    rw [uniform_order]
    have hdl : d+1 ≤ r := by nlinarith
    have hc : r*(d+1) ≤ r^2 := by
      have hm := Nat.mul_le_mul_left r hdl
      simpa only [pow_two] using hm
    have hsub : r^2-r*(d+1)+r*(d+1)=r^2 := by omega
    have hadd : edgeCount (uniformSeed q d p (2*d) (2*r))+
        (r^2-r*(d+1)+2*d*p)=r*(q+d+2*r) := by
      change edgeCount (uniformSeed q d p (2*d) (2*r))+p*(2*d)=(q+d)*(2*r) at he
      nlinarith only [hr,hsub,he]
    omega

theorem closed_deficit (q : ℕ) (hq : 5 ≤ q) :
    (q-1)*(closedSeed q).order-(closedSeed q).graph.edgeFinset.card=closedDeficit q := by
  change (q-1)*(closedSeed q).order-edgeCount (closedSeed q)=closedDeficit q
  by_cases hlow : q=5 ∨ q=6
  · simp only [closedSeed,closedDeficit,if_pos hlow]
    exact hcq_deficit q hq
  · simp only [closedSeed,if_neg hlow]
    change (q-1)*(uniformSeed q (closedS q) (closedP q) (closedH q) (closedB q)).order-(uniformSeed q (closedS q) (closedP q) (closedH q) (closedB q)).graph.edgeFinset.card=closedDeficit q
    rw [uniform_deficit q (closedS q) (closedP q) (closedH q) (closedB q) hq
      (closed_params q (by omega))]
    by_cases hq7 : q=7
    · subst q
      norm_num [uniformDeficit,closedS,closedP,closedH,closedB,closedDeficit]
    by_cases hq8 : q=8
    · subst q
      norm_num [uniformDeficit,closedS,closedP,closedH,closedB,closedDeficit]
    exact closed_uniform_deficit_ge9 q (by omega)

/-- The bare graph-valued C24 endpoint: all seed facts and startup guards are internal. -/
theorem c24_state (q t : ℕ) (hq : 5 ≤ q) :
    FamilyConclusion q (closedStart q+t) (closedDeficit q) (closedState q t) := by
  have ht := T24 q (closedSeed q) hq (closed_seedHyp q hq) t
  rw [closed_deficit q hq,closed_order] at ht
  exact ht

theorem c24 (q n : ℕ) (hq : 5 ≤ q) (hn : closedStart q ≤ n) :
    FamilyConclusion q n (closedDeficit q) (closedFamily q n) := by
  have ht := c24_state q (n-closedStart q) hq
  have he : closedStart q+(n-closedStart q)=n := by omega
  simpa only [he,closedFamily] using ht

theorem c24_endpoint : C24Endpoint := c24

/- -/
theorem t24 (q : ℕ) (D : GraphData) (hq : 5 ≤ q) (hs : SeedHyp q D) (t : ℕ) :
    (transferState q D t).order=D.order+t ∧
    (transferState q D t).graph.IsBipartite ∧
    (∀ v,q-1 ≤ (transferState q D t).graph.degree v) ∧
    (transferState q D t).graph.maxDegree ≤ 2*q-2 ∧
    (transferState q D t).graph.edgeFinset.card=D.graph.edgeFinset.card+(q-1)*t ∧
    ¬(∃ H : (transferState q D t).graph.Subgraph,H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) := by
  have ht := T24 q D hq hs t
  exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,transfer_edges q D hq hs t,ht.2.2.2.2.2⟩

theorem u24 (q s p h b n : ℕ) (hq : 5 ≤ q) (hp : UParams q s p h b)
    (hn : q+s+b ≤ n) :
    FamilyConclusion q n (uniformDeficit q s p h b) (uniformFamily q s p h b n) :=
  U24 q s p h b n hq hp hn

end Erdos585.GeneralStar
