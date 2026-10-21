import Openmath.Erdos643R3.Redistribution
import Openmath.Erdos643R3.BothLight
import Openmath.Erdos643R3.G1Bicone

set_option autoImplicit false
namespace Erdos643R3.CPrime
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.SlotModel
  Erdos643R3.L1Top Erdos643R3.Redistribution Erdos643R3.RedistArith
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- The exact parts G1(ii)-(iii) used by redistribution, on any labelled bicone. -/
def BiconeG1 (H : Finset (Finset V)) : Prop :=
  ∀ x y u v w : V, x ≠ y →
    CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)) →
    Deficient H {x,u,v} → ExactlyOneLight H x u v ∧
      (Light H x u → (CN H {v,w}).card = 2) ∧
      (Light H x v → (CN H {u,w}).card = 2)

/-- G3h' for the actual both-heavy anchor and actual apex deficit sum. -/
def G3hPrime (H : Finset (Finset V)) : Prop :=
  ∀ x y u v w : V, x ≠ y →
    CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)) →
    Active H {x,y} → Light H x v → ¬ Light H x u → ¬ Light H x w →
    0 < apexDeficit H {x,y} x →
    apexDeficit H {x,y} x ≤ charge H {x,u,w} / (act H {x,u,w} : ℚ)

theorem CN_rot {x y u v w : V}
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V))) :
    CN H {x,y} = ({{v,w},{w,u},{v,u}} : Finset (Finset V)) := by
  rw [hCN]
  ext P
  simp only [mem_insert, mem_singleton, pair_comm w u, pair_comm v u]
  tauto

theorem CN_swap {x y u v w : V}
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V))) :
    CN H {x,y} = ({{v,u},{u,w},{v,w}} : Finset (Finset V)) := by
  rw [hCN]
  ext P
  simp only [mem_insert, mem_singleton, pair_comm v u]
  tauto

theorem bicone_edges {x y u v w : V}
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V))) :
    ({x,u,v} : Finset V) ∈ H ∧ ({x,v,w} : Finset V) ∈ H ∧ ({x,u,w} : Finset V) ∈ H := by
  have edge : ∀ P ∈ ({{u,v},{v,w},{u,w}} : Finset (Finset V)), insert x P ∈ H := by
    intro P hP
    exact (mem_CN.mp (hCN ▸ hP)).2.2 x (by simp)
  exact ⟨edge _ (by simp), edge _ (by simp), edge _ (by simp)⟩

theorem anchor_mem_bicone {x y u v w : V}
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V))) :
    ({x,u,w} : Finset V) ∈ bicone H {x,y} := by
  exact mem_bicone.mpr ⟨{u,w}, by rw [hCN]; simp, x, by simp, rfl⟩

theorem light_link {x y u v w : V} (hH : Uniform H)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (hl : Light H x u) : link H {x,u} = {v,w} := by
  obtain ⟨hT, _, hA⟩ := bicone_edges hCN
  have hxu := card_pair (triple_ne (hH _ hT)).1
  have hvw : ({v,w} : Finset V).card = 2 :=
    (mem_CN.mp (show ({v,w} : Finset V) ∈ CN H {x,y} by rw [hCN]; simp)).1
  apply (eq_of_subset_of_card_le (s := ({v,w} : Finset V)) ?_ ?_).symm
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rw [mem_link_iff_of_uniform hH hxu]
    rcases hz with hz | hz
    · subst z
      rwa [show insert v ({x,u} : Finset V) = {x,u,v} from triple_perm (fun t => by tauto)]
    · subst z
      rwa [show insert w ({x,u} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
  · rw [← codeg_eq_card_link hH hxu, hvw]
    exact le_of_eq hl

theorem apex_positive_has_deficient {x y u v w : V} (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (hp : 0 < apexDeficit H {x,y} x) :
    Deficient H {x,u,v} ∨ Deficient H {x,v,w} ∨ Deficient H {x,u,w} := by
  have hn : (apexDefSet H {x,y} x).Nonempty := by
    by_contra he
    have he' := not_nonempty_iff_eq_empty.mp he
    unfold apexDeficit at hp
    rw [he', sum_empty] at hp
    exact lt_irrefl _ hp
  obtain ⟨T, hT⟩ := hn
  have hs := apexDefSet_subset_three hxy hCN hT
  have hd := (mem_defSet.mp (mem_filter.mp hT).1).2
  simp only [mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · exact Or.inl hd
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr hd)

/-- A mixed coloring oriented with equal outer colors determines the anchor. -/
theorem oriented_anchor_share (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hG1 : BiconeG1 H) (hG3 : G3hPrime H)
    {x y u v w : V} (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (ha : Active H {x,y}) (hp : 0 < apexDeficit H {x,y} x)
    (heq : Light H x u ↔ Light H x w) (hmix : ExactlyOneLight H x u v) :
    apexDeficit H {x,y} x ≤ charge H {x,u,w} / (act H {x,u,w} : ℚ) := by
  have hrot := CN_rot hCN
  have hswap := CN_swap (CN_rot hrot)
  have hc : (apexDefSet H {x,y} x).card ≤ 2 := by
    apply apexDefSet_card_le_two (apexDefSet_subset_three hxy hCN)
    · intro ht
      exact (hG1 x y u v w hxy hCN (mem_defSet.mp (mem_filter.mp ht).1).2).1
    · intro ht
      exact (hG1 x y v w u hxy hrot (mem_defSet.mp (mem_filter.mp ht).1).2).1
    · intro ht
      exact (hG1 x y u w v hxy hswap (mem_defSet.mp (mem_filter.mp ht).1).2).1
  have hD := apexDeficit_le_sixth hH hav hc
  by_cases hu : Light H x u
  · have hw := heq.mp hu
    have hv : ¬ Light H x v := by
      intro hv
      exact hmix ⟨fun _ => hv, fun _ => hu⟩
    have hxu := light_link hH hCN hu
    have hxw : link H {x,w} = {u,v} := by
      have hh := light_link hH (CN_rot hrot) hw
      exact hh
    have hT := (bicone_edges hCN).2.2
    have hmem := anchor_mem_bicone hCN
    have hQ : (1/6 : ℚ) ≤ charge H {x,u,w} ∧ act H {x,u,w} = 1 := by
      rcases apex_positive_has_deficient hxy hCN hp with hd | hd | hd
      · have hh := BothLight.bicone_both_light hH hav hxy hCN hxu hxw
          ((hG1 x y u v w hxy hCN hd).2.1 hu)
        exact ⟨hh.1, G1Bicone.act_eq_one hT hH hh.2 ha hmem⟩
      · have hs := (hG1 x y v w u hxy hrot hd).2.2 hw
        have hmirror : CN H {x,y} = ({{w,v},{v,u},{w,u}} : Finset (Finset V)) := by
          rw [hCN]
          ext P
          simp only [mem_insert, mem_singleton, pair_comm w v, pair_comm v u, pair_comm w u]
          tauto
        have hh := BothLight.bicone_both_light hH hav hxy hmirror
          (show link H {x,w} = {v,u} by rw [hxw, pair_comm u v])
          (show link H {x,u} = {w,v} by rw [hxu, pair_comm v w]) hs
        have ht : ({x,w,u} : Finset V) = {x,u,w} := triple_perm (fun t => by tauto)
        have hcharge := hh.1
        rw [ht] at hcharge
        have hact := G1Bicone.act_eq_one (show ({x,w,u} : Finset V) ∈ H by rwa [ht])
          hH hh.2 ha (show ({x,w,u} : Finset V) ∈ bicone H {x,y} by rwa [ht])
        rw [ht] at hact
        exact ⟨hcharge,hact⟩
      · have hh := (hG1 x y u w v hxy hswap hd).1
        exact False.elim (hh heq)
    rw [hQ.2]
    norm_num
    exact hD.trans hQ.1
  · have hw : ¬ Light H x w := fun hw => hu (heq.mpr hw)
    have hv : Light H x v := by
      by_contra hv
      exact hmix ⟨fun h => False.elim (hu h), fun h => False.elim (hv h)⟩
    exact hG3 x y u v w hxy hCN ha hv hu hw hp

theorem anchor_from_deficient_edge (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hG1 : BiconeG1 H) (hG3 : G3hPrime H)
    {x y u v w : V} (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (ha : Active H {x,y}) (hp : 0 < apexDeficit H {x,y} x) (hd : Deficient H {x,u,v}) :
    ∃ A ∈ bicone H {x,y}, x ∈ A ∧
      apexDeficit H {x,y} x ≤ charge H A / (act H A : ℚ) := by
  have hm := (hG1 x y u v w hxy hCN hd).1
  by_cases heq : Light H x u ↔ Light H x w
  · exact ⟨{x,u,w}, anchor_mem_bicone hCN, by simp,
      oriented_anchor_share hH hav hG1 hG3 hxy hCN ha hp heq hm⟩
  · have heq' : Light H x v ↔ Light H x w := by
      unfold ExactlyOneLight at hm
      tauto
    have hm' : ExactlyOneLight H x v u := by
      unfold ExactlyOneLight at hm ⊢
      tauto
    exact ⟨{x,v,w}, anchor_mem_bicone (CN_swap hCN), by simp,
      oriented_anchor_share hH hav hG1 hG3 hxy (CN_swap hCN) ha hp heq' hm'⟩

theorem apex_anchor_exists (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hG1 : BiconeG1 H) (hG3 : G3hPrime H)
    {x y u v w : V} (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (ha : Active H {x,y}) (hp : 0 < apexDeficit H {x,y} x) :
    ∃ A ∈ bicone H {x,y}, x ∈ A ∧
      apexDeficit H {x,y} x ≤ charge H A / (act H A : ℚ) := by
  rcases apex_positive_has_deficient hxy hCN hp with hd | hd | hd
  · exact anchor_from_deficient_edge hH hav hG1 hG3 hxy hCN ha hp hd
  · exact anchor_from_deficient_edge hH hav hG1 hG3 hxy (CN_rot hCN) ha hp hd
  · exact anchor_from_deficient_edge hH hav hG1 hG3 hxy (CN_swap (CN_rot (CN_rot hCN))) ha hp hd

/-- Theorem C', funding step: G1 selects the anchors, Q funds both-light
anchors, G3h' funds both-heavy anchors, and the finite accounting adds them. -/
theorem funded_of_G1_G3hPrime (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hG1 : BiconeG1 H) (hG3 : G3hPrime H) :
    ∀ q ∈ activePairs H, totalDeficit H q ≤ pot H q := by
  classical
  intro q hq
  have ha := (mem_activePairs.mp hq).2
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp ha.1.1
  obtain ⟨u,v,w,_,_,_,hCN⟩ := ha.1.2
  have hex : ∀ z, ∃ A : Finset V, z ∈ deficientApexes H {x,y} →
      A ∈ bicone H {x,y} ∧ z ∈ A ∧
        apexDeficit H {x,y} z ≤ charge H A / (act H A : ℚ) := by
    intro z
    by_cases hz : z ∈ deficientApexes H {x,y}
    · have hp := (mem_filter.mp hz).2
      have hz' : z = x ∨ z = y := by simpa using (mem_filter.mp hz).1
      rcases hz' with hz' | hz'
      · subst z
        obtain ⟨A,hA,hx,hshare⟩ := apex_anchor_exists hH hav hG1 hG3 hxy hCN ha hp
        exact ⟨A, fun _ => ⟨hA,hx,hshare⟩⟩
      · subst z
        have hCN' : CN H {y,x} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)) := by
          rwa [pair_comm y x]
        have ha' : Active H {y,x} := by rwa [pair_comm y x]
        have hp' : 0 < apexDeficit H {y,x} y := by rwa [pair_comm y x]
        obtain ⟨A,hA,hy,hshare⟩ := apex_anchor_exists hH hav hG1 hG3 hxy.symm hCN' ha' hp'
        rw [pair_comm y x] at hA hshare
        exact ⟨A, fun _ => ⟨hA,hy,hshare⟩⟩
    · exact ⟨∅, fun hh => False.elim (hz hh)⟩
  choose A hA using hex
  apply pot_ge_totalDeficit_of_apex_shares hq A
  · intro z hz
    exact ⟨(hA z hz).1, (hA z hz).2.1⟩
  · intro z hz
    exact (hA z hz).2.2

end Erdos643R3.CPrime
