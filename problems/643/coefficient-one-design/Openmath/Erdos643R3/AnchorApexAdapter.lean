import Openmath.Erdos643R3.AnchorHostAdapter
import Openmath.Erdos643R3.AnchorActivity
import Openmath.Erdos643R3.CPrime

set_option autoImplicit false
namespace Erdos643R3.AnchorApexAdapter
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound
  Erdos643R3.SlotModel Erdos643R3.L1Top Erdos643R3.AnchorCaps
  Erdos643R3.Redistribution Erdos643R3.RedistArith
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

/-- G1 excludes a deficient anchor when both its apex pairs are heavy. -/
theorem anchor_not_deficient (h : Host H x y u v w)
    (hu : ¬ Light H x u) (hw : ¬ Light H x w) : ¬ Deficient H {x,u,w} := by
  intro hd
  have hc : CN H {x,y} = ({{u,w},{w,v},{u,v}} : Finset (Finset V)) := by
    rw [h.CN_xy]; ext P; simp only [mem_insert,mem_singleton,pair_comm w v]; tauto
  have hg := G1BiconeAdapter.deficient_geometric h.uniform h.avoiding h.xy hc hd
  exact hw (hg.1.mpr hu)

/-- A host apex pair has at least two neighbours, so nonlight means codegree at least three. -/
theorem heavy_xu (h : Host H x y u v w) (hu : ¬ Light H x u) : 3 ≤ codeg H {x,u} := by
  have hs : ({v,w} : Finset V) ⊆ link H {x,u} := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl
    · apply mem_link.mpr
      refine ⟨by simp [h.xv.symm,h.uv.symm],?_⟩
      convert h.xuv using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
    · apply mem_link.mpr
      refine ⟨by simp [h.xw.symm,h.uw.symm],?_⟩
      convert h.xuw using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  have hc := card_le_card hs
  rw [card_pair h.vw,← codeg_eq_card_link h.uniform (card_pair h.xu)] at hc
  change codeg H {x,u} ≠ 2 at hu
  omega

/-- The original apex sum is exactly the two side deficits, with deficient indicators. -/
theorem apexDeficit_eq (h : Host H x y u v w)
    (hu : ¬ Light H x u) (hw : ¬ Light H x w) :
    apexDeficit H {x,y} x =
      (if Deficient H {x,u,v} then deficit H {x,u,v} else 0) +
      (if Deficient H {x,v,w} then deficit H {x,v,w} else 0) := by
  classical
  have hn := anchor_not_deficient h hu hw
  have hs : apexDefSet H {x,y} x =
      ({({x,u,v} : Finset V),{x,v,w}} : Finset (Finset V)).filter (Deficient H) := by
    ext T
    constructor
    · intro hT
      have hthree := apexDefSet_subset_three h.xy h.CN_xy hT
      have hd := (mem_defSet.mp (mem_filter.mp hT).1).2
      apply mem_filter.mpr
      refine ⟨?_,hd⟩
      simp only [mem_insert,mem_singleton] at hthree ⊢
      rcases hthree with ht | ht | ht
      · exact Or.inl ht
      · exact Or.inr ht
      · exact False.elim (hn (ht ▸ hd))
    · rintro hT
      obtain ⟨hT,hd⟩ := mem_filter.mp hT
      simp only [mem_insert,mem_singleton] at hT
      rcases hT with rfl | rfl
      · apply mem_filter.mpr
        refine ⟨mem_defSet.mpr ⟨?_,hd⟩,by simp⟩
        exact mem_bicone.mpr ⟨{u,v},by rw [h.CN_xy]; simp,x,by simp,rfl⟩
      · apply mem_filter.mpr
        refine ⟨mem_defSet.mpr ⟨?_,hd⟩,by simp⟩
        exact mem_bicone.mpr ⟨{v,w},by rw [h.CN_xy]; simp,x,by simp,rfl⟩
  have hne : ({x,u,v} : Finset V) ≠ {x,v,w} := by
    intro he
    have hm : u ∈ ({x,v,w} : Finset V) := by rw [← he]; simp
    simp [h.xu.symm,h.uv,h.uw] at hm
  unfold apexDeficit
  rw [hs,sum_filter]
  simp [hne]

/-- A positive original apex deficit comes from one of the two side triples. -/
theorem deficient_sides (h : Host H x y u v w)
    (hu : ¬ Light H x u) (hw : ¬ Light H x w)
    (hp : 0 < apexDeficit H {x,y} x) :
    Deficient H {x,u,v} ∨ Deficient H {x,v,w} := by
  rcases CPrime.apex_positive_has_deficient h.xy h.CN_xy hp with hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr hd
  · exact False.elim (anchor_not_deficient h hu hw hd)

/-- All host hypotheses follow from the original both-heavy bicone setting. -/
theorem original_data (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (hl : Light H x v) (hu : ¬ Light H x u) (hw : ¬ Light H x w)
    (hp : 0 < apexDeficit H {x,y} x) :
    Host H x y u v w ∧ 3 ≤ codeg H {x,u} ∧ 3 ≤ codeg H {x,w} ∧
      (CN H {u,w}).card = 2 ∧ (Deficient H {x,u,v} ∨ Deficient H {x,v,w}) := by
  have hlight : link H {x,v} = {u,w} := CPrime.light_link hH (CPrime.CN_swap hCN) hl
  have h := Host.of_bicone hH hav hxy hCN hlight
  have hd := deficient_sides h hu hw hp
  have hcard : (CN H {u,w}).card = 2 := by
    rcases hd with hd | hd
    · exact AnchorActivity.card_CN_uw_of_deficient h hd
    · have hd' : Deficient H {x,w,v} := by
        convert hd using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
      have hc := AnchorActivity.card_CN_uw_of_deficient h.mirror hd'
      simpa only [pair_comm w u] using hc
  exact ⟨h,heavy_xu h hu,heavy_xu h.mirror hw,hcard,hd⟩

end Erdos643R3.AnchorApexAdapter
