import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralHost

/-! Actual rich cycles and distinct chords survive injective graph homomorphisms. -/
namespace Erdos642.CampaignFe72210bContinuation3
open SimpleGraph
open Erdos642.CampaignFe72210b

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Extra ambient edges do not change which mapped edges belong to the actual walk. -/
theorem actual_isChord_map (f : G →g H) (hf : Function.Injective f)
    {u v : V} (p : G.Walk u v) (e : Sym2 V) (he : p.IsChord e) :
    (p.map f).IsChord (Sym2.map f e) := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    rcases Walk.isChord_sym2Mk.mp he with ⟨hadj, hnot, ha, hb⟩
    apply Walk.isChord_sym2Mk.mpr
    refine ⟨f.map_adj hadj, ?_, ?_, ?_⟩
    · intro hm
      rw [Walk.edges_map] at hm
      obtain ⟨e0, he0, heq⟩ := List.mem_map.mp hm
      have hinj := Sym2.map.injective hf
      have he0eq : e0 = s(a, b) := hinj heq
      apply hnot
      simpa only [he0eq] using he0
    · rw [Walk.support_map]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    · rw [Walk.support_map]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩

variable [Fintype V] [Fintype W] [DecidableEq W]

/-- The actual chord image is included in the mapped walk's actual chord finset. -/
theorem actual_chordEdges_image_subset (f : G →g H) (hf : Function.Injective f)
    {u v : V} (p : G.Walk u v) :
    (chordEdges p).image (Sym2.map f) ⊆ chordEdges (p.map f) := by
  classical
  intro e he
  obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
  have hchord : p.IsChord e0 := by simpa only [chordEdges, Finset.mem_filter,
    Finset.mem_univ, true_and] using he0
  have hm := actual_isChord_map f hf p e0 hchord
  simpa only [chordEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hm

/-- Distinct actual chords remain distinct under the injective vertex map. -/
theorem actual_chordEdges_card_le_map (f : G →g H) (hf : Function.Injective f)
    {u v : V} (p : G.Walk u v) :
    (chordEdges p).card ≤ (chordEdges (p.map f)).card := by
  classical
  have hcard := Finset.card_le_card (actual_chordEdges_image_subset f hf p)
  rw [Finset.card_image_of_injective _ (Sym2.map.injective hf)] at hcard
  exact hcard

/-- Exact frozen rich-cycle target transported by an injective adjacency-preserving map. -/
theorem hasRichCycle_of_injective_hom (f : G →g H) (hf : Function.Injective f)
    (hG : HasRichCycle G) : HasRichCycle H := by
  obtain ⟨v, c, hc, hrich⟩ := hG
  refine ⟨f v, c.map f, hc.map hf, ?_⟩
  rw [Walk.length_map]
  exact hrich.trans (actual_chordEdges_card_le_map f hf c)

/-- Literal subgraphs, including noninduced ones, inherit actual rich-cycle avoidance. -/
theorem not_hasRichCycle_of_injective_hom (f : G →g H) (hf : Function.Injective f)
    (hH : ¬ HasRichCycle H) : ¬ HasRichCycle G := by
  intro hG
  exact hH (hasRichCycle_of_injective_hom f hf hG)

end Erdos642.CampaignFe72210bContinuation3
