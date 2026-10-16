import MatchingConstruction
import Mathlib.Data.Fintype.EquivFin

/-! Finite extremal/minimum interpretations on the fixed labelled carrier Fin N.
The binary-field graphs are actual attained constructions. The universal lower
bound remains an explicit conditional input: this module does not prove or
promote the #60 universal headline. -/
namespace Erdos60.Construction.ExtremalInterpretation
open scoped Classical
open Erdos60.Counting
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Ordinary unlabelled C4 count cannot decrease under a graph embedding. -/
theorem cycleCount_le_of_embedding (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V ↪ W) (hf : ∀ a b, G.Adj a b → H.Adj (f a) (f b)) :
    cycleCount G ≤ cycleCount H := by
  classical
  apply Finset.card_le_card_of_injOn (fun C : Finset (Sym2 V) => C.map f.sym2Map)
  · intro C hC
    obtain ⟨hsub,a,b,c,d,hd,rfl⟩ := (mem_cycles G C).mp hC
    apply (mem_cycles H _).mpr
    constructor
    · intro e he
      obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp he
      have hsG := hsub hs
      induction s using Sym2.inductionOn with | _ u v =>
        have huv : G.Adj u v := by simpa using hsG
        simpa using hf u v huv
    · refine ⟨f a,f b,f c,f d,?_,?_⟩
      · simpa only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_or,not_false_eq_true,and_true,f.injective.eq_iff] using hd
      · simp [fourEdges]
  · intro C hC D hD he
    exact Finset.map_injective f.sym2Map he

/-- Actual graph relabelling preserves the ordinary unlabelled C4 count. -/
theorem cycleCount_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    cycleCount G = cycleCount H := by
  apply Nat.le_antisymm
  · exact cycleCount_le_of_embedding G H e.toEquiv.toEmbedding (fun a b h => e.map_rel_iff.mpr h)
  · exact cycleCount_le_of_embedding H G e.symm.toEquiv.toEmbedding (fun a b h => e.symm.map_rel_iff.mpr h)

/-- Relabel any actual finite graph onto Fin N, preserving both actual edge
cardinality and ordinary unlabelled cycle count. -/
theorem relabel_graph_to_fin (G : SimpleGraph V) (N : ℕ) (hN : Fintype.card V = N) :
    ∃ H : SimpleGraph (Fin N), H.edgeFinset.card = G.edgeFinset.card ∧
      cycleCount H = cycleCount G := by
  classical
  let e := Fintype.equivFinOfCardEq hN
  let H := G.map e.toEmbedding
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  have hi : G ≃g H := SimpleGraph.Iso.map e G
  exact ⟨H,hi.card_edgeFinset_eq.symm,(cycleCount_iso hi).symm⟩

/-- The proved actual finite-field matching construction on the standard
labelled carrier, with exact edge and ordinary-cycle counts preserved. -/
theorem power_two_sharpness_fin (k t : ℕ) (hk : k ≠ 0) (ht : 2*t ≤ 2^k+1) :
    ∃ G : SimpleGraph (Fin ((2^k)^2+2^k+1)),
      G.edgeFinset.card = 2^k*(2^k+1)^2/2+t ∧
      cycleCount G = t*(2^k-1) := by
  classical
  obtain ⟨G,hN,he,hc⟩ := power_two_sharpness k t hk ht
  obtain ⟨H,hHe,hHc⟩ := relabel_graph_to_fin G _ hN
  exact ⟨H,hHe.trans he,hHc.trans hc⟩

/-- Any requested number of edges up to the actual cardinal is realized by
an actual spanning subgraph. -/
theorem exists_subgraph_edge_card (G : SimpleGraph V) (m : ℕ)
    (hm : m ≤ G.edgeFinset.card) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card = m := by
  classical
  obtain ⟨S,hS,hSc⟩ := Finset.exists_subset_card_eq hm
  let H := SimpleGraph.fromEdgeSet (S : Set (Sym2 V))
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHedge : H.edgeFinset = S := by
    ext e
    rw [SimpleGraph.mem_edgeFinset]
    change e ∈ (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet ↔ e ∈ S
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · exact fun h => h.1
    · intro he
      exact ⟨he,G.not_isDiag_of_mem_edgeFinset (hS he)⟩
  refine ⟨H,?_,?_⟩
  · apply (SimpleGraph.fromEdgeSet_le G).mpr
    intro e he
    exact SimpleGraph.mem_edgeFinset.mp (hS he.1)
  · convert (congrArg Finset.card hHedge).trans hSc using 1
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]

/-- Finite maximum of the edge counts of all actual C4-free graphs on Fin N. -/
noncomputable def c4Extremal (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (SimpleGraph (Fin N))).filter
    (fun G => cycleCount G = 0)).sup (fun G => G.edgeFinset.card)

/-- Minimum number of ordinary unlabelled C4s among actual graphs with m
edges on Fin N. The value is used below only after actual nonemptiness is proved. -/
noncomputable def minimumCycles (N m : ℕ) : ℕ :=
  sInf {z : ℕ | ∃ G : SimpleGraph (Fin N), G.edgeFinset.card = m ∧ cycleCount G = z}

/-- The exact h(N,t) convention: ex(N,C4)+t edges. -/
noncomputable def c4Supersaturation (N t : ℕ) : ℕ :=
  minimumCycles N (c4Extremal N+t)

/-- A universal upper edge bound and an actual attained graph determine the
finite extremal maximum. -/
theorem c4Extremal_eq_of_upper_attained (N m : ℕ)
    (hupper : ∀ G : SimpleGraph (Fin N), cycleCount G = 0 → G.edgeFinset.card ≤ m)
    (hattained : ∃ G : SimpleGraph (Fin N), G.edgeFinset.card = m ∧ cycleCount G = 0) :
    c4Extremal N = m := by
  classical
  apply Nat.le_antisymm
  · exact Finset.sup_le (fun G hG => hupper G (Finset.mem_filter.mp hG).2)
  · obtain ⟨G,he,hc⟩ := hattained
    have hh := Finset.le_sup (s := (Finset.univ : Finset (SimpleGraph (Fin N))).filter
      (fun G => cycleCount G = 0)) (f := fun G => G.edgeFinset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ G,hc⟩)
    simpa only [c4Extremal,he] using hh

/-- A universal lower bound and an actual graph attaining it determine the
finite minimum, including the required nonempty exact-edge graph family. -/
theorem minimumCycles_eq_of_lower_attained (N m c : ℕ)
    (hlower : ∀ G : SimpleGraph (Fin N), G.edgeFinset.card = m → c ≤ cycleCount G)
    (hattained : ∃ G : SimpleGraph (Fin N), G.edgeFinset.card = m ∧ cycleCount G = c) :
    minimumCycles N m = c := by
  apply Nat.le_antisymm
  · exact csInf_le ⟨0,fun z hz => Nat.zero_le z⟩ hattained
  · apply le_csInf ⟨c,hattained⟩
    rintro z ⟨G,he,hc⟩
    exact hc ▸ hlower G he

/-- The minimum is attained and is below every actual exact-edge graph's
cycle count whenever the exact-edge graph family is nonempty. -/
theorem minimumCycles_spec (N m : ℕ)
    (hexists : ∃ G : SimpleGraph (Fin N), G.edgeFinset.card = m) :
    (∃ G : SimpleGraph (Fin N), G.edgeFinset.card = m ∧
      cycleCount G = minimumCycles N m) ∧
    ∀ G : SimpleGraph (Fin N), G.edgeFinset.card = m → minimumCycles N m ≤ cycleCount G := by
  classical
  obtain ⟨G,hG⟩ := hexists
  have hnonempty : {z : ℕ | ∃ H : SimpleGraph (Fin N),
      H.edgeFinset.card = m ∧ cycleCount H = z}.Nonempty := ⟨cycleCount G,G,hG,rfl⟩
  constructor
  · exact Nat.sInf_mem hnonempty
  · intro H hH
    exact csInf_le ⟨0,fun z hz => Nat.zero_le z⟩ ⟨H,hH,rfl⟩

/-- Precisely the unpaid universal lower-bound input, on the fixed labelled
vertex carrier and only in the original linear t-range. -/
def UniversalLinearLowerBound (q : ℕ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → 100000000*t ≤ q →
    ∀ G : SimpleGraph (Fin (q^2+q+1)), G.edgeFinset.card = q*(q+1)^2/2+t →
      t*(q-1) ≤ cycleCount G

/-- Conditional ex/h interpretation. Binary-field existence and attainment are
proved constructions; the universal headline lower bound is still explicit. -/
theorem power_two_interpretation_of_universal_lower (k : ℕ) (hk : k ≠ 0)
    (hq : 10000000000000000 ≤ 2^k)
    (hlower : UniversalLinearLowerBound (2^k)) :
    c4Extremal ((2^k)^2+2^k+1) = 2^k*(2^k+1)^2/2 ∧
      ∀ t : ℕ, 1 ≤ t → 100000000*t ≤ 2^k →
        c4Supersaturation ((2^k)^2+2^k+1) t = t*(2^k-1) := by
  classical
  let q := 2^k
  let N := q^2+q+1
  let M := q*(q+1)^2/2
  have hqpos : 1 < q := by dsimp [q]; omega
  have hex : c4Extremal N = M := by
    apply c4Extremal_eq_of_upper_attained
    · intro G hzero
      by_contra hn
      have hmore : M+1 ≤ G.edgeFinset.card := by omega
      obtain ⟨H,hHG,hH⟩ := exists_subgraph_edge_card G (M+1) hmore
      have hcount := hlower 1 (by omega) (by dsimp [q] at *; omega) H hH
      have hmono := cycleCount_mono hHG
      simp only [one_mul] at hcount
      omega
    · obtain ⟨G,he,hc⟩ := power_two_sharpness_fin k 0 hk (by omega)
      exact ⟨G,by simpa only [Nat.add_zero] using he,by simpa using hc⟩
  refine ⟨hex,?_⟩
  intro t ht htrange
  unfold c4Supersaturation
  rw [hex]
  apply minimumCycles_eq_of_lower_attained
  · exact hlower t ht htrange
  · exact power_two_sharpness_fin k t hk (by omega)

#print axioms cycleCount_le_of_embedding
#print axioms cycleCount_iso
#print axioms relabel_graph_to_fin
#print axioms power_two_sharpness_fin
#print axioms exists_subgraph_edge_card
#print axioms c4Extremal_eq_of_upper_attained
#print axioms minimumCycles_eq_of_lower_attained
#print axioms minimumCycles_spec
#print axioms power_two_interpretation_of_universal_lower
end Erdos60.Construction.ExtremalInterpretation
