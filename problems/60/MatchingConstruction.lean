import MatchingEquality
import FiniteFieldPolarity
import PolarityMatchingCount
import PolarityAbsoluteBound
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
namespace Erdos60.Construction
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph formed by pairing the two slots of each injectively labelled pair. -/
def pairedGraph {t : ℕ} (f : Fin t × Fin 2 ↪ V) : SimpleGraph V where
  Adj a b := ∃ i, (a = f (i,0) ∧ b = f (i,1)) ∨ (a = f (i,1) ∧ b = f (i,0))
  symm := ⟨by rintro a b ⟨i,h|h⟩; exact ⟨i,Or.inr ⟨h.2,h.1⟩⟩; exact ⟨i,Or.inl ⟨h.2,h.1⟩⟩⟩
  loopless := ⟨by
    rintro a ⟨i,h|h⟩
    · have := f.injective (h.1.symm.trans h.2); simp at this
    · have := f.injective (h.1.symm.trans h.2); simp at this⟩

omit [Fintype V] [DecidableEq V] in
theorem pairedGraph_matching {t : ℕ} (f : Fin t × Fin 2 ↪ V) :
    Erdos60.Counting.IsMatchingGraph (pairedGraph f) := by
  rintro a b c ⟨i,hi|hi⟩ ⟨j,hj|hj⟩
  · have hh := f.injective (hi.1.symm.trans hj.1)
    have hij : i = j := congrArg Prod.fst hh
    subst j
    exact hi.2.trans hj.2.symm
  · have hh := f.injective (hi.1.symm.trans hj.1)
    have := congrArg Prod.snd hh
    simp at this
  · have hh := f.injective (hi.1.symm.trans hj.1)
    have := congrArg Prod.snd hh
    simp at this
  · have hh := f.injective (hi.1.symm.trans hj.1)
    have hij : i = j := congrArg Prod.fst hh
    subst j
    exact hi.2.trans hj.2.symm

theorem pairedGraph_edge_card {t : ℕ} (f : Fin t × Fin 2 ↪ V) :
    (pairedGraph f).edgeFinset.card = t := by
  classical
  have he : (pairedGraph f).edgeFinset = Finset.univ.image (fun i => s(f (i,0),f (i,1))) := by
    ext e
    induction e using Sym2.inductionOn with | _ a b =>
      rw [SimpleGraph.mem_edgeFinset]
      change (∃ i, (a = f (i,0) ∧ b = f (i,1)) ∨ (a = f (i,1) ∧ b = f (i,0))) ↔ _
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Sym2.eq_iff]
      aesop
  rw [he, Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj he
    simp only [Sym2.eq_iff] at he
    rcases he with he | he
    · exact congrArg Prod.fst (f.injective he.1)
    · have hh := congrArg Prod.snd (f.injective he.1)
      simp at hh

/-- Any finite support with at least 2t vertices admits an actual t-edge matching. -/
theorem exists_matching_on (S : Finset V) (t : ℕ) (h : 2*t ≤ S.card) :
    ∃ K : SimpleGraph V, Erdos60.Counting.IsMatchingGraph K ∧
      (∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S) ∧ K.edgeFinset.card = t := by
  classical
  have hc : Fintype.card (Fin t × Fin 2) ≤ Fintype.card S := by simpa [mul_comm] using h
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hc
  let f : Fin t × Fin 2 ↪ V := g.trans (Function.Embedding.subtype _)
  refine ⟨pairedGraph f, pairedGraph_matching f, ?_, pairedGraph_edge_card f⟩
  rintro a b ⟨i,h|h⟩
  · exact ⟨h.1 ▸ (g (i,0)).property, h.2 ▸ (g (i,1)).property⟩
  · exact ⟨h.1 ▸ (g (i,1)).property, h.2 ▸ (g (i,0)).property⟩

noncomputable instance binaryPointFintype (k : ℕ) : Fintype (Point (GaloisField 2 k)) := Fintype.ofFinite _
noncomputable instance binaryPointDecidable (k : ℕ) : DecidableEq (Point (GaloisField 2 k)) := Classical.decEq _

/-- Actual sharpness graph obtained by adding an actual matching to the
constructed orthogonal polarity graph. -/
theorem power_two_sharpness (k t : ℕ) (hk : k ≠ 0) (ht : 2*t ≤ 2^k+1) :
    ∃ G : SimpleGraph (Point (GaloisField 2 k)),
      Fintype.card (Point (GaloisField 2 k)) = (2^k)^2 + 2^k + 1 ∧
      G.edgeFinset.card = 2^k * (2^k+1)^2 / 2 + t ∧
      Erdos60.Counting.cycleCount G = t * (2^k-1) := by
  classical
  let π := dotPolarity (GaloisField 2 k)
  have ho : Configuration.ProjectivePlane.order (Point (GaloisField 2 k))
      (Point (GaloisField 2 k)) = 2^k := by rw [plane_order, GaloisField.card 2 k hk]
  have ha : Nat.card {p : Point (GaloisField 2 k) // π.Absolute p} = 2^k+1 := by
    exact (absolute_count _).trans (by rw [GaloisField.card 2 k hk])
  let S := Finset.univ.filter (fun p => π.Absolute p)
  have hS : S.card = 2^k+1 := by
    simpa [S, Nat.card_eq_fintype_card, Fintype.card_subtype] using ha
  obtain ⟨K,hm,hs,hK⟩ := exists_matching_on S t (by omega)
  have hsupport : ∀ a b, K.Adj a b → π.Absolute a ∧ π.Absolute b := by
    intro a b hab
    obtain ⟨ha,hb⟩ := hs a b hab
    exact ⟨(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩
  have heven : Even (Configuration.ProjectivePlane.order (Point (GaloisField 2 k))
      (Point (GaloisField 2 k))) := by
    rw [ho]
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact even_iff_two_dvd.mpr ⟨2^n, by simp [pow_succ, mul_comm]⟩
  have he := (π.edge_count_eq_iff_absolute_count heven).mpr (by rw [ho]; exact ha)
  have hd : Disjoint π.graph.edgeFinset K.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e heQ heK
    induction e using Sym2.inductionOn with | _ a b =>
      have habQ : π.graph.Adj a b := by simpa using heQ
      have habK : K.Adj a b := by simpa using heK
      exact π.absolute_not_adjacent (hsupport a b habK).1 (hsupport a b habK).2 habQ
  refine ⟨π.graph ⊔ K, ?_, ?_, ?_⟩
  · rw [Configuration.ProjectivePlane.card_points (Point (GaloisField 2 k)) (Point (GaloisField 2 k)), ho]
  · calc
      _ = (π.graph.edgeFinset ∪ K.edgeFinset).card := by
        congr 1
        ext e
        simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union]
        exact SimpleGraph.edgeSet_sup π.graph K ▸ Iff.rfl
      _ = π.graph.edgeFinset.card + K.edgeFinset.card := Finset.card_union_of_disjoint hd
      _ = _ := by rw [he, hK, ho]
  · rw [π.matching_absolute_cycle_count K hm hsupport, hK, ho]

#print axioms power_two_sharpness
#print axioms exists_matching_on
end Erdos60.Construction
