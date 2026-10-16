import Openmath.Erdos643.HypergraphBasics

namespace Erdos643.Projection
open Finset HypergraphBasics
variable {V : Type*} [DecidableEq V]

/-- Actual one-X/two-Y projected edges, encoding Y pairs as two-element finsets. -/
def projected (H : TripleSystem V) : Finset (V × Finset V) :=
  H.biUnion (fun E => E.image (fun x => (x, E.erase x)))

lemma reconstruct {H : TripleSystem V} {z : V × Finset V}
    (hz : z ∈ projected H) : insert z.1 z.2 ∈ H := by
  obtain ⟨E, hE, hzE⟩ := mem_biUnion.mp hz
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hzE
  simpa only [insert_erase hx] using hE

lemma projected_pair {H : TripleSystem V} (hu : Uniform H) {z : V × Finset V}
    (hz : z ∈ projected H) : z.2.card = 2 ∧ z.1 ∉ z.2 := by
  obtain ⟨E, hE, hzE⟩ := mem_biUnion.mp hz
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hzE
  constructor
  · rw [card_erase_of_mem hx, hu E hE]
  · simp

/-- Each actual triple has exactly three distinct projected edges; different
triples have disjoint projected images because insertion reconstructs the triple. -/
theorem projected_card {H : TripleSystem V} (hu : Uniform H) :
    (projected H).card = 3 * H.card := by
  classical
  have hd : ∀ E ∈ H, ∀ F ∈ H, E ≠ F →
      Disjoint (E.image (fun x => (x, E.erase x)))
        (F.image (fun x => (x, F.erase x))) := by
    intro E hE F hF hEF
    apply disjoint_left.mpr
    intro z hzE hzF
    obtain ⟨x, hx, hzx⟩ := mem_image.mp hzE
    obtain ⟨y, hy, hzy⟩ := mem_image.mp hzF
    have heq : (x, E.erase x) = (y, F.erase y) := hzx.trans hzy.symm
    have hrec := congrArg (fun p : V × Finset V => insert p.1 p.2) heq
    apply hEF
    simpa only [insert_erase hx, insert_erase hy] using hrec
  unfold projected
  rw [card_biUnion hd]
  calc
    (∑ E ∈ H, (E.image (fun x => (x, E.erase x))).card) = ∑ _E ∈ H, 3 := by
      apply sum_congr rfl
      intro E hE
      rw [card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
      exact hu E hE
    _ = 3 * H.card := by simp [Nat.mul_comm]

/-- The flag encoding is an actual triple on two disjoint copies of V. -/
def liftedEdge (z : V × Finset V) : Finset (Sum V V) :=
  insert (Sum.inl z.1) (z.2.image Sum.inr)

def lifted (H : TripleSystem V) : TripleSystem (Sum V V) :=
  (projected H).image liftedEdge

lemma liftedEdge_injective : Function.Injective (liftedEdge (V := V)) := by
  intro z w he
  have hf : z.1 = w.1 := by
    have hm : Sum.inl z.1 ∈ liftedEdge w := by rw [← he]; simp [liftedEdge]
    simpa [liftedEdge] using hm
  have hs : z.2 = w.2 := by
    ext v
    have hm := congrArg (fun S : Finset (Sum V V) => Sum.inr v ∈ S) he
    have hp : (v ∈ z.2) = (v ∈ w.2) := by simpa [liftedEdge] using hm
    exact Iff.of_eq hp
  exact Prod.ext hf hs

theorem lifted_card {H : TripleSystem V} (hu : Uniform H) :
    (lifted H).card = 3 * H.card := by
  rw [lifted, card_image_of_injective _ liftedEdge_injective]
  exact projected_card hu

theorem lifted_uniform {H : TripleSystem V} (hu : Uniform H) : Uniform (lifted H) := by
  intro E hE
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hE
  obtain ⟨hc, _⟩ := projected_pair hu hz
  unfold liftedEdge
  rw [card_insert_of_notMem (by simp), card_image_of_injective _ Sum.inr_injective, hc]

end Erdos643.Projection
