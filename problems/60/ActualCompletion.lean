import CoreRowDesign
import DenseEmbedding
import EmbeddedCoreCompletion

/-! Actual count-based completion, with every geometric supplier discharged.
CoreRowDesign constructs the indexed dual from actual good full graph rows;
DenseEmbedding proves its plane embedding on the ORIGINAL point-label carrier;
EmbeddedCoreCompletion constructs the actual containing polarity. The final
endpoint assumes neither an embedding, a plane, a row map, nor a polarity. -/
namespace Erdos60.Completion
open scoped Classical
universe u
variable {P : Type u} [Fintype P]

/-- The full actual count-based completion contract. All line labels and graph
vertices remain on their original point carrier, with actual edge containment. -/
theorem actual_count_based_completion
    (G : SimpleGraph P) (hG : NoFourCycle G) (q : ℕ)
    (heven : Even q) (hq : 100000000 ≤ q)
    (hN : Fintype.card P = q^2+q+1)
    (hmin : ∀ v, 999*q ≤ 1000*G.degree v)
    (hcap : ∀ v, G.degree v ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun v : P => G.degree v ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun v : P => G.degree v ≤ q-1)).card ≤ q) :
    ∃ (L : Type u) (fL : Fintype L) (M : Membership P L), letI := fL; letI := M
      ∃ pp : Configuration.ProjectivePlane P L, letI := pp
        Configuration.ProjectivePlane.order P L = q ∧
        ∃ π : Erdos60.Geometry.Polarity (P := P) (L := L), G ≤ π.graph := by
  classical
  let D := Erdos60.Embedding.coreRowDesign G hG q hq heven hN hcap hS hD
  let s := (q^2+q+1)-Fintype.card (Erdos60.Embedding.CorePoint G q)
  have hX : Fintype.card (Erdos60.Embedding.CorePoint G q)+s = q^2+q+1 :=
    Erdos60.Embedding.corePoint_missing_eq G q hN
  have hs : 500*s ≤ 501*q :=
    Erdos60.Embedding.corePoint_missing_budget G hG q hq hN hcap hS
  obtain ⟨L,fL,M,pp,ho,f,hinc⟩ := D.near_dense_plane s hq hN hX hs
  let : Fintype L := fL
  let : Membership P L := M
  let : Configuration.ProjectivePlane P L := pp
  have hpositive : 0 < Fintype.card (Erdos60.Embedding.CorePoint G q) := by
    have hh := Erdos60.Embedding.corePoint_dense G hG q hq hN hcap hS
    omega
  let a0 : Erdos60.Embedding.CorePoint G q :=
    Classical.choice (Fintype.card_pos_iff.mp hpositive)
  let row : P → L := fun a => if ha : a ∈ Erdos60.Embedding.coreVertices G q then
      f ⟨a,ha⟩ else f a0
  have hrow : ∀ a ∈ goodFullVertices G q
      (Finset.univ.filter (fun v : P => G.degree v ≤ q)),
      ∀ x, x ∈ row a ↔ G.Adj a x := by
    intro a ha x
    have hacore : a ∈ Erdos60.Embedding.coreVertices G q := ha
    dsimp only [row]
    rw [dif_pos hacore]
    exact hinc ⟨a,hacore⟩ x
  obtain ⟨π,hπ⟩ := embedded_good_rows_complete_graph G hG q heven hq hN hmin hcap hS hD ho row hrow
  exact ⟨L,fL,M,pp,ho,π,hπ⟩

#print axioms actual_count_based_completion
end Erdos60.Completion
