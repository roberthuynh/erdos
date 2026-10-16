import IndexedDesign
import FullRowIntersection
import ExceptionalSet

/-! Actual dual indexed input for the count-based completion proof. Retained
full graph rows are the design points; ORIGINAL graph vertices are independent
line labels. Incidence is actual graph adjacency. No embedding is assumed. -/
namespace Erdos60.Embedding
open Finset
open scoped Classical
variable {P : Type*} [Fintype P]

noncomputable def coreVertices (G : SimpleGraph P) (q : ℕ) : Finset P :=
  Completion.goodFullVertices G q (Finset.univ.filter (fun x => G.degree x ≤ q))

def CorePoint (G : SimpleGraph P) (q : ℕ) := ↥(coreVertices G q)

noncomputable instance (G : SimpleGraph P) (q : ℕ) : Fintype (CorePoint G q) := by
  unfold CorePoint
  infer_instance

theorem corePoint_good (G : SimpleGraph P) (q : ℕ) (a : CorePoint G q) :
    G.degree a.val = q+1 ∧
      100*((G.neighborFinset a.val).filter (fun x => G.degree x ≤ q)).card < q := by
  have hh := Completion.goodFullVertices_neighbor_budget G q
    (Finset.univ.filter (fun x => G.degree x ≤ q)) a.property
  have he : G.neighborFinset a.val ∩ Finset.univ.filter (fun x => G.degree x ≤ q) =
      (G.neighborFinset a.val).filter (fun x => G.degree x ≤ q) := by
    ext x; simp
  rwa [he] at hh

/-- The actual retained-row indexed design, not an embedding interface. -/
noncomputable def coreRowDesign (G : SimpleGraph P) (hG : Completion.NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card P = q^2+q+1) (hcap : ∀ x, G.degree x ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q-1)).card ≤ q) :
    IndexedDesign q (CorePoint G q) P where
  inc := fun a x => G.Adj a.val x
  point_degree := by
    intro a
    have ha := (corePoint_good G q a).1
    have hc := G.card_neighborSet_eq_degree a.val
    change Fintype.card {x : P // G.Adj a.val x} = G.degree a.val at hc
    rw [Nat.card_eq_fintype_card,hc,ha]
  unique_join := by
    intro a b hab
    have ha := corePoint_good G q a
    have hb := corePoint_good G q b
    have hv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    exact Completion.full_rows_intersect G hG q hq heven hN hcap hS hD
      ha.1 hb.1 hv ha.2 hb.2

@[simp] theorem coreRowDesign_inc (G : SimpleGraph P) (hG : Completion.NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card P = q^2+q+1) (hcap : ∀ x, G.degree x ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q-1)).card ≤ q)
    (a : CorePoint G q) (x : P) :
    (coreRowDesign G hG q hq heven hN hcap hS hD).inc a x ↔ G.Adj a.val x := Iff.rfl

theorem card_corePoint (G : SimpleGraph P) (q : ℕ) :
    Fintype.card (CorePoint G q) = (coreVertices G q).card := by
  exact Fintype.card_coe _

theorem corePoint_card_le (G : SimpleGraph P) (q : ℕ) :
    Fintype.card (CorePoint G q) ≤ Fintype.card P := by
  rw [card_corePoint]
  exact Finset.card_le_univ _

/-- Exact missing-point equation, on the original indexed line-label carrier. -/
theorem corePoint_missing_eq (G : SimpleGraph P) (q : ℕ)
    (hN : Fintype.card P = q^2+q+1) :
    Fintype.card (CorePoint G q) + ((q^2+q+1)-Fintype.card (CorePoint G q)) = q^2+q+1 := by
  have hc := corePoint_card_le G q
  rw [hN] at hc
  omega

/-- Actual retained-row density needed by the specialized book embedding route. -/
theorem corePoint_missing_budget (G : SimpleGraph P) (hG : Completion.NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q)
    (hN : Fintype.card P = q^2+q+1) (hcap : ∀ x, G.degree x ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q) :
    500*((q^2+q+1)-Fintype.card (CorePoint G q)) ≤ 501*q := by
  have hA := Completion.goodFullVertices_card_lower G hG q hq hN hcap hS
  have hc := corePoint_missing_eq G q hN
  rw [card_corePoint] at hc ⊢
  change (q:ℝ)^2-(q:ℝ)/1000+1-11000 ≤ ((coreVertices G q).card:ℝ) at hA
  have hcR : ((coreVertices G q).card:ℝ)+
      (((q^2+q+1)-(coreVertices G q).card:ℕ):ℝ) = (q:ℝ)^2+q+1 := by exact_mod_cast hc
  have hqR : (100000000:ℝ) ≤ q := by exact_mod_cast hq
  have hh : (500:ℝ)*(((q^2+q+1)-(coreVertices G q).card:ℕ):ℝ) ≤ 501*q := by linarith
  exact_mod_cast hh

/-- Density also supplies the nondegenerate size hypothesis used to derive
all indexed-line degree caps inside the book proof. -/
theorem corePoint_dense (G : SimpleGraph P) (hG : Completion.NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q)
    (hN : Fintype.card P = q^2+q+1) (hcap : ∀ x, G.degree x ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q) :
    q+1 < Fintype.card (CorePoint G q) := by
  have hb := corePoint_missing_budget G hG q hq hN hcap hS
  have he := corePoint_missing_eq G q hN
  have hh := Nat.mul_le_mul_left q (show 2 ≤ q by omega)
  nlinarith

#print axioms corePoint_dense
#print axioms coreRowDesign
#print axioms corePoint_missing_budget
end Erdos60.Embedding
