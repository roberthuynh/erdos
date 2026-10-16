import L17HCq.Original
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open Finset SimpleGraph BqLowerFamily
namespace Erdos585.L17HCq

/-- Actual data, independent of any success or factor-exclusion proof. -/
structure LabeledGraph where
  carrier : Type
  finite : Fintype carrier
  eqDec : DecidableEq carrier
  graph : SimpleGraph carrier
  adjDec : DecidableRel graph.Adj
  A : Finset carrier
  B : Finset carrier
  labels : @Labeling carrier finite

namespace LabeledGraph

def order (D : LabeledGraph) : ℕ := @Fintype.card D.carrier D.finite

def label (D : LabeledGraph) : D.carrier → ℕ := @Labeling.label D.carrier D.finite D.labels

def IsGood (q c : ℕ) (D : LabeledGraph) : Prop :=
  letI := D.finite
  letI := D.eqDec
  letI := D.adjDec
  Good q c D.graph D.A D.B

def neighbors (q : ℕ) (D : LabeledGraph) : Finset D.carrier :=
  letI := D.finite
  letI := D.adjDec
  BqLowerFamily.nextNeighbors q D.graph D.A D.B D.labels

def step (q : ℕ) (D : LabeledGraph) : LabeledGraph :=
  letI := D.finite
  letI := D.eqDec
  letI := D.adjDec
  { carrier := Option D.carrier
    finite := inferInstance
    eqDec := inferInstance
    graph := extendGraph D.graph (D.neighbors q)
    adjDec := inferInstance
    A := nextA D.A D.B
    B := nextB D.A D.B
    labels := D.labels.extend }

theorem order_step (q : ℕ) (D : LabeledGraph) : (D.step q).order=D.order+1 := by
  letI := D.finite
  change Fintype.card (Option D.carrier)=Fintype.card D.carrier+1
  exact Fintype.card_option

theorem good_step (q c : ℕ) (D : LabeledGraph) (hq : 5 ≤ q)
    (hc : (q-1)*(q-2)+1 ≤ c) (h : D.IsGood q c) : (D.step q).IsGood q c := by
  letI := D.finite
  letI := D.eqDec
  letI := D.adjDec
  exact literalNext_good q c D.graph D.A D.B D.labels hq hc h

theorem neighbors_card (q c : ℕ) (D : LabeledGraph) (hq : 5 ≤ q)
    (hc : (q-1)*(q-2)+1 ≤ c) (h : D.IsGood q c) : (D.neighbors q).card=q-1 := by
  letI := D.finite
  letI := D.eqDec
  letI := D.adjDec
  exact Erdos585.L17HCq.nextNeighbors_card q c D.graph D.A D.B D.labels hq hc h

theorem neighbors_least (q : ℕ) (D : LabeledGraph) :
    letI := D.finite
    letI := D.adjDec
    ∀ (v w : D.carrier), v ∈ D.neighbors q →
      w ∈ (if D.A.card ≤ D.B.card then D.B else D.A).filter
        (fun x => D.graph.degree x ≤ 2*(q-1)-1) →
      w ∉ D.neighbors q → D.label v ≤ D.label w := by
  letI := D.finite
  letI := D.adjDec
  intro v w hv hw hwn
  exact BqLowerFamily.nextNeighbors_least q D.graph D.A D.B D.labels v w hv hw hwn

theorem step_old_edge (q : ℕ) (D : LabeledGraph) (v w : D.carrier) :
    (D.step q).graph.Adj (some v) (some w) ↔ D.graph.Adj v w := Iff.rfl

theorem step_new_edge (q : ℕ) (D : LabeledGraph) (v : D.carrier) :
    (D.step q).graph.Adj none (some v) ↔ v ∈ D.neighbors q := Iff.rfl

theorem step_label_old (q : ℕ) (D : LabeledGraph) (v : D.carrier) :
    (D.step q).label (some v)=D.label v := rfl

theorem step_label_new (q : ℕ) (D : LabeledGraph) :
    (D.step q).label none=D.order := rfl

theorem labels_range (D : LabeledGraph) :
    (@Finset.univ D.carrier D.finite).image D.label=range D.order :=
  @Labeling.image_range D.carrier D.finite D.labels

end LabeledGraph

def iterate (q : ℕ) (seed : LabeledGraph) : ℕ → LabeledGraph
  | 0 => seed
  | k+1 => (iterate q seed k).step q

theorem iterate_order (q : ℕ) (seed : LabeledGraph) (k : ℕ) :
    (iterate q seed k).order=seed.order+k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate,LabeledGraph.order_step,ih];omega

theorem iterate_good (q c : ℕ) (seed : LabeledGraph) (hq : 5 ≤ q)
    (hc : (q-1)*(q-2)+1 ≤ c) (hs : seed.IsGood q c) (k : ℕ) :
    (iterate q seed k).IsGood q c := by
  induction k with
  | zero => exact hs
  | succ k ih => exact LabeledGraph.good_step q c (iterate q seed k) hq hc ih

def hcqSeedLabel (q : ℕ) : SeedVertex q → ℕ
  | .inl (.inl i) => i.val
  | .inl (.inr a) => q+1+a.val
  | .inr (.inl j) => q+3+j.val
  | .inr (.inr _) => 2*q+6

def hcqSeedLabeling (q : ℕ) : Labeling (SeedVertex q) where
  label := hcqSeedLabel q
  injective := by
    intro x y h
    rcases x with (i | a) | (j | u) <;> rcases y with (i' | a') | (j' | u')
    all_goals simp only [hcqSeedLabel] at h
    all_goals try (simp only [Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.ext_iff])
    all_goals first | exact Subsingleton.elim _ _ | omega
  bounded := by
    intro x
    have hc : Fintype.card (SeedVertex q)=2*q+7 := by
      simp [SeedVertex,SeedLeft,SeedRight,Fintype.card_sum];omega
    rw [hc]
    rcases x with (i | a) | (j | u) <;> dsimp [hcqSeedLabel] <;> omega

def hcqSeedData (q : ℕ) : LabeledGraph where
  carrier := SeedVertex q
  finite := inferInstance
  eqDec := inferInstance
  graph := hcqSeedGraph q
  adjDec := inferInstance
  A := hcqSeedA q
  B := hcqSeedB q
  labels := hcqSeedLabeling q

def l17SeedData : LabeledGraph where
  carrier := Fin 17
  finite := inferInstance
  eqDec := inferInstance
  graph := l17SeedGraph
  adjDec := inferInstance
  A := l17SeedA
  B := l17SeedB
  labels := l17SeedLabeling

def hcqFamily (q k : ℕ) : LabeledGraph := iterate q (hcqSeedData q) k
def l17Family (k : ℕ) : LabeledGraph := iterate 5 l17SeedData k

theorem hcq_family_good (q : ℕ) (hq : 5 ≤ q) (k : ℕ) :
    (hcqFamily q k).IsGood q (hcqDeficit q) :=
  iterate_good q (hcqDeficit q) (hcqSeedData q) hq (hcq_deficit_guard q hq)
    (hcq_seed_good q hq) k

theorem l17_family_good (k : ℕ) : (l17Family k).IsGood 5 13 :=
  iterate_good 5 13 l17SeedData (by decide) (by decide) l17_seed_good k

theorem hcq_family_order (q k : ℕ) : (hcqFamily q k).order=2*q+7+k := by
  rw [hcqFamily,iterate_order]
  change Fintype.card (SeedVertex q)+k=2*q+7+k
  simp only [SeedVertex,SeedLeft,SeedRight,Fintype.card_sum,Fintype.card_fin,Fintype.card_unique]
  omega

theorem l17_family_order (k : ℕ) : (l17Family k).order=17+k := by
  rw [l17Family,iterate_order]
  rfl
end Erdos585.L17HCq
