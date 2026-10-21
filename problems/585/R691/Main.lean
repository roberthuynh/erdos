import Openmath.AllHTopCritical.Original

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1PrefixR691
open QB4 B5 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ} {A B : Finset V}

/-- The original induced-support potential, expressed by its actual shores. -/
def f (q : ℕ) (G : SimpleGraph V) (A B S : Finset V) : ℤ :=
  coreDefect q G (A ∩ S) (B ∩ S)
def k (A B S : Finset V) : ℤ := (#(A ∩ S) : ℤ) - #(B ∩ S)
def g (q : ℕ) (G : SimpleGraph V) (A B S : Finset V) : ℤ :=
  (ec G (A ∩ S) (B \ S) : ℤ) - (q : ℤ) * k A B S
def sA (q : ℕ) (G : SimpleGraph V) (A B S : Finset V) : ℤ :=
  deficiency (2 * (q : ℤ) - 2) G B (A ∩ S)
def sB (q : ℕ) (G : SimpleGraph V) (A B S : Finset V) : ℤ :=
  deficiency (2 * (q : ℤ) - 2) G A (B ∩ S)

/-- Only literal original graph hypotheses used by the preceding argument. -/
structure Host (q : ℕ) (L : ℤ) (G : SimpleGraph V) (A B : Finset V) : Prop where
  large : 16384 ≤ q
  loss : 0 ≤ L ∧ L ≤ 14
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  balanced : #A = #B
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  cap : ∀ v : V, G.degree v ≤ 2 * q - 2
  total : coreDefect q G A B = 3 * (q : ℤ) - 31 + L
  proper : ∀ S : Finset V, 3 ≤ #S → #S < Fintype.card V →
    3 * (q : ℤ) - 31 + L + 1 ≤
      ((q : ℤ) - 1) * #S - ((G.induce (S : Set V)).edgeSet.ncard : ℤ)

variable {L : ℤ} (host : Host q L G A B)
include host

lemma support_partition (S : Finset V) : (A ∩ S) ∪ (B ∩ S) = S := by
  rw [← union_inter_distrib_right, host.cover, univ_inter]
lemma support_card (S : Finset V) : #(A ∩ S) + #(B ∩ S) = #S := by
  rw [← card_union_of_disjoint (host.disjoint.mono inter_subset_left inter_subset_left),
    support_partition host]
lemma f_actual (S : Finset V) : f q G A B S =
    ((q : ℤ) - 1) * #S - ((G.induce (S : Set V)).edgeSet.ncard : ℤ) := by
  have he := induced_edges_eq_ec host.disjoint host.bipartite
    (inter_subset_left : A ∩ S ⊆ A) (inter_subset_left : B ∩ S ⊆ B)
  rw [support_partition host] at he
  unfold f coreDefect
  rw [he, ← support_card host S, Nat.cast_add]
lemma floor (S : Finset V) (hs : 3 ≤ #S) (hp : #S < Fintype.card V) :
    3 * (q : ℤ) - 31 + L + 1 ≤ f q G A B S := by
  rw [f_actual host]
  exact host.proper S hs hp
lemma capA {v : V} (hv : v ∈ A) : (dg G B v : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  rw [dg_eq_degree host.bipartite hv]
  have hc := host.cap v
  have hq := host.large
  omega
lemma capB {v : V} (hv : v ∈ B) : (dg G A v : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  rw [dg_eq_degree host.bipartite.symm hv]
  have hc := host.cap v
  have hq := host.large
  omega
lemma scar_bounds (S : Finset V) :
    0 ≤ sA q G A B S ∧ sA q G A B S ≤ 3 * (q : ℤ) - 31 + L ∧
    0 ≤ sB q G A B S ∧ sB q G A B S ≤ 3 * (q : ℤ) - 31 + L := by
  have da : deficiency (2 * (q : ℤ) - 2) G B A = 3 * (q : ℤ) - 31 + L := by
    rw [deficiency_eq]
    have ht := host.total
    unfold coreDefect at ht
    have hb := host.balanced
    zify at hb
    nlinarith
  have db : deficiency (2 * (q : ℤ) - 2) G A B = 3 * (q : ℤ) - 31 + L := by
    rw [deficiency_eq, ec_comm (G := G) B A, ← host.balanced]
    rw [deficiency_eq] at da
    exact da
  refine ⟨deficiency_nonneg _ (fun v hv => capA host (inter_subset_left hv)), ?_,
    deficiency_nonneg _ (fun v hv => capB host (inter_subset_left hv)), ?_⟩
  · exact (deficiency_le_subset _ inter_subset_left (fun v hv => capA host hv)).trans_eq da
  · exact (deficiency_le_subset _ inter_subset_left (fun v hv => capB host hv)).trans_eq db

omit [Fintype V] host in
lemma cut_identity (S : Finset V) :
    g q G A B S = f q G A B S - sA q G A B S - k A B S := by
  have he := ec_sdiff_add_right (G := G) (inter_subset_left : B ∩ S ⊆ B) (A ∩ S)
  have hs : B \ (B ∩ S) = B \ S := by ext x; simp
  rw [hs] at he
  zify at he
  unfold g f sA k coreDefect
  rw [deficiency_eq]
  nlinarith

lemma f_twice (S : Finset V) : 2 * f q G A B S =
    2 * ((q : ℤ) - 1) * #S - (ec G S S : ℤ) := by
  have he := NEQAssembly.ec_self_eq_twice_induced_edges (G := G) S
  rw [f_actual host]
  zify at he
  rw [he]
  ring_nf
  rfl

lemma f_disjoint {S T : Finset V} (hd : Disjoint S T) :
    f q G A B S + f q G A B T =
      f q G A B (S ∪ T) + (ec G S T : ℤ) := by
  have he : ec G (S ∪ T) (S ∪ T) =
      ec G S S + ec G S T + ec G T S + ec G T T := by
    rw [ec_union_left hd, ec_union_right hd, ec_union_right hd]
    omega
  rw [ec_comm (G := G) T S] at he
  have hc := card_union_of_disjoint hd
  have h1 := f_twice host S
  have h2 := f_twice host T
  have h3 := f_twice host (S ∪ T)
  zify at he hc
  nlinarith

lemma f_univ : f q G A B univ = 3 * (q : ℤ) - 31 + L := by
  simpa [f] using host.total
lemma complementary (S : Finset V) :
    f q G A B S + f q G A B (univ \ S) =
      3 * (q : ℤ) - 31 + L + (ec G S (univ \ S) : ℤ) := by
  have he := f_disjoint host (disjoint_sdiff_self_right : Disjoint S (univ \ S))
  rw [union_sdiff_of_subset (subset_univ S), f_univ host] at he
  exact he

lemma boundary_identity (S : Finset V) :
    (ec G S (univ \ S) : ℤ) =
      2 * f q G A B S - sA q G A B S - sB q G A B S := by
  have he := ec_sdiff_add_right (G := G) (subset_univ S) S
  have hpart := support_partition host S
  have hdeg : ec G S univ = ec G (A ∩ S) B + ec G (B ∩ S) A := by
    conv_lhs => rw [← hpart]
    rw [ec_union_left (host.disjoint.mono inter_subset_left inter_subset_left)]
    have ha : ec G (A ∩ S) univ = ec G (A ∩ S) B := by
      rw [← host.cover, ec_union_right host.disjoint]
      have hz : ec G (A ∩ S) A = 0 := by
        have hm := ec_mono_left (G := G) (inter_subset_left : A ∩ S ⊆ A) A
        have hz := ec_internal_zero host.disjoint host.bipartite (Subset.refl A)
        omega
      omega
    have hb : ec G (B ∩ S) univ = ec G (B ∩ S) A := by
      rw [← host.cover, ec_union_right host.disjoint]
      have hz : ec G (B ∩ S) B = 0 := by
        have hm := ec_mono_left (G := G) (inter_subset_left : B ∩ S ⊆ B) B
        have hz := ec_internal_zero host.disjoint.symm host.bipartite.symm (Subset.refl B)
        omega
      omega
    rw [ha, hb]
  rw [hdeg] at he
  have hf := f_twice host S
  have hc := support_card host S
  zify at he hc
  unfold sA sB
  rw [deficiency_eq, deficiency_eq]
  nlinarith

lemma complement_identity (S : Finset V) :
    f q G A B (univ \ S) = 3 * (q : ℤ) - 31 + L +
      g q G A B S + k A B S - sB q G A B S := by
  have h1 := complementary host S
  have h2 := boundary_identity host S
  have h3 := cut_identity (q := q) (G := G) (A := A) (B := B) S
  omega

lemma cap_potential (S : Finset V) :
    ((q : ℤ) - 1) * k A B S ≤ f q G A B S := by
  have he : (ec G (A ∩ S) (B ∩ S) : ℤ) ≤
      (2 * (q : ℤ) - 2) * #(B ∩ S) := by
    rw [ec_comm]
    have hm := deficiency_nonneg (W := A ∩ S) (X := B ∩ S) (2 * (q : ℤ) - 2)
      (fun v hv => show (dg G (A ∩ S) v : ℤ) ≤ 2 * (q : ℤ) - 2 from
        (by have hh := dg_mono (G := G) (inter_subset_left : A ∩ S ⊆ A) v
            have hc := capB host (inter_subset_left hv)
            exact (show (dg G (A ∩ S) v : ℤ) ≤ dg G A v by exact_mod_cast hh).trans hc))
    rw [deficiency_eq] at hm
    omega
  unfold f k coreDefect
  nlinarith

/-- CL on every actual band cut. The scar conclusions require both actual orders. -/
theorem counting (S : Finset V) (band : g q G A B S ≤ (q : ℤ) - 1) :
    0 ≤ k A B S ∧ k A B S ≤ 3 ∧
    (3 ≤ #S → 3 ≤ #(univ \ S) →
      3 * (q : ℤ) - 31 + L + 1 - g q G A B S - k A B S ≤ sA q G A B S ∧
      sB q G A B S ≤ g q G A B S + k A B S - 1 ∧
      2 * (q : ℤ) - 32 + L ≤ sA q G A B S ∧ sB q G A B S ≤ (q : ℤ) + 1) := by
  have hq : (16384 : ℤ) ≤ q := by exact_mod_cast host.large
  have scars := scar_bounds host S
  have ident := cut_identity (q := q) (G := G) (A := A) (B := B) S
  have capf := cap_potential host S
  have kn : 0 ≤ k A B S := by
    by_contra! hn
    have hk : k A B S ≤ -1 := by omega
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ q by omega)
      (show k A B S + 1 ≤ 0 by omega)
    have he : 0 ≤ (ec G (A ∩ S) (B \ S) : ℤ) := Nat.cast_nonneg _
    unfold g at band
    nlinarith only [band, hm, he]
  have ku : k A B S ≤ 3 := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ) - 2 by omega)
      (show 0 ≤ k A B S - 4 by omega)
    have hl := host.loss
    nlinarith only [hm, ident, capf, scars.2.1, band, hq, hl.2]
  refine ⟨kn, ku, ?_⟩
  intro hs ht
  have hc := card_sdiff_add_card_eq_card (subset_univ S)
  rw [card_univ] at hc
  have fl := floor host S hs (by omega)
  have fr := floor host (univ \ S) ht (by omega)
  have hi := complement_identity host S
  omega

omit host in
lemma proper_of_disjoint {S T : Finset V} (hd : Disjoint S T) (ht : 3 ≤ #T) :
    #S < Fintype.card V := by
  have hc := card_union_of_disjoint hd
  have hu := card_le_univ (S ∪ T)
  omega

/-- Four actual cells: a tight original diagonal partition cannot be crossed
by an actual band cut in four cells all of order at least three. -/
theorem four_cell (S M : Finset V) (band : g q G A B S ≤ (q : ℤ) - 1)
    (tight : f q G A B M = 3 * (q : ℤ) - 31 + L + 1)
    (tight_complement : f q G A B (univ \ M) = 3 * (q : ℤ) - 31 + L + 1) :
    #(S ∩ M) ≤ 2 ∨ #(S ∩ (univ \ M)) ≤ 2 ∨
    #((univ \ S) ∩ M) ≤ 2 ∨ #((univ \ S) ∩ (univ \ M)) ≤ 2 := by
  by_contra! hn
  obtain ⟨hp, hr, hq, ht⟩ := hn
  have p3 : 3 ≤ #(S ∩ M) := by omega
  have r3 : 3 ≤ #(S ∩ (univ \ M)) := by omega
  have q3 : 3 ≤ #((univ \ S) ∩ M) := by omega
  have t3 : 3 ≤ #((univ \ S) ∩ (univ \ M)) := by omega
  have dpr : Disjoint (S ∩ M) (S ∩ (univ \ M)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [mem_inter, mem_sdiff, mem_univ] at hx hy
    tauto
  have dqt : Disjoint ((univ \ S) ∩ M) ((univ \ S) ∩ (univ \ M)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [mem_inter, mem_sdiff, mem_univ] at hx hy
    tauto
  have dpq : Disjoint (S ∩ M) ((univ \ S) ∩ M) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [mem_inter, mem_sdiff, mem_univ] at hx hy
    tauto
  have drt : Disjoint (S ∩ (univ \ M)) ((univ \ S) ∩ (univ \ M)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [mem_inter, mem_sdiff, mem_univ] at hx hy
    tauto
  have upr : (S ∩ M) ∪ (S ∩ (univ \ M)) = S := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff, mem_univ]
    tauto
  have uqt : ((univ \ S) ∩ M) ∪ ((univ \ S) ∩ (univ \ M)) = univ \ S := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff, mem_univ]
    tauto
  have upq : (S ∩ M) ∪ ((univ \ S) ∩ M) = M := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff, mem_univ]
    tauto
  have urt : (S ∩ (univ \ M)) ∪ ((univ \ S) ∩ (univ \ M)) = univ \ M := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff, mem_univ]
    tauto
  have fp := floor host (S ∩ M) p3 (proper_of_disjoint dpr r3)
  have fr := floor host (S ∩ (univ \ M)) r3 (proper_of_disjoint dpr.symm p3)
  have fq := floor host ((univ \ S) ∩ M) q3 (proper_of_disjoint dqt t3)
  have ft := floor host ((univ \ S) ∩ (univ \ M)) t3
    (proper_of_disjoint dqt.symm q3)
  have apr := f_disjoint host dpr
  have aqt := f_disjoint host dqt
  rw [upr] at apr
  rw [uqt] at aqt
  have boundary_le : ec G (S ∩ M) (S ∩ (univ \ M)) +
      ec G ((univ \ S) ∩ M) ((univ \ S) ∩ (univ \ M)) ≤ ec G M (univ \ M) := by
    calc
      _ ≤ ec G ((S ∩ M) ∪ ((univ \ S) ∩ M))
          ((S ∩ (univ \ M)) ∪ ((univ \ S) ∩ (univ \ M))) := by
        rw [ec_union_left dpq, ec_union_right drt, ec_union_right drt]
        omega
      _ = _ := by rw [upq, urt]
  have bm := complementary host M
  rw [tight, tight_complement] at bm
  have bs := complementary host S
  have lower : 2 * (3 * (q : ℤ) - 31 + L) + 2 ≤ (ec G S (univ \ S) : ℤ) := by
    zify at boundary_le
    linarith only [fp, fr, fq, ft, apr, aqt, boundary_le, bm, bs]
  have ck := counting host S band
  have sc := scar_bounds host S
  have bi := boundary_identity host S
  have ci := cut_identity (q := q) (G := G) (A := A) (B := B) S
  have upper : (ec G S (univ \ S) : ℤ) ≤ 3 * (q : ℤ) - 31 + L + 2 * q + 4 := by
    linarith only [bi, ci, ck.2.1, sc.2.1, sc.2.2.1, band]
  have large : (16384 : ℤ) ≤ q := by exact_mod_cast host.large
  have loss := host.loss
  linarith only [lower, upper, large, loss.1]

#check @counting
#check @four_cell
#print axioms counting
#print axioms four_cell
end Erdos585.Omit1PrefixR691
