import Openmath.AllHTopCritical.Numeric

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHTopCritical
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}
variable {h q : ℕ} {A B R T : Finset V}

omit [Fintype V] in
lemma ec_le_product (X Y : Finset V) : ec G X Y ≤ #X * #Y := by
  calc
    _ ≤ ∑ _v ∈ X, #Y := sum_le_sum fun v _ => dg_le_card (G := G) Y v
    _ = _ := by simp

lemma dg_le_ambient (X : Finset V) (v : V) : dg G X v ≤ G.degree v := by
  change #(X.filter (G.Adj v)) ≤ #(G.neighborFinset v)
  apply card_le_card
  intro w hw
  exact (G.mem_neighborFinset v w).mpr (mem_filter.mp hw).2

omit [Fintype V] in
lemma saturated_of_zero {X Y : Finset V} {D : ℕ}
    (hc : ∀ v ∈ X, dg G Y v ≤ D)
    (hz : deficiency (D : ℤ) G Y X = 0) {v : V} (hv : v ∈ X) :
    dg G Y v = D := by
  have hall := (sum_eq_zero_iff_of_nonneg (fun x hx =>
    sub_nonneg.mpr (show (dg G Y x : ℤ) ≤ D by exact_mod_cast hc x hx))).1 hz v hv
  omega

omit [Fintype V] in
lemma coreDefect_symm (X Y : Finset V) : coreDefect q G X Y = coreDefect q G Y X := by
  unfold coreDefect
  rw [ec_comm]
  ring

namespace Host
variable (host : Host h q G A B)
include host

lemma shore_order : #A + #B = Fintype.card V := by
  have hc := card_union_of_disjoint host.disjoint
  rw [host.cover, card_univ] at hc
  exact hc.symm

lemma minA (v : V) (hv : v ∈ A) : q ≤ dg G B v := by
  rw [dg_eq_degree host.bipartite hv]
  exact host.min_degree v
lemma minB (v : V) (hv : v ∈ B) : q ≤ dg G A v := by
  rw [dg_eq_degree host.bipartite.symm hv]
  exact host.min_degree v
lemma capA (v : V) (hv : v ∈ A) : dg G B v ≤ 2*q-2 := by
  rw [dg_eq_degree host.bipartite hv]
  exact host.cap_degree v
lemma capB (v : V) (hv : v ∈ B) : dg G A v ≤ 2*q-2 := by
  rw [dg_eq_degree host.bipartite.symm hv]
  exact host.cap_degree v
lemma capA_int (v : V) (hv : v ∈ A) : (dg G B v : ℤ) ≤ 2*q-2 := by
  have hc := host.capA v hv
  have hq := host.parameters.q_pos
  omega
lemma capB_int (v : V) (hv : v ∈ B) : (dg G A v : ℤ) ≤ 2*q-2 := by
  have hc := host.capB v hv
  have hq := host.parameters.q_pos
  omega

lemma deficiency_A : deficiency (2*(q : ℤ)-2) G B A = constant h q := by
  rw [deficiency_eq, ec_eq_ncard host.bipartite]
  have he := host.edges
  have ho := host.shore_order
  have hb := host.balanced
  have hq := host.parameters.q_pos
  zify at he ho hb
  have hqm : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
  rw [hqm] at he
  nlinarith

lemma deficiency_B : deficiency (2*(q : ℤ)-2) G A B = constant h q := by
  have he := host.deficiency_A
  rw [deficiency_eq] at he ⊢
  rw [ec_comm (G := G) B A]
  rw [host.balanced] at he
  exact he

lemma paired_floor {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    (hl : 2*q ≤ #X+#Y) (hp : #X+#Y < Fintype.card V) :
    (constant h q : ℤ)+1 ≤ coreDefect q G X Y := by
  have hd := host.disjoint.mono hX hY
  have hc := card_union_of_disjoint hd
  have hf := host.proper (X∪Y) (by omega) (by omega)
  rw [induced_edges_eq_ec host.disjoint host.bipartite hX hY, hc] at hf
  simpa [coreDefect, Nat.cast_add] using hf

end Host

namespace TopCore
variable (core : TopCore h q G A B R T)
include core
lemma subset : R ⊆ A := by rw [core.canonical]; exact canonical_subset q A B T
lemma optimizer : Optimizer q G A B T R := by
  rw [core.canonical]
  exact strict_optimizer q A B T
lemma first_deficit : coreDefect q G R T = (constant h q : ℤ)+1 := by
  have ht := twice_coreDefect (G := G) q R T
  rw [core.potential] at ht
  omega
lemma forward (p : Parameters h q) :
    (ec G R (B\T) : ℤ) = ((h : ℤ)-1)*q-h+2 := by
  have he := core.optimizer.outward_edges (j := 0) core.T_subset
  rw [core.height] at he
  have hi := core.imbalance
  have hs := p.surplus_cast
  zify at hi
  norm_num at he
  nlinarith
end TopCore

end Erdos585.AllHTopCritical
