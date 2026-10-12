import Openmath.Proofs.PaperSupport.BqMinSizeScalar
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.BqMinimumSupport
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/- Minimum original dense source, chosen without any NoRegular premise. -/
omit [DecidableEq V] in
theorem minimum_dense_source (q : ℕ) (U W : Finset V)
    (hn : 2 ≤ #U + #W) (he : (q - 1) * (#U + #W) ≤ ec G U W + q) :
    ∃ P ⊆ U, ∃ Q ⊆ W, 2 ≤ #P + #Q ∧
      (q - 1) * (#P + #Q) ≤ ec G P Q + q ∧
      ∀ X ⊆ P, ∀ Y ⊆ Q, 2 ≤ #X + #Y → #X + #Y < #P + #Q →
        (q - 1) * (#X + #Y) ≤ ec G X Y + q → False := by
  classical
  let candidate : ℕ → Prop := fun t =>
    ∃ P ⊆ U, ∃ Q ⊆ W, #P + #Q = t ∧ 2 ≤ t ∧
      (q - 1) * (#P + #Q) ≤ ec G P Q + q
  have hex : ∃ t, candidate t := ⟨#U + #W,U,Subset.refl U,W,Subset.refl W,rfl,hn,he⟩
  obtain ⟨P,hPU,Q,hQW,hnum,horder,hdense⟩ := Nat.find_spec hex
  refine ⟨P,hPU,Q,hQW,by omega,hdense,?_⟩
  intro X hX Y hY hlarge hproper hDense
  have hcand : candidate (#X + #Y) :=
    ⟨X,hX.trans hPU,Y,hY.trans hQW,rfl,hlarge,hDense⟩
  exact Nat.find_min hex (by omega) hcand

theorem original_edge_count_mono {K : SimpleGraph V} [DecidableRel K.Adj]
    (hKG : K ≤ G) (X Y : Finset V) : ec K X Y ≤ ec G X Y :=
  sum_le_sum fun _ _ => dg_mono_graph hKG Y _

open scoped Classical in
/-- All critical inputs come from the minimum source and original thinning. -/
theorem thinned_source {q : ℕ} {P Q : Finset V} (hq : 5 ≤ q)
    (hPQ : Disjoint P Q) (hn : 2 ≤ #P + #Q)
    (he : (q - 1) * (#P + #Q) ≤ ec G P Q + q)
    (hcapP : ∀ a ∈ P, dg G Q a ≤ 2 * q - 2)
    (hcapQ : ∀ a ∈ Q, dg G P a ≤ 2 * q - 2)
    (hminimum : ∀ X ⊆ P, ∀ Y ⊆ Q, 2 ≤ #X + #Y → #X + #Y < #P + #Q →
      (q - 1) * (#X + #Y) ≤ ec G X Y + q → False) :
    ∃ K : SimpleGraph V, K ≤ G ∧
      ec K P Q + q = (q - 1) * (#P + #Q) ∧
      (∀ a ∈ P, q ≤ dg K Q a) ∧ (∀ a ∈ P, dg K Q a ≤ 2 * q - 2) ∧
      (∀ a ∈ Q, q ≤ dg K P a) ∧ (∀ a ∈ Q, dg K P a ≤ 2 * q - 2) ∧
      Bq.Sparse q K P Q := by
  classical
  have hlarge := dense_order hq hn he
  have hnontrunc : q ≤ (q - 1) * (#P + #Q) := by
    have hm := Nat.mul_le_mul_right (#P + #Q) (by omega : 1 ≤ q - 1)
    simp only [one_mul] at hm
    omega
  let m := (q - 1) * (#P + #Q) - q
  have hm : m ≤ ec G P Q := by dsimp [m];omega
  obtain ⟨K,hKG,hmK⟩ := thin_pair (G := G) hPQ m hm
  let _ : DecidableRel K.Adj := Classical.decRel _
  have heK : ec K P Q + q = (q - 1) * (#P + #Q) := by rw [hmK];dsimp [m];omega
  have hcapPK : ∀ a ∈ P, dg K Q a ≤ 2 * q - 2 := fun a ha =>
    (dg_mono_graph hKG Q a).trans (hcapP a ha)
  have hcapQK : ∀ a ∈ Q, dg K P a ≤ 2 * q - 2 := fun a ha =>
    (dg_mono_graph hKG P a).trans (hcapQ a ha)
  have hsmaller : ∀ X ⊆ P, ∀ Y ⊆ Q, 2 ≤ #X + #Y → #X + #Y < #P + #Q →
      (q - 1) * (#X + #Y) ≤ ec K X Y + q → False := by
    intro X hX Y hY htwo hlt hdense
    exact hminimum X hX Y hY htwo hlt
      (hdense.trans (Nat.add_le_add_right (original_edge_count_mono hKG X Y) q))
  have hminP : ∀ a ∈ P, q ≤ dg K Q a := by
    intro a ha
    by_contra! hlow
    have hcard := card_erase_add_one ha
    have hec := Bq.ec_erase_add (G := K) (W := Q) ha
    have hprod : (q - 1) * (#(P.erase a) + #Q) + (q - 1) =
        (q - 1) * (#P + #Q) := by
      calc _ = (q - 1) * ((#(P.erase a) + #Q) + 1) := by ring
        _ = _ := by congr 1;omega
    exact hsmaller (P.erase a) (erase_subset a P) Q (Subset.refl Q)
      (by omega) (by omega) (by omega)
  have hminQ : ∀ a ∈ Q, q ≤ dg K P a := by
    intro a ha
    by_contra! hlow
    have hcard := card_erase_add_one ha
    have hec := Bq.ec_erase_add (G := K) (W := P) ha
    rw [ec_comm (G := K) (Q.erase a) P,ec_comm (G := K) Q P] at hec
    have hprod : (q - 1) * (#P + #(Q.erase a)) + (q - 1) =
        (q - 1) * (#P + #Q) := by
      calc _ = (q - 1) * ((#P + #(Q.erase a)) + 1) := by ring
        _ = _ := by congr 1;omega
    exact hsmaller P (Subset.refl P) (Q.erase a) (erase_subset a Q)
      (by omega) (by omega) (by omega)
  have hs : Bq.Sparse q K P Q := by
    intro X hX Y hY hthree hlt
    by_cases hsmall : #X + #Y ≤ 2 * q - 1
    · exact Bq.small_potential (G := K) hq hthree hsmall
    · by_contra! hfail
      have hpot : potential (2 * (q : ℤ) - 2) K X Y =
          2 * (((q - 1) * (#X + #Y) : ℕ) : ℤ) - 2 * (ec K X Y : ℤ) := by
        unfold potential
        push_cast
        rw [Bq.pred_cast hq]
        ring
      rw [hpot] at hfail
      exact hsmaller X hX Y hY (by omega) hlt (by omega)
  exact ⟨K,hKG,heK,hminP,hcapPK,hminQ,hcapQK,hs⟩
end Erdos585.BqMinimumSupport
