import CompletionBasic

/-! Source correspondence: COUNT-BASED-COMPLETION-PROOF-v2.md, Section 2 first
paragraph, and Section 1 local matching fact. Frozen source SHA256:
d07eaa46889ac5a9808a097f281e43c25a768e5057e19ddefe5b72952d9eacbb.
The result constructs the actual matching with one isolated neighbor and the
actual outside-cell partition. The isolated neighbor is NOT identified with the
specified degree-q neighbor here. That next source step requires the separate
cell-deficiency count using global deficient/deep-vertex budgets, which this
bounded module does not formalize or assume. No completion theorem is asserted.
-/
namespace Erdos60.Completion
variable {V : Type*} [Fintype V]

/-- An odd C4-free neighborhood contains a locally isolated vertex. -/
theorem exists_isolated_neighbor (G : SimpleGraph V) (hG : NoFourCycle G)
    (v : V) (hodd : letI := Classical.decRel G.Adj; Odd (G.degree v)) :
    ∃ w, G.Adj v w ∧ ∀ a, G.Adj v a → ¬G.Adj w a := by
  classical
  by_contra hn
  let A := {a : V // G.Adj v a}
  let H : SimpleGraph A := G.comap Subtype.val
  have hd : ∀ a : A, H.degree a = 1 := by
    intro a
    have hex : ∃ b, G.Adj v b ∧ G.Adj a.val b := by
      by_contra hb
      exact hn ⟨a.val,a.property,fun b hvb hab => hb ⟨b,hvb,hab⟩⟩
    obtain ⟨b,hvb,hab⟩ := hex
    let b' : A := ⟨b,hvb⟩
    have he : H.neighborFinset a = {b'} := by
      ext c
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
      constructor
      · intro hac
        exact Subtype.ext (neighborhood_neighbor_unique hG a.property c.property hvb hac hab)
      · intro hc
        exact hc ▸ hab
    rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
    simp
  have hs := H.sum_degrees_eq_twice_card_edges
  simp only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hs
  have hc : Fintype.card A = G.degree v := by
    change Fintype.card (G.neighborSet v) = G.degree v
    exact G.card_neighborSet_eq_degree v
  obtain ⟨k,hk⟩ := hodd
  omega

/-- Exact matching and outside-cell partition at a regular vertex.
The isolated neighbor is not yet identified with the deficient neighbor. -/
theorem regular_vertex_structure (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (v low : V) (hv : letI := Classical.decRel G.Adj; G.degree v = q+1)
    (hlow : G.Adj v low) (hdl : letI := Classical.decRel G.Adj; G.degree low = q)
    (hfull : ∀ a, G.Adj v a → a ≠ low →
      letI := Classical.decRel G.Adj; G.degree a = q+1) :
    ∃ w, G.Adj v w ∧
      (∀ a, G.Adj v a → ¬G.Adj w a) ∧
      (∀ a, G.Adj v a → a ≠ w → ∃! b, G.Adj v b ∧ G.Adj a b) ∧
      (∀ x, x ≠ v → ¬G.Adj v x → ∃! a, G.Adj v a ∧ x ∈ cell G v a) := by
  classical
  have hqpos : 0 < q := by
    have h := (G.degree_pos low).mpr (show ¬G.IsIsolated low from fun h => h v hlow.symm)
    omega
  have hodd : Odd (G.degree v) := by
    rw [hv]
    obtain ⟨k,hk⟩ := heven
    exact ⟨k,by omega⟩
  obtain ⟨w,hvw,hw⟩ := exists_isolated_neighbor G hG v hodd
  let A := {a : V // G.Adj v a}
  let T := (a : A) × {b : V // G.Adj a.val b ∧ b ≠ v}
  have hAc : Fintype.card A = q+1 := by
    change Fintype.card (G.neighborSet v) = q+1
    rw [G.card_neighborSet_eq_degree,hv]
  have hcbranch : ∀ a : A, Fintype.card {b : V // G.Adj a.val b ∧ b ≠ v} = G.degree a.val - 1 := by
    intro a
    have he : Finset.univ.filter (fun b => G.Adj a.val b ∧ b ≠ v) =
        (G.neighborFinset a.val).erase v := by ext b; simp [and_comm]
    rw [Fintype.card_subtype,he,Finset.card_erase_of_mem
      (show v ∈ G.neighborFinset a.val by simpa using a.property.symm),
      G.card_neighborFinset_eq_degree]
  have hTc : Fintype.card T = q^2+q-1 := by
    rw [show Fintype.card T = ∑ a : A, Fintype.card {b : V // G.Adj a.val b ∧ b ≠ v} from Fintype.card_sigma]
    simp_rw [hcbranch]
    let la : A := ⟨low,hlow⟩
    rw [← Finset.add_sum_erase Finset.univ (fun a : A => G.degree a.val - 1) (Finset.mem_univ la)]
    have hh : ∀ a ∈ Finset.univ.erase la, G.degree a.val - 1 = q := by
      intro a ha
      have hne : a.val ≠ low := by
        intro h
        exact (Finset.mem_erase.mp ha).1 (Subtype.ext h)
      rw [hfull a.val a.property hne]
      omega
    rw [Finset.sum_congr rfl hh]
    change G.degree low - 1 + _ = _
    rw [hdl]
    simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ la),
      Finset.card_univ,hAc,smul_eq_mul]
    have heq : q*q = q^2 := by ring
    simp only [Nat.add_sub_cancel]
    rw [heq]
    omega
  let f : T → {b : V // b ≠ v ∧ b ≠ w} := fun p =>
    ⟨p.2.val,p.2.property.2,by
      intro h
      exact hw p.1.val p.1.property (h ▸ p.2.property.1).symm⟩
  have hi : Function.Injective f := by
    intro p r h
    have he : p.2.val = r.2.val := congrArg Subtype.val h
    have ha : p.1.val = r.1.val := common_neighbor_unique hG p.2.property.2
      p.2.property.1.symm p.1.property (he ▸ r.2.property.1.symm) r.1.property
    cases p with | mk a b =>
      cases r with | mk c d =>
        have hac : a = c := Subtype.ext ha
        subst c
        have hbd : b = d := Subtype.ext he
        subst d
        rfl
  have hcardout : Fintype.card {b : V // b ≠ v ∧ b ≠ w} = q^2+q-1 := by
    have he : Finset.univ.filter (fun b : V => b ≠ v ∧ b ≠ w) = (Finset.univ.erase v).erase w := by
      ext b; simp [and_comm]
    rw [Fintype.card_subtype,he,Finset.card_erase_of_mem (by simp [hvw.ne.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ v),Finset.card_univ,hN]
    omega
  have hs := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi,hTc.trans hcardout.symm⟩).2
  refine ⟨w,hvw,hw,?_,?_⟩
  · intro a hva haw
    obtain ⟨p,hp⟩ := hs ⟨a,hva.ne.symm,haw⟩
    have he : p.2.val = a := congrArg Subtype.val hp
    refine ⟨p.1.val,⟨p.1.property,he ▸ p.2.property.1.symm⟩,?_⟩
    intro b hb
    exact neighborhood_neighbor_unique hG hva hb.1 p.1.property hb.2 (he ▸ p.2.property.1.symm)
  · intro x hx hnx
    have hxw : x ≠ w := by intro h; exact hnx (h.symm ▸ hvw)
    obtain ⟨p,hp⟩ := hs ⟨x,hx,hxw⟩
    have he : p.2.val = x := congrArg Subtype.val hp
    refine ⟨p.1.val,⟨p.1.property,he ▸ p.2.property.1,hx,hnx⟩,?_⟩
    intro a ha
    exact common_neighbor_unique hG hx ha.2.1.symm ha.1 (he ▸ p.2.property.1.symm) p.1.property

#print axioms exists_isolated_neighbor
#print axioms regular_vertex_structure
end Erdos60.Completion
