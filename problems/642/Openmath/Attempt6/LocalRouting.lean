import Openmath.Attempt6.PrivateLeaves
import Openmath.Attempt6.PairedRouting
import Openmath.Attempt6.LocalRoutingCharge
import Openmath.Attempt6.RainbowRoutingBudgets
import Openmath.Attempt6.RoutingSelection

/-! Local original-edge deletion and prescribed-pair avoidance. -/
namespace Erdos585.Attempt6.LocalRouting
open SimpleGraph Reachability PairedRouting
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def withoutWW (G : SimpleGraph V) (W : Finset V) : SimpleGraph V := by
  classical
  exact { Adj := fun x y => G.Adj x y ∧ ¬(x ∈ W ∧ y ∈ W)
          symm := ⟨fun _ _ h => ⟨h.1.symm, fun hmem => h.2 ⟨hmem.2, hmem.1⟩⟩⟩
          loopless := ⟨fun _ h => h.1.ne rfl⟩ }

noncomputable def localGraph (G : SimpleGraph V) (Q W : Finset V) : SimpleGraph V := by
  classical
  exact { Adj := fun x y => G.Adj x y ∧ x ∈ Q ∪ W ∧ y ∈ Q ∪ W
          symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
          loopless := ⟨fun _ h => h.1.ne rfl⟩ }

noncomputable instance localGraph_decidable (G : SimpleGraph V) (Q W : Finset V) :
    DecidableRel (localGraph G Q W).Adj := fun _ _ => Classical.propDecidable _

theorem localGraph_le (G : SimpleGraph V) (Q W : Finset V) : localGraph G Q W ≤ G :=
  fun _ _ h => h.1

theorem withoutWW_le (G : SimpleGraph V) (W : Finset V) : withoutWW G W ≤ G :=
  fun _ _ h => h.1

/-- W-W deletion preserves reservoir balls with arbitrary ambient seeds. -/
theorem ball_subset_withoutWW (G : SimpleGraph V) (Q W U : Finset V)
    (hQW : Disjoint Q W) (F : Finset (Sym2 V)) (ell : ℕ) :
    reservoirBall (G.deleteEdges F) U Q ell ⊆
      reservoirBall ((withoutWW G W).deleteEdges F) U Q ell := by
  classical
  intro v hv
  obtain ⟨hvQ, u, hu, p, hp, hs⟩ := mem_reservoirBall.mp hv
  have he : ∀ e ∈ p.edges, e ∈ ((withoutWW G W).deleteEdges F).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | hf x y =>
      intro hxy
      have hadj := SimpleGraph.deleteEdges_adj.mp (p.adj_of_mem_edges hxy)
      change ((withoutWW G W).deleteEdges F).Adj x y
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨⟨hadj.1, ?_⟩, hadj.2⟩
      intro hWW
      have hx := (hs x (p.fst_mem_support_of_mem_edges hxy)).resolve_right
        (fun hxQ => Finset.disjoint_left.mp hQW hxQ hWW.1)
      have hy := (hs y (p.snd_mem_support_of_mem_edges hxy)).resolve_right
        (fun hyQ => Finset.disjoint_left.mp hQW hyQ hWW.2)
      exact hadj.1.ne (hx.trans hy.symm)
  refine mem_reservoirBall.mpr ⟨hvQ, u, hu, p.transfer _ he, ?_, ?_⟩
  · simpa using hp
  · simpa using hs

theorem local_deletion_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q W S : Finset V) :
    incidentDeletion (localGraph G Q W) S ⊆ G.edgeFinset := by
  classical
  exact (incidentDeletion_subset_edges _ S).trans
    (SimpleGraph.edgeFinset_mono (localGraph_le G Q W))

/-- Only local edges at S are needed to exclude S from these paths. -/
theorem local_deleted_walk_avoids (G : SimpleGraph V) (Q W S : Finset V)
    (hQW : Disjoint Q W) (hSQ : S ⊆ Q) {a b : V} (ha : a ∈ W) (hb : b ∈ W)
    (p : ((withoutWW G W).deleteEdges (incidentDeletion (localGraph G Q W) S)).Walk a b)
    (hinside : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ Q) :
    ∀ x ∈ p.support, x ∉ S := by
  classical
  intro x hx hxS
  have hxa : x ≠ a := fun he => Finset.disjoint_left.mp hQW (he ▸ hSQ hxS) ha
  have hxb : x ≠ b := fun he => Finset.disjoint_left.mp hQW (he ▸ hSQ hxS) hb
  obtain ⟨e, he, hxe⟩ := ((Walk.mem_support_iff_exists_mem_edges).mp hx).resolve_left hxb
  have hs : ∀ y ∈ p.support, y ∈ Q ∪ W := by
    intro y hy
    by_cases hya : y = a
    · exact Finset.mem_union_right _ (hya ▸ ha)
    by_cases hyb : y = b
    · exact Finset.mem_union_right _ (hyb ▸ hb)
    exact Finset.mem_union_left _ (hinside y hy hya hyb)
  have heH : e ∈ (localGraph G Q W).edgeSet := by
    induction e using Sym2.inductionOn with
    | hf y z =>
      have hadj := SimpleGraph.deleteEdges_adj.mp (p.adj_of_mem_edges he)
      exact ⟨hadj.1.1, hs y (p.fst_mem_support_of_mem_edges he),
        hs z (p.snd_mem_support_of_mem_edges he)⟩
  have heF : e ∈ incidentDeletion (localGraph G Q W) S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hxS, ?_⟩
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨heH, hxe⟩
  have henot := p.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_deleteEdges] at henot
  exact henot.2 heF


/-- The charged degree is precisely the original degree into Q union W. -/
theorem local_degree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (Q W : Finset V)
    {v : V} (hv : v ∈ Q ∪ W) :
    (localGraph G Q W).degree v = ((Q ∪ W).filter (G.Adj v)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  change (G.Adj v w ∧ v ∈ Q ∪ W ∧ w ∈ Q ∪ W) ↔ w ∈ Q ∪ W ∧ G.Adj v w
  simp [hv, and_comm]

/-- An actual same-index leaf path avoiding S, using only the local degree
charge at Q. Its interior is nonempty and contained in Q. -/
theorem local_paired_avoidance {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q W S : Finset V)
    (hQW : Disjoint Q W) (hSQ : S ⊆ Q)
    (ell t n : ℕ) (lambda M : ℝ) (ht : 1 ≤ t)
    (hQ : 4 * t - 2 ≤ Q.card) (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hbudget : M * S.card ≤ lambda * t)
    (z w : I → V) (hz : Function.Injective z) (hw : Function.Injective w)
    (hzW : ∀ i, z i ∈ W) (hwW : ∀ i, w i ∈ W) (hzw : ∀ i, z i ≠ w i)
    (hI : 2 * t - 1 ≤ Fintype.card I) :
    ∃ i, ∃ p : G.Walk (z i) (w i), p.IsPath ∧
      (p.length : ℝ) ≤ 4 * ell * logTwo (n : ℝ) ∧
      (∀ x ∈ p.support, x ≠ z i → x ≠ w i → x ∈ Q) ∧
      (∀ x ∈ p.support, x ∉ S) ∧ ∃ x ∈ p.support, x ∈ Q := by
  classical
  let H := localGraph G Q W
  let F := incidentDeletion H S
  let K := (withoutWW G W).deleteEdges F
  have hFG : F ⊆ G.edgeFinset := local_deletion_subset G Q W S
  have hF : (F.card : ℝ) ≤ lambda * t := by
    apply le_trans (incidentDeletion_card_le_real H S M ?_) hbudget
    intro v hv
    change ((localGraph G Q W).degree v : ℝ) ≤ M
    rw [local_degree_eq G Q W (Finset.mem_union_left _ (hSQ hv))]
    exact hM v (hSQ hv)
  have hexpand : ∀ U : Finset V, U.card = t →
      (Q.card : ℝ) / 2 < (reservoirBall K U Q ell).card := by
    intro U hUt
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    have horig := hreach U hUne F
      (by simpa only [Finset.subset_iff, SimpleGraph.mem_edgeFinset] using hFG)
      (by simpa only [hUt] using hF)
    have hc : ((reservoirBall (G.deleteEdges F) U Q ell).card : ℝ) ≤
        (reservoirBall K U Q ell).card := by
      exact_mod_cast Finset.card_le_card (ball_subset_withoutWW G Q W U hQW F ell)
    exact horig.trans_le hc
  obtain ⟨i, p, hp, hlen, hins⟩ := paired_routing K Q ell t n ht hQ horder hexpand z w hz hw hI
  have hav : ∀ x ∈ p.support, x ∉ S :=
    local_deleted_walk_avoids G Q W S hQW hSQ (hzW i) (hwW i) p hins
  have hmid : ∃ x ∈ p.support, x ∈ Q := by
    have hadj : K.Adj (z i) p.snd := Walk.adj_snd (Walk.not_nil_of_ne (hzw i))
    have hcW : p.snd ∉ W := fun hc => (SimpleGraph.deleteEdges_adj.mp hadj).1.2 ⟨hzW i, hc⟩
    have hca : p.snd ≠ z i := fun h => hcW (h.symm ▸ hzW i)
    have hcb : p.snd ≠ w i := fun h => hcW (h.symm ▸ hwW i)
    have hcs : p.snd ∈ p.support := p.getVert_mem_support 1
    exact ⟨p.snd, hcs, hins p.snd hcs hca hcb⟩
  have hKG : K ≤ G := fun _ _ h => (SimpleGraph.deleteEdges_adj.mp h).1.1
  refine ⟨i, p.mapLe hKG, hp.mapLe hKG, ?_, ?_, ?_, ?_⟩
  · simpa using hlen
  · simpa using hins
  · simpa using hav
  · simpa using hmid


                                                                       
                                                         
theorem exists_private_leaves_local_load {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (terminal : I → V) (W : Finset V)
    (M L lambda delta D : ℝ) (hlambda : 0 < lambda) (hlambdaM : lambda ≤ M)
    (hL : 1 ≤ L) (hdelta : 0 < delta) (hD : 0 ≤ D)
    (hleft : ∀ i, delta ≤ ((W.filter (G.Adj (terminal i))).card : ℝ))
    (hright : ∀ v ∈ W, ((Finset.univ.filter (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12)) :
    ∃ f : I × Fin (RainbowRoutingBudgets.privateCopies (M * L ^ 12 / lambda)) → V,
      Function.Injective f ∧ ∀ ij, f ij ∈ W ∧ G.Adj (terminal ij.1) (f ij) := by
  classical
  let a := M * L ^ 12 / lambda
  have ha := RainbowRoutingBudgets.local_scale_ge_one M L lambda hlambda hlambdaM hL
  have hM : 0 < M := hlambda.trans_le hlambdaM
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hnorm := RainbowRoutingBudgets.local_load_normalization M L lambda D delta
    hM hLp hlambda hload
  have hHall := (RainbowRoutingBudgets.hall_load_budget a D delta ha hD hdelta hnorm).2
  apply exists_private_graph_leaves G terminal W (RainbowRoutingBudgets.privateCopies a)
    (Nat.ceil delta) (Nat.ceil_pos.mpr hdelta)
  · intro i
    exact Nat.ceil_le.mpr (hleft i)
  · intro v hv
    have hmul := mul_le_mul_of_nonneg_left (hright v hv)
      (Nat.cast_nonneg (RainbowRoutingBudgets.privateCopies a) :
        (0 : ℝ) ≤ RainbowRoutingBudgets.privateCopies a)
    have hc := (hmul.trans hHall.le).trans (Nat.le_ceil delta)
    exact_mod_cast hc

                                                                        
                                         
theorem private_leaf_volume {I : Type*} [Fintype I] [DecidableEq I]
    (W : Finset V) (q : ℕ) (f : (I × Bool) × Fin q → V)
    (hf : Function.Injective f) (hfW : ∀ ij, f ij ∈ W) :
    2 * Fintype.card I * q ≤ W.card := by
  classical
  have hsub : (Finset.univ.image f) ⊆ W := by
    intro v hv
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hv
    exact hfW ij
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hc
  simpa [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hc

                                                                            
                                                                          
                                                   
theorem private_leaf_family_avoidance {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q W : Finset V)
    (hQW : Disjoint Q W) (hWQ : W.card ≤ Q.card)
    (ell rank n : ℕ) (M L lambda : ℝ)
    (hlambda : 0 < lambda) (hlambdaM : lambda ≤ M) (hL : 1 ≤ L)
    (horder : Fintype.card V ≤ n) (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hrank : (rank : ℝ) ≤ L ^ 6) (hpath : 4 * ell * logTwo (n : ℝ) ≤ rank)
    (f : (I × Bool) × Fin (RainbowRoutingBudgets.privateCopies (M * L ^ 12 / lambda)) → V)
    (hf : Function.Injective f) (hfW : ∀ ij, f ij ∈ W)
    (J : Finset I) (hJ : J.Nonempty) (S : Finset V) (hSQ : S ⊆ Q)
    (hS : S.card ≤ rank * (2 * rank * (J.card - 1))) :
    ∃ i ∈ J, ∃ j, ∃ p : G.Walk (f ((i, false), j)) (f ((i, true), j)),
      p.IsPath ∧ p.length ≤ rank ∧
      (∀ x ∈ p.support, x ≠ f ((i, false), j) → x ≠ f ((i, true), j) → x ∈ Q) ∧
      (∀ x ∈ p.support, x ∉ S) ∧ ∃ x ∈ p.support, x ∈ Q := by
  classical
  let a := M * L ^ 12 / lambda
  let q := RainbowRoutingBudgets.privateCopies a
  let t := RainbowRoutingBudgets.deletionScale a J.card
  have ha : 1 ≤ a := RainbowRoutingBudgets.local_scale_ge_one M L lambda hlambda hlambdaM hL
  have hm : 1 ≤ J.card := hJ.card_pos
  have hmr : J.card ≤ Fintype.card I := Finset.card_le_univ J
  have hb := RainbowRoutingBudgets.leaf_pair_budget a ha J.card (Fintype.card I) hm hmr
  have ht : 1 ≤ t := (RainbowRoutingBudgets.deletion_scale_bounds a ha J.card hm).1
  have hQ : 4 * t - 2 ≤ Q.card := by
    have hv := private_leaf_volume W q f hf hfW
    exact hb.2.2.trans (hv.trans hWQ)
  have hMp : 0 < M := hlambda.trans_le hlambdaM
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  let b : ℝ := 2 * rank * ((J.card - 1 : ℕ) : ℝ)
  have hbpos : 0 ≤ b := by dsimp [b]; positivity
  have hbsmall : b ≤ 2 * ((J.card - 1 : ℕ) : ℝ) * L ^ 6 := by
    have hx := mul_le_mul_of_nonneg_left hrank
      (by positivity : (0 : ℝ) ≤ 2 * ((J.card - 1 : ℕ) : ℝ))
    dsimp [b]
    nlinarith
  have hunion : (S.card : ℝ) ≤ b * L ^ 6 := by
    have hc : (S.card : ℝ) ≤ (rank : ℝ) * b := by dsimp [b]; exact_mod_cast hS
    have hmR := mul_le_mul_of_nonneg_left hrank hbpos
    nlinarith
  have hScard := RainbowRoutingBudgets.union_size_budget L b S.card J.card hbsmall hunion
  have hbudget : M * S.card ≤ lambda * t := by
    apply RainbowRoutingBudgets.doubled_deleted_edge_budget M L lambda (M * S.card)
      J.card hMp hLp hlambda
    have hh := mul_le_mul_of_nonneg_left hScard hMp.le
    nlinarith
  let z : {i : I // i ∈ J} × Fin q → V := fun ij => f ((ij.1.val, false), ij.2)
  let w : {i : I // i ∈ J} × Fin q → V := fun ij => f ((ij.1.val, true), ij.2)
  have hz : Function.Injective z := by
    intro x y h
    have he := hf h
    have hi : x.1.val = y.1.val := congrArg (fun v => v.1.1) he
    have hj : x.2 = y.2 := congrArg (fun v : (I × Bool) × Fin q => v.2) he
    exact Prod.ext (Subtype.ext hi) hj
  have hw : Function.Injective w := by
    intro x y h
    have he := hf h
    have hi : x.1.val = y.1.val := congrArg (fun v => v.1.1) he
    have hj : x.2 = y.2 := congrArg (fun v : (I × Bool) × Fin q => v.2) he
    exact Prod.ext (Subtype.ext hi) hj
  have hzw : ∀ ij, z ij ≠ w ij := by
    intro ij h
    have he := congrArg (fun v => v.1.2) (hf h)
    simp at he
  have hI : 2 * t - 1 ≤ Fintype.card ({i : I // i ∈ J} × Fin q) := by
    simpa [Fintype.card_prod, Nat.mul_comm, q, t] using hb.2.1
  obtain ⟨ij, p, hp, hlen, hins, hav, hmid⟩ := local_paired_avoidance G Q W S hQW hSQ
    ell t n lambda M ht hQ horder hreach hM hbudget z w hz hw
    (fun ij => hfW _) (fun ij => hfW _) hzw hI
  refine ⟨ij.1.val, ij.1.property, ij.2, p, hp, ?_, hins, hav, hmid⟩
  exact_mod_cast hlen.trans hpath


/-- Package the exact original path interior for the checked finite routing
selection interface. Its nonemptiness comes from an actual Q vertex. -/
theorem supportsRoute_of_local_path (G : SimpleGraph V) (Q S : Finset V) (rank : ℕ)
    {a b : V} (haQ : a ∉ Q) (hbQ : b ∉ Q)
    (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length ≤ rank)
    (hins : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ Q)
    (hav : ∀ x ∈ p.support, x ∉ S) (hmid : ∃ x ∈ p.support, x ∈ Q) :
    ∃ T, SupportsRoute G Q rank a b T ∧ Disjoint T S := by
  classical
  let T := (p.support.toFinset.erase a).erase b
  have hmem : ∀ x, x ∈ T ↔ x ∈ p.support ∧ x ≠ a ∧ x ≠ b := by
    intro x
    simp [T, and_comm, and_left_comm, and_assoc]
  have hTQ : T ⊆ Q := by
    intro x hx
    obtain ⟨hs, hxa, hxb⟩ := (hmem x).mp hx
    exact hins x hs hxa hxb
  have hTne : T.Nonempty := by
    obtain ⟨x, hx, hxQ⟩ := hmid
    refine ⟨x, (hmem x).mpr ⟨hx, ?_, ?_⟩⟩
    · exact fun he => haQ (he ▸ hxQ)
    · exact fun he => hbQ (he ▸ hxQ)
  have hlenT : T.card ≤ rank := by
    have hsupport : p.support.toFinset.card = p.length + 1 := by
      rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
    have hT : T ⊆ p.support.toFinset.erase a := Finset.erase_subset _ _
    have hc := Finset.card_le_card hT
    have ha : a ∈ p.support.toFinset := by simp
    have he : (p.support.toFinset.erase a).card = p.support.toFinset.card - 1 := Finset.card_erase_of_mem ha
    rw [he, hsupport] at hc
    omega
  have heq : p.support.toFinset = insert a (insert b T) := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp
    by_cases hxb : x = b
    · subst x
      simp
    simp [hmem, hxa, hxb]
  refine ⟨T, ⟨hTne, hTQ, ?_, ?_, hlenT, p, hp, hlen, heq⟩, ?_⟩
  · exact fun h => haQ (hTQ h)
  · exact fun h => hbQ (hTQ h)
  · apply Finset.disjoint_left.mpr
    intro x hx hxS
    exact hav x ((hmem x).mp hx).1 hxS

                                                                          
                                                                              
                                                            
theorem exists_private_leaf_routing_avoidance {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (terminal : I × Bool → V)
    (Q W : Finset V) (hQW : Disjoint Q W) (hWQ : W.card ≤ Q.card)
    (ell rank n : ℕ) (M L lambda delta D : ℝ)
    (hlambda : 0 < lambda) (hlambdaM : lambda ≤ M) (hL : 1 ≤ L)
    (hdelta : 0 < delta) (hD : 0 ≤ D) (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hrank : (rank : ℝ) ≤ L ^ 6) (hpath : 4 * ell * logTwo (n : ℝ) ≤ rank)
    (hleft : ∀ i, delta ≤ ((W.filter (G.Adj (terminal i))).card : ℝ))
    (hright : ∀ v ∈ W, ((Finset.univ.filter (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12)) :
    ∃ f : (I × Bool) × Fin (RainbowRoutingBudgets.privateCopies (M * L ^ 12 / lambda)) → V,
      Function.Injective f ∧ (∀ ij, f ij ∈ W ∧ G.Adj (terminal ij.1) (f ij)) ∧
      ∀ J : Finset I, J.Nonempty → ∀ S : Finset V,
        S.card ≤ rank * (2 * rank * (J.card - 1)) →
        ∃ i ∈ J, ∃ j, ∃ T,
          SupportsRoute G Q rank (f ((i, false), j)) (f ((i, true), j)) T ∧ Disjoint T S := by
  classical
  obtain ⟨f, hf, hfadj⟩ := exists_private_leaves_local_load G terminal W M L lambda delta D
    hlambda hlambdaM hL hdelta hD hleft hright hload
  refine ⟨f, hf, hfadj, ?_⟩
  intro J hJ S hS
  have hSsmall : (S ∩ Q).card ≤ rank * (2 * rank * (J.card - 1)) :=
    (Finset.card_le_card Finset.inter_subset_left).trans hS
  obtain ⟨i, hi, j, p, hp, hlen, hins, hav, hmid⟩ := private_leaf_family_avoidance G Q W
    hQW hWQ ell rank n M L lambda hlambda hlambdaM hL horder hreach hM hrank hpath
    f hf (fun ij => (hfadj ij).1) J hJ (S ∩ Q) Finset.inter_subset_right hSsmall
  have haQ : f ((i, false), j) ∉ Q := fun h => Finset.disjoint_left.mp hQW h (hfadj _).1
  have hbQ : f ((i, true), j) ∉ Q := fun h => Finset.disjoint_left.mp hQW h (hfadj _).1
  obtain ⟨T, hroute, hdisj⟩ := supportsRoute_of_local_path G Q (S ∩ Q) rank haQ hbQ p hp hlen hins hav hmid
  refine ⟨i, hi, j, T, hroute, ?_⟩
  apply Finset.disjoint_left.mpr
  intro x hx hxS
  exact Finset.disjoint_left.mp hdisj hx (Finset.mem_inter.mpr ⟨hxS, hroute.2.1 hx⟩)

                                                                              
                                                               
theorem select_disjoint_routes_with_copies {I C : Type*}
    [Fintype I] [DecidableEq I] [Fintype C]
    (G : SimpleGraph V) (Q : Finset V) (rank : ℕ) (z w : I → C → V)
    (havoid : ∀ J : Finset I, J.Nonempty → ∀ S : Finset V,
      S.card ≤ rank * (2 * rank * (J.card - 1)) →
      ∃ i ∈ J, ∃ c, ∃ T, SupportsRoute G Q rank (z i c) (w i c) T ∧ Disjoint T S) :
    ∃ copy : I → C, ∃ T : I → Finset V,
      (∀ i, SupportsRoute G Q rank (z i (copy i)) (w i (copy i)) (T i)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) := by
  classical
  let H : I → Finset (Finset V) := fun i => Finset.univ.filter
    (fun T => ∃ c, SupportsRoute G Q rank (z i c) (w i c) T)
  have hmem : ∀ i T, T ∈ H i ↔ ∃ c, SupportsRoute G Q rank (z i c) (w i c) T := by
    intro i T
    simp [H]
  have hrank : ∀ i T, T ∈ H i → T.card ≤ rank := by
    intro i T hT
    obtain ⟨c, hc⟩ := (hmem i T).mp hT
    exact hc.2.2.2.2.1
  have hne : ∀ i T, T ∈ H i → T.Nonempty := by
    intro i T hT
    obtain ⟨c, hc⟩ := (hmem i T).mp hT
    exact hc.1
  have ha : ∀ J : Finset I, J.Nonempty → ∀ S : Finset V,
      S.card ≤ rank * (2 * rank * (J.card - 1)) →
      ∃ i ∈ J, ∃ T ∈ H i, Disjoint T S := by
    intro J hJ S hS
    obtain ⟨i, hi, c, T, hT, hd⟩ := havoid J hJ S hS
    exact ⟨i, hi, T, (hmem i T).mpr ⟨c, hT⟩, hd⟩
  obtain ⟨T, hT, hpair⟩ := rainbow_matching_of_small_set_avoidance H rank hrank hne ha
  have hc : ∀ i, ∃ c, SupportsRoute G Q rank (z i c) (w i c) (T i) :=
    fun i => (hmem i (T i)).mp (hT i)
  choose copy hcopy using hc
  exact ⟨copy, T, hcopy, hpair⟩

                                                                         
                                                                      
                                                                
theorem local_routing_central {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (terminal : I × Bool → V)
    (Q W : Finset V) (hQW : Disjoint Q W) (hWQ : W.card ≤ Q.card)
    (ell rank n : ℕ) (M L lambda delta D : ℝ)
    (hlambda : 0 < lambda) (hlambdaM : lambda ≤ M) (hL : 1 ≤ L)
    (hdelta : 0 < delta) (hD : 0 ≤ D) (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hrank : (rank : ℝ) ≤ L ^ 6) (hpath : 4 * ell * logTwo (n : ℝ) ≤ rank)
    (hleft : ∀ i, delta ≤ ((W.filter (G.Adj (terminal i))).card : ℝ))
    (hright : ∀ v ∈ W, ((Finset.univ.filter (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12)) :
    ∃ f : (I × Bool) × Fin (RainbowRoutingBudgets.privateCopies (M * L ^ 12 / lambda)) → V,
      Function.Injective f ∧ (∀ ij, f ij ∈ W ∧ G.Adj (terminal ij.1) (f ij)) ∧
      ∃ copy : I → Fin (RainbowRoutingBudgets.privateCopies (M * L ^ 12 / lambda)),
      ∃ T : I → Finset V,
        (∀ i, SupportsRoute G Q rank (f ((i, false), copy i)) (f ((i, true), copy i)) (T i)) ∧
        Pairwise (fun i j => Disjoint (T i) (T j)) := by
  obtain ⟨f, hf, hfadj, hav⟩ := exists_private_leaf_routing_avoidance G terminal Q W hQW hWQ
    ell rank n M L lambda delta D hlambda hlambdaM hL hdelta hD horder hreach hM
    hrank hpath hleft hright hload
  obtain ⟨copy, T, hT, hd⟩ := select_disjoint_routes_with_copies G Q rank
    (fun i c => f ((i, false), c)) (fun i c => f ((i, true), c)) hav
  exact ⟨f, hf, hfadj, copy, T, hT, hd⟩

/-- Reachability of a reservoir of size at least three forces lambda below
the local degree ceiling; deleting one vertex incidence otherwise isolates it. -/
theorem lambda_lt_local_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q W : Finset V) (ell : ℕ) (lambda M : ℝ) (hQ : 3 ≤ Q.card)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M) : lambda < M := by
  classical
  by_contra hlt
  have hMl : M ≤ lambda := le_of_not_gt hlt
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < Q.card by omega)
  let H := localGraph G Q W
  let F := incidentDeletion H {v}
  have hF : (F.card : ℝ) ≤ lambda * ({v} : Finset V).card := by
    have hc := incidentDeletion_card_le_real H {v} M (by
      intro x hx
      have he : x = v := by simpa using hx
      subst x
      change ((localGraph G Q W).degree v : ℝ) ≤ M
      rw [local_degree_eq G Q W (Finset.mem_union_left _ hv)]
      exact hM v hv)
    simpa using hc.trans (by simpa using hMl)
  have hFG := local_deletion_subset G Q W {v}
  have hb := hreach {v} (Finset.singleton_nonempty v) F
    (by simpa only [Finset.subset_iff, SimpleGraph.mem_edgeFinset] using hFG) hF
  have hsub : reservoirBall (G.deleteEdges F) {v} Q ell ⊆ {v} := by
    intro x hx
    obtain ⟨hxQ, u, hu, p, hlen, hs⟩ := mem_reservoirBall.mp hx
    have huv : u = v := by simpa using hu
    subst u
    by_cases hxv : x = v
    · simpa using hxv
    have hfirst : (G.deleteEdges F).Adj v p.snd := Walk.adj_snd (Walk.not_nil_of_ne (Ne.symm hxv))
    have hadj := SimpleGraph.deleteEdges_adj.mp hfirst
    have hsq : p.snd ∈ Q := by
      rcases hs p.snd (p.getVert_mem_support 1) with he | he
      · exact he.symm ▸ hv
      · exact he
    have hi : H.Adj v p.snd := ⟨hadj.1, Finset.mem_union_left _ hv,
      Finset.mem_union_left _ hsq⟩
    have hiF : s(v, p.snd) ∈ F := by
      apply Finset.mem_biUnion.mpr
      refine ⟨v, Finset.mem_singleton_self v, ?_⟩
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨hi, by simp⟩
    exact False.elim (hadj.2 hiF)
  have hc : (reservoirBall (G.deleteEdges F) {v} Q ell).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hcr : ((reservoirBall (G.deleteEdges F) {v} Q ell).card : ℝ) ≤ 1 := by exact_mod_cast hc
  have hQr : (3 : ℝ) ≤ Q.card := by exact_mod_cast hQ
  linarith

/-- The selected actual central routes with the local inequality derived
from reservoir reachability itself. -/
theorem local_routing_central_of_large_reservoir {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (terminal : I × Bool → V)
    (Q W : Finset V) (hQW : Disjoint Q W) (hWQ : W.card ≤ Q.card) (hQ : 3 ≤ Q.card)
    (ell rank n : ℕ) (M L lambda delta D : ℝ)
    (hlambda : 0 < lambda) (hL : 1 ≤ L)
    (hdelta : 0 < delta) (hD : 0 ≤ D) (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hrank : (rank : ℝ) ≤ L ^ 6) (hpath : 4 * ell * logTwo (n : ℝ) ≤ rank)
    (hleft : ∀ i, delta ≤ ((W.filter (G.Adj (terminal i))).card : ℝ))
    (hright : ∀ v ∈ W, ((Finset.univ.filter (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12)) :
    ∃ f : (I × Bool) × Fin (RainbowRoutingBudgets.privateCopies (M * L ^ 12 / lambda)) → V,
      Function.Injective f ∧ (∀ ij, f ij ∈ W ∧ G.Adj (terminal ij.1) (f ij)) ∧
      ∃ copy : I → Fin (RainbowRoutingBudgets.privateCopies (M * L ^ 12 / lambda)),
      ∃ T : I → Finset V,
        (∀ i, SupportsRoute G Q rank (f ((i, false), copy i)) (f ((i, true), copy i)) (T i)) ∧
        Pairwise (fun i j => Disjoint (T i) (T j)) := by
  have hlambdaM : lambda ≤ M := (lambda_lt_local_degree G Q W ell lambda M hQ hreach hM).le
  exact local_routing_central G terminal Q W hQW hWQ ell rank n M L lambda delta D
    hlambda hlambdaM hL hdelta hD horder hreach hM hrank hpath hleft hright hload

end Erdos585.Attempt6.LocalRouting
