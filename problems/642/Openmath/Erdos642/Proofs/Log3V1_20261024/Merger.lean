import Openmath.Erdos642.Proofs.Log3V1_20261024.Interface
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

   
                                                                                      
                                                                                
                                                                

                                                                                                 
                                                                                                  
                                                                                             
                                                                                                  
                                                                                               
               

                                                                                                   
                                                                                       
  

namespace Erdos642.Log3V1_20261024

open SimpleGraph

namespace Merger

universe u

variable {W : Type u} {H : SimpleGraph W}

/-! ### Joining paths by one edge -/

/-- Join two walks by one edge. -/
def joinPath {u v v' w : W} (p : H.Walk u v) (h : H.Adj v v') (q : H.Walk v' w) : H.Walk u w :=
  p.append (Walk.cons h q)

theorem support_joinPath {u v v' w : W} (p : H.Walk u v) (h : H.Adj v v') (q : H.Walk v' w) :
    (joinPath p h q).support = p.support ++ q.support := by
  simp [joinPath, Walk.support_append]

theorem mem_support_joinPath {u v v' w x : W} (p : H.Walk u v) (h : H.Adj v v') (q : H.Walk v' w) :
    x ∈ (joinPath p h q).support ↔ x ∈ p.support ∨ x ∈ q.support := by
  rw [support_joinPath, List.mem_append]

theorem edges_joinPath {u v v' w : W} (p : H.Walk u v) (h : H.Adj v v') (q : H.Walk v' w) :
    (joinPath p h q).edges = p.edges ++ s(v, v') :: q.edges := by
  simp [joinPath, Walk.edges_append]

theorem joinPath_isPath {u v v' w : W} {p : H.Walk u v} (h : H.Adj v v') {q : H.Walk v' w}
    (hp : p.IsPath) (hq : q.IsPath) (hd : ∀ x ∈ p.support, x ∉ q.support) :
    (joinPath p h q).IsPath := by
  rw [Walk.isPath_def, support_joinPath, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
  intro x hx y hy hxy
  subst hxy
  exact hd x hx hy

/-- The merge of two path components through a port path: reverse the first component, step to
the first port, run the port path, step to the second component and run it. -/
theorem merge_walk {x1 y1 x2 y2 p1 p2 : W}
    (w1 : H.Walk x1 y1) (w2 : H.Walk x2 y2) (r : H.Walk p1 p2)
    (h1 : H.Adj x1 p1) (h2 : H.Adj p2 x2)
    (hw1 : w1.IsPath) (hw2 : w2.IsPath) (hr : r.IsPath)
    (hd12 : ∀ x ∈ w1.support, x ∉ w2.support)
    (hd1r : ∀ x ∈ w1.support, x ∉ r.support)
    (hd2r : ∀ x ∈ w2.support, x ∉ r.support) :
    ∃ m : H.Walk y1 y2, m.IsPath ∧
      ∀ x, x ∈ m.support ↔ x ∈ w1.support ∨ x ∈ r.support ∨ x ∈ w2.support := by
  refine ⟨joinPath (joinPath w1.reverse h1 r) h2 w2, ?_, ?_⟩
  · refine joinPath_isPath h2 (joinPath_isPath h1 hw1.reverse hr ?_) hw2 ?_
    · intro x hx
      rw [Walk.support_reverse, List.mem_reverse] at hx
      exact hd1r x hx
    · intro x hx hx2
      rcases (mem_support_joinPath _ _ _).1 hx with hx | hx
      · rw [Walk.support_reverse, List.mem_reverse] at hx
        exact hd12 x hx hx2
      · exact hd2r x hx2 hx
  · intro x
    rw [mem_support_joinPath, mem_support_joinPath, Walk.support_reverse, List.mem_reverse]
    tauto

/-- Close a path through a disjoint connector path into a cycle. -/
theorem close_cycle {s e p1 p2 : W} (w : H.Walk s e) (r : H.Walk p2 p1)
    (hw : w.IsPath) (hr : r.IsPath) (h1 : H.Adj e p2) (h2 : H.Adj p1 s)
    (hd : ∀ x ∈ w.support, x ∉ r.support) (hse : s ≠ e) :
    ∃ (v : W) (c : H.Walk v v), c.IsCycle ∧ ∀ x ∈ w.support, x ∈ c.support := by
  refine ⟨p1, Walk.cons h2 (joinPath w h1 r), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨joinPath_isPath h1 hw hr hd, ?_⟩
    rw [edges_joinPath, List.mem_append, List.mem_cons]
    rintro (hm | hm | hm)
    · exact hd p1 (Walk.fst_mem_support_of_mem_edges w hm) r.end_mem_support
    · rcases Sym2.eq_iff.1 hm with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hd _ w.end_mem_support r.end_mem_support
      · exact hse rfl
    · exact hd s w.start_mem_support (Walk.snd_mem_support_of_mem_edges r hm)
  · intro x hx
    rw [Walk.support_cons, List.mem_cons, mem_support_joinPath]
    exact Or.inr (Or.inl hx)

/-- A path whose support contains two distinct vertices has distinct endpoints. -/
theorem endpoints_ne_of_two_le {Q : Finset W} {u v : W} (w : H.Walk u v) (hw : w.IsPath)
    (hQ : 2 ≤ Q.card) (hcov : ∀ x ∈ Q, x ∈ w.support) : u ≠ v := by
  intro huv
  subst huv
  have hsupp := Walk.nil_iff_support_eq.1 (Walk.isPath_iff_nil.1 hw)
  have hle : Q.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := hcov x hx
    have hy' := hcov y hy
    rw [hsupp, List.mem_singleton] at hx' hy'
    rw [hx', hy']
  omega

/-! ### The merger state -/

/-- One path component: a walk with its two endpoints. -/
structure Comp (H : SimpleGraph W) where
  s : W
  e : W
  w : H.Walk s e

/-- The merger invariant for a family of components: paths with endpoints in `Q`, pairwise
vertex-disjoint, covering `Q`, with every vertex in `Q` or in the used region `U`. -/
structure Good (H : SimpleGraph W) (Q : Finset W) (U : Set W) {ι : Type u} (C : ι → Comp H) :
    Prop where
  path : ∀ a, (C a).w.IsPath
  s_mem : ∀ a, (C a).s ∈ Q
  e_mem : ∀ a, (C a).e ∈ Q
  disj : ∀ a b x, x ∈ (C a).w.support → x ∈ (C b).w.support → a = b
  cover : ∀ q ∈ Q, ∃ a, q ∈ (C a).w.support
  sub : ∀ a, ∀ x ∈ (C a).w.support, x ∈ Q ∨ x ∈ U

theorem Good.mono {Q : Finset W} {U U' : Set W} {ι : Type u} {C : ι → Comp H}
    (h : Good H Q U C) (hU : U ⊆ U') : Good H Q U' C :=
  { h with sub := fun a x hx => (h.sub a x hx).imp_right fun hx => hU hx }

/-- The initial state: the isolates on `Q`. -/
theorem good_isolates (Q : Finset W) (U : Set W) :
    Good H Q U (fun q : ↥Q => (⟨q.1, q.1, Walk.nil⟩ : Comp H)) where
  path _ := Walk.IsPath.nil
  s_mem q := q.2
  e_mem q := q.2
  disj q q' x hx hx' := by
    simp only [Walk.support_nil, List.mem_singleton] at hx hx'
    exact Subtype.ext (hx.symm.trans hx')
  cover q hq := ⟨⟨q, hq⟩, by simp⟩
  sub q x hx := by
    simp only [Walk.support_nil, List.mem_singleton] at hx
    rw [hx]
    exact Or.inl q.2

/-- Vertices of a good family avoid every layer that is disjoint from `Q` and from `U`. -/
theorem Good.not_mem {Q : Finset W} {U : Set W} {ι : Type u} {C : ι → Comp H}
    (h : Good H Q U C) {A : Finset W} (hQA : Disjoint Q A) (hUA : ∀ x ∈ U, x ∉ A) :
    ∀ c x, x ∈ (C c).w.support → x ∉ A := by
  intro c x hx hxA
  rcases h.sub c x hx with hxQ | hxU
  · exact Finset.disjoint_left.1 hQA hxQ hxA
  · exact hUA x hxU hxA

/-! ### One merger phase -/

/-- One phase: in a fresh layer `A`, a good family with at least two components merges pairwise
along the port paths that `Linked` provides (ports are the images of the start vertices), and
the number of components drops to at most `(1 - γ)` times its value. -/
theorem merge_phase [DecidableEq W] (Q : Finset W) (U : Set W) (A : Finset W) (γ : ℝ)
    (hQA : Disjoint Q A) (hUA : ∀ x ∈ U, x ∉ A)
    (g : W → W) (hginj : Set.InjOn g ↑Q) (hgA : ∀ x ∈ Q, g x ∈ A)
    (hgadj : ∀ x ∈ Q, H.Adj x (g x)) (hlink : Linked H A γ)
    {ι : Type u} [Fintype ι] (C : ι → Comp H) (hC : Good H Q U C) (h2 : 2 ≤ Fintype.card ι) :
    ∃ (ι' : Type u) (_ : Fintype ι') (C' : ι' → Comp H), Good H Q (U ∪ ↑A) C' ∧
      (Fintype.card ι' : ℝ) ≤ (1 - γ) * Fintype.card ι := by
  classical
  have hCA := hC.not_mem hQA hUA
  -- the port of each component
  obtain ⟨π, hπ⟩ : ∃ π : ι → W, ∀ c, π c = g (C c).s := ⟨_, fun _ => rfl⟩
  have hπA : ∀ c, π c ∈ A := fun c => by rw [hπ]; exact hgA _ (hC.s_mem c)
  have hπadj : ∀ c, H.Adj (C c).s (π c) := fun c => by rw [hπ]; exact hgadj _ (hC.s_mem c)
  have hπinj : Function.Injective π := by
    intro c c' h
    rw [hπ, hπ] at h
    have hs : (C c).s = (C c').s :=
      hginj (Finset.mem_coe.2 (hC.s_mem c)) (Finset.mem_coe.2 (hC.s_mem c')) h
    refine hC.disj c c' (C c).s (C c).w.start_mem_support ?_
    rw [hs]
    exact (C c').w.start_mem_support
  obtain ⟨P, hP⟩ : ∃ P : Finset W, P = Finset.univ.image π := ⟨_, rfl⟩
  have hPmem : ∀ x ∈ P, ∃ c, π c = x := by
    intro x hx
    rw [hP, Finset.mem_image] at hx
    obtain ⟨c, -, hc⟩ := hx
    exact ⟨c, hc⟩
  have hPcard : P.card = Fintype.card ι := by
    rw [hP, Finset.card_image_of_injective _ hπinj, Finset.card_univ]
  have hPA : P ⊆ A := by
    intro x hx
    rw [hP, Finset.mem_image] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact hπA c
  obtain ⟨k, -, hγk, pp, hppd⟩ := hlink P hPA (by rw [hPcard]; exact h2)
  rw [hPcard] at hγk
  have hppd' : ∀ j j' x, x ∈ (pp j).walk.support → x ∈ (pp j').walk.support → j = j' := by
    intro j j' x hx hx'
    by_contra hne
    exact Set.disjoint_left.1 (hppd hne) hx hx'
  have hppA : ∀ j x, x ∈ (pp j).walk.support → x ∈ A := fun j x hx => (pp j).inside x hx
  -- the two components joined by each port path
  have hfirst : ∀ j, ∃ c, π c = (pp j).first := fun j => hPmem _ (pp j).first_mem
  have hlast : ∀ j, ∃ c, π c = (pp j).last := fun j => hPmem _ (pp j).last_mem
  choose a ha using hfirst
  choose b hb using hlast
  have hmemA : ∀ j, π (a j) ∈ (pp j).walk.support := fun j => by
    rw [ha j]; exact (pp j).walk.start_mem_support
  have hmemB : ∀ j, π (b j) ∈ (pp j).walk.support := fun j => by
    rw [hb j]; exact (pp j).walk.end_mem_support
  have hab : ∀ j, a j ≠ b j := by
    intro j h
    apply (pp j).distinct
    rw [← ha j, ← hb j, h]
  have haa : ∀ j j', a j = a j' → j = j' := fun j j' h =>
    hppd' j j' _ (hmemA j) (by rw [h]; exact hmemA j')
  have hbb : ∀ j j', b j = b j' → j = j' := fun j j' h =>
    hppd' j j' _ (hmemB j) (by rw [h]; exact hmemB j')
  have hab' : ∀ j j', a j = b j' → j = j' := fun j j' h =>
    hppd' j j' _ (hmemA j) (by rw [h]; exact hmemB j')
  -- the merged paths
  have h1 : ∀ j, H.Adj (C (a j)).s (pp j).first := fun j => by rw [← ha j]; exact hπadj _
  have h2' : ∀ j, H.Adj (pp j).last (C (b j)).s := fun j => by
    rw [← hb j]; exact (hπadj _).symm
  have hmw : ∀ j, ∃ m : H.Walk (C (a j)).e (C (b j)).e, m.IsPath ∧
      ∀ x, x ∈ m.support ↔
        x ∈ (C (a j)).w.support ∨ x ∈ (pp j).walk.support ∨ x ∈ (C (b j)).w.support :=
    fun j => merge_walk (C (a j)).w (C (b j)).w (pp j).walk (h1 j) (h2' j) (hC.path _)
      (hC.path _) (pp j).isPath (fun x hx hx' => hab j (hC.disj _ _ x hx hx'))
      (fun x hx hx' => hCA _ x hx (hppA j x hx')) (fun x hx hx' => hCA _ x hx (hppA j x hx'))
  choose mw hmwp hmws using hmw
  -- the matched components
  obtain ⟨M, hM⟩ : ∃ M : Finset ι, M = Finset.univ.image a ∪ Finset.univ.image b := ⟨_, rfl⟩
  have hmemM : ∀ d, d ∈ M ↔ ∃ j, d = a j ∨ d = b j := by
    intro d
    rw [hM]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨j, Or.inl rfl⟩
      · exact ⟨j, Or.inr rfl⟩
    · rintro ⟨j, rfl | rfl⟩
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
  have haInj : Function.Injective a := fun j j' h => haa j j' h
  have hbInj : Function.Injective b := fun j j' h => hbb j j' h
  have hMcard : M.card = 2 * k := by
    have hdis : Disjoint (Finset.univ.image a) (Finset.univ.image b) := by
      rw [Finset.disjoint_left]
      intro x hxa hxb
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxa hxb
      obtain ⟨j, rfl⟩ := hxa
      obtain ⟨j', hj'⟩ := hxb
      have hjj := hab' j j' hj'.symm
      rw [← hjj] at hj'
      exact hab j hj'.symm
    rw [hM, Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ haInj,
      Finset.card_image_of_injective _ hbInj, Finset.card_univ, Fintype.card_fin]
    omega
  have hnotM : ∀ d : ↥(Mᶜ), ∀ j, d.1 ≠ a j ∧ d.1 ≠ b j := by
    intro d j
    have hd : ¬ ∃ j, d.1 = a j ∨ d.1 = b j := fun h => Finset.mem_compl.1 d.2 ((hmemM _).2 h)
    exact ⟨fun h => hd ⟨j, Or.inl h⟩, fun h => hd ⟨j, Or.inr h⟩⟩
  -- the new family: merged pairs, then the unmatched components
  refine ⟨Fin k ⊕ ↥(Mᶜ), inferInstance,
    Sum.elim (fun j => (⟨(C (a j)).e, (C (b j)).e, mw j⟩ : Comp H)) (fun d => C d.1), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (j | d)
      · exact hmwp j
      · exact hC.path d.1
    · rintro (j | d)
      · exact hC.e_mem (a j)
      · exact hC.s_mem d.1
    · rintro (j | d)
      · exact hC.e_mem (b j)
      · exact hC.e_mem d.1
    · rintro (j | d) (j' | d') x hx hx'
      · change x ∈ (mw j).support at hx
        change x ∈ (mw j').support at hx'
        rw [hmws] at hx hx'
        suffices hjj : j = j' by rw [hjj]
        rcases hx with hx | hx | hx <;> rcases hx' with hx' | hx' | hx' <;>
          first
          | exact haa _ _ (hC.disj _ _ x hx hx')
          | exact hbb _ _ (hC.disj _ _ x hx hx')
          | exact hab' _ _ (hC.disj _ _ x hx hx')
          | exact (hab' _ _ (hC.disj _ _ x hx' hx)).symm
          | exact hppd' _ _ x hx hx'
          | exact (hCA _ x hx (hppA _ x hx')).elim
          | exact (hCA _ x hx' (hppA _ x hx)).elim
      · change x ∈ (mw j).support at hx
        change x ∈ (C d'.1).w.support at hx'
        rw [hmws] at hx
        exfalso
        rcases hx with hx | hx | hx
        · exact (hnotM d' j).1 (hC.disj _ _ x hx hx').symm
        · exact hCA _ x hx' (hppA _ x hx)
        · exact (hnotM d' j).2 (hC.disj _ _ x hx hx').symm
      · change x ∈ (C d.1).w.support at hx
        change x ∈ (mw j').support at hx'
        rw [hmws] at hx'
        exfalso
        rcases hx' with hx' | hx' | hx'
        · exact (hnotM d j').1 (hC.disj _ _ x hx hx')
        · exact hCA _ x hx (hppA _ x hx')
        · exact (hnotM d j').2 (hC.disj _ _ x hx hx')
      · change x ∈ (C d.1).w.support at hx
        change x ∈ (C d'.1).w.support at hx'
        rw [Subtype.ext (hC.disj _ _ x hx hx')]
    · intro q hq
      obtain ⟨c, hc⟩ := hC.cover q hq
      by_cases hcM : c ∈ M
      · obtain ⟨j, rfl | rfl⟩ := (hmemM c).1 hcM
        · exact ⟨Sum.inl j, (hmws j q).2 (Or.inl hc)⟩
        · exact ⟨Sum.inl j, (hmws j q).2 (Or.inr (Or.inr hc))⟩
      · exact ⟨Sum.inr ⟨c, Finset.mem_compl.2 hcM⟩, hc⟩
    · rintro (j | d) x hx
      · change x ∈ (mw j).support at hx
        rw [hmws] at hx
        rcases hx with hx | hx | hx
        · exact (hC.sub _ x hx).imp_right fun h => Set.mem_union_left _ h
        · exact Or.inr (Set.mem_union_right _ (Finset.mem_coe.2 (hppA j x hx)))
        · exact (hC.sub _ x hx).imp_right fun h => Set.mem_union_left _ h
      · exact (hC.sub d.1 x hx).imp_right fun h => Set.mem_union_left _ h
  · have hcomp := Finset.card_add_card_compl M
    have hcard' : Fintype.card (Fin k ⊕ ↥(Mᶜ)) = k + (Mᶜ).card := by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe]
    have hnat : Fintype.card (Fin k ⊕ ↥(Mᶜ)) + k = Fintype.card ι := by omega
    have hreal : (Fintype.card (Fin k ⊕ ↥(Mᶜ)) : ℝ) + k = Fintype.card ι := by
      exact_mod_cast hnat
    linarith

/-! ### Layers -/

/-- A layer of index at least `t` avoids the union of the layers of index below `t`. -/
theorem layer_away {b : ℕ} (A : Fin b → Finset W)
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (t : ℕ) (L : Fin b) (hL : t ≤ L.val) :
    ∀ x ∈ {x | ∃ j : Fin b, (j : ℕ) < t ∧ x ∈ A j}, x ∉ A L := by
  rintro x ⟨j, hj, hx⟩ hxL
  have hne : j ≠ L := fun h => by rw [h] at hj; omega
  exact Finset.disjoint_left.1 (hdisj hne) hx hxL

/-- The merger iterated over the first `t ≤ b - 1` layers: either one component remains, or the
count is at most `(1 - γ)^t |Q|`. -/
theorem merge_rounds [DecidableEq W] (Q : Finset W) (γ : ℝ) (hγ1 : γ ≤ 1) (b : ℕ)
    (A : Fin b → Finset W) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hQA : ∀ i, Disjoint Q (A i))
    (g : Fin b → W → W) (hginj : ∀ i, Set.InjOn (g i) ↑Q) (hgA : ∀ i, ∀ x ∈ Q, g i x ∈ A i)
    (hgadj : ∀ i, ∀ x ∈ Q, H.Adj x (g i x)) (hlink : ∀ i, Linked H (A i) γ) :
    ∀ t, t ≤ b - 1 → ∃ (ι : Type u) (_ : Fintype ι) (C : ι → Comp H),
      Good H Q {x | ∃ j : Fin b, (j : ℕ) < t ∧ x ∈ A j} C ∧
      (Fintype.card ι = 1 ∨ (Fintype.card ι : ℝ) ≤ (1 - γ) ^ t * Q.card) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨↥Q, inferInstance, fun q => ⟨q.1, q.1, Walk.nil⟩, good_isolates Q _, Or.inr ?_⟩
    exact le_of_eq (by rw [Fintype.card_coe, pow_zero, one_mul])
  | succ t ih =>
    intro ht
    obtain ⟨ι, _, C, hC, hcard⟩ := ih (by omega)
    have htb : t < b := by omega
    have hmono : {x | ∃ j : Fin b, (j : ℕ) < t ∧ x ∈ A j} ∪ ↑(A ⟨t, htb⟩) ⊆
        {x | ∃ j : Fin b, (j : ℕ) < t + 1 ∧ x ∈ A j} := by
      rintro x (⟨j, hj, hx⟩ | hx)
      · exact ⟨j, by omega, hx⟩
      · exact ⟨⟨t, htb⟩, by simp, Finset.mem_coe.1 hx⟩
    by_cases h2 : 2 ≤ Fintype.card ι
    · obtain ⟨ι', _, C', hC', hcard'⟩ :=
        merge_phase Q _ (A ⟨t, htb⟩) γ (hQA _) (layer_away A hdisj t ⟨t, htb⟩ le_rfl) (g ⟨t, htb⟩)
          (hginj _) (hgA _) (hgadj _) (hlink _) C hC h2
      refine ⟨ι', inferInstance, C', hC'.mono hmono, Or.inr ?_⟩
      have hc : (Fintype.card ι : ℝ) ≤ (1 - γ) ^ t * Q.card := by
        rcases hcard with h | h
        · omega
        · exact h
      calc (Fintype.card ι' : ℝ) ≤ (1 - γ) * Fintype.card ι := hcard'
        _ ≤ (1 - γ) * ((1 - γ) ^ t * Q.card) :=
          mul_le_mul_of_nonneg_left hc (by linarith)
        _ = (1 - γ) ^ (t + 1) * Q.card := by ring
    · refine ⟨ι, inferInstance, C, hC.mono (fun x hx => hmono (Or.inl hx)), ?_⟩
      rcases Nat.lt_or_ge (Fintype.card ι) 1 with h | h
      · right
        have h0 : Fintype.card ι = 0 := by omega
        rw [h0, Nat.cast_zero]
        exact mul_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _)
      · left
        omega

end Merger

open Merger

/-- **Stage 6: the occurrence-sensitive merger.** Given `b` pairwise disjoint layers, disjoint
from `Q`, each `Linked` with constant `γ` and inside-connected, and per layer an injective token
map `f i` from `Q × Bool` into the layer with each token adjacent to its vertex, if
`(1 - γ)^(b - 1) |Q| < 2` then some simple cycle of `H` passes through every vertex of `Q`. -/
theorem cycle_through_tokens {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj]
    (Q : Finset W) (hQ : 2 ≤ Q.card) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (b : ℕ) (hb : 1 ≤ b)
    (hphase : (1 - γ) ^ (b - 1) * (Q.card : ℝ) < 2)
    (A : Fin b → Finset W) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hQA : ∀ i, Disjoint Q (A i))
    (f : Fin b → (↥(Q : Set W) × Bool) → W) (hinj : ∀ i, Function.Injective (f i))
    (hmem : ∀ i z, f i z ∈ A i) (hadj : ∀ i z, H.Adj (z.1 : W) (f i z))
    (hlink : ∀ i, Linked H (A i) γ) (hconn : ∀ i, InsideConnected H (A i)) :
    ∃ (v : W) (c : H.Walk v v), c.IsCycle ∧ ∀ x ∈ Q, x ∈ c.support := by
  classical
  -- the port maps: the `false` token of each vertex of `Q`
  obtain ⟨g, hg⟩ : ∃ g : Fin b → W → W,
      ∀ i x (hx : x ∈ Q), g i x = f i (⟨x, Finset.mem_coe.2 hx⟩, false) :=
    ⟨fun i x => if hx : x ∈ Q then f i (⟨x, Finset.mem_coe.2 hx⟩, false) else x,
      fun i x hx => dif_pos hx⟩
  have hgA : ∀ i, ∀ x ∈ Q, g i x ∈ A i := fun i x hx => by rw [hg i x hx]; exact hmem i _
  have hgadj : ∀ i, ∀ x ∈ Q, H.Adj x (g i x) := fun i x hx => by
    rw [hg i x hx]; exact hadj i (⟨x, Finset.mem_coe.2 hx⟩, false)
  have hginj : ∀ i, Set.InjOn (g i) ↑Q := by
    intro i x hx y hy h
    rw [hg i x (Finset.mem_coe.1 hx), hg i y (Finset.mem_coe.1 hy)] at h
    exact congrArg (fun z : ↥(Q : Set W) × Bool => (z.1 : W)) (hinj i h)
  -- merge over the first `b - 1` layers
  obtain ⟨ι, _, C, hC, hcard⟩ :=
    merge_rounds Q γ hγ1 b A hdisj hQA g hginj hgA hgadj hlink (b - 1) le_rfl
  obtain ⟨q0, hq0⟩ : Q.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a0, -⟩ := hC.cover q0 hq0
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨a0⟩
  have hone : Fintype.card ι = 1 := by
    rcases hcard with h | h
    · exact h
    · have hlt : (Fintype.card ι : ℝ) < 2 := lt_of_le_of_lt h hphase
      have hlt' : Fintype.card ι < 2 := by exact_mod_cast hlt
      omega
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hone
  have hQa : ∀ x ∈ Q, x ∈ (C a).w.support := fun x hx => by
    obtain ⟨c, hc⟩ := hC.cover x hx
    rw [ha c] at hc
    exact hc
  have hse : (C a).s ≠ (C a).e := endpoints_ne_of_two_le (C a).w (hC.path a) hQ hQa
  -- close the last path through the last layer
  have hL : b - 1 < b := by omega
  have hUL := layer_away A hdisj (b - 1) ⟨b - 1, hL⟩ le_rfl
  have hCL := hC.not_mem (hQA ⟨b - 1, hL⟩) hUL
  have hne : g ⟨b - 1, hL⟩ (C a).e ≠ g ⟨b - 1, hL⟩ (C a).s := fun h =>
    hse (hginj _ (Finset.mem_coe.2 (hC.s_mem a)) (Finset.mem_coe.2 (hC.e_mem a)) h.symm)
  obtain ⟨r, hr, hrA⟩ := hconn ⟨b - 1, hL⟩ _ (hgA _ _ (hC.e_mem a)) _ (hgA _ _ (hC.s_mem a)) hne
  obtain ⟨v, c, hc, hcs⟩ := close_cycle (C a).w r (hC.path a) hr (hgadj _ _ (hC.e_mem a))
    (hgadj _ _ (hC.s_mem a)).symm (fun x hx hxr => hCL a x hx (hrA x hxr)) hse
  exact ⟨v, c, hc, fun x hx => hcs x (hQa x hx)⟩

end Erdos642.Log3V1_20261024
