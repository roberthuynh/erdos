import Openmath.Attempt6.RoutingSelection

                                                                           
namespace Erdos585.Attempt6
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem append_private_leaf_edges (Q W : Finset V) (r : ℕ) {x y a b : V}
    (hxa : G.Adj x a) (hby : G.Adj b y) (hxy : x ≠ y)
    (hx : x ∉ Q ∪ W) (hy : y ∉ Q ∪ W) (ha : a ∈ W) (hb : b ∈ W)
    {T : Finset V} (hT : SupportsRoute G Q r a b T) :
    SupportsRoute G (Q ∪ W) (r + 2) x y (insert a (insert b T)) := by
  classical
  obtain ⟨hTne, hTQ, haT, hbT, hcard, p, hp, hlen, hsupport⟩ := hT
  have hS : insert a (insert b T) ⊆ Q ∪ W := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_union_right Q ha
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_right Q hb
      · exact Finset.mem_union_left W (hTQ hv)
  have hpS : ∀ v ∈ p.support, v ∈ Q ∪ W := by
    intro v hv
    apply hS
    rw [← hsupport]
    exact List.mem_toFinset.mpr hv
  have hyp : y ∉ p.support := fun hyP => hy (hpS y hyP)
  have hxp : x ∉ p.support := fun hxP => hx (hpS x hxP)
  have hxconcat : x ∉ (p.concat hby).support := by
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
    exact not_or.mpr ⟨hxp, hxy⟩
  refine ⟨Finset.insert_nonempty a _, hS, (fun hv => hx (hS hv)),
    (fun hv => hy (hS hv)), ?_, Walk.cons hxa (p.concat hby),
    (hp.concat hyp hby).cons hxconcat, ?_, ?_⟩
  · have h1 := Finset.card_insert_le a (insert b T)
    have h2 := Finset.card_insert_le b T
    omega
  · simp only [Walk.length_cons, Walk.length_concat]
    omega
  · simp only [Walk.support_cons, Walk.support_concat, List.toFinset_cons,
      List.toFinset_append, List.toFinset_nil, hsupport]
    ext v
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto

theorem private_leaf_interiors_disjoint {I : Type*} (Q W : Finset V)
    (hQW : Disjoint Q W) (a b : I → V) (T : I → Finset V)
    (ha : ∀ i, a i ∈ W) (hb : ∀ i, b i ∈ W)
    (hT : ∀ i, T i ⊆ Q)
    (hleaf : Function.Injective (fun z : I × Bool => if z.2 then b z.1 else a z.1))
    (hdis : Pairwise (fun i j => Disjoint (T i) (T j))) :
    Pairwise (fun i j => Disjoint (insert (a i) (insert (b i) (T i)))
      (insert (a j) (insert (b j) (T j)))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  have haa : a i ≠ a j := by
    intro h
    have he : (i, false) = (j, false) := hleaf (by simpa using h)
    exact hij (congrArg Prod.fst he)
  have hab : a i ≠ b j := by
    intro h
    have he : (i, false) = (j, true) := hleaf (by simpa using h)
    exact hij (congrArg Prod.fst he)
  have hba : b i ≠ a j := by
    intro h
    have he : (i, true) = (j, false) := hleaf (by simpa using h)
    exact hij (congrArg Prod.fst he)
  have hbb : b i ≠ b j := by
    intro h
    have he : (i, true) = (j, true) := hleaf (by simpa using h)
    exact hij (congrArg Prod.fst he)
  simp only [Finset.mem_insert] at hvi hvj
  rcases hvi with rfl | rfl | hvi <;> rcases hvj with hvj | hvj | hvj
  · exact haa hvj
  · exact hab hvj
  · exact Finset.disjoint_left.mp hQW (hT j hvj) (ha i)
  · exact hba hvj
  · exact hbb hvj
  · exact Finset.disjoint_left.mp hQW (hT j hvj) (hb i)
  · exact Finset.disjoint_left.mp hQW (hT i hvi) (hvj.symm ▸ ha j)
  · exact Finset.disjoint_left.mp hQW (hT i hvi) (hvj.symm ▸ hb j)
  · exact Finset.disjoint_left.mp (hdis hij) hvi hvj

theorem append_private_leaf_route_family {I : Type*}
    (Q W : Finset V) (hQW : Disjoint Q W) (r : ℕ)
    (x y a b : I → V) (T : I → Finset V)
    (hxa : ∀ i, G.Adj (x i) (a i)) (hby : ∀ i, G.Adj (b i) (y i))
    (hxy : ∀ i, x i ≠ y i) (hx : ∀ i, x i ∉ Q ∪ W) (hy : ∀ i, y i ∉ Q ∪ W)
    (ha : ∀ i, a i ∈ W) (hb : ∀ i, b i ∈ W)
    (hT : ∀ i, SupportsRoute G Q r (a i) (b i) (T i))
    (hleaf : Function.Injective (fun z : I × Bool => if z.2 then b z.1 else a z.1))
    (hdis : Pairwise (fun i j => Disjoint (T i) (T j))) :
    ∃ S : I → Finset V, (∀ i, SupportsRoute G (Q ∪ W) (r + 2) (x i) (y i) (S i)) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) := by
  refine ⟨fun i => insert (a i) (insert (b i) (T i)), ?_, ?_⟩
  · intro i
    exact append_private_leaf_edges Q W r (hxa i) (hby i) (hxy i)
      (hx i) (hy i) (ha i) (hb i) (hT i)
  · exact private_leaf_interiors_disjoint Q W hQW a b T ha hb
      (fun i => (hT i).2.1) hleaf hdis

theorem selected_private_leaves_injective {I J : Type*}
    (f : (I × Bool) × J → V) (hf : Function.Injective f) (choose : I → J) :
    Function.Injective (fun z : I × Bool => f (z, choose z.1)) := by
  intro z w he
  exact congrArg Prod.fst (hf he)

end Erdos585.Attempt6
