import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiNormalization

namespace Erdos642.DenseMask20261019.GallaiComponents
open SimpleGraph GallaiTwins
variable {V : Type*}

abbrev original (G : SimpleGraph V) (U : Set V) := G.induce Uᶜ
abbrev auxiliary (G : SimpleGraph V) (A U : Set V) :=
  (doubled G A).induce (project ⁻¹' U)ᶜ

def embedding (G : SimpleGraph V) (A U : Set V) : original G U →g auxiliary G A U where
  toFun x := ⟨Sum.inl x.val, x.property⟩
  map_rel' h := Or.inr h

def projection (A U : Set V) (x : ↥((project (A := A) ⁻¹' U)ᶜ)) : ↥(Uᶜ) :=
  ⟨project x.val, x.property⟩

theorem projection_reachable (G : SimpleGraph V) (A U : Set V)
    {x y : ↥((project (A := A) ⁻¹' U)ᶜ)} (h : (auxiliary G A U).Reachable x y) :
    (original G U).Reachable (projection A U x) (projection A U y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons x z y hx p ih =>
    apply Reachable.trans (v := projection A U z) _ ih
    rcases hx with ⟨_, he⟩ | he
    · have hxy : projection A U x = projection A U z := Subtype.ext he
      rw [hxy]
    · exact (show (original G U).Adj (projection A U x) (projection A U z) from he).reachable

theorem reachable_embedding_projection (G : SimpleGraph V) (A U : Set V)
    (x : ↥((project (A := A) ⁻¹' U)ᶜ)) :
    (auxiliary G A U).Reachable x (embedding G A U (projection A U x)) := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x => exact .refl _
  | inr x =>
    apply Adj.reachable
    exact Or.inl ⟨by simp [embedding, projection], rfl⟩

private theorem component_map_bijective (G : SimpleGraph V) (A U : Set V) :
    Function.Bijective (ConnectedComponent.map (embedding G A U)) := by
  constructor
  · intro C D
    induction C using ConnectedComponent.ind with | _ x =>
      induction D using ConnectedComponent.ind with | _ y =>
        intro h
        exact ConnectedComponent.sound
          (projection_reachable G A U (ConnectedComponent.exact h))
  · intro C
    induction C using ConnectedComponent.ind with | _ x =>
      exact ⟨(original G U).connectedComponentMk (projection A U x),
        (ConnectedComponent.sound (reachable_embedding_projection G A U x)).symm⟩

noncomputable def componentEquiv (G : SimpleGraph V) (A U : Set V) :
    (original G U).ConnectedComponent ≃ (auxiliary G A U).ConnectedComponent :=
  Equiv.ofBijective _ (component_map_bijective G A U)

theorem mem_component_iff (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) (x : ↥((project (A := A) ⁻¹' U)ᶜ)) :
    x ∈ (componentEquiv G A U C).supp ↔ projection A U x ∈ C.supp := by
  simp only [ConnectedComponent.mem_supp_iff]
  have hx := ConnectedComponent.sound (reachable_embedding_projection G A U x)
  rw [hx]
  change (componentEquiv G A U) ((original G U).connectedComponentMk (projection A U x)) =
    (componentEquiv G A U) C ↔ _
  exact (componentEquiv G A U).injective.eq_iff

/-- The actual auxiliary support consists of all original copies and the extra nonterminal copies. -/
noncomputable def supportEquiv (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) :
    (componentEquiv G A U C).supp ≃ C.supp ⊕ {x : C.supp // x.val.val ∉ A} where
  toFun x := by
    have hp := (mem_component_iff G A U C x.val).mp x.property
    rcases x with ⟨⟨x, hx⟩, hC⟩
    cases x with
    | inl x => exact Sum.inl ⟨⟨x, hx⟩, hp⟩
    | inr x => exact Sum.inr ⟨⟨⟨x.val, hx⟩, hp⟩, x.property⟩
  invFun x := by
    cases x with
    | inl x =>
      exact ⟨embedding G A U x.val,
        (mem_component_iff G A U C _).mpr x.property⟩
    | inr x =>
      exact ⟨⟨Sum.inr ⟨x.val.val.val, x.property⟩, x.val.val.property⟩,
        (mem_component_iff G A U C _).mpr x.val.property⟩
  left_inv x := by
    rcases x with ⟨⟨x, hx⟩, hC⟩
    cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem support_card [Fintype V] (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) :
    (componentEquiv G A U C).supp.ncard =
      Nat.card C.supp + Nat.card {x : C.supp // x.val.val ∉ A} := by
  classical
  have h := Nat.card_congr (supportEquiv G A U C)
  simpa only [Nat.card_sum, Nat.card_coe_set_eq] using h

noncomputable def terminals (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) := Nat.card {x : C.supp // x.val.val ∈ A}

noncomputable def nonterminals (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) := Nat.card {x : C.supp // x.val.val ∉ A}

theorem support_card_exact [Fintype V] (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) :
    (componentEquiv G A U C).supp.ncard =
      2 * nonterminals G A U C + terminals G A U C := by
  classical
  have hs := Nat.card_congr (Equiv.sumCompl (fun x : C.supp => x.val.val ∈ A))
  rw [Nat.card_sum] at hs
  rw [support_card]
  unfold nonterminals terminals
  omega

private noncomputable def sigmaNontermEquiv (G : SimpleGraph V) (A U : Set V) :
    (Σ C : (original G U).ConnectedComponent, {x : C.supp // x.val.val ∉ A}) ≃
      {x : ↥(Uᶜ) // x.val ∉ A} where
  toFun x := ⟨x.2.val.val, x.2.property⟩
  invFun x := ⟨(original G U).connectedComponentMk x.val,
    ⟨⟨x.val, by simp⟩, x.property⟩⟩
  left_inv x := by
    rcases x with ⟨C, ⟨⟨x, hx⟩, ha⟩⟩
    have hc : (original G U).connectedComponentMk x = C := hx
    subst C
    rfl
  right_inv x := rfl

theorem sum_nonterminals [Fintype V] (G : SimpleGraph V) (A U : Set V) :
    letI := Fintype.ofFinite (original G U).ConnectedComponent
    ∑ C, nonterminals G A U C = Nat.card {x : ↥(Uᶜ) // x.val ∉ A} := by
  classical
  letI := Fintype.ofFinite (original G U).ConnectedComponent
  have h := Nat.card_congr (sigmaNontermEquiv G A U)
  simpa only [Nat.card_sigma, nonterminals] using h

private noncomputable def deletionEquiv (A U : Set V) :
    ↥(project (A := A) ⁻¹' U) ≃ U ⊕ {x : U // x.val ∉ A} where
  toFun x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl x => exact .inl ⟨x, hx⟩
    | inr x => exact .inr ⟨⟨x.val, hx⟩, x.property⟩
  invFun x := by
    cases x with
    | inl x => exact ⟨Sum.inl x.val, x.property⟩
    | inr x => exact ⟨Sum.inr ⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv x := by rcases x with ⟨x, hx⟩; cases x <;> rfl
  right_inv x := by cases x <;> rfl

private noncomputable def nonterminalPartition (A U : Set V) :
    {x : U // x.val ∉ A} ⊕ {x : ↥(Uᶜ) // x.val ∉ A} ≃ ↥(Aᶜ) where
  toFun x := Sum.elim (fun x => ⟨x.val.val, x.property⟩)
    (fun x => ⟨x.val.val, x.property⟩) x
  invFun x := by
    classical
    exact if h : x.val ∈ U then .inl ⟨⟨x.val, h⟩, x.property⟩
      else .inr ⟨⟨x.val, h⟩, x.property⟩
  left_inv x := by
    classical
    cases x with
    | inl x => simp [x.val.property]
    | inr x => simp [show x.val.val ∉ U from x.val.property]
  right_inv x := by
    classical
    dsimp
    split_ifs <;> rfl

/-- The exact normalized Tutte--Berge deletion obstruction in original component terms. -/
theorem obstruction_identity [Fintype V] (G : SimpleGraph V) (A U : Set V) :
    letI := Fintype.ofFinite (original G U).ConnectedComponent
    obstruction (doubled G A) (project ⁻¹' U) =
      Aᶜ.ncard + U.ncard + ∑ C, terminals G A U C / 2 := by
  classical
  letI := Fintype.ofFinite (original G U).ConnectedComponent
  letI := Fintype.ofFinite (auxiliary G A U).ConnectedComponent
  have hd := Nat.card_congr (deletionEquiv A U)
  rw [Nat.card_sum] at hd
  have hp := Nat.card_congr (nonterminalPartition A U)
  rw [Nat.card_sum] at hp
  have hs := sum_nonterminals G A U
  have hhalf : halfComponents (auxiliary G A U) =
      (∑ C, nonterminals G A U C) + ∑ C, terminals G A U C / 2 := by
    unfold halfComponents
    rw [← (componentEquiv G A U).sum_comp (fun C => C.supp.ncard / 2)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _
    rw [support_card_exact]
    omega
  change (project ⁻¹' U).ncard + halfComponents (auxiliary G A U) = _
  rw [hhalf, hs]
  simp only [Nat.card_coe_set_eq] at hd hp ⊢
  omega

end Erdos642.DenseMask20261019.GallaiComponents


