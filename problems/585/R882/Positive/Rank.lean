import R882.Positive.PetalEscape

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
namespace Erdos585.R882.Positive
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Rank

/-- An actual maximizing-cardinality minimizer among original supersets of S. -/
structure UpwardMin (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K S P : Finset V) : Prop where
  subset : P⊆B\K
  contains : S⊆P
  minimal : ∀ Q⊆B\K, S⊆Q → extensionCost q j G A B K P≤extensionCost q j G A B K Q
  strict : ∀ Q⊆B\K, P⊆Q → P≠Q → extensionCost q j G A B K P+1≤extensionCost q j G A B K Q

lemma exists_upward_min (q j : ℕ) (A B K S : Finset V) (hS : S⊆B\K) :
    ∃ P, UpwardMin q j G A B K S P := by
  classical
  let F := (B\K).powerset.filter fun P => S⊆P
  have hF : F.Nonempty := ⟨S,mem_filter.mpr ⟨mem_powerset.mpr hS,Subset.rfl⟩⟩
  obtain ⟨P,hPF,hPmin⟩ := exists_min_image F (extensionCost q j G A B K) hF
  let M := F.filter fun Q => extensionCost q j G A B K Q=extensionCost q j G A B K P
  have hM : M.Nonempty := ⟨P,mem_filter.mpr ⟨hPF,rfl⟩⟩
  obtain ⟨Q,hQM,hQmax⟩ := exists_max_image M Finset.card hM
  obtain ⟨hQF,hcost⟩ := mem_filter.mp hQM
  obtain ⟨hQr,hSQ⟩ := mem_filter.mp hQF
  refine ⟨Q,mem_powerset.mp hQr,hSQ,?_,?_⟩
  · intro Z hZ hSZ
    rw [hcost]
    exact hPmin Z (mem_filter.mpr ⟨mem_powerset.mpr hZ,hSZ⟩)
  · intro Z hZ hQZ hne
    have hZF : Z∈F := mem_filter.mpr ⟨mem_powerset.mpr hZ,hSQ.trans hQZ⟩
    have hge := hPmin Z hZF
    by_contra! hbad
    have he : extensionCost q j G A B K Z=extensionCost q j G A B K P := by omega
    have hZM : Z∈M := mem_filter.mpr ⟨hZF,he⟩
    have hc := hQmax Z hZM
    have hlt : #Q<#Z := card_lt_card ⟨hQZ,fun hZQ => hne (Subset.antisymm hQZ hZQ)⟩
    omega

/-- Submodularity transfers a gain on the actual contraction to every old superset. -/
lemma gain_transfer {q j : ℕ} {A B K S P Q : Finset V}
    (hp : UpwardMin q j G A B K S P) (_hQ : Q⊆B\K) (hSQ : S⊆Q) :
    extensionCost q j G A B K (P∪Q)≤extensionCost q j G A B K Q := by
  classical
  have hI : S⊆P∩Q := subset_inter hp.contains hSQ
  have hm := hp.minimal (P∩Q) (inter_subset_left.trans hp.subset) hI
  have hs := extensionCost_submod (G:=G) q j A B K P Q
  omega

end Rank
end Erdos585.R882.Positive
