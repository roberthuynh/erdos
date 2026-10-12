import R898.Numeric
import R882.Positive.Main
import R898.Balanced.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R898
open QB4 B5 R837 NEQAssembly
universe u

lemma terminal_oriented {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (h q e : ℕ) (hh : 6 ≤ h)
    (hq : 4096*(h+1)^2 ≤ q)
    (he : e ≤ 4*h^2-10*h+4)
    (hdis : Disjoint A B) (hcov : A∪B=univ)
    (hbip : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hn : 2*q ≤ Fintype.card V)
    (hmin : ∀ v : V, q+2*h-4 ≤ G.degree v)
    (hcap : ∀ v : V, G.degree v ≤ 2*q-2)
    (hf : ((q:ℤ)-1)*Fintype.card V-(G.edgeSet.ncard:ℤ)=(h:ℤ)*q-16*h^2+e)
    (hproper : ∀ U : Finset V, h≤#U → #U<Fintype.card V →
      (h:ℤ)*q-16*h^2+1≤((q:ℤ)-1)*#U-((G.induce (U : Set V)).edgeSet.ncard:ℤ))
    (hab : #A ≤ #B) (hgap : (#B:ℤ)-#A ≤ (h:ℤ)-1) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  have hminimum : ∀ v : V, q ≤ G.degree v := by intro v;have hm:=hmin v;omega
  by_cases hbal : #A=#B
  · apply Balanced.original_host_caller
      (h := h) (epsilon := e) (F := (h:ℤ)*q-16*h^2+e)
      hh hq (by
        have heb : (e:ℤ) ≤ (4*h^2-10*h+4:ℕ) := by exact_mod_cast he
        rwa [R866.budget_cast hh] at heb) rfl
      hdis hcov hbal hbip hn hminimum hcap hf
    intro U hu hp
    have ff:=hproper U hu hp
    omega
  · let j := #B-#A
    have hj : 1 ≤ j := by dsimp [j];omega
    have hju : j ≤ h-1 := by dsimp [j];omega
    obtain ⟨O,hOB,hOj,hcuts,H,hverts,hne,hreg⟩ :=
      R882.Positive.error_floor_positive_selector h q j e G A B hh he hq hj hju hdis hcov hbip
        (by dsimp [j];omega) hn hminimum hcap (fun v _ => hmin v) hf hproper
    exact ⟨H,hne,hreg⟩

lemma terminal_unoriented {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (h q e : ℕ) (hh : 6 ≤ h)
    (hq : 4096*(h+1)^2 ≤ q)
    (he : e ≤ 4*h^2-10*h+4)
    (hdis : Disjoint A B) (hcov : A∪B=univ)
    (hbip : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hn : 2*q ≤ Fintype.card V)
    (hmin : ∀ v : V, q+2*h-4 ≤ G.degree v)
    (hcap : ∀ v : V, G.degree v ≤ 2*q-2)
    (hf : ((q:ℤ)-1)*Fintype.card V-(G.edgeSet.ncard:ℤ)=(h:ℤ)*q-16*h^2+e)
    (hproper : ∀ U : Finset V, h≤#U → #U<Fintype.card V →
      (h:ℤ)*q-16*h^2+1≤((q:ℤ)-1)*#U-((G.induce (U : Set V)).edgeSet.ncard:ℤ))
    (hgap : |(#B:ℤ)-#A| ≤ (h:ℤ)-1) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  by_cases hab : #A ≤ #B
  · exact terminal_oriented G A B h q e hh hq he hdis hcov hbip hn hmin hcap hf hproper hab
      ((le_abs_self _).trans hgap)
  · apply terminal_oriented G B A h q e hh hq he hdis.symm
      (by rwa [union_comm]) hbip.symm hn hmin hcap hf hproper (by omega)
    have hhg := (neg_le_abs ((#B:ℤ)-#A)).trans hgap
    omega
end Erdos585.R898
