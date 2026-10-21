import Erdos1017.MesoscopicCounts
import Erdos1017.MesoscopicInterpolation
import Mathlib.Tactic.FieldSimp

namespace Erdos1017.Mesoscopic

theorem graph_identity (a b s : ℕ) (T : Finset (Fin 2 × Fin b)) :
    total (graph a b s T) weight + ((graph a b s T).edgeFinset.card:ℝ) -
      ((a:ℝ)+b+s+2)^2/2 = (s:ℝ)^2/18-s/3-
        ((a:ℝ)-b-2*s/3-2)^2/2 := by
  rw [graph_weight_total,graph_edge_count]
  ring

noncomputable def lowerBound (n m : ℕ) : ℝ :=
  (n*n/4:ℕ) - (m:ℝ) + 2*(m:ℝ)^2/(9*(n:ℝ)^2) -
    8*(m:ℝ)/(9*(n:ℝ)) - 29/18

theorem selected_lower (n m s : ℕ) (T : Finset (Fin 2 × Fin (partB n s)))
    (hn : 100 ≤ n) (hm : 2*n ≤ m) (hs : 10*s ≤ n)
    (hnext : (m:ℝ) < (n:ℝ)*(s+1)/2)
    (hedges : (graph (partA n s) (partB n s) s T).edgeFinset.card = n*n/4+m)
    (P : FractionalPartition (graph (partA n s) (partB n s) s T)) :
    lowerBound n m ≤ P.cost := by
  obtain ⟨_,_,hsize,hlo,hhi⟩ := part_bounds n s hn hs
  have hsizeR : (partA n s:ℝ)+partB n s+s+2=n := by exact_mod_cast hsize
  have hlow : 3*(partB n s:ℝ)+2*s < 3*(partA n s:ℝ) := by exact_mod_cast hlo
  have hhigh : 3*(partA n s:ℝ) ≤ 3*(partB n s:ℝ)+2*s+6 := by exact_mod_cast hhi
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hmreal : 2*(n:ℝ) ≤ m := by exact_mod_cast hm
  have hratio : 2*(m:ℝ)/(n:ℝ)-1 < s := by
    have : 2*(m:ℝ)/(n:ℝ) < (s:ℝ)+1 :=
      (div_lt_iff₀ hnpos).mpr (by nlinarith)
    linarith
  have hx : (0:ℝ) ≤ 2*(m:ℝ)/(n:ℝ)-4 := by
    have : (4:ℝ) ≤ 2*(m:ℝ)/(n:ℝ) :=
      (le_div_iff₀ hnpos).mpr (by linarith)
    linarith
  have hs3 : (0:ℝ) ≤ (s:ℝ)-3 := by linarith
  have hsq := mul_nonneg
    (show 0 ≤ ((s:ℝ)-3)-(2*(m:ℝ)/(n:ℝ)-4) by linarith)
    (add_nonneg hs3 hx)
  have hd1 : 0 ≤ ((partA n s:ℝ)-partB n s-2*s/3-2)+2 := by linarith
  have hd2 : 0 ≤ 2-((partA n s:ℝ)-partB n s-2*s/3-2) := by linarith
  have hd := mul_nonneg hd1 hd2
  have hid := graph_identity (partA n s) (partB n s) s T
  rw [hsizeR,hedges] at hid
  push_cast at hid
  have hq := (quarter_bounds n).1
  have hdual := graph_lower (partA n s) (partB n s) s T P
  have hbound : (n*n/4:ℕ)-(m:ℝ)+(2*(m:ℝ)/(n:ℝ)-4)^2/18-5/2 ≤ P.cost := by
    nlinarith
  have hformula : (n*n/4:ℕ)-(m:ℝ)+(2*(m:ℝ)/(n:ℝ)-4)^2/18-5/2=lowerBound n m := by
    unfold lowerBound
    field_simp
    ring
  rwa [hformula] at hbound

/-- Full finite original-graph lower bound. Graph order and original edge count
are exact; cliques have unrestricted order. The same witness works for every
exact fractional partition and every integral edge-clique partition. -/
theorem finite_lower_bound (n m : ℕ) (hn : 100 ≤ n)
    (hmlo : 2*n ≤ m) (hmhi : 100*m ≤ n*n) :
    ∃ (a b s : ℕ) (T : Finset (Fin 2 × Fin b)),
      Fintype.card (Vertex a b s)=n ∧
      (graph a b s T).edgeFinset.card=n*n/4+m ∧
      Nonempty (IntegralPartition (graph a b s T)) ∧
      (∀ P : FractionalPartition (graph a b s T), lowerBound n m ≤ P.cost) ∧
      (∀ P : IntegralPartition (graph a b s T), lowerBound n m ≤ (P.pieces.card:ℝ)) := by
  obtain ⟨s,t,hs,ht,he,hnext⟩ := interpolate n m hn hmhi
  obtain ⟨T,hT⟩ := neutral_choice (partB n s) t ht
  have hs0 : 10*s ≤ n := by omega
  have hsize := (part_bounds n s hn hs0).2.2.1
  have hedges : (graph (partA n s) (partB n s) s T).edgeFinset.card=n*n/4+m := by
    have hcount := graph_edge_count (partA n s) (partB n s) s T
    rw [hT,← baseEdges_real] at hcount
    have heR : (baseEdges n s:ℝ)+(t:ℝ)=(n*n/4:ℕ)+(m:ℝ) := by exact_mod_cast he
    have h : ((graph (partA n s) (partB n s) s T).edgeFinset.card:ℝ)=(n*n/4:ℕ)+(m:ℝ) := by linarith
    exact_mod_cast h
  refine ⟨partA n s,partB n s,s,T,?_,hedges,⟨edgePartition _⟩,?_,?_⟩
  · rw [graph_order]; exact hsize
  · intro P; exact selected_lower n m s T hn hmlo hs0 hnext hedges P
  · intro P
    simpa only [P.fractional_cost] using selected_lower n m s T hn hmlo hs0 hnext hedges P.fractional

end Erdos1017.Mesoscopic
