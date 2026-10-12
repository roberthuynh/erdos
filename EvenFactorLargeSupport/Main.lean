import EvenFactorLargeSupport.Critical

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.EvenFactorLargeSupport
universe u

theorem even_factor_large_support (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + (q - 2)) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      2 * q - 1 ≤ H.verts.ncard := by
  classical
  obtain ⟨U, K, hnK, hsub, hcapK, hexact, hfloor⟩ :=
    L34EvenTransfer.critical_extraction q hq G hn hcap he
  have hlarge := critical_large_support q hq heven K hnK hcapK hexact hfloor
  let f : K →g G :=
    { toFun := fun a => a.val
      map_rel' := fun h => hsub h }
  exact regular_map_large f (fun _ _ h => Subtype.ext h) hlarge

end Erdos585.EvenFactorLargeSupport
