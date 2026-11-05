module
public import FiveColour.TargetChoice
public import FiveColour.RodAxes
@[expose] public section
namespace FiveColour.Physical

/-- Choose a corner-solvable target and a long direction so every
edge in that direction has at least d suppliers. -/
theorem rod_target (h : Threshold15) {n : ℕ} (d : ℕ) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 15 ≤ n) (hd : 2*d ≤ n+1) :
    ∃ t : Fin 75, ∃ corners : Fin 8 ↪ Fin n,
      (∀ k, Fits (cubes (corners k)) (catalogue t) k) ∧
      ∃ z : Fin 3, BichromaticAxis (catalogue t) z ∧ (OppositeRepeat (catalogue t) → Axial (catalogue t) z) ∧
        ∀ e, edgeAxis e = z →
          d ≤ (Finset.univ.filter fun i => HasEdge (cubes i)
            (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card := by
  obtain ⟨t,corners,hf,hchoice⟩ := corner_target_choice h d cubes hc hn hd
  rcases hchoice with hnone | ⟨p,hp,hrare⟩
  · obtain ⟨z,hz,haxial⟩ := rod_axis t
    exact ⟨t,corners,hf,z,hz,haxial,fun e he =>
      edge_suppliers_of_not_rare d cubes t e (hz e he) (hnone _)⟩
  · obtain ⟨z,hz,haxial,he⟩ := rod_family_axis p t hp
    refine ⟨t,corners,hf,z,hz,haxial,?_⟩
    intro e hz'
    apply edge_suppliers_of_not_rare d cubes t e (hz e hz')
    intro hr
    exact he e hz' _ (hrare _ hr) rfl
end FiveColour.Physical
