module
public import FiveColour.TargetChoice
@[expose] public section
namespace FiveColour.Physical

/-- Choose a corner-solvable target and a zero-length direction so every
edge in another direction has at least d suppliers. -/
theorem thin_target (h : Threshold15) {n : ℕ} (d : ℕ) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 15 ≤ n) (hd : 2*d ≤ n+1) :
    ∃ t : Fin 75, ∃ corners : Fin 8 ↪ Fin n,
      (∀ k, Fits (cubes (corners k)) (catalogue t) k) ∧
      ∃ z : Fin 3, (∀ a, a ≠ z → BichromaticAxis (catalogue t) a) ∧
        ∀ e, edgeAxis e ≠ z →
          d ≤ (Finset.univ.filter fun i => HasEdge (cubes i)
            (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card := by
  obtain ⟨t,corners,hf,hchoice⟩ := corner_target_choice h d cubes hc hn hd
  rcases hchoice with hnone | ⟨p,hp,hrare⟩
  · obtain ⟨z,hz⟩ := mono_axis t
    exact ⟨t,corners,hf,z,hz,fun e he =>
      edge_suppliers_of_not_rare d cubes t e (hz _ he e rfl) (hnone _)⟩
  · obtain ⟨z,hz,he⟩ := family_axis p t hp
    refine ⟨t,corners,hf,z,hz,?_⟩
    intro e hz'
    apply edge_suppliers_of_not_rare d cubes t e (hz _ hz' e rfl)
    intro hr
    exact he e hz' _ (hrare _ hr) rfl
end FiveColour.Physical
