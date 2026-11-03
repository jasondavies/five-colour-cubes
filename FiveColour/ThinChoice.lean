module
public import FiveColour.BoxMatching
public import FiveColour.EightPlusThree
@[expose] public section
namespace FiveColour.Physical

/-- Choose a corner-solvable target and a zero-length direction so every
edge in another direction has at least d suppliers. -/
theorem thin_target (h : Threshold15) {n : ℕ} (d : ℕ) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 15 ≤ n) (hd : 2*d ≤ n+1)
    (hfamily : 8+d ≤ n+1) :
    ∃ t : Fin 75, ∃ corners : Fin 8 ↪ Fin n,
      (∀ k, Fits (cubes (corners k)) (catalogue t) k) ∧
      ∃ z : Fin 3, (∀ a, a ≠ z → BichromaticAxis (catalogue t) a) ∧
        ∀ e, edgeAxis e ≠ z →
          d ≤ (Finset.univ.filter fun i => HasEdge (cubes i)
            (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card := by
  classical
  have finish (t : Fin 75) (corners : Fin 8 ↪ Fin n)
      (hf : ∀ k, Fits (cubes (corners k)) (catalogue t) k)
      (z : Fin 3) (hz : ∀ a, a ≠ z → BichromaticAxis (catalogue t) a)
      (havoid : ∀ e, edgeAxis e ≠ z →
        ¬ RareAt d cubes (pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)))) :
      ∃ t : Fin 75, ∃ corners : Fin 8 ↪ Fin n,
        (∀ k, Fits (cubes (corners k)) (catalogue t) k) ∧
        ∃ z : Fin 3, (∀ a, a ≠ z → BichromaticAxis (catalogue t) a) ∧
          ∀ e, edgeAxis e ≠ z → d ≤ (Finset.univ.filter fun i => HasEdge (cubes i)
            (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card := by
    refine ⟨t,corners,hf,z,hz,?_⟩
    intro e he
    have hb := hz _ he e rfl
    have hn := havoid e he
    have hn' : d ≤ (pairCopies cubes (pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)))).card := by
      unfold RareAt at hn; omega
    apply hn'.trans (Finset.card_le_card ?_)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hasEdge_samePair (pairIndex_correct _ _ hb) (Finset.mem_filter.mp hi).2⟩
  by_cases hr : ∃ p, RareAt d cubes p
  · obtain ⟨p,hp⟩ := hr
    have hF : 8 ≤ (missingPairCopies cubes p).card := by
      rw [missingPairCopies_card]; unfold RareAt at hp; omega
    obtain ⟨t,ht,corners,hf⟩ := eight_plus_three_available p cubes hc (missingPairCopies cubes p)
      hF (by simpa using (show 11 ≤ n by omega))
      (fun i hi => (mem_missingPairCopies cubes p i).mp hi)
    obtain ⟨z,hz,he⟩ := family_axis p t ht
    apply finish t corners hf z hz
    intro e hz' hr
    let r := pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))
    have hrel : r=p ∨ PairDisjoint p r := by
      by_cases hpr : r=p
      · exact Or.inl hpr
      · exact Or.inr (rareAt_disjoint d cubes hc hd p r (Ne.symm hpr) hp hr)
    exact he e hz' r hrel rfl
  · obtain ⟨t,corners,hf⟩ := corners_of_threshold h cubes hc hn
    obtain ⟨z,hz⟩ := mono_axis t
    exact finish t corners hf z hz (fun _ _ hp => hr ⟨_,hp⟩)
end FiveColour.Physical
