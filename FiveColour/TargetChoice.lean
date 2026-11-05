module
public import FiveColour.BoxMatching
public import FiveColour.EightPlusThree
@[expose] public section
namespace FiveColour.Physical

/-- The common rare/no-rare selection for every frame with a side of length two.
The threshold bound already guarantees eight members of a rare pair's family. -/
theorem corner_target_choice (h : Threshold15) {n : ℕ} (d : ℕ) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 15 ≤ n) (hd : 2*d ≤ n+1) :
    ∃ t : Fin 75, ∃ corners : Fin 8 ↪ Fin n,
      (∀ k, Fits (cubes (corners k)) (catalogue t) k) ∧
      ((∀ p, ¬ RareAt d cubes p) ∨ ∃ p, ¬ HasPair (catalogue t) p ∧
        ∀ r, RareAt d cubes r → r = p ∨ PairDisjoint p r) := by
  classical
  by_cases hr : ∃ p, RareAt d cubes p
  · obtain ⟨p,hp⟩ := hr
    have hF : 8 ≤ (missingPairCopies cubes p).card := by
      rw [missingPairCopies_card]
      unfold RareAt at hp
      omega
    obtain ⟨t,ht,corners,hf⟩ := eight_plus_three_available p cubes hc (missingPairCopies cubes p)
      hF (by simpa using (show 11 ≤ n by omega))
      (fun i hi => (mem_missingPairCopies cubes p i).mp hi)
    refine ⟨t,corners,hf,Or.inr ⟨p,ht,?_⟩⟩
    intro r hr
    by_cases he : r = p
    · exact Or.inl he
    · exact Or.inr (rareAt_disjoint d cubes hc hd p r (Ne.symm he) hp hr)
  · obtain ⟨t,corners,hf⟩ := corners_of_threshold h cubes hc hn
    exact ⟨t,corners,hf,Or.inl (fun p hp => hr ⟨p,hp⟩)⟩

/-- A nonrare bichromatic edge has the required number of physical suppliers. -/
lemma edge_suppliers_of_not_rare {n : ℕ} (d : ℕ) (cubes : Fin n → Cube)
    (t : Fin 75) (e : Fin 12)
    (hb : catalogue t (edgeFaces e 0) ≠ catalogue t (edgeFaces e 1))
    (hr : ¬ RareAt d cubes (pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)))) :
    d ≤ (Finset.univ.filter fun i => HasEdge (cubes i)
      (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card := by
  have hn : d ≤ (pairCopies cubes (pairIndex (catalogue t (edgeFaces e 0))
      (catalogue t (edgeFaces e 1)))).card := by unfold RareAt at hr; omega
  apply hn.trans (Finset.card_le_card ?_)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hasEdge_samePair (pairIndex_correct _ _ hb) (Finset.mem_filter.mp hi).2⟩
end FiveColour.Physical
