module
public import FiveColour.RectCore
public import FiveColour.FamilyAlignment
public import FiveColour.EightPairReserve
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators
set_option maxHeartbeats 0

lemma wide_frame_avoiding {n : ℕ} (m u M : ℕ) (hmu : m ≤ u) (huM : u ≤ M) (hs : 2 ≤ m+u)
    (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i)) (hn : 8+4*(m+u+M) ≤ n)
    (t : Fin 75) (z : Fin 3) (hz : ∀ a, a ≠ z → BichromaticAxis (catalogue t) a)
    (core : {pos : FrameSlot m // CorePosition (catalogue t) pos} ↪ Fin n)
    (hcore : ∀ pos, FrameFits (cubes (core pos)) (catalogue t) pos.val)
    (havoid : ∀ p, RareAt (m+u+2*M+6) cubes p → ¬ HasPair (catalogue t) p) :
    BoxFrameSolvable (m+2) (u+2) (M+2) cubes := by
  classical
  let axes := Equiv.swap (0 : Fin 3) z
  let l := fun a => ![m,u,M] (axes a)
  obtain ⟨f,hf⟩ := rect_core_of_uniform l cubes t (shortest_mono_length t z hz m u M) core hcore
  have hsize : Fintype.card (RectSlot l) ≤ n := by
    rw [rectSlot_card,Equiv.sum_comp axes (fun a => ![m,u,M] a)]
    simpa [Fin.sum_univ_succ,Nat.add_assoc] using hn
  have hrect : RectSolvable l cubes := by
    apply rect_from_core l cubes t (m+u+2*M+6) hsize
      (fun i => rect_missing_bound _ (hc i) t axes m u M hmu huM hs) f hf
    intro e he
    let p := pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))
    have ht : HasPair (catalogue t) p := hasEdge_samePair (samePair_symm (pairIndex_correct _ _ he))
      (edge_of_corner _ _ e (fits_self _ _))
    have hp : ¬ RareAt (m+u+2*M+6) cubes p := fun hp => havoid p hp ht
    have hn' : m+u+2*M+6 ≤ (pairCopies cubes p).card := by unfold RareAt at hp; omega
    apply hn'.trans (Finset.card_le_card ?_)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hasEdge_samePair (pairIndex_correct _ _ he) (Finset.mem_filter.mp hi).2⟩
  refine ⟨axes,?_⟩
  simpa only [Nat.add_sub_cancel] using hrect

/-- The frame's own number of copies suffices when the two shortest edge
lengths sum to at least two. -/
theorem wide_frame_of_threshold (h : Threshold15) {n : ℕ} (m u M : ℕ)
    (hmu : m ≤ u) (huM : u ≤ M) (hs : 2 ≤ m+u)
    (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hn : 8+4*(m+u+M) ≤ n) : BoxFrameSolvable (m+2) (u+2) (M+2) cubes := by
  classical
  let d := m+u+2*M+6
  have hd : 2*d ≤ n+1 := by dsimp [d]; omega
  have hreserve : 11+3*m ≤ n := by omega
  have hfamily (p) (hp : RareAt d cubes p) : 8+3*m ≤ (missingPairCopies cubes p).card := by
    rw [missingPairCopies_card]; unfold RareAt at hp; dsimp [d] at hp; omega
  by_cases htwo : ∃ p r : Fin 10, p ≠ r ∧ RareAt d cubes p ∧ RareAt d cubes r
  · obtain ⟨p,r,hpr,hp,hr⟩ := htwo
    have hcover : ∀ s, RareAt d cubes s → s=p ∨ s=r := by
      intro s hs'
      by_contra hh
      have hsp : s ≠ p := fun he => hh (Or.inl he)
      have hsr : s ≠ r := fun he => hh (Or.inr he)
      exact no_three_disjoint p r s (rareAt_disjoint d cubes hc hd p r hpr hp hr)
        (rareAt_disjoint d cubes hc hd p s hsp.symm hp hs')
        (rareAt_disjoint d cubes hc hd r s hsr.symm hr hs')
    let common := Finset.univ \ (pairCopies cubes p ∪ pairCopies cubes r)
    have hu := Finset.card_union_le (pairCopies cubes p) (pairCopies cubes r)
    have he : common.card = n-(pairCopies cubes p ∪ pairCopies cubes r).card := by simp [common,Finset.card_sdiff]
    have hcommon : 2*(m+u)-2 ≤ common.card := by unfold RareAt at hp hr; dsimp [d] at hp hr; omega
    have hnone (i : Fin n) (hi : i ∈ common) :
        ¬ HasPair (catalogue (catalogueIndex (cubes i))) p ∧ ¬ HasPair (catalogue (catalogueIndex (cubes i))) r := by
      have hh : ¬ HasPair (cubes i) p ∧ ¬ HasPair (cubes i) r := by simpa [common,pairCopies] using hi
      simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using hh
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < common.card)
    let v := catalogueIndex (cubes i)
    obtain ⟨hop,unique⟩ := two_missing_pairs v p r hpr (hnone i hi).1 (hnone i hi).2
    have hv (j) (hj : j ∈ common) : catalogueIndex (cubes j)=v := unique _ (hnone j hj).1 (hnone j hj).2
    have hfull (j) (hj : j ∈ common) (k : Fin 8) : Fits (cubes j) (catalogue v) k := by
      apply (fits_catalogueIndex _ (hc j) _ _).mpr
      rw [hv j hj]; exact fits_self _ _
    let available := missingPairCopies cubes p
    have havail : 8 ≤ available.card := by
      change 8 ≤ (missingPairCopies cubes p).card
      have := hfamily p hp; omega
    have hnot (j) (hj : j ∈ available) : ¬ HasPair (cubes j) p := (mem_missingPairCopies cubes p j).mp hj
    by_cases h4 : 4 ≤ common.card
    · obtain ⟨f,hf⟩ := FrameHall.match_of_pools (fun j k => Fits (cubes j) (catalogue v) k)
        4 available common (by simpa using havail) h4 (by
          intro j hj
          have hb := (common_pair_geometry p (catalogueIndex (cubes j)) v
            (by simpa only [HasPair,hasEdge_catalogueIndex _ (hc j)] using hnot j hj) (hnone i hi).1 hop).1
          change missingCorners (cubes j) (catalogue v) ≤ 4
          have he' : missingCorners (cubes j) (catalogue v) = missingCorners (catalogue (catalogueIndex (cubes j))) (catalogue v) := by
            unfold missingCorners; congr 1; ext k; simp [fits_catalogueIndex _ (hc j)]
          rw [he']; exact hb) hfull
      obtain ⟨core,hcore⟩ := opposite_core (q := m) cubes v hop f hf
      obtain ⟨z,hz⟩ := mono_axis v
      apply wide_frame_avoiding m u M hmu huM hs cubes hc hn v z hz core hcore
      intro s hs'
      rcases hcover s hs' with rfl | rfl
      · exact (hnone i hi).1
      · exact (hnone i hi).2
    have hsum : m+u=2 := by omega
    have hm1 : m ≤ 1 := by omega
    obtain ⟨t,ht,core,hcore⟩ := reserve_eight_pair m cubes hc p hreserve (hfamily p hp)
    let z := poleAxis p t
    let axes := Equiv.swap (0 : Fin 3) z
    let l := fun a => ![m,u,M] (axes a)
    obtain ⟨rcore,hrcore⟩ := rect_core_of_uniform l cubes t
      (shortest_mono_length t z (family_alignment p t ht).1 m u M) core hcore
    have hsize : Fintype.card (RectSlot l) ≤ n := by
      rw [rectSlot_card,Equiv.sum_comp axes (fun a => ![m,u,M] a)]
      simpa [Fin.sum_univ_succ,Nat.add_assoc] using hn
    have hS : 6 ≤ (pairCopies cubes r).card := by unfold RareAt at hp hr; dsimp [d] at hp hr; omega
    have hSV : d ≤ (pairCopies cubes r).card+common.card := by unfold RareAt at hp; dsimp [d] at hp ⊢; omega
    have hrect : RectSolvable l cubes := by
      apply rect_of_match l cubes t
      apply FrameHall.match_of_one_deficit (fun j pos => RectFits (cubes j) (catalogue t) pos)
        d 6 (RectCorePosition (catalogue t)) (by simpa using hsize)
        (fun j => rect_missing_bound _ (hc j) t axes m u M hmu huM hs) rcore hrcore
        (pairCopies cubes r) common
      · apply Finset.disjoint_left.mpr
        intro j hj hcom; exact (Finset.mem_sdiff.mp hcom).2 (Finset.mem_union_right _ hj)
      · exact hS
      · exact hSV
      · intro j hj
        have he' : (Finset.univ.filter fun pos : RectSlot l => ¬ RectFits (cubes j) (catalogue t) pos) =
            (Finset.univ.filter fun pos : RectSlot l => ¬ RectFits (catalogue v) (catalogue t) pos) := by
          ext pos; simp only [Finset.mem_filter,Finset.mem_univ,true_and,rectFits_catalogueIndex _ _ (hc j),hv j hj]
        rw [he']
        exact (family_rect_missing p v t (hnone i hi).1 ht hop m u M).trans (by omega)
      · intro pos hpos
        cases pos with
        | inl k => exact False.elim (hpos trivial)
        | inr ep =>
          let s := pairIndex (catalogue t (edgeFaces ep.1 0)) (catalogue t (edgeFaces ep.1 1))
          have hs' : catalogue t (edgeFaces ep.1 0) ≠ catalogue t (edgeFaces ep.1 1) := hpos
          by_cases hrare : RareAt d cubes s
          · have hsr : s=r := by
              rcases hcover s hrare with hsp | hsr
              · have hh := hasEdge_samePair (samePair_symm (pairIndex_correct _ _ hs')) (edge_of_corner _ _ ep.1 (fits_self _ _))
                exact False.elim (ht (hsp ▸ hh))
              · exact hsr
            right; intro j hj
            exact hasEdge_samePair (pairIndex_correct _ _ hs')
              (by change HasPair (cubes j) s; rw [hsr]; exact (Finset.mem_filter.mp hj).2)
          · left
            change d ≤ (Finset.univ.filter fun j => HasEdge (cubes j) (catalogue t (edgeFaces ep.1 0)) (catalogue t (edgeFaces ep.1 1))).card
            have hcard : d ≤ (pairCopies cubes s).card := by unfold RareAt at hrare; omega
            apply hcard.trans (Finset.card_le_card ?_)
            intro j hj
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hasEdge_samePair (pairIndex_correct _ _ hs') (Finset.mem_filter.mp hj).2⟩
    refine ⟨axes,?_⟩
    simpa only [Nat.add_sub_cancel] using hrect
  · by_cases hex : ∃ p, RareAt d cubes p
    · obtain ⟨p,hp⟩ := hex
      have hcover : ∀ r, RareAt d cubes r → r=p := by
        intro r hr; by_contra hne; exact htwo ⟨r,p,hne,hr,hp⟩
      obtain ⟨t,ht,core,hcore⟩ := reserve_eight_pair m cubes hc p hreserve (hfamily p hp)
      exact wide_frame_avoiding m u M hmu huM hs cubes hc hn t (poleAxis p t)
        (family_alignment p t ht).1 core hcore (fun r hr => by simpa only [hcover r hr] using ht)
    · obtain ⟨t,_,core,hcore⟩ := reserve_core h m cubes hc Finset.univ (fun _ => m)
        (fun _ _ _ _ => rfl) (by simp; omega)
      obtain ⟨z,hz⟩ := mono_axis t
      exact wide_frame_avoiding m u M hmu huM hs cubes hc hn t z hz core hcore
        (fun p hp => False.elim (hex ⟨p,hp⟩))
end FiveColour.Physical
