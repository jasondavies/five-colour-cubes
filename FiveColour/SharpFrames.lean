module
public import FiveColour.FixedPairReserve
public import FiveColour.SharpGeometry
public import FiveColour.DeficitHall
@[expose] public section
namespace FiveColour.Physical
set_option maxHeartbeats 0

def RarePair {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) (p : Fin 10) : Prop :=
  (pairCopies cubes p).card ≤ 4*q+5
instance {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) (p : Fin 10) : Decidable (RarePair q cubes p) :=
  inferInstanceAs (Decidable (_ ≤ _))

def missingPairCopies {m : ℕ} (cubes : Fin m → Cube) (p : Fin 10) :=
  Finset.univ \ pairCopies cubes p
lemma mem_missingPairCopies {m : ℕ} (cubes : Fin m → Cube) (p : Fin 10) (i : Fin m) :
    i ∈ missingPairCopies cubes p ↔ ¬ HasPair (cubes i) p := by
  simp [missingPairCopies,pairCopies]
lemma missingPairCopies_card {m : ℕ} (cubes : Fin m → Cube) (p : Fin 10) :
    (missingPairCopies cubes p).card = m - (pairCopies cubes p).card := by
  simp [missingPairCopies,Finset.card_sdiff]

lemma rare_disjoint {m q : ℕ} (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hq : 1 ≤ q) (hm : 12*q+8 ≤ m) (p r : Fin 10) (hpr : p ≠ r)
    (hp : RarePair q cubes p) (hr : RarePair q cubes r) : PairDisjoint p r := by
  classical
  let common := Finset.univ \ (pairCopies cubes p ∪ pairCopies cubes r)
  have hcard : 0 < common.card := by
    have hu := Finset.card_union_le (pairCopies cubes p) (pairCopies cubes r)
    have he : common.card = m - (pairCopies cubes p ∪ pairCopies cubes r).card := by
      simp [common,Finset.card_sdiff]
    unfold RarePair at hp hr
    omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hcard
  have hn : ¬ HasPair (cubes i) p ∧ ¬ HasPair (cubes i) r := by
    simpa [common,pairCopies] using hi
  apply missing_disjoint p r (catalogueIndex (cubes i)) hpr
  · simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using hn.1
  · simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using hn.2

lemma at_most_two_rare {m q : ℕ} (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hq : 1 ≤ q) (hm : 12*q+8 ≤ m) (p r : Fin 10) (hpr : p ≠ r)
    (hp : RarePair q cubes p) (hr : RarePair q cubes r) :
    ∀ s, RarePair q cubes s → s = p ∨ s = r := by
  intro s hs
  by_contra hn
  have hsp : s ≠ p := fun he => hn (Or.inl he)
  have hsr : s ≠ r := fun he => hn (Or.inr he)
  exact no_three_disjoint p r s
    (rare_disjoint cubes hc hq hm p r hpr hp hr)
    (rare_disjoint cubes hc hq hm p s hsp.symm hp hs)
    (rare_disjoint cubes hc hq hm r s hsr.symm hr hs)

lemma frame_avoiding_rare {m q : ℕ} (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hq : 1 ≤ q) (hm : 12*q+8 ≤ m) (t : Fin 75)
    (core : {pos : FrameSlot q // CorePosition (catalogue t) pos} ↪ Fin m)
    (hcore : ∀ pos, FrameFits (cubes (core pos)) (catalogue t) pos.val)
    (havoid : ∀ p, RarePair q cubes p → ¬ HasPair (catalogue t) p) : FrameSolvable q cubes := by
  apply frame_from_core q hq cubes hc hm t core hcore
  intro e he
  let p := pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))
  have hpair : HasPair (catalogue t) p := hasEdge_samePair (samePair_symm (pairIndex_correct _ _ he))
    (edge_of_corner _ _ e (fits_self _ _))
  have hn : ¬ RarePair q cubes p := fun hr => havoid p hr hpair
  have hcard : 4*q+6 ≤ (pairCopies cubes p).card := by unfold RarePair at hn; omega
  apply hcard.trans (Finset.card_le_card ?_)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hasEdge_samePair (pairIndex_correct _ _ he) (Finset.mem_filter.mp hi).2⟩

/-- Exactly the frame's piece count suffices, for every q = n-2 ≥ 1. -/
theorem sharp_frame_of_threshold (h : Threshold15) {m : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hm : 12*q+8 ≤ m) : FrameSolvable q cubes := by
  classical
  by_cases htwo : ∃ p r : Fin 10, p ≠ r ∧ RarePair q cubes p ∧ RarePair q cubes r
  · obtain ⟨p,r,hpr,hp,hr⟩ := htwo
    have hcover := at_most_two_rare cubes hc hq hm p r hpr hp hr
    let common := Finset.univ \ (pairCopies cubes p ∪ pairCopies cubes r)
    have hcommon : 4*q-2 ≤ common.card := by
      have hu := Finset.card_union_le (pairCopies cubes p) (pairCopies cubes r)
      have he : common.card = m-(pairCopies cubes p ∪ pairCopies cubes r).card := by
        simp [common,Finset.card_sdiff]
      unfold RarePair at hp hr
      omega
    have hnone (i : Fin m) (hi : i ∈ common) :
        ¬ HasPair (catalogue (catalogueIndex (cubes i))) p ∧
        ¬ HasPair (catalogue (catalogueIndex (cubes i))) r := by
      have hn : ¬ HasPair (cubes i) p ∧ ¬ HasPair (cubes i) r := by
        simpa [common,pairCopies] using hi
      simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using hn
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < common.card)
    let v := catalogueIndex (cubes i)
    obtain ⟨hop,unique⟩ := two_missing_pairs v p r hpr (hnone i hi).1 (hnone i hi).2
    have hv (j : Fin m) (hj : j ∈ common) : catalogueIndex (cubes j) = v :=
      unique _ (hnone j hj).1 (hnone j hj).2
    have hfull (j : Fin m) (hj : j ∈ common) (k : Fin 8) : Fits (cubes j) (catalogue v) k := by
      apply (fits_catalogueIndex _ (hc j) _ _).mpr
      rw [hv j hj]
      exact fits_self _ _
    have hfinish (corners : Fin 8 ↪ Fin m) (hfit : ∀ k, Fits (cubes (corners k)) (catalogue v) k) :
        FrameSolvable q cubes := by
      obtain ⟨core,hcore⟩ := opposite_core (q := q) cubes v hop corners hfit
      apply frame_avoiding_rare cubes hc hq hm v core hcore
      intro s hs
      rcases hcover s hs with rfl | rfl
      · exact (hnone i hi).1
      · exact (hnone i hi).2
    by_cases h6 : 6 ≤ common.card
    · obtain ⟨f,hf⟩ := FrameHall.match_of_pools (fun j k => Fits (cubes j) (catalogue v) k)
        6 Finset.univ common (by simp; omega) h6
        (fun j _ => opposite_corner_missing _ (hc j) v hop) hfull
      exact hfinish f hf
    have hq1 : q = 1 := by omega
    subst q
    let available := missingPairCopies cubes p
    have havail : 11 ≤ available.card := by
      rw [missingPairCopies_card]
      unfold RarePair at hp
      omega
    have hnot (j : Fin m) (hj : j ∈ available) : ¬ HasPair (cubes j) p :=
      (mem_missingPairCopies cubes p j).mp hj
    by_cases h4 : 4 ≤ common.card
    · obtain ⟨f,hf⟩ := FrameHall.match_of_pools (fun j k => Fits (cubes j) (catalogue v) k)
        4 available common (by simpa using (show 8 ≤ available.card by omega)) h4 (by
          intro j hj
          have hb := (common_pair_geometry p (catalogueIndex (cubes j)) v
            (by simpa only [HasPair,hasEdge_catalogueIndex _ (hc j)] using hnot j hj)
            (hnone i hi).1 hop).1
          have he : missingCorners (cubes j) (catalogue v) =
              missingCorners (catalogue (catalogueIndex (cubes j))) (catalogue v) := by
            unfold missingCorners; congr 1; ext k; simp [fits_catalogueIndex _ (hc j)]
          change missingCorners (cubes j) (catalogue v) ≤ 4
          rw [he]
          exact hb) hfull
      exact hfinish f hf
    have hiA : i ∈ available := (mem_missingPairCopies cubes p i).mpr
      (by simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using (hnone i hi).1)
    obtain ⟨t,ht,core,hcore⟩ := fixed_pair_core_available cubes hc p available hnot havail ⟨i,hiA,hop⟩
    have hS : 8 ≤ (pairCopies cubes r).card := by
      have hu := Finset.card_union_le (pairCopies cubes p) (pairCopies cubes r)
      have he : common.card = m-(pairCopies cubes p ∪ pairCopies cubes r).card := by
        simp [common,Finset.card_sdiff]
      unfold RarePair at hp hr
      omega
    have hSV : 10 ≤ (pairCopies cubes r).card + common.card := by
      have hu := Finset.card_union_le (pairCopies cubes p) (pairCopies cubes r)
      have he : common.card = m-(pairCopies cubes p ∪ pairCopies cubes r).card := by
        simp [common,Finset.card_sdiff]
      unfold RarePair at hp
      omega
    apply frame_of_match cubes t
    apply FrameHall.match_of_one_deficit
      (fun (j : Fin m) (pos : FrameSlot 1) => FrameFits (cubes j) (catalogue t) pos)
      10 7 (CorePosition (catalogue t)) (by simpa [frameSlot_card,Nat.add_comm] using hm)
      (fun j => (frame_missing_bound _ (hc j) t 1 (by omega)).1) core hcore
      (pairCopies cubes r) common
    · apply Finset.disjoint_left.mpr
      intro j hj hcj
      exact (Finset.mem_sdiff.mp hcj).2 (Finset.mem_union_right _ hj)
    · omega
    · exact hSV
    · intro j hj
      have he : (Finset.univ.filter fun pos : FrameSlot 1 => ¬ FrameFits (cubes j) (catalogue t) pos) =
          (Finset.univ.filter fun pos : FrameSlot 1 => ¬ FrameFits (catalogue v) (catalogue t) pos) := by
        ext pos
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,frameFits_catalogueIndex _ _ (hc j),hv j hj]
      rw [he,frame_missing_card]
      simpa using (common_pair_geometry p t v ht (hnone i hi).1 hop).2
    · intro pos hpos
      cases pos with
      | inl k => exact False.elim (hpos trivial)
      | inr ep =>
        let s := pairIndex (catalogue t (edgeFaces ep.1 0)) (catalogue t (edgeFaces ep.1 1))
        have hs : catalogue t (edgeFaces ep.1 0) ≠ catalogue t (edgeFaces ep.1 1) := hpos
        by_cases hrare : RarePair 1 cubes s
        · have hsr : s = r := by
            rcases hcover s hrare with hsp | hsr
            · have he := hasEdge_samePair (samePair_symm (pairIndex_correct _ _ hs))
                (edge_of_corner _ _ ep.1 (fits_self _ _))
              exact False.elim (ht (hsp ▸ he))
            · exact hsr
          right
          intro j hj
          exact hasEdge_samePair (pairIndex_correct _ _ hs)
            (by change HasPair (cubes j) s; rw [hsr]; exact (Finset.mem_filter.mp hj).2)
        · left
          have hcard : 10 ≤ (pairCopies cubes s).card := by unfold RarePair at hrare; omega
          apply hcard.trans (Finset.card_le_card ?_)
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hasEdge_samePair (pairIndex_correct _ _ hs) (Finset.mem_filter.mp hj).2⟩
  · by_cases hex : ∃ p : Fin 10, RarePair q cubes p
    · obtain ⟨p,hp⟩ := hex
      have hcover : ∀ r, RarePair q cubes r → r = p := by
        intro r hr; by_contra hne; exact htwo ⟨r,p,hne,hr,hp⟩
      let available := missingPairCopies cubes p
      have hsize : 8*q+3 ≤ available.card := by
        rw [missingPairCopies_card]
        unfold RarePair at hp
        omega
      have hnot (j : Fin m) (hj : j ∈ available) : ¬ HasPair (cubes j) p :=
        (mem_missingPairCopies cubes p j).mp hj
      have hcore : ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
          ∃ f : {pos : FrameSlot q // CorePosition (catalogue t) pos} ↪ Fin m,
            ∀ pos, FrameFits (cubes (f pos)) (catalogue t) pos.val := by
        by_cases hq1 : q = 1
        · subst q
          exact fixed_pair_extra_available cubes hc p available hnot (by omega) (by omega)
        · exact reserve_fixed_pair q cubes hc p available hnot (by omega)
      obtain ⟨t,ht,core,hcore⟩ := hcore
      exact frame_avoiding_rare cubes hc hq hm t core hcore
        (fun r hr => by simpa only [hcover r hr] using ht)
    · obtain ⟨t,_,core,hcore⟩ := reserve_core h q cubes hc Finset.univ (fun _ => q)
        (fun _ _ _ _ => rfl) (by simp; omega)
      exact frame_avoiding_rare cubes hc hq hm t core hcore (fun p hp => False.elim (hex ⟨p,hp⟩))
end FiveColour.Physical
