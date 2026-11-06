module
public import FiveColour.Universal
public import FiveColour.SymmetryAction
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Copies supplying bicoloured corners of one repeated colour. -/
def universalRepeatSources (cubes : Fin 15 → Cube) (r : Fin 5) : Finset (Fin 15) :=
  Finset.univ.filter fun i => universalSourceClass (catalogueIndex (cubes i)) = r.castSucc

lemma minimum_universal_counts (cubes : Fin 15 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hu : Submission.AdjacentUniversal cubes) :
    (∀ r, (universalRepeatSources cubes r).card = 3) ∧
    (∀ i, universalSourceClass (catalogueIndex (cubes i)) ≠ 5) := by
  classical
  let count (r : Fin 6) :=
    (Finset.univ.filter fun i => universalSourceClass (catalogueIndex (cubes i)) = r).card
  have total : ∑ r : Fin 6, count r = 15 := by
    dsimp [count]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have lower (r : Fin 5) : 3 ≤ count r.castSucc := universal_three_per_colour cubes hc hu r
  have hsum : (∑ r : Fin 5, 3) = ∑ r : Fin 5, count r.castSucc := by
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun r _ => lower r)
    rw [Fin.sum_univ_castSucc] at total
    have he : (∑ _ : Fin 5, (3 : ℕ)) = 15 := by decide
    omega
  have counts (r : Fin 5) : count r.castSucc = 3 :=
    ((Finset.sum_eq_sum_iff_of_le fun r _ => lower r).mp hsum r (Finset.mem_univ _)).symm
  have zero : count 5 = 0 := by
    rw [Fin.sum_univ_castSucc] at total
    have ht : 15 + count 5 = 15 := by simpa [counts] using total
    omega
  refine ⟨counts, ?_⟩
  intro i hi
  have hm : i ∈ (Finset.univ.filter fun j => universalSourceClass (catalogueIndex (cubes j)) = 5) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hp := Finset.card_pos.mpr ⟨i, hm⟩
  change 0 < count 5 at hp
  omega

/-- The graph whose edges are the smaller pairs of three adjacent sources. -/
def universalPairGraph (pairs : Fin 3 → Finset (Fin 4)) : SimpleGraph (Fin 4) where
  Adj p q := p ≠ q ∧ ∃ i, p ∈ pairs i ∧ q ∈ pairs i
  symm := ⟨by
    intro p q h
    obtain ⟨hne, i, hp, hq⟩ := h
    exact ⟨Ne.symm hne, i, hq, hp⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

instance (pairs : Fin 3 → Finset (Fin 4)) : DecidableRel (universalPairGraph pairs).Adj := by
  unfold universalPairGraph
  infer_instance

/-- Small finite combinatorial lemma: three pairs matching every prescribed
pair are distinct and form a connected three-edge graph on four vertices. -/
lemma universal_three_pair_check : ∀ pairs : Fin 3 → Finset (Fin 4),
    (∀ i, (pairs i).card = 2) →
    (∀ z : Fin 6, ∃ i j : Fin 3, i ≠ j ∧ universalPairFirst z ∈ pairs i ∧ universalPairSecond z ∈ pairs j) →
    Function.Injective pairs ∧
      (∀ p : Fin 4, p = 0 ∨ (universalPairGraph pairs).Adj 0 p ∨
        (∃ w, (universalPairGraph pairs).Adj 0 w ∧ (universalPairGraph pairs).Adj w p) ∨
        (∃ w z, (universalPairGraph pairs).Adj 0 w ∧
          (universalPairGraph pairs).Adj w z ∧ (universalPairGraph pairs).Adj z p)) ∧
      (universalPairGraph pairs).edgeFinset.card = 3 := by
  decide +kernel

lemma universal_three_pair_tree (pairs : Fin 3 → Finset (Fin 4))
    (hp : ∀ i, (pairs i).card = 2)
    (hm : ∀ z : Fin 6, ∃ i j : Fin 3, i ≠ j ∧ universalPairFirst z ∈ pairs i ∧ universalPairSecond z ∈ pairs j) :
    Function.Injective pairs ∧ (universalPairGraph pairs).IsTree := by
  obtain ⟨hi, hc, he⟩ := universal_three_pair_check pairs hp hm
  have connected : (universalPairGraph pairs).Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable (G := universalPairGraph pairs)).mpr
    refine ⟨0, fun p => ?_⟩
    rcases hc p with h | h | ⟨w, h, h'⟩ | ⟨w, z, h, h', h''⟩
    · subst p; exact .refl 0
    · exact h.reachable
    · exact h.reachable.trans h'.reachable
    · exact (h.reachable.trans h'.reachable).trans h''.reachable
  refine ⟨hi, (SimpleGraph.isTree_iff_connected_and_card).mpr ⟨connected, ?_⟩⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

lemma universal_class_pair_size (a : Fin 75) : ∀ r : Fin 5,
    universalSourceClass a = r.castSucc → (universalBiTypes a r).card = 2 := by
  fin_cases a <;> decide +kernel

/-- Every optimum has three different smaller pairs for each repeated colour;
these pairs form a spanning tree on the other four colours. -/
theorem minimum_universal_pair_trees (cubes : Fin 15 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hu : Submission.AdjacentUniversal cubes)
    (r : Fin 5) :
    ∃ e : Fin 3 ≃ {i // i ∈ universalRepeatSources cubes r},
      Function.Injective (fun j => universalBiTypes (catalogueIndex (cubes (e j).val)) r) ∧
      (universalPairGraph (fun j => universalBiTypes (catalogueIndex (cubes (e j).val)) r)).IsTree := by
  classical
  let e := (Finset.equivFinOfCardEq ((minimum_universal_counts cubes hc hu).1 r)).symm
  refine ⟨e, universal_three_pair_tree _ ?_ ?_⟩
  · intro j
    apply universal_class_pair_size
    exact (Finset.mem_filter.mp (e j).property).2
  · intro z
    obtain ⟨i, j, hij, hi, hj⟩ := universal_pair_suppliers cubes hc hu r z
    have mi : i ∈ universalRepeatSources cubes r := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (universal_bi_types _ r).2 ⟨_, hi⟩⟩
    have mj : j ∈ universalRepeatSources cubes r := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (universal_bi_types _ r).2 ⟨_, hj⟩⟩
    refine ⟨e.symm ⟨i, mi⟩, e.symm ⟨j, mj⟩, ?_, ?_, ?_⟩
    · intro h
      exact hij (congrArg Subtype.val (e.symm.injective h))
    · simpa using hi
    · simpa using hj

lemma universal_class_adjacent (a : Fin 75) : ∀ rot : Fin 24,
    universalSourceClass a ≠ 5 → Submission.AdjacentRepeat (rotate (catalogue a) rot) := by
  unfold Submission.AdjacentRepeat
  fin_cases a <;> decide +kernel

/-- Every fifteen-source universal pool consists of distinct adjacent-repeat
varieties, not merely distinct physical copies. -/
theorem minimum_universal_distinct_adjacent (cubes : Fin 15 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hu : Submission.AdjacentUniversal cubes) :
    (∀ i, Submission.AdjacentRepeat (cubes i)) ∧
      Function.Injective (fun i => catalogueIndex (cubes i)) := by
  classical
  have hn := (minimum_universal_counts cubes hc hu).2
  constructor
  · intro i
    obtain ⟨rot, hr⟩ := catalogueIndex_spec (cubes i) (hc i)
    rw [hr]
    exact universal_class_adjacent _ _ (hn i)
  · intro i j hij
    change catalogueIndex (cubes i) = catalogueIndex (cubes j) at hij
    let a := universalSourceClass (catalogueIndex (cubes i))
    have ha : a.val < 5 := by
      have hb := a.isLt
      have he : a ≠ 5 := hn i
      have hne : a.val ≠ 5 := fun h => he (Fin.ext h)
      omega
    let r : Fin 5 := ⟨a.val, ha⟩
    have hi : i ∈ universalRepeatSources cubes r :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext rfl⟩
    have hj : j ∈ universalRepeatSources cubes r := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hij]
      exact Fin.ext rfl
    obtain ⟨e, hp, _⟩ := minimum_universal_pair_trees cubes hc hu r
    have hs : e.symm ⟨i, hi⟩ = e.symm ⟨j, hj⟩ := by
      apply hp
      simp only [Equiv.apply_symm_apply]
      rw [hij]
    exact congrArg Subtype.val (e.symm.injective hs)

end FiveColour.Physical
