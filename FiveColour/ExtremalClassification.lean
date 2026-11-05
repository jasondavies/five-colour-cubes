module
public import FiveColour.ExtremalMultiplicity
public import FiveColour.ExtremalSymmetry
public import FiveColour.ExtremalExamples
public import FiveColour.ExtremalTripleChecks
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

lemma multiplicity_zero_off_support {n : ℕ} (cubes : Fin n → Cube) (i : Fin 75)
    (h : i ∉ varietySupport cubes) : multiplicity cubes i = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply h
  rw [← (Finset.mem_filter.mp hj).2]
  exact support_mem cubes j

lemma inventory_of_three_counts {n : ℕ} (cubes : Fin n → Cube) (a b c : Fin 75)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : varietySupport cubes = {a,b,c})
    (ha : multiplicity cubes a = 4) (hb : multiplicity cubes b = 5)
    (hc : multiplicity cubes c = 5) : SameInventory cubes (tripleFamily a b c) := by
  intro i
  rw [triple_multiplicity a b c hab hac hbc]
  split_ifs with hia hib hic
  · simpa [hia] using ha
  · simpa [hib] using hb
  · simpa [hic] using hc
  · apply multiplicity_zero_off_support
    simp [hs,hia,hib,hic]

/-- The multiplicity bound and total fourteen force the unique four-copy variety. -/
theorem three_variety_pattern (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hno : ¬ HasSolution cubes)
    (hs : (varietySupport cubes).card = 3) :
    ∃ a b c : Fin 75, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      SameInventory cubes (tripleFamily a b c) := by
  obtain ⟨a,b,c,hab,hac,hbc,hs⟩ := Finset.card_eq_three.mp hs
  have ha := fourteen_multiplicity_le_five cubes hc hno a
  have hb := fourteen_multiplicity_le_five cubes hc hno b
  have hc' := fourteen_multiplicity_le_five cubes hc hno c
  have ht : ∑ i, multiplicity cubes i = 14 := by
    have h := multiplicity_total cubes
    unfold Certificate.mass multiplicityVector at h
    exact_mod_cast h
  have hsum := Finset.sum_subset (Finset.subset_univ (varietySupport cubes))
    (fun i _ hi => multiplicity_zero_off_support cubes i hi)
  rw [ht, hs] at hsum
  simp [hab,hac,hbc] at hsum
  have hp : (multiplicity cubes a = 4 ∧ multiplicity cubes b = 5 ∧ multiplicity cubes c = 5) ∨
      (multiplicity cubes b = 4 ∧ multiplicity cubes a = 5 ∧ multiplicity cubes c = 5) ∨
      (multiplicity cubes c = 4 ∧ multiplicity cubes a = 5 ∧ multiplicity cubes b = 5) := by omega
  rcases hp with ⟨ha,hb,hc'⟩ | ⟨hb,ha,hc'⟩ | ⟨hc',ha,hb⟩
  · exact ⟨a,b,c,hab,hac,hbc, inventory_of_three_counts cubes a b c hab hac hbc hs ha hb hc'⟩
  · exact ⟨b,a,c,Ne.symm hab,hbc,hac, inventory_of_three_counts cubes b a c (Ne.symm hab) hbc hac
      (by simpa only [Finset.insert_comm] using hs) hb ha hc'⟩
  · refine ⟨c,a,b,Ne.symm hac,Ne.symm hbc,hab, inventory_of_three_counts cubes c a b
      (Ne.symm hac) (Ne.symm hbc) hab ?_ hc' ha hb⟩
    rw [hs]
    ext i
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim (fun h => Or.inr (Or.inr h)) Or.inl),
      fun h => h.elim (fun h => Or.inr (Or.inr h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))⟩

lemma triple_swap_inventory (a b c : Fin 75) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    SameInventory (tripleFamily a b c) (tripleFamily a c b) := by
  intro i
  rw [triple_multiplicity a b c hab hac hbc,
    triple_multiplicity a c b hac hab (Ne.symm hbc)]
  by_cases ha : i = a <;> by_cases hb : i = b <;> by_cases hc : i = c <;> simp_all

lemma extremal_orbit_inventory (j : Fin 5) (g : Fin 16) (swap : Bool) :
    SameInventory (fun i => (stabiliserSymmetry g).apply (extremalFamily j i))
      (tripleFamily 0
        (stabiliserAction g (if swap then extremalC j else extremalB j))
        (stabiliserAction g (if swap then extremalB j else extremalC j))) := by
  have hfix : stabiliserAction g 0 = 0 := by
    have : ∀ g : Fin 16, stabiliserAction g 0 = 0 := by decide +kernel
    exact this g
  cases swap
  · simpa only [extremalFamily, Bool.false_eq_true, ↓reduceIte, stabiliser_variety, hfix] using
      triple_inventory_apply 0 (extremalB j) (extremalC j) (stabiliserSymmetry g)
  · have h := sameInventory_apply _ _ (extremal_uses_all j)
      (triple_uses_all 0 (extremalC j) (extremalB j))
      (triple_swap_inventory 0 (extremalB j) (extremalC j)
        (extremal_distinct j).1 (extremal_distinct j).2.1 (extremal_distinct j).2.2)
      (stabiliserSymmetry g)
    have ht := triple_inventory_apply 0 (extremalC j) (extremalB j) (stabiliserSymmetry g)
    intro i
    simpa only [Bool.true_eq, ↓reduceIte, stabiliser_variety, hfix] using (h i).trans (ht i)

lemma normalised_triple_class (kind : Fin 2) (b c : Fin 75)
    (hab : tripleAnchor kind ≠ b) (hac : tripleAnchor kind ≠ c) (hbc : b < c)
    (hno : ¬ HasSolution (tripleFamily (tripleAnchor kind) b c)) :
    ∃ j : Fin 5, SymmetryEquivalent (tripleFamily (tripleAnchor kind) b c) (extremalFamily j) := by
  have hbc' : b ≠ c := ne_of_lt hbc
  have hm (i : Fin 75) (hi : i = tripleAnchor kind ∨ i = b ∨ i = c) :
      4 ≤ multiplicity (tripleFamily (tripleAnchor kind) b c) i := by
    rw [triple_multiplicity _ _ _ hab hac hbc']
    rcases hi with rfl | rfl | rfl <;> simp_all <;> split_ifs <;> omega
  have nonzero (i j : Fin 75) (hij : i ≠ j)
      (hi : i = tripleAnchor kind ∨ i = b ∨ i = c)
      (hj : j = tripleAnchor kind ∨ j = b ∨ j = c) : Replay.fits i j ≠ 0 := by
    intro hz
    exact hno (disjoint_pair_suffices _ (triple_uses_all _ _ _) i j hij hz (hm i hi) (hm j hj))
  have hr : TripleResidual kind b c := ⟨hab,hac,hbc,
    fun h => hno (triple_criterion_solves _ _ _ _ h),
    fun h => hno (triple_criterion_solves _ _ _ _ h),
    fun h => hno (triple_criterion_solves _ _ _ _ h),
    nonzero _ _ hab (Or.inl rfl) (Or.inr (Or.inl rfl)),
    nonzero _ _ hac (Or.inl rfl) (Or.inr (Or.inr rfl)),
    nonzero _ _ hbc' (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))⟩
  obtain ⟨w,hw,hkind,hb,hc⟩ := triple_residuals_cover kind b c hr
  have hw := triple_residuals_valid w hw
  rw [hkind,hb,hc] at hw
  cases he : w.reduction with
  | solve w =>
    rw [he] at hw
    exact False.elim (hno (triple_criterion_solves _ _ _ w hw))
  | orbit j g swap =>
    rw [he] at hw
    obtain ⟨ha,hb,hc⟩ := hw
    have hrep : SymmetryEquivalent (extremalFamily j) (tripleFamily (tripleAnchor kind) b c) := by
      refine ⟨stabiliserSymmetry g, ?_⟩
      simpa only [ha,hb,hc] using extremal_orbit_inventory j g swap
    exact ⟨j,symmetryEquivalent_symm _ _ (extremal_uses_all j) (triple_uses_all _ _ _) hrep⟩

lemma normalised_triple_class_unordered (kind : Fin 2) (b c : Fin 75)
    (hab : tripleAnchor kind ≠ b) (hac : tripleAnchor kind ≠ c) (hbc : b ≠ c)
    (hno : ¬ HasSolution (tripleFamily (tripleAnchor kind) b c)) :
    ∃ j : Fin 5, SymmetryEquivalent (tripleFamily (tripleAnchor kind) b c) (extremalFamily j) := by
  rcases lt_or_gt_of_ne hbc with hlt | hgt
  · exact normalised_triple_class kind b c hab hac hlt hno
  · have hs := inventory_equivalent _ _ (triple_swap_inventory _ _ _ hab hac hbc)
    have hno' : ¬ HasSolution (tripleFamily (tripleAnchor kind) c b) :=
      fun h => hno ((symmetryEquivalent_hasSolution _ _ (triple_uses_all _ _ _) (triple_uses_all _ _ _) hs).mpr h)
    obtain ⟨j,hj⟩ := normalised_triple_class kind c b hac hab hgt hno'
    exact ⟨j,symmetryEquivalent_trans _ _ _ (triple_uses_all _ _ _) (triple_uses_all _ _ _) hs hj⟩

lemma triple_obstruction_class (a b c : Fin 75) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ HasSolution (tripleFamily a b c)) :
    ∃ j : Fin 5, SymmetryEquivalent (tripleFamily a b c) (extremalFamily j) := by
  let s := anchorSymmetry a
  let b' := varietyEquiv s b
  let c' := varietyEquiv s c
  have hn : SymmetryEquivalent (tripleFamily a b c) (tripleFamily (anchorFor a) b' c') := by
    refine ⟨s, ?_⟩
    simpa only [s, normalise_variety] using triple_inventory_apply a b c s
  have hnno : ¬ HasSolution (tripleFamily (anchorFor a) b' c') :=
    fun h => hno ((symmetryEquivalent_hasSolution _ _ (triple_uses_all _ _ _) (triple_uses_all _ _ _) hn).mpr h)
  have hab' : anchorFor a ≠ b' := by
    rw [← normalise_variety a]
    exact fun h => hab ((varietyEquiv s).injective h)
  have hac' : anchorFor a ≠ c' := by
    rw [← normalise_variety a]
    exact fun h => hac ((varietyEquiv s).injective h)
  have hbc' : b' ≠ c' := fun h => hbc ((varietyEquiv s).injective h)
  have hk : ∃ kind : Fin 2, tripleAnchor kind = anchorFor a := by
    unfold anchorFor
    split
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  obtain ⟨kind,hk⟩ := hk
  rw [← hk] at hab' hac' hnno hn
  obtain ⟨j,hj⟩ := normalised_triple_class_unordered kind b' c' hab' hac' hbc' hnno
  exact ⟨j,symmetryEquivalent_trans _ _ _ (triple_uses_all _ _ _) (triple_uses_all _ _ _) hn hj⟩

/-- Complete classification of physical fourteen-cube obstructions using three varieties. -/
theorem three_variety_obstruction_iff (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hs : (varietySupport cubes).card = 3) :
    ¬ HasSolution cubes ↔ ∃ j : Fin 5, SymmetryEquivalent cubes (extremalFamily j) := by
  constructor
  · intro hno
    obtain ⟨a,b,c,hab,hac,hbc,hi⟩ := three_variety_pattern cubes hc hno hs
    have he := inventory_equivalent _ _ hi
    have ht : ¬ HasSolution (tripleFamily a b c) :=
      fun h => hno ((symmetryEquivalent_hasSolution _ _ hc (triple_uses_all _ _ _) he).mpr h)
    obtain ⟨j,hj⟩ := triple_obstruction_class a b c hab hac hbc ht
    exact ⟨j,symmetryEquivalent_trans _ _ _ hc (triple_uses_all _ _ _) he hj⟩
  · rintro ⟨j,hj⟩ hsol
    exact extremal_no_solution j ((symmetryEquivalent_hasSolution _ _ hc (extremal_uses_all j) hj).mp hsol)

def extremalCount (j : Fin 5) (i : Fin 75) : ℕ :=
  if i = 0 then 4 else if i = extremalB j then 5 else if i = extremalC j then 5 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma extremal_inequivalent_check : ∀ (j k : Fin 5) (g : Fin 16),
    (∀ i : Fin 75, extremalCount j i = extremalCount k (stabiliserAction g i)) → j = k := by
  decide +kernel

/-- The five representatives remain distinct under every colour permutation and global reflection. -/
theorem extremal_inequivalent (j k : Fin 5)
    (h : SymmetryEquivalent (extremalFamily j) (extremalFamily k)) : j = k := by
  obtain ⟨s,hs⟩ := h
  have hi (i : Fin 75) : multiplicity (extremalFamily j) i =
      multiplicity (extremalFamily k) (varietyEquiv s i) :=
    (multiplicity_apply s _ (extremal_uses_all j) i).symm.trans (hs _)
  have hf : varietyEquiv s 0 = 0 := by
    have h4 := hi 0
    rw [extremal_multiplicity,extremal_multiplicity] at h4
    simp only [ite_true] at h4
    split_ifs at h4 with ha hb hc
    · exact ha
    all_goals omega
  obtain ⟨g,hg⟩ := opposite_stabiliser_complete s hf
  subst s
  apply extremal_inequivalent_check j k g
  intro i
  simpa only [extremal_multiplicity,stabiliser_variety,extremalCount] using hi i

end FiveColour.Physical
