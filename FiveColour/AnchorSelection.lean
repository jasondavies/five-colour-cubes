module
public import FiveColour.SharedCorners
@[expose] public section
namespace FiveColour.Physical

/-- Varieties present in a collection, without multiplicity. -/
def usedVarieties {n : Nat} (cubes : Fin n → Cube) : Finset (Fin 75) :=
  Finset.univ.image fun q => catalogueIndex (cubes q)

lemma multiplicity_pos_of_copy {n : Nat} (cubes : Fin n → Cube) (q : Fin n) :
    0 < multiplicity cubes (catalogueIndex (cubes q)) := by
  apply Finset.card_pos.mpr
  exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

lemma mem_usedVarieties {n : Nat} (cubes : Fin n → Cube) (i : Fin 75) :
    i ∈ usedVarieties cubes ↔ 0 < multiplicity cubes i := by
  constructor
  · intro h
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h
    exact multiplicity_pos_of_copy cubes q
  · intro h
    obtain ⟨q, hq⟩ := Finset.card_pos.mp h
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩

lemma catalogueIndex_injective {n : Nat} (cubes : Fin n → Cube)
    (h : ∀ i, multiplicity cubes i ≤ 1) : Function.Injective (fun q => catalogueIndex (cubes q)) := by
  intro q r hqr
  exact (Finset.card_le_one.mp (h (catalogueIndex (cubes q)))) q
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) r
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqr.symm⟩)

lemma usedVarieties_card {n : Nat} (cubes : Fin n → Cube)
    (h : ∀ i, multiplicity cubes i ≤ 1) : (usedVarieties cubes).card = n := by
  rw [usedVarieties, Finset.card_image_of_injective _ (catalogueIndex_injective cubes h)]
  simp

lemma maximum_multiplicity {n : Nat} (cubes : Fin n → Cube) (hn : 0 < n) :
    ∃ a, 0 < multiplicity cubes a ∧ ∀ i, multiplicity cubes i ≤ multiplicity cubes a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (multiplicity cubes) Finset.univ_nonempty
  have hq := multiplicity_pos_of_copy cubes ⟨0, hn⟩
  have hqa := ha (catalogueIndex (cubes ⟨0, hn⟩)) (Finset.mem_univ _)
  exact ⟨a, by omega, fun i => ha i (Finset.mem_univ _)⟩

/-- Anchor selection supplies the class caps and, in the distinct/all-adjacent
case, a positive mass that rules out the exceptional cover after normalisation. -/
def AnchorSelected {n : Nat} (cubes : Fin n → Cube) (a : Fin 75) (kind : Fin 2) (m : Fin 8) : Prop :=
  anchorFor a = canonicalAnchor kind ∧ 0 < m.val ∧ multiplicity cubes a = m.val ∧
    (∀ i, multiplicity cubes i ≤ classCap kind m i) ∧
    (kind = 0 → m = 1 →
      0 < Certificate.mass (multiplicityVector (fun q => (anchorSymmetry a).apply (cubes q)))
        (anchorBad 3 (cornerSet omittedCover.val)))

/-- Adjacent anchors have priority at maximum multiplicity at least two.
For distinct collections choose an opposite anchor when available, and otherwise
use the shared-corner pigeonhole argument. -/
theorem select_anchor {n : Nat} (cubes : Fin n → Cube)
    (hc : ∀ q, UsesAllColours (cubes q)) (hn : 10 < n)
    (hseven : ∀ i, multiplicity cubes i ≤ 7) :
    ∃ (a : Fin 75) (kind : Fin 2) (m : Fin 8), AnchorSelected cubes a kind m := by
  obtain ⟨a, hapos, hmax⟩ := maximum_multiplicity cubes (by omega)
  by_cases hone : multiplicity cubes a = 1
  · have hsingle : ∀ i, multiplicity cubes i ≤ 1 := by intro i; simpa only [hone] using hmax i
    by_cases hopp : ∃ b, OppositeRepeat (catalogue b) ∧ 0 < multiplicity cubes b
    · obtain ⟨b, hb, hbpos⟩ := hopp
      have hb1 : multiplicity cubes b = 1 := by have := hsingle b; omega
      refine ⟨b, 1, 1, ?_, by decide, hb1, ?_, ?_⟩
      · simp [anchorFor, canonicalAnchor, hb]
      · intro i
        simpa [classCap] using hsingle i
      · intro hk
        simp at hk
    · have hz : ∀ i, OppositeRepeat (catalogue i) → multiplicity cubes i = 0 := by
        intro i hi
        by_contra h0
        exact hopp ⟨i, hi, by omega⟩
      have hadj : ∀ i ∈ usedVarieties cubes, ¬ OppositeRepeat (catalogue i) := by
        intro i hi hio
        exact hopp ⟨i, hio, (mem_usedVarieties cubes i).mp hi⟩
      obtain ⟨i, hi, j, hj, hij, hkey⟩ := exists_shared_double (usedVarieties cubes)
        (by simpa only [usedVarieties_card cubes hsingle] using hn) hadj
      have hi1 : multiplicity cubes i = 1 := by
        have := (mem_usedVarieties cubes i).mp hi
        have := hsingle i
        omega
      refine ⟨i, 0, 1, ?_, by decide, hi1, ?_, ?_⟩
      · simp [anchorFor, canonicalAnchor, hadj i hi]
      · intro k
        by_cases hk : OppositeRepeat (catalogue k)
        · simp [classCap, hk, hz k hk]
        · simpa [classCap, hk] using hsingle k
      · intro _ _
        exact normalised_omitted_mass_pos cubes hc i j hij (hadj i hi)
          ((mem_usedVarieties cubes j).mp hj) hkey
  · let m : Fin 8 := ⟨multiplicity cubes a, by have := hseven a; omega⟩
    have hmval : m.val = multiplicity cubes a := rfl
    have hmne : m ≠ 1 := by intro he; have := congrArg Fin.val he; simp only [hmval] at this; exact hone this
    by_cases hadjmax : ∃ b, ¬ OppositeRepeat (catalogue b) ∧ multiplicity cubes b = m.val
    · obtain ⟨b, hb, hbm⟩ := hadjmax
      refine ⟨b, 0, m, ?_, by omega, hbm, ?_, ?_⟩
      · simp [anchorFor, canonicalAnchor, hb]
      · intro i
        simpa [classCap, hmne, hmval] using hmax i
      · intro _ he
        exact (hmne he).elim
    · have ha : OppositeRepeat (catalogue a) := by
        by_contra hna
        exact hadjmax ⟨a, hna, hmval.symm⟩
      refine ⟨a, 1, m, ?_, by omega, hmval.symm, ?_, ?_⟩
      · simp [anchorFor, canonicalAnchor, ha]
      · intro i
        by_cases hi : OppositeRepeat (catalogue i)
        · simpa [classCap, hmne, hi, hmval] using hmax i
        · have hne : multiplicity cubes i ≠ m.val := fun he => hadjmax ⟨i, hi, he⟩
          have hb := hmax i
          have hbound : multiplicity cubes i ≤ m.val - 1 := by omega
          simpa [classCap, hmne, hi] using hbound
      · intro _ he
        exact (hmne he).elim

end FiveColour.Physical
