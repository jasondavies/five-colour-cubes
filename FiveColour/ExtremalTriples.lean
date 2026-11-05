module
public import FiveColour.ExtremalMatching
public import FiveColour.SmallSupport
public import FiveColour.StabiliserData
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Four copies of a and five each of b and c, indexed as distinct physical pieces. -/
def tripleVariety (a b c : Fin 75) (i : Fin 14) : Fin 75 :=
  if i.val < 4 then a else if i.val < 9 then b else c

def tripleFamily (a b c : Fin 75) (i : Fin 14) : Cube :=
  catalogue (tripleVariety a b c i)

lemma triple_uses_all (a b c : Fin 75) : ∀ i, UsesAllColours (tripleFamily a b c i) :=
  fun _ => catalogue_uses_all_colours _

lemma triple_multiplicity (a b c : Fin 75) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 75) : multiplicity (tripleFamily a b c) i =
      if i = a then 4 else if i = b then 5 else if i = c then 5 else 0 := by
  unfold multiplicity tripleFamily
  simp only [catalogue_index_faces]
  by_cases ha : i = a
  · subst i
    simp [tripleVariety, ite_eq_iff, Ne.symm hab, Ne.symm hac]
    decide +kernel
  · by_cases hb : i = b
    · subst i
      simp [tripleVariety, ite_eq_iff, ha, hab, Ne.symm hbc]
      decide +kernel
    · by_cases hc : i = c
      · subst i
        simp [tripleVariety, ite_eq_iff, ha, hb, hac, hbc]
        decide +kernel
      · simp [tripleVariety, ite_eq_iff, ha, hb, hc, Ne.symm ha, Ne.symm hb, Ne.symm hc]

/-- A small positive witness specifies an actual copy at each target corner. -/
structure TriplePlacement where
  target : Fin 75
  copies : Fin 8 → Fin 14
  deriving Inhabited

def TriplePlacement.Valid (a b c : Fin 75) (w : TriplePlacement) : Prop :=
  Function.Injective w.copies ∧ ∀ k,
    (Replay.fits w.target (tripleVariety a b c (w.copies k))).testBit k.val = true

instance instDecidableTriplePlacementValid (a b c : Fin 75) (w : TriplePlacement) : Decidable (w.Valid a b c) := by
  unfold TriplePlacement.Valid Function.Injective
  infer_instance

lemma triple_placement_solves (a b c : Fin 75) (w : TriplePlacement)
    (h : w.Valid a b c) : HasSolution (tripleFamily a b c) :=
  (hasSolution_iff_catalogue _).mpr
    ⟨w.target, ⟨w.copies,h.1⟩, fun k => (incidence_fits _ _ _).mp (h.2 k)⟩

end FiveColour.Physical
