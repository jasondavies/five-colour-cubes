module
public import FiveColour.Catalogue
public import FiveColour.Geometry
public import Mathlib.Combinatorics.Hall.Finite
@[expose] public section
namespace FiveColour.Physical
open ThreeColour.Geometry

/-- Compute compatibility through the verified corner criterion. -/
instance (c t : Cube) (k : Fin 8) : Decidable (Fits c t k) :=
  decidable_of_iff (∃ l, CyclicEq (corner c l) (corner t k)) (fits_iff_corner c t k).symm

/-- Physical copies that can serve at least one corner in K. -/
def neighbours {n : Nat} (cubes : Fin n → Cube) (t : Cube) (K : Finset (Fin 8)) :
    Finset (Fin n) := Finset.univ.filter fun i => ∃ k ∈ K, Fits (cubes i) t k

/-- Any assignment of distinct physical copies satisfies Hall's necessary inequality. -/
theorem solution_card_le {n : Nat} (cubes : Fin n → Cube) (t : Cube)
    (copies : Fin 8 ↪ Fin n) (h : ∀ k, Fits (cubes (copies k)) t k)
    (K : Finset (Fin 8)) : K.card ≤ (neighbours cubes t K).card := by
  apply Finset.card_le_card_of_injOn copies
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, h k⟩
  · exact fun _ _ _ _ he => copies.injective he

/-- Eight distinct physical copies assigned to a specified target. -/
def SolvesTarget {n : Nat} (cubes : Fin n → Cube) (t : Cube) : Prop :=
  ∃ copies : Fin 8 ↪ Fin n, ∀ k, Fits (cubes (copies k)) t k

/-- Hall's marriage theorem applied to the eight physical corner requirements. -/
theorem solvesTarget_iff_hall {n : Nat} (cubes : Fin n → Cube) (t : Cube) :
    SolvesTarget cubes t ↔ ∀ K, K.card ≤ (neighbours cubes t K).card := by
  let allowed : Fin 8 → Finset (Fin n) := fun k =>
    Finset.univ.filter fun i => Fits (cubes i) t k
  have hneigh (K : Finset (Fin 8)) : K.biUnion allowed = neighbours cubes t K := by
    ext i
    simp [allowed, neighbours]
  constructor
  · rintro ⟨copies, h⟩
    exact solution_card_le cubes t copies h
  · intro h
    have hh : ∀ K : Finset (Fin 8), K.card ≤ (K.biUnion allowed).card := by
      simpa only [hneigh] using h
    obtain ⟨f, hf, hfits⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp hh
    exact ⟨⟨f, hf⟩, fun k => (Finset.mem_filter.mp (hfits k)).2⟩

/-- Failure is witnessed by a deficient set of target corners. -/
theorem not_solvesTarget_iff {n : Nat} (cubes : Fin n → Cube) (t : Cube) :
    ¬ SolvesTarget cubes t ↔ ∃ K, (neighbours cubes t K).card < K.card := by
  rw [solvesTarget_iff_hall]
  simp only [not_forall, not_le]

/-- Catalogue completeness and rotation transport suffice for arbitrary target orientations. -/
theorem hasSolution_iff_catalogue {n : Nat} (cubes : Fin n → Cube) :
    HasSolution cubes ↔ ∃ t : Fin 75, SolvesTarget cubes (catalogue t) := by
  constructor
  · rintro ⟨target, ht, copies, hfits⟩
    obtain ⟨t, r, hr⟩ := catalogue_complete target ht
    have he : target = rotate (catalogue t) r := funext hr
    rw [he] at hfits
    exact ⟨t, unrotate_solution cubes (catalogue t) r copies hfits⟩
  · rintro ⟨t, copies, hfits⟩
    exact ⟨catalogue t, catalogue_uses_all_colours t, copies, hfits⟩

/-- A collection fails precisely when every catalogue target has a Hall deficiency. -/
theorem not_hasSolution_iff_hall {n : Nat} (cubes : Fin n → Cube) :
    ¬ HasSolution cubes ↔ ∀ t : Fin 75, ∃ K,
      (neighbours cubes (catalogue t) K).card < K.card := by
  rw [hasSolution_iff_catalogue]
  simp only [not_exists, not_solvesTarget_iff]

end FiveColour.Physical
