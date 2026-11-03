module
public import FiveColour.Problem
public import ColourCubes.RotationAction
@[expose] public section
namespace FiveColour.Physical
open ColourCubes.Geometry

/-- Specialise the shared rotation action to five face colours. -/
abbrev rotate := @ColourCubes.Geometry.rotate (Fin 5)

theorem fits_rotate_source (c t : Cube) (r : Fin 24) (k : Fin 8) :
    Fits (rotate c r) t k ↔ Fits c t k :=
  ColourCubes.Geometry.fits_rotate_source c t r k

theorem fits_rotate_target (c t : Cube) (r : Fin 24) (k : Fin 8) :
    Fits c (rotate t r) k ↔ Fits c t (slotEquiv r k) :=
  ColourCubes.Geometry.fits_rotate_target c t r k

theorem unrotate_solution {n : Nat} (cubes : Fin n → Cube) (t : Cube) (r : Fin 24)
    (copies : Fin 8 ↪ Fin n) (h : ∀ k, Fits (cubes (copies k)) (rotate t r) k) :
    ∃ copies' : Fin 8 ↪ Fin n, ∀ k, Fits (cubes (copies' k)) t k :=
  ColourCubes.Geometry.unrotate_solution cubes t r copies h

end FiveColour.Physical
