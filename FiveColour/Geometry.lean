module
public import FiveColour.Problem
public import ColourCubes.RotationAction
@[expose] public section
namespace FiveColour.Physical
open ColourCubes.Geometry

/-- Specialise the shared rotation action to five face colours. -/
abbrev rotate (c : Cube) (r : Fin 24) : Cube := fun f => c (ColourCubes.rotations r f)

theorem fits_rotate_source (c t : Cube) (r : Fin 24) (k : Fin 8) :
    Fits (rotate c r) t k ↔ Fits c t k :=
  ColourCubes.Geometry.fits_rotate_source c t r k

abbrev cyclicEq_trans := @ColourCubes.Geometry.cyclicEq_trans (Fin 5)
abbrev cyclicEq_symm := @ColourCubes.Geometry.cyclicEq_symm (Fin 5)

theorem rotated_corner (t : Cube) (r : Fin 24) (k : Fin 8) :
    CyclicEq (corner t (slotEquiv r k)) (corner (rotate t r) k) :=
  ColourCubes.Geometry.rotated_corner t r k

theorem fits_rotate_target (c t : Cube) (r : Fin 24) (k : Fin 8) :
    Fits c (rotate t r) k ↔ Fits c t (slotEquiv r k) :=
  ColourCubes.Geometry.fits_rotate_target c t r k

theorem unrotate_solution {n : Nat} (cubes : Fin n → Cube) (t : Cube) (r : Fin 24)
    (copies : Fin 8 ↪ Fin n) (h : ∀ k, Fits (cubes (copies k)) (rotate t r) k) :
    ∃ copies' : Fin 8 ↪ Fin n, ∀ k, Fits (cubes (copies' k)) t k :=
  ColourCubes.Geometry.unrotate_solution cubes t r copies h

end FiveColour.Physical
