module
public import FiveColour.CoverChecks0
public import FiveColour.CoverChecks1
public import FiveColour.CoverChecks2
public import FiveColour.CoverChecks3
public import FiveColour.CoverChecks4
public import FiveColour.CoverChecks5
public import FiveColour.CoverChecks6
public import FiveColour.CoverChecks7
@[expose] public section
namespace FiveColour.Physical

lemma cover_orbit_block (kind : Fin 2) (b : Fin 8) (d : Fin 32) :
    CoverOrbitValid kind (coverBlock b d) := by
  fin_cases kind <;> fin_cases b
  · exact cover_orbit_0_0 d
  · exact cover_orbit_0_1 d
  · exact cover_orbit_0_2 d
  · exact cover_orbit_0_3 d
  · exact cover_orbit_0_4 d
  · exact cover_orbit_0_5 d
  · exact cover_orbit_0_6 d
  · exact cover_orbit_0_7 d
  · exact cover_orbit_1_0 d
  · exact cover_orbit_1_1 d
  · exact cover_orbit_1_2 d
  · exact cover_orbit_1_3 d
  · exact cover_orbit_1_4 d
  · exact cover_orbit_1_5 d
  · exact cover_orbit_1_6 d
  · exact cover_orbit_1_7 d

theorem cover_orbit_valid (kind : Fin 2) (d : Fin 256) : CoverOrbitValid kind d := by
  let b : Fin 8 := ⟨d.val / 32, by omega⟩
  let e : Fin 32 := ⟨d.val % 32, Nat.mod_lt _ (by decide)⟩
  have he : coverBlock b e = d := by apply Fin.ext; simp [coverBlock, b, e, Nat.div_add_mod]
  rw [← he]
  exact cover_orbit_block kind b e

theorem cover_root_valid (kind : Fin 2) (m : Fin 8) (d : Fin 256)
    (h : CoverEligible kind m d) : CoverRootValid kind m d := by
  fin_cases kind <;> fin_cases m
  · exact cover_root_0_0 d h
  · exact cover_root_0_1 d h
  · exact cover_root_0_2 d h
  · exact cover_root_0_3 d h
  · exact cover_root_0_4 d h
  · exact cover_root_0_5 d h
  · exact cover_root_0_6 d h
  · exact cover_root_0_7 d h
  · exact cover_root_1_0 d h
  · exact cover_root_1_1 d h
  · exact cover_root_1_2 d h
  · exact cover_root_1_3 d h
  · exact cover_root_1_4 d h
  · exact cover_root_1_5 d h
  · exact cover_root_1_6 d h
  · exact cover_root_1_7 d h
end FiveColour.Physical
