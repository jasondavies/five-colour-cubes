module
public import FiveColour.CoverData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical
lemma cover_orbit_0_5 : ∀ d : Fin 32,
    CoverOrbitValid 0 (coverBlock 5 d) := by decide +kernel

lemma cover_root_0_5 : ∀ d : Fin 256,
    CoverEligible 0 5 d → CoverRootValid 0 5 d := by decide +kernel

lemma cover_orbit_1_5 : ∀ d : Fin 32,
    CoverOrbitValid 1 (coverBlock 5 d) := by decide +kernel

lemma cover_root_1_5 : ∀ d : Fin 256,
    CoverEligible 1 5 d → CoverRootValid 1 5 d := by decide +kernel

end FiveColour.Physical
