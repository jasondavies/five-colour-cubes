module
public import FiveColour.CubeBoxBridge
@[expose] public section
namespace FiveColour.Physical

/-- Cube completion is the equal-length case of cuboid completion. -/
lemma full_of_frame {m : ℕ} (k : ℕ) (cubes : Fin m → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) (hm : (k+2)^3 ≤ m)
    (h : FrameSolvable k cubes) : FullSolvable k cubes := by
  apply (full_iff_rect k cubes).mpr
  apply rect_full_of_frame (fun _ => k) cubes hc
  · simpa [Fin.prod_univ_succ,pow_succ,Nat.mul_assoc] using hm
  · exact (frame_iff_rect k cubes).mp h

/-- Completing a frame adds only the requirement that enough physical pieces remain. -/
theorem full_iff_frame_and_size {m : ℕ} (k : ℕ) (cubes : Fin m → Cube)
    (hc : ∀ j, UsesAllColours (cubes j)) : FullSolvable k cubes ↔
      FrameSolvable k cubes ∧ (k+2)^3 ≤ m :=
  ⟨fun h => ⟨frame_of_full k cubes h,full_requires_pieces k cubes h⟩,
    fun h => full_of_frame k cubes hc h.2 h.1⟩

end FiveColour.Physical
