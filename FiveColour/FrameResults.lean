module
public import FiveColour.FrameReserve
public import FiveColour.FullCube
@[expose] public section
namespace FiveColour.Physical

/-- The side-length form of the reserve bound. -/
theorem frame_bound_of_threshold (h : Threshold15) {m : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hm : 25*n-39 ≤ m) : FrameSolvable (n-2) cubes :=
  frame_of_threshold h (n-2) (by omega) cubes hc (by omega)

lemma cube_size_ge_frame_bound (q : ℕ) (hq : 2 ≤ q) : 25*q+11 ≤ (q+2)^3 := by
  by_cases h : q = 2
  · subst q; norm_num
  have hq3 : 3 ≤ q := by omega
  have hs : 25 ≤ (q+2)^2 := by nlinarith
  have hm := Nat.mul_le_mul_right (q+2) hs
  rw [← pow_succ] at hm
  change 25*(q+2) ≤ (q+2)^3 at hm
  omega

/-- For side length at least four, piece count is the only obstruction. -/
theorem full_iff_size_of_threshold (h : Threshold15) {m : ℕ} (n : ℕ) (hn : 4 ≤ n)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FullSolvable (n-2) cubes ↔ n^3 ≤ m := by
  have he : n-2+2 = n := by omega
  constructor
  · intro hf
    simpa only [he] using full_requires_pieces (n-2) cubes hf
  · intro hm
    have hb := cube_size_ge_frame_bound (n-2) (by omega)
    rw [he] at hb
    exact full_of_frame (n-2) cubes hc (by simpa only [he] using hm)
      (frame_of_threshold h (n-2) (by omega) cubes hc (hb.trans hm))

/-- All n³ supplied cubes can be used, for every n ≥ 4. -/
theorem full_cube_of_threshold (h : Threshold15) (n : ℕ) (hn : 4 ≤ n)
    (cubes : Fin (n^3) → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FullSolvable (n-2) cubes :=
  (full_iff_size_of_threshold h n hn cubes hc).mpr le_rfl

/-- The least guaranteed pool size for a complete cube is exactly n³. -/
theorem complete_threshold_of_threshold (h : Threshold15) (n : ℕ) (hn : 4 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → FullSolvable (n-2) cubes} (n^3) := by
  refine ⟨fun m cubes hc hm => (full_iff_size_of_threshold h n hn cubes hc).mpr hm, ?_⟩
  intro v hv
  exact (full_iff_size_of_threshold h n hn (fun _ : Fin v => catalogue 0)
    (fun _ => catalogue_uses_all_colours 0)).mp
      (hv v _ (fun _ => catalogue_uses_all_colours 0) le_rfl)

end FiveColour.Physical
