module
public import FiveColour.ThinGeometry
public import FiveColour.ThinChoice
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- The uniform thin-box bounds, including the sharp fifteen-copy
2×2×3 bound and the seventeen-copy 2×3×3 bound. -/
theorem thin_frame_of_threshold (h : Threshold15) {n : ℕ} (w : Fin 2) (M : ℕ) (hM : 1 ≤ M)
    (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hn : 4*M+11+2*w.val ≤ n) : BoxFrameSolvable 2 (w.val+2) (M+2) cubes := by
  classical
  let d := 2*M+6+w.val
  have hw := w.isLt
  obtain ⟨t,corners,hf,z,hz,hedges⟩ := thin_target h d cubes hc (by omega) (by dsimp [d]; omega)
  let axes := Equiv.swap (0 : Fin 3) z
  let l := fun a => ![0,w.val,M] (axes a)
  have hmono : ∀ a, axes a ≠ 0 → BichromaticAxis (catalogue t) a := by
    intro a ha
    exact hz a (fun he => ha ((swap_zero z a).mpr he))
  have hsize : Fintype.card (RectSlot l) ≤ n := by
    rw [rectSlot_card]
    have he := Equiv.sum_comp axes (fun i => ![0,w.val,M] i)
    change (∑ i, l i) = _ at he
    rw [he]
    simp [Fin.sum_univ_succ]
    omega
  have hrect : RectSolvable l cubes := by
    apply rect_from_corners l cubes t d hsize
      (fun i => thin_missing_bound _ (hc i) t axes w M hM hmono) corners hf
    intro e he
    apply hedges e
    intro hez
    have hx : axes (edgeAxis e) = 0 := (swap_zero z _).mpr hez
    simp [l,hx] at he
  refine ⟨axes,?_⟩
  simpa only [Nat.add_sub_cancel,Nat.sub_self] using hrect

theorem box223_of_threshold (h : Threshold15) (cubes : Fin 15 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) : BoxFrameSolvable 2 2 3 cubes :=
  thin_frame_of_threshold h 0 1 (by decide) cubes hc (by decide)
theorem box233_of_threshold (h : Threshold15) (cubes : Fin 17 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) : BoxFrameSolvable 2 3 3 cubes :=
  thin_frame_of_threshold h 1 1 (by decide) cubes hc (by decide)
end FiveColour.Physical
