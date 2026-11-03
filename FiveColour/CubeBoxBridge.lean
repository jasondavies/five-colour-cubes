module
public import FiveColour.BoxModel
public import FiveColour.CubeModel
@[expose] public section
namespace FiveColour.Physical

/-- Equal edge lengths identify the cube and cuboid frame positions. -/
def cubeFrameEquiv (q : ℕ) : FrameSlot q ≃ RectSlot (fun _ => q) :=
  Equiv.sumCongr (Equiv.refl _) {
    toFun := fun p => ⟨p.1,p.2⟩
    invFun := fun p => (p.1,p.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma cubeFrameEquiv_exposed (q : ℕ) (p : FrameSlot q) :
    rectExposed (fun _ => q) (cubeFrameEquiv q p) = frameExposed q p := by
  cases p <;> rfl

lemma cubeFrameEquiv_fits (c t : Cube) (q : ℕ) (p : FrameSlot q) :
    RectFits c t (cubeFrameEquiv q p) ↔ FrameFits c t p := by
  cases p <;> rfl

/-- The identification preserves individual physical placements and their target. -/
lemma frame_iff_rect {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) :
    FrameSolvable q cubes ↔ RectSolvable (fun _ => q) cubes := by
  constructor
  · rintro ⟨t,ht,f,hf⟩
    refine ⟨t,ht,(cubeFrameEquiv q).symm.toEmbedding.trans f,?_⟩
    intro p
    have he := cubeFrameEquiv_exposed q ((cubeFrameEquiv q).symm p)
    simp only [Equiv.apply_symm_apply] at he
    change FacesFit (cubes (f ((cubeFrameEquiv q).symm p))) t (rectExposed _ p)
    rw [he]
    exact hf _
  · rintro ⟨t,ht,f,hf⟩
    refine ⟨t,ht,(cubeFrameEquiv q).toEmbedding.trans f,?_⟩
    intro p
    exact (cubeFrameEquiv_exposed q p) ▸ hf (cubeFrameEquiv q p)

/-- Face interiors and internal positions also agree when the lengths are equal. -/
def cubeFillerEquiv (q : ℕ) : FillerSlot q ≃ RectFiller (fun _ => q) :=
  Equiv.sumCongr {
    toFun := fun p => ⟨p.1,p.2⟩
    invFun := fun p => (p.1,p.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl } (Equiv.refl _)

def cubeFullEquiv (q : ℕ) : FullSlot q ≃ RectFullSlot (fun _ => q) :=
  Equiv.sumCongr (cubeFrameEquiv q) (cubeFillerEquiv q)

lemma cubeFullEquiv_exposed (q : ℕ) (p : FullSlot q) :
    rectFullExposed (fun _ => q) (cubeFullEquiv q p) = fullExposed q p := by
  cases p with
  | inl p => exact cubeFrameEquiv_exposed q p
  | inr p => cases p <;> rfl

lemma full_iff_rect {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) :
    FullSolvable q cubes ↔ RectFullSolvable (fun _ => q) cubes := by
  constructor
  · rintro ⟨t,ht,f,hf⟩
    refine ⟨t,ht,(cubeFullEquiv q).symm.toEmbedding.trans f,?_⟩
    intro p
    have he := cubeFullEquiv_exposed q ((cubeFullEquiv q).symm p)
    simp only [Equiv.apply_symm_apply] at he
    change FacesFit (cubes (f ((cubeFullEquiv q).symm p))) t (rectFullExposed _ p)
    rw [he]
    exact hf _
  · rintro ⟨t,ht,f,hf⟩
    refine ⟨t,ht,(cubeFullEquiv q).toEmbedding.trans f,?_⟩
    intro p
    exact (cubeFullEquiv_exposed q p) ▸ hf (cubeFullEquiv q p)

lemma cube_lengths (n : ℕ) (axes : Equiv.Perm (Fin 3)) :
    (fun i => (![n-2,n-2,n-2] : Fin 3 → ℕ) (axes i)) = (fun _ => n-2) := by
  funext i
  generalize axes i = j
  fin_cases j <;> rfl

/-- Axis assignments have no effect when all side lengths coincide. -/
lemma frame_iff_box {m : ℕ} (n : ℕ) (cubes : Fin m → Cube) :
    FrameSolvable (n-2) cubes ↔ BoxFrameSolvable n n n cubes := by
  constructor
  · intro h
    refine ⟨Equiv.refl _,?_⟩
    rw [cube_lengths]
    exact (frame_iff_rect _ cubes).mp h
  · rintro ⟨axes,h⟩
    rw [cube_lengths] at h
    exact (frame_iff_rect _ cubes).mpr h

lemma full_iff_box {m : ℕ} (n : ℕ) (cubes : Fin m → Cube) :
    FullSolvable (n-2) cubes ↔ BoxSolvable n n n cubes := by
  constructor
  · intro h
    refine ⟨Equiv.refl _,?_⟩
    rw [cube_lengths]
    exact (full_iff_rect _ cubes).mp h
  · rintro ⟨axes,h⟩
    rw [cube_lengths] at h
    exact (full_iff_rect _ cubes).mpr h

end FiveColour.Physical
