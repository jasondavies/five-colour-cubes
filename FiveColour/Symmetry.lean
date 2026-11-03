module
public import FiveColour.Matching
@[expose] public section
namespace FiveColour.Physical

/-- Apply one permutation to the colours of the whole puzzle. -/
def recolour (p : Equiv.Perm (Fin 5)) (c : Cube) : Cube := fun f => p (c f)

@[simp] lemma recolour_symm (p : Equiv.Perm (Fin 5)) (c : Cube) :
    recolour p.symm (recolour p c) = c := by
  funext f
  simp [recolour]

@[simp] lemma recolour_apply_symm (p : Equiv.Perm (Fin 5)) (c : Cube) :
    recolour p (recolour p.symm c) = c := by
  funext f
  simp [recolour]

theorem usesAllColours_recolour (p : Equiv.Perm (Fin 5)) (c : Cube) :
    UsesAllColours (recolour p c) ↔ UsesAllColours c := by
  constructor
  · intro h a
    obtain ⟨f, hf⟩ := h (p a)
    exact ⟨f, p.injective hf⟩
  · intro h a
    obtain ⟨f, hf⟩ := h (p.symm a)
    exact ⟨f, by simp [recolour, hf]⟩

theorem fits_recolour (p : Equiv.Perm (Fin 5)) (c t : Cube) (k : Fin 8) :
    Fits (recolour p c) (recolour p t) k ↔ Fits c t k := by
  simp only [Fits, ColourCubes.TableFits, recolour, p.injective.eq_iff]

theorem solvesTarget_recolour {n : Nat} (p : Equiv.Perm (Fin 5))
    (cubes : Fin n → Cube) (t : Cube) :
    SolvesTarget (fun j => recolour p (cubes j)) (recolour p t) ↔ SolvesTarget cubes t := by
  simp only [SolvesTarget, fits_recolour]

/-- Global colour relabelling preserves physical solvability. -/
theorem hasSolution_recolour {n : Nat} (p : Equiv.Perm (Fin 5)) (cubes : Fin n → Cube) :
    HasSolution (fun j => recolour p (cubes j)) ↔ HasSolution cubes := by
  constructor
  · rintro ⟨t, ht, hs⟩
    refine ⟨recolour p.symm t, (usesAllColours_recolour _ _).mpr ht, ?_⟩
    apply (solvesTarget_recolour p cubes (recolour p.symm t)).mp
    simpa only [SolvesTarget, recolour_apply_symm] using hs
  · rintro ⟨t, ht, hs⟩
    exact ⟨recolour p t, (usesAllColours_recolour _ _).mpr ht,
      (solvesTarget_recolour p cubes t).mpr hs⟩

/-- Reflection across the yz-plane, matching the case generator's face swap. -/
def reflectFace : Fin 6 → Fin 6 := ![1,0,2,3,4,5]
def reflectSlot (k : Fin 8) : Fin 8 := k + 4

def reflectCube (c : Cube) : Cube := fun f => c (reflectFace f)

lemma reflectFace_involutive : ∀ f, reflectFace (reflectFace f) = f := by decide +kernel
lemma reflectSlot_involutive : ∀ k, reflectSlot (reflectSlot k) = k := by decide +kernel

/-- The corresponding permutation of the eight exterior corner positions. -/
def reflectionSlots : Equiv.Perm (Fin 8) where
  toFun := reflectSlot
  invFun := reflectSlot
  left_inv := reflectSlot_involutive
  right_inv := reflectSlot_involutive

@[simp] lemma reflectCube_involutive (c : Cube) : reflectCube (reflectCube c) = c := by
  funext f
  exact congrArg c (reflectFace_involutive f)

lemma reflect_exposed : ∀ (k : Fin 8) (f : Fin 3),
    reflectFace (ColourCubes.exposedFaces k f) = ColourCubes.exposedFaces (reflectSlot k) f := by
  decide +kernel

/-- Conjugation by reflection preserves the group of proper rotations. -/
lemma reflect_conjugation : ∀ r : Fin 24, ∃ s : Fin 24, ∀ f : Fin 6,
    reflectFace (ColourCubes.rotations r f) = ColourCubes.rotations s (reflectFace f) := by
  decide +kernel

theorem usesAllColours_reflect (c : Cube) : UsesAllColours (reflectCube c) ↔ UsesAllColours c := by
  constructor
  · intro h a
    obtain ⟨f, hf⟩ := h a
    exact ⟨reflectFace f, hf⟩
  · intro h a
    obtain ⟨f, hf⟩ := h a
    exact ⟨reflectFace f, by simpa only [reflectCube, reflectFace_involutive] using hf⟩

lemma fits_reflect_imp (c t : Cube) (k : Fin 8)
    (h : Fits (reflectCube c) (reflectCube t) k) : Fits c t (reflectSlot k) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨s, hs⟩ := reflect_conjugation r
  refine ⟨s, fun f => ?_⟩
  simpa only [reflectCube, hs, reflect_exposed] using hr f

/-- Reflecting both source and target permutes the target corners. -/
theorem fits_reflect (c t : Cube) (k : Fin 8) :
    Fits (reflectCube c) (reflectCube t) k ↔ Fits c t (reflectSlot k) := by
  constructor
  · exact fits_reflect_imp c t k
  · intro h
    have hh : Fits (reflectCube (reflectCube c)) (reflectCube (reflectCube t)) (reflectSlot k) := by
      simpa only [reflectCube_involutive] using h
    simpa only [reflectSlot_involutive] using fits_reflect_imp _ _ _ hh

theorem solvesTarget_reflect {n : Nat} (cubes : Fin n → Cube) (t : Cube) :
    SolvesTarget (fun j => reflectCube (cubes j)) (reflectCube t) ↔ SolvesTarget cubes t := by
  constructor
  · rintro ⟨copies, h⟩
    refine ⟨reflectionSlots.toEmbedding.trans copies, fun k => ?_⟩
    change Fits (cubes (copies (reflectSlot k))) t k
    have hk := (fits_reflect _ _ _).mp (h (reflectSlot k))
    simpa only [reflectSlot_involutive] using hk
  · rintro ⟨copies, h⟩
    refine ⟨reflectionSlots.toEmbedding.trans copies, fun k => ?_⟩
    exact (fits_reflect _ _ _).mpr (h (reflectSlot k))

/-- Global reflection transports a whole solution. It is not an allowed move
on a single physical copy. -/
theorem hasSolution_reflect {n : Nat} (cubes : Fin n → Cube) :
    HasSolution (fun j => reflectCube (cubes j)) ↔ HasSolution cubes := by
  constructor
  · rintro ⟨t, ht, hs⟩
    refine ⟨reflectCube t, (usesAllColours_reflect _).mpr ht, ?_⟩
    apply (solvesTarget_reflect cubes (reflectCube t)).mp
    simpa only [SolvesTarget, reflectCube_involutive] using hs
  · rintro ⟨t, ht, hs⟩
    exact ⟨reflectCube t, (usesAllColours_reflect _).mpr ht,
      (solvesTarget_reflect cubes t).mpr hs⟩

lemma recolour_rotate (p : Equiv.Perm (Fin 5)) (c : Cube) (r : Fin 24) :
    recolour p (rotate c r) = rotate (recolour p c) r := rfl

lemma reflect_rotate (c : Cube) (r : Fin 24) :
    ∃ s : Fin 24, reflectCube (rotate c r) = rotate (reflectCube c) s := by
  obtain ⟨s, hs⟩ := reflect_conjugation r
  refine ⟨s, funext fun f => ?_⟩
  change c (ColourCubes.rotations r (reflectFace f)) = c (reflectFace (ColourCubes.rotations s f))
  have he := congrArg reflectFace (hs (reflectFace f))
  simpa only [reflectFace_involutive] using congrArg c he

end FiveColour.Physical
