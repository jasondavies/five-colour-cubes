module
public import FiveColour.BoxAxes
public import FiveColour.NormalisationData
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000

/-- A proper rotation permutes geometric edges and their parallel axes. -/
def rotatedEdge (r : Fin 24) (e : Fin 12) : Fin 12 :=
  ((List.finRange 12).find? fun d => decide (
    (edgeFaces d 0 = ColourCubes.rotations r (edgeFaces e 0) ∧
      edgeFaces d 1 = ColourCubes.rotations r (edgeFaces e 1)) ∨
    (edgeFaces d 0 = ColourCubes.rotations r (edgeFaces e 1) ∧
      edgeFaces d 1 = ColourCubes.rotations r (edgeFaces e 0)))).getD 0

def rotatedAxis (r : Fin 24) (a : Fin 3) : Fin 3 :=
  ⟨(ColourCubes.rotations r ⟨2*a.val,by omega⟩).val / 2, by omega⟩

lemma rotatedEdge_bijective : ∀ r, Function.Bijective (rotatedEdge r) := by decide +kernel
lemma rotatedAxis_bijective : ∀ r, Function.Bijective (rotatedAxis r) := by decide +kernel

noncomputable def edgeEquiv (r : Fin 24) : Equiv.Perm (Fin 12) := Equiv.ofBijective _ (rotatedEdge_bijective r)
noncomputable def axisEquiv (r : Fin 24) : Equiv.Perm (Fin 3) := Equiv.ofBijective _ (rotatedAxis_bijective r)

lemma rotatedEdge_axis : ∀ r e, edgeAxis (edgeEquiv r e) = axisEquiv r (edgeAxis e) := by decide +kernel
lemma rotatedEdge_faces : ∀ r e,
    (edgeFaces (edgeEquiv r e) 0 = ColourCubes.rotations r (edgeFaces e 0) ∧
      edgeFaces (edgeEquiv r e) 1 = ColourCubes.rotations r (edgeFaces e 1)) ∨
    (edgeFaces (edgeEquiv r e) 0 = ColourCubes.rotations r (edgeFaces e 1) ∧
      edgeFaces (edgeEquiv r e) 1 = ColourCubes.rotations r (edgeFaces e 0)) := by decide +kernel

lemma hasEdge_recolour (p : Equiv.Perm (Fin 5)) (c : Cube) (a b : Fin 5) :
    HasEdge (recolour p c) (p a) (p b) ↔ HasEdge c a b := by
  simp only [HasEdge,recolour,p.injective.eq_iff]

lemma edge_fits_rotate_target (c t : Cube) (r : Fin 24) (e : Fin 12) :
    HasEdge c ((rotate t r) (edgeFaces e 0)) ((rotate t r) (edgeFaces e 1)) ↔
      HasEdge c (t (edgeFaces (edgeEquiv r e) 0)) (t (edgeFaces (edgeEquiv r e) 1)) := by
  rcases rotatedEdge_faces r e with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simp only [h0,h1,rotate,ColourCubes.rotate]
  · simp only [h0,h1,rotate,ColourCubes.rotate]
    exact ⟨hasEdge_symm,hasEdge_symm⟩

lemma missingCorners_rotate_target (c t : Cube) (r : Fin 24) :
    missingCorners c (rotate t r) = missingCorners c t := by
  classical
  apply Finset.card_bij (fun k _ => ColourCubes.Geometry.slotEquiv r k)
  · intro k hk
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,fits_rotate_target] using hk
  · intro a _ b _ he
    exact (ColourCubes.Geometry.slotEquiv r).injective he
  · intro k hk
    refine ⟨(ColourCubes.Geometry.slotEquiv r).symm k,?_,by simp⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,fits_rotate_target,Equiv.apply_symm_apply] using hk

lemma missingAlong_rotate_target (c t : Cube) (r : Fin 24) (a : Fin 3) :
    missingAlong c (rotate t r) a = missingAlong c t (axisEquiv r a) := by
  classical
  apply Finset.card_bij (fun e _ => edgeEquiv r e)
  · intro e he
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,rotatedEdge_axis,
      (axisEquiv r).injective.eq_iff,edge_fits_rotate_target] using he
  · intro e _ f _ h; exact (edgeEquiv r).injective h
  · intro e he
    refine ⟨(edgeEquiv r).symm e,?_,by simp⟩
    have h := rotatedEdge_axis r ((edgeEquiv r).symm e)
    simp only [Equiv.apply_symm_apply] at h
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
    refine ⟨(axisEquiv r).injective (h.symm.trans he.1), ?_⟩
    simpa only [edge_fits_rotate_target,Equiv.apply_symm_apply] using he.2

lemma bichromaticAxis_rotate (t : Cube) (r : Fin 24) (a : Fin 3) :
    BichromaticAxis (rotate t r) a ↔ BichromaticAxis t (axisEquiv r a) := by
  have h (e : Fin 12) :
      (rotate t r) (edgeFaces e 0) ≠ (rotate t r) (edgeFaces e 1) ↔
      t (edgeFaces (edgeEquiv r e) 0) ≠ t (edgeFaces (edgeEquiv r e) 1) := by
    rcases rotatedEdge_faces r e with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · simp only [h0,h1,rotate,ColourCubes.rotate]
    · simp only [h0,h1,rotate,ColourCubes.rotate,ne_comm]
  constructor
  · intro ht e he
    obtain ⟨e,rfl⟩ := (edgeEquiv r).surjective e
    exact (h e).mp (ht e ((axisEquiv r).injective ((rotatedEdge_axis r e).symm.trans he)))
  · intro ht e he
    exact (h e).mpr (ht _ ((rotatedEdge_axis r e).trans (congrArg (axisEquiv r) he)))

lemma missingCorners_recolour (p : Equiv.Perm (Fin 5)) (c t : Cube) :
    missingCorners (recolour p c) (recolour p t) = missingCorners c t := by
  unfold missingCorners
  simp only [fits_recolour]
lemma missingAlong_recolour (p : Equiv.Perm (Fin 5)) (c t : Cube) (a : Fin 3) :
    missingAlong (recolour p c) (recolour p t) a = missingAlong c t a := by
  unfold missingAlong
  simp only [recolour,hasEdge_recolour]
lemma bichromaticAxis_recolour (p : Equiv.Perm (Fin 5)) (t : Cube) (a : Fin 3) :
    BichromaticAxis (recolour p t) a ↔ BichromaticAxis t a := by
  simp only [BichromaticAxis,recolour,ne_eq,p.injective.eq_iff]

lemma missingCorners_source_index (c t : Cube) (hc : UsesAllColours c) :
    missingCorners c t = missingCorners (catalogue (catalogueIndex c)) t := by
  unfold missingCorners
  simp only [fits_catalogueIndex c hc]
lemma missingAlong_source_index (c t : Cube) (hc : UsesAllColours c) (a : Fin 3) :
    missingAlong c t a = missingAlong (catalogue (catalogueIndex c)) t a := by
  unfold missingAlong
  simp only [hasEdge_catalogueIndex c hc]

lemma normalisation_cube (t : Fin 75) :
    recolour (normalisingColour t) (catalogue t) =
      rotate (catalogue (anchorFor t)) (normalisationRotation t) :=
  funext (normalisation_faces t)

/-- Normalising the target leaves just the two repeated-face types to check. -/
def normalisedSource (s t : Fin 75) : Fin 75 :=
  catalogueIndex (recolour (normalisingColour t) (catalogue s))

lemma normalised_corners (s t : Fin 75) :
    missingCorners (catalogue s) (catalogue t) =
      missingCorners (catalogue (normalisedSource s t)) (catalogue (anchorFor t)) := by
  rw [← missingCorners_recolour (normalisingColour t)]
  rw [normalisation_cube t]
  rw [missingCorners_rotate_target,missingCorners_source_index _ _
    ((usesAllColours_recolour _ _).mpr (catalogue_uses_all_colours s))]
  rfl

lemma normalised_along (s t : Fin 75) (a : Fin 3) :
    missingAlong (catalogue s) (catalogue t) a =
      missingAlong (catalogue (normalisedSource s t)) (catalogue (anchorFor t))
        (axisEquiv (normalisationRotation t) a) := by
  rw [← missingAlong_recolour (normalisingColour t)]
  rw [normalisation_cube t]
  rw [missingAlong_rotate_target,missingAlong_source_index _ _
    ((usesAllColours_recolour _ _).mpr (catalogue_uses_all_colours s))]
  rfl

lemma normalised_bichromatic (t : Fin 75) (a : Fin 3) :
    BichromaticAxis (catalogue t) a ↔
      BichromaticAxis (catalogue (anchorFor t)) (axisEquiv (normalisationRotation t) a) := by
  rw [← bichromaticAxis_recolour (normalisingColour t)]
  rw [normalisation_cube t]
  exact bichromaticAxis_rotate _ _ _

lemma normalisedSource_injective (t : Fin 75) : Function.Injective (fun s => normalisedSource s t) :=
  (varietyEquiv ⟨normalisingColour t,false⟩).injective

lemma normalised_source_kind (s t : Fin 75) :
    OppositeRepeat (catalogue (normalisedSource s t)) ↔ OppositeRepeat (catalogue s) :=
  oppositeRepeat_varietyEquiv ⟨normalisingColour t,false⟩ s

lemma normalised_target_kind (t : Fin 75) :
    OppositeRepeat (catalogue (anchorFor t)) ↔ OppositeRepeat (catalogue t) := by
  have h := oppositeRepeat_recolour (normalisingColour t) (catalogue t)
  rw [normalisation_cube t,
    oppositeRepeat_rotate] at h
  exact h

lemma normalised_corner_fits (s t : Fin 75) (k : Fin 8) :
    Fits (catalogue s) (catalogue t) k ↔
      Fits (catalogue (normalisedSource s t)) (catalogue (anchorFor t))
        (ColourCubes.Geometry.slotEquiv (normalisationRotation t) k) := by
  rw [← fits_recolour (normalisingColour t)]
  rw [normalisation_cube t,
    fits_rotate_target,fits_catalogueIndex _
      ((usesAllColours_recolour _ _).mpr (catalogue_uses_all_colours s))]
  rfl

lemma normalised_edge_fits (s t : Fin 75) (e : Fin 12) :
    HasEdge (catalogue s) (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)) ↔
      HasEdge (catalogue (normalisedSource s t))
        (catalogue (anchorFor t) (edgeFaces (edgeEquiv (normalisationRotation t) e) 0))
        (catalogue (anchorFor t) (edgeFaces (edgeEquiv (normalisationRotation t) e) 1)) := by
  rw [← hasEdge_recolour (normalisingColour t)]
  change HasEdge (recolour (normalisingColour t) (catalogue s))
    ((recolour (normalisingColour t) (catalogue t)) (edgeFaces e 0))
    ((recolour (normalisingColour t) (catalogue t)) (edgeFaces e 1)) ↔ _
  rw [normalisation_cube t,
    edge_fits_rotate_target,hasEdge_catalogueIndex _
      ((usesAllColours_recolour _ _).mpr (catalogue_uses_all_colours s))]
  rfl

end FiveColour.Physical
