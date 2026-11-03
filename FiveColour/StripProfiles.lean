module
public import FiveColour.RodSymmetry
@[expose] public section
namespace FiveColour.Physical.Strip
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cornerMissing (s t : Fin 75) (k : Fin 8) : Prop := (Replay.fits t s).testBit k.val = false
instance (s t : Fin 75) : DecidablePred (cornerMissing s t) := by intro k; unfold cornerMissing; infer_instance
def edgeMissing (s t : Fin 75) (e : Fin 12) : Prop :=
  (edgeBits s).testBit (5*(catalogue t (edgeFaces e 0)).val+(catalogue t (edgeFaces e 1)).val) = false
instance (s t : Fin 75) : DecidablePred (edgeMissing s t) := by intro e; unfold edgeMissing; infer_instance

def Maximal (s t : Fin 75) (a b : Fin 3) : Prop :=
  OppositeRepeat (catalogue s) ∧ cornerMissBits s t = 6 ∧ alongBits s t a = 1 ∧ alongBits s t b = 2
instance (s t : Fin 75) (a b : Fin 3) : Decidable (Maximal s t a b) := by unfold Maximal; infer_instance

lemma adjacent_canonical (s : Fin 75) : ¬ OppositeRepeat (catalogue s) → ∀ t, t = 0 ∨ t = 3 → ∀ a b,
    a ≠ b → BichromaticAxis (catalogue t) a → BichromaticAxis (catalogue t) b →
      cornerMissBits s t + alongBits s t a + 2*alongBits s t b ≤ 10 := by
  fin_cases s <;> decide +kernel

/-- Equality in the strip defect bound determines the source from its
missing positions. This checks only individual cube incidence profiles. -/
lemma maximal_witness_canonical (t : Fin 75) : t = 0 ∨ t = 3 → ∀ a b, a ≠ b →
    BichromaticAxis (catalogue t) a → BichromaticAxis (catalogue t) b →
    ∀ s, Maximal s t a b → ∀ u, Maximal u t a b → s ≠ u →
      (∃ k, cornerMissing s t k ∧ ¬ cornerMissing u t k) ∨
      (∃ e, (edgeAxis e = a ∨ edgeAxis e = b) ∧ edgeMissing s t e ∧ ¬ edgeMissing u t e) := by
  fin_cases t <;> decide +kernel

/-- Put the repeated axis of an opposite-repeat target along the length-two
side; the other two directions then have the improved bound. -/
lemma opposite_short_canonical (s : Fin 75) : ∀ t, t = 0 ∨ t = 3 → ∀ (z a b : Fin 3),
    a ≠ b → a ≠ z → b ≠ z → Axial (catalogue t) z →
      cornerMissBits s t + alongBits s t a + 2*alongBits s t b ≤ 10 := by
  fin_cases s <;> decide +kernel

lemma normalised_cornerMissing (s t : Fin 75) (k : Fin 8) :
    cornerMissing s t k ↔ cornerMissing (normalisedSource s t) (anchorFor t)
      (ColourCubes.Geometry.slotEquiv (normalisationRotation t) k) := by
  simpa only [cornerMissing,Bool.eq_false_iff,ne_eq,incidence_fits] using
    not_congr (normalised_corner_fits s t k)

lemma normalised_edgeMissing (s t : Fin 75) (e : Fin 12) :
    edgeMissing s t e ↔ edgeMissing (normalisedSource s t) (anchorFor t)
      (edgeEquiv (normalisationRotation t) e) := by
  simpa only [edgeMissing,Bool.eq_false_iff,ne_eq,edgeBits_correct] using
    not_congr (normalised_edge_fits s t e)

lemma normalised_maximal (s t : Fin 75) (a b : Fin 3) :
    Maximal s t a b ↔ Maximal (normalisedSource s t) (anchorFor t)
      (axisEquiv (normalisationRotation t) a) (axisEquiv (normalisationRotation t) b) := by
  simp only [Maximal,normalised_source_kind s t,normalised_corner_bits s t,normalised_along_bits s t]

lemma adjacent_bits (s : Fin 75) : ¬ OppositeRepeat (catalogue s) → ∀ t a b,
    a ≠ b → BichromaticAxis (catalogue t) a → BichromaticAxis (catalogue t) b →
      cornerMissBits s t + alongBits s t a + 2*alongBits s t b ≤ 10 := by
  intro hs t a b hab ha hb
  simpa only [normalised_corner_bits s t,normalised_along_bits s t] using
    adjacent_canonical (normalisedSource s t) (fun h => hs ((normalised_source_kind s t).mp h))
      (anchorFor t) (anchorFor_cases t) _ _ ((axisEquiv (normalisationRotation t)).injective.ne hab)
      ((normalised_bichromatic t a).mp ha) ((normalised_bichromatic t b).mp hb)

lemma opposite_short_bits (s : Fin 75) : ∀ t (z a b : Fin 3),
    a ≠ b → a ≠ z → b ≠ z → Axial (catalogue t) z →
      cornerMissBits s t + alongBits s t a + 2*alongBits s t b ≤ 10 := by
  intro t z a b hab haz hbz hz
  simpa only [normalised_corner_bits s t,normalised_along_bits s t] using
    opposite_short_canonical (normalisedSource s t) (anchorFor t) (anchorFor_cases t) _ _ _
      ((axisEquiv (normalisationRotation t)).injective.ne hab)
      ((axisEquiv (normalisationRotation t)).injective.ne haz)
      ((axisEquiv (normalisationRotation t)).injective.ne hbz) ((normalised_axial t z).mp hz)

/-- The small canonical check is transported through bijections of sources,
corners and edges, preserving an actual distinguishing position. -/
lemma maximal_witness_bits (t : Fin 75) : ∀ a b, a ≠ b →
    BichromaticAxis (catalogue t) a → BichromaticAxis (catalogue t) b →
    ∀ s, Maximal s t a b → ∀ u, Maximal u t a b → s ≠ u →
      (∃ k, cornerMissing s t k ∧ ¬ cornerMissing u t k) ∨
      (∃ e, (edgeAxis e = a ∨ edgeAxis e = b) ∧ edgeMissing s t e ∧ ¬ edgeMissing u t e) := by
  intro a b hab ha hb s hs u hu hsu
  have h := maximal_witness_canonical (anchorFor t) (anchorFor_cases t) _ _
    ((axisEquiv (normalisationRotation t)).injective.ne hab)
    ((normalised_bichromatic t a).mp ha) ((normalised_bichromatic t b).mp hb)
    (normalisedSource s t) ((normalised_maximal s t a b).mp hs)
    (normalisedSource u t) ((normalised_maximal u t a b).mp hu)
    ((normalisedSource_injective t).ne hsu)
  rcases h with ⟨k,hk,huk⟩ | ⟨e,he,hse,hue⟩
  · left
    refine ⟨(ColourCubes.Geometry.slotEquiv (normalisationRotation t)).symm k,?_,?_⟩
    · simpa only [normalised_cornerMissing s t,Equiv.apply_symm_apply] using hk
    · simpa only [normalised_cornerMissing u t,Equiv.apply_symm_apply] using huk
  · right
    refine ⟨(edgeEquiv (normalisationRotation t)).symm e,?_,?_,?_⟩
    · have he' := rotatedEdge_axis (normalisationRotation t) ((edgeEquiv (normalisationRotation t)).symm e)
      simp only [Equiv.apply_symm_apply] at he'
      rcases he with he | he
      · exact Or.inl ((axisEquiv (normalisationRotation t)).injective (he'.symm.trans he))
      · exact Or.inr ((axisEquiv (normalisationRotation t)).injective (he'.symm.trans he))
    · simpa only [normalised_edgeMissing s t,Equiv.apply_symm_apply] using hse
    · simpa only [normalised_edgeMissing u t,Equiv.apply_symm_apply] using hue

end FiveColour.Physical.Strip
