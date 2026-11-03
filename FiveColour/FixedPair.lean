module
public import FiveColour.RingEleven
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Assign each physical cube lacking a fixed pair to one of its nine varieties. -/
lemma fixed_pair_types {I : Type*} (cubes : I → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (p : Fin 10) (hp : ∀ i, ¬ HasPair (cubes i) p) :
    ∃ typeOf : I → Fin 9, ∀ i, Ring.variety p (typeOf i) = catalogueIndex (cubes i) := by
  classical
  have h (i) : ∃ s, Ring.variety p s = catalogueIndex (cubes i) :=
    Ring.family_complete p _ (by simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using hp i)
  exact ⟨fun i => Classical.choose (h i),fun i => Classical.choose_spec (h i)⟩

lemma fixed_pair_corners {I : Type*} [Fintype I] [DecidableEq I]
    (cubes : I → Cube) (hc : ∀ i, UsesAllColours (cubes i)) (hI : Fintype.card I = 11)
    (p : Fin 10) (hp : ∀ i, ¬ HasPair (cubes i) p) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : Fin 8 ↪ I, ∀ k, Fits (cubes (f k)) (catalogue t) k := by
  classical
  obtain ⟨typeOf,htype⟩ := fixed_pair_types cubes hc p hp
  obtain ⟨t,f,hf⟩ := Ring.eleven_corners typeOf hI
  let e : Fin 8 ↪ Ring.Positions false t :=
    ⟨fun k => ⟨k.castSucc,Or.inl k.isLt⟩,fun a b he => Fin.ext (congrArg (fun z => z.val.val) he)⟩
  let g := (Ring.cornerEquiv p t).symm.toEmbedding.trans (e.trans f)
  refine ⟨Ring.variety p t,Ring.family_missing p t,g,?_⟩
  intro k
  apply (fits_catalogueIndex _ (hc _) _ _).mpr
  rw [← htype]
  have hfit := (Ring.corner_fits p t (typeOf (g k)) ((Ring.cornerEquiv p t).symm k)).mpr
    (hf (e ((Ring.cornerEquiv p t).symm k)))
  have he : Ring.cornerMap p t ((Ring.cornerEquiv p t).symm k) = k :=
    (Ring.cornerEquiv p t).apply_symm_apply k
  simpa only [he] using hfit

lemma fixed_pair_core {I : Type*} [Fintype I] [DecidableEq I]
    (cubes : I → Cube) (hc : ∀ i, UsesAllColours (cubes i)) (hI : Fintype.card I = 11)
    (p : Fin 10) (hp : ∀ i, ¬ HasPair (cubes i) p)
    (ho : ∃ i, OppositeRepeat (catalogue (catalogueIndex (cubes i)))) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : {pos : FrameSlot 1 // CorePosition (catalogue t) pos} ↪ I,
        ∀ pos, FrameFits (cubes (f pos)) (catalogue t) pos.val := by
  classical
  obtain ⟨typeOf,htype⟩ := fixed_pair_types cubes hc p hp
  have hO : ∃ i, (typeOf i).val < 3 := by
    obtain ⟨i,hi⟩ := ho
    exact ⟨i,(Ring.opposite_iff p _).mp (by simpa only [htype] using hi)⟩
  obtain ⟨t,f,hf⟩ := Ring.eleven_core typeOf hI hO
  let g := (Ring.coreEquiv p t).symm.toEmbedding.trans f
  refine ⟨Ring.variety p t,Ring.family_missing p t,g,?_⟩
  intro pos
  apply (frameFits_catalogueIndex _ _ (hc _) _).mpr
  rw [← htype]
  have hfit := (Ring.slot_fits p t (typeOf (g pos))
    ((Ring.coreEquiv p t).symm pos).val ((Ring.coreEquiv p t).symm pos).property).mpr
    (hf ((Ring.coreEquiv p t).symm pos))
  have he : Ring.slot p t ((Ring.coreEquiv p t).symm pos).val = pos.val :=
    congrArg Subtype.val ((Ring.coreEquiv p t).apply_symm_apply pos)
  simpa only [he] using hfit

lemma fixed_pair_extra {I : Type*} [Fintype I] [DecidableEq I]
    (cubes : I → Cube) (hc : ∀ i, UsesAllColours (cubes i)) (hI : Fintype.card I = 11)
    (p : Fin 10) (hp : ∀ i, ¬ HasPair (cubes i) p) (w : Cube) (hw : UsesAllColours w) :
    ∃ t : Fin 75, ¬ HasPair (catalogue t) p ∧
      ∃ f : {pos : FrameSlot 1 // CorePosition (catalogue t) pos} ↪ Option I,
        ∀ pos, FrameFits (Option.elim (f pos) w cubes) (catalogue t) pos.val := by
  classical
  obtain ⟨typeOf,htype⟩ := fixed_pair_types cubes hc p hp
  obtain ⟨t,f,hf⟩ := Ring.eleven_extra typeOf hI p (catalogueIndex w)
  let g := (Ring.coreEquiv p t).symm.toEmbedding.trans f
  refine ⟨Ring.variety p t,Ring.family_missing p t,g,?_⟩
  intro pos
  let k := (Ring.coreEquiv p t).symm pos
  have he : Ring.slot p t k.val = pos.val := congrArg Subtype.val ((Ring.coreEquiv p t).apply_symm_apply pos)
  have hfit := hf k
  change FrameFits (Option.elim (f k) w cubes) _ _
  cases hfk : f k with
  | none =>
    simp only [hfk] at hfit
    apply (frameFits_catalogueIndex _ _ hw _).mpr
    simpa only [he] using (Ring.extraFits_correct p t (catalogueIndex w) k.val).mp hfit
  | some i =>
    simp only [hfk] at hfit
    apply (frameFits_catalogueIndex _ _ (hc i) _).mpr
    rw [← htype]
    simpa only [he] using (Ring.slot_fits p t (typeOf i) k.val k.property).mpr hfit

end FiveColour.Physical
