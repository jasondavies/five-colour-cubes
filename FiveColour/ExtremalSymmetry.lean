module
public import FiveColour.ExtremalTriples
public import FiveColour.StabiliserData
public import FiveColour.Inventory
@[expose] public section
namespace FiveColour.Physical

lemma triple_inventory_apply (a b c : Fin 75) (s : PuzzleSymmetry) :
    SameInventory (fun i => s.apply (tripleFamily a b c i))
      (tripleFamily (varietyEquiv s a) (varietyEquiv s b) (varietyEquiv s c)) := by
  intro j
  unfold multiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    catalogueIndex_apply s _ (triple_uses_all a b c i)]
  simp only [tripleFamily, catalogue_index_faces, tripleVariety]
  split_ifs <;> rfl

/-- Completeness of the sixteen symmetries fixing the four-copy opposite variety.
The test concerns only the six physical faces of that one variety. -/
def FixesOppositeFaces (p : Fin 5 → Fin 5) (mirror : Bool) : Prop :=
  ∃ r : Fin 24, ∀ f : Fin 6,
    p ((if mirror then reflectCube (catalogue 0) else catalogue 0) f) =
      catalogue 0 (ColourCubes.rotations r f)

instance (p : Fin 5 → Fin 5) (b : Bool) : Decidable (FixesOppositeFaces p b) := by
  unfold FixesOppositeFaces
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma opposite_stabiliser_complete_check : ∀ (p : Fin 5 → Fin 5) (b : Bool),
    Function.Injective p → FixesOppositeFaces p b →
      ∃ g : Fin 16, stabiliserColour g = p ∧ stabiliserMirror g = b := by decide +kernel

lemma opposite_stabiliser_complete (s : PuzzleSymmetry)
    (h : varietyEquiv s 0 = 0) : ∃ g : Fin 16, stabiliserSymmetry g = s := by
  obtain ⟨r,hr⟩ := catalogueIndex_spec (s.apply (catalogue 0))
    ((s.usesAllColours_apply _).mpr (catalogue_uses_all_colours 0))
  change catalogueIndex (s.apply (catalogue 0)) = 0 at h
  rw [h] at hr
  have hf : FixesOppositeFaces s.colour s.mirror := ⟨r, congrFun hr⟩
  obtain ⟨g,hg,hb⟩ := opposite_stabiliser_complete_check s.colour s.mirror s.colour.injective hf
  refine ⟨g, ?_⟩
  have he : (stabiliserSymmetry g).colour = s.colour := Equiv.ext (congrFun hg)
  have hm : (stabiliserSymmetry g).mirror = s.mirror := hb
  cases s with
  | mk p b =>
    cases hs : stabiliserSymmetry g with
    | mk q d =>
      rw [hs] at he hm
      exact congrArg₂ PuzzleSymmetry.mk he hm

end FiveColour.Physical
