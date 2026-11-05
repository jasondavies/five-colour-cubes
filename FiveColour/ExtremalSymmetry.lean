module
public import FiveColour.ExtremalTripleData
@[expose] public section
namespace FiveColour.Physical

namespace PuzzleSymmetry
/-- Composition acts on the whole collection; it never changes the allowed cube moves. -/
def trans (s t : PuzzleSymmetry) : PuzzleSymmetry :=
  ⟨s.colour.trans t.colour, xor s.mirror t.mirror⟩

lemma trans_apply (s t : PuzzleSymmetry) (c : Cube) :
    (s.trans t).apply c = t.apply (s.apply c) := by
  cases s with
  | mk p b => cases t with
    | mk q d => cases b <;> cases d <;> funext f <;>
        simp [trans, apply, recolour, reflectCube, reflectFace_involutive]
end PuzzleSymmetry

/-- Same inventory of proper-rotation varieties, with physical copies counted. -/
def SameInventory {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube) : Prop :=
  ∀ i, multiplicity a i = multiplicity b i

/-- Common colour relabelling and simultaneous reflection of the entire collection. -/
def SymmetryEquivalent {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube) : Prop :=
  ∃ s : PuzzleSymmetry, SameInventory (fun i => s.apply (a i)) b

lemma sameInventory_apply {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube)
    (ha : ∀ i, UsesAllColours (a i)) (hb : ∀ i, UsesAllColours (b i))
    (h : SameInventory a b) (s : PuzzleSymmetry) :
    SameInventory (fun i => s.apply (a i)) (fun i => s.apply (b i)) := by
  intro i
  obtain ⟨j,rfl⟩ := (varietyEquiv s).surjective i
  rw [multiplicity_apply s a ha, multiplicity_apply s b hb]
  exact h j

lemma symmetryEquivalent_trans {l m n : ℕ} (a : Fin l → Cube) (b : Fin m → Cube)
    (c : Fin n → Cube) (ha : ∀ i, UsesAllColours (a i)) (hb : ∀ i, UsesAllColours (b i))
    (hab : SymmetryEquivalent a b) (hbc : SymmetryEquivalent b c) :
    SymmetryEquivalent a c := by
  obtain ⟨s,hs⟩ := hab
  obtain ⟨t,ht⟩ := hbc
  refine ⟨s.trans t, ?_⟩
  have hst := sameInventory_apply _ b (fun i => (s.usesAllColours_apply _).mpr (ha i)) hb hs t
  intro i
  simpa only [PuzzleSymmetry.trans_apply] using (hst i).trans (ht i)

lemma symmetryEquivalent_symm {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube)
    (ha : ∀ i, UsesAllColours (a i)) (hb : ∀ i, UsesAllColours (b i))
    (h : SymmetryEquivalent a b) : SymmetryEquivalent b a := by
  obtain ⟨s,hs⟩ := h
  have ht := sameInventory_apply _ b (fun i => (s.usesAllColours_apply _).mpr (ha i)) hb hs s.inverse
  exact ⟨s.inverse, fun i => by simpa only [PuzzleSymmetry.inverse_apply] using (ht i).symm⟩

lemma symmetryEquivalent_hasSolution {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube)
    (ha : ∀ i, UsesAllColours (a i)) (hb : ∀ i, UsesAllColours (b i))
    (h : SymmetryEquivalent a b) : HasSolution a ↔ HasSolution b := by
  have forward {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube)
      (ha : ∀ i, UsesAllColours (a i)) (hb : ∀ i, UsesAllColours (b i))
      (h : SymmetryEquivalent a b) (hsol : HasSolution a) : HasSolution b := by
    obtain ⟨s,hs⟩ := h
    exact hasSolution_of_multiplicity_le _ b
      (fun i => (s.usesAllColours_apply _).mpr (ha i)) hb (fun i => (hs i).le)
      ((s.hasSolution_apply a).mpr hsol)
  exact ⟨forward a b ha hb h, forward b a hb ha (symmetryEquivalent_symm a b ha hb h)⟩

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
