module
public import FiveColour.SymmetryAction
@[expose] public section
namespace FiveColour.Physical

/-- Multiplicity comparison transports solutions without identifying physical copies. -/
theorem hasSolution_of_multiplicity_le {m n : ℕ} (small : Fin m → Cube)
    (large : Fin n → Cube) (hs : ∀ i, UsesAllColours (small i))
    (hl : ∀ i, UsesAllColours (large i))
    (hcount : ∀ a, multiplicity small a ≤ multiplicity large a)
    (hsol : HasSolution small) : HasSolution large := by
  by_contra hno
  obtain ⟨t, ht⟩ := (hasSolution_iff_catalogue small).mp hsol
  obtain ⟨K, _, hK⟩ := (counterexample_iff_deficient_mass large hl).mp hno t
  have hm : Certificate.mass (multiplicityVector small) (varietyNeighbours t K) ≤
      Certificate.mass (multiplicityVector large) (varietyNeighbours t K) :=
    Finset.sum_le_sum fun i _ => by
      change (multiplicity small i : Int) ≤ multiplicity large i
      exact_mod_cast hcount i
  rw [mass_varietyNeighbours small hs] at hm
  have hh := (solvesTarget_iff_hall small (catalogue t)).mp ht K
  omega


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

lemma inventory_equivalent {m n : ℕ} (a : Fin m → Cube) (b : Fin n → Cube)
    (h : SameInventory a b) : SymmetryEquivalent a b :=
  ⟨⟨Equiv.refl _,false⟩, h⟩

end FiveColour.Physical
