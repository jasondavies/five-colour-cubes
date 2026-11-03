module
public import FiveColour.CatalogueChecks
@[expose] public section
namespace FiveColour.Physical

def encodeTriple (a b c : Fin 5) : Fin 125 :=
  ⟨a.val + 5 * b.val + 25 * c.val, by omega⟩

/-- Every face assignment has a base-five address; this does not assume all colours occur. -/
lemma rawCube_complete (c : Cube) : ∃ b k, rawCube b k = c := by
  refine ⟨encodeTriple (c 3) (c 4) (c 5), encodeTriple (c 0) (c 1) (c 2), ?_⟩
  funext f
  apply Fin.ext
  fin_cases f <;> simp [rawCube, encodeTriple] <;> omega

/-- Every cube using all five fixed colours is a proper rotation of a catalogue entry. -/
theorem catalogue_complete (c : Cube) (hc : UsesAllColours c) :
    ∃ i : Fin 75, ∃ r : Fin 24, ∀ f, c f = catalogue i (ColourCubes.rotations r f) := by
  obtain ⟨b, k, rfl⟩ := rawCube_complete c
  exact ⟨(rawWitness b k).1, (rawWitness b k).2, raw_checks b k hc⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem catalogue_uses_all_colours : ∀ i, UsesAllColours (catalogue i) := by
  unfold UsesAllColours
  decide +kernel

/-- Read the representative index certified by the raw catalogue. -/
def catalogueIndex (c : Cube) : Fin 75 :=
  (rawWitness (encodeTriple (c 3) (c 4) (c 5)) (encodeTriple (c 0) (c 1) (c 2))).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma catalogue_index_rotations (i : Fin 75) : ∀ r : Fin 24,
    catalogueIndex (fun f => catalogue i (ColourCubes.rotations r f)) = i := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma catalogue_index_faces : ∀ i, catalogueIndex (catalogue i) = i := by
  decide +kernel

/-- No two catalogue entries are related by a proper rotation. -/
theorem catalogue_unique (i j : Fin 75) (r : Fin 24)
    (h : ∀ f, catalogue i (ColourCubes.rotations r f) = catalogue j f) : i = j := by
  have hi := catalogue_index_rotations i r
  rw [funext h, catalogue_index_faces] at hi
  exact hi.symm

end FiveColour.Physical
