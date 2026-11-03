module
public import FiveColour.RareFrames
@[expose] public section
namespace FiveColour.Physical

def missingPairCopies {m : ℕ} (cubes : Fin m → Cube) (p : Fin 10) :=
  Finset.univ \ pairCopies cubes p
lemma mem_missingPairCopies {m : ℕ} (cubes : Fin m → Cube) (p : Fin 10) (i : Fin m) :
    i ∈ missingPairCopies cubes p ↔ ¬ HasPair (cubes i) p := by
  simp [missingPairCopies,pairCopies]
lemma missingPairCopies_card {m : ℕ} (cubes : Fin m → Cube) (p : Fin 10) :
    (missingPairCopies cubes p).card = m - (pairCopies cubes p).card := by
  simp [missingPairCopies,Finset.card_sdiff]

end FiveColour.Physical
