module
public import FiveColour.ClassificationData
public import FiveColour.HallCuts
@[expose] public section
namespace FiveColour.Physical.Classification
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma terminal_counts (j : Fin 81) : ∀ a : Fin 75,
    Packed.values (terminalPacked j) a = (Finset.univ.filter (fun i => terminalVariety j i = a)).card := by
  fin_cases j <;> decide +kernel

def indexedNeighbours {n : ℕ} (v : Fin n → Fin 75) (t : Fin 75) (d : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (Replay.fits t (v i)).land d ≠ 0)

lemma deficits (j : Fin 56) : ∀ t : Fin 75,
    hallDeficit j t < 256 ∧
      (indexedNeighbours (representativeVariety j) t (hallDeficit j t)).card <
        (cornerSet (hallDeficit j t)).card := by
  fin_cases j <;> decide +kernel

end FiveColour.Physical.Classification
