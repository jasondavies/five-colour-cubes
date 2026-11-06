module
public import FiveColour.ClassificationData
public import FiveColour.ClassificationSymmetries
@[expose] public section
namespace FiveColour.Physical.Classification
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators
lemma terminal_orbit_counts (j : Fin 81) : ∀ a : Fin 75,
    (Finset.univ.filter (fun i => action (terminalSymmetry j) (terminalVariety j i) = a)).card =
    (Finset.univ.filter (fun i => representativeVariety (terminalClass j) i = a)).card := by
  fin_cases j <;> decide +kernel

def indexCode {n : ℕ} (v : Fin n → Fin 75) : ℕ := ∑ i, 16^(v i).val

lemma representative_code (j : Fin 56) :
    indexCode (representativeVariety j) = representativeCode j := by
  fin_cases j <;> decide +kernel

lemma orbit_code (j : Fin 56) : ∀ g : Fin 240,
    indexCode (fun i => action g (representativeVariety j i)) = orbitCode j g := by
  fin_cases j <;> decide +kernel

lemma orbit_separation (j : Fin 56) : ∀ (k : Fin 56) (g : Fin 240),
    orbitCode j g = representativeCode k → j = k := by
  fin_cases j <;> decide +kernel

end FiveColour.Physical.Classification
