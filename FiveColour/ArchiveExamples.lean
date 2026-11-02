module
public import FiveColour.ArchiveBridge
public import FiveColour.PackedCase79
public import FiveColour.PackedCase165
public import FiveColour.PackedCase207
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed.Archive
open Physical

def selectedCases : Fin 3 → Fin 357 := ![79,165,207]

/-- The existing concrete certificates have exactly the archived headers and
constraint families used by the new bridge. These are actual exclusion proofs. -/
theorem selected_exclusions (i : Fin 3) :
    Chunks.Excludes 15 (families (selectedCases i)) (root (selectedCases i)) := by
  fin_cases i
  · exact Replay79.excludes
  · exact Replay165.excludes
  · exact Replay207.excludes

/-- End-to-end integration of three checked certificates with the physical
case-cover interface, without assuming any unverified exclusions. -/
theorem selected_integer_exclusions (i : Fin 3) :
    ∀ x, (rootBox (rootCapacity (selectedCases i))).Contains x →
      ¬ (rootProblem (selectedCases i)).Admissible x :=
  integer_exclusion _ (selected_exclusions i)

end FiveColour.Packed.Archive
