module
public import FiveColour.Chunked.All
public import FiveColour.ArchiveBridge
@[expose] public section
namespace FiveColour.Packed.Chunked
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Case identities are retained even for selected, reordered replay lists. -/
def caseNumbers : Fin 3 → Fin 357 := ![78,326,7]

/-- Exact matching of the concrete replay roots with the verified archive headers. -/
theorem roots_match (i : Fin 3) : roots i = Archive.root (caseNumbers i) := by
  fin_cases i <;> rfl

theorem families_match (i : Fin 3) : families i = Archive.families (caseNumbers i) := by
  fin_cases i <;> funext t <;> rfl

theorem archive_exclusions (i : Fin 3) :
    Chunks.Excludes 15 (Archive.families (caseNumbers i)) (Archive.root (caseNumbers i)) := by
  rw [← roots_match, ← families_match]
  exact all_excluded i

theorem integer_exclusions (i : Fin 3) :
    ∀ x, (rootBox (rootCapacity (caseNumbers i))).Contains x →
      ¬ (rootProblem (caseNumbers i)).Admissible x :=
  Archive.integer_exclusion _ (archive_exclusions i)

end FiveColour.Packed.Chunked
