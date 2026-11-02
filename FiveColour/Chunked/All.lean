module
public import FiveColour.Chunked.Case78
public import FiveColour.Chunked.Case326
public import FiveColour.Chunked.Case7
@[expose] public section
namespace FiveColour.Packed.Chunked
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def roots : Fin 3 → Box := ![Case78.root, Case326.root, Case7.root]
def families : Fin 3 → Fin 78 → List Cut := ![Case78.families, Case326.families, Case7.families]
theorem all_excluded : ∀ i, Chunks.Excludes 15 (families i) (roots i) := by
  intro i
  fin_cases i
  · exact Case78.excludes
  · exact Case326.excludes
  · exact Case7.excludes
end FiveColour.Packed.Chunked
