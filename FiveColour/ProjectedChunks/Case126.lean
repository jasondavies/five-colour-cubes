module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case126
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 11307087139359073962393892825233373280996631873624487871371450167397181316541301269413832408806855323825733492583890674494205332211371867165932774038922994107506820880934307683997415122543099221054215777501203484857335811⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨23611742337562385305406, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340647030340707156299050781889704801152725612693487204679141161216171784460345221283290785923672815928606721, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply FastWeight.cut_valid_of_fast_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply FastWeight.cut_valid_of_fast_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply FastWeight.cut_valid_of_fast_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨3, 11307087139359073962393892825233373280996631873624487871371450167397181316541301269413832408806855323825733492583890674494205332211371867165930919556242077278727791040122739840221552159317427285547044625639156872520925187⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 54 1 (.split 56 1 (.split 72 1 (.split 73 1 (.split 6 0 (.step 18 (.close 7)) (.step 18 (.step 9 (.close 18)))) (.step 76 (.close 6))) (.step 75 (.close 6))) (.step 59 (.step 18 (.close 59)))) (.step 57 (.step 59 (.step 18 (.step 57 (.close 6)))))) (.split 54 1 (.split 73 1 (.step 45 (.step 18 (.close 45))) (.step 18 (.close 45))) (.step 18 (.close 45)))) (.step 41 (.split 42 1 (.split 54 1 (.split 72 1 (.split 73 1 (.step 41 (.close 6)) (.step 76 (.close 18))) (.step 33 (.step 18 (.close 75)))) (.step 59 (.split 72 1 (.split 73 1 (.step 41 (.close 6)) (.step 18 (.close 9))) (.step 18 (.close 75))))) (.step 41 (.close 45))))) (.split 54 1 (.split 73 1 (.step 39 (.step 41 (.step 18 (.close 39)))) (.step 18 (.close 39))) (.step 18 (.close 39)))) (.step 33 (.step 38 (.split 36 1 (.split 42 1 (.split 54 1 (.split 56 1 (.step 38 (.step 75 (.step 38 (.close 6)))) (.step 33 (.step 18 (.step 38 (.close 7))))) (.step 57 (.close 38))) (.step 38 (.close 45))) (.step 38 (.close 39)))))) (.split 54 1 (.split 73 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 6 0 (.step 37 (.close 10)) (.step 7 (.close 37))) (.step 37 (.close 9))) (.step 37 (.close 18))) (.step 37 (.close 18))) (.step 18 (.close 37))) (.step 18 (.close 37)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3, 11307087139359073962393892825233373280996631873624487871371450167397181316541301269413832408806855323825733492583890674494205332211371867165932774038922994107506820879401812143131524901726056514365135685735685353302392835⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 19 1 (.split 23 1 (.split 25 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 54 1 (.split 56 1 (.step 29 (.step 75 (.step 10 (.step 7 (.close 18))))) (.step 7 (.step 18 (.close 29)))) (.step 57 (.close 29))) (.step 29 (.close 45))) (.step 7 (.step 41 (.step 18 (.close 29))))) (.step 29 (.close 39))) (.step 29 (.close 37)))))) (.run (.step 7 (.step 28 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 54 1 (.split 72 1 (.split 73 1 (.step 28 (.close 18)) (.step 76 (.close 18))) (.step 7 (.step 18 (.close 28)))) (.step 9 (.step 59 (.step 18 (.close 28))))) (.step 28 (.close 45))) (.step 28 (.close 39))) (.step 7 (.step 33 (.step 38 (.step 18 (.step 28 (.close 15))))))) (.step 28 (.close 37))))))) (.run (.step 18 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 72 1 (.step 26 (.step 18 (.close 26))) (.step 18 (.close 26))) (.step 18 (.close 26))) (.step 18 (.close 26))) (.step 18 (.close 26))) (.step 18 (.close 26))) (.step 6 (.step 18 (.step 26 (.close 9)))))))) (.run (.step 18 (.split 25 1 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 72 1 (.step 22 (.step 18 (.close 22))) (.step 18 (.close 22))) (.step 18 (.close 22))) (.step 18 (.close 22))) (.step 18 (.close 22))) (.step 6 (.step 18 (.step 22 (.close 10))))) (.step 18 (.close 22))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2722258935367507707706996859454145691651, 11307087139359073962393892825233373280996631873624487871371450167397181316541301269413832408806855323825733492583890674494205332211371867165932774038922994107506820880934307683997415121213871225269298722852854202558840835⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 1 (.split 19 1 (.split 23 1 (.split 25 1 (.split 26 1 (.step 76 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 54 1 (.split 56 1 (.step 16 (.step 76 (.step 16 (.close 6)))) (.step 59 (.close 16))) (.step 12 (.step 18 (.step 16 (.close 57))))) (.step 18 (.close 45))) (.step 41 (.split 54 1 (.split 72 1 (.split 6 0 (.step 16 (.close 7)) (.step 10 (.close 41))) (.step 18 (.close 41))) (.step 16 (.close 18))))) (.step 18 (.close 39))) (.step 33 (.step 38 (.split 36 1 (.split 42 1 (.split 54 1 (.split 56 1 (.split 6 0 (.step 16 (.close 38)) (.step 10 (.step 16 (.close 18)))) (.step 18 (.close 59))) (.step 18 (.close 57))) (.step 18 (.close 45))) (.step 38 (.close 39)))))) (.step 18 (.close 37)))) (.step 29 (.step 37 (.split 36 1 (.step 10 (.split 38 1 (.split 42 1 (.split 54 1 (.split 56 1 (.step 16 (.close 29)) (.step 16 (.step 18 (.close 29)))) (.step 12 (.step 16 (.close 18)))) (.step 29 (.close 16))) (.step 18 (.close 41)))) (.step 29 (.close 39)))))) (.step 28 (.split 35 1 (.split 54 1 (.split 72 1 (.split 6 0 (.step 16 (.close 7)) (.step 6 (.step 16 (.close 9)))) (.step 18 (.close 28))) (.step 16 (.close 18))) (.step 18 (.close 28))))) (.step 16 (.close 26))) (.step 16 (.step 18 (.close 22)))) (.step 16 (.step 18 (.close 21)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2658455991569831745807614120560689155, 11307087139359073962393892825233373280996631873624487871371450167397181316541301269413832408806855323825733492583890674494205332211371867165932774038922994107506820880934307683997415122543099221054214595756661262839185411⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.split 18 1 (.split 19 1 (.split 23 1 (.split 25 1 (.step 57 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 72 1 (.step 15 (.step 12 (.close 18))) (.step 75 (.close 15))) (.step 57 (.split 72 1 (.step 15 (.step 12 (.step 18 (.close 6)))) (.step 18 (.close 28))))) (.step 18 (.close 45))) (.step 41 (.split 42 1 (.split 72 1 (.split 73 1 (.split 7 0 (.step 15 (.close 41)) (.step 9 (.step 15 (.close 18)))) (.step 18 (.close 76))) (.step 18 (.close 75))) (.step 18 (.close 45))))) (.step 18 (.close 39))) (.step 38 (.split 56 1 (.split 73 1 (.split 7 0 (.step 15 (.close 7)) (.step 9 (.close 38))) (.step 15 (.close 18))) (.step 18 (.close 38))))) (.step 18 (.close 37))) (.step 29 (.split 38 1 (.split 56 1 (.split 73 1 (.split 7 0 (.step 15 (.close 7)) (.step 6 (.close 29))) (.step 15 (.close 18))) (.step 18 (.close 29))) (.step 18 (.close 29)))))) (.step 7 (.step 28 (.step 37 (.split 35 1 (.split 36 1 (.step 9 (.split 42 1 (.split 72 1 (.split 73 1 (.step 15 (.close 28)) (.step 12 (.step 15 (.close 18)))) (.step 18 (.close 75))) (.step 28 (.close 15)))) (.step 28 (.close 39))) (.step 18 (.close 38))))))) (.step 15 (.step 18 (.close 26)))) (.step 15 (.close 22))) (.step 15 (.step 18 (.close 21))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3, 11307087139359073962393892825233373280996631873624487871371450167397181316541301269413832408806855323825733492583890674494205332211371867165932774038922994107506820880934307683997415122543099221054215776348281980250488835⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 7 1 (.split 12 1 (.split 13 1 (.split 18 1 (.reuse 0) (.run (.step 18 (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 72 1 (.split 54 1 (.split 25 0 (.step 21 (.close 10)) (.step 18 (.close 21))) (.step 21 (.close 18))) (.step 18 (.close 21))) (.step 18 (.close 21))) (.step 18 (.close 21))) (.step 18 (.close 21))) (.step 18 (.close 21)))))) (.reuse 1)) (.reuse 2)) (.run (.split 12 1 (.split 18 1 (.split 19 1 (.split 23 1 (.split 25 1 (.split 26 1 (.step 76 (.split 34 1 (.split 35 1 (.split 36 1 (.step 10 (.split 38 1 (.split 42 1 (.split 54 1 (.split 56 1 (.step 10 (.step 76 (.step 10 (.close 15)))) (.step 59 (.close 10))) (.step 6 (.step 18 (.close 10)))) (.step 18 (.close 45))) (.split 54 1 (.split 6 0 (.step 41 (.close 10)) (.step 6 (.close 7))) (.step 10 (.close 18))))) (.step 7 (.step 18 (.close 39)))) (.step 29 (.step 33 (.step 38 (.split 36 1 (.split 42 1 (.split 54 1 (.split 56 1 (.step 10 (.close 18)) (.step 18 (.close 59))) (.step 18 (.close 10))) (.step 18 (.close 45))) (.step 18 (.close 39))))))) (.step 18 (.close 37)))) (.step 10 (.step 29 (.close 10)))) (.step 7 (.close 10))) (.step 10 (.close 26))) (.step 10 (.step 18 (.close 22)))) (.step 10 (.step 18 (.close 21)))) (.step 6 (.step 10 (.step 12 (.step 15 (.step 21 (.step 22 (.step 18 (.step 10 (.step 15 (.close 18)))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3, 11307087139359073962393892825233373280996631873624487871371450167397181316541301269413832408806855323825733492583890674494205332211371867165932774038922994107506820880934307683997415122543099221054215777501203484857335811⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.reuse 0) (.run (.step 6 (.split 13 1 (.split 18 1 (.split 19 1 (.split 23 1 (.split 25 1 (.step 57 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 9 (.split 42 1 (.split 56 1 (.split 72 1 (.step 9 (.close 18)) (.step 75 (.close 9))) (.step 28 (.step 57 (.step 9 (.close 18))))) (.step 18 (.close 45)))) (.step 28 (.step 41 (.split 42 1 (.split 72 1 (.split 73 1 (.step 9 (.close 18)) (.step 18 (.close 9))) (.step 18 (.close 75))) (.step 18 (.close 45)))))) (.step 18 (.close 39))) (.step 9 (.split 73 1 (.split 7 0 (.step 38 (.close 9)) (.step 6 (.close 7))) (.step 9 (.close 18))))) (.step 18 (.close 37))) (.step 6 (.close 7)))) (.step 9 (.step 28 (.close 9)))) (.step 9 (.step 18 (.close 26)))) (.step 9 (.close 22))) (.step 9 (.step 18 (.close 21)))) (.step 6 (.step 9 (.step 12 (.step 16 (.step 21 (.step 22 (.step 18 (.step 9 (.step 16 (.close 18))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case126
