module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case166
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 10273712730478288321023642923791353606196196407812131726871936621419135109769172305990500435502698646277160710723671530593951730670736222394774007769655957198336352452447008444936506055575773247184330922393600⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨37033564156298044177399, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969540306823801303036701114543271236497705040614186417671967029225310810172032001, 0⟩]
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
def root : Box := ⟨2147483648, 10273712730478288321023642923791353606196196407812131726868660034140723444323111406160730159168467075596845489699220736144180852689296269641985610458744626171073214577207516192196319828671720268931766807429120⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 64 (.step 54 (.step 65 (.split 34 0 (.step 9 (.step 22 (.close 52))) (.step 7 (.step 9 (.close 22))))))) (.step 7 (.step 10 (.step 22 (.step 54 (.step 26 (.close 52))))))) (.step 7 (.step 53 (.step 54 (.step 53 (.step 52 (.step 53 (.close 64)))))))) (.step 7 (.step 30 (.step 36 (.step 54 (.step 44 (.step 36 (.step 44 (.close 52))))))))) (.step 7 (.step 30 (.step 36 (.step 54 (.step 44 (.close 52))))))) (.step 7 (.step 30 (.step 36 (.step 54 (.step 44 (.step 36 (.step 44 (.close 52))))))))) (.step 7 (.step 52 (.step 54 (.step 52 (.step 53 (.step 52 (.close 64)))))))) (.step 54 (.step 70 (.close 7)))) (.step 54 (.step 70 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 64 (.step 62 (.step 9 (.step 22 (.close 65))))) (.step 7 (.step 10 (.step 26 (.step 22 (.step 52 (.step 22 (.close 53)))))))) (.step 7 (.step 53 (.step 52 (.close 64))))) (.step 7 (.step 30 (.step 44 (.step 36 (.step 52 (.step 36 (.close 53)))))))) (.step 7 (.step 30 (.step 44 (.step 36 (.step 52 (.step 36 (.close 53)))))))) (.step 7 (.step 30 (.step 44 (.step 36 (.step 52 (.step 36 (.close 53)))))))) (.step 7 (.step 52 (.step 53 (.close 65)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 10273712730478288321023642923791353606196196407812131726871936621419135109769172305990500435502698646277160710723671528556915754336250136126326634363611099230382752919803643590718909775533646373518728203599872⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 54 (.step 70 (.split 59 1 (.split 10 0 (.step 65 (.split 17 0 (.split 22 0 (.split 43 0 (.step 53 (.step 52 (.step 64 (.step 7 (.step 22 (.step 36 (.close 53))))))) (.step 53 (.step 7 (.close 9)))) (.step 7 (.step 27 (.step 36 (.step 44 (.step 36 (.step 44 (.close 52)))))))) (.step 7 (.step 27 (.step 36 (.step 44 (.step 36 (.step 44 (.close 52))))))))) (.step 7 (.step 52 (.close 53)))) (.step 53 (.close 7))))))) (.run (.split 50 1 (.step 54 (.step 70 (.split 59 1 (.split 10 0 (.split 16 0 (.step 52 (.step 64 (.step 7 (.step 53 (.step 64 (.step 7 (.step 9 (.close 27)))))))) (.step 7 (.step 30 (.close 52)))) (.step 7 (.close 52))) (.step 52 (.close 7))))) (.step 52 (.close 7))))) (.run (.step 46 (.split 49 1 (.split 50 1 (.step 46 (.split 10 0 (.split 61 1 (.split 62 1 (.step 46 (.close 7)) (.step 10 (.step 30 (.close 46)))) (.step 10 (.step 30 (.close 46)))) (.step 7 (.close 46)))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46))))))) (.run (.step 7 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 7 (.close 64)) (.step 7 (.close 52))) (.step 7 (.close 52)))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.step 37 (.step 39 (.step 64 (.close 37))))) (.step 7 (.close 37))) (.step 7 (.step 37 (.step 45 (.close 52))))) (.step 7 (.step 37 (.step 52 (.close 37))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 10273712730478288321023642923791353606196196407812131726871936621419135109769172305990500435502698646277160710723671530593951730670736222394774007769655957198336352452447008444936506055575773247184330922393600⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.step 7 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 7 (.step 64 (.close 65))) (.step 7 (.close 53))) (.step 7 (.step 52 (.close 53))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.step 19 (.step 20 (.step 64 (.step 65 (.close 19)))))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 53)))) (.step 7 (.step 19 (.step 25 (.step 52 (.step 53 (.close 19)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part2.excludes
end FiveColour.Packed.EnumerationChunks.Case166
