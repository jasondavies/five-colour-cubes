module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case268
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5653548956058700166731417831957222835792060869588458894420752633442121112516058933536319246290492648189535944136999435573090003575782175849212904177256684980701058685762056803967313027059914440807907888584654501214945281⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨21221736057412879896382, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340644790595964978494840224447424232708447491047989970029606261225677024092266535310765487517604899868114945, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨1, 5653548956058700166731417831957222835792060869588458894420752633442121112516058933536319246290492648189535944136999435573090003575782175849212904177256684980701058685762056803967313027059914440807907887431732996608098305⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 18 0 (.split 7 0 (.split 25 0 (.split 13 0 (.step 31 (.step 5 (.step 15 (.close 37)))) (.step 31 (.step 37 (.step 22 (.close 21))))) (.step 29 (.split 13 0 (.step 31 (.step 5 (.step 15 (.close 37)))) (.step 31 (.step 37 (.step 22 (.close 21))))))) (.step 29 (.step 31 (.step 63 (.close 16))))) (.split 7 0 (.split 23 0 (.step 31 (.step 38 (.step 31 (.close 16)))) (.step 75 (.step 31 (.close 16)))) (.split 19 0 (.step 29 (.step 31 (.close 16))) (.split 25 0 (.step 21 (.step 22 (.step 10 (.step 21 (.close 5))))) (.step 6 (.close 9)))))) (.split 7 0 (.split 23 0 (.split 25 0 (.split 18 0 (.step 31 (.step 15 (.step 31 (.close 15)))) (.step 15 (.step 21 (.close 5)))) (.step 29 (.step 31 (.step 15 (.step 37 (.step 15 (.step 21 (.close 5)))))))) (.step 31 (.step 63 (.step 75 (.step 15 (.step 6 (.close 21))))))) (.step 29 (.step 31 (.step 16 (.step 63 (.step 15 (.close 21)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1, 5653548956058700166731417831957222835792060869588458894420752633442121112516058933536319246290492648189535944136999435573090003575782175849212904177256684980701058685762056803967313027059914440807907888584654501214945281⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.reuse 0) (.run (.split 12 0 (.split 7 0 (.split 23 0 (.split 25 0 (.split 18 0 (.step 31 (.split 13 0 (.step 31 (.step 5 (.step 11 (.close 15)))) (.step 15 (.step 28 (.step 22 (.close 5)))))) (.step 31 (.step 38 (.step 10 (.step 21 (.step 12 (.step 15 (.close 16)))))))) (.step 28 (.step 9 (.close 12)))) (.step 31 (.step 63 (.step 75 (.step 31 (.step 9 (.close 10))))))) (.step 29 (.step 31 (.step 63 (.close 9))))) (.split 7 0 (.split 23 0 (.split 25 0 (.step 15 (.step 31 (.step 10 (.close 5)))) (.step 9 (.step 15 (.close 28)))) (.step 9 (.step 15 (.step 31 (.step 26 (.step 6 (.close 21))))))) (.step 9 (.step 6 (.close 15)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case268
