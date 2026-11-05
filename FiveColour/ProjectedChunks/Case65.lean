module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case65
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5653548956058700166731417831957222835796210385157339887379265041305812273667071379768561683190488308101476475035320933375408882627741153973206894893091498600542810377485090596116394531539381684632800506291227983486124034⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨2, 5653548956058700166731417831957222835796210385157339887379265041305812273667071379768561683190488308101476475035320933375408882627741153973206894893091498600542810377485090596116394531539381684632800506291227983486124034⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.step 63 (.split 6 0 (.split 7 0 (.split 23 0 (.split 25 0 (.split 12 0 (.step 18 (.step 4 (.step 18 (.step 13 (.step 16 (.close 33)))))) (.split 13 0 (.step 31 (.step 4 (.close 15))) (.step 4 (.step 13 (.close 12))))) (.step 4 (.step 29 (.step 18 (.step 48 (.step 13 (.step 16 (.close 33)))))))) (.step 31 (.step 63 (.step 18 (.step 29 (.step 15 (.close 18))))))) (.step 31 (.step 29 (.step 63 (.close 18))))) (.split 7 0 (.split 12 0 (.split 13 0 (.split 25 0 (.split 18 0 (.step 7 (.step 18 (.close 4))) (.step 18 (.close 6))) (.step 4 (.step 7 (.step 18 (.close 15))))) (.step 4 (.step 18 (.step 6 (.close 12))))) (.split 13 0 (.split 18 0 (.split 19 0 (.step 7 (.step 15 (.step 4 (.step 9 (.close 18))))) (.step 6 (.step 9 (.step 15 (.step 4 (.close 18)))))) (.step 6 (.step 9 (.step 15 (.close 18))))) (.step 4 (.step 6 (.step 9 (.step 12 (.close 13))))))) (.step 4 (.step 18 (.step 6 (.close 7))))))) (.step 5 (.split 7 0 (.split 13 0 (.step 4 (.step 24 (.step 6 (.close 15)))) (.step 4 (.step 5 (.close 16)))) (.step 4 (.step 5 (.step 6 (.close 16))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case65
