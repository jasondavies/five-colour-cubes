module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case69
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5260135901548373507240989882880128665554204340346194632619378241831841263940103671587036994856464153116356181750708692256867704353528451149109989800074996372159268087382359341910673950294640752640864086015344642⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨36598186871210186373086, 5653548961318841089639973500642015693236235224231190043906103201777981023951928279572763835464728950349135465840953962536991606646746825747881197814404025084909808628036390642683365795134764479495963128771311687678559233, 0⟩]
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
def root : Box := ⟨2, 5260135901548373507240989882880128665554204340346194632619378241831841263940103671587036994856464153116356181750708692256867704353528451149109989800074996372159268087382359341910673950294640752640864086015344642⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.step 4 (.step 6 (.close 12)))))
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
end FiveColour.Packed.ProjectedChunks.Case69
