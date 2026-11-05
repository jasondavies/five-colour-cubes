module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case222
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536719788076541084446496990463323944165023385493327194111847916592822891319394304⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11593704327342213348339, 5789228615357111146520048038021683988773733487122101869605338720869906162805958987122173504434281850008071622175991935381017825153590590481063666660227604324706233660950604329370748855691173985301545264301300140783538537472, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536719788076541084446496990463323944165023385493327194111847916592822891319394304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 17 0 (.split 14 0 (.split 63 0 (.step 7 (.split 35 0 (.split 38 0 (.step 3 (.step 11 (.close 15))) (.step 3 (.close 5))) (.step 33 (.step 3 (.close 11))))) (.step 37 (.step 7 (.step 3 (.step 13 (.step 11 (.close 19))))))) (.step 37 (.step 5 (.step 11 (.step 13 (.close 19)))))) (.split 25 0 (.split 10 0 (.step 39 (.step 3 (.step 11 (.step 13 (.step 15 (.close 17)))))) (.split 35 0 (.step 13 (.step 20 (.step 3 (.step 5 (.close 14))))) (.step 33 (.step 4 (.step 11 (.step 13 (.close 15))))))) (.step 7 (.close 28)))) (.split 10 0 (.step 45 (.step 7 (.split 14 0 (.step 45 (.step 4 (.step 11 (.close 15)))) (.step 13 (.step 43 (.step 3 (.close 17))))))) (.step 7 (.split 35 0 (.step 13 (.step 45 (.step 3 (.step 5 (.close 11))))) (.step 33 (.step 13 (.step 17 (.step 4 (.step 11 (.close 19)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case222
