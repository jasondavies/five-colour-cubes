module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case34
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536719788076541084446496990463323944165023385493327194111847916592822891319394304⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨11593704327342213348339, 5789228615357111146520048038021683988773733487122101869605338720869906162805958987122173504434281850008071622175991935381017825153590590481063666660227604324706233660950604329370748855691173985301545264301300140783538537472, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536719788076541084446496990463323944165023385493325926461247688363421394616188928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 16 0 (.split 14 0 (.split 63 0 (.split 51 0 (.split 30 0 (.step 3 (.step 29 (.close 3))) (.step 38 (.step 3 (.close 11)))) (.step 39 (.step 7 (.step 3 (.step 4 (.close 11)))))) (.step 37 (.split 25 0 (.step 3 (.step 24 (.close 29))) (.step 3 (.step 7 (.close 28)))))) (.step 37 (.step 5 (.step 11 (.step 19 (.close 20)))))) (.split 22 0 (.split 14 0 (.split 63 0 (.split 51 0 (.step 38 (.close 3)) (.step 7 (.step 38 (.step 3 (.close 11))))) (.step 37 (.step 38 (.step 3 (.close 11))))) (.step 7 (.step 37 (.step 5 (.step 11 (.close 19)))))) (.step 7 (.step 45 (.split 35 0 (.split 14 0 (.step 38 (.step 3 (.step 11 (.close 15)))) (.step 13 (.step 19 (.step 5 (.step 11 (.close 17)))))) (.step 24 (.step 3 (.step 13 (.step 17 (.close 19)))))))))) (.split 25 0 (.split 16 0 (.split 34 0 (.split 22 0 (.step 39 (.step 3 (.step 11 (.close 13)))) (.step 45 (.step 20 (.step 3 (.close 11))))) (.step 39 (.step 5 (.step 11 (.step 17 (.step 15 (.close 19))))))) (.split 14 0 (.split 22 0 (.step 39 (.step 4 (.step 11 (.step 15 (.close 19))))) (.step 45 (.step 19 (.step 20 (.step 3 (.close 11)))))) (.step 13 (.step 20 (.step 19 (.step 11 (.step 17 (.close 20)))))))) (.step 7 (.step 29 (.close 5))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774536719788076541084446496990463323944165023385493327194111847916592822891319394304⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 51 0 (.split 63 0 (.split 71 0 (.step 7 (.split 35 0 (.step 3 (.step 5 (.close 11))) (.step 33 (.close 3)))) (.step 39 (.step 7 (.step 3 (.step 11 (.close 15)))))) (.step 37 (.split 25 0 (.step 3 (.close 13)) (.step 3 (.step 5 (.step 3 (.close 28))))))) (.step 7 (.step 39 (.step 13 (.split 35 0 (.step 3 (.step 5 (.close 11))) (.step 33 (.close 3))))))) (.step 7 (.split 22 0 (.step 39 (.step 4 (.step 11 (.step 13 (.close 15))))) (.step 13 (.step 39 (.step 17 (.step 4 (.step 11 (.close 19))))))))) (.step 7 (.split 17 0 (.split 22 0 (.split 51 0 (.step 38 (.step 3 (.step 11 (.close 13)))) (.step 13 (.step 39 (.step 38 (.close 3))))) (.step 13 (.step 45 (.step 17 (.step 3 (.step 4 (.close 11))))))) (.step 13 (.split 35 0 (.split 38 0 (.step 20 (.step 39 (.step 17 (.step 3 (.close 11))))) (.step 14 (.step 19 (.step 5 (.close 20))))) (.step 17 (.step 19 (.step 23 (.close 20))))))))) (.step 7 (.split 63 0 (.split 16 0 (.split 17 0 (.split 51 0 (.step 37 (.step 5 (.step 11 (.close 13)))) (.step 13 (.close 3))) (.step 13 (.close 3))) (.step 13 (.close 3))) (.step 3 (.close 13)))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Case34
