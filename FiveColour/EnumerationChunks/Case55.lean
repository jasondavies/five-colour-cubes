module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case55
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423277128847227091184192333350141696178997166080⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨18740915245514456087539, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475066830037980738387460577625234839625950792211697196357563187971868412046230991680761629786926547894765880320, 0⟩]
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
def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286115961774097719749263548910554423237234503767293952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 5 (.step 11 (.close 27))) (.step 62 (.close 5))) (.step 52 (.step 43 (.step 33 (.step 5 (.step 20 (.step 39 (.close 43)))))))) (.split 34 0 (.step 33 (.step 43 (.step 45 (.step 11 (.step 5 (.close 27)))))) (.step 58 (.step 33 (.step 17 (.step 20 (.step 37 (.close 43)))))))) (.split 34 0 (.split 30 0 (.step 62 (.step 5 (.close 11))) (.step 33 (.step 24 (.close 39)))) (.split 30 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 43 (.close 11)))))) (.split 22 0 (.split 34 0 (.step 54 (.step 24 (.step 25 (.close 5)))) (.split 30 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 43 (.close 11))))) (.split 38 0 (.step 70 (.split 39 0 (.step 24 (.step 11 (.close 20))) (.step 33 (.step 11 (.step 5 (.step 17 (.close 20))))))) (.step 33 (.step 24 (.step 5 (.close 20))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286115961775491516324171712856900405629275026361417728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 52 (.step 24 (.step 62 (.close 5)))) (.split 34 0 (.split 42 0 (.step 42 (.step 24 (.step 25 (.close 33)))) (.step 55 (.step 24 (.close 33)))) (.step 52 (.step 5 (.close 16))))) (.split 30 0 (.split 39 0 (.step 62 (.step 5 (.step 11 (.close 17)))) (.step 33 (.step 24 (.step 11 (.step 17 (.step 5 (.close 20))))))) (.step 33 (.step 62 (.step 20 (.step 5 (.close 11))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 61 (.step 24 (.close 11))) (.step 52 (.close 5))) (.step 33 (.step 54 (.step 17 (.close 5))))) (.split 34 0 (.split 36 0 (.step 70 (.step 61 (.step 11 (.step 17 (.step 5 (.close 19)))))) (.step 20 (.step 5 (.close 11)))) (.split 38 0 (.step 17 (.step 20 (.close 11))) (.step 5 (.step 17 (.step 5 (.close 20)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423277128847227089916541733121912294682293960704⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 68 (.step 11 (.close 17))) (.step 52 (.close 5))) (.step 33 (.close 53))) (.split 34 0 (.split 36 0 (.step 42 (.step 53 (.step 24 (.close 11)))) (.step 25 (.step 19 (.step 5 (.step 11 (.step 17 (.close 20))))))) (.split 38 0 (.step 17 (.step 19 (.step 17 (.step 20 (.close 23))))) (.step 5 (.step 17 (.step 5 (.close 19))))))) (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 53 (.step 11 (.step 17 (.step 5 (.close 20))))) (.step 11 (.step 17 (.close 19)))) (.step 19 (.step 5 (.step 11 (.close 24))))) (.step 20 (.step 5 (.close 11)))) (.split 36 0 (.split 38 0 (.step 17 (.step 19 (.step 17 (.close 20)))) (.step 5 (.step 17 (.step 5 (.close 19))))) (.step 17 (.step 19 (.close 20))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423275735050652183020245987367749655656403042304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 38 0 (.split 39 0 (.step 13 (.split 50 0 (.step 43 (.step 53 (.close 39))) (.step 33 (.step 24 (.step 15 (.step 38 (.close 39))))))) (.step 33 (.step 13 (.step 24 (.close 14))))) (.step 13 (.step 33 (.step 5 (.step 54 (.close 5)))))) (.step 13 (.split 38 0 (.split 39 0 (.split 50 0 (.split 34 0 (.step 25 (.step 5 (.close 20))) (.step 14 (.step 17 (.close 20)))) (.step 19 (.close 24))) (.step 17 (.step 19 (.close 24)))) (.step 19 (.step 14 (.close 23)))))) (.split 38 0 (.split 39 0 (.step 13 (.split 50 0 (.split 22 0 (.split 36 0 (.split 51 0 (.step 17 (.step 5 (.close 11))) (.step 20 (.step 14 (.step 17 (.close 23))))) (.step 20 (.close 17))) (.step 20 (.step 11 (.step 15 (.close 17))))) (.step 19 (.close 24)))) (.step 17 (.step 33 (.step 13 (.step 19 (.step 5 (.step 11 (.close 20)))))))) (.step 33 (.split 34 0 (.split 36 0 (.step 24 (.close 19)) (.step 13 (.step 19 (.step 5 (.close 20))))) (.step 13 (.close 14)))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1267650600228229401497776947200, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423277128847227091184192333350141696178997166080⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.step 52 (.step 43 (.step 33 (.step 5 (.step 20 (.step 39 (.close 43))))))) (.step 33 (.step 13 (.step 5 (.step 20 (.close 39)))))) (.step 52 (.step 16 (.close 5)))) (.split 38 0 (.step 70 (.step 13 (.split 39 0 (.step 43 (.close 11)) (.step 24 (.close 33))))) (.step 13 (.step 33 (.step 5 (.step 45 (.close 11))))))) (.split 22 0 (.split 38 0 (.split 39 0 (.step 13 (.step 54 (.step 24 (.close 15)))) (.step 33 (.step 13 (.step 20 (.step 5 (.close 11)))))) (.step 13 (.step 33 (.step 5 (.step 39 (.step 5 (.close 11))))))) (.step 13 (.split 38 0 (.split 39 0 (.split 50 0 (.split 36 0 (.step 25 (.step 5 (.close 14))) (.step 20 (.close 17))) (.step 33 (.step 24 (.close 11)))) (.step 17 (.step 19 (.step 20 (.close 11))))) (.step 19 (.step 14 (.step 33 (.step 20 (.close 5)))))))))) (.reuse 0)) (.run (.split 16 0 (.split 17 0 (.split 34 0 (.split 36 0 (.split 22 0 (.split 39 0 (.step 13 (.step 15 (.close 11))) (.step 33 (.step 13 (.step 11 (.step 5 (.close 13)))))) (.step 13 (.step 11 (.step 13 (.step 15 (.close 17)))))) (.split 38 0 (.step 54 (.step 15 (.close 5))) (.step 13 (.close 5)))) (.split 36 0 (.split 38 0 (.step 15 (.close 13)) (.step 13 (.close 5))) (.step 13 (.step 5 (.close 15))))) (.step 13 (.step 11 (.step 13 (.step 15 (.close 17)))))) (.split 17 0 (.step 13 (.step 11 (.step 13 (.step 15 (.close 17))))) (.step 13 (.close 17))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423277128847227091184192333350141696178997166080⟩
def references : Fin 3 → Box := ![Part0.root, Part2.root, Part4.root]
def proof : Chunks.Proof 3 := (.split 10 0 (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 34 0 (.step 53 (.step 24 (.close 5))) (.split 30 0 (.step 43 (.step 11 (.close 17))) (.step 33 (.step 38 (.step 5 (.step 11 (.close 17))))))) (.split 38 0 (.step 70 (.split 39 0 (.step 24 (.step 11 (.close 20))) (.step 33 (.step 11 (.step 5 (.step 17 (.close 19))))))) (.step 33 (.step 24 (.step 5 (.step 19 (.close 20))))))) (.split 22 0 (.split 38 0 (.split 39 0 (.step 54 (.step 24 (.close 11))) (.step 33 (.step 20 (.close 11)))) (.step 33 (.step 24 (.step 5 (.step 19 (.close 20)))))) (.split 38 0 (.split 39 0 (.step 25 (.step 20 (.step 11 (.close 17)))) (.step 19 (.step 11 (.step 17 (.close 19))))) (.step 19 (.step 17 (.step 19 (.step 11 (.step 20 (.step 23 (.close 24)))))))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part2.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part5.excludes
end FiveColour.Packed.EnumerationChunks.Case55
