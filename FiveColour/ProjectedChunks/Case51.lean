module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case51
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759869379394596642197669783870791221248⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37630511536740893520887, 5789234131009374248507346766749886964179117598075761631441503938856419104125729984377942245333425284026394393415169773689373755704242316349912225571028696891635007459092358541327061333498215709696615525420286517587399934977, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333607532427808700155424991973343179088590124986613361869506463616058715241551421320018266029796604861414388575343531414402307405608785127713508715873027517901352943375876096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 57 1 (.split 59 1 (.split 52 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 48 (.step 3 (.step 55 (.close 7)))) (.split 38 0 (.step 7 (.close 3)) (.step 3 (.close 7)))) (.split 30 0 (.step 55 (.close 3)) (.step 7 (.close 3)))) (.split 22 0 (.split 30 0 (.step 55 (.close 3)) (.step 7 (.close 3))) (.step 7 (.close 18)))) (.split 30 0 (.split 17 0 (.split 22 0 (.step 55 (.close 3)) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 3 (.close 55)) (.step 3 (.close 4))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 3))))) (.split 11 0 (.split 38 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 7 (.close 3))) (.step 55 (.close 3))) (.step 55 (.split 67 1 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.split 22 0 (.step 55 (.step 7 (.step 58 (.close 3)))) (.step 7 (.close 3)))) (.step 48 (.close 7))) (.step 48 (.step 7 (.close 18)))) (.step 48 (.step 3 (.step 7 (.close 48))))) (.step 55 (.close 7)))) (.step 7 (.step 3 (.close 62)))))) (.step 3 (.split 52 1 (.split 10 0 (.step 60 (.split 30 0 (.step 60 (.step 3 (.close 48))) (.step 3 (.close 50)))) (.step 48 (.step 3 (.close 49)))) (.step 48 (.step 3 (.close 60)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216962965697198491383587046510367216899573738619030867535914622262553063115121778599327025338885665920544938956899324941611624927437464686624664623873806827520⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 53 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 52 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 46 0 (.step 43 (.step 55 (.close 7))) (.split 34 0 (.step 3 (.close 48)) (.step 16 (.close 3)))) (.step 7 (.step 3 (.close 38)))) (.step 7 (.step 5 (.close 37)))) (.step 7 (.step 5 (.close 37)))) (.step 43 (.close 59))) (.step 43 (.step 3 (.close 59)))) (.step 7 (.step 3 (.close 59)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 48 (.close 58)))) (.step 28 (.step 60 (.close 3)))) (.step 3 (.step 48 (.close 59)))))) (.run (.step 58 (.step 18 (.step 3 (.step 5 (.step 28 (.step 7 (.step 3 (.close 31)))))))))) (.run (.split 52 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.split 11 0 (.step 3 (.step 4 (.close 48))) (.split 34 0 (.step 56 (.close 55)) (.step 4 (.close 14)))) (.step 3 (.close 4))) (.step 3 (.close 7))) (.step 7 (.close 18))) (.step 7 (.close 51))) (.split 17 0 (.step 7 (.step 18 (.close 3))) (.step 19 (.step 7 (.close 18))))) (.step 7 (.step 3 (.close 14)))) (.step 3 (.step 7 (.close 8)))) (.step 4 (.step 48 (.close 17)))) (.step 8 (.step 60 (.close 3)))) (.step 3 (.step 43 (.step 51 (.close 3))))) (.step 18 (.step 3 (.step 48 (.step 51 (.close 58)))))) (.step 3 (.step 48 (.close 56))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 9797766621314684873895708907333611310075747213533922095702950587036435675200524143378245324142973470715541365092366787220646025235940865402766144354386238522478039134168762970504624341848475622669549568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.split 22 0 (.step 55 (.step 7 (.step 58 (.close 3)))) (.step 7 (.close 3)))) (.step 48 (.close 7))) (.step 48 (.step 7 (.close 18)))) (.step 48 (.step 3 (.step 7 (.close 48))))) (.step 55 (.close 7)))) (.step 7 (.step 3 (.close 52)))) (.split 10 0 (.split 16 0 (.split 17 0 (.split 11 0 (.split 34 0 (.step 62 (.close 3)) (.step 55 (.close 52))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 48 (.close 7)))) (.split 11 0 (.split 17 0 (.split 22 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 3 (.close 7))))) (.step 3 (.step 48 (.close 18)))) (.step 48 (.step 5 (.step 16 (.step 48 (.step 9 (.close 58))))))) (.step 4 (.step 48 (.step 49 (.step 34 (.step 48 (.close 27))))))) (.step 3 (.step 54 (.step 57 (.step 61 (.split 11 0 (.split 38 0 (.step 52 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 7 (.close 52))))))))) (.step 55 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 52 (.close 3)) (.step 52 (.step 55 (.close 7)))) (.step 55 (.close 52))) (.step 52 (.step 48 (.close 7)))) (.step 52 (.step 48 (.close 7)))) (.step 52 (.step 48 (.close 7)))) (.step 55 (.close 52))) (.step 48 (.close 52))) (.step 27 (.step 48 (.close 44)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768255444527386074741220752012962974214626175412773094685138378919474051297220685733493421843034394218218468152729756970362946248135489768227078144⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 3 (.split 53 1 (.split 55 1 (.split 56 1 (.split 11 0 (.split 38 0 (.step 54 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 26)))) (.step 3 (.step 7 (.close 44)))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 7 (.close 54))))))) (.run (.step 55 (.split 51 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.split 22 0 (.step 55 (.step 7 (.step 58 (.close 3)))) (.step 7 (.close 3)))) (.step 48 (.close 7))) (.step 48 (.step 7 (.close 18)))) (.step 48 (.step 3 (.step 7 (.close 48))))) (.step 55 (.close 7)))) (.step 7 (.step 3 (.close 53)))) (.split 10 0 (.split 16 0 (.split 17 0 (.split 11 0 (.split 34 0 (.step 62 (.close 3)) (.step 55 (.close 53))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 48 (.close 7)))) (.step 53 (.split 30 0 (.step 55 (.close 7)) (.step 7 (.close 3)))))) (.step 3 (.step 48 (.close 18)))) (.step 48 (.step 5 (.step 48 (.step 7 (.step 9 (.close 58))))))) (.step 48 (.step 53 (.close 21)))) (.step 4 (.step 48 (.step 35 (.step 50 (.step 48 (.close 27))))))) (.step 3 (.step 54 (.step 57 (.step 61 (.split 11 0 (.split 38 0 (.step 53 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 53)))) (.step 3 (.step 7 (.close 53)))))))))))) (.step 55 (.reuse 1)))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993512314372461856235306444415223878076369764031936969052252089930458175788306216846475086027172720343518804709447111541105750513287168⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 45 1 (.split 46 1 (.split 47 1 (.reuse 0) (.run (.step 3 (.split 49 1 (.split 52 1 (.split 55 1 (.split 10 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 50 (.step 3 (.step 5 (.close 58)))) (.step 8 (.step 3 (.step 48 (.close 50))))) (.step 48 (.step 50 (.close 3)))) (.step 48 (.step 50 (.close 55)))) (.step 48 (.step 49 (.step 50 (.step 3 (.close 21)))))) (.step 48 (.step 49 (.step 3 (.close 50))))) (.step 48 (.step 50 (.close 58)))) (.step 48 (.step 3 (.close 50)))) (.step 48 (.step 49 (.close 55))))))) (.run (.split 47 1 (.step 3 (.split 49 1 (.split 52 1 (.split 55 1 (.split 30 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 50 (.step 60 (.step 49 (.close 18)))) (.step 8 (.step 28 (.step 3 (.step 48 (.close 49)))))) (.step 48 (.step 49 (.close 3)))) (.step 48 (.step 49 (.step 3 (.close 21))))) (.step 3 (.step 48 (.step 49 (.close 3))))) (.step 48 (.step 49 (.close 48)))) (.step 48 (.step 3 (.close 49)))) (.step 48 (.step 49 (.close 55))))) (.step 49 (.step 3 (.step 49 (.step 48 (.close 49)))))))) (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 48 (.step 31 (.step 3 (.step 4 (.step 8 (.step 7 (.step 3 (.close 18)))))))) (.step 48 (.close 54))) (.step 48 (.close 53))) (.step 48 (.close 52))) (.step 48 (.close 50))) (.step 48 (.close 49)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225215024284136453122862303379606157926290523134599960255853580143376029398501553830444170708836391677399173255101677568⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 45 1 (.split 46 1 (.step 3 (.split 51 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 45 0 (.split 49 1 (.step 55 (.close 9)) (.step 9 (.close 52))) (.step 3 (.step 7 (.close 46)))) (.step 7 (.close 9))) (.step 7 (.close 46))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 3 (.step 7 (.close 27)))) (.step 7 (.close 46))) (.split 11 0 (.split 38 0 (.step 46 (.step 7 (.close 3))) (.step 3 (.close 46))) (.step 3 (.close 46)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.step 46 (.close 52)))))) (.step 3 (.step 7 (.close 27)))) (.step 54 (.step 7 (.step 3 (.close 54)))))) (.step 3 (.close 47))) (.step 3 (.step 7 (.step 27 (.step 46 (.close 52)))))))) (.run (.step 7 (.step 31 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 46 0 (.step 7 (.close 31)) (.step 31 (.close 7))) (.step 7 (.close 37))) (.step 7 (.step 31 (.close 16)))) (.step 28 (.step 31 (.close 60)))) (.step 76 (.step 59 (.close 45)))) (.step 7 (.step 31 (.close 45)))) (.step 4 (.step 7 (.step 37 (.close 51))))) (.step 3 (.step 31 (.close 45)))) (.step 7 (.step 31 (.close 45)))) (.step 31 (.step 7 (.close 58)))) (.step 31 (.step 28 (.step 50 (.step 31 (.step 50 (.close 45))))))) (.step 49 (.step 31 (.step 49 (.close 3)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 9797766621314684873895708907333611310075747216966320925768258496089993515087042155977052628648216682676110840640475271320731644744114442880826360790809863483612297400146310293741588380172227993736839168⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.split 22 0 (.split 30 0 (.split 46 0 (.step 43 (.step 48 (.step 41 (.close 3)))) (.split 34 0 (.step 3 (.close 48)) (.step 16 (.close 3)))) (.step 7 (.step 3 (.close 38)))) (.step 7 (.step 5 (.close 37))))) (.step 7 (.step 5 (.close 37)))) (.step 43 (.close 41))) (.step 43 (.step 3 (.step 41 (.close 3))))) (.step 7 (.step 3 (.close 41)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 48 (.close 58)))) (.step 5 (.step 58 (.close 31)))) (.step 28 (.step 60 (.step 3 (.close 16))))) (.step 28 (.split 59 1 (.step 59 (.step 3 (.close 7))) (.step 5 (.step 21 (.step 26 (.close 41))))))) (.step 43 (.step 24 (.step 59 (.step 60 (.step 3 (.close 56))))))) (.step 3 (.step 48 (.close 41)))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 21 (.step 5 (.step 48 (.step 7 (.step 21 (.close 26)))))))) (.step 49 (.step 58 (.step 16 (.step 48 (.step 9 (.step 52 (.close 58)))))))) (.step 21 (.step 41 (.step 3 (.step 50 (.step 3 (.close 21))))))) (.step 49 (.step 3 (.step 28 (.step 50 (.step 41 (.step 49 (.close 48)))))))) (.step 21 (.step 31 (.step 48 (.step 4 (.step 16 (.close 59))))))) (.step 10 (.close 46))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872270360586904047501897498942677645680046895178646782421085727644481431221992543941020983011492372383006720⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.reuse 0) (.split 42 1 (.reuse 1) (.run (.step 7 (.step 31 (.step 38 (.step 28 (.step 76 (.step 41 (.split 49 1 (.step 41 (.step 7 (.close 31))) (.step 7 (.step 16 (.step 21 (.close 31)))))))))))))) (.run (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 46 0 (.step 7 (.close 31)) (.step 31 (.close 7))) (.step 7 (.close 37))) (.step 7 (.step 22 (.close 31)))) (.step 28 (.step 31 (.step 51 (.close 60))))) (.step 22 (.step 59 (.step 7 (.close 16))))) (.step 7 (.step 31 (.close 58)))) (.step 4 (.step 7 (.step 37 (.close 51))))) (.step 3 (.step 31 (.step 39 (.close 51))))) (.step 7 (.step 31 (.close 58)))) (.step 22 (.step 31 (.step 7 (.close 52))))) (.step 31 (.step 28 (.step 50 (.step 31 (.step 50 (.close 39))))))) (.step 49 (.step 31 (.step 49 (.close 3))))) (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 55 1 (.step 45 (.step 7 (.step 31 (.close 3)))) (.step 31 (.close 39))) (.step 7 (.step 39 (.close 37)))) (.step 7 (.step 31 (.close 45)))) (.step 7 (.step 31 (.step 45 (.close 52))))) (.step 31 (.step 39 (.close 60)))) (.step 31 (.step 37 (.step 45 (.close 49)))))) (.step 38 (.step 28 (.step 45 (.split 49 1 (.step 41 (.split 52 1 (.split 59 1 (.step 41 (.step 7 (.close 16))) (.step 7 (.step 21 (.close 41)))) (.step 3 (.step 31 (.close 39))))) (.step 7 (.step 21 (.step 22 (.step 31 (.close 39))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 4898883310657342436947858505931971705553515434341103012552357296195872284853796012395923681835527219708876064032175917693156873971618961541256477412217657012912915357517311705493750763534503296970522624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 46 0 (.step 7 (.close 31)) (.step 31 (.close 7))) (.step 7 (.close 37))) (.step 7 (.step 31 (.close 16)))) (.step 31 (.step 49 (.step 3 (.close 37))))) (.step 28 (.step 59 (.step 37 (.step 7 (.close 31)))))) (.step 7 (.step 31 (.close 37)))) (.step 4 (.step 7 (.step 14 (.step 39 (.close 51)))))) (.step 3 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 58)))) (.step 31 (.step 7 (.close 16)))) (.step 31 (.step 49 (.step 31 (.step 50 (.step 3 (.step 31 (.close 37)))))))) (.step 31 (.step 49 (.close 3)))) (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 55 1 (.step 45 (.step 7 (.step 31 (.close 3)))) (.step 31 (.close 37))) (.step 7 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 16 (.close 52)))) (.step 31 (.step 45 (.step 3 (.close 50))))) (.step 37 (.close 49)))) (.step 16 (.step 28 (.step 38 (.step 41 (.split 53 1 (.step 37 (.step 7 (.close 31))) (.step 3 (.close 37)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875037076187987961584376921275777874072438102419149160448⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.step 31 (.split 36 1 (.reuse 1) (.run (.step 37 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 55 1 (.split 57 1 (.split 59 1 (.step 37 (.step 7 (.close 31))) (.step 7 (.step 16 (.step 22 (.close 31))))) (.step 31 (.step 37 (.close 3)))) (.step 31 (.close 37))) (.step 3 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 16 (.close 52)))) (.step 31 (.step 49 (.step 39 (.close 50))))) (.step 37 (.close 49))))))))) (.run (.step 18 (.step 31 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 7 (.step 41 (.step 3 (.close 7))))))))) (.run (.step 7 (.step 18 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 38 0 (.split 46 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 17)))) (.step 8 (.step 18 (.close 60)))) (.step 5 (.step 7 (.step 19 (.close 20))))) (.step 73 (.step 56 (.close 25)))) (.step 3 (.step 18 (.close 25)))) (.step 7 (.step 18 (.close 25)))) (.step 18 (.step 7 (.close 48)))) (.step 50 (.step 18 (.step 50 (.close 3))))) (.step 18 (.step 8 (.step 49 (.step 18 (.step 49 (.close 25))))))) (.step 4 (.step 18 (.close 48)))) (.step 3 (.step 4 (.step 5 (.step 24 (.step 41 (.step 49 (.step 50 (.step 7 (.step 19 (.close 51)))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759868080052731408262533249750005710848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 38 0 (.split 46 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 17)))) (.step 18 (.step 50 (.step 3 (.close 19))))) (.step 7 (.close 19))) (.step 8 (.step 56 (.step 19 (.step 7 (.close 18)))))) (.step 3 (.step 18 (.close 19)))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.step 7 (.close 48)))) (.step 18 (.step 50 (.close 3)))) (.step 18 (.step 8 (.step 49 (.step 18 (.step 49 (.step 3 (.close 19)))))))) (.step 4 (.step 18 (.close 48)))) (.step 3 (.step 4 (.step 5 (.step 24 (.step 41 (.step 19 (.close 49)))))))) (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 56 1 (.step 25 (.step 7 (.step 18 (.close 3)))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 19)))) (.step 7 (.step 18 (.step 19 (.close 52))))) (.step 19 (.close 50))) (.step 18 (.step 49 (.step 19 (.close 3))))) (.step 18 (.close 19))) (.step 7 (.step 19 (.close 41))))) (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 57 1 (.split 59 1 (.step 19 (.step 7 (.close 18))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.step 19 (.close 3)))) (.step 7 (.step 18 (.step 19 (.close 52))))) (.step 19 (.close 50))) (.step 18 (.step 49 (.step 19 (.close 3))))) (.step 18 (.close 19))) (.step 7 (.step 19 (.close 41))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225215024284136453122862303379606157926290523134599960255853580143376029398501553830445468783051025384306305879183982592⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 45 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.split 30 0 (.split 34 0 (.step 3 (.step 48 (.close 37))) (.step 4 (.close 37))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 7))) (.step 7 (.close 18))) (.step 7 (.step 14 (.close 18)))) (.step 8 (.split 17 0 (.step 7 (.step 14 (.close 18))) (.step 14 (.close 7))))) (.step 7 (.step 3 (.close 14)))) (.step 3 (.step 7 (.close 8)))) (.step 48 (.close 14))) (.step 48 (.close 14))) (.step 8 (.step 60 (.step 3 (.close 14))))) (.step 24 (.step 43 (.step 60 (.step 3 (.close 59)))))) (.step 5 (.step 18 (.step 3 (.step 34 (.close 58)))))) (.step 8 (.split 59 1 (.step 56 (.step 3 (.close 7))) (.step 4 (.step 14 (.close 48)))))) (.step 3 (.step 48 (.close 14)))) (.step 3 (.step 7 (.close 54)))) (.step 48 (.step 35 (.step 50 (.step 58 (.step 48 (.close 44))))))) (.step 34 (.step 4 (.step 48 (.step 58 (.step 27 (.step 34 (.close 44)))))))) (.step 49 (.step 8 (.step 50 (.step 3 (.step 50 (.step 3 (.close 14)))))))) (.step 34 (.step 49 (.step 3 (.step 49 (.step 3 (.close 14))))))) (.step 8 (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 5 (.step 4 (.step 24 (.step 14 (.step 49 (.step 50 (.step 7 (.step 37 (.close 51))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759869378126946041969440382374088015872⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 4 (.step 49 (.step 50 (.step 60 (.split 42 1 (.split 53 1 (.step 43 (.step 24 (.split 16 0 (.step 43 (.step 41 (.close 14))) (.step 3 (.close 14))))) (.step 14 (.close 3))) (.step 4 (.close 41))))))))) (.run (.step 4 (.step 3 (.step 5 (.step 4 (.step 41 (.step 43 (.step 49 (.step 50 (.step 51 (.step 14 (.step 7 (.step 37 (.close 39))))))))))))))) (.run (.step 3 (.step 4 (.step 7 (.step 43 (.step 49 (.step 4 (.step 14 (.step 7 (.step 41 (.step 37 (.step 14 (.step 37 (.close 50))))))))))))))) (.run (.step 3 (.step 31 (.step 50 (.step 7 (.close 14))))))) (.run (.step 7 (.step 17 (.step 8 (.step 18 (.step 73 (.split 38 1 (.split 50 1 (.step 14 (.step 7 (.close 18))) (.step 7 (.step 14 (.close 18)))) (.step 5 (.close 14)))))))))) (.run (.step 7 (.step 17 (.step 8 (.step 25 (.split 38 1 (.split 50 1 (.split 52 1 (.split 56 1 (.split 59 1 (.step 14 (.step 7 (.close 14))) (.step 7 (.step 14 (.close 17)))) (.step 5 (.close 14))) (.step 3 (.step 14 (.close 18)))) (.step 7 (.step 17 (.step 14 (.close 18))))) (.step 5 (.close 14))))))))) (.run (.step 7 (.step 17 (.step 8 (.step 18 (.step 35 (.step 14 (.split 38 1 (.split 56 1 (.step 19 (.step 7 (.close 14))) (.step 5 (.close 14))) (.step 5 (.close 14)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759869379394596642197669783870791221248⟩
def references : Fin 3 → Box := ![Part9.root, Part10.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 10 1 (.split 11 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 22 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 38 0 (.split 46 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 17)))) (.step 8 (.step 18 (.step 51 (.close 60))))) (.step 5 (.step 7 (.step 19 (.close 20))))) (.step 36 (.step 56 (.step 7 (.close 18))))) (.step 3 (.step 18 (.step 20 (.close 51))))) (.step 7 (.step 18 (.close 48)))) (.step 18 (.step 7 (.close 48)))) (.step 50 (.step 18 (.step 50 (.close 3))))) (.step 18 (.step 8 (.step 49 (.step 18 (.step 49 (.close 20))))))) (.step 4 (.step 18 (.close 48)))) (.step 3 (.step 4 (.step 5 (.step 24 (.step 41 (.step 49 (.step 50 (.step 7 (.step 19 (.close 51))))))))))) (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 56 1 (.step 25 (.step 7 (.step 18 (.close 3)))) (.step 7 (.step 20 (.close 19)))) (.step 7 (.step 18 (.close 25)))) (.step 7 (.step 18 (.step 48 (.close 52))))) (.step 18 (.step 19 (.step 20 (.close 50))))) (.step 18 (.step 49 (.step 20 (.close 3))))) (.step 18 (.close 25))) (.step 7 (.step 19 (.step 20 (.close 60)))))))))) (.reuse 1)) (.reuse 2)) (.run (.step 18 (.step 31 (.split 11 1 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 3 (.step 49 (.step 7 (.close 41))))) (.step 7 (.step 14 (.step 3 (.close 7)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case51
