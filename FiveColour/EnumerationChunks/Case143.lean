module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case143
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644916960232424190509056⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32016031753816107707383, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699533605928482613073959526943958677216822273, 0⟩]
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
def root : Box := ⟨2147483648, 11031304531345847419206713694029083651922938300223353678645140482247226209330261113345799791430134245752672712106866336352468556623363832419213459975370532341151350347516161563945872355322270794907922072848311861116928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 16 0 (.split 10 0 (.split 12 0 (.split 17 0 (.split 21 0 (.split 26 0 (.split 22 0 (.split 35 0 (.split 68 0 (.step 7 (.close 9)) (.step 7 (.step 9 (.close 22)))) (.step 7 (.step 9 (.close 21)))) (.step 7 (.close 4))) (.step 7 (.step 9 (.step 29 (.step 7 (.step 21 (.close 22))))))) (.step 7 (.step 9 (.step 7 (.close 4))))) (.step 7 (.step 4 (.close 7)))) (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 17 0 (.split 30 0 (.step 9 (.step 71 (.step 15 (.step 7 (.close 16))))) (.step 7 (.step 9 (.close 15)))) (.step 4 (.close 7))) (.step 7 (.step 9 (.step 15 (.step 16 (.close 21)))))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 7 (.step 9 (.step 15 (.step 7 (.step 18 (.step 16 (.step 21 (.close 22))))))))) (.step 7 (.step 9 (.step 18 (.step 15 (.step 7 (.close 4)))))))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 18 (.close 4)))) (.split 10 0 (.split 12 0 (.step 7 (.split 16 0 (.split 21 0 (.split 26 0 (.step 7 (.step 9 (.step 26 (.step 7 (.step 21 (.close 22)))))) (.step 29 (.close 22))) (.step 7 (.step 18 (.close 4)))) (.step 7 (.step 4 (.close 18))))) (.step 9 (.step 29 (.step 7 (.step 18 (.step 15 (.step 26 (.step 7 (.step 16 (.close 21)))))))))) (.step 7 (.step 9 (.close 15))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973191984381084500630769492679916833617023780404672701586152017245777266494690284288273142738280548349377904898996149901186905957742528827836922267365818862057087458319110335006304712892874752⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 68 1 (.split 69 1 (.reuse 0) (.run (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 21 0 (.split 26 0 (.step 72 (.close 7)) (.step 10 (.step 22 (.step 29 (.step 7 (.step 21 (.close 26))))))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 22 (.close 52))))) (.step 4 (.step 7 (.close 27)))) (.step 7 (.step 4 (.close 27)))) (.step 7 (.step 4 (.close 27)))) (.step 4 (.split 16 0 (.split 17 0 (.step 4 (.step 10 (.step 22 (.step 57 (.step 7 (.step 15 (.step 7 (.step 16 (.close 21))))))))) (.step 4 (.close 7))) (.step 4 (.close 7))))) (.step 7 (.step 64 (.step 7 (.close 9))))) (.step 4 (.step 57 (.step 9 (.step 26 (.step 29 (.step 7 (.step 15 (.step 16 (.close 21)))))))))))) (.run (.step 71 (.step 18 (.step 4 (.step 9 (.step 29 (.step 7 (.step 18 (.step 16 (.close 21))))))))))) (.run (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 26 0 (.step 70 (.step 7 (.step 21 (.close 15)))) (.step 7 (.step 9 (.step 26 (.close 70))))) (.step 7 (.step 4 (.close 9)))) (.step 7 (.step 9 (.step 26 (.close 70))))) (.step 70 (.step 4 (.step 7 (.close 15))))) (.step 7 (.step 70 (.close 71))))))
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
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 11031304536487720240955970973196339712625598120978747303210563859767883068238063247922252687710509803881143276663603870799123229520389791497937122495231799693097580036285425429644748073373397735531185230700773063524352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 21 0 (.split 34 0 (.split 43 0 (.step 71 (.step 21 (.close 22))) (.step 9 (.close 52))) (.step 10 (.step 15 (.close 7)))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 22 (.close 52))))) (.step 4 (.step 7 (.close 27)))) (.step 7 (.step 4 (.close 27)))) (.step 7 (.step 4 (.close 27)))) (.step 4 (.split 16 0 (.split 17 0 (.step 4 (.step 10 (.step 15 (.step 7 (.close 22))))) (.step 4 (.close 7))) (.step 4 (.close 7))))) (.step 7 (.step 52 (.close 15)))) (.step 4 (.step 15 (.step 10 (.step 26 (.step 64 (.close 7))))))) (.split 72 1 (.step 72 (.step 7 (.step 4 (.step 7 (.close 15))))) (.step 4 (.step 10 (.step 15 (.step 22 (.step 26 (.step 57 (.close 64))))))))) (.step 63 (.step 64 (.step 9 (.step 15 (.step 21 (.step 26 (.step 28 (.close 29))))))))) (.step 64 (.step 70 (.step 4 (.step 7 (.close 15)))))) (.step 64 (.split 72 1 (.split 21 0 (.split 30 0 (.split 36 0 (.step 64 (.close 4)) (.step 7 (.step 10 (.step 15 (.step 21 (.close 64)))))) (.step 7 (.step 52 (.step 53 (.close 15))))) (.step 7 (.step 4 (.step 7 (.step 9 (.close 22)))))) (.step 4 (.step 10 (.step 15 (.step 21 (.close 64)))))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712625598120978747303210563859767883068238063247922252687710509803881143276663603870799123229520389791497937122495231799693097580036285425429644748073373397735531185230700773063524352⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 61 1 (.split 62 1 (.reuse 0) (.run (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 21 0 (.split 35 0 (.step 65 (.close 7)) (.step 9 (.step 21 (.close 22)))) (.step 4 (.step 7 (.close 9)))) (.step 10 (.step 4 (.step 21 (.step 7 (.close 15)))))) (.step 7 (.step 9 (.step 22 (.close 52))))) (.step 4 (.step 7 (.close 27)))) (.step 7 (.step 4 (.close 27)))) (.step 7 (.step 4 (.close 27)))) (.step 4 (.split 16 0 (.split 17 0 (.step 4 (.step 10 (.step 21 (.step 64 (.step 7 (.step 22 (.close 26))))))) (.step 4 (.close 7))) (.step 4 (.close 7))))) (.step 7 (.step 53 (.step 7 (.step 9 (.close 15)))))) (.step 4 (.step 71 (.close 15)))) (.split 72 1 (.step 72 (.step 7 (.step 4 (.step 7 (.close 16))))) (.step 4 (.step 10 (.step 21 (.step 22 (.step 26 (.step 57 (.close 65))))))))) (.step 63 (.step 65 (.close 71)))) (.step 65 (.step 70 (.step 4 (.step 7 (.close 15)))))))) (.reuse 1))
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
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384264315699200, 11031304536487720240955970973196339712629650382276482651495742168706826074048029646094712429591419507633702611280353747000311757972567493802279239626988333839970241307824223340035469193974026904401143060747788434276352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 68 0 (.split 17 0 (.split 43 0 (.step 57 (.close 4)) (.step 9 (.close 4))) (.step 7 (.close 4))) (.step 7 (.step 4 (.step 9 (.step 54 (.step 15 (.step 16 (.close 26)))))))) (.step 7 (.step 9 (.step 18 (.step 21 (.step 7 (.step 15 (.step 16 (.close 22))))))))) (.step 7 (.step 9 (.step 15 (.close 7))))) (.step 9 (.step 57 (.close 7)))) (.step 9 (.step 18 (.close 57)))) (.step 9 (.step 26 (.step 29 (.step 57 (.close 4)))))) (.step 4 (.step 22 (.step 9 (.close 57))))) (.step 4 (.step 9 (.step 29 (.step 57 (.step 18 (.close 57))))))) (.step 57 (.step 72 (.split 68 1 (.split 10 0 (.step 26 (.split 16 0 (.step 57 (.close 7)) (.step 4 (.close 7)))) (.step 7 (.step 9 (.step 15 (.step 22 (.close 26)))))) (.step 4 (.step 7 (.step 9 (.step 26 (.step 29 (.step 54 (.close 57))))))))))) (.step 4 (.step 21 (.step 57 (.step 10 (.step 57 (.step 65 (.close 7)))))))) (.step 4 (.step 71 (.split 62 1 (.step 4 (.step 15 (.step 57 (.step 10 (.step 57 (.step 52 (.step 7 (.step 26 (.step 7 (.close 53)))))))))) (.step 10 (.step 21 (.step 4 (.step 15 (.step 57 (.close 64)))))))))) (.step 9 (.step 26 (.step 57 (.step 4 (.step 7 (.step 52 (.step 7 (.close 53))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216826650525696, 11031304536487720240955970973196339712629650382276482651495742172058778056533678920988218679142881039503544066428452091431202118903008501320665983827456908381696098230332187886656981907412497607387785547356200685797376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.step 70 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 59 1 (.split 36 0 (.step 54 (.step 7 (.step 22 (.step 15 (.step 16 (.close 21)))))) (.step 7 (.step 9 (.step 15 (.step 16 (.close 22)))))) (.step 62 (.close 7))) (.step 7 (.step 4 (.step 26 (.step 27 (.close 36)))))) (.step 7 (.step 4 (.step 9 (.step 4 (.close 22)))))) (.step 7 (.step 4 (.step 22 (.step 27 (.close 36)))))) (.step 7 (.step 4 (.step 27 (.step 4 (.close 36)))))) (.step 7 (.step 9 (.step 22 (.step 26 (.step 29 (.step 53 (.close 15)))))))) (.step 22 (.step 54 (.step 4 (.step 7 (.close 15)))))) (.step 7 (.step 54 (.step 62 (.close 71))))) (.step 54 (.step 65 (.split 12 0 (.split 21 0 (.step 71 (.step 54 (.close 7))) (.step 4 (.step 7 (.step 4 (.step 9 (.close 22)))))) (.step 10 (.step 53 (.step 4 (.step 54 (.step 7 (.close 15)))))))))) (.step 54 (.step 64 (.split 12 0 (.split 21 0 (.step 71 (.step 54 (.close 7))) (.step 4 (.step 7 (.step 4 (.step 9 (.close 22)))))) (.step 10 (.step 15 (.step 52 (.step 4 (.step 54 (.step 7 (.close 15)))))))))))) (.step 22 (.step 57 (.step 7 (.step 4 (.step 10 (.step 7 (.step 52 (.close 53))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635117070658382340178474022002387483074570784541978421714863933670940409529213386752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 53 (.split 51 1 (.split 54 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 10 0 (.split 12 0 (.step 53 (.step 7 (.step 9 (.close 21)))) (.step 9 (.split 17 0 (.step 21 (.split 22 0 (.split 61 0 (.split 68 0 (.step 53 (.step 5 (.close 7))) (.step 5 (.step 7 (.step 16 (.step 22 (.close 26)))))) (.step 5 (.step 15 (.step 7 (.close 22))))) (.step 7 (.step 4 (.close 7))))) (.step 18 (.close 4))))) (.step 18 (.step 7 (.step 52 (.close 9))))) (.step 18 (.step 7 (.step 4 (.close 27))))) (.step 9 (.step 55 (.step 26 (.step 18 (.step 21 (.step 7 (.close 53)))))))) (.step 53 (.step 71 (.step 72 (.step 4 (.close 7)))))) (.step 18 (.step 53 (.step 15 (.close 29))))) (.step 53 (.close 7))) (.step 53 (.close 4))) (.step 52 (.step 65 (.step 70 (.step 71 (.split 16 0 (.split 12 0 (.step 72 (.step 53 (.step 4 (.step 7 (.step 9 (.close 22)))))) (.step 4 (.step 9 (.step 15 (.step 7 (.step 22 (.step 7 (.close 26)))))))) (.step 4 (.step 7 (.step 27 (.close 36)))))))))) (.step 9 (.step 21 (.step 53 (.step 57 (.step 7 (.step 4 (.step 52 (.step 7 (.close 26)))))))))) (.step 53 (.step 7 (.step 22 (.step 36 (.step 52 (.close 54)))))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635117070658382340178474022002387483074570784541978421714863933670940409529213386752⟩
def references : Fin 4 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 4 := (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.reuse 0) (.run (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.step 62 (.split 10 0 (.step 62 (.split 21 0 (.split 26 0 (.split 35 0 (.step 7 (.step 4 (.close 9))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.step 15 (.close 21))))) (.step 7 (.close 4)))) (.step 7 (.close 9)))) (.step 18 (.step 7 (.step 4 (.close 27))))) (.step 9 (.step 26 (.close 7)))) (.step 26 (.step 62 (.step 72 (.step 4 (.close 7)))))) (.step 18 (.step 26 (.step 62 (.step 15 (.close 21)))))) (.step 26 (.step 62 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53)))))))) (.step 26 (.step 53 (.step 70 (.step 71 (.step 72 (.step 62 (.step 65 (.step 4 (.close 7)))))))))) (.step 26 (.step 52 (.step 70 (.step 71 (.split 12 0 (.step 65 (.step 72 (.step 62 (.split 16 0 (.step 64 (.step 4 (.close 7))) (.step 4 (.close 7)))))) (.step 4 (.step 9 (.step 15 (.step 26 (.step 7 (.step 22 (.step 7 (.close 53)))))))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434276803595271946858057795038993245151143890047831291497731209822335181667471539403261542233562010298803559802660766531613682854526976⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 54 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 10 0 (.split 12 0 (.split 17 0 (.step 52 (.step 7 (.step 9 (.close 21)))) (.step 7 (.step 18 (.step 4 (.close 27))))) (.step 9 (.split 21 0 (.step 52 (.close 7)) (.step 15 (.step 18 (.close 4)))))) (.step 18 (.step 7 (.close 52)))) (.step 18 (.step 7 (.step 4 (.close 27))))) (.step 9 (.step 55 (.step 26 (.step 18 (.step 52 (.step 7 (.close 16)))))))) (.step 52 (.step 71 (.split 12 0 (.step 7 (.step 9 (.step 21 (.close 22)))) (.step 4 (.step 9 (.step 7 (.close 16)))))))) (.step 18 (.step 52 (.step 16 (.step 21 (.close 29)))))) (.step 52 (.close 7))) (.step 53 (.step 70 (.step 71 (.step 64 (.step 65 (.step 52 (.step 4 (.step 7 (.step 9 (.close 22))))))))))) (.step 52 (.close 7))) (.step 9 (.step 52 (.step 57 (.step 18 (.step 4 (.close 52))))))) (.step 52 (.step 7 (.step 22 (.step 36 (.step 53 (.close 54))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775634760222489937077505622052248736002254491837261732745465932815854707943120399455463929605332389681187442917376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 26 (.step 7 (.close 15)))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 4 (.close 26)))) (.step 7 (.step 4 (.step 26 (.step 15 (.close 21)))))) (.step 4 (.step 7 (.step 26 (.step 15 (.step 28 (.step 15 (.close 21)))))))) (.step 7 (.step 4 (.step 21 (.step 26 (.step 15 (.step 28 (.step 15 (.close 31))))))))) (.step 7 (.step 26 (.step 28 (.step 31 (.step 15 (.step 21 (.step 26 (.step 21 (.close 57)))))))))) (.step 7 (.step 26 (.step 15 (.close 21))))) (.step 26 (.step 31 (.step 29 (.step 7 (.step 15 (.step 26 (.step 15 (.close 21))))))))) (.step 7 (.step 18 (.step 26 (.step 29 (.step 38 (.step 40 (.step 45 (.step 18 (.step 15 (.step 26 (.step 15 (.step 52 (.close 53)))))))))))))) (.step 7 (.step 26 (.step 55 (.step 9 (.step 52 (.step 7 (.step 26 (.step 15 (.step 29 (.step 15 (.close 21))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775634760222489937077505622052248736002254491837261732745465932815854707943120399455463929605332389681187442917376⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 70 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 59 1 (.split 10 0 (.split 26 0 (.split 49 0 (.split 50 0 (.step 29 (.close 10)) (.step 9 (.close 7))) (.step 9 (.step 7 (.step 9 (.close 46))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 46)))) (.step 9 (.close 46))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.step 4 (.close 9)))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.close 9))) (.step 10 (.step 30 (.close 46)))) (.step 7 (.step 9 (.close 46)))) (.step 10 (.step 30 (.close 46)))) (.step 10 (.step 30 (.step 46 (.step 7 (.step 52 (.step 53 (.close 64))))))))) (.step 9 (.step 10 (.step 4 (.step 7 (.step 4 (.close 10))))))) (.step 46 (.step 54 (.step 7 (.close 9))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46)))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404237493564800576407533357227799741497031882949738790856989270474570991344174895267113406773389414096611938118836084378977387413504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 31 (.step 26 (.step 7 (.close 15))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 4 (.step 26 (.step 4 (.close 15)))))) (.step 7 (.step 4 (.step 28 (.step 15 (.step 26 (.step 15 (.close 21)))))))) (.step 4 (.step 7 (.step 28 (.step 31 (.step 15 (.step 26 (.step 15 (.close 21))))))))) (.step 7 (.step 4 (.step 21 (.step 28 (.step 31 (.step 15 (.step 26 (.step 15 (.close 39)))))))))) (.step 7 (.step 28 (.step 31 (.step 15 (.step 39 (.step 21 (.step 26 (.step 39 (.close 57)))))))))) (.step 7 (.step 26 (.step 15 (.close 21))))) (.step 31 (.step 29 (.step 39 (.step 7 (.step 26 (.step 15 (.close 21)))))))) (.step 7 (.step 18 (.step 29 (.step 38 (.step 40 (.step 53 (.step 7 (.step 26 (.close 15)))))))))) (.step 7 (.step 57 (.step 7 (.step 29 (.step 26 (.step 37 (.step 26 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52))))))))))))))
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
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708476788654836675481782715456012372745323136743463190283511220663410171464854510199672003689493519654899941376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 18 (.step 21 (.step 29 (.step 7 (.step 4 (.step 7 (.close 22))))))))) (.step 9 (.step 29 (.step 7 (.step 15 (.step 18 (.step 21 (.step 7 (.close 16))))))))) (.step 29 (.step 26 (.close 38)))) (.step 18 (.step 40 (.step 7 (.step 29 (.step 7 (.step 15 (.step 17 (.close 18))))))))) (.step 18 (.step 40 (.split 72 1 (.step 18 (.close 7)) (.step 29 (.step 18 (.close 7))))))) (.step 7 (.step 18 (.step 29 (.step 7 (.close 15)))))) (.step 4 (.step 57 (.step 9 (.step 21 (.step 29 (.step 7 (.step 26 (.step 7 (.close 15)))))))))) (.step 4 (.step 29 (.step 38 (.close 71))))) (.step 7 (.step 9 (.step 21 (.step 26 (.step 29 (.step 38 (.step 22 (.step 38 (.close 15)))))))))) (.step 4 (.step 21 (.step 53 (.close 71))))) (.step 4 (.step 63 (.step 15 (.step 71 (.step 10 (.close 22))))))) (.step 9 (.step 21 (.step 26 (.step 71 (.step 75 (.step 53 (.step 18 (.step 26 (.step 29 (.step 7 (.close 15)))))))))))) (.step 9 (.step 21 (.step 29 (.step 38 (.step 57 (.step 4 (.close 7)))))))) (.step 22 (.step 53 (.step 57 (.step 7 (.step 9 (.step 21 (.step 62 (.step 38 (.step 15 (.step 26 (.step 29 (.step 38 (.step 52 (.close 54))))))))))))))) (.step 9 (.step 21 (.step 38 (.step 18 (.step 21 (.close 26))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900805023143666420641368808316375630233617763844415079539068390152392201374349327560016161406976⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 9 (.step 21 (.step 53 (.step 57 (.step 62 (.step 71 (.split 51 1 (.split 67 1 (.split 72 1 (.step 53 (.step 18 (.step 29 (.step 52 (.close 7))))) (.step 21 (.step 26 (.step 18 (.step 29 (.step 7 (.step 16 (.step 22 (.close 38))))))))) (.step 7 (.step 21 (.step 26 (.step 29 (.close 52)))))) (.step 7 (.step 21 (.step 22 (.close 52))))))))))))) (.run (.step 9 (.step 7 (.close 10))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 41 (.step 29 (.split 54 1 (.split 59 1 (.split 61 1 (.step 38 (.step 7 (.step 21 (.step 26 (.step 7 (.step 4 (.close 15))))))) (.step 4 (.step 7 (.step 15 (.step 21 (.step 26 (.step 31 (.close 38)))))))) (.step 7 (.step 21 (.step 15 (.close 26))))) (.step 21 (.step 26 (.step 7 (.step 31 (.step 7 (.step 15 (.close 37)))))))))) (.step 7 (.step 21 (.close 26)))) (.step 7 (.step 21 (.step 26 (.step 29 (.step 15 (.step 37 (.close 38))))))))))) (.run (.step 7 (.step 57 (.step 29 (.split 42 1 (.split 49 1 (.split 50 1 (.step 41 (.step 38 (.step 7 (.step 21 (.close 38))))) (.step 7 (.close 21))) (.step 7 (.step 21 (.step 37 (.close 26))))) (.step 38 (.step 7 (.step 4 (.step 15 (.close 21)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404237493564800576407531008687456712405981797679699443800530339070143728521538837511041863665328091359348635365218577103545962594304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.step 7 (.step 21 (.close 7))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 4 (.step 15 (.step 4 (.step 21 (.close 26))))))) (.step 7 (.step 4 (.step 15 (.step 21 (.step 26 (.step 21 (.close 28)))))))) (.step 4 (.step 7 (.step 28 (.step 15 (.step 21 (.step 26 (.step 21 (.close 31))))))))) (.step 7 (.step 4 (.step 15 (.step 21 (.step 28 (.step 26 (.step 31 (.step 26 (.close 37)))))))))) (.step 7 (.step 15 (.close 31)))) (.step 7 (.step 15 (.step 21 (.close 26))))) (.step 15 (.step 29 (.step 7 (.step 31 (.step 7 (.step 21 (.close 26)))))))) (.step 7 (.step 15 (.step 7 (.step 21 (.step 26 (.step 29 (.step 26 (.close 52))))))))) (.step 7 (.step 15 (.step 52 (.step 7 (.step 26 (.step 29 (.step 21 (.step 26 (.close 21)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404240201250048741265792315732558414636160934825280865496404528991609172487659741442314363640334052433155371098823031599221576826880⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.reuse 0) (.run (.step 37 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.step 7 (.step 21 (.close 7))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 15 (.step 4 (.step 21 (.close 26)))))) (.step 7 (.step 4 (.step 15 (.step 26 (.step 21 (.close 28))))))) (.step 7 (.step 28 (.step 31 (.step 15 (.step 21 (.close 26))))))) (.step 7 (.step 15 (.step 31 (.close 64))))) (.step 7 (.step 15 (.step 26 (.step 21 (.close 29)))))) (.step 15 (.step 29 (.step 7 (.step 26 (.step 31 (.step 7 (.step 21 (.close 37))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.close 52))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 38 (.close 52))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642982827354223862921937252594497275730852413379315068640032182023572362319730205053287768522752⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.step 7 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 37 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.step 7 (.step 21 (.close 7))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 15 (.step 4 (.step 21 (.close 26)))))) (.step 7 (.step 4 (.step 15 (.step 28 (.step 21 (.close 26))))))) (.step 7 (.step 28 (.step 31 (.step 15 (.step 21 (.close 26))))))) (.step 7 (.step 15 (.step 31 (.close 64))))) (.step 7 (.step 15 (.step 26 (.step 21 (.close 29)))))) (.step 15 (.step 29 (.step 7 (.step 31 (.step 7 (.step 21 (.step 26 (.step 21 (.close 37)))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.close 52))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 38 (.close 52)))))))))) (.run (.step 15 (.step 29 (.step 37 (.split 49 1 (.split 50 1 (.step 41 (.step 38 (.step 7 (.step 15 (.step 21 (.step 31 (.step 7 (.close 26)))))))) (.step 7 (.step 15 (.close 21)))) (.step 7 (.step 15 (.step 21 (.step 26 (.step 37 (.close 26)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200197408023521040185685109013464847708734576282818164021716701029968389993951920128⟩
def references : Fin 4 → Box := ![Part10.root, Part11.root, Part13.root, Part16.root]
def proof : Chunks.Proof 4 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.step 7 (.split 42 1 (.reuse 1) (.run (.split 49 1 (.split 50 1 (.step 39 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 26 (.step 31 (.close 15)))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 26 (.step 4 (.close 15))))) (.step 7 (.step 4 (.step 26 (.step 28 (.step 15 (.close 21))))))) (.step 7 (.step 28 (.step 31 (.step 15 (.close 39)))))) (.step 7 (.step 28 (.step 31 (.step 39 (.step 41 (.step 57 (.close 64)))))))) (.step 7 (.step 26 (.step 29 (.step 15 (.close 21)))))) (.step 29 (.step 31 (.step 39 (.close 37)))))) (.step 7 (.step 26 (.step 29 (.step 38 (.step 37 (.step 26 (.step 37 (.step 39 (.close 53)))))))))) (.step 7 (.step 26 (.step 29 (.step 52 (.step 26 (.step 37 (.close 21)))))))))))) (.reuse 2)) (.reuse 3)) (.run (.step 7 (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 15))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 7 (.step 9 (.step 18 (.close 52))))))) (.step 7 (.step 18 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part13.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨3705346855594118253554271520278013051304639509300498049262642688253222295961600, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635118923331810137237600799138147622081096436861733071963888564992284536139287625728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.step 29 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.step 7 (.step 9 (.step 29 (.step 7 (.step 21 (.close 22)))))) (.step 9 (.step 15 (.step 18 (.step 29 (.close 16)))))) (.step 7 (.step 9 (.step 15 (.step 7 (.close 18)))))) (.step 9 (.step 18 (.step 4 (.close 15))))) (.step 18 (.step 7 (.close 4)))) (.step 18 (.step 7 (.close 4))))) (.step 4 (.step 10 (.step 29 (.step 57 (.close 71)))))) (.step 4 (.close 29))) (.step 7 (.step 9 (.step 26 (.step 71 (.step 21 (.close 29))))))) (.step 4 (.step 10 (.step 71 (.step 15 (.close 21)))))) (.step 4 (.step 63 (.step 10 (.step 15 (.step 71 (.close 22))))))) (.step 9 (.step 26 (.step 29 (.step 27 (.step 26 (.step 18 (.step 62 (.step 7 (.step 29 (.step 15 (.step 21 (.step 29 (.step 57 (.close 64))))))))))))))) (.step 9 (.step 29 (.step 57 (.step 29 (.close 4)))))) (.step 22 (.step 57 (.step 7 (.step 46 (.step 62 (.step 70 (.step 71 (.step 21 (.close 26)))))))))) (.step 9 (.step 29 (.step 27 (.step 53 (.step 57 (.step 71 (.split 10 0 (.step 21 (.step 18 (.split 61 0 (.split 68 0 (.step 53 (.step 7 (.close 15))) (.step 18 (.step 29 (.close 22)))) (.step 15 (.step 7 (.step 52 (.step 29 (.close 22)))))))) (.step 15 (.step 7 (.close 18))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838929808552846139973881948671541299731373062858760098296673001799680⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 26 1 (.reuse 0) (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 1) (.run (.step 9 (.step 29 (.step 27 (.step 52 (.step 57 (.step 71 (.split 10 0 (.split 34 0 (.split 30 0 (.split 62 0 (.split 68 0 (.step 52 (.step 7 (.step 21 (.close 26)))) (.step 18 (.step 29 (.close 22)))) (.step 18 (.step 21 (.step 16 (.close 52))))) (.step 18 (.close 21))) (.step 15 (.step 18 (.step 21 (.close 26))))) (.step 15 (.step 7 (.close 18)))))))))))) (.run (.step 9 (.step 7 (.close 10))))) (.run (.step 7 (.step 28 (.close 29))))) (.run (.step 7 (.step 28 (.close 29))))) (.run (.step 9 (.step 29 (.split 51 1 (.split 67 1 (.split 16 0 (.step 29 (.step 4 (.step 9 (.step 15 (.close 21))))) (.step 4 (.step 18 (.close 29)))) (.step 7 (.step 9 (.step 21 (.step 26 (.step 29 (.close 22))))))) (.step 7 (.step 9 (.step 21 (.step 22 (.close 29)))))))))) (.run (.step 7 (.step 15 (.step 28 (.close 29)))))) (.run (.step 7 (.step 18 (.step 7 (.step 9 (.step 18 (.close 29))))))))) (.run (.step 7 (.step 18 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 4))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 26 (.step 7 (.step 18 (.close 7))))))) (.step 4 (.step 5 (.step 4 (.step 18 (.close 7)))))) (.step 4 (.step 5 (.step 4 (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403461179924103640723857081878045594625731876536350408704⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.step 18 (.step 4 (.split 62 1 (.split 67 1 (.split 69 1 (.split 72 1 (.step 68 (.close 4)) (.step 4 (.step 7 (.step 15 (.step 7 (.close 17)))))) (.step 4 (.close 7))) (.step 7 (.step 4 (.close 9)))) (.step 4 (.step 7 (.close 10)))))) (.step 4 (.step 31 (.step 5 (.step 10 (.step 34 (.step 18 (.step 4 (.close 22))))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 26)))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 57)))))) (.step 4 (.step 7 (.step 22 (.close 54))))) (.step 4 (.step 9 (.step 18 (.step 26 (.close 53)))))) (.step 4 (.step 9 (.step 18 (.close 52))))) (.step 4 (.step 7 (.step 9 (.close 10))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 4 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 4 (.step 26 (.step 29 (.step 15 (.close 26)))))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.step 29 (.step 26 (.close 38)))))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 31 (.step 15 (.step 29 (.step 26 (.close 37)))))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 29))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196339712625598120978747303210563859767883068238063247922252687710509803881143276663603870799123229520389791497937122495231799693097580036285425429644749402601393520447058134507833343868928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 68 0 (.split 72 0 (.split 17 0 (.split 36 0 (.split 16 0 (.step 15 (.split 22 0 (.step 9 (.step 7 (.close 15))) (.step 4 (.close 7)))) (.step 4 (.close 7))) (.step 7 (.step 9 (.close 15)))) (.step 4 (.close 7))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 4 (.step 9 (.close 15))))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 9 (.step 15 (.close 7)))) (.step 9 (.step 15 (.step 4 (.close 7))))) (.step 9 (.step 15 (.step 4 (.close 7))))) (.step 4 (.step 15 (.step 10 (.step 15 (.step 7 (.close 16))))))) (.step 4 (.step 9 (.step 15 (.step 29 (.step 15 (.step 7 (.step 16 (.close 22))))))))) (.step 15 (.split 68 1 (.split 69 1 (.split 10 0 (.step 26 (.split 16 0 (.split 21 0 (.split 26 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 4 (.close 7))) (.step 4 (.close 7)))) (.step 7 (.step 9 (.close 15)))) (.step 4 (.step 10 (.step 15 (.step 16 (.step 15 (.step 7 (.step 15 (.close 22))))))))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 16 (.step 22 (.close 26)))))))))) (.step 4 (.step 15 (.step 16 (.step 10 (.step 21 (.step 64 (.step 71 (.step 72 (.step 15 (.step 7 (.step 15 (.close 22))))))))))))) (.step 4 (.step 15 (.step 16 (.step 64 (.step 4 (.step 9 (.close 15)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677468650784044688730830927487303680⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.reuse 0) (.run (.step 9 (.step 15 (.step 26 (.step 4 (.step 16 (.step 7 (.step 22 (.step 7 (.close 53))))))))))) (.run (.step 9 (.step 15 (.close 4))))) (.run (.step 15 (.step 22 (.step 57 (.step 62 (.step 64 (.step 70 (.split 68 1 (.split 16 0 (.step 22 (.split 21 0 (.split 62 1 (.step 15 (.close 54)) (.step 4 (.step 10 (.step 15 (.step 7 (.close 16)))))) (.step 4 (.close 7)))) (.step 4 (.close 7))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 16 (.close 26))))))))))))))) (.run (.step 9 (.step 15 (.step 21 (.close 53)))))) (.run (.step 9 (.step 15 (.step 16 (.close 52)))))) (.run (.step 9 (.step 10 (.step 7 (.step 27 (.step 10 (.close 7)))))))) (.run (.step 7 (.step 15 (.step 7 (.step 15 (.close 26))))))) (.run (.step 7 (.step 15 (.step 29 (.step 31 (.step 37 (.step 7 (.step 15 (.close 7)))))))))) (.run (.step 9 (.step 15 (.step 21 (.step 15 (.step 29 (.step 7 (.step 22 (.close 26)))))))))) (.run (.step 7 (.step 15 (.step 7 (.close 15)))))) (.run (.step 7 (.step 15 (.step 18 (.close 15)))))) (.run (.step 9 (.step 15 (.step 18 (.step 29 (.close 4))))))) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.step 18 (.close 15))))))))) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.close 7))))))) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.step 18 (.close 15))))))))) (.run (.step 4 (.step 5 (.step 7 (.step 18 (.close 15)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677468650784044688730830927487303680⟩
def references : Fin 2 → Box := ![Part20.root, Part22.root]
def proof : Chunks.Proof 2 := (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 4))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 22 (.step 7 (.step 18 (.close 7))))))) (.step 4 (.step 5 (.step 4 (.step 18 (.close 7)))))) (.step 4 (.step 5 (.step 4 (.step 18 (.step 22 (.step 7 (.step 18 (.close 7))))))))) (.step 7 (.step 18 (.split 26 1 (.step 18 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))) (.step 5 (.step 4 (.step 18 (.close 29)))))))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 4))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 21 (.step 7 (.step 18 (.close 7))))))) (.step 4 (.step 5 (.step 4 (.step 18 (.close 7)))))) (.step 4 (.step 5 (.step 4 (.step 18 (.step 21 (.step 7 (.step 18 (.close 7))))))))) (.step 7 (.step 18 (.split 26 1 (.step 18 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))) (.step 5 (.step 4 (.step 18 (.close 29)))))))) (.step 7 (.step 18 (.step 19 (.split 26 1 (.step 18 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))) (.step 5 (.step 4 (.step 18 (.close 29))))))))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644916960232424190509056⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 15))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18)))))))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18)))))))) (.step 15 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part24

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part24.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case143

namespace FiveColour.Packed.EnumerationChunks.Projected.Case143
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 30 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 30 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 30 0).upper i := by decide +kernel
lemma budget_model : (⟨32016031753816107707383, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699533605928482613073959526943958677216822273, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 30), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32016031753816107707383, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699533605928482613073959526943958677216822273, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 30) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 30 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 30 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 30) (Archive.root 30) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 30 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 30 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case143

namespace FiveColour.Packed.EnumerationChunks.Case143
def root : Box := Archive.root 30
def families : Fin 78 → List Cut := Enumeration.families 30
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case143.original_covered points
end FiveColour.Packed.EnumerationChunks.Case143
