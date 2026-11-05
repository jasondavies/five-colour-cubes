module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case30
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644916960232424190509056⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32016031753816107707383, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699533605928482613073959526943958677216822273, 0⟩]
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
def root : Box := ⟨2147483648, 11031304536487720240955970973191984381084500630769492679916833617023780404672701586152017245777266494690284288273142738280548349377904898996149901186905957742528827836922267365818862057087458319110335006304712892874752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.step 71 (.split 69 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 7 (.split 16 0 (.step 7 (.step 9 (.step 40 (.step 7 (.step 21 (.close 22)))))) (.step 7 (.close 4)))) (.split 21 0 (.split 26 0 (.split 35 0 (.split 68 0 (.step 7 (.step 4 (.close 9))) (.step 4 (.step 7 (.step 9 (.close 15))))) (.step 7 (.step 9 (.step 15 (.close 16))))) (.step 7 (.step 9 (.step 15 (.step 7 (.step 18 (.step 16 (.close 21)))))))) (.step 7 (.step 9 (.step 7 (.step 15 (.step 7 (.step 4 (.close 17))))))))) (.step 7 (.close 9))) (.step 7 (.step 29 (.step 18 (.step 26 (.step 40 (.step 7 (.step 15 (.step 16 (.close 21)))))))))) (.step 71 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 72 (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 7 (.close 4))) (.step 4 (.split 16 0 (.step 4 (.step 10 (.step 22 (.step 7 (.step 15 (.step 7 (.step 16 (.close 21)))))))) (.step 4 (.close 7))))) (.step 7 (.step 9 (.close 15))))))) (.step 70 (.step 71 (.split 69 1 (.step 7 (.step 26 (.step 15 (.step 29 (.step 15 (.step 16 (.close 21))))))) (.step 70 (.step 4 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712625598120978747303210563859767883068238063247922252687710509803881143276663603870799123229520389791497937122495231799693097580036285425429644748073373397735531185230700773063524352⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 61 1 (.split 62 1 (.reuse 0) (.run (.split 68 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.step 72 (.split 17 0 (.split 36 0 (.step 65 (.step 4 (.step 7 (.close 9)))) (.step 7 (.step 10 (.step 4 (.step 7 (.step 15 (.step 7 (.close 22)))))))) (.step 7 (.step 4 (.close 27))))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.step 72 (.step 4 (.split 16 0 (.split 17 0 (.step 4 (.step 10 (.step 21 (.step 64 (.step 7 (.step 22 (.close 26))))))) (.step 4 (.close 7))) (.step 4 (.close 7)))))) (.step 7 (.step 53 (.step 7 (.step 9 (.step 52 (.close 9))))))) (.step 4 (.step 10 (.step 21 (.step 26 (.step 65 (.close 7))))))) (.step 63 (.step 65 (.step 9 (.step 21 (.step 29 (.step 7 (.step 26 (.close 65))))))))))) (.run (.split 68 1 (.split 72 1 (.split 12 0 (.split 16 0 (.split 67 1 (.split 10 0 (.step 72 (.split 17 0 (.step 64 (.split 21 0 (.step 64 (.step 4 (.step 7 (.close 9)))) (.step 4 (.close 7)))) (.step 7 (.step 4 (.close 27))))) (.step 7 (.step 52 (.close 21)))) (.step 64 (.step 7 (.close 9)))) (.step 7 (.step 30 (.step 4 (.step 7 (.step 36 (.close 44))))))) (.step 64 (.step 4 (.split 10 0 (.split 16 0 (.step 4 (.step 10 (.step 15 (.close 7)))) (.step 4 (.close 7))) (.step 7 (.step 9 (.close 15))))))) (.step 4 (.step 10 (.step 15 (.step 64 (.step 7 (.step 26 (.step 7 (.step 52 (.step 21 (.step 29 (.step 21 (.close 22))))))))))))) (.step 63 (.close 64)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384264315699200, 11031304536487720240955970973196339712629650382276482651495742168706826074048029646094712429591419507633702611280353747000311757972567493802279239626988333839970241307824223340035469193974026904401143060747788434276352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 72 1 (.split 12 0 (.split 67 1 (.split 21 0 (.split 26 0 (.split 69 1 (.split 35 0 (.step 54 (.step 7 (.close 9))) (.step 7 (.step 9 (.close 21)))) (.step 4 (.step 9 (.step 22 (.step 7 (.step 31 (.step 21 (.close 26)))))))) (.step 7 (.step 9 (.step 18 (.step 29 (.step 22 (.step 29 (.step 7 (.step 21 (.close 26)))))))))) (.step 4 (.step 7 (.step 9 (.step 7 (.step 18 (.close 4))))))) (.step 26 (.step 54 (.step 57 (.step 7 (.step 4 (.close 9))))))) (.step 9 (.step 15 (.close 57)))) (.step 9 (.step 26 (.step 29 (.close 57))))) (.step 4 (.step 9 (.step 29 (.step 57 (.close 7)))))) (.step 4 (.step 21 (.step 10 (.step 57 (.step 7 (.close 26))))))) (.step 4 (.step 15 (.step 10 (.step 57 (.step 52 (.step 53 (.step 7 (.step 26 (.step 53 (.close 57))))))))))) (.step 9 (.step 26 (.step 57 (.step 4 (.step 7 (.close 52))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172058778056533678920988218679142881039503544066428452091431202118903008501320665983827456908381696098230332187886656981907412497607387785547356200685797376⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 51 1 (.split 54 1 (.split 59 1 (.reuse 0) (.run (.split 68 1 (.split 72 1 (.split 16 0 (.split 61 1 (.step 62 (.step 70 (.split 62 1 (.split 21 0 (.split 26 0 (.step 7 (.split 35 0 (.step 7 (.step 4 (.close 9))) (.step 4 (.step 7 (.step 9 (.close 15)))))) (.step 7 (.step 9 (.step 15 (.close 21))))) (.step 7 (.close 4))) (.step 53 (.step 65 (.step 4 (.close 7))))))) (.step 52 (.step 64 (.step 62 (.step 64 (.step 4 (.close 7))))))) (.step 7 (.step 18 (.step 4 (.step 27 (.step 36 (.close 44))))))) (.step 9 (.step 18 (.close 26)))) (.step 18 (.step 26 (.step 62 (.step 15 (.step 21 (.step 15 (.close 29)))))))))) (.reuse 1)) (.run (.step 54 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 54 1 (.step 54 (.step 7 (.step 15 (.step 22 (.step 15 (.step 16 (.close 21))))))) (.step 22 (.step 9 (.step 54 (.close 21))))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.step 9 (.step 22 (.step 26 (.step 29 (.step 15 (.step 53 (.close 15))))))))) (.step 22 (.step 54 (.step 4 (.close 7))))) (.step 7 (.step 54 (.step 22 (.step 26 (.step 15 (.step 16 (.close 21)))))))) (.step 54 (.step 7 (.step 15 (.step 21 (.step 15 (.close 22))))))) (.step 54 (.step 64 (.step 54 (.step 4 (.step 7 (.close 15))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434276803595271946858057795038993245151143890047831291497731209822335181667471539403261542233562010298803559802660766531613682854526976⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 53 (.split 51 1 (.split 61 1 (.step 53 (.split 54 1 (.split 68 1 (.split 72 1 (.step 53 (.step 70 (.step 7 (.step 9 (.step 15 (.close 21)))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 7 (.close 53))))))) (.step 18 (.step 53 (.close 15)))) (.step 9 (.step 21 (.step 53 (.step 57 (.step 4 (.close 7)))))))) (.step 52 (.step 53 (.step 64 (.step 53 (.step 70 (.step 4 (.step 71 (.step 4 (.step 9 (.step 7 (.step 15 (.close 22))))))))))))) (.step 53 (.step 7 (.step 9 (.step 27 (.close 52))))))))) (.run (.step 52 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 54 1 (.split 72 1 (.split 69 1 (.split 10 0 (.split 12 0 (.split 16 0 (.step 52 (.step 7 (.close 9))) (.step 7 (.step 18 (.close 4)))) (.step 9 (.step 52 (.step 7 (.close 4))))) (.step 7 (.step 9 (.close 15)))) (.step 52 (.step 4 (.step 7 (.step 9 (.step 16 (.close 21))))))) (.step 9 (.step 18 (.step 26 (.step 7 (.step 16 (.close 52))))))) (.step 9 (.step 57 (.step 4 (.close 7))))) (.step 18 (.step 52 (.step 16 (.step 21 (.close 29)))))) (.step 52 (.close 7))) (.step 52 (.step 53 (.step 64 (.step 65 (.step 70 (.step 4 (.step 7 (.step 9 (.step 22 (.step 29 (.step 22 (.close 52))))))))))))) (.step 52 (.close 4))) (.step 52 (.step 7 (.step 9 (.step 27 (.close 53)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775634760222489937077507659088225070488340760282950142123626984284248373879371035595913283986632153017893626314752⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 54 (.step 70 (.split 49 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 9 (.split 50 1 (.step 46 (.close 9)) (.step 9 (.step 7 (.close 46))))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.step 4 (.close 9)))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.close 9))) (.step 10 (.step 30 (.close 46)))) (.step 7 (.step 9 (.close 46)))) (.step 10 (.step 30 (.close 46)))) (.step 10 (.step 30 (.close 46)))) (.step 9 (.step 27 (.close 46)))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 26 (.step 7 (.close 15)))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 4 (.close 26)))) (.step 7 (.step 4 (.step 26 (.step 15 (.close 21)))))) (.step 4 (.step 7 (.step 26 (.step 15 (.step 28 (.step 15 (.close 21)))))))) (.step 7 (.step 4 (.step 21 (.step 26 (.step 15 (.step 28 (.step 15 (.close 31))))))))) (.step 7 (.step 4 (.step 15 (.step 26 (.step 28 (.step 21 (.close 31)))))))) (.step 7 (.step 26 (.step 15 (.close 21))))) (.step 7 (.step 21 (.step 26 (.step 15 (.close 29)))))) (.step 7 (.step 18 (.step 26 (.step 29 (.step 40 (.step 45 (.step 18 (.step 21 (.step 15 (.step 26 (.step 15 (.close 52)))))))))))))))) (.run (.step 7 (.step 18 (.step 7 (.close 18))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279576264966067672917373455470886850837397996517488209608467242712361277947626152622171047355037314470142001941746488295637515239424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 68 1 (.split 69 1 (.step 29 (.step 7 (.step 18 (.step 21 (.step 7 (.step 26 (.step 7 (.step 4 (.step 7 (.close 15)))))))))) (.step 4 (.step 9 (.step 21 (.step 22 (.step 29 (.step 7 (.step 26 (.step 7 (.close 15)))))))))) (.step 4 (.step 29 (.step 21 (.close 38))))) (.step 4 (.step 18 (.step 7 (.close 4))))) (.step 4 (.step 18 (.step 7 (.close 4))))) (.step 18 (.step 7 (.step 15 (.step 21 (.close 28)))))) (.step 7 (.step 9 (.step 21 (.step 26 (.step 29 (.step 38 (.close 15)))))))) (.step 4 (.step 21 (.step 7 (.step 9 (.step 7 (.close 21))))))) (.step 4 (.step 15 (.step 10 (.close 71))))) (.step 9 (.step 21 (.step 26 (.step 53 (.step 18 (.step 26 (.step 7 (.step 29 (.step 15 (.step 16 (.step 15 (.step 22 (.close 38)))))))))))))) (.step 9 (.step 21 (.step 29 (.step 38 (.step 57 (.close 4))))))) (.step 7 (.step 22 (.step 9 (.step 21 (.step 54 (.step 26 (.step 29 (.step 38 (.step 15 (.close 52))))))))))) (.step 9 (.step 21 (.step 18 (.close 21))))) (.step 9 (.step 21 (.step 52 (.step 53 (.step 29 (.step 18 (.step 57 (.step 38 (.step 7 (.step 16 (.step 22 (.step 26 (.close 38)))))))))))))) (.step 7 (.step 9 (.close 10)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404240201250048741265792315732558414636160934825280865496404528991609172487659741442314363640334052433155371098823031599221576826880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.step 7 (.step 21 (.close 7))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 4 (.step 15 (.step 4 (.step 21 (.close 26))))))) (.step 7 (.step 4 (.step 15 (.step 21 (.step 26 (.step 21 (.close 28)))))))) (.step 4 (.step 7 (.step 15 (.step 28 (.step 21 (.step 26 (.step 21 (.close 31))))))))) (.step 7 (.step 4 (.step 15 (.step 21 (.step 28 (.step 26 (.close 31)))))))) (.step 7 (.step 4 (.close 15)))) (.step 7 (.step 15 (.step 21 (.close 26))))) (.step 7 (.step 15 (.step 21 (.step 26 (.close 29)))))) (.step 7 (.step 15 (.step 7 (.step 29 (.step 26 (.step 21 (.step 26 (.close 52))))))))) (.step 37 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 54 1 (.step 7 (.step 15 (.step 26 (.step 7 (.close 4))))) (.step 15 (.step 7 (.step 26 (.step 29 (.step 7 (.close 4))))))) (.step 7 (.step 4 (.step 15 (.step 21 (.step 26 (.step 21 (.close 28)))))))) (.step 7 (.step 4 (.step 15 (.step 21 (.step 26 (.step 28 (.close 31)))))))) (.step 7 (.step 15 (.close 31)))) (.step 7 (.step 15 (.step 21 (.step 26 (.step 21 (.close 29))))))) (.step 7 (.step 15 (.step 21 (.step 26 (.step 29 (.close 37))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.close 52)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200197408023521040185685109013464847708734576282818165289367301258197791490655125504⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 3 := (.split 34 1 (.split 35 1 (.split 36 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 7 (.step 15 (.close 18))))))) (.run (.step 7 (.split 42 1 (.step 57 (.step 7 (.step 57 (.step 71 (.step 29 (.step 31 (.step 7 (.step 15 (.step 21 (.step 15 (.close 26))))))))))) (.split 49 1 (.step 39 (.split 50 1 (.step 39 (.step 7 (.step 40 (.step 57 (.step 26 (.step 29 (.step 7 (.close 15)))))))) (.step 7 (.step 21 (.step 26 (.step 15 (.step 29 (.step 15 (.close 37))))))))) (.step 7 (.step 26 (.step 29 (.step 37 (.step 21 (.step 26 (.step 21 (.close 52))))))))))))) (.split 10 1 (.split 30 1 (.split 36 1 (.split 42 1 (.reuse 1) (.run (.step 7 (.step 29 (.split 49 1 (.step 41 (.step 38 (.step 7 (.step 21 (.step 26 (.step 7 (.step 4 (.close 15)))))))) (.step 7 (.step 21 (.step 26 (.step 15 (.close 37)))))))))) (.run (.step 7 (.step 29 (.step 57 (.step 38 (.step 7 (.step 21 (.close 38))))))))) (.run (.step 7 (.close 18)))) (.run (.step 7 (.step 15 (.step 7 (.close 18))))))) (.step 7 (.split 35 1 (.split 36 1 (.reuse 2) (.run (.step 37 (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 15 (.step 40 (.step 15 (.step 29 (.step 31 (.step 21 (.close 7))))))))) (.step 7 (.step 15 (.step 21 (.step 26 (.step 29 (.close 37))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.close 52))))))))) (.run (.step 15 (.step 29 (.step 37 (.step 38 (.step 7 (.step 15 (.step 21 (.step 7 (.close 26)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838929808552846139973881948671541299732640713458988327698169705005056⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.reuse 0) (.run (.split 10 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 29 (.step 71 (.step 7 (.split 67 1 (.step 29 (.step 7 (.close 15))) (.step 7 (.step 9 (.step 26 (.step 29 (.close 15))))))))) (.step 4 (.step 10 (.step 71 (.close 15))))) (.step 4 (.step 10 (.step 15 (.close 71))))) (.step 9 (.step 26 (.step 27 (.step 26 (.step 18 (.step 29 (.step 62 (.step 7 (.step 15 (.step 21 (.step 15 (.close 29))))))))))))) (.step 9 (.step 29 (.step 40 (.close 57))))) (.step 7 (.step 22 (.step 9 (.step 57 (.step 54 (.step 29 (.step 54 (.step 15 (.step 21 (.close 16))))))))))) (.step 9 (.step 27 (.step 29 (.step 21 (.step 53 (.step 18 (.step 57 (.step 53 (.step 7 (.close 15))))))))))) (.step 9 (.step 27 (.step 29 (.step 52 (.step 57 (.step 18 (.step 52 (.step 7 (.step 16 (.close 21))))))))))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 28 (.close 29)))) (.step 7 (.step 28 (.close 29)))) (.step 9 (.step 29 (.step 4 (.step 21 (.close 22)))))) (.step 7 (.step 15 (.step 28 (.close 29))))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.close 7)))))) (.run (.step 7 (.step 18 (.step 7 (.close 18))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904899348241922649729044056425363910164480⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 7 (.step 18 (.step 4 (.step 40 (.step 68 (.step 4 (.step 9 (.close 10)))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.step 15 (.step 7 (.step 18 (.close 26))))))))) (.step 4 (.step 7 (.step 22 (.step 4 (.step 9 (.close 26))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.step 26 (.close 53))))))) (.step 4 (.step 9 (.step 18 (.step 26 (.close 52)))))) (.step 4 (.step 7 (.step 9 (.close 10))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 15 (.close 26))))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 4 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 18 (.step 26 (.step 29 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 4 (.step 15 (.step 26 (.step 29 (.step 26 (.close 37))))))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 29)))))))))) (.run (.step 7 (.step 18 (.step 7 (.close 18)))))) (.run (.step 7 (.step 18 (.step 7 (.step 18 (.close 19)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196339712629650382276482647896611136427497537563659780285494091876893621196242330630456352982172918290163927607689388369481811555794123906562598970073420666856128396028790964168216964759552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 43 1 (.split 51 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 67 1 (.split 34 0 (.split 69 1 (.split 35 0 (.split 17 0 (.step 15 (.step 7 (.step 4 (.close 9)))) (.step 4 (.close 7))) (.step 7 (.step 9 (.close 15)))) (.step 4 (.step 9 (.step 15 (.close 7))))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 26 (.step 70 (.close 7)))) (.step 9 (.step 15 (.step 7 (.close 15))))) (.step 4 (.step 7 (.step 9 (.step 15 (.close 4)))))) (.step 9 (.step 15 (.step 4 (.close 7))))) (.step 4 (.step 9 (.step 15 (.step 7 (.step 16 (.close 22))))))) (.step 4 (.step 15 (.step 10 (.step 15 (.step 16 (.step 15 (.step 7 (.step 22 (.step 7 (.close 26))))))))))) (.step 4 (.step 15 (.step 7 (.step 10 (.step 7 (.step 16 (.close 22)))))))) (.step 15 (.step 22 (.step 54 (.step 22 (.step 54 (.step 15 (.step 4 (.step 7 (.close 15)))))))))) (.step 9 (.step 10 (.step 4 (.step 7 (.step 4 (.close 10))))))) (.step 9 (.step 15 (.step 26 (.step 4 (.step 16 (.step 7 (.close 22)))))))) (.step 9 (.step 15 (.step 21 (.close 53))))) (.step 9 (.step 15 (.step 16 (.close 52))))) (.step 7 (.step 15 (.step 7 (.step 4 (.close 15)))))) (.step 7 (.step 15 (.step 7 (.step 15 (.close 26)))))) (.step 9 (.step 15 (.step 7 (.step 18 (.step 21 (.step 22 (.close 26)))))))) (.step 7 (.step 15 (.close 7)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644916960232424190509056⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 12 1 (.reuse 0) (.split 10 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 15 (.step 18 (.split 26 1 (.reuse 1) (.run (.step 9 (.step 15 (.close 29))))))) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.step 7 (.step 15 (.step 17 (.step 15 (.close 18)))))))))))) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.close 7))))))) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.close 18)))))))) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.close 18)))))))) (.run (.step 7 (.step 15 (.step 4 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case30
