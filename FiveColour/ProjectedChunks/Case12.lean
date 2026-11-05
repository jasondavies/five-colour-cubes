module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644919266077632427458560⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32016031753816107707303, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697928522998852134929247591988189268012958721, 0⟩]
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
def root : Box := ⟨2147483648, 11031304536487720240955970973191984381084500630769492679916833617023780404672701586152017245777266494690284288273142738280548349377904898996149901186905957742528827836922267365818862057087458319110336159227317011349504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.step 71 (.split 69 1 (.split 72 1 (.split 6 0 (.step 7 (.step 18 (.step 9 (.step 40 (.step 7 (.step 15 (.step 16 (.close 21)))))))) (.split 16 0 (.split 21 0 (.split 26 0 (.split 35 0 (.split 68 0 (.step 7 (.step 4 (.close 9))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 4 (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 18 (.step 26 (.step 29 (.step 4 (.step 7 (.close 15))))))))) (.step 71 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.step 7 (.step 4 (.step 7 (.step 9 (.step 21 (.close 22)))))) (.step 4 (.step 9 (.step 7 (.step 15 (.step 7 (.step 16 (.close 21)))))))) (.step 7 (.close 9))) (.step 4 (.step 10 (.step 4 (.step 9 (.close 7)))))) (.step 7 (.close 9)))))) (.step 70 (.step 71 (.split 72 1 (.split 6 0 (.step 7 (.step 15 (.step 26 (.step 15 (.step 16 (.close 21)))))) (.step 46 (.step 70 (.step 7 (.step 4 (.step 9 (.close 7))))))) (.step 7 (.step 9 (.step 26 (.step 15 (.step 29 (.step 15 (.step 16 (.close 21)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304536487720240955970973196335463521655586841957790104042475653421537741552237815652579253161895294197696326266415588575172223294736638533781406336362640399607321444226252051530785070021936087831845169756012281856⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 54 1 (.split 62 1 (.reuse 0) (.run (.step 71 (.split 4 0 (.split 6 0 (.split 10 0 (.step 65 (.split 12 0 (.split 67 1 (.step 7 (.step 4 (.step 7 (.step 9 (.step 21 (.close 22)))))) (.step 65 (.step 4 (.close 7)))) (.step 4 (.split 67 1 (.step 4 (.step 9 (.step 7 (.step 15 (.step 7 (.step 16 (.close 21))))))) (.step 10 (.step 4 (.step 21 (.step 26 (.step 7 (.step 15 (.close 16))))))))))) (.step 7 (.step 9 (.step 52 (.close 9))))) (.step 10 (.step 4 (.step 65 (.split 67 1 (.step 4 (.step 9 (.close 7))) (.step 10 (.close 7))))))) (.step 7 (.step 53 (.step 7 (.step 9 (.close 15))))))))) (.run (.split 68 1 (.split 72 1 (.split 4 0 (.split 12 0 (.split 62 1 (.split 67 1 (.step 57 (.step 7 (.step 9 (.step 18 (.step 4 (.step 7 (.step 21 (.close 26)))))))) (.step 26 (.step 54 (.step 9 (.step 7 (.step 21 (.close 29))))))) (.step 4 (.step 10 (.step 21 (.step 57 (.close 7)))))) (.step 9 (.step 15 (.close 57)))) (.step 7 (.step 9 (.step 31 (.step 7 (.step 15 (.step 22 (.step 15 (.step 16 (.close 26)))))))))) (.step 9 (.step 26 (.step 29 (.close 57))))) (.step 4 (.step 9 (.step 29 (.step 31 (.close 57))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742168706826074048029646094712429591419507633702611280353747000311757972567493802279239626988333839970241307824223340035469193974026904401144213670392552751104⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.split 61 1 (.reuse 0) (.run (.split 54 1 (.split 68 1 (.split 72 1 (.split 4 0 (.split 6 0 (.split 10 0 (.step 65 (.step 72 (.split 12 0 (.split 67 1 (.step 7 (.step 4 (.step 7 (.step 9 (.step 21 (.close 22)))))) (.step 64 (.close 7))) (.step 4 (.step 64 (.close 4)))))) (.step 7 (.step 52 (.close 15)))) (.step 10 (.step 64 (.step 4 (.split 67 1 (.step 4 (.step 9 (.close 7))) (.step 10 (.close 7))))))) (.step 7 (.step 52 (.step 64 (.close 7))))) (.step 4 (.step 10 (.step 15 (.step 64 (.close 7)))))) (.step 63 (.close 64))) (.step 4 (.step 10 (.step 15 (.step 57 (.step 52 (.step 7 (.step 26 (.step 7 (.close 53)))))))))))) (.run (.step 62 (.split 54 1 (.step 71 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.step 7 (.step 9 (.step 4 (.step 18 (.step 15 (.close 21)))))) (.step 26 (.step 62 (.step 72 (.step 4 (.close 7)))))) (.step 26 (.step 62 (.close 7)))) (.step 26 (.step 53 (.step 62 (.step 65 (.step 4 (.close 7))))))) (.step 26 (.step 52 (.step 62 (.step 64 (.step 4 (.close 7)))))))) (.step 9 (.step 26 (.step 54 (.step 7 (.step 15 (.step 21 (.step 15 (.close 29))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635117070658382340178474022002387483074570784541978421714863933672093332133331861504⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 54 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 54 1 (.step 54 (.step 7 (.step 9 (.step 15 (.step 16 (.close 21)))))) (.step 22 (.step 9 (.close 54)))) (.step 7 (.step 4 (.close 9)))) (.step 7 (.step 9 (.step 22 (.step 26 (.step 15 (.step 29 (.step 15 (.step 16 (.close 21)))))))))) (.step 22 (.step 54 (.step 4 (.close 7))))) (.step 7 (.step 54 (.step 9 (.step 22 (.step 15 (.close 26))))))) (.step 54 (.step 4 (.step 7 (.step 9 (.step 15 (.close 21))))))) (.step 54 (.step 7 (.step 9 (.step 15 (.step 21 (.close 22)))))))))) (.run (.step 53 (.split 51 1 (.split 54 1 (.split 68 1 (.split 72 1 (.step 53 (.step 70 (.split 6 0 (.step 7 (.step 9 (.step 15 (.close 21)))) (.step 9 (.step 4 (.close 7)))))) (.step 9 (.step 7 (.step 18 (.step 21 (.step 7 (.step 26 (.close 53)))))))) (.step 18 (.step 53 (.step 9 (.close 15))))) (.step 9 (.step 21 (.step 53 (.step 57 (.step 4 (.close 7))))))) (.step 53 (.close 7))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279576264966067672917373453177388234847326484906667314306380301915796288779345028884582207968114438381657193871729088108115947159552⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 62 1 (.split 67 1 (.split 54 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 4 0 (.step 52 (.step 7 (.step 9 (.step 4 (.close 7))))) (.step 7 (.close 9))) (.step 9 (.step 7 (.step 18 (.step 26 (.step 7 (.step 16 (.step 21 (.close 22))))))))) (.step 52 (.step 4 (.step 7 (.step 9 (.step 16 (.close 21))))))) (.step 18 (.step 52 (.step 9 (.close 16))))) (.step 9 (.step 57 (.close 7)))) (.step 52 (.close 7))) (.step 52 (.step 53 (.step 64 (.step 65 (.step 70 (.step 4 (.step 7 (.step 9 (.step 22 (.close 29))))))))))) (.step 52 (.close 7)))))) (.run (.step 54 (.step 70 (.split 49 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.step 9 (.step 46 (.step 9 (.close 7)))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.step 4 (.step 9 (.close 27))))) (.step 7 (.close 9))) (.step 10 (.step 7 (.step 27 (.close 46))))) (.step 7 (.step 9 (.close 46)))) (.step 10 (.step 30 (.close 46)))) (.step 10 (.step 30 (.close 46)))) (.step 9 (.step 27 (.close 46))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900805023143666420641368808316375630233617763844415079539068390152392201374350480482620279881728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 21 (.step 29 (.step 9 (.step 21 (.step 7 (.step 38 (.close 4))))))) (.step 4 (.step 18 (.step 7 (.close 4))))) (.step 4 (.step 18 (.step 7 (.close 4))))) (.step 18 (.step 7 (.step 9 (.step 15 (.close 21)))))) (.step 18 (.step 7 (.step 9 (.step 15 (.close 21)))))) (.step 7 (.step 9 (.step 21 (.step 26 (.step 29 (.step 15 (.step 22 (.step 15 (.step 16 (.close 38))))))))))) (.step 4 (.step 10 (.step 15 (.close 71))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 7 (.step 15 (.step 16 (.step 15 (.step 22 (.close 29))))))))))) (.step 9 (.step 21 (.step 29 (.step 38 (.step 7 (.step 18 (.step 40 (.close 57))))))))) (.step 7 (.step 21 (.step 22 (.step 9 (.step 21 (.step 29 (.close 54)))))))) (.step 9 (.step 21 (.step 7 (.close 21))))) (.step 9 (.step 21 (.step 52 (.step 53 (.step 18 (.step 29 (.step 38 (.step 7 (.step 16 (.step 22 (.close 26)))))))))))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 29 (.step 38 (.step 7 (.step 9 (.step 21 (.step 26 (.step 7 (.step 4 (.close 15))))))))))) (.step 7 (.step 29 (.step 38 (.step 7 (.step 9 (.step 21 (.close 38)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900807060179642755127455076762064039611778815312808745475319026292841555755650243819326463279104⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 6 0 (.step 7 (.step 26 (.step 7 (.step 4 (.close 15))))) (.step 9 (.step 7 (.close 9)))) (.step 7 (.step 4 (.step 9 (.step 15 (.close 26)))))) (.step 4 (.step 7 (.step 9 (.step 26 (.step 15 (.close 21))))))) (.step 7 (.step 4 (.step 9 (.step 21 (.step 26 (.step 15 (.close 28)))))))) (.step 7 (.step 4 (.step 9 (.step 15 (.step 26 (.step 21 (.step 28 (.step 21 (.close 31)))))))))) (.step 7 (.step 9 (.step 15 (.close 26))))) (.step 7 (.step 9 (.step 21 (.step 15 (.close 26)))))) (.step 7 (.step 9 (.step 7 (.step 26 (.step 15 (.step 21 (.step 15 (.close 29)))))))))))) (.run (.step 7 (.split 42 1 (.step 57 (.step 7 (.step 9 (.step 57 (.step 71 (.step 29 (.step 7 (.step 15 (.close 21))))))))) (.step 39 (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 26 (.step 39 (.step 4 (.close 7)))))) (.step 7 (.step 9 (.step 21 (.step 15 (.step 26 (.step 15 (.close 29)))))))) (.step 7 (.step 9 (.step 26 (.step 29 (.step 15 (.step 21 (.step 15 (.close 37)))))))))))))) (.reuse 1)) (.run (.step 7 (.step 18 (.step 7 (.step 9 (.close 18)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404240201250048741265792315732558414636160934825280865496404528991609172487659741442314363640334052433155371098824184521825695301632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 6 0 (.step 7 (.step 15 (.step 7 (.step 26 (.step 7 (.close 4)))))) (.step 9 (.step 7 (.close 9)))) (.step 7 (.step 4 (.step 9 (.step 15 (.step 21 (.close 26))))))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 21 (.step 26 (.step 21 (.close 28))))))))) (.step 7 (.step 4 (.step 9 (.step 15 (.step 21 (.step 26 (.step 28 (.step 26 (.close 31)))))))))) (.step 7 (.step 4 (.step 9 (.close 15))))) (.step 7 (.step 9 (.step 15 (.step 21 (.close 26)))))) (.step 7 (.step 9 (.step 15 (.step 21 (.close 26)))))) (.step 7 (.step 9 (.step 7 (.step 15 (.step 26 (.step 21 (.step 26 (.close 29))))))))) (.step 37 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 54 1 (.step 7 (.step 9 (.step 15 (.step 7 (.step 4 (.close 21)))))) (.step 15 (.step 7 (.step 9 (.step 26 (.step 7 (.step 4 (.close 21)))))))) (.step 7 (.step 4 (.step 9 (.step 15 (.step 21 (.step 26 (.close 28)))))))) (.step 7 (.step 4 (.step 10 (.close 15))))) (.step 7 (.step 9 (.step 15 (.step 21 (.close 26)))))) (.step 7 (.step 9 (.step 15 (.step 21 (.step 26 (.close 29))))))) (.step 7 (.step 9 (.step 15 (.step 26 (.step 21 (.step 29 (.step 21 (.close 37))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838929808552846139973881948671541299731373062858761251219277120274432⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 26 1 (.split 34 1 (.reuse 0) (.step 7 (.split 35 1 (.split 36 1 (.reuse 1) (.run (.step 37 (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 15 (.step 9 (.step 29 (.step 7 (.step 4 (.close 21)))))))) (.step 7 (.step 9 (.step 15 (.step 21 (.step 26 (.close 29))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 21 (.step 26 (.step 21 (.close 37)))))))))))) (.run (.step 15 (.step 29 (.step 37 (.step 38 (.close 7))))))))) (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.step 29 (.step 71 (.step 7 (.step 9 (.step 29 (.step 7 (.close 15))))))) (.step 4 (.step 10 (.step 15 (.close 71))))) (.step 9 (.step 18 (.step 26 (.step 7 (.step 29 (.step 62 (.step 15 (.close 21))))))))) (.step 9 (.step 29 (.step 18 (.step 54 (.close 57)))))) (.step 7 (.step 22 (.step 9 (.step 29 (.step 54 (.close 21))))))) (.step 9 (.step 27 (.step 29 (.step 21 (.step 18 (.step 53 (.step 7 (.close 15))))))))) (.step 9 (.step 27 (.step 29 (.step 52 (.step 7 (.step 16 (.close 21)))))))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 28 (.close 29)))) (.step 7 (.step 28 (.close 29)))) (.step 9 (.step 29 (.step 4 (.close 21))))) (.step 7 (.step 15 (.step 28 (.close 29))))) (.step 7 (.step 18 (.close 7)))))) (.run (.step 7 (.step 18 (.step 7 (.step 4 (.step 9 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196339712629650382276482647896611136427497537563659780285494091876893621196242330630456352982172918290163927609542061797278870682571259666701605495725740421506377420660113461217431157473280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 61 1 (.split 59 1 (.split 68 1 (.split 72 1 (.split 4 0 (.split 21 0 (.split 26 0 (.split 62 1 (.split 67 1 (.split 34 0 (.split 69 1 (.step 15 (.close 7)) (.step 4 (.step 9 (.close 15)))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 26 (.step 70 (.close 7)))) (.step 4 (.step 10 (.step 15 (.step 7 (.close 16)))))) (.step 9 (.step 15 (.close 4)))) (.step 4 (.step 7 (.step 9 (.step 15 (.close 4)))))) (.step 7 (.step 9 (.step 15 (.step 7 (.close 16)))))) (.step 9 (.step 15 (.step 4 (.close 7))))) (.step 4 (.step 9 (.step 15 (.step 7 (.step 16 (.close 22))))))) (.step 9 (.step 15 (.step 26 (.step 4 (.step 7 (.close 16))))))) (.step 4 (.step 15 (.step 7 (.step 9 (.close 10)))))) (.step 15 (.step 22 (.step 54 (.step 22 (.step 57 (.step 62 (.step 54 (.step 15 (.step 4 (.step 7 (.close 15)))))))))))) (.step 9 (.step 15 (.step 21 (.close 53))))) (.step 9 (.step 15 (.step 16 (.step 7 (.step 18 (.step 16 (.step 7 (.step 21 (.step 22 (.close 26))))))))))) (.step 9 (.step 10 (.step 4 (.close 7))))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 7 (.step 15 (.step 7 (.step 4 (.close 15)))))) (.step 9 (.step 15 (.step 7 (.close 26))))) (.step 7 (.step 15 (.close 7)))) (.step 9 (.step 15 (.step 7 (.step 18 (.step 21 (.step 22 (.close 26)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677468650784044689883753531605778432⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 61 1 (.step 4 (.step 7 (.step 18 (.step 4 (.step 57 (.step 40 (.step 68 (.close 4)))))))) (.step 4 (.step 7 (.step 4 (.close 5))))) (.step 4 (.step 7 (.step 9 (.step 7 (.close 18)))))) (.step 4 (.step 7 (.step 22 (.step 4 (.step 9 (.close 26))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 26)))))) (.step 4 (.step 9 (.step 7 (.step 18 (.step 26 (.close 52))))))) (.step 4 (.step 7 (.step 9 (.close 10))))) (.step 4 (.step 7 (.step 4 (.step 9 (.close 15)))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 9 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.step 15 (.close 26))))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 4 (.step 9 (.step 15 (.step 26 (.close 29)))))))))) (.step 4 (.step 7 (.step 9 (.step 7 (.step 18 (.close 29))))))))))) (.run (.step 7 (.step 18 (.step 7 (.close 18)))))) (.run (.step 7 (.step 18 (.step 7 (.close 18)))))) (.split 16 1 (.split 17 1 (.step 15 (.step 18 (.split 21 1 (.reuse 1) (.run (.step 4 (.step 9 (.step 7 (.step 15 (.close 7))))))))) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.close 18)))))))) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.close 18)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644919266076532915830784⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 12 1 (.step 7 (.step 18 (.step 7 (.step 9 (.step 15 (.close 18)))))) (.step 15 (.step 4 (.close 7)))))))) (.run (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.step 57 (.step 18 (.split 21 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 68 1 (.split 4 0 (.split 10 0 (.split 26 1 (.split 30 0 (.split 34 0 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 69 1 (.step 9 (.step 4 (.close 9))) (.step 4 (.close 9))) (.step 9 (.close 4))) (.step 9 (.close 4))) (.step 9 (.close 4))) (.step 9 (.close 4))) (.step 9 (.step 7 (.step 9 (.close 7))))) (.step 9 (.step 7 (.close 9)))) (.step 9 (.close 4))) (.step 9 (.step 7 (.close 9)))) (.step 9 (.step 7 (.close 9)))) (.step 4 (.close 9))) (.step 9 (.step 10 (.step 26 (.step 46 (.step 70 (.step 7 (.close 9)))))))) (.step 9 (.step 10 (.step 46 (.step 22 (.step 9 (.step 26 (.close 9)))))))) (.step 9 (.step 10 (.step 4 (.close 7))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 9 (.step 10 (.step 29 (.step 7 (.close 9))))))) (.step 7 (.step 9 (.step 10 (.step 15 (.step 29 (.step 7 (.close 9)))))))) (.step 4 (.close 9))))) (.step 4 (.step 5 (.step 4 (.step 7 (.step 9 (.step 7 (.close 9)))))))) (.step 4 (.step 5 (.step 4 (.step 7 (.step 9 (.step 7 (.close 9)))))))) (.step 9 (.step 4 (.close 7)))) (.step 7 (.step 9 (.close 7))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644919266077632427458560⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 6 1 (.split 12 1 (.step 7 (.step 18 (.step 7 (.step 9 (.close 18))))) (.step 9 (.step 7 (.step 15 (.step 7 (.close 15)))))) (.step 9 (.step 4 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case12
