module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196335463521655586841957790104042475653421537741552237815652579253161895294197696326266415588575172223294736638533781406336362640399607321444226252051530785070021936087831845169756012281856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 62 1 (.split 67 1 (.step 71 (.split 69 1 (.split 72 1 (.split 6 0 (.step 7 (.step 18 (.step 9 (.step 40 (.step 7 (.close 53)))))) (.split 16 0 (.split 26 0 (.split 35 0 (.split 68 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 4 (.close 9))))) (.step 7 (.step 9 (.step 26 (.step 29 (.step 7 (.close 15))))))) (.step 71 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.step 7 (.step 4 (.close 71))) (.step 4 (.step 9 (.close 71)))) (.step 7 (.close 9))) (.step 10 (.step 4 (.step 9 (.close 7))))) (.step 7 (.close 9)))))) (.step 70 (.step 71 (.split 6 0 (.step 7 (.close 70)) (.step 46 (.step 70 (.step 7 (.step 4 (.step 9 (.close 7)))))))))) (.step 71 (.split 4 0 (.split 6 0 (.split 10 0 (.step 65 (.split 12 0 (.split 67 1 (.step 7 (.step 4 (.close 71))) (.step 65 (.close 7))) (.split 67 1 (.step 4 (.step 9 (.close 71))) (.step 10 (.step 21 (.step 26 (.step 7 (.close 57)))))))) (.step 7 (.close 65))) (.step 10 (.step 65 (.split 67 1 (.step 4 (.step 9 (.close 7))) (.step 10 (.close 7)))))) (.step 7 (.step 53 (.step 7 (.close 65))))))) (.split 68 1 (.split 4 0 (.split 12 0 (.split 62 1 (.split 67 1 (.step 57 (.step 7 (.step 9 (.close 57)))) (.step 26 (.step 54 (.step 9 (.close 57))))) (.step 4 (.step 57 (.close 7)))) (.step 15 (.close 57))) (.step 9 (.step 7 (.close 57)))) (.step 9 (.close 71)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635117070658382340178474022002387483074570784541978421714863933672093332133331861504⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 59 1 (.split 61 1 (.reuse 0) (.run (.split 54 1 (.split 68 1 (.split 72 1 (.split 4 0 (.split 6 0 (.split 10 0 (.step 65 (.step 72 (.split 12 0 (.split 67 1 (.step 7 (.step 4 (.close 71))) (.step 64 (.close 7))) (.step 4 (.step 64 (.close 4)))))) (.step 7 (.close 64))) (.step 10 (.step 64 (.split 67 1 (.step 4 (.step 9 (.close 7))) (.step 10 (.close 7)))))) (.step 7 (.step 64 (.close 7)))) (.step 4 (.close 71))) (.step 63 (.close 64))) (.step 4 (.step 10 (.step 57 (.close 64))))))) (.run (.step 62 (.split 54 1 (.step 71 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.step 7 (.close 62)) (.step 62 (.step 72 (.close 7)))) (.step 62 (.close 7))) (.step 53 (.step 62 (.step 65 (.close 7))))) (.step 62 (.step 64 (.close 7))))) (.step 9 (.step 26 (.step 54 (.step 7 (.close 57))))))))) (.run (.step 54 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 54 1 (.step 54 (.step 7 (.close 54))) (.step 22 (.close 57))) (.step 7 (.close 54))) (.step 7 (.step 26 (.close 54)))) (.step 22 (.step 54 (.close 7)))) (.step 7 (.step 54 (.close 71)))) (.step 54 (.close 71))) (.step 54 (.step 7 (.close 64))))))) (.run (.step 53 (.split 51 1 (.split 54 1 (.split 68 1 (.split 72 1 (.step 53 (.step 70 (.split 6 0 (.step 7 (.close 53)) (.step 9 (.close 7))))) (.step 9 (.step 18 (.step 21 (.step 7 (.close 53)))))) (.step 18 (.step 53 (.close 64)))) (.step 9 (.step 53 (.step 57 (.close 7))))) (.step 53 (.close 7))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637108765072710910733511532845525339281867519810641065336640106826240152145514063907393304331927372494593327104⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 62 1 (.split 67 1 (.split 54 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 4 0 (.step 52 (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 9 (.step 18 (.close 75)))) (.step 52 (.step 7 (.close 71)))) (.step 18 (.close 71))) (.step 57 (.close 7))) (.step 52 (.close 7))) (.step 52 (.step 53 (.step 64 (.step 65 (.step 70 (.step 7 (.close 71)))))))) (.step 52 (.close 7)))))) (.run (.step 54 (.step 70 (.split 49 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 16 0 (.split 17 0 (.step 9 (.step 46 (.step 9 (.close 7)))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 10 (.close 46))) (.step 10 (.close 46))) (.step 10 (.step 30 (.close 46)))) (.step 9 (.step 27 (.close 46)))))))) (.run (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 6 0 (.step 7 (.step 26 (.step 7 (.close 31)))) (.step 9 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 21 (.close 71))))) (.step 7 (.step 15 (.close 71)))) (.step 7 (.close 62))) (.step 7 (.step 9 (.close 62)))) (.step 9 (.step 7 (.step 26 (.close 52))))))) (.run (.split 42 1 (.step 57 (.step 7 (.step 9 (.step 57 (.step 71 (.step 29 (.step 7 (.close 26)))))))) (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 39 (.close 7)))) (.step 7 (.step 9 (.close 39)))) (.step 7 (.step 9 (.step 26 (.close 52))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900807060179642755127455076762064039611778815312808745475319026292841555755650243819326463279104⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 21 (.step 29 (.step 9 (.step 21 (.step 38 (.close 4)))))) (.step 18 (.step 7 (.close 4)))) (.step 18 (.step 7 (.close 4)))) (.step 18 (.step 7 (.close 38)))) (.step 18 (.step 7 (.close 38)))) (.step 7 (.step 9 (.step 21 (.close 70))))) (.step 4 (.step 15 (.close 71)))) (.step 9 (.step 18 (.step 21 (.step 26 (.close 71)))))) (.step 9 (.step 21 (.step 29 (.step 38 (.step 18 (.close 57))))))) (.step 7 (.step 22 (.step 9 (.step 21 (.step 29 (.close 54))))))) (.step 21 (.step 7 (.close 21)))) (.step 9 (.step 52 (.step 53 (.step 18 (.step 38 (.close 57))))))) (.step 7 (.step 9 (.close 10)))) (.step 38 (.step 7 (.step 21 (.close 38))))) (.step 29 (.step 38 (.step 7 (.step 21 (.close 38)))))))) (.run (.step 18 (.step 7 (.close 18)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200197408023521040185685109013464847708734576282818164021716701031121312598070394880⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 6 0 (.step 7 (.step 15 (.step 7 (.step 26 (.step 7 (.close 4)))))) (.step 9 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 37)))) (.step 4 (.step 7 (.step 9 (.step 15 (.close 39)))))) (.step 7 (.step 9 (.step 15 (.close 71))))) (.step 7 (.step 9 (.close 62)))) (.step 9 (.step 7 (.step 15 (.close 52))))) (.step 37 (.split 49 1 (.split 50 1 (.split 61 1 (.split 62 1 (.split 54 1 (.step 7 (.close 37)) (.step 15 (.step 9 (.close 45)))) (.step 7 (.close 37))) (.step 7 (.close 15))) (.step 7 (.close 37))) (.step 7 (.step 9 (.close 37)))))) (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 15 (.close 39)))) (.step 7 (.close 37))) (.step 7 (.step 9 (.close 37))))) (.step 15 (.step 29 (.step 37 (.step 38 (.close 7)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904899348240654999128816979946471325433856⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.step 29 (.step 71 (.step 7 (.step 9 (.step 29 (.step 7 (.close 15))))))) (.step 10 (.close 71))) (.step 9 (.step 18 (.step 26 (.step 7 (.close 71)))))) (.step 29 (.close 57))) (.step 7 (.step 22 (.step 9 (.step 29 (.step 54 (.close 21))))))) (.step 9 (.step 27 (.step 29 (.step 53 (.close 29)))))) (.step 9 (.step 27 (.step 29 (.step 52 (.close 29)))))) (.step 7 (.step 9 (.close 10)))) (.step 28 (.close 29))) (.step 28 (.close 29))) (.step 29 (.close 21))) (.step 28 (.close 29))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 61 1 (.step 18 (.step 57 (.step 40 (.step 68 (.close 4))))) (.step 4 (.step 7 (.close 24)))) (.step 4 (.step 9 (.close 18)))) (.step 7 (.close 54))) (.step 4 (.step 9 (.step 18 (.close 26))))) (.step 9 (.step 18 (.close 52)))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 4 (.close 26)))) (.step 7 (.close 39))) (.step 4 (.step 18 (.close 38)))) (.step 7 (.step 24 (.step 4 (.close 37))))) (.step 4 (.step 18 (.close 29))))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.step 7 (.close 18)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644918113155028308983808⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.split 16 1 (.split 17 1 (.step 15 (.step 18 (.split 21 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 61 1 (.split 59 1 (.split 68 1 (.split 72 1 (.split 4 0 (.split 21 0 (.split 26 0 (.split 62 1 (.split 67 1 (.split 69 1 (.step 15 (.close 7)) (.step 4 (.step 9 (.close 15)))) (.step 26 (.step 70 (.close 7)))) (.step 4 (.step 10 (.step 15 (.close 53))))) (.step 15 (.close 4))) (.step 9 (.step 15 (.close 4)))) (.step 7 (.step 9 (.step 15 (.close 65))))) (.step 15 (.close 7))) (.step 9 (.close 71))) (.step 15 (.close 62))) (.step 15 (.close 64))) (.step 15 (.step 57 (.step 62 (.step 54 (.step 15 (.close 54))))))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 9 (.close 46))) (.step 9 (.step 7 (.close 15)))) (.step 15 (.step 7 (.close 15)))) (.step 15 (.close 38))) (.step 15 (.close 7))) (.step 15 (.close 29))) (.step 4 (.step 15 (.close 7)))))) (.step 5 (.step 15 (.close 18)))) (.step 5 (.step 7 (.step 15 (.close 18))))))) (.run (.split 12 1 (.step 18 (.step 7 (.close 18))) (.step 15 (.close 7)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200199260696948838931454057403462677963281904900677469918434644919266077632427458560⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.split 6 1 (.reuse 0) (.run (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.step 57 (.step 18 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 34 0 (.split 69 1 (.step 9 (.step 4 (.close 9))) (.step 4 (.close 9))) (.step 9 (.step 7 (.step 9 (.close 7))))) (.step 9 (.step 7 (.close 9)))) (.step 9 (.step 7 (.close 9)))) (.step 9 (.step 10 (.step 26 (.step 70 (.step 7 (.close 9))))))) (.step 9 (.step 10 (.step 46 (.step 22 (.step 9 (.close 54))))))) (.step 9 (.close 46))) (.step 9 (.close 7))) (.step 9 (.step 10 (.step 29 (.step 7 (.close 9)))))) (.step 9 (.step 15 (.step 29 (.step 7 (.close 9)))))))) (.step 5 (.step 9 (.close 18)))) (.step 5 (.step 4 (.step 7 (.step 9 (.close 11)))))) (.step 9 (.close 7))) (.step 7 (.step 9 (.close 7)))))) (.run (.step 7 (.split 6 1 (.split 12 1 (.step 18 (.step 7 (.close 18))) (.step 9 (.close 18))) (.step 9 (.close 7))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case12
