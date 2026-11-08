module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case27
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409448681681725776274288279552⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨8697816018884211022835, 5789228615357111146520048038021683988769484383179567732815818416086450779233412664265074676308133956708084476189281768283666591250201089101977864971187095671403204624927834713340492290444220293581974657099303306801573789696, 0⟩]
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
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781380463818846560926962014735848135688628578769167001117017650680037376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 43 0 (.split 14 0 (.step 5 (.step 13 (.step 18 (.close 21)))) (.step 5 (.close 34))) (.split 56 0 (.split 14 0 (.step 76 (.step 5 (.step 27 (.step 35 (.close 52))))) (.step 52 (.close 5))) (.step 54 (.step 5 (.close 10))))) (.split 42 0 (.step 65 (.step 5 (.close 11))) (.step 5 (.step 54 (.step 5 (.close 52)))))) (.split 42 0 (.step 54 (.step 5 (.step 10 (.close 13)))) (.split 43 0 (.step 58 (.close 17)) (.step 54 (.close 58))))) (.split 36 0 (.split 42 0 (.split 39 0 (.split 43 0 (.step 5 (.step 13 (.step 15 (.close 16)))) (.split 56 0 (.step 52 (.step 5 (.close 10))) (.step 54 (.step 5 (.close 10))))) (.step 5 (.step 52 (.step 5 (.close 10))))) (.split 43 0 (.step 58 (.close 17)) (.step 70 (.step 58 (.close 11))))) (.split 43 0 (.split 56 0 (.step 58 (.close 17)) (.step 54 (.close 5))) (.step 54 (.step 58 (.close 11)))))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 63 (.step 53 (.close 5))) (.step 53 (.step 63 (.step 5 (.close 10))))) (.step 70 (.step 53 (.step 5 (.close 10))))) (.step 54 (.step 33 (.step 5 (.step 10 (.close 13)))))) (.split 36 0 (.split 42 0 (.split 43 0 (.step 53 (.step 5 (.close 13))) (.split 56 0 (.step 53 (.step 5 (.step 13 (.step 5 (.close 11))))) (.step 33 (.step 5 (.close 10))))) (.step 70 (.split 14 0 (.step 33 (.close 58)) (.step 13 (.step 38 (.step 5 (.step 17 (.close 16)))))))) (.step 54 (.step 33 (.step 38 (.step 5 (.step 10 (.close 13))))))))))
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
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843445759100917919003786254359394883714925394579685376⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 36 0 (.step 70 (.step 62 (.step 5 (.step 11 (.close 13))))) (.step 55 (.step 54 (.step 5 (.step 13 (.step 5 (.close 11))))))) (.step 55 (.step 68 (.step 48 (.step 13 (.step 33 (.close 39))))))) (.step 70 (.step 33 (.split 14 0 (.step 33 (.step 70 (.step 5 (.close 13)))) (.step 13 (.step 33 (.step 5 (.step 11 (.close 17))))))))))) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 61 (.step 5 (.close 13))) (.step 54 (.step 63 (.step 5 (.close 27))))) (.step 55 (.step 48 (.step 11 (.close 17))))) (.step 54 (.close 5))) (.step 55 (.step 54 (.step 48 (.step 11 (.close 17)))))) (.split 34 0 (.step 54 (.split 42 0 (.step 63 (.close 11)) (.step 33 (.close 5)))) (.step 33 (.step 54 (.step 5 (.close 11)))))) (.split 14 0 (.step 70 (.split 30 0 (.step 70 (.split 34 0 (.step 63 (.step 23 (.step 11 (.close 13)))) (.step 23 (.step 24 (.close 13))))) (.step 33 (.step 70 (.split 34 0 (.step 54 (.step 5 (.step 11 (.close 13)))) (.step 23 (.step 20 (.close 5)))))))) (.split 30 0 (.step 63 (.step 20 (.step 25 (.step 5 (.close 11))))) (.step 13 (.step 33 (.split 34 0 (.step 63 (.step 20 (.step 5 (.close 11)))) (.step 20 (.step 5 (.step 11 (.close 17))))))))))))
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

namespace Part2
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220601161453331796294097881617605904527918104576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 65 (.step 5 (.close 13))) (.step 5 (.step 54 (.step 5 (.close 13))))) (.step 54 (.step 5 (.step 40 (.step 5 (.step 13 (.step 5 (.close 11)))))))) (.step 55 (.step 68 (.step 48 (.step 13 (.step 33 (.close 39))))))) (.step 65 (.step 33 (.close 38)))) (.step 70 (.split 30 0 (.step 70 (.split 38 0 (.step 70 (.step 48 (.step 5 (.step 11 (.step 13 (.step 14 (.close 16))))))) (.step 23 (.step 5 (.step 13 (.step 5 (.close 11))))))) (.step 33 (.step 53 (.step 23 (.step 5 (.close 11)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.split 43 0 (.step 63 (.step 23 (.step 13 (.step 5 (.close 19))))) (.step 54 (.step 48 (.close 5)))) (.step 23 (.step 24 (.step 43 (.step 5 (.step 13 (.close 33))))))) (.step 24 (.step 54 (.step 5 (.step 23 (.close 13)))))) (.step 33 (.step 53 (.step 23 (.step 65 (.close 20)))))) (.split 34 0 (.split 36 0 (.split 38 0 (.step 70 (.split 30 0 (.step 62 (.step 48 (.close 5))) (.step 53 (.step 19 (.close 5))))) (.step 23 (.close 19))) (.step 23 (.step 19 (.close 20)))) (.split 36 0 (.step 23 (.step 19 (.step 20 (.close 11)))) (.step 20 (.step 19 (.step 20 (.close 5)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1267650600228229401497776947200, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843445759099524122428879358063649129552286368688766976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 42 0 (.split 36 0 (.step 52 (.step 64 (.step 5 (.step 18 (.step 5 (.close 11)))))) (.step 54 (.step 52 (.close 5)))) (.step 70 (.split 38 0 (.step 52 (.step 58 (.step 13 (.step 15 (.close 10))))) (.step 33 (.step 55 (.step 58 (.step 10 (.close 13)))))))) (.split 36 0 (.split 42 0 (.split 56 0 (.step 52 (.split 58 0 (.step 33 (.step 5 (.step 10 (.step 13 (.close 18))))) (.step 52 (.step 31 (.close 11))))) (.step 13 (.step 33 (.close 5)))) (.step 13 (.step 33 (.step 5 (.close 10))))) (.step 13 (.step 33 (.step 39 (.close 5)))))) (.step 70 (.split 34 0 (.step 70 (.step 63 (.step 13 (.close 5)))) (.step 13 (.step 52 (.step 64 (.step 5 (.close 11)))))))) (.split 22 0 (.split 30 0 (.step 54 (.split 34 0 (.step 63 (.step 13 (.close 5))) (.step 13 (.step 5 (.step 25 (.step 5 (.close 10))))))) (.step 13 (.step 33 (.step 54 (.close 5))))) (.split 30 0 (.step 70 (.split 34 0 (.step 54 (.step 48 (.step 5 (.step 11 (.close 13))))) (.step 13 (.step 14 (.step 11 (.close 15)))))) (.step 13 (.step 33 (.step 54 (.step 5 (.step 14 (.close 11))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1267650600228229401497776947200, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220601161453331797561748481845835306024621309952⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 63 (.step 54 (.step 48 (.close 5)))) (.step 13 (.step 5 (.step 54 (.close 5))))) (.step 13 (.step 54 (.close 5)))) (.step 13 (.step 52 (.step 40 (.step 52 (.step 10 (.close 16))))))) (.step 13 (.step 33 (.step 53 (.step 10 (.close 16)))))) (.split 30 0 (.step 70 (.split 34 0 (.step 70 (.step 13 (.step 5 (.close 11)))) (.step 13 (.step 14 (.step 11 (.close 15)))))) (.step 13 (.step 33 (.step 53 (.step 14 (.step 10 (.close 20)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 54 (.split 38 0 (.split 42 0 (.step 48 (.step 13 (.step 11 (.close 5)))) (.step 13 (.step 5 (.close 11)))) (.step 23 (.step 11 (.close 13))))) (.step 13 (.step 23 (.step 14 (.step 15 (.step 11 (.close 17))))))) (.step 13 (.step 33 (.step 53 (.step 14 (.step 10 (.close 20))))))) (.split 30 0 (.split 34 0 (.step 70 (.split 36 0 (.step 70 (.step 54 (.step 19 (.step 11 (.close 13))))) (.step 13 (.step 19 (.step 5 (.close 11)))))) (.step 13 (.step 14 (.close 17)))) (.step 13 (.step 19 (.step 20 (.step 5 (.step 11 (.close 14)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602555249906705725694827828227346547215433728⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part4.root]
def proof : Chunks.Proof 3 := (.split 10 0 (.split 16 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 68 (.step 27 (.step 31 (.close 5)))) (.step 13 (.step 5 (.close 17)))) (.step 13 (.step 33 (.step 53 (.close 5))))) (.split 30 0 (.step 63 (.step 19 (.step 11 (.step 5 (.close 17))))) (.step 13 (.step 33 (.split 34 0 (.step 42 (.step 5 (.close 19))) (.step 19 (.step 17 (.step 5 (.close 20))))))))) (.split 22 0 (.split 30 0 (.step 63 (.step 19 (.step 11 (.step 5 (.close 17))))) (.step 13 (.step 33 (.split 34 0 (.step 42 (.step 5 (.close 19))) (.step 19 (.step 17 (.step 5 (.close 20)))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 38 0 (.step 61 (.step 62 (.close 63))) (.step 14 (.step 19 (.close 5)))) (.step 13 (.step 62 (.step 11 (.close 5))))) (.step 13 (.step 19 (.step 5 (.step 11 (.close 17)))))) (.step 13 (.step 19 (.step 5 (.step 11 (.step 17 (.close 20))))))) (.step 13 (.step 19 (.step 17 (.step 5 (.close 20)))))) (.step 13 (.step 19 (.step 20 (.step 11 (.step 5 (.close 17)))))))))))) (.split 14 0 (.reuse 2) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 39 0 (.step 52 (.split 36 0 (.split 56 0 (.step 63 (.close 13)) (.step 13 (.close 5))) (.step 13 (.step 54 (.close 5))))) (.step 31 (.step 13 (.step 15 (.close 11))))) (.step 13 (.step 15 (.close 13)))) (.step 13 (.step 62 (.step 5 (.close 11))))) (.step 13 (.step 54 (.step 61 (.step 13 (.close 5)))))) (.step 13 (.step 63 (.step 11 (.step 13 (.close 17)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1361129467683753853853498429728146587648, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843445759099525483558345774166902754821314599058407424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 52 (.step 5 (.close 10))) (.step 55 (.step 65 (.step 10 (.step 5 (.close 13)))))) (.step 55 (.step 54 (.step 72 (.step 52 (.step 5 (.close 10))))))) (.split 36 0 (.step 52 (.step 10 (.close 13))) (.step 40 (.split 43 0 (.step 16 (.close 5)) (.step 13 (.step 52 (.close 10))))))) (.split 34 0 (.split 36 0 (.step 65 (.split 43 0 (.step 18 (.step 13 (.close 5))) (.split 56 0 (.step 52 (.close 5)) (.step 13 (.step 18 (.close 10)))))) (.step 13 (.step 54 (.step 18 (.step 5 (.close 10)))))) (.step 13 (.step 52 (.step 10 (.close 16)))))) (.split 30 0 (.split 34 0 (.step 55 (.step 5 (.step 54 (.step 5 (.close 52))))) (.step 13 (.step 40 (.close 5)))) (.step 13 (.step 55 (.step 5 (.step 18 (.step 11 (.close 17)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 55 (.step 5 (.close 54))) (.step 13 (.step 40 (.close 5)))) (.step 13 (.step 54 (.step 55 (.step 5 (.close 11)))))) (.split 30 0 (.step 63 (.step 13 (.step 40 (.step 5 (.close 18))))) (.step 13 (.step 23 (.step 11 (.step 17 (.close 19)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1361129467683753853853498429728146587648, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220601162814461265245502335699333735751694155776⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 55 (.step 5 (.step 54 (.step 5 (.close 52))))) (.step 13 (.step 40 (.close 5)))) (.step 13 (.step 55 (.step 5 (.step 18 (.step 11 (.close 17))))))) (.step 65 (.step 13 (.step 23 (.step 24 (.step 5 (.step 23 (.close 11)))))))) (.split 22 0 (.step 65 (.step 13 (.step 23 (.step 24 (.step 5 (.step 23 (.close 11))))))) (.step 23 (.step 24 (.step 17 (.close 20)))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 38 0 (.step 52 (.step 5 (.close 10))) (.step 55 (.step 18 (.step 13 (.step 15 (.close 10)))))) (.step 13 (.step 55 (.step 18 (.step 13 (.step 5 (.close 10))))))) (.step 13 (.step 54 (.step 15 (.close 10))))) (.step 13 (.step 52 (.step 10 (.close 13))))) (.step 13 (.step 18 (.step 13 (.step 15 (.step 18 (.close 27))))))) (.step 13 (.step 55 (.step 5 (.step 13 (.step 5 (.step 17 (.close 18)))))))) (.step 13 (.step 54 (.step 55 (.step 5 (.step 13 (.close 5))))))) (.step 13 (.step 55 (.step 24 (.step 13 (.step 5 (.close 18)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409448681681725776274288279552⟩
def references : Fin 2 → Box := ![Part5.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 13 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 10 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 34 0 (.split 22 0 (.step 55 (.step 5 (.step 52 (.close 5)))) (.step 58 (.step 5 (.step 11 (.close 17))))) (.step 40 (.close 5))) (.step 63 (.step 13 (.step 40 (.step 5 (.close 16)))))) (.step 63 (.step 14 (.step 24 (.step 5 (.step 16 (.close 17))))))) (.split 17 0 (.step 63 (.step 14 (.step 24 (.step 5 (.step 16 (.close 17)))))) (.step 23 (.step 17 (.close 20))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 55 (.step 52 (.step 5 (.step 13 (.step 5 (.close 11)))))) (.step 13 (.close 5))) (.step 5 (.close 13))) (.step 5 (.close 13))) (.step 13 (.step 5 (.close 13))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part8.excludes
end FiveColour.Packed.EnumerationChunks.Case27
