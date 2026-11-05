module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case215
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409448681681725776274288279552⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨8697816018884211022835, 5789228615357111146520048038021683988769484383179567732815818416086450779233412664265074676308133956708084476189281768283666591250201089101977864971187095671403204624927834713340492290444220293581974657099303306801573789696, 0⟩]
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
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843445759100917919003786254359394883714925394579685376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 42 0 (.split 36 0 (.split 14 0 (.split 34 0 (.step 5 (.close 52)) (.step 5 (.step 10 (.close 13)))) (.step 5 (.step 11 (.step 27 (.close 34))))) (.step 54 (.step 5 (.step 10 (.close 13))))) (.split 43 0 (.step 58 (.step 5 (.step 13 (.step 5 (.close 17))))) (.step 70 (.step 58 (.step 5 (.step 13 (.step 5 (.close 11)))))))) (.split 42 0 (.split 36 0 (.step 53 (.step 5 (.close 13))) (.step 54 (.step 33 (.close 5)))) (.step 70 (.split 14 0 (.step 33 (.step 58 (.close 10))) (.step 13 (.step 53 (.step 5 (.close 11)))))))) (.split 30 0 (.split 42 0 (.split 43 0 (.step 5 (.step 31 (.close 17))) (.step 70 (.step 5 (.close 11)))) (.step 55 (.step 62 (.step 5 (.step 13 (.step 5 (.close 11))))))) (.step 70 (.step 5 (.step 31 (.step 13 (.step 5 (.close 11)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.split 43 0 (.step 5 (.step 13 (.close 17))) (.step 54 (.step 5 (.close 11)))) (.step 54 (.close 5))) (.step 55 (.step 52 (.step 5 (.step 15 (.step 5 (.close 11))))))) (.step 54 (.step 33 (.step 63 (.step 25 (.step 5 (.close 10))))))) (.step 70 (.split 14 0 (.step 70 (.step 54 (.step 5 (.close 11)))) (.step 63 (.step 11 (.step 17 (.step 5 (.close 19))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1267650600228229401497776947200, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220601161453331797561748481845835306024621309952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 52 (.step 64 (.step 5 (.close 10)))) (.step 54 (.step 13 (.step 5 (.close 10))))) (.split 36 0 (.split 56 0 (.step 52 (.step 33 (.step 5 (.step 13 (.close 5))))) (.step 13 (.step 33 (.close 5)))) (.step 13 (.step 33 (.step 5 (.close 10)))))) (.step 70 (.step 13 (.close 5)))) (.split 30 0 (.step 54 (.split 22 0 (.step 52 (.step 5 (.step 13 (.close 5)))) (.step 70 (.step 5 (.close 11))))) (.step 13 (.step 33 (.step 54 (.close 5)))))) (.split 17 0 (.split 22 0 (.split 36 0 (.split 56 0 (.split 58 0 (.split 42 0 (.step 52 (.step 63 (.close 10))) (.step 13 (.step 5 (.step 25 (.step 5 (.step 10 (.close 15))))))) (.step 52 (.step 42 (.close 5)))) (.step 13 (.step 54 (.step 5 (.close 10))))) (.step 13 (.step 54 (.step 5 (.step 25 (.step 5 (.step 10 (.close 15)))))))) (.step 70 (.step 13 (.split 38 0 (.step 70 (.step 5 (.step 11 (.close 14)))) (.step 14 (.step 5 (.step 19 (.close 5)))))))) (.split 22 0 (.split 30 0 (.step 54 (.split 34 0 (.step 63 (.step 13 (.close 5))) (.step 13 (.step 5 (.step 14 (.close 11)))))) (.step 13 (.step 33 (.step 20 (.step 5 (.close 14)))))) (.split 30 0 (.step 70 (.step 19 (.step 13 (.step 19 (.step 5 (.close 11)))))) (.step 13 (.step 19 (.step 20 (.close 5)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602555249906705725694827828227346547215433728⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 14 0 (.step 5 (.step 11 (.step 13 (.close 27)))) (.step 63 (.close 11))) (.step 54 (.step 5 (.close 11)))) (.step 55 (.step 52 (.step 5 (.step 15 (.step 5 (.close 11))))))) (.step 53 (.step 65 (.close 11)))) (.step 70 (.split 14 0 (.step 70 (.step 63 (.close 20))) (.step 63 (.step 11 (.step 17 (.step 5 (.close 19)))))))) (.split 14 0 (.split 30 0 (.split 34 0 (.split 42 0 (.split 43 0 (.step 63 (.step 20 (.close 5))) (.step 54 (.step 48 (.close 5)))) (.step 23 (.step 24 (.step 13 (.step 19 (.step 5 (.close 20))))))) (.step 23 (.step 24 (.step 54 (.step 5 (.step 13 (.step 14 (.close 16)))))))) (.step 33 (.step 53 (.step 23 (.step 20 (.step 23 (.close 11))))))) (.split 22 0 (.step 63 (.step 19 (.step 11 (.step 5 (.close 17))))) (.split 30 0 (.step 63 (.step 19 (.step 11 (.step 5 (.close 17))))) (.step 13 (.step 19 (.step 20 (.step 5 (.close 11))))))))))) (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.split 36 0 (.step 63 (.close 13)) (.step 13 (.step 5 (.close 13))))) (.step 13 (.step 5 (.close 11)))) (.step 13 (.step 20 (.step 13 (.close 5))))) (.step 13 (.step 53 (.step 14 (.step 11 (.close 5)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409448681681725776274288279552⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.reuse 0) (.run (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 52 (.step 5 (.close 10))) (.step 55 (.step 65 (.step 10 (.step 5 (.close 13)))))) (.step 52 (.step 10 (.close 13)))) (.split 34 0 (.split 36 0 (.step 65 (.step 52 (.close 5))) (.step 13 (.step 54 (.step 5 (.step 10 (.close 16)))))) (.step 13 (.step 52 (.step 10 (.close 16)))))) (.step 55 (.step 70 (.step 5 (.close 11))))) (.split 14 0 (.step 55 (.step 72 (.step 5 (.step 11 (.close 13))))) (.step 24 (.step 13 (.step 5 (.close 11)))))) (.split 14 0 (.split 17 0 (.step 55 (.step 65 (.close 5))) (.step 24 (.step 13 (.step 23 (.step 54 (.step 5 (.step 10 (.close 17)))))))) (.step 24 (.step 63 (.step 5 (.step 13 (.step 5 (.close 17)))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 52 (.step 5 (.close 10))) (.step 13 (.step 15 (.close 10)))) (.step 13 (.step 54 (.step 5 (.step 10 (.close 13)))))) (.step 13 (.step 52 (.step 10 (.close 13))))) (.step 13 (.step 5 (.step 10 (.close 18))))) (.step 13 (.close 5))) (.step 13 (.step 54 (.step 5 (.close 11))))) (.step 13 (.step 55 (.step 13 (.close 5))))) (.step 13 (.step 31 (.step 63 (.step 13 (.close 5)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case215
