module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case17
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575918783260537824242223744277181749559044341760⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨2147483648, 5789228615351851005602038365663647631691741564492063194893353984289248658424585975995156013904601150434851207722254404397047265528834370213355123138570923585945874081878591057287959391630268912121111872138590874780594864128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 55 0 (.step 76 (.close 27)) (.step 3 (.close 58))) (.step 3 (.close 4))) (.step 5 (.step 3 (.close 61)))) (.step 5 (.step 7 (.close 21)))) (.step 31 (.close 4))) (.step 31 (.step 58 (.step 7 (.close 4))))) (.step 7 (.close 53))) (.step 7 (.step 5 (.step 7 (.close 27))))) (.step 18 (.step 55 (.step 5 (.close 3))))) (.step 7 (.step 18 (.step 7 (.close 61))))) (.step 7 (.step 18 (.step 7 (.close 42))))) (.split 16 0 (.split 17 0 (.split 20 0 (.step 7 (.step 31 (.step 27 (.step 5 (.step 7 (.close 34)))))) (.step 5 (.close 23))) (.step 7 (.close 5))) (.step 7 (.close 18)))) (.split 14 0 (.split 16 0 (.split 20 0 (.split 34 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 38 0 (.step 5 (.step 9 (.step 7 (.close 15)))) (.step 10 (.step 5 (.step 7 (.close 21))))) (.step 22 (.step 5 (.close 7)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 7 (.step 4 (.close 14))))) (.step 5 (.step 18 (.close 4)))) (.step 7 (.step 16 (.close 52)))) (.split 34 0 (.step 5 (.close 7)) (.step 7 (.close 5)))) (.step 7 (.step 5 (.step 18 (.close 4))))) (.split 17 0 (.split 34 0 (.step 5 (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.step 7 (.split 13 0 (.step 18 (.step 3 (.step 7 (.close 27)))) (.step 58 (.step 18 (.step 3 (.close 15))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11578457230703696874347711492183134751562017083787797120494327942557771010665042900802197551944822644225191831993736597382200024103885071655989556969969163104129006069418159104461855140240311143954814459070201662030352482304⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 73 1 (.split 74 1 (.split 2 0 (.reuse 0) (.run (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 5 (.step 10 (.step 7 (.step 3 (.close 5))))) (.step 5 (.close 3))) (.step 5 (.close 7))) (.step 5 (.close 7))) (.step 63 (.split 20 0 (.step 3 (.step 5 (.close 3))) (.step 5 (.close 3))))) (.split 14 0 (.split 30 0 (.split 43 0 (.split 51 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 5 (.step 18 (.close 16))))) (.step 7 (.step 3 (.close 5)))))) (.run (.split 2 0 (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 20 0 (.step 7 (.split 17 0 (.step 31 (.step 27 (.close 63))) (.step 7 (.close 5)))) (.step 5 (.close 23))) (.step 7 (.close 18))) (.step 23 (.step 7 (.split 16 0 (.split 17 0 (.step 44 (.step 63 (.step 7 (.close 5)))) (.step 7 (.close 18))) (.step 7 (.step 17 (.close 18))))))) (.step 23 (.close 76))) (.step 7 (.close 63))) (.step 23 (.step 3 (.step 23 (.close 5))))))) (.run (.split 74 1 (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 76 (.step 10 (.split 20 0 (.split 2 0 (.step 18 (.step 5 (.close 7))) (.step 3 (.close 5))) (.step 5 (.close 7))))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 5 (.close 18)))) (.split 34 0 (.step 5 (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 5)))) (.split 16 0 (.step 16 (.close 76)) (.step 18 (.close 76)))) (.step 18 (.step 16 (.step 76 (.close 3))))) (.step 23 (.close 76)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11578457230703702011204076731327295259028151583830417592595522381253978734077371731857790545491029535505612768037828793850585700012199878051465129812480461565259843150674919828071091739620109056385765333447254043783439843328⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 60 1 (.split 67 1 (.split 69 1 (.reuse 0) (.run (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 13 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 38 0 (.split 43 0 (.split 20 0 (.step 72 (.close 7)) (.step 5 (.close 22))) (.step 10 (.close 72))) (.step 18 (.close 72))) (.step 10 (.step 22 (.close 7)))) (.step 7 (.close 72))) (.step 7 (.step 18 (.close 72)))) (.step 72 (.close 18))) (.step 7 (.step 18 (.close 72)))) (.step 7 (.close 72))) (.step 7 (.step 18 (.step 30 (.close 72))))) (.step 18 (.step 63 (.step 3 (.step 7 (.close 34)))))) (.step 30 (.split 10 0 (.split 13 0 (.split 14 0 (.step 72 (.close 5)) (.step 3 (.close 5))) (.step 16 (.step 3 (.close 5)))) (.step 3 (.close 7))))) (.step 63 (.close 3))) (.step 76 (.close 72))))) (.run (.split 73 1 (.split 74 1 (.split 13 0 (.split 14 0 (.split 20 0 (.split 38 0 (.step 70 (.split 39 0 (.split 69 1 (.step 7 (.close 70)) (.step 70 (.close 3))) (.step 3 (.step 7 (.step 65 (.close 7)))))) (.step 3 (.close 70))) (.step 7 (.close 70))) (.step 3 (.step 7 (.close 70)))) (.step 3 (.step 70 (.step 7 (.close 52))))) (.step 3 (.step 7 (.close 70)))) (.step 3 (.close 70))))) (.run (.step 63 (.split 69 1 (.step 31 (.split 73 1 (.split 67 1 (.step 63 (.close 3)) (.step 3 (.close 70))) (.step 5 (.close 3)))) (.step 63 (.close 72))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483124927907801850145674984221478180035297219452315726471468748921958896817184311718218587080020536357631599701769891101793719427119191229155565506125342325181754297478439843610492928⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 61 1 (.split 62 1 (.reuse 0) (.run (.split 60 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 17 0 (.split 20 0 (.step 65 (.split 10 0 (.split 38 0 (.step 65 (.step 7 (.close 3))) (.step 7 (.close 65))) (.step 7 (.close 3)))) (.step 18 (.close 65))) (.step 7 (.step 18 (.close 65)))) (.step 18 (.step 63 (.step 3 (.step 7 (.close 34)))))) (.step 30 (.split 10 0 (.split 13 0 (.split 34 0 (.step 5 (.close 65)) (.step 3 (.close 4))) (.step 16 (.step 3 (.close 5)))) (.step 3 (.close 7))))) (.step 63 (.close 3))) (.step 76 (.close 65))) (.step 65 (.close 5))) (.step 65 (.close 70))) (.step 63 (.close 65))))) (.run (.split 60 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 13 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 64 (.step 4 (.step 7 (.close 3)))) (.step 18 (.close 64))) (.step 7 (.close 64))) (.step 7 (.close 64))) (.step 64 (.step 5 (.close 7)))) (.step 18 (.close 64))) (.step 7 (.step 18 (.close 64)))) (.step 7 (.step 18 (.step 30 (.step 5 (.step 7 (.close 35))))))) (.step 18 (.step 52 (.step 63 (.close 64))))) (.step 30 (.split 10 0 (.split 13 0 (.split 34 0 (.step 5 (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 14 (.step 12 (.close 18))))) (.step 3 (.close 7))))) (.step 63 (.close 3))) (.step 76 (.close 64))) (.step 64 (.close 72))) (.step 64 (.step 63 (.step 64 (.close 70))))) (.step 64 (.close 65))) (.step 63 (.close 64)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨8104522595470689372094546608771799123071184047348509570304018222052056272290836223436927829974812098219136497287696853871865529444163623648216552410378835326291370709770720772096, 11578457230703702011204076731327295263383478979464600218592531848623631091404783846308812096963826258243601379270033907548989930598494988419969392511383407234161038260208808501535659502739567433550912356261360393218373451776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 10 0 (.split 16 0 (.step 62 (.step 7 (.step 5 (.step 7 (.close 3))))) (.step 18 (.step 7 (.step 4 (.close 62))))) (.step 7 (.step 31 (.close 62)))) (.step 31 (.step 27 (.step 44 (.step 18 (.close 34)))))) (.split 14 0 (.split 16 0 (.step 5 (.step 52 (.step 62 (.step 4 (.close 7))))) (.step 3 (.step 5 (.close 7)))) (.step 3 (.step 23 (.close 5))))) (.step 9 (.split 10 0 (.split 14 0 (.split 16 0 (.step 5 (.close 62)) (.step 3 (.close 4))) (.step 3 (.step 23 (.close 5)))) (.step 3 (.close 7))))) (.step 31 (.close 44))) (.step 5 (.step 62 (.close 76)))) (.step 44 (.split 14 0 (.split 20 0 (.split 30 0 (.split 34 0 (.step 72 (.step 62 (.close 3))) (.step 7 (.close 62))) (.step 7 (.close 62))) (.step 3 (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 7 (.close 62)))))) (.step 62 (.close 70))) (.step 44 (.step 65 (.step 70 (.split 10 0 (.split 14 0 (.split 20 0 (.split 34 0 (.step 65 (.step 4 (.close 62))) (.step 7 (.close 62))) (.step 4 (.close 62))) (.step 4 (.step 7 (.close 62)))) (.step 7 (.close 62))))))) (.step 44 (.step 70 (.step 76 (.split 14 0 (.step 64 (.step 52 (.split 20 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 16 0 (.step 62 (.step 3 (.close 64))) (.step 4 (.step 7 (.close 42)))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.close 64))) (.step 7 (.close 62))) (.step 3 (.step 4 (.close 7)))))) (.step 4 (.close 52))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126386009060033576462822902249213795606440986345643339556078820331676058840840180268997940743569429103581277766478884789505753859875408973882285996229708129829503082276323328⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 58 1 (.split 59 1 (.reuse 0) (.split 60 1 (.reuse 1) (.run (.step 31 (.step 62 (.close 63)))))) (.run (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 67 1 (.split 73 1 (.split 2 0 (.split 10 0 (.split 13 0 (.split 20 0 (.split 30 0 (.split 74 1 (.split 34 0 (.step 61 (.step 5 (.close 7))) (.step 7 (.step 5 (.close 31)))) (.step 44 (.close 61))) (.step 42 (.step 3 (.step 7 (.close 27))))) (.split 30 0 (.step 61 (.close 23)) (.step 5 (.close 3)))) (.split 74 1 (.split 14 0 (.split 16 0 (.step 5 (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 5))) (.step 23 (.close 5))) (.step 23 (.close 3)))) (.step 31 (.step 61 (.step 18 (.step 3 (.close 7)))))) (.split 20 0 (.split 30 0 (.split 43 0 (.split 67 0 (.split 74 1 (.split 13 0 (.step 61 (.close 3)) (.step 5 (.close 3))) (.step 23 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 5 (.close 3)))) (.step 5 (.step 22 (.step 5 (.close 3))))) (.step 3 (.step 44 (.step 54 (.step 27 (.step 7 (.close 61))))))) (.step 5 (.step 61 (.step 72 (.close 18))))) (.step 5 (.step 63 (.step 72 (.step 65 (.step 5 (.step 27 (.step 7 (.close 61))))))))) (.step 34 (.step 63 (.step 64 (.step 72 (.step 5 (.step 3 (.step 27 (.step 52 (.close 61)))))))))) (.step 5 (.step 11 (.close 63)))) (.step 44 (.step 61 (.step 5 (.close 62)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578493961620602187929371688242052919635309437302374115269548619918503932890235652736818656209412069125544330970915392250451335848862899735198690288961798012928⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.split 30 0 (.step 22 (.step 10 (.close 58))) (.step 3 (.close 7))) (.step 7 (.close 5))) (.step 18 (.close 5))) (.step 7 (.close 5))) (.step 7 (.close 43))) (.step 18 (.step 5 (.step 3 (.close 5))))) (.step 43 (.step 18 (.step 10 (.step 16 (.step 22 (.close 58))))))) (.step 7 (.close 58))) (.step 43 (.step 3 (.step 43 (.close 5))))) (.step 18 (.step 5 (.close 3)))) (.step 76 (.step 5 (.close 7)))) (.step 18 (.step 22 (.close 18)))) (.step 3 (.step 7 (.step 10 (.step 22 (.close 58)))))) (.step 18 (.step 68 (.step 10 (.step 21 (.step 22 (.step 18 (.step 58 (.close 3))))))))) (.step 18 (.step 68 (.step 10 (.step 64 (.step 22 (.step 43 (.step 18 (.close 58))))))))) (.step 63 (.close 68))) (.step 48 (.step 5 (.close 58)))) (.step 5 (.step 58 (.close 17)))))) (.run (.step 58 (.step 63 (.split 58 1 (.split 59 1 (.split 61 1 (.step 58 (.step 18 (.step 63 (.split 62 1 (.split 67 1 (.split 69 1 (.split 14 0 (.step 58 (.close 7)) (.step 3 (.close 5))) (.step 18 (.close 72))) (.step 7 (.close 70))) (.step 18 (.close 65)))))) (.step 18 (.step 64 (.close 5)))) (.step 48 (.step 58 (.close 3)))) (.step 58 (.close 61)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11578457230703702011204076731327295263383478975412338920857187162576357790292274892669361943302761169919191420460647817446636608363322441528697139806489713473582703650180200930340531806191362237578751239001068091662614396928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 10 0 (.split 16 0 (.split 20 0 (.split 22 0 (.split 17 0 (.split 30 0 (.split 34 0 (.step 53 (.step 5 (.step 31 (.close 3)))) (.step 9 (.step 31 (.step 5 (.close 7))))) (.step 31 (.close 53))) (.step 7 (.step 4 (.close 53)))) (.step 7 (.step 4 (.close 53)))) (.step 7 (.step 9 (.step 31 (.close 3))))) (.step 18 (.step 7 (.close 53)))) (.step 7 (.step 31 (.close 53)))) (.step 31 (.step 52 (.step 18 (.step 3 (.close 53)))))) (.split 14 0 (.split 16 0 (.step 5 (.step 52 (.split 17 0 (.step 53 (.step 5 (.close 7))) (.step 3 (.close 4))))) (.step 3 (.step 5 (.close 7)))) (.step 3 (.step 23 (.close 5))))) (.step 9 (.split 10 0 (.split 14 0 (.split 16 0 (.step 5 (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 23 (.close 5)))) (.step 3 (.close 7))))) (.step 31 (.step 27 (.step 44 (.step 55 (.step 23 (.step 3 (.close 53)))))))) (.step 5 (.step 62 (.step 21 (.step 5 (.step 53 (.close 7))))))) (.step 63 (.step 65 (.split 10 0 (.split 14 0 (.split 20 0 (.step 72 (.step 53 (.step 4 (.close 7)))) (.step 3 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 53)))) (.step 7 (.close 72)))))) (.step 53 (.step 70 (.close 3)))) (.step 63 (.step 65 (.close 7)))) (.step 63 (.step 65 (.step 52 (.step 64 (.step 70 (.split 20 0 (.step 64 (.step 4 (.step 7 (.step 4 (.close 76))))) (.step 3 (.close 4))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316845975281474788451761492167924440459360471309410957840292156231427376967528237411561256703177305410629766622999524120296550859267726569950702577123328⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 59 1 (.split 60 1 (.split 67 1 (.split 73 1 (.split 74 1 (.split 10 0 (.split 13 0 (.split 14 0 (.split 20 0 (.split 38 0 (.split 39 0 (.split 40 0 (.step 54 (.step 64 (.step 65 (.step 7 (.step 22 (.close 7)))))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 54 (.close 7)))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 7 (.step 36 (.close 54))))) (.step 3 (.step 64 (.step 54 (.step 22 (.step 7 (.close 15))))))) (.step 7 (.close 54))) (.step 3 (.step 7 (.step 36 (.close 54))))) (.step 3 (.step 22 (.step 54 (.step 64 (.step 7 (.step 21 (.close 54)))))))) (.step 54 (.close 3))) (.step 3 (.step 7 (.step 54 (.close 63))))) (.step 62 (.close 54))) (.step 3 (.step 7 (.step 22 (.step 54 (.close 21)))))) (.step 3 (.step 54 (.step 58 (.step 15 (.close 22)))))))) (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 60 1 (.reuse 1) (.run (.step 31 (.step 53 (.close 63))))) (.run (.step 53 (.step 44 (.step 53 (.step 26 (.step 5 (.close 62)))))))) (.run (.step 53 (.step 61 (.split 60 1 (.split 73 1 (.step 61 (.close 53)) (.step 3 (.close 5))) (.step 5 (.step 31 (.step 35 (.close 53))))))))) (.run (.step 48 (.step 5 (.close 58))))) (.run (.step 48 (.step 58 (.close 3))))) (.run (.step 53 (.step 54 (.step 4 (.close 7)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11578457230703702011204076731327295263383478975412338920857187162576357787022080955288743649334506228654900470541092335901660749338510850159219724062366598585315804773813059557921510456099611610206433420211266242487727947776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 20 0 (.split 17 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.step 5 (.step 52 (.close 21))) (.step 9 (.close 31))) (.step 7 (.close 3))) (.step 4 (.close 7)))) (.step 7 (.step 4 (.close 52)))) (.step 7 (.step 9 (.step 31 (.close 3))))) (.step 18 (.step 7 (.step 4 (.close 52))))) (.step 31 (.close 52))) (.split 14 0 (.split 16 0 (.step 5 (.step 52 (.close 4))) (.step 3 (.step 5 (.close 7)))) (.step 3 (.close 34)))) (.step 9 (.split 10 0 (.split 14 0 (.split 16 0 (.step 5 (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 23 (.close 5)))) (.step 3 (.close 7))))) (.step 31 (.step 34 (.step 44 (.step 31 (.close 63)))))) (.step 5 (.step 62 (.step 63 (.step 5 (.step 9 (.step 16 (.step 7 (.close 52))))))))) (.step 63 (.split 73 1 (.split 14 0 (.step 64 (.split 20 0 (.split 34 0 (.step 72 (.step 52 (.step 4 (.close 7)))) (.step 4 (.close 52))) (.step 3 (.step 4 (.close 7))))) (.step 4 (.close 52))) (.step 4 (.step 22 (.step 52 (.close 7))))))) (.step 52 (.close 70))) (.step 63 (.step 65 (.step 70 (.split 73 1 (.split 14 0 (.step 64 (.step 53 (.split 20 0 (.split 34 0 (.step 65 (.step 4 (.step 52 (.close 7)))) (.step 4 (.close 52))) (.step 3 (.close 4))))) (.step 4 (.close 52))) (.step 4 (.step 16 (.step 21 (.step 52 (.close 7)))))))))) (.step 64 (.step 52 (.close 7)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809199593181869476517136288093189854454072445229409164763959331136874517934648052031274260183096580256493189205783564726685192421376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 67 1 (.split 73 1 (.split 74 1 (.split 10 0 (.split 13 0 (.split 14 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 55 0 (.split 56 0 (.split 22 0 (.step 46 (.split 61 1 (.split 62 1 (.split 69 1 (.step 4 (.step 7 (.close 3))) (.step 10 (.close 11))) (.step 10 (.close 65))) (.step 10 (.close 64)))) (.step 7 (.close 30))) (.step 7 (.close 10))) (.step 7 (.step 10 (.close 46)))) (.step 7 (.close 10))) (.step 3 (.step 30 (.step 46 (.step 7 (.close 11)))))) (.step 7 (.close 10))) (.step 7 (.step 27 (.close 30)))) (.step 3 (.step 10 (.step 46 (.step 7 (.close 9)))))) (.step 7 (.close 46))) (.step 7 (.step 27 (.close 30)))) (.step 3 (.step 10 (.close 4)))) (.step 46 (.step 7 (.close 3)))) (.step 3 (.step 7 (.step 27 (.close 46))))) (.step 9 (.step 27 (.close 46)))) (.step 3 (.step 11 (.step 9 (.step 27 (.close 30)))))) (.step 3 (.step 7 (.close 10)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 54 (.step 3 (.step 7 (.step 61 (.step 10 (.close 3))))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.close 3))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809199593181869476517136288093189854454072445229409164763959331136874517934648052031274260183096580256493189205783564726685193469952⟩
def references : Fin 3 → Box := ![Part8.root, Part9.root, Part10.root]
def proof : Chunks.Proof 3 := (.split 2 1 (.split 43 1 (.split 49 1 (.reuse 0) (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 60 1 (.reuse 1) (.run (.step 31 (.step 52 (.close 63))))) (.run (.step 52 (.close 62)))) (.run (.step 34 (.step 61 (.step 5 (.close 52)))))) (.run (.step 48 (.step 5 (.close 58))))) (.run (.step 48 (.step 58 (.close 3))))) (.run (.step 52 (.step 54 (.close 3))))) (.run (.step 52 (.step 5 (.step 7 (.step 5 (.close 53)))))))) (.reuse 2)) (.run (.step 3 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 13 0 (.step 5 (.close 3)) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 5 (.close 64)))) (.step 5 (.close 23))) (.step 5 (.close 43))) (.step 3 (.step 5 (.close 23)))) (.step 3 (.step 5 (.close 52)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343947642470400, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869699891253484503727947475856254594249320292252662744571170621257309603584563601352732186683580062770823922394333555195904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 5 (.step 43 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 13 0 (.split 14 0 (.split 30 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 5 (.step 31 (.close 4))) (.step 43 (.close 3))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.close 43))) (.step 7 (.close 5))) (.step 31 (.close 5))) (.step 43 (.close 3))) (.step 5 (.close 31))) (.step 43 (.close 3))) (.step 68 (.step 22 (.step 4 (.close 43))))) (.step 3 (.step 7 (.close 4)))) (.step 68 (.step 21 (.step 65 (.step 4 (.step 18 (.step 43 (.close 3)))))))) (.step 5 (.step 34 (.step 64 (.step 18 (.step 4 (.step 10 (.step 24 (.close 43))))))))) (.step 5 (.step 24 (.close 16)))) (.step 5 (.step 9 (.close 31)))) (.step 5 (.step 31 (.close 61)))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 31 (.close 53)))) (.step 5 (.step 31 (.close 52)))) (.step 7 (.step 9 (.close 10)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11578457230703702011204076731327295263383483128980169099585490361031494782565934858755044339400726253900933591651241889703805916164110344715047205812583328323536969346137755639504343211093532060554912052044175418919276773376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 67 1 (.split 73 1 (.split 2 0 (.split 10 0 (.split 13 0 (.split 20 0 (.split 30 0 (.split 34 0 (.split 74 1 (.split 36 0 (.step 42 (.step 3 (.close 7))) (.step 7 (.step 5 (.close 7)))) (.step 23 (.close 42))) (.step 7 (.step 5 (.close 31)))) (.step 7 (.close 42))) (.step 42 (.close 23))) (.split 74 1 (.split 14 0 (.split 16 0 (.step 5 (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 5))) (.step 23 (.close 5))) (.step 23 (.close 3)))) (.split 74 1 (.step 7 (.split 13 0 (.step 42 (.step 4 (.close 7))) (.step 3 (.close 5)))) (.step 18 (.close 31)))) (.split 20 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 74 1 (.split 13 0 (.step 42 (.close 3)) (.step 5 (.close 3))) (.step 23 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 5 (.close 3)))) (.step 5 (.step 21 (.step 23 (.step 5 (.close 3)))))) (.step 3 (.step 44 (.step 70 (.step 7 (.close 34)))))) (.step 5 (.step 35 (.step 36 (.step 63 (.step 65 (.step 72 (.step 5 (.step 7 (.close 42)))))))))) (.step 35 (.step 42 (.step 21 (.step 5 (.close 65)))))) (.step 5 (.step 34 (.step 35 (.step 63 (.step 30 (.step 64 (.step 65 (.step 5 (.step 42 (.close 7))))))))))) (.step 5 (.step 11 (.close 63)))) (.step 44 (.step 42 (.step 5 (.close 62))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702412981881072974617061714821003440603817355976054359757369948087475310756977174211317196620375405424934018524934832128⟩
def references : Fin 3 → Box := ![Part11.root, Part12.root, Part13.root]
def proof : Chunks.Proof 3 := (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 2 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 7))) (.step 31 (.close 76))) (.step 7 (.step 22 (.step 31 (.close 16))))) (.step 7 (.step 18 (.step 21 (.step 31 (.close 37)))))) (.step 4 (.step 68 (.step 18 (.close 64))))) (.step 4 (.step 5 (.close 31)))) (.step 76 (.split 61 1 (.split 62 1 (.split 69 1 (.split 13 0 (.step 7 (.step 31 (.close 7))) (.step 31 (.close 59))) (.step 7 (.close 22))) (.step 7 (.close 59))) (.step 7 (.close 59))))) (.step 7 (.step 31 (.close 45)))) (.step 7 (.step 31 (.close 45)))) (.step 31 (.step 7 (.close 45)))) (.step 4 (.step 5 (.close 16)))))))) (.reuse 1)) (.split 2 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.reuse 2) (.run (.step 61 (.split 60 1 (.split 61 1 (.step 42 (.step 44 (.step 42 (.close 3)))) (.step 5 (.close 42))) (.step 5 (.close 42)))))) (.run (.step 5 (.step 58 (.close 23))))) (.run (.step 5 (.step 42 (.step 5 (.close 3)))))) (.run (.step 42 (.step 3 (.step 54 (.step 36 (.step 42 (.step 54 (.close 4))))))))) (.run (.step 21 (.step 42 (.step 35 (.close 53)))))) (.run (.step 52 (.step 61 (.step 34 (.step 42 (.step 5 (.close 52)))))))) (.run (.step 3 (.step 27 (.close 46))))) (.run (.step 4 (.step 31 (.close 42))))) (.run (.step 5 (.step 27 (.step 31 (.close 42)))))) (.run (.step 5 (.close 42)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11578457230703702011204076731327295263383483128984126386009060033576462822902249213795606440986345643339556081282957063333495790947709004199719432246587285681856895631557843519217486127549545499387870638437057053496525717504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 20 0 (.split 30 0 (.split 43 0 (.split 51 0 (.step 43 (.close 58)) (.step 3 (.step 7 (.close 21)))) (.step 3 (.close 10))) (.step 3 (.close 7))) (.step 18 (.close 5))) (.step 7 (.close 21))) (.step 18 (.step 5 (.step 3 (.close 5))))) (.step 43 (.step 18 (.step 10 (.step 16 (.step 21 (.step 7 (.close 5)))))))) (.step 7 (.close 58))) (.step 43 (.step 3 (.step 43 (.close 5))))) (.step 18 (.step 5 (.close 3)))) (.step 76 (.step 5 (.close 7)))) (.step 18 (.step 68 (.step 10 (.step 21 (.step 22 (.step 43 (.step 7 (.close 15))))))))) (.step 3 (.step 7 (.step 21 (.close 70))))) (.step 18 (.step 21 (.step 10 (.step 18 (.close 21)))))) (.step 18 (.step 68 (.step 10 (.step 64 (.step 21 (.step 43 (.step 64 (.close 7))))))))) (.step 63 (.close 68))) (.step 26 (.step 48 (.close 58)))) (.step 5 (.step 42 (.close 58)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444506460249272012482261009699579680173459758763847786694855813076114587892786980410012016335732161568939184226304⟩
def references : Fin 2 → Box := ![Part14.root, Part15.root]
def proof : Chunks.Proof 2 := (.split 38 1 (.reuse 0) (.step 43 (.split 2 1 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.reuse 1) (.run (.step 43 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 74 1 (.split 73 1 (.split 14 0 (.step 28 (.split 16 0 (.step 59 (.close 7)) (.step 18 (.step 5 (.close 7))))) (.step 18 (.step 5 (.close 3)))) (.step 21 (.close 41))) (.step 5 (.close 41))) (.step 21 (.step 22 (.close 3)))) (.step 7 (.step 21 (.close 59)))) (.step 18 (.step 21 (.close 7)))) (.step 10 (.step 21 (.step 22 (.step 41 (.close 3)))))) (.step 22 (.step 31 (.step 5 (.close 41))))) (.step 22 (.close 58)))))) (.run (.step 5 (.step 41 (.close 58))))) (.run (.step 7 (.step 18 (.step 3 (.step 22 (.step 21 (.step 54 (.close 16))))))))) (.run (.step 31 (.step 21 (.step 42 (.step 7 (.step 9 (.close 21)))))))) (.run (.step 48 (.step 5 (.step 16 (.step 58 (.close 26))))))) (.run (.step 3 (.step 7 (.step 9 (.close 10)))))) (.run (.step 31 (.step 60 (.step 76 (.split 49 1 (.split 50 1 (.split 61 1 (.split 69 1 (.split 13 0 (.split 14 0 (.step 41 (.step 7 (.step 31 (.close 7)))) (.step 7 (.close 5))) (.step 31 (.close 41))) (.step 7 (.close 41))) (.step 7 (.close 41))) (.step 5 (.step 7 (.close 21)))) (.step 16 (.close 58)))))))) (.run (.step 42 (.step 43 (.close 42))))) (.run (.step 5 (.step 31 (.step 21 (.step 3 (.step 22 (.close 3))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11578457230703702011199177848016637920946531129067155869189227224388008407774805038344188571496963533808523375941142655527226249485474442505551299915869188104912230761225618659496026897981813444331294759915376638508221333504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 16)))) (.step 7 (.step 22 (.step 31 (.close 16))))) (.step 7 (.step 21 (.step 22 (.step 31 (.close 16)))))) (.step 4 (.step 68 (.step 18 (.close 64))))) (.step 4 (.step 5 (.close 31)))) (.step 22 (.split 2 0 (.split 13 0 (.step 7 (.step 22 (.close 5))) (.step 22 (.close 7))) (.step 7 (.close 5))))) (.step 5 (.step 7 (.step 22 (.close 31))))) (.step 7 (.step 22 (.step 31 (.close 39))))) (.step 31 (.step 7 (.close 52)))) (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 61 1 (.step 39 (.split 62 1 (.split 69 1 (.split 73 1 (.split 13 0 (.step 7 (.step 31 (.close 7))) (.step 31 (.close 39))) (.step 31 (.close 39))) (.step 7 (.close 39))) (.step 7 (.step 31 (.step 21 (.close 72)))))) (.step 7 (.step 22 (.step 31 (.step 37 (.close 64)))))) (.step 7 (.close 45))) (.step 5 (.close 39))) (.step 7 (.step 31 (.close 39)))) (.step 7 (.step 31 (.close 45)))))) (.step 31 (.close 36))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11578457230703702011204076731327295263383478979468557508793749456170633625688020939544079785372302305209790472450982751479054487577946848673037265645828663824259173693630401811864817193670629600556711458188104938314269720576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 16)))) (.step 7 (.step 16 (.step 22 (.close 31))))) (.step 7 (.step 16 (.step 21 (.step 4 (.step 22 (.close 31))))))) (.step 4 (.step 16 (.step 7 (.step 31 (.close 64)))))) (.step 4 (.step 5 (.close 31)))) (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 13 0 (.step 7 (.step 31 (.close 7))) (.step 16 (.close 59))) (.step 16 (.close 59))) (.step 7 (.close 22))) (.step 7 (.close 59))) (.step 7 (.close 59))) (.step 7 (.step 16 (.close 31))))) (.step 5 (.step 16 (.close 58)))) (.step 7 (.step 31 (.close 37)))) (.step 31 (.step 7 (.close 16)))) (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 37 (.split 69 1 (.split 73 1 (.split 13 0 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 16)))) (.step 31 (.close 45))) (.step 7 (.close 37)))) (.step 7 (.close 37))) (.step 31 (.step 37 (.close 64)))) (.step 7 (.close 45))) (.step 5 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 16 (.close 31)))))) (.step 31 (.close 34))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057666703390733911791055578724518340511961169901986109202775886889635640980111423830913823277056⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.step 31 (.split 2 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 16 (.step 31 (.split 42 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 61 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 13 0 (.split 14 0 (.step 41 (.step 7 (.step 31 (.close 7)))) (.step 7 (.close 5))) (.step 16 (.close 41))) (.step 3 (.step 5 (.close 16)))) (.step 16 (.close 41))) (.step 7 (.close 41))) (.step 7 (.close 41))) (.step 7 (.step 16 (.step 21 (.close 31))))) (.step 5 (.close 41))) (.step 5 (.step 16 (.close 21)))) (.step 37 (.close 31))))))) (.run (.step 31 (.split 49 1 (.split 50 1 (.split 55 1 (.split 59 1 (.split 61 1 (.step 39 (.split 62 1 (.split 69 1 (.split 73 1 (.split 13 0 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 16)))) (.step 16 (.step 31 (.step 7 (.close 21))))) (.step 7 (.close 37))) (.step 7 (.close 37)))) (.step 31 (.step 37 (.close 64)))) (.step 7 (.step 31 (.close 37)))) (.step 31 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 37))))))) (.run (.step 3 (.step 4 (.step 5 (.close 37)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847170206749890122221370379775139026523030084995361411187167620006674432⟩
def references : Fin 3 → Box := ![Part16.root, Part17.root, Part19.root]
def proof : Chunks.Proof 3 := (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 7 (.step 31 (.split 2 1 (.split 38 1 (.reuse 1) (.run (.step 31 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 13 0 (.split 14 0 (.step 41 (.step 7 (.step 31 (.close 7)))) (.step 7 (.close 5))) (.step 31 (.close 41))) (.step 3 (.step 5 (.close 16)))) (.step 21 (.step 22 (.close 41)))) (.step 7 (.close 41))) (.step 7 (.close 41))) (.step 7 (.step 21 (.step 22 (.close 31))))) (.step 5 (.step 7 (.close 21)))) (.step 16 (.close 58))) (.step 38 (.step 39 (.close 31))))))) (.run (.step 3 (.step 4 (.step 5 (.close 31))))))))) (.reuse 2)) (.run (.step 3 (.step 31 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.step 7 (.step 3 (.step 7 (.close 18))))) (.step 7 (.close 3))) (.step 3 (.close 31))) (.step 7 (.close 31))) (.step 31 (.close 7))) (.step 18 (.step 31 (.close 42))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨3213876088517980551083924184682325205044405987565587818086400, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757180616536739123927342288349919410022966730481817616384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 5 (.step 18 (.step 23 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 34 0 (.split 36 0 (.split 73 1 (.split 38 0 (.split 39 0 (.split 10 0 (.split 13 0 (.split 40 0 (.split 14 0 (.step 5 (.step 18 (.close 4))) (.step 3 (.close 23))) (.step 18 (.close 5))) (.step 5 (.step 18 (.step 5 (.close 7))))) (.step 7 (.close 5))) (.step 23 (.close 3))) (.step 18 (.close 5))) (.step 5 (.close 18))) (.step 18 (.close 23))) (.step 18 (.close 23))) (.step 5 (.step 10 (.close 18)))) (.step 3 (.step 7 (.close 70)))) (.step 5 (.step 18 (.close 65)))) (.step 5 (.step 18 (.close 64)))) (.step 26 (.step 31 (.step 4 (.step 9 (.close 23)))))) (.step 5 (.step 23 (.close 3)))) (.step 5 (.step 18 (.close 16)))) (.step 5 (.close 23))) (.step 3 (.step 7 (.step 22 (.close 54))))) (.step 5 (.step 21 (.step 48 (.step 53 (.step 31 (.step 4 (.step 9 (.step 23 (.step 3 (.step 4 (.close 7)))))))))))) (.step 5 (.step 55 (.step 34 (.step 27 (.step 52 (.step 4 (.step 23 (.close 52))))))))) (.step 3 (.step 7 (.step 9 (.close 10))))) (.step 7 (.step 23 (.close 16)))) (.step 18 (.step 5 (.close 23)))) (.step 23 (.step 21 (.step 5 (.step 23 (.close 42)))))) (.step 5 (.step 18 (.close 41)))) (.step 7 (.step 22 (.step 23 (.close 16))))) (.step 7 (.step 31 (.close 37))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182113114415750771930528923188111496778858156741623808⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 60 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.step 7 (.close 17)))) (.step 7 (.close 72))) (.step 7 (.step 18 (.close 20)))) (.step 7 (.step 18 (.close 20)))) (.step 7 (.close 63)))) (.step 4 (.step 7 (.step 18 (.close 19))))) (.step 18 (.step 7 (.close 61)))) (.step 7 (.step 18 (.step 23 (.step 19 (.close 44)))))) (.step 7 (.step 48 (.step 11 (.step 23 (.step 52 (.close 19))))))) (.step 7 (.step 18 (.close 19)))) (.step 23 (.step 42 (.step 18 (.step 7 (.close 42)))))) (.step 5 (.step 18 (.close 7)))) (.step 18 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.step 20 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.step 7 (.close 17)))) (.step 7 (.close 20))) (.step 7 (.step 18 (.close 20))))) (.step 7 (.step 18 (.close 20)))) (.step 18 (.close 20))) (.step 7 (.close 20))) (.step 18 (.close 20))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 20 (.close 52)))) (.step 18 (.step 19 (.step 20 (.step 7 (.close 42)))))) (.step 7 (.step 18 (.close 5)))))) (.step 3 (.step 4 (.step 5 (.close 18))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11578457230703702011199177848016637920946535278582724750178500226615382312459157657644924457595074765903874223970566569746915425722473298253107587561110854330115918430400002907745012382747849347717331733726375555520877559808⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 60 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.step 7 (.close 17)))) (.step 7 (.step 18 (.close 14)))) (.step 7 (.step 18 (.close 19)))) (.step 7 (.step 18 (.close 19)))) (.step 7 (.close 63)))) (.step 4 (.step 7 (.close 19)))) (.step 18 (.step 7 (.step 23 (.close 61))))) (.step 7 (.step 23 (.step 19 (.close 17))))) (.step 4 (.step 42 (.step 7 (.step 23 (.step 19 (.step 44 (.close 52)))))))) (.step 18 (.step 23 (.step 42 (.close 5))))) (.step 5 (.step 18 (.close 7)))) (.step 18 (.split 38 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.step 19 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.close 19))) (.step 7 (.step 18 (.close 14)))) (.step 7 (.step 18 (.close 19))))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 11 (.step 18 (.close 19)))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 52)))) (.step 7 (.step 18 (.close 5)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575917388102833447126872944213061877812674166784⟩
def references : Fin 4 → Box := ![Part20.root, Part21.root, Part22.root, Part23.root]
def proof : Chunks.Proof 4 := (.split 16 1 (.split 17 1 (.split 20 1 (.split 22 1 (.reuse 0) (.run (.split 2 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 60 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.step 7 (.close 17)))) (.step 7 (.step 18 (.close 14)))) (.step 7 (.step 18 (.close 25)))) (.step 7 (.step 14 (.step 18 (.close 44))))) (.step 7 (.close 63)))) (.step 4 (.step 7 (.close 62)))) (.step 18 (.step 7 (.step 23 (.close 61))))) (.step 7 (.step 18 (.step 23 (.close 62))))) (.step 7 (.step 48 (.step 11 (.step 23 (.step 44 (.close 52))))))) (.step 23 (.step 42 (.step 18 (.step 7 (.close 42)))))) (.step 5 (.step 18 (.close 7)))) (.step 3 (.step 4 (.step 5 (.close 18))))))) (.reuse 1)) (.reuse 2)) (.step 7 (.step 18 (.split 2 1 (.split 17 1 (.reuse 3) (.run (.step 18 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.step 19 (.split 62 1 (.split 69 1 (.split 38 0 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.close 19))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 18 (.close 14)))) (.step 7 (.step 18 (.close 19))))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 11 (.step 18 (.close 19)))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 52)))) (.step 19 (.close 42)))))) (.run (.step 3 (.step 4 (.step 5 (.close 18)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2787593149816327892691964784081047335731200, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027806426923487748661657557873909046770750636008154033348188788851556259896626842426408234287170789015586559744340804553195378812387328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.step 63 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.step 63 (.step 7 (.step 31 (.step 27 (.close 63))))) (.step 7 (.close 5))) (.step 5 (.close 17))) (.step 7 (.step 18 (.close 3)))) (.step 7 (.step 18 (.close 17)))) (.step 23 (.close 16))) (.step 7 (.close 63))) (.step 23 (.step 3 (.step 23 (.close 5))))) (.split 36 0 (.split 38 0 (.step 11 (.step 77 (.close 7))) (.step 23 (.close 17))) (.step 23 (.close 17)))) (.step 23 (.close 16))) (.step 16 (.step 63 (.close 3)))) (.step 3 (.step 7 (.close 70)))) (.step 5 (.step 16 (.step 63 (.close 3))))) (.step 34 (.step 16 (.step 7 (.step 30 (.close 34)))))) (.step 55 (.step 27 (.step 63 (.split 2 0 (.step 44 (.step 23 (.step 31 (.step 17 (.close 34))))) (.step 17 (.step 3 (.close 23))))))))) (.step 23 (.step 34 (.step 61 (.close 17))))) (.step 5 (.step 18 (.step 5 (.close 17))))) (.step 5 (.step 18 (.step 31 (.step 34 (.step 23 (.step 17 (.close 58)))))))) (.step 7 (.step 18 (.step 3 (.step 36 (.step 34 (.step 54 (.close 17)))))))) (.step 55 (.step 27 (.step 61 (.step 62 (.step 63 (.split 51 1 (.split 2 0 (.step 55 (.step 34 (.step 53 (.step 23 (.step 17 (.close 35)))))) (.step 17 (.step 3 (.close 23)))) (.step 3 (.close 53))))))))) (.step 31 (.step 34 (.step 31 (.step 34 (.close 52)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2787593149816327892691964784081047335731200, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891746556819137854124141602606413095924531935276177115886500446208⟩
def references : Fin 1 → Box := ![Part25.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 2 1 (.split 43 1 (.reuse 0) (.run (.step 7 (.step 27 (.close 30))))) (.run (.step 5 (.step 17 (.close 23))))) (.run (.step 7 (.step 5 (.close 31))))) (.run (.step 5 (.step 23 (.close 17))))) (.run (.step 23 (.step 31 (.step 61 (.step 34 (.step 42 (.close 17)))))))) (.run (.step 5 (.step 16 (.step 42 (.step 49 (.step 58 (.close 5)))))))) (.run (.step 31 (.step 5 (.close 7))))) (.run (.step 31 (.step 7 (.close 37))))) (.run (.step 31 (.close 7)))) (.run (.step 7 (.step 18 (.split 39 1 (.split 40 1 (.split 49 1 (.step 14 (.split 56 1 (.split 58 1 (.split 62 1 (.split 69 1 (.split 38 0 (.step 11 (.step 17 (.split 39 0 (.step 7 (.step 17 (.close 18))) (.step 17 (.close 3))))) (.step 7 (.step 5 (.close 17)))) (.step 5 (.step 7 (.close 17)))) (.step 5 (.step 7 (.close 17)))) (.step 17 (.close 5))) (.step 5 (.close 17)))) (.step 7 (.close 17))) (.step 5 (.step 7 (.close 17)))) (.step 14 (.step 17 (.close 5)))))))) (.run (.step 7 (.step 18 (.step 61 (.step 74 (.split 22 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 14 (.split 62 1 (.split 38 0 (.step 11 (.step 17 (.split 39 0 (.step 7 (.step 17 (.close 18))) (.step 17 (.close 3))))) (.step 7 (.step 5 (.close 17)))) (.step 5 (.step 7 (.close 17))))) (.step 7 (.close 17))) (.step 5 (.step 7 (.close 17)))) (.step 17 (.close 5))) (.step 17 (.close 20)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2722258935367507707706996859456293175296, 11578457230703702011204076731327295263383483128984126389786707968578493961620602187929371688242052919635309437302374115269548619918503932890235652736818656209412069125544330970915392251812465316546653589052188718688871907328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 60 1 (.split 67 1 (.split 2 0 (.split 10 0 (.split 16 0 (.step 76 (.split 74 1 (.split 17 0 (.split 20 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 49 0 (.split 50 0 (.step 10 (.step 16 (.close 3))) (.step 5 (.step 10 (.step 15 (.close 16))))) (.step 5 (.close 16))) (.step 7 (.step 16 (.close 3)))) (.step 7 (.close 16))) (.step 7 (.step 5 (.close 7)))) (.step 16 (.close 4))) (.step 7 (.step 5 (.close 16)))) (.step 23 (.close 76)))) (.step 18 (.step 5 (.step 16 (.step 7 (.step 5 (.close 7))))))) (.step 5 (.step 16 (.step 7 (.step 15 (.close 16)))))) (.step 5 (.step 16 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 34 0 (.step 5 (.close 3)) (.step 15 (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))))) (.step 3 (.step 26 (.step 16 (.close 70))))) (.step 5 (.step 16 (.close 63)))) (.step 76 (.step 16 (.close 72)))) (.step 76 (.step 16 (.close 65)))) (.step 34 (.step 16 (.step 64 (.close 3))))) (.step 5 (.step 15 (.step 26 (.step 63 (.step 76 (.split 62 1 (.step 52 (.step 5 (.step 9 (.step 7 (.close 16))))) (.step 4 (.step 10 (.step 16 (.close 7))))))))))) (.step 5 (.step 22 (.step 34 (.step 5 (.close 3)))))) (.step 16 (.step 58 (.step 76 (.step 16 (.step 5 (.close 3))))))) (.step 5 (.step 10 (.step 16 (.step 18 (.step 15 (.close 58))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨2722258935367507707706996859456293175296, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575918783260537822974573144048952348062341136384⟩
def references : Fin 1 → Box := ![Part27.root]
def proof : Chunks.Proof 1 := (.split 14 1 (.split 16 1 (.split 17 1 (.split 20 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 16 (.step 3 (.step 54 (.step 22 (.step 54 (.step 16 (.step 54 (.step 7 (.close 52))))))))))) (.run (.step 5 (.step 15 (.step 21 (.step 58 (.step 62 (.step 63 (.step 65 (.step 52 (.step 5 (.step 9 (.step 16 (.step 7 (.close 22))))))))))))))) (.run (.step 15 (.step 16 (.step 34 (.step 5 (.close 52))))))) (.run (.step 3 (.step 10 (.close 46))))) (.run (.step 16 (.step 31 (.step 7 (.step 16 (.close 5))))))) (.run (.step 5 (.step 16 (.step 43 (.close 3)))))) (.run (.step 5 (.step 23 (.step 21 (.step 43 (.step 34 (.step 16 (.step 5 (.close 3)))))))))) (.run (.step 43 (.step 76 (.step 16 (.step 5 (.close 41))))))) (.run (.step 16 (.step 22 (.step 31 (.step 41 (.step 7 (.step 16 (.close 5))))))))) (.run (.step 16 (.step 31 (.step 41 (.step 16 (.close 7))))))) (.run (.step 3 (.step 16 (.close 18))))) (.run (.step 18 (.close 26)))) (.run (.step 5 (.step 16 (.close 7))))) (.run (.step 18 (.close 22)))) (.run (.step 18 (.close 21)))) (.run (.step 16 (.step 23 (.close 16)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part27.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575918783260537824242223744277181749559044341760⟩
def references : Fin 3 → Box := ![Part24.root, Part26.root, Part28.root]
def proof : Chunks.Proof 3 := (.split 10 1 (.split 13 1 (.split 14 1 (.reuse 0) (.step 23 (.split 16 1 (.reuse 1) (.run (.step 7 (.step 18 (.step 42 (.split 17 1 (.split 22 1 (.split 40 1 (.split 49 1 (.step 14 (.split 56 1 (.split 58 1 (.split 69 1 (.split 38 0 (.step 11 (.step 17 (.split 39 0 (.step 7 (.step 17 (.close 18))) (.step 17 (.close 3))))) (.step 7 (.step 5 (.close 17)))) (.step 5 (.step 7 (.close 17)))) (.step 17 (.close 5))) (.step 5 (.close 17)))) (.step 7 (.close 17))) (.step 5 (.step 7 (.close 17)))) (.step 17 (.close 19))) (.step 17 (.close 19)))))))))) (.reuse 2)) (.run (.step 3 (.step 7 (.step 31 (.split 13 1 (.split 14 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.step 7 (.step 3 (.step 7 (.close 18))))) (.step 7 (.close 3))) (.step 3 (.close 31))) (.step 7 (.close 31))) (.step 31 (.close 7))) (.step 18 (.step 31 (.close 42)))) (.step 3 (.step 7 (.step 17 (.step 7 (.close 17)))))) (.step 15 (.step 3 (.close 16)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part24.excludes
  · exact Part26.excludes
  · exact Part28.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part29

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part29.excludes
end FiveColour.Packed.ProjectedChunks.Case17
