module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case1
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575918783260537824242226164490004220252216360960⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨8697816018884211022451, 5789228615357111146515144370645293582521562950893008474422619893061853696606201481707084707191459675456370831556440846149949944370837561739506646933964126675846887447766945946864215253787366754672169104713068902630525239296, 0⟩]
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
def root : Box := ⟨2147483648, 5789228615351851005602038365663647631691741564492063194893353984289248658424585975995156013904601150434851207722254404397047265528834370213355123138570923585945874081878591057287959391630268912121111872138590874780595912704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 2 0 (.split 14 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 34 0 (.step 5 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.step 4 (.close 11))))) (.step 31 (.close 3))) (.step 31 (.step 3 (.close 9)))) (.step 7 (.close 3))) (.step 7 (.close 5))) (.step 7 (.step 5 (.step 7 (.step 31 (.step 5 (.close 7))))))) (.step 7 (.step 18 (.close 3)))) (.step 7 (.step 18 (.close 27)))) (.step 7 (.close 3))) (.step 7 (.step 63 (.split 16 0 (.step 31 (.split 17 0 (.step 5 (.step 3 (.step 7 (.close 11)))) (.step 7 (.close 5)))) (.step 7 (.close 5)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 5 (.split 22 0 (.step 5 (.step 3 (.close 4))) (.step 4 (.close 18)))) (.step 5 (.close 7))) (.step 5 (.close 7))) (.step 5 (.close 3)))) (.split 14 0 (.split 16 0 (.split 20 0 (.split 2 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 22 0 (.split 10 0 (.step 5 (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 7))) (.step 5 (.step 3 (.close 7)))) (.step 7 (.step 5 (.step 3 (.step 7 (.close 21)))))) (.step 7 (.step 22 (.close 31)))) (.step 7 (.step 16 (.close 7)))) (.step 3 (.close 5))) (.step 5 (.close 7))) (.step 5 (.step 7 (.step 18 (.close 3))))) (.step 5 (.step 3 (.close 5))))))
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
def root : Box := ⟨2147483648, 5789228615351851005602038365663647631691745714007632075886312496697112349585736988441388256341501146092180898375065817305193665235883317317149411336457534886735056477029666469063267278505103026084800143426805511636705607680⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 60 1 (.split 7 0 (.split 8 0 (.reuse 0) (.run (.split 13 0 (.split 2 0 (.split 14 0 (.step 7 (.split 16 0 (.step 31 (.split 17 0 (.step 5 (.step 7 (.close 11))) (.step 7 (.close 5)))) (.step 7 (.close 5)))) (.split 16 0 (.split 20 0 (.step 7 (.step 63 (.step 7 (.close 5)))) (.step 5 (.close 11))) (.step 7 (.close 18)))) (.step 63 (.split 20 0 (.step 3 (.step 5 (.close 3))) (.step 5 (.close 3))))) (.split 14 0 (.step 5 (.step 3 (.close 5))) (.step 23 (.close 3)))))) (.run (.split 8 0 (.split 10 0 (.split 13 0 (.split 14 0 (.split 20 0 (.split 2 0 (.split 34 0 (.split 36 0 (.split 16 0 (.split 17 0 (.split 38 0 (.step 5 (.step 7 (.close 9))) (.step 7 (.step 5 (.close 10)))) (.step 7 (.step 4 (.close 8)))) (.step 18 (.close 3))) (.step 7 (.step 10 (.close 3)))) (.step 7 (.step 16 (.step 10 (.close 3))))) (.step 3 (.close 5))) (.step 5 (.close 7))) (.step 5 (.step 3 (.close 5)))) (.split 16 0 (.split 17 0 (.split 2 0 (.split 20 0 (.split 14 0 (.split 34 0 (.split 36 0 (.split 40 0 (.step 10 (.close 3)) (.step 3 (.close 5))) (.step 10 (.close 3))) (.step 10 (.close 3))) (.step 16 (.close 3))) (.step 10 (.close 5))) (.step 10 (.close 5))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 5 (.close 8))))) (.step 7 (.step 16 (.step 5 (.close 7))))) (.split 13 0 (.split 14 0 (.step 5 (.step 3 (.close 5))) (.step 23 (.close 3))) (.split 34 0 (.step 5 (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 5))))))) (.run (.step 63 (.close 3))))
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
def root : Box := ⟨2147483648, 11578457230703696874347711492183134751562021233303366001487286454965634701826193913248429794381722639882521522646548010290346423810934018759783845167855774404918188464569234516237163027115145257918502730358416298886462177280⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 73 1 (.split 74 1 (.reuse 0) (.run (.step 63 (.split 2 0 (.split 7 0 (.split 8 0 (.split 13 0 (.split 16 0 (.split 20 0 (.step 7 (.step 63 (.step 7 (.close 5)))) (.step 5 (.close 23))) (.step 7 (.close 18))) (.step 23 (.close 3))) (.split 10 0 (.step 23 (.step 11 (.close 7))) (.step 7 (.close 11)))) (.step 23 (.step 63 (.step 3 (.step 23 (.close 3)))))) (.step 23 (.step 3 (.step 11 (.step 5 (.close 3))))))))) (.run (.split 60 1 (.split 74 1 (.split 7 0 (.split 8 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 76 (.step 10 (.step 5 (.close 7)))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 16 (.step 5 (.close 7))))) (.split 34 0 (.step 5 (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 5)))) (.split 10 0 (.split 16 0 (.step 76 (.close 3)) (.step 18 (.close 76))) (.step 16 (.step 7 (.close 10))))) (.step 23 (.close 76))) (.step 5 (.step 10 (.step 63 (.close 3)))))))
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
def root : Box := ⟨2147483648, 11578457230703702011204076731327295259028151583830417592595522381253978734077371731857790545491029535505612768037828793850585700012199878051465129812480461565259843150674919828071091739620109056385766543553665279130025852928⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 69 1 (.reuse 0) (.run (.split 60 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 73 1 (.step 72 (.split 20 0 (.split 38 0 (.split 7 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 72))) (.step 5 (.step 3 (.close 7))))) (.step 10 (.step 72 (.close 18)))) (.step 18 (.step 7 (.close 72)))) (.step 68 (.step 30 (.step 63 (.close 72))))) (.step 18 (.step 30 (.step 63 (.step 3 (.close 7)))))) (.step 76 (.split 8 0 (.split 14 0 (.split 20 0 (.step 72 (.close 5)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.step 5 (.step 63 (.close 3)))) (.step 63 (.close 72))))) (.run (.split 60 1 (.split 73 1 (.split 74 1 (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.step 70 (.split 20 0 (.step 70 (.split 38 0 (.step 70 (.split 17 0 (.split 40 0 (.step 70 (.close 3)) (.step 3 (.close 7))) (.step 4 (.close 7)))) (.step 3 (.close 7)))) (.step 3 (.close 7)))) (.step 7 (.close 70))) (.step 3 (.step 70 (.close 4)))) (.step 3 (.step 7 (.close 70)))) (.step 3 (.step 70 (.step 7 (.close 9))))) (.step 3 (.step 7 (.close 70)))) (.step 3 (.close 70))) (.step 3 (.close 63)))))
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
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483124927907801850145674984221478180035297219452315726471468748921958896817184311718218587080020536357631599701769891101793719427119191229155565506125342325182964403889675190196502528⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 61 1 (.split 62 1 (.reuse 0) (.run (.split 60 1 (.split 67 1 (.split 69 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 73 1 (.split 7 0 (.step 65 (.step 7 (.step 5 (.close 7)))) (.split 10 0 (.split 17 0 (.step 10 (.step 5 (.close 7))) (.step 7 (.close 65))) (.step 3 (.step 7 (.close 9))))) (.step 21 (.step 76 (.close 7)))) (.step 68 (.step 30 (.step 63 (.close 65))))) (.step 18 (.step 30 (.step 63 (.step 3 (.close 7)))))) (.step 30 (.step 76 (.split 38 0 (.split 7 0 (.step 5 (.step 3 (.close 4))) (.step 3 (.close 5))) (.step 10 (.step 3 (.close 5))))))) (.step 5 (.step 63 (.close 3)))) (.step 65 (.close 5))) (.step 65 (.close 70))) (.step 63 (.close 65))))) (.run (.split 60 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 73 1 (.split 7 0 (.step 64 (.split 13 0 (.step 7 (.step 5 (.close 64))) (.step 10 (.step 7 (.step 5 (.close 3)))))) (.step 10 (.step 64 (.close 3)))) (.step 10 (.step 76 (.close 7)))) (.step 18 (.step 7 (.step 18 (.close 64))))) (.step 68 (.step 5 (.step 30 (.step 52 (.step 5 (.close 7))))))) (.step 18 (.step 30 (.step 63 (.step 3 (.close 7)))))) (.step 76 (.split 8 0 (.split 14 0 (.split 20 0 (.split 38 0 (.step 64 (.close 5)) (.step 10 (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.step 5 (.step 63 (.close 3)))) (.step 64 (.close 72))) (.step 64 (.step 7 (.step 4 (.close 11))))) (.step 64 (.close 65))) (.step 63 (.close 64)))))
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
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128980169099585490361031494782565934858755044339400726253900931069922845320457136330305543935523763680709270018534950220655359883913310967389614401547514600627549575030074483146752⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.reuse 0) (.run (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 7 0 (.split 8 0 (.split 10 0 (.split 13 0 (.step 62 (.step 7 (.step 5 (.close 62)))) (.step 52 (.step 5 (.step 9 (.step 7 (.close 62)))))) (.step 7 (.step 31 (.close 62)))) (.step 31 (.step 9 (.step 27 (.step 18 (.close 62)))))) (.split 10 0 (.step 9 (.split 13 0 (.step 62 (.step 3 (.close 4))) (.step 4 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 9 (.split 14 0 (.step 5 (.close 62)) (.step 3 (.close 5))))) (.step 31 (.close 44))) (.step 5 (.step 62 (.close 76)))) (.step 44 (.split 8 0 (.split 14 0 (.split 20 0 (.step 72 (.step 62 (.step 4 (.close 7)))) (.step 3 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 62)))) (.step 4 (.step 7 (.close 62)))))) (.step 62 (.close 70))) (.step 44 (.step 65 (.step 70 (.split 8 0 (.split 10 0 (.split 14 0 (.split 20 0 (.step 65 (.step 4 (.step 62 (.close 4)))) (.step 3 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 62)))) (.step 7 (.close 62))) (.step 4 (.step 7 (.close 62)))))))) (.step 44 (.step 65 (.step 70 (.step 76 (.split 7 0 (.step 52 (.step 64 (.split 20 0 (.step 62 (.step 64 (.step 4 (.close 7)))) (.step 4 (.close 7))))) (.step 4 (.step 9 (.close 62))))))))) (.step 62 (.close 63)))))
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
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126386009060033576462822902249213795606440986345643339556078820331676058840840180268997940743569429103581277766478884789505753859875408973882285996230918236240738428862332928⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 58 1 (.reuse 0) (.run (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 2 0 (.split 7 0 (.split 10 0 (.split 20 0 (.split 30 0 (.split 74 1 (.split 34 0 (.step 61 (.step 27 (.step 5 (.close 31)))) (.step 7 (.step 5 (.close 31)))) (.step 11 (.step 23 (.close 61)))) (.step 42 (.step 18 (.step 3 (.close 7))))) (.split 13 0 (.step 61 (.close 23)) (.step 5 (.close 3)))) (.step 31 (.step 61 (.step 7 (.close 61))))) (.step 11 (.split 10 0 (.split 13 0 (.split 30 0 (.split 43 0 (.step 61 (.close 5)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 9 (.close 5))) (.step 3 (.close 5))))) (.split 74 1 (.split 7 0 (.step 61 (.close 5)) (.step 5 (.close 3))) (.step 11 (.step 23 (.close 5))))) (.step 5 (.step 22 (.step 5 (.close 3))))) (.step 5 (.step 61 (.step 72 (.close 18))))) (.step 3 (.step 44 (.step 54 (.step 27 (.close 61)))))) (.step 5 (.step 63 (.step 72 (.step 65 (.step 5 (.step 7 (.close 61)))))))) (.step 34 (.step 63 (.step 64 (.step 72 (.step 5 (.step 3 (.step 52 (.close 61))))))))) (.step 5 (.close 63))) (.step 44 (.step 27 (.step 61 (.step 5 (.close 7))))))))
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
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578493961620602187929371688242052919635309437302374115269548619918503932890235652736818656209412069125544330970915392250451335848862900945305101524308384022528⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 7 0 (.split 8 0 (.split 10 0 (.split 13 0 (.split 16 0 (.step 58 (.step 7 (.step 22 (.step 43 (.split 17 0 (.step 18 (.step 10 (.close 58))) (.step 5 (.close 7))))))) (.step 5 (.close 7))) (.step 22 (.step 43 (.step 7 (.step 10 (.step 16 (.step 5 (.close 18)))))))) (.step 7 (.close 58))) (.step 18 (.step 5 (.step 3 (.step 5 (.close 3)))))) (.split 8 0 (.split 10 0 (.step 43 (.step 7 (.step 10 (.close 3)))) (.step 7 (.close 10))) (.step 10 (.close 3)))) (.step 58 (.step 18 (.close 5)))) (.step 18 (.step 5 (.close 3)))) (.step 76 (.step 5 (.close 3)))) (.step 18 (.step 10 (.step 18 (.close 22))))) (.step 3 (.step 7 (.step 10 (.close 70))))) (.step 18 (.step 10 (.step 65 (.step 18 (.step 21 (.step 22 (.step 18 (.close 58))))))))) (.step 18 (.step 10 (.step 64 (.step 18 (.step 22 (.step 43 (.step 18 (.close 58))))))))) (.step 5 (.step 10 (.step 31 (.step 18 (.step 22 (.step 5 (.close 21)))))))) (.step 26 (.step 31 (.close 58)))) (.step 5 (.step 58 (.close 9)))))) (.run (.step 58 (.split 58 1 (.split 59 1 (.split 61 1 (.step 58 (.step 63 (.step 58 (.split 62 1 (.split 67 1 (.split 69 1 (.step 5 (.step 58 (.close 3))) (.step 18 (.close 72))) (.step 7 (.close 70))) (.step 18 (.close 65)))))) (.step 18 (.step 64 (.close 5)))) (.step 48 (.close 58))) (.step 3 (.step 58 (.close 48)))))))
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

namespace Part8
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11578457230703702011204076731327295263383483128984126389786707968578493964893992795825513558255242616462908589519016161312613409401795300986369449141493211092682161451448488121802076378011406858080157491190494577636911611904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 7 0 (.split 8 0 (.split 10 0 (.split 13 0 (.split 14 0 (.step 53 (.step 7 (.step 31 (.step 4 (.close 3))))) (.step 31 (.step 18 (.step 3 (.close 53))))) (.step 52 (.step 5 (.step 9 (.step 7 (.step 5 (.close 7))))))) (.step 7 (.step 31 (.close 53)))) (.step 31 (.step 9 (.step 27 (.step 18 (.close 53)))))) (.split 10 0 (.step 9 (.split 13 0 (.split 14 0 (.step 5 (.step 9 (.close 53))) (.step 3 (.close 5))) (.step 4 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 9 (.split 14 0 (.step 5 (.close 53)) (.step 3 (.close 5))))) (.step 31 (.step 27 (.step 44 (.step 23 (.step 31 (.close 63))))))) (.step 5 (.step 62 (.step 21 (.step 5 (.step 9 (.step 7 (.close 15)))))))) (.step 63 (.step 65 (.split 8 0 (.split 14 0 (.step 72 (.step 53 (.step 4 (.close 7)))) (.step 4 (.close 53))) (.step 4 (.step 7 (.close 11))))))) (.step 53 (.step 70 (.close 3)))) (.step 63 (.step 65 (.close 7)))) (.step 63 (.step 65 (.step 52 (.step 64 (.step 70 (.step 4 (.step 64 (.step 53 (.step 7 (.close 3))))))))))) (.step 53 (.close 63))) (.step 53 (.step 44 (.step 53 (.step 5 (.close 62)))))) (.step 53 (.step 61 (.split 60 1 (.split 73 1 (.step 61 (.close 53)) (.step 3 (.close 5))) (.step 5 (.close 63)))))) (.step 48 (.step 5 (.close 58)))) (.step 48 (.step 53 (.close 58)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11578457230703702011204076731327295263383483128980169099585490361031494782569131529270567915445661009464239272219931884955225260764023712250420061369821458529953414104896899691778630167082721929359539354645166234228124286976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 7 0 (.split 8 0 (.split 14 0 (.split 20 0 (.split 30 0 (.split 36 0 (.split 39 0 (.step 52 (.step 4 (.close 7))) (.split 40 0 (.step 52 (.close 3)) (.step 5 (.close 7)))) (.step 7 (.step 9 (.close 52)))) (.step 7 (.close 52))) (.step 7 (.step 9 (.step 5 (.close 3))))) (.step 31 (.close 52))) (.step 31 (.step 9 (.step 27 (.step 18 (.close 52)))))) (.split 10 0 (.step 9 (.split 13 0 (.split 14 0 (.step 5 (.step 9 (.step 3 (.close 4)))) (.step 3 (.close 5))) (.step 4 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 9 (.split 14 0 (.step 5 (.step 3 (.close 4))) (.step 3 (.close 5))))) (.step 31 (.step 27 (.step 34 (.step 44 (.step 23 (.close 63))))))) (.step 5 (.step 62 (.step 63 (.step 5 (.step 9 (.close 52))))))) (.step 63 (.split 73 1 (.split 8 0 (.step 64 (.split 14 0 (.split 20 0 (.step 72 (.step 52 (.step 4 (.close 7)))) (.step 4 (.close 7))) (.step 4 (.close 52)))) (.step 4 (.step 7 (.close 52)))) (.step 4 (.step 9 (.step 16 (.close 72))))))) (.step 52 (.close 70))) (.step 63 (.step 65 (.step 70 (.split 73 1 (.split 8 0 (.step 64 (.step 53 (.step 4 (.step 65 (.step 52 (.close 7)))))) (.step 4 (.step 7 (.close 52)))) (.step 4 (.step 16 (.step 21 (.step 52 (.close 7)))))))))) (.step 64 (.step 52 (.close 64)))) (.step 52 (.close 63))) (.step 52 (.close 62))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027806426923487748661657557873909046770750636008154033348188788851556259896626842426408234285776992440678395799204928572390202804273152⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 67 1 (.split 73 1 (.split 74 1 (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 20 0 (.split 38 0 (.step 54 (.step 65 (.split 61 1 (.step 7 (.step 36 (.close 7))) (.step 54 (.close 7))))) (.step 3 (.step 7 (.close 54)))) (.step 7 (.step 4 (.close 54)))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 54 (.close 7)))) (.step 3 (.step 7 (.step 36 (.close 54))))) (.step 3 (.step 64 (.step 54 (.step 22 (.step 7 (.close 9))))))) (.step 3 (.step 7 (.step 36 (.close 54))))) (.step 3 (.step 22 (.step 54 (.step 10 (.step 7 (.step 21 (.close 54)))))))) (.step 54 (.close 3))) (.step 3 (.step 54 (.close 63)))) (.step 62 (.close 54))) (.step 3 (.step 54 (.close 11)))) (.step 3 (.step 7 (.step 10 (.step 22 (.close 54)))))) (.step 3 (.step 7 (.step 54 (.step 58 (.close 22)))))))) (.split 51 1 (.reuse 1) (.run (.step 53 (.step 54 (.step 4 (.close 7))))))) (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.reuse 2) (.run (.step 34 (.step 27 (.step 52 (.step 61 (.step 5 (.close 7)))))))) (.run (.step 48 (.step 5 (.close 58))))) (.run (.step 48 (.step 52 (.close 58))))) (.run (.step 52 (.step 54 (.close 3))))) (.run (.step 52 (.step 5 (.step 7 (.step 5 (.close 53))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809199593181869476517136288093189854454072445229409164763959331136874517934648052031274260183096580256493190415889975962031778430976⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 67 1 (.split 73 1 (.split 74 1 (.split 13 0 (.split 14 0 (.split 20 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 10 0 (.split 17 0 (.step 46 (.step 65 (.split 30 0 (.step 64 (.step 4 (.step 7 (.close 3)))) (.step 7 (.close 3))))) (.step 7 (.close 30))) (.step 7 (.close 46))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 30 (.step 46 (.close 7))))) (.step 7 (.close 10))) (.step 7 (.close 10))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 10 (.step 46 (.step 7 (.close 9)))))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 10 (.close 4)))) (.step 46 (.close 70))) (.step 3 (.step 7 (.step 27 (.close 46))))) (.step 9 (.step 27 (.close 46)))) (.step 3 (.step 27 (.close 46)))) (.step 7 (.step 9 (.close 10)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 54 (.step 3 (.step 7 (.step 10 (.close 11)))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343947642470400, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869699891253484503727947475856254594249320292252662744571170621257309603584563601352732186683580063980930333629680140156928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 43 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 7 0 (.split 8 0 (.split 10 0 (.split 13 0 (.split 14 0 (.split 38 0 (.step 31 (.step 5 (.step 24 (.close 4)))) (.step 5 (.close 3))) (.step 5 (.close 31))) (.step 34 (.close 43))) (.step 7 (.close 5))) (.step 31 (.close 5))) (.step 43 (.close 3))) (.step 5 (.step 43 (.close 3)))) (.step 36 (.step 24 (.step 10 (.step 4 (.close 43)))))) (.step 3 (.step 7 (.close 4)))) (.step 68 (.step 10 (.step 21 (.step 4 (.step 18 (.step 3 (.close 65)))))))) (.step 5 (.step 34 (.step 64 (.step 18 (.step 4 (.step 10 (.close 43)))))))) (.step 5 (.step 10 (.close 24)))) (.step 5 (.close 31))) (.step 5 (.step 27 (.step 7 (.close 61))))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 9 (.step 31 (.close 44))))) (.step 5 (.step 31 (.close 52)))) (.step 7 (.step 9 (.close 10))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11578457230703702011204076731327295263383483128984126389786707968578493961620602187929371688242052919635311959030770684516218205777070342081519177840131965997998817816322202697108768071930466361903213579906113148499764707328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 2 0 (.split 7 0 (.split 10 0 (.split 20 0 (.split 30 0 (.split 34 0 (.split 74 1 (.split 36 0 (.step 42 (.step 4 (.close 7))) (.step 7 (.step 5 (.close 7)))) (.step 23 (.close 42))) (.step 7 (.step 5 (.close 31)))) (.step 7 (.close 42))) (.step 42 (.close 23))) (.step 31 (.step 42 (.step 18 (.step 3 (.close 7)))))) (.step 11 (.split 8 0 (.split 10 0 (.split 13 0 (.split 30 0 (.split 43 0 (.split 51 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 9 (.close 5))) (.step 3 (.close 5))) (.step 9 (.close 5))))) (.split 74 1 (.split 7 0 (.step 42 (.close 5)) (.step 5 (.close 3))) (.step 11 (.step 23 (.close 5))))) (.step 5 (.step 21 (.step 23 (.step 5 (.close 3)))))) (.step 5 (.step 35 (.step 36 (.step 63 (.step 30 (.step 65 (.step 72 (.step 5 (.close 7)))))))))) (.step 3 (.step 44 (.step 70 (.step 7 (.close 42)))))) (.step 35 (.step 42 (.step 21 (.step 5 (.close 42)))))) (.step 5 (.step 34 (.step 35 (.step 30 (.step 63 (.step 64 (.step 65 (.step 5 (.step 7 (.close 42))))))))))) (.step 5 (.close 63))) (.step 44 (.step 42 (.step 5 (.close 62))))) (.step 61 (.split 60 1 (.split 61 1 (.step 42 (.step 44 (.step 42 (.close 3)))) (.step 5 (.close 42))) (.step 5 (.close 42))))) (.step 5 (.step 58 (.close 23)))) (.step 5 (.step 42 (.close 58)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702412981881072974617061714821003440603817355976054359757369948087475310756977174211317196620376615531345253871520841728⟩
def references : Fin 3 → Box := ![Part11.root, Part12.root, Part13.root]
def proof : Chunks.Proof 3 := (.split 39 1 (.split 2 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 31 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 7))) (.step 31 (.close 76))) (.step 7 (.step 10 (.step 22 (.close 31))))) (.step 7 (.step 10 (.step 21 (.step 4 (.close 76)))))) (.step 18 (.step 68 (.step 10 (.close 64))))) (.step 4 (.step 5 (.close 31)))) (.step 76 (.split 61 1 (.split 62 1 (.split 69 1 (.split 7 0 (.step 7 (.step 31 (.close 7))) (.step 10 (.close 59))) (.step 7 (.close 22))) (.step 7 (.close 59))) (.step 7 (.close 59))))) (.step 7 (.step 31 (.close 45)))) (.step 7 (.step 31 (.close 45))))))) (.reuse 1)) (.run (.step 3 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 7 0 (.step 5 (.close 3)) (.step 5 (.close 3))) (.step 5 (.close 3))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 10)))) (.step 3 (.step 5 (.close 64)))) (.step 5 (.close 23))) (.step 5 (.close 43))) (.step 5 (.close 23))) (.step 3 (.step 5 (.close 23)))) (.step 3 (.step 5 (.close 10))))))) (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 2) (.run (.step 3 (.step 36 (.step 42 (.step 3 (.step 54 (.step 42 (.close 7))))))))) (.run (.step 21 (.step 42 (.step 35 (.close 53)))))) (.run (.step 34 (.step 42 (.step 5 (.step 52 (.close 3))))))) (.run (.step 11 (.step 3 (.step 9 (.step 27 (.close 30))))))) (.run (.step 31 (.close 3)))) (.run (.step 5 (.step 27 (.step 31 (.close 42)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11578457230703702011204076731327295263383483128984126386009060033576462822902249213795606440986345643339556081282957063333495790947709004199719432246587285681856895631557843519217486127549545499387871848543468288843111727104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 7 0 (.split 8 0 (.split 10 0 (.split 13 0 (.split 16 0 (.step 58 (.step 7 (.split 14 0 (.step 18 (.step 10 (.step 21 (.step 5 (.close 7))))) (.step 3 (.close 5))))) (.step 5 (.close 7))) (.step 43 (.step 7 (.step 10 (.step 16 (.step 18 (.close 21))))))) (.step 7 (.close 58))) (.step 18 (.step 5 (.step 3 (.step 5 (.close 3)))))) (.split 8 0 (.split 10 0 (.step 43 (.step 7 (.step 10 (.close 3)))) (.step 7 (.close 10))) (.step 10 (.close 3)))) (.step 58 (.step 18 (.close 5)))) (.step 18 (.step 5 (.close 3)))) (.step 76 (.step 5 (.close 3)))) (.step 18 (.step 10 (.step 18 (.step 21 (.step 22 (.step 43 (.close 7)))))))) (.step 3 (.step 7 (.step 10 (.close 70))))) (.step 18 (.step 10 (.step 21 (.close 18))))) (.step 18 (.step 10 (.step 64 (.step 18 (.step 21 (.step 43 (.step 31 (.close 64))))))))) (.step 5 (.step 10 (.step 31 (.step 18 (.step 21 (.step 5 (.close 22)))))))) (.step 26 (.step 31 (.close 58)))) (.step 5 (.step 42 (.close 58)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11578457230703702011204076731327295263383478979468557508793749456170633625688020939544079785372302305209790474913610487294052467436436940202052475519771299632776853263034797333293971020307615551211656352219250999506529943552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 10)))) (.step 7 (.step 10 (.close 72)))) (.step 7 (.step 10 (.step 21 (.step 22 (.close 31)))))) (.step 18 (.step 68 (.step 10 (.close 64))))) (.step 4 (.step 5 (.close 31)))) (.step 22 (.split 2 0 (.split 7 0 (.step 7 (.step 22 (.close 5))) (.step 10 (.close 59))) (.step 7 (.close 5))))) (.step 7 (.step 22 (.step 31 (.close 16))))) (.step 7 (.step 22 (.step 31 (.close 39))))) (.step 31 (.split 49 1 (.split 50 1 (.step 39 (.split 55 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 7 0 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 10)))) (.step 31 (.close 45))) (.step 7 (.close 39))) (.step 7 (.step 10 (.close 39)))) (.step 7 (.step 10 (.step 31 (.close 64))))) (.step 5 (.close 39)))) (.step 7 (.step 31 (.close 39)))) (.step 7 (.step 31 (.close 39)))))) (.step 31 (.close 3))) (.step 31 (.step 38 (.split 42 1 (.split 49 1 (.split 59 1 (.split 61 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 7 0 (.split 8 0 (.step 41 (.step 7 (.step 31 (.close 7)))) (.step 7 (.close 5))) (.step 10 (.close 41))) (.step 3 (.step 5 (.close 10)))) (.step 10 (.step 21 (.close 41)))) (.step 7 (.close 41))) (.step 7 (.close 41))) (.step 5 (.step 7 (.close 41)))) (.step 7 (.step 21 (.step 22 (.close 31))))) (.step 39 (.close 5)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808791854786315488899180176469510487134446396695014726520367086120101812095018455481244836957572988802170880⟩
def references : Fin 3 → Box := ![Part14.root, Part15.root, Part16.root]
def proof : Chunks.Proof 3 := (.split 36 1 (.split 38 1 (.reuse 0) (.step 43 (.split 2 1 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.reuse 1) (.run (.step 43 (.split 59 1 (.split 60 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 74 1 (.split 73 1 (.split 8 0 (.step 28 (.split 14 0 (.step 41 (.close 7)) (.step 18 (.step 5 (.close 3))))) (.step 10 (.close 5))) (.step 21 (.close 41))) (.step 5 (.close 41))) (.step 10 (.step 21 (.close 59)))) (.step 3 (.step 7 (.close 59)))) (.step 18 (.step 21 (.close 7)))) (.step 21 (.step 22 (.step 41 (.close 3))))) (.step 10 (.step 21 (.step 22 (.step 31 (.close 5)))))) (.step 10 (.close 58)))))) (.run (.step 5 (.step 41 (.close 58))))) (.run (.step 3 (.step 7 (.step 10 (.step 3 (.step 21 (.step 22 (.close 54))))))))) (.run (.step 5 (.step 31 (.step 21 (.step 7 (.step 5 (.close 21)))))))) (.run (.step 48 (.step 5 (.step 16 (.step 58 (.close 9))))))) (.run (.step 3 (.step 7 (.step 9 (.close 10)))))) (.run (.step 31 (.step 38 (.step 60 (.step 76 (.split 49 1 (.split 61 1 (.split 69 1 (.split 7 0 (.split 8 0 (.step 41 (.step 7 (.step 31 (.close 7)))) (.step 7 (.close 5))) (.step 10 (.close 41))) (.step 7 (.close 41))) (.step 7 (.close 41))) (.step 16 (.close 58))))))))) (.run (.step 42 (.step 43 (.close 42))))) (.run (.step 5 (.step 10 (.step 21 (.close 41)))))))) (.step 31 (.split 2 1 (.reuse 2) (.run (.step 3 (.step 4 (.step 5 (.close 31))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11578457230703702011204076731327295263383478979468557508793749456170633625688020939544079785372302305209790472450982751479054487577946848673037265645828663824259173693630401811864817193670629600556712668294516173660855730176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 10)))) (.step 7 (.step 10 (.step 16 (.close 31))))) (.step 7 (.step 10 (.step 16 (.step 21 (.close 31)))))) (.step 4 (.step 16 (.step 7 (.step 10 (.close 64)))))) (.step 4 (.step 5 (.close 31)))) (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 7 0 (.step 7 (.step 31 (.close 7))) (.step 10 (.close 59))) (.step 10 (.step 16 (.close 59)))) (.step 7 (.close 22))) (.step 7 (.close 59))) (.step 7 (.close 59)))) (.step 5 (.step 7 (.step 16 (.close 31))))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 16)))) (.step 31 (.step 37 (.split 49 1 (.split 50 1 (.split 55 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 7 0 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 10)))) (.step 31 (.close 45))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 7 (.step 10 (.close 37)))) (.step 5 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 16 (.close 31))))))) (.step 31 (.close 3))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847170206749890122221370379775139026523030084996571517598402966592684032⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.reuse 0) (.step 31 (.split 2 1 (.split 36 1 (.split 38 1 (.reuse 1) (.run (.step 16 (.step 31 (.step 37 (.step 38 (.split 59 1 (.split 61 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 7 0 (.split 8 0 (.step 41 (.step 7 (.step 31 (.close 7)))) (.step 7 (.close 5))) (.step 10 (.close 41))) (.step 3 (.step 5 (.close 10)))) (.step 16 (.close 41))) (.step 7 (.close 41))) (.step 7 (.close 41))) (.step 7 (.step 16 (.step 21 (.close 31))))))))))) (.run (.step 31 (.step 37 (.split 49 1 (.split 50 1 (.split 55 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 7 0 (.step 7 (.step 31 (.close 7))) (.step 31 (.step 7 (.close 10)))) (.step 16 (.step 31 (.step 7 (.close 10))))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 7 (.step 10 (.close 37)))) (.step 5 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 16 (.close 31)))))))) (.run (.step 3 (.step 4 (.step 5 (.close 31)))))))) (.run (.step 3 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.step 7 (.step 18 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.close 31))) (.step 7 (.close 31))) (.step 7 (.close 31))) (.step 3 (.close 31))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨3213876088517980551083924184682325205044405987565587818086400, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757180616536739123927342288349920620129377965828403625984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 5 (.step 18 (.step 23 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 7 0 (.split 13 0 (.split 30 0 (.split 38 0 (.split 39 0 (.split 56 0 (.step 23 (.close 4)) (.step 18 (.close 5))) (.step 11 (.step 21 (.close 23)))) (.step 18 (.close 5))) (.step 7 (.close 5))) (.step 23 (.close 4))) (.step 23 (.close 10))) (.step 5 (.close 18))) (.step 5 (.step 10 (.close 18)))) (.step 3 (.step 7 (.close 70)))) (.step 5 (.step 10 (.step 18 (.close 22))))) (.step 5 (.step 18 (.close 64)))) (.step 5 (.step 26 (.step 31 (.step 4 (.close 23)))))) (.step 23 (.close 3))) (.step 5 (.step 10 (.close 18)))) (.step 5 (.close 23))) (.step 3 (.step 7 (.step 22 (.close 54))))) (.step 5 (.step 21 (.step 53 (.step 31 (.step 4 (.step 9 (.step 23 (.close 4))))))))) (.step 5 (.step 55 (.step 34 (.step 9 (.step 52 (.step 3 (.close 4)))))))) (.step 3 (.step 7 (.step 9 (.close 10))))) (.step 7 (.step 23 (.close 10)))) (.step 18 (.step 5 (.close 23)))) (.step 21 (.step 23 (.step 5 (.close 42))))) (.step 5 (.step 18 (.close 41)))) (.step 7 (.step 22 (.step 23 (.close 10))))) (.step 7 (.step 31 (.close 37))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182113114415750771930528923189321603190093503327633408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 2 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.step 63 (.split 59 1 (.step 18 (.split 61 1 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.step 7 (.close 11)))) (.step 7 (.close 72))) (.step 7 (.step 8 (.step 18 (.close 14))))) (.step 7 (.step 8 (.step 14 (.step 18 (.close 19))))))) (.step 7 (.step 11 (.step 18 (.close 17)))))) (.step 18 (.step 7 (.close 61)))) (.step 7 (.step 11 (.step 18 (.step 23 (.close 53)))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 23 (.close 52))))))) (.step 7 (.step 18 (.close 11)))) (.step 18 (.step 23 (.step 11 (.step 42 (.step 18 (.step 7 (.close 17)))))))) (.step 5 (.step 18 (.close 7)))) (.step 18 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.step 20 (.split 62 1 (.split 8 0 (.step 7 (.step 18 (.close 7))) (.step 8 (.close 20))) (.step 7 (.step 8 (.step 18 (.close 14)))))) (.step 18 (.close 20))) (.step 18 (.close 20))) (.step 7 (.close 20))) (.step 18 (.close 20))) (.step 18 (.close 20))) (.step 7 (.step 11 (.step 17 (.step 18 (.close 62)))))) (.step 18 (.step 19 (.close 20)))))) (.step 4 (.step 5 (.close 18)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11578457230703702011199177848016637920946535278582724750178500226615382312459157657644924457595074765903874223970566569746915425722473298253107587561110854330115918430400002907745012382747849347717332943832786790867463569408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.step 63 (.split 59 1 (.step 18 (.split 61 1 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.step 7 (.close 11)))) (.step 7 (.step 8 (.close 18)))) (.step 7 (.step 8 (.close 65)))) (.step 7 (.step 18 (.close 19))))) (.step 7 (.step 11 (.step 18 (.close 17)))))) (.step 18 (.step 7 (.step 11 (.close 61))))) (.step 7 (.step 11 (.step 23 (.close 19))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 23 (.close 19))))))) (.step 7 (.step 18 (.close 11)))) (.step 18 (.step 23 (.step 11 (.step 42 (.close 3)))))) (.step 5 (.step 18 (.close 7)))) (.step 18 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.step 19 (.split 62 1 (.split 8 0 (.step 7 (.step 18 (.close 7))) (.step 8 (.close 19))) (.step 7 (.step 8 (.close 65))))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 11 (.step 18 (.close 19)))) (.step 18 (.close 19))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575917388102833447126874154319473113159260176384⟩
def references : Fin 4 → Box := ![Part19.root, Part20.root, Part21.root, Part22.root]
def proof : Chunks.Proof 4 := (.split 16 1 (.split 17 1 (.split 20 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 2 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.step 63 (.split 59 1 (.step 18 (.split 61 1 (.split 62 1 (.split 69 1 (.split 39 0 (.step 7 (.step 18 (.close 7))) (.step 18 (.step 7 (.close 11)))) (.step 7 (.step 8 (.close 18)))) (.step 7 (.step 8 (.step 18 (.close 14))))) (.step 7 (.step 8 (.step 14 (.step 18 (.close 19))))))) (.step 7 (.close 62)))) (.step 18 (.step 7 (.step 11 (.close 61))))) (.step 7 (.step 11 (.step 18 (.step 23 (.close 53)))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 62))))))) (.step 7 (.step 18 (.close 11)))) (.step 18 (.step 23 (.step 11 (.step 42 (.step 18 (.step 7 (.close 17)))))))) (.step 5 (.step 18 (.close 7)))) (.step 3 (.step 5 (.close 18)))))))) (.reuse 1)) (.reuse 2)) (.step 7 (.step 18 (.split 2 1 (.split 17 1 (.reuse 3) (.run (.step 18 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 60 1 (.split 61 1 (.step 19 (.split 62 1 (.split 8 0 (.step 7 (.step 18 (.close 7))) (.step 8 (.close 19))) (.step 7 (.step 8 (.close 65))))) (.step 8 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 11 (.step 18 (.close 19)))) (.step 18 (.close 19)))))) (.run (.step 3 (.step 4 (.step 5 (.close 18)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part21.excludes
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2787593149816327892691964784081047335731200, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809199593181869476517136288093189854454072445229409164763959331136874517934648052031274261576893155164657136761872368002554372554752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.step 63 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 7 0 (.split 8 0 (.split 13 0 (.split 16 0 (.split 20 0 (.step 7 (.step 63 (.step 7 (.close 5)))) (.step 5 (.close 17))) (.step 7 (.close 18))) (.step 23 (.close 3))) (.split 10 0 (.step 23 (.step 11 (.close 7))) (.step 7 (.close 11)))) (.step 23 (.step 63 (.step 3 (.step 23 (.close 3)))))) (.step 23 (.step 3 (.step 11 (.step 5 (.close 3)))))) (.step 11 (.split 2 0 (.split 34 0 (.step 77 (.close 7)) (.step 7 (.step 5 (.close 17)))) (.step 17 (.close 3))))) (.step 23 (.close 16))) (.step 16 (.step 63 (.close 3)))) (.step 3 (.step 7 (.close 70)))) (.step 5 (.step 16 (.step 63 (.close 3))))) (.step 34 (.step 16 (.close 63)))) (.step 44 (.step 55 (.step 27 (.step 34 (.step 23 (.step 31 (.step 44 (.close 63)))))))))) (.step 23 (.step 34 (.step 61 (.close 17))))) (.step 5 (.step 18 (.step 5 (.close 17))))) (.step 5 (.step 18 (.step 34 (.step 11 (.step 5 (.close 44))))))) (.step 7 (.step 18 (.step 3 (.step 36 (.step 34 (.step 11 (.close 54)))))))) (.step 55 (.step 27 (.step 61 (.step 62 (.step 63 (.split 2 0 (.step 55 (.step 34 (.step 53 (.step 11 (.step 17 (.close 3)))))) (.step 11 (.step 3 (.close 17)))))))))) (.step 31 (.step 34 (.step 27 (.step 31 (.step 34 (.close 3))))))) (.step 7 (.step 27 (.close 30)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2787593149816327892691964784081047335731200, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891746556819137854124141602606413095924533145382588351233086455808⟩
def references : Fin 1 → Box := ![Part24.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 2 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 5 (.close 31))))) (.run (.step 5 (.step 17 (.close 21))))) (.run (.step 5 (.step 7 (.step 17 (.close 23)))))) (.run (.step 23 (.step 31 (.step 34 (.step 42 (.step 5 (.close 17)))))))) (.run (.step 5 (.step 16 (.step 42 (.step 49 (.step 58 (.close 5)))))))) (.run (.step 23 (.step 7 (.step 31 (.close 5)))))) (.run (.step 31 (.step 5 (.close 7))))) (.run (.step 31 (.close 7)))) (.run (.step 14 (.step 18 (.split 38 1 (.split 40 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 62 1 (.split 69 1 (.step 11 (.step 17 (.step 7 (.step 17 (.close 5))))) (.step 5 (.step 7 (.close 17)))) (.step 5 (.step 7 (.close 17)))) (.step 7 (.close 17))) (.step 5 (.close 17))) (.step 7 (.close 17))) (.step 5 (.step 7 (.close 17)))) (.step 5 (.close 17))))))) (.run (.step 14 (.step 18 (.step 61 (.step 74 (.split 22 1 (.split 38 1 (.split 40 1 (.split 50 1 (.split 59 1 (.split 62 1 (.step 11 (.step 17 (.step 7 (.step 17 (.close 5))))) (.step 5 (.step 7 (.close 17)))) (.step 7 (.close 17))) (.step 7 (.close 17))) (.step 5 (.step 7 (.close 17)))) (.step 5 (.close 17))) (.step 17 (.close 20)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2722258935367507707706996859456293175296, 11578457230703702011204076731327295263383483128984126389786707968578497313572584673578646581748302471096841307143829263367893050808864863331243171123562856677986610851401253478879938873325178755017357785801086562447708389376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 51 1 (.split 2 0 (.split 10 0 (.split 16 0 (.step 76 (.split 60 1 (.split 67 1 (.split 74 1 (.split 17 0 (.split 20 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 49 0 (.step 10 (.step 16 (.close 3))) (.step 5 (.close 16))) (.step 7 (.step 10 (.close 16)))) (.step 10 (.close 16))) (.step 7 (.step 5 (.close 7)))) (.step 16 (.close 3))) (.step 18 (.step 5 (.close 7)))) (.step 23 (.close 76))) (.step 3 (.step 16 (.close 7)))) (.step 16 (.close 63)))) (.step 18 (.step 16 (.step 21 (.step 5 (.close 7)))))) (.step 5 (.step 16 (.step 18 (.step 15 (.close 16)))))) (.step 3 (.step 5 (.step 16 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 34 0 (.step 5 (.close 3)) (.step 10 (.close 16))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))))) (.step 3 (.step 22 (.step 54 (.close 16))))) (.step 76 (.step 16 (.close 72)))) (.step 76 (.step 16 (.close 65)))) (.step 34 (.step 16 (.step 15 (.close 64))))) (.step 5 (.step 15 (.step 26 (.step 63 (.step 76 (.split 51 1 (.split 62 1 (.step 52 (.step 5 (.step 9 (.close 16)))) (.step 3 (.step 4 (.step 9 (.close 16))))) (.step 4 (.step 9 (.step 16 (.close 7))))))))))) (.step 5 (.step 22 (.step 34 (.step 5 (.close 3)))))) (.step 16 (.step 58 (.step 76 (.step 16 (.close 5)))))) (.step 5 (.step 16 (.step 7 (.step 15 (.step 22 (.close 26))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575918783260537822974574354155363583408927145984⟩
def references : Fin 3 → Box := ![Part23.root, Part25.root, Part26.root]
def proof : Chunks.Proof 3 := (.split 13 1 (.split 14 1 (.reuse 0) (.step 23 (.split 16 1 (.reuse 1) (.run (.step 14 (.step 18 (.step 42 (.step 67 (.split 17 1 (.split 22 1 (.split 40 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 69 1 (.step 11 (.step 17 (.step 7 (.step 17 (.close 5))))) (.step 5 (.step 7 (.close 17)))) (.step 7 (.close 17))) (.step 5 (.close 17))) (.step 7 (.close 17))) (.step 5 (.step 7 (.close 17)))) (.step 17 (.close 19))) (.step 17 (.close 19))))))))))) (.split 14 1 (.split 16 1 (.split 17 1 (.split 20 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 2 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 2) (.run (.step 5 (.step 15 (.step 21 (.step 58 (.step 62 (.step 63 (.step 65 (.step 52 (.step 5 (.step 16 (.step 7 (.close 22)))))))))))))) (.run (.step 15 (.step 16 (.step 34 (.step 5 (.close 52))))))) (.run (.step 3 (.step 9 (.step 10 (.close 7)))))) (.run (.step 16 (.step 31 (.step 7 (.close 16)))))) (.run (.step 5 (.close 16)))) (.run (.step 5 (.step 16 (.step 43 (.close 3)))))) (.run (.step 5 (.step 23 (.step 21 (.step 43 (.step 34 (.step 16 (.step 5 (.close 3)))))))))) (.run (.step 43 (.step 76 (.step 16 (.step 5 (.close 41))))))) (.run (.step 16 (.step 31 (.step 22 (.step 7 (.close 16))))))) (.run (.step 16 (.step 31 (.step 16 (.close 3)))))) (.run (.step 3 (.step 16 (.close 18))))) (.run (.step 18 (.close 26)))) (.run (.step 5 (.step 16 (.close 7))))) (.run (.step 18 (.close 22)))) (.run (.step 18 (.close 21)))) (.run (.step 16 (.step 23 (.close 16))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes
  · exact Part25.excludes
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨2417851639229260496896000, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702412981881072974617061714821003440603817355976054359757369948087475310756977174211317197888028424685394269997398753280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 40 1 (.split 2 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 58 1 (.step 63 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 7 0 (.split 10 0 (.split 13 0 (.split 20 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 63 (.step 7 (.close 11))) (.step 7 (.close 5))) (.step 7 (.close 8))) (.step 7 (.step 8 (.close 7)))) (.step 23 (.close 3))) (.step 23 (.close 3))) (.step 7 (.close 63))) (.step 23 (.step 63 (.step 3 (.step 23 (.close 3)))))) (.step 23 (.step 3 (.step 8 (.close 5))))) (.step 11 (.close 3))) (.step 23 (.close 10))) (.step 10 (.step 63 (.close 3)))) (.step 3 (.step 7 (.close 70)))) (.step 5 (.step 10 (.step 63 (.close 3))))) (.step 63 (.close 10))) (.step 11 (.step 9 (.step 44 (.step 18 (.step 62 (.close 11)))))))) (.step 11 (.step 23 (.step 61 (.step 5 (.close 11)))))) (.step 5 (.step 18 (.step 5 (.close 11))))) (.step 11 (.step 18 (.step 5 (.step 11 (.close 5)))))) (.step 7 (.step 18 (.step 3 (.step 36 (.step 11 (.step 54 (.close 11)))))))) (.step 11 (.step 31 (.step 9 (.step 55 (.step 53 (.close 11))))))) (.step 11 (.step 31 (.step 9 (.step 55 (.step 52 (.close 11))))))) (.step 7 (.step 27 (.close 30)))) (.step 7 (.step 10 (.step 5 (.close 11))))) (.step 5 (.step 9 (.close 11)))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 23 (.step 31 (.step 61 (.step 42 (.step 5 (.close 11))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575918783260537824242226163309412599534805057536⟩
def references : Fin 2 → Box := ![Part27.root, Part28.root]
def proof : Chunks.Proof 2 := (.split 8 1 (.split 10 1 (.reuse 0) (.run (.step 3 (.step 7 (.split 13 1 (.split 14 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.step 7 (.step 18 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.close 31))) (.step 7 (.close 31))) (.step 7 (.close 31))) (.step 3 (.close 31))) (.step 3 (.step 17 (.step 7 (.close 17))))) (.step 15 (.step 3 (.close 16)))))))) (.step 23 (.split 13 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 1) (.run (.step 5 (.step 42 (.step 58 (.step 5 (.close 10))))))) (.run (.step 23 (.step 7 (.step 31 (.close 5)))))) (.run (.step 31 (.step 5 (.close 7))))) (.run (.step 11 (.step 3 (.step 7 (.close 11)))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 11 (.step 63 (.split 34 1 (.split 36 1 (.split 38 1 (.split 40 1 (.split 56 1 (.step 11 (.close 4)) (.step 5 (.close 3))) (.step 5 (.close 11))) (.step 5 (.close 3))) (.step 5 (.close 11))) (.step 5 (.close 11))))))) (.run (.step 10 (.step 23 (.close 10)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part27.excludes
  · exact Part28.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part29

namespace Part30
def root : Box := ⟨2361183241436970090496, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869699891253484503727947475856254594249320292252662744571170621257309603584563601352732186683580063982110925250397552508928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 51 1 (.split 2 0 (.split 10 0 (.split 16 0 (.step 76 (.split 60 1 (.split 67 1 (.split 74 1 (.split 17 0 (.split 20 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 40 0 (.step 10 (.close 3)) (.step 5 (.close 3))) (.step 10 (.close 3))) (.step 10 (.close 5))) (.step 7 (.step 5 (.close 7)))) (.step 10 (.close 5))) (.step 18 (.step 5 (.close 7)))) (.step 23 (.close 10))) (.step 3 (.step 10 (.close 4)))) (.step 10 (.close 3)))) (.step 18 (.step 5 (.step 10 (.step 18 (.step 5 (.close 7))))))) (.step 18 (.step 10 (.step 16 (.step 7 (.step 10 (.close 3))))))) (.step 3 (.step 5 (.step 10 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 34 0 (.step 5 (.close 3)) (.step 9 (.close 10))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))))) (.step 3 (.step 10 (.step 22 (.step 54 (.step 7 (.close 9))))))) (.step 76 (.step 10 (.close 3)))) (.step 76 (.step 10 (.close 3)))) (.step 76 (.step 10 (.close 3)))) (.step 9 (.close 10))) (.step 5 (.step 9 (.step 5 (.close 10))))) (.step 10 (.step 58 (.step 76 (.step 10 (.close 3)))))) (.step 5 (.close 10))) (.step 9 (.close 10))) (.step 9 (.close 10))) (.step 3 (.step 9 (.step 10 (.close 7))))) (.step 10 (.step 31 (.step 7 (.close 10))))) (.step 5 (.step 10 (.step 43 (.close 3))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part30

namespace Part31
def root : Box := ⟨2147483648, 11578457230703702011204076731327295263383483128984126389786707968578497316849171951990312027809202300869702415444508808794094531057668740426710246277141847171891748163757182114575918783260537824242226164490004220252216360960⟩
def references : Fin 2 → Box := ![Part29.root, Part30.root]
def proof : Chunks.Proof 2 := (.split 7 1 (.reuse 0) (.split 8 1 (.split 10 1 (.split 13 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 20 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.reuse 1) (.run (.step 5 (.step 23 (.step 9 (.step 5 (.close 10))))))) (.run (.step 10 (.step 58 (.step 76 (.step 10 (.close 3))))))) (.run (.step 10 (.step 31 (.step 7 (.close 10)))))) (.run (.step 9 (.step 10 (.step 31 (.step 16 (.step 7 (.close 10)))))))) (.run (.step 3 (.step 10 (.close 18))))) (.run (.step 4 (.step 8 (.close 26))))) (.run (.step 5 (.close 10)))) (.run (.step 4 (.step 8 (.close 22))))) (.run (.step 4 (.step 8 (.close 21))))) (.run (.step 16 (.step 23 (.close 16))))) (.run (.step 16 (.step 21 (.step 22 (.step 26 (.step 76 (.split 50 1 (.split 59 1 (.split 39 1 (.step 16 (.step 22 (.step 10 (.close 3)))) (.step 5 (.close 3))) (.step 5 (.close 9))) (.step 5 (.close 9)))))))))) (.run (.step 8 (.step 16 (.step 3 (.step 10 (.close 18))))))) (.run (.step 10 (.step 23 (.close 10))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part29.excludes
  · exact Part30.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part31

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part31.excludes
end FiveColour.Packed.ProjectedChunks.Case1
