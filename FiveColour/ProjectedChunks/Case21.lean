module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case21
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438752422821662792338292685257105107186207177486955970560⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11592891989185001204471, 5789234131009374248507341982684158351525473076195097263463908735304727765271163198607014520417109729396981796214162666810521916439567451338240667233911583614265164498419429981634596862352413225127988347882672294734774404096, 0⟩]
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
def root : Box := ⟨2147483648, 5783586108473071698929507001637161558579861677237086861867373389705307203385890430320350290099762791203058827501574509611081663848235674504478897771119470946671357392930101402806377331141284751746080791468621897896321613824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 21 0 (.split 65 1 (.split 22 0 (.split 34 0 (.step 55 (.step 40 (.split 35 0 (.step 55 (.close 7)) (.step 29 (.step 40 (.close 3)))))) (.step 29 (.step 40 (.step 7 (.close 15))))) (.split 26 0 (.split 30 0 (.step 40 (.close 3)) (.step 7 (.close 3))) (.step 75 (.step 27 (.close 3))))) (.step 3 (.close 31))) (.step 18 (.step 23 (.step 40 (.close 3))))) (.step 18 (.split 22 0 (.split 26 0 (.split 30 0 (.step 40 (.close 3)) (.step 7 (.close 3))) (.step 40 (.split 30 0 (.step 27 (.close 3)) (.step 3 (.close 7))))) (.step 7 (.close 18))))) (.step 23 (.split 65 1 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 40 (.close 3)) (.step 7 (.close 3))) (.step 38 (.step 27 (.close 3)))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 3 (.close 18))))))
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
def root : Box := ⟨2147483648, 5783586108473071698929507001637161558579861677237086861867373389705307203385890430320350290099762791203058827501574509611081663848235674504478897771119470946671357392930101402806378724939188887905812053323917745479196082176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 14 0 (.reuse 0) (.run (.split 65 1 (.split 16 0 (.step 23 (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 27 (.step 40 (.close 3))) (.step 40 (.close 3))) (.step 40 (.step 3 (.close 7)))) (.split 39 0 (.step 29 (.close 3)) (.step 23 (.close 27)))) (.step 11 (.step 23 (.step 31 (.split 26 0 (.split 30 0 (.step 17 (.step 3 (.close 15))) (.step 3 (.close 7))) (.step 3 (.close 23))))))) (.step 11 (.step 23 (.split 26 0 (.split 22 0 (.step 74 (.step 3 (.close 7))) (.step 7 (.close 18))) (.step 3 (.close 27))))))) (.step 11 (.split 26 0 (.split 17 0 (.step 23 (.step 67 (.split 42 0 (.step 17 (.step 7 (.close 15))) (.step 3 (.close 7))))) (.split 39 0 (.step 7 (.close 18)) (.step 18 (.close 7)))) (.step 3 (.step 18 (.close 21)))))) (.step 3 (.close 18))))) (.run (.split 65 1 (.split 14 0 (.split 21 0 (.split 26 0 (.split 16 0 (.step 9 (.split 34 0 (.step 40 (.split 35 0 (.split 22 0 (.step 55 (.close 7)) (.step 18 (.close 23))) (.step 40 (.split 30 0 (.step 15 (.close 55)) (.step 18 (.close 15)))))) (.step 15 (.step 18 (.close 34))))) (.step 3 (.step 23 (.close 7)))) (.step 29 (.step 23 (.step 3 (.close 15))))) (.step 18 (.step 9 (.step 15 (.step 40 (.close 3)))))) (.split 16 0 (.step 15 (.step 23 (.close 3))) (.step 3 (.close 17)))) (.step 3 (.close 31)))))
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
def root : Box := ⟨2147483648, 5783586108473071698929507001637161558579861677237086861867373389705307203385890430320350290099762791203058827501574509611081663848235674504478897771119470946671357392930101402806378724939188889173463862477966761605073993728⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 18 (.split 22 0 (.split 30 0 (.step 31 (.split 26 0 (.step 52 (.step 3 (.step 18 (.close 44)))) (.step 29 (.close 3)))) (.step 7 (.close 3))) (.step 7 (.close 3)))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.split 16 0 (.step 3 (.split 17 0 (.step 15 (.split 22 0 (.split 26 0 (.split 30 0 (.step 66 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 15))) (.step 3 (.close 7)))) (.step 3 (.close 7)))) (.step 7 (.close 17)))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.step 15 (.step 18 (.close 15)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 15)))))) (.run (.split 65 1 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.step 9 (.step 23 (.split 26 0 (.split 34 0 (.split 35 0 (.step 11 (.close 55)) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))))) (.step 11 (.step 3 (.step 9 (.step 11 (.close 7)))))) (.step 11 (.step 9 (.close 11)))) (.split 14 0 (.step 9 (.close 11)) (.step 11 (.close 9)))) (.split 16 0 (.split 14 0 (.step 3 (.split 17 0 (.step 9 (.split 22 0 (.split 26 0 (.split 30 0 (.step 66 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 9))) (.step 3 (.close 7)))) (.step 3 (.close 7)))) (.step 11 (.close 9))) (.step 7 (.close 11)))) (.step 3 (.close 11)))))
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
def root : Box := ⟨10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579557027741696, 11567172216946143397854115110615220493706481850345774675622263473507740028906894108343610970802390301956296063883384246047735487414750708958138613235295119848855767901289469234154579471374525989336842982640016901670231343104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 55 (.close 31)) (.step 29 (.step 40 (.close 55)))) (.step 29 (.step 31 (.step 3 (.close 74))))) (.step 3 (.close 74))) (.step 31 (.close 55))) (.step 3 (.close 74))) (.step 67 (.step 3 (.close 74)))) (.step 74 (.close 55))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 29 (.step 57 (.step 23 (.step 15 (.close 3))))) (.step 22 (.close 31))) (.step 18 (.close 74))) (.step 23 (.close 74)))) (.split 21 0 (.split 26 0 (.split 30 0 (.split 14 0 (.split 16 0 (.split 22 0 (.step 9 (.close 74)) (.step 3 (.close 11))) (.step 11 (.close 3))) (.step 11 (.close 9))) (.step 3 (.step 11 (.close 9)))) (.step 47 (.close 74))) (.step 11 (.close 3)))) (.step 3 (.step 66 (.step 31 (.step 3 (.step 17 (.close 74))))))) (.step 11 (.step 69 (.step 74 (.close 18))))) (.step 29 (.step 69 (.step 74 (.close 31))))) (.step 3 (.close 74))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993925877836143429700747176315226785705290361894868127523894227291168706852201910475692193128257419240004475832879280591059798846923440810622667762011590391847507811866257468236926362296666478870528⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.reuse 0) (.run (.step 11 (.split 65 1 (.split 26 0 (.split 34 0 (.split 35 0 (.split 10 0 (.step 77 (.close 55)) (.step 17 (.step 31 (.step 77 (.close 3))))) (.step 23 (.close 77))) (.step 23 (.close 77))) (.step 23 (.close 77))) (.step 3 (.close 18)))))) (.run (.split 65 1 (.split 74 1 (.step 29 (.split 8 0 (.split 14 0 (.split 16 0 (.split 10 0 (.step 75 (.close 55)) (.step 18 (.step 75 (.step 40 (.step 15 (.close 55)))))) (.step 18 (.step 38 (.step 40 (.close 3))))) (.step 40 (.close 75))) (.step 9 (.step 11 (.close 3))))) (.step 23 (.close 77))) (.step 3 (.close 75))))) (.reuse 1)) (.run (.step 3 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 12 0 (.split 35 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 29)))) (.step 3 (.close 55))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630615804215296, 11567172216946143397859013993930444732269467542640835691101632188306002089418840193746613689929299388380024630302709300749216413524762071519234628430397924972600390528867184841524684102920857075770377681822685486165553840128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.split 8 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 55 (.close 31)) (.step 29 (.step 40 (.close 55)))) (.step 15 (.close 66))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 67 (.step 3 (.close 66)))) (.step 66 (.close 3))) (.split 21 0 (.split 26 0 (.split 16 0 (.split 17 0 (.step 9 (.step 66 (.close 3))) (.step 3 (.close 11))) (.step 11 (.close 3))) (.step 40 (.close 47))) (.step 11 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.step 66 (.close 3))) (.step 11 (.step 3 (.close 66)))) (.step 11 (.step 18 (.step 3 (.close 66))))) (.step 11 (.step 66 (.close 18))))) (.step 3 (.close 66))) (.step 11 (.step 66 (.close 55)))) (.step 29 (.step 66 (.close 55)))) (.step 66 (.close 3))) (.step 3 (.close 55))) (.step 3 (.close 66))) (.step 66 (.close 3))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467542640835691101632188306002089418840193746613689929299388380024630302709300749216413524762071519234628430397924972600390528867184841524684102920857075770377681822685486165553840128⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 63 1 (.split 64 1 (.reuse 0) (.run (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.split 8 0 (.split 12 0 (.step 67 (.step 3 (.step 29 (.step 18 (.close 23))))) (.split 16 0 (.split 17 0 (.step 29 (.step 66 (.step 21 (.step 3 (.close 23))))) (.step 18 (.close 67))) (.step 18 (.close 67)))) (.split 21 0 (.split 26 0 (.split 17 0 (.split 22 0 (.step 9 (.close 67)) (.step 3 (.close 11))) (.step 11 (.close 3))) (.step 40 (.close 47))) (.step 11 (.close 3)))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 8 0 (.split 22 0 (.step 67 (.close 3)) (.step 3 (.close 67))) (.step 11 (.close 67))) (.step 11 (.step 3 (.close 23)))) (.step 11 (.step 18 (.step 3 (.close 67))))) (.step 11 (.close 67)))) (.step 3 (.step 66 (.step 31 (.step 3 (.step 17 (.close 67))))))) (.step 11 (.step 67 (.close 55)))) (.step 29 (.step 67 (.close 55)))) (.step 67 (.close 3))) (.step 3 (.close 55))) (.step 3 (.close 67))))) (.reuse 1))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416710905856000, 11567172216946143397859013993930444732269467546697054275260546546898243434141054110322767815189173562970658750226223792496339035117951048923620566259799736359265075694229571404155403946388614019441425635655036549404219670528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 12 0 (.step 40 (.close 55)) (.step 9 (.step 34 (.close 40)))) (.step 3 (.step 27 (.step 31 (.close 23))))) (.step 3 (.step 27 (.step 31 (.close 23))))) (.step 3 (.close 23))) (.step 18 (.step 3 (.step 27 (.step 31 (.close 55)))))) (.step 18 (.step 31 (.close 61)))) (.step 27 (.split 16 0 (.step 34 (.step 23 (.close 61))) (.step 42 (.step 17 (.step 23 (.close 61))))))) (.step 3 (.step 27 (.step 31 (.step 17 (.close 61)))))) (.step 27 (.split 10 0 (.split 14 0 (.split 16 0 (.split 22 0 (.step 9 (.step 11 (.close 9))) (.step 11 (.close 3))) (.step 11 (.close 3))) (.step 11 (.close 3))) (.step 11 (.close 61))))) (.step 27 (.step 44 (.step 61 (.close 40))))) (.step 40 (.close 11))) (.step 11 (.step 40 (.split 10 0 (.step 51 (.close 74)) (.step 17 (.step 18 (.close 61))))))) (.step 3 (.step 31 (.close 61)))) (.step 3 (.close 61))) (.step 11 (.step 40 (.step 55 (.step 74 (.step 77 (.split 65 1 (.split 10 0 (.step 51 (.step 67 (.close 40))) (.step 17 (.step 18 (.close 67)))) (.step 3 (.close 18))))))))) (.step 11 (.step 40 (.step 55 (.step 77 (.split 10 0 (.step 51 (.step 66 (.step 27 (.step 34 (.step 3 (.close 61)))))) (.step 18 (.close 66)))))))) (.step 27 (.step 44 (.step 40 (.step 44 (.step 55 (.step 61 (.close 40)))))))))
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
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384264315699200, 11567172216946143397859013993930444732269467546697054275260550146029279068698160358753573963974660658728353391759530273100797124588015586113916821492348619471950795630958078220871502513001458414881176842467181241535303778304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 23 (.split 10 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 55 (.step 40 (.split 35 0 (.split 36 0 (.step 23 (.close 57)) (.step 18 (.close 23))) (.step 9 (.step 21 (.close 57)))))) (.step 9 (.step 31 (.step 18 (.close 57))))) (.step 9 (.step 18 (.step 31 (.close 23))))) (.step 29 (.close 27))) (.step 23 (.close 57))) (.step 9 (.split 58 0 (.step 15 (.close 57)) (.step 22 (.close 57))))) (.step 3 (.step 9 (.step 18 (.step 15 (.step 29 (.close 57)))))))) (.step 29 (.step 57 (.close 23)))) (.step 29 (.step 57 (.split 10 0 (.step 51 (.close 74)) (.step 3 (.close 74)))))) (.step 3 (.step 18 (.close 57)))) (.step 3 (.close 57))) (.step 23 (.step 29 (.step 55 (.step 74 (.step 75 (.split 8 0 (.split 10 0 (.step 51 (.step 21 (.step 57 (.close 67)))) (.step 3 (.step 15 (.step 21 (.close 55))))) (.step 9 (.close 11))))))))) (.step 23 (.step 29 (.step 55 (.step 74 (.step 75 (.split 64 1 (.split 65 1 (.split 8 0 (.split 10 0 (.step 51 (.step 15 (.step 57 (.step 23 (.close 3))))) (.step 23 (.close 66))) (.step 9 (.close 11))) (.step 3 (.close 31))) (.step 51 (.close 66))))))))) (.step 9 (.step 26 (.step 23 (.step 26 (.step 55 (.step 57 (.close 23)))))))) (.step 3 (.step 23 (.step 57 (.split 10 0 (.split 30 0 (.step 22 (.split 8 0 (.step 57 (.close 15)) (.step 9 (.close 11)))) (.step 3 (.step 23 (.close 38)))) (.step 3 (.step 15 (.close 40)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029279068698160358753573963974660658728353391759530273100797124588015586113916821492348619471950795630958078220871502513001458414881176842467181241535303778304⟩
def references : Fin 3 → Box := ![Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 3 := (.split 54 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 55 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 10 0 (.step 62 (.step 23 (.step 26 (.close 31)))) (.step 52 (.split 26 0 (.step 52 (.close 62)) (.step 18 (.close 23))))) (.step 3 (.step 9 (.step 18 (.close 40))))) (.step 9 (.split 10 0 (.step 26 (.split 21 0 (.split 30 0 (.step 26 (.step 40 (.step 15 (.close 55)))) (.step 3 (.step 18 (.close 55)))) (.step 3 (.step 15 (.close 62))))) (.step 15 (.close 62))))) (.step 18 (.step 27 (.step 55 (.close 7))))) (.step 53 (.step 23 (.step 55 (.close 7))))) (.step 55 (.close 62))) (.step 9 (.step 11 (.close 3)))) (.step 23 (.close 77))) (.step 40 (.close 75))) (.step 55 (.close 74))) (.step 3 (.step 62 (.close 7)))) (.step 55 (.close 67))) (.step 55 (.close 66)))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11567172216946143397859013993930444732269467546697054275260550146029282423923533452298990727494099907017484413817627467242206344961667884651058136283767374823795429682719157879722733262074242862569136374995060903276082888704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 30 0 (.split 22 0 (.step 53 (.close 23)) (.step 27 (.step 55 (.close 3)))) (.step 53 (.close 3))) (.step 27 (.step 29 (.close 3)))) (.step 3 (.step 9 (.step 18 (.close 40))))) (.split 21 0 (.split 26 0 (.step 53 (.close 31)) (.step 15 (.close 53))) (.step 18 (.close 53)))) (.step 18 (.step 27 (.step 55 (.close 7))))) (.step 18 (.step 53 (.close 55)))) (.step 55 (.close 53))) (.step 9 (.step 11 (.close 3)))) (.step 11 (.step 23 (.step 44 (.step 53 (.close 18)))))) (.step 29 (.step 40 (.step 26 (.close 53))))) (.step 55 (.close 74))) (.step 53 (.step 7 (.close 3)))) (.step 55 (.close 67))) (.step 55 (.close 66))) (.step 53 (.close 55))) (.step 53 (.step 61 (.step 40 (.close 3))))) (.step 9 (.step 53 (.step 23 (.step 57 (.close 53)))))) (.step 53 (.step 7 (.close 3))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303539034662580792616114714031740295275420147661377714516944318814818798623132256173658190396039542563244414075102090652107429724028928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 10 0 (.split 22 0 (.step 52 (.close 23)) (.step 27 (.step 55 (.close 3)))) (.step 52 (.close 3))) (.step 27 (.step 29 (.close 3)))) (.step 3 (.step 9 (.step 18 (.close 40))))) (.split 21 0 (.split 26 0 (.step 52 (.close 31)) (.step 27 (.close 29))) (.step 17 (.step 3 (.close 52))))) (.step 18 (.step 27 (.step 55 (.close 7))))) (.step 53 (.step 23 (.step 55 (.close 7))))) (.step 23 (.step 27 (.step 52 (.close 55))))) (.step 9 (.step 11 (.close 3)))) (.step 11 (.step 23 (.step 44 (.close 52))))) (.step 29 (.step 40 (.step 26 (.step 52 (.close 15)))))) (.step 55 (.close 74))) (.step 52 (.step 7 (.close 3)))) (.step 55 (.close 67))) (.step 55 (.close 66))) (.step 52 (.close 55))) (.step 27 (.step 52 (.step 40 (.step 61 (.close 52)))))) (.step 52 (.step 57 (.step 23 (.close 3))))) (.step 52 (.step 7 (.close 3)))) (.step 52 (.close 53)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541807332274913430974292445924438359123584098453090333519489294399413244440061799281230370445646702822511466313052055679258698186752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 9 (.step 11 (.step 3 (.split 8 0 (.split 12 0 (.split 35 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 11))))))) (.step 3 (.split 72 1 (.split 8 0 (.split 12 0 (.step 70 (.close 3)) (.step 3 (.close 46))) (.step 3 (.close 46))) (.step 7 (.close 9))))) (.step 3 (.close 47))) (.step 3 (.close 47))) (.step 9 (.step 27 (.close 62)))) (.step 11 (.step 3 (.step 9 (.close 27))))) (.step 9 (.close 7))) (.step 3 (.split 58 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 26 0 (.step 54 (.close 3)) (.step 7 (.close 9))) (.step 3 (.close 46))) (.step 3 (.close 46))) (.step 3 (.close 54))) (.step 7 (.close 9))) (.step 9 (.close 27))))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 9 (.step 27 (.close 52)))))
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
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039960161595832553752969540061353763235598671755215363484320878688406182703212502870420652663896318202046656510174934312419328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 12 0 (.split 14 0 (.split 21 0 (.split 49 0 (.split 50 0 (.split 54 0 (.step 45 (.step 7 (.close 21))) (.step 31 (.close 7))) (.step 7 (.close 31))) (.step 7 (.close 31))) (.step 7 (.close 31))) (.step 7 (.step 29 (.close 31)))) (.step 29 (.step 31 (.close 7)))) (.step 29 (.step 31 (.step 3 (.close 37))))) (.step 29 (.step 31 (.step 3 (.close 67))))) (.step 31 (.step 66 (.close 3)))) (.step 29 (.step 40 (.step 66 (.step 7 (.step 9 (.step 37 (.close 39)))))))) (.step 23 (.step 11 (.step 29 (.step 40 (.step 66 (.step 7 (.step 37 (.close 39))))))))) (.step 75 (.close 7))) (.step 3 (.step 29 (.step 31 (.step 45 (.step 39 (.step 66 (.close 67)))))))) (.step 7 (.step 26 (.step 29 (.step 31 (.close 15)))))) (.step 31 (.close 40))) (.step 29 (.step 31 (.step 18 (.close 57))))) (.step 40 (.step 9 (.step 44 (.step 38 (.step 31 (.step 7 (.close 62)))))))) (.step 26 (.step 44 (.step 55 (.step 57 (.step 31 (.close 52)))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962743845710640661559195980525766247473001461008192707833709347762723350834519711615282309249598339878092413346907059912704⟩
def references : Fin 5 → Box := ![Part9.root, Part10.root, Part11.root, Part12.root, Part13.root]
def proof : Chunks.Proof 5 := (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 3 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 12 0 (.split 35 0 (.split 39 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 29)))) (.step 3 (.close 51))) (.step 3 (.split 72 1 (.split 8 0 (.split 12 0 (.step 70 (.close 3)) (.step 3 (.close 54))) (.step 3 (.close 54))) (.step 3 (.close 54))))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.step 62 (.close 7)))) (.step 3 (.step 61 (.close 7)))) (.step 3 (.step 57 (.close 7))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.run (.step 40 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 40 (.step 68 (.split 54 1 (.split 58 1 (.split 59 1 (.step 40 (.split 67 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 63 1 (.step 3 (.close 23)) (.step 23 (.close 15))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 31 (.step 18 (.close 34)))) (.step 18 (.step 11 (.step 7 (.close 11))))) (.step 23 (.close 77))) (.step 3 (.close 7)))) (.step 9 (.step 31 (.close 3)))) (.step 31 (.close 61))) (.step 31 (.close 57))))) (.step 7 (.close 54))) (.step 31 (.step 3 (.close 53)))) (.step 27 (.step 34 (.step 31 (.close 52))))) (.step 7 (.close 9))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11567172216946143397859013993930444732269467542640835691101632188306002089418840193746613689929299388380027152031105869995885999383328480710518153533711234761187139219645056567718059924399987588810690316423697110356933476352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 40 0 (.split 12 0 (.step 40 (.close 3)) (.step 21 (.close 40))) (.step 31 (.close 42))) (.step 3 (.step 27 (.step 31 (.close 23))))) (.step 3 (.step 27 (.step 31 (.close 23))))) (.step 3 (.close 23))) (.step 18 (.step 31 (.close 42)))) (.step 18 (.step 31 (.close 42)))) (.step 27 (.split 17 0 (.step 34 (.step 23 (.close 42))) (.step 36 (.step 17 (.close 42)))))) (.step 3 (.step 27 (.step 31 (.step 17 (.close 42)))))) (.step 27 (.split 10 0 (.split 34 0 (.step 42 (.close 11)) (.step 11 (.close 9))) (.step 11 (.close 42))))) (.step 11 (.step 42 (.close 40)))) (.step 40 (.close 11))) (.step 11 (.step 40 (.step 77 (.split 10 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 40 (.close 42)) (.step 18 (.close 42))) (.step 18 (.close 42))) (.step 17 (.step 27 (.step 36 (.step 34 (.close 42)))))) (.step 18 (.step 23 (.close 42)))))))) (.step 3 (.step 31 (.step 11 (.close 42))))) (.step 3 (.close 42))) (.step 11 (.step 42 (.split 10 0 (.step 67 (.close 3)) (.step 18 (.close 67)))))) (.step 11 (.step 40 (.step 67 (.step 77 (.split 65 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 40 (.step 3 (.close 42))) (.step 18 (.close 42))) (.step 18 (.close 42))) (.step 27 (.step 34 (.close 3)))) (.step 18 (.close 66))) (.step 66 (.close 3))) (.step 3 (.close 42)))))))))
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
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039579348448340217560546144881775448533393304845004773371929851684619645786554371082116211691809739801471483904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 12 0 (.split 21 0 (.split 54 0 (.split 26 0 (.step 7 (.close 31)) (.step 29 (.close 7))) (.step 31 (.close 7))) (.step 7 (.close 31))) (.step 29 (.step 31 (.close 7)))) (.step 29 (.close 74))) (.step 29 (.step 31 (.step 3 (.close 67))))) (.step 31 (.step 51 (.step 31 (.close 66))))) (.step 29 (.step 40 (.step 66 (.step 7 (.step 9 (.step 37 (.close 39)))))))) (.step 23 (.step 11 (.step 29 (.step 40 (.step 66 (.step 7 (.step 37 (.close 39))))))))) (.step 75 (.close 7))) (.step 3 (.step 29 (.step 31 (.close 39))))) (.step 7 (.step 29 (.step 31 (.close 26))))) (.step 31 (.close 36))) (.step 31 (.close 57))) (.step 36 (.step 40 (.step 9 (.step 38 (.step 29 (.step 31 (.step 7 (.close 62))))))))) (.step 57 (.step 7 (.step 31 (.close 52))))) (.step 31 (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 8 0 (.step 45 (.close 31)) (.step 7 (.step 29 (.step 31 (.close 37))))) (.step 29 (.step 23 (.close 77)))) (.step 31 (.step 39 (.close 11)))) (.step 31 (.step 39 (.step 45 (.close 67))))) (.step 31 (.step 37 (.step 45 (.close 66))))) (.step 31 (.close 39))) (.step 7 (.step 29 (.step 31 (.step 21 (.close 62))))))) (.step 7 (.step 26 (.step 29 (.step 31 (.step 37 (.close 52))))))))) (.step 31 (.close 36))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581641946956207632057755702670750620334101409993941653053589273459032709430459566924281710362849927158038528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 40 (.split 36 1 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 75 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 74 1 (.step 29 (.split 8 0 (.split 14 0 (.split 16 0 (.split 10 0 (.step 38 (.split 12 0 (.step 40 (.step 38 (.close 3))) (.step 38 (.close 3)))) (.step 18 (.split 12 0 (.split 17 0 (.step 38 (.close 3)) (.step 3 (.close 7))) (.step 15 (.close 3))))) (.step 38 (.close 40))) (.step 40 (.close 38))) (.step 9 (.step 11 (.close 3))))) (.step 23 (.step 11 (.step 29 (.close 77))))) (.step 74 (.close 38))) (.step 29 (.step 3 (.close 7)))) (.step 3 (.close 38))) (.step 29 (.step 67 (.close 38)))) (.step 66 (.close 38))) (.step 26 (.step 29 (.step 40 (.step 21 (.step 38 (.close 3))))))) (.step 3 (.step 40 (.close 42)))) (.step 29 (.step 38 (.step 57 (.close 23)))))) (.step 3 (.step 51 (.step 55 (.step 29 (.step 38 (.close 75))))))) (.step 9 (.step 23 (.step 21 (.step 53 (.step 38 (.close 7))))))) (.step 9 (.step 53 (.step 55 (.step 57 (.step 66 (.split 51 1 (.step 40 (.step 75 (.split 58 1 (.split 59 1 (.step 40 (.step 38 (.close 3))) (.step 26 (.step 21 (.close 52)))) (.step 22 (.step 23 (.close 52)))))) (.step 3 (.close 52))))))))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 31 (.step 38 (.close 7)))))) (.step 40 (.close 42))) (.step 7 (.step 29 (.step 31 (.step 38 (.close 7))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397854115110619787389832519696295652635656027914246657206013514221614623089666471268558894499322711308479608538912418548371703884709513521475226128148376511838962526117866316874009643540147152092968446328832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 12 0 (.split 21 0 (.split 54 0 (.split 26 0 (.step 7 (.close 31)) (.step 29 (.close 7))) (.step 31 (.close 7))) (.step 7 (.close 31))) (.step 29 (.step 31 (.close 7)))) (.step 29 (.step 31 (.step 3 (.close 37))))) (.step 29 (.step 31 (.step 66 (.close 67))))) (.step 31 (.close 66))) (.step 29 (.step 40 (.step 66 (.step 3 (.close 74)))))) (.step 23 (.step 11 (.step 17 (.step 29 (.step 40 (.step 3 (.step 37 (.close 66))))))))) (.step 75 (.close 7))) (.step 3 (.step 29 (.step 31 (.close 37))))) (.step 7 (.step 15 (.step 29 (.step 31 (.close 21)))))) (.step 31 (.close 34))) (.step 15 (.step 29 (.step 31 (.step 7 (.close 26)))))) (.step 15 (.step 34 (.step 31 (.step 7 (.step 21 (.close 62))))))) (.step 15 (.step 9 (.step 31 (.step 40 (.step 52 (.close 26))))))) (.step 31 (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.step 37 (.close 31)) (.step 7 (.step 9 (.close 37)))) (.step 29 (.step 23 (.close 77)))) (.step 31 (.step 37 (.close 3)))) (.step 3 (.close 37))) (.step 29 (.step 31 (.step 45 (.close 67))))) (.step 37 (.close 66))) (.step 7 (.step 15 (.step 29 (.step 31 (.close 21)))))) (.step 29 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 37))))) (.step 31 (.step 37 (.close 52)))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949809861966260113031188778379531639438887703124173448133673222330747085227091240343198765154304⟩
def references : Fin 5 → Box := ![Part14.root, Part15.root, Part16.root, Part17.root, Part18.root]
def proof : Chunks.Proof 5 := (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.reuse 0) (.split 40 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 42 1 (.reuse 1) (.run (.step 31 (.close 40)))) (.run (.step 42 (.step 3 (.step 44 (.step 40 (.close 3))))))) (.run (.step 42 (.close 40)))) (.run (.step 3 (.step 23 (.step 40 (.step 61 (.step 62 (.split 8 0 (.split 10 0 (.step 21 (.split 12 0 (.step 36 (.step 9 (.step 23 (.close 57)))) (.step 15 (.close 57)))) (.step 3 (.step 15 (.close 40)))) (.step 9 (.close 11)))))))))) (.run (.step 7 (.step 42 (.step 55 (.step 3 (.step 54 (.step 27 (.step 7 (.close 42)))))))))) (.run (.step 42 (.step 53 (.close 21))))) (.run (.step 27 (.step 42 (.close 52))))) (.run (.step 27 (.close 7)))) (.run (.step 27 (.step 31 (.step 42 (.close 24))))))) (.reuse 2)) (.reuse 3)) (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 39 1 (.reuse 4) (.run (.step 31 (.close 34)))) (.run (.step 31 (.split 49 1 (.split 50 1 (.step 37 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.step 37 (.close 31)) (.step 7 (.step 9 (.close 37)))) (.step 29 (.step 23 (.step 11 (.step 31 (.close 37)))))) (.step 31 (.step 37 (.close 3)))) (.step 3 (.close 37))) (.step 31 (.step 39 (.step 3 (.close 67))))) (.step 37 (.close 66))) (.step 7 (.step 15 (.step 29 (.step 31 (.close 21)))))) (.step 29 (.step 31 (.close 37))))) (.step 7 (.step 31 (.close 37)))) (.step 31 (.step 37 (.close 52))))))) (.run (.step 29 (.step 31 (.step 38 (.close 37)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part15.excludes
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567172216946143397854115110619787389832519696295652635656027914246657206013514221614623089666468560876231106070933481562091212960702539691999146931300361375306432567317516445755781887866942800930326923626073790380014305280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 63 1 (.split 64 1 (.split 71 1 (.step 7 (.close 18)) (.step 18 (.close 3))) (.step 18 (.step 3 (.close 67)))) (.step 66 (.step 3 (.close 18)))) (.step 67 (.split 26 0 (.split 63 1 (.split 71 1 (.split 39 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 18 (.close 3))) (.step 18 (.step 3 (.close 19)))) (.step 7 (.step 18 (.close 19)))))) (.step 11 (.split 63 1 (.split 64 1 (.split 71 1 (.split 26 0 (.split 16 0 (.split 39 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 19 (.close 25))) (.step 3 (.step 18 (.close 19)))) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))))) (.step 11 (.close 7))) (.step 77 (.close 7))) (.step 23 (.step 11 (.step 40 (.step 29 (.step 66 (.step 7 (.step 19 (.close 69))))))))) (.step 3 (.step 11 (.step 18 (.step 25 (.step 20 (.step 66 (.close 67)))))))) (.step 7 (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 7 (.close 61))))) (.step 18 (.close 23))) (.step 18 (.step 23 (.step 26 (.step 27 (.step 23 (.step 7 (.step 11 (.close 62))))))))) (.step 26 (.step 44 (.step 55 (.step 61 (.step 18 (.close 52))))))) (.step 42 (.step 18 (.close 7)))) (.step 18 (.step 26 (.step 66 (.step 67 (.step 69 (.step 38 (.step 18 (.step 23 (.step 7 (.step 11 (.step 19 (.close 20))))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623964172260881429718740328165182340038547785766121133586583998431232⟩
def references : Fin 2 → Box := ![Part19.root, Part20.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 26 1 (.split 30 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 8 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 18 (.step 3 (.close 15)))) (.step 3 (.close 67))) (.step 3 (.close 66))) (.step 7 (.step 18 (.close 11)))) (.step 18 (.close 31))) (.step 3 (.step 18 (.close 31)))) (.step 18 (.step 31 (.close 53)))) (.step 52 (.step 18 (.step 31 (.step 7 (.close 3)))))) (.step 18 (.step 31 (.close 42)))) (.step 3 (.step 38 (.close 7))))))) (.run (.step 29 (.split 30 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 74 1 (.step 29 (.step 27 (.step 29 (.split 14 0 (.step 3 (.step 23 (.close 3))) (.step 11 (.step 3 (.close 18))))))) (.step 23 (.step 11 (.step 27 (.close 29))))) (.step 29 (.close 74))) (.step 3 (.step 29 (.close 7)))) (.step 29 (.close 67))) (.step 29 (.close 66))) (.step 27 (.close 29))) (.step 27 (.close 29))) (.step 29 (.close 57))) (.step 3 (.step 55 (.step 29 (.close 26))))) (.step 27 (.step 57 (.step 29 (.close 26))))) (.step 27 (.step 29 (.step 57 (.split 34 0 (.step 53 (.step 29 (.close 26))) (.step 18 (.close 29))))))) (.step 27 (.close 29))) (.step 3 (.step 7 (.step 29 (.close 7)))))))) (.step 7 (.split 26 1 (.reuse 1) (.run (.step 18 (.step 29 (.step 23 (.step 11 (.step 40 (.step 29 (.step 66 (.step 19 (.close 69)))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438750924782483134364897389052768501986767166447347040256⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.reuse 0) (.run (.step 18 (.step 23 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 23 (.step 68 (.split 54 1 (.split 58 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 68 (.step 18 (.close 24))) (.step 21 (.close 24))) (.step 7 (.close 31))) (.step 23 (.close 29))) (.step 9 (.step 24 (.step 15 (.step 18 (.close 24)))))) (.step 23 (.step 26 (.step 29 (.step 24 (.step 15 (.step 21 (.close 24)))))))) (.step 3 (.close 7))) (.step 9 (.step 18 (.close 3)))) (.step 18 (.close 3))) (.step 18 (.close 57))))) (.step 7 (.close 54))) (.step 9 (.step 21 (.step 18 (.close 53))))) (.step 52 (.step 18 (.step 3 (.close 52))))) (.step 7 (.close 9))) (.step 7 (.step 26 (.close 31)))) (.step 24 (.close 31))) (.step 23 (.step 3 (.close 42)))) (.step 7 (.step 24 (.step 29 (.step 31 (.close 26)))))) (.step 9 (.step 21 (.step 29 (.step 18 (.step 31 (.close 38))))))) (.step 7 (.step 31 (.close 37)))) (.step 29 (.close 18)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397854115110619787389832519696295652635656027914246657206013514221614623089666468560876231106070933481562091212960702539691999146931300361373621435900620602955166770071772804124401274098691100137985962672128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 63 1 (.split 64 1 (.split 71 1 (.step 7 (.close 18)) (.step 18 (.close 3))) (.step 18 (.step 3 (.close 67)))) (.step 11 (.step 51 (.step 66 (.close 3))))) (.step 67 (.step 74 (.split 26 0 (.split 63 1 (.split 39 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 18 (.close 3))) (.step 7 (.step 18 (.close 19))))))) (.step 11 (.step 74 (.split 63 1 (.split 64 1 (.split 26 0 (.split 16 0 (.split 39 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 19 (.close 20))) (.step 3 (.step 18 (.close 19)))) (.step 18 (.close 67))) (.step 18 (.close 66)))))) (.step 7 (.step 3 (.close 20)))) (.step 11 (.close 7))) (.step 77 (.close 7))) (.step 23 (.step 11 (.step 40 (.step 29 (.step 66 (.step 7 (.step 19 (.close 69))))))))) (.step 3 (.step 11 (.step 18 (.close 20))))) (.step 7 (.step 11 (.step 18 (.close 19))))) (.step 18 (.close 61))) (.step 18 (.close 22))) (.step 18 (.step 22 (.step 23 (.step 27 (.step 23 (.step 7 (.step 11 (.step 19 (.close 44)))))))))) (.step 61 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 7 (.step 11 (.step 18 (.close 19))))) (.step 42 (.step 18 (.close 7)))) (.step 66 (.step 67 (.step 74 (.step 7 (.step 11 (.step 18 (.close 38)))))))))
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
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519696295652635656027914246657206013514221614623089666468560876231106070933481562091212960702539691999148783973789170680562677756361599057120734578873452280714861254915156577045446656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 35 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 63 1 (.split 64 1 (.split 71 1 (.step 7 (.close 18)) (.step 18 (.close 3))) (.step 18 (.close 67))) (.step 66 (.step 3 (.close 18)))) (.step 67 (.step 74 (.split 26 0 (.split 63 1 (.split 39 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 18 (.close 3))) (.step 7 (.step 18 (.close 19))))))) (.step 11 (.step 67 (.split 63 1 (.split 71 1 (.split 26 0 (.split 17 0 (.split 39 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 19 (.close 18))) (.step 18 (.close 19))) (.step 18 (.close 74))) (.step 18 (.close 66)))))) (.step 7 (.step 3 (.close 19)))) (.step 11 (.close 7))) (.step 77 (.close 7))) (.step 23 (.step 11 (.step 40 (.step 29 (.step 38 (.step 3 (.step 66 (.step 19 (.close 67)))))))))) (.step 3 (.step 11 (.step 18 (.close 19))))) (.step 7 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 7 (.close 19))))) (.step 18 (.close 21))) (.step 18 (.step 21 (.step 23 (.step 27 (.step 23 (.step 7 (.step 11 (.step 19 (.close 17)))))))))) (.step 42 (.step 18 (.step 27 (.step 23 (.step 52 (.close 11))))))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.step 42 (.close 3)))) (.step 18 (.step 38 (.step 23 (.step 11 (.step 40 (.step 38 (.close 19)))))))) (.step 18 (.step 29 (.step 23 (.step 11 (.step 40 (.step 29 (.step 66 (.step 19 (.close 67)))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438752422821661398540388547829722036176862313778203590656⟩
def references : Fin 1 → Box := ![Part24.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 18 (.split 26 1 (.split 35 1 (.split 49 1 (.step 19 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 26 0 (.step 19 (.close 18)) (.step 18 (.close 19))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.step 19 (.close 3)))) (.step 3 (.close 19))) (.step 18 (.close 67))) (.step 11 (.step 18 (.step 66 (.close 3))))) (.step 18 (.close 19))) (.step 11 (.step 18 (.close 19)))) (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 52))))) (.step 18 (.step 19 (.close 38)))) (.step 7 (.step 18 (.step 19 (.step 29 (.step 19 (.close 66)))))))))) (.run (.step 18 (.split 26 1 (.split 35 1 (.split 49 1 (.step 19 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 26 0 (.step 19 (.close 18)) (.step 18 (.close 19))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.step 19 (.close 3)))) (.step 3 (.close 19))) (.step 18 (.close 67))) (.step 11 (.step 18 (.step 51 (.step 19 (.close 66)))))) (.step 18 (.close 19))) (.step 11 (.step 18 (.close 19)))) (.step 11 (.step 18 (.close 19))))) (.step 11 (.step 18 (.step 19 (.close 52))))) (.step 18 (.step 19 (.close 38)))) (.step 7 (.step 18 (.step 19 (.step 29 (.step 19 (.close 66))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438752422821661398540388547829722036176862313778203590656⟩
def references : Fin 3 → Box := ![Part22.root, Part23.root, Part25.root]
def proof : Chunks.Proof 3 := (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.split 26 1 (.reuse 1) (.run (.step 18 (.step 29 (.step 23 (.step 11 (.step 40 (.step 29 (.step 66 (.step 20 (.close 67))))))))))) (.run (.step 18 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.step 25 (.split 50 1 (.split 58 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 26 0 (.step 25 (.close 18)) (.step 7 (.step 11 (.step 18 (.close 19))))) (.step 7 (.step 18 (.close 20)))) (.step 18 (.step 20 (.close 19)))) (.step 18 (.step 19 (.step 20 (.close 29))))) (.step 11 (.step 18 (.step 66 (.close 3))))) (.step 18 (.close 20))) (.step 7 (.step 18 (.step 19 (.close 20)))))) (.step 18 (.step 20 (.close 62)))) (.step 18 (.step 19 (.step 20 (.close 42))))) (.step 18 (.step 19 (.step 20 (.step 25 (.close 38)))))) (.step 7 (.step 18 (.step 25 (.step 29 (.step 20 (.close 66))))))))))))) (.reuse 2))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes
  · exact Part23.excludes
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039579348448340217560546144881775448533393304845004773371929851684621039583129279246062557674201780324065607680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 77 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 11 (.split 26 0 (.split 34 0 (.split 35 0 (.split 10 0 (.split 16 0 (.split 36 0 (.step 17 (.close 55)) (.step 23 (.close 17))) (.step 17 (.close 7))) (.step 17 (.close 3))) (.step 23 (.close 17))) (.step 17 (.close 23))) (.step 23 (.close 17)))) (.step 23 (.step 17 (.close 29)))) (.step 74 (.close 17))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.close 17))) (.step 67 (.close 17))) (.step 66 (.step 3 (.close 17)))) (.step 27 (.step 23 (.step 17 (.close 55))))) (.step 61 (.close 17))) (.step 3 (.step 23 (.close 15))))) (.step 3 (.step 51 (.step 55 (.step 11 (.step 17 (.close 77))))))) (.step 27 (.step 34 (.step 55 (.step 61 (.step 67 (.split 51 1 (.split 54 1 (.split 59 1 (.step 23 (.step 17 (.close 3))) (.step 44 (.step 17 (.close 36)))) (.step 3 (.step 15 (.close 23)))) (.step 3 (.close 53))))))))) (.step 23 (.step 27 (.step 34 (.step 52 (.step 17 (.close 7))))))) (.step 11 (.step 7 (.close 27)))) (.step 31 (.step 40 (.step 44 (.step 66 (.step 67 (.step 69 (.step 23 (.step 17 (.step 29 (.step 17 (.close 37)))))))))))) (.step 23 (.step 27 (.step 17 (.step 31 (.close 34)))))) (.step 27 (.step 42 (.close 17)))) (.step 36 (.step 66 (.step 67 (.step 74 (.step 7 (.step 29 (.step 23 (.step 17 (.close 37)))))))))))
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
def root : Box := ⟨2658455991569831745807614122708172800, 11567172216946143397859013993930444732269467546697054275260546546898243434141054110322767815189173562970658750226223792496339035117951048923620566259799736360951717865483809095403427016483293581985414693974846904250274938880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 23 (.split 8 0 (.split 21 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.split 22 0 (.step 15 (.close 23)) (.step 18 (.step 3 (.close 15)))) (.step 3 (.close 15))) (.step 18 (.close 15))) (.step 9 (.step 21 (.step 15 (.close 3))))) (.step 15 (.close 3))) (.step 3 (.step 9 (.step 18 (.step 15 (.close 3)))))) (.split 16 0 (.step 15 (.close 23)) (.step 18 (.step 15 (.close 3))))) (.step 18 (.close 15))) (.step 9 (.close 11)))) (.step 15 (.step 23 (.close 3)))) (.step 23 (.step 29 (.step 75 (.split 8 0 (.split 10 0 (.split 14 0 (.step 22 (.step 15 (.step 23 (.close 15)))) (.step 23 (.close 15))) (.step 3 (.close 15))) (.step 9 (.close 11))))))) (.step 3 (.step 7 (.step 9 (.step 15 (.close 7)))))) (.step 3 (.close 15))) (.step 23 (.step 29 (.step 55 (.step 75 (.split 21 1 (.split 65 1 (.split 71 1 (.split 8 0 (.split 10 0 (.split 14 0 (.step 21 (.step 15 (.step 23 (.close 3)))) (.step 23 (.close 15))) (.step 3 (.close 15))) (.step 9 (.close 11))) (.step 66 (.close 67))) (.step 3 (.close 15))) (.step 15 (.close 18)))))))) (.step 15 (.step 29 (.step 66 (.split 10 0 (.step 66 (.close 3)) (.step 3 (.close 15))))))) (.step 9 (.step 15 (.step 23 (.close 62))))) (.step 3 (.step 23 (.step 40 (.step 62 (.split 10 0 (.split 8 0 (.step 22 (.step 15 (.step 27 (.step 34 (.step 23 (.close 3)))))) (.step 9 (.close 11))) (.step 3 (.close 15)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨2658455991569831745807614122708172800, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438752422821662792338292683989453298032158161361078059008⟩
def references : Fin 1 → Box := ![Part28.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.step 15 (.close 23)))) (.run (.step 7 (.step 15 (.step 55 (.step 3 (.step 54 (.step 9 (.step 7 (.close 15)))))))))) (.run (.step 9 (.step 15 (.step 22 (.close 53)))))) (.run (.step 15 (.step 52 (.close 17))))) (.run (.step 7 (.step 9 (.close 7))))) (.run (.step 7 (.step 15 (.step 23 (.step 26 (.step 29 (.step 24 (.close 31))))))))) (.run (.step 3 (.step 15 (.step 31 (.close 15)))))) (.run (.step 3 (.step 23 (.step 34 (.step 40 (.step 62 (.split 40 1 (.split 54 1 (.split 58 1 (.split 8 0 (.split 10 0 (.step 21 (.step 15 (.step 9 (.step 23 (.step 3 (.close 15)))))) (.step 3 (.close 15))) (.step 9 (.close 11))) (.step 27 (.step 34 (.close 42)))) (.step 15 (.close 23))) (.step 3 (.step 21 (.step 15 (.close 31)))))))))))) (.run (.step 7 (.step 15 (.step 22 (.step 29 (.step 31 (.step 15 (.close 7))))))))) (.run (.step 9 (.step 15 (.step 22 (.close 38)))))) (.run (.step 15 (.step 31 (.close 7))))) (.run (.step 7 (.step 15 (.step 3 (.step 18 (.close 31))))))) (.run (.step 15 (.close 29))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part28.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part29

namespace Part30
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438752422821662792338292683989453298032158161361078059008⟩
def references : Fin 3 → Box := ![Part26.root, Part27.root, Part29.root]
def proof : Chunks.Proof 3 := (.split 12 1 (.split 14 1 (.reuse 0) (.step 23 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 1) (.run (.step 42 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 42 1 (.split 72 1 (.split 74 1 (.split 8 0 (.step 40 (.step 29 (.step 23 (.close 17)))) (.step 9 (.close 11))) (.step 17 (.close 23))) (.step 38 (.close 17))) (.step 31 (.close 38))) (.step 31 (.close 38))))))))) (.run (.step 17 (.step 38 (.step 40 (.step 29 (.step 66 (.step 7 (.step 31 (.step 37 (.step 17 (.close 37)))))))))))) (.run (.step 7 (.step 11 (.step 3 (.step 31 (.step 17 (.step 31 (.step 17 (.step 42 (.step 3 (.close 17)))))))))))) (.run (.step 29 (.step 17 (.step 23 (.step 11 (.step 27 (.step 29 (.close 17))))))))) (.run (.step 17 (.step 7 (.step 17 (.close 18)))))) (.run (.step 17 (.step 7 (.step 18 (.close 17)))))) (.run (.step 17 (.step 7 (.step 17 (.step 18 (.close 17))))))))) (.reuse 2))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part26.excludes
  · exact Part27.excludes
  · exact Part29.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part30

namespace Part31
def root : Box := ⟨2417851639229260496896000, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438752422821662792338292685257105107186207177486955970560⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 11 (.split 10 1 (.split 12 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 11 (.step 9 (.step 11 (.split 26 0 (.step 3 (.step 9 (.close 3))) (.step 9 (.close 3)))))) (.step 9 (.step 11 (.close 29)))) (.step 11 (.close 74))) (.step 3 (.step 11 (.close 7)))) (.step 11 (.close 67))) (.step 11 (.close 66))) (.step 9 (.close 11))) (.step 11 (.close 61))) (.step 9 (.close 11))) (.step 3 (.step 55 (.step 11 (.close 44))))) (.step 9 (.step 61 (.step 11 (.close 44))))) (.step 9 (.step 11 (.step 61 (.split 14 0 (.step 53 (.step 11 (.close 44))) (.step 11 (.close 34))))))) (.step 9 (.step 11 (.step 40 (.step 29 (.step 23 (.step 11 (.step 66 (.close 69))))))))) (.step 11 (.close 31))) (.step 11 (.close 42))) (.step 11 (.step 40 (.step 29 (.step 66 (.step 67 (.step 7 (.step 9 (.step 11 (.close 39)))))))))) (.step 9 (.step 11 (.step 38 (.step 11 (.close 38)))))) (.step 11 (.step 38 (.step 40 (.step 29 (.step 66 (.step 7 (.step 9 (.step 37 (.step 11 (.step 37 (.close 67)))))))))))) (.step 3 (.step 7 (.step 11 (.close 7))))) (.step 9 (.step 29 (.step 11 (.close 29))))) (.step 9 (.close 11))) (.step 3 (.step 7 (.step 11 (.close 7)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part31

namespace Part32
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054275260550146029282423926730122814514303541810039962746367439039581644186700949811899002236449369948474623965817765438752422821662792338292685257105107186207177486955970560⟩
def references : Fin 2 → Box := ![Part30.root, Part31.root]
def proof : Chunks.Proof 2 := (.split 8 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.split 12 1 (.split 14 1 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 8 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 18 (.step 3 (.close 15)))) (.step 66 (.step 18 (.step 3 (.close 15))))) (.step 3 (.close 66))) (.step 7 (.step 18 (.close 11)))) (.step 18 (.close 31))) (.step 15 (.step 18 (.close 31)))) (.step 18 (.step 31 (.step 52 (.close 53))))) (.step 31 (.step 52 (.close 55)))) (.step 3 (.step 18 (.step 31 (.close 42))))) (.step 3 (.step 18 (.step 29 (.step 38 (.step 18 (.step 38 (.close 3)))))))) (.step 29 (.step 3 (.close 7)))) (.step 11 (.step 3 (.step 17 (.close 7))))) (.step 15 (.close 3)))))) (.reuse 1))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part30.excludes
  · exact Part31.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part32

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part32.excludes
end FiveColour.Packed.ProjectedChunks.Case21
