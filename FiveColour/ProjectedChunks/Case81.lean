module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case81
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562851922368242941742672128758506872498766551979367279320337164452299911707525405913513012166084551394003517440⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11592783902519133514739, 5789228615357111146520048038021683984422651049967145797140232129277306765738256663147118356499696898191722988419604555454183885220064633287200423898230768667241036816214958065107230067542665395155955896287055491154965431296, 0⟩]
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
def root : Box := ⟨3221225472, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168957499588850659789093106779054817433303901179239374402154620894975243164057600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 55 (.split 43 0 (.split 49 0 (.step 31 (.close 3)) (.step 55 (.step 3 (.close 5)))) (.step 3 (.close 9)))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 29 (.step 32 (.step 40 (.step 3 (.close 21))))) (.step 18 (.step 23 (.close 3)))) (.step 18 (.step 23 (.close 3)))) (.step 18 (.close 38)))) (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.close 21)) (.step 3 (.close 15))) (.step 3 (.close 39))) (.step 3 (.step 7 (.close 15)))))) (.step 18 (.step 3 (.step 31 (.step 23 (.close 3)))))) (.split 16 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 40 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 35 0 (.split 49 0 (.step 12 (.step 18 (.close 21))) (.step 17 (.close 52))) (.step 23 (.close 18))) (.step 3 (.step 12 (.step 3 (.close 23))))) (.step 3 (.close 11))) (.step 3 (.step 12 (.step 3 (.close 23))))) (.step 18 (.close 40))) (.step 18 (.close 40))) (.step 18 (.step 12 (.close 40)))) (.step 31 (.close 17))) (.step 18 (.step 3 (.step 18 (.close 21)))))))
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
def root : Box := ⟨3221225472, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168957499588850659789093106779054817433303902508468637837670722028183800147607552⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 9 (.split 40 0 (.split 49 0 (.split 51 0 (.split 55 0 (.step 55 (.close 22)) (.step 31 (.close 15))) (.step 3 (.step 15 (.close 18)))) (.step 12 (.close 3))) (.step 12 (.step 31 (.close 57))))) (.step 21 (.step 9 (.step 12 (.step 5 (.close 40)))))) (.step 9 (.step 31 (.close 15)))) (.step 3 (.step 31 (.close 23)))) (.step 3 (.step 23 (.step 12 (.step 23 (.close 31)))))) (.step 3 (.step 18 (.step 12 (.step 23 (.step 31 (.step 18 (.step 15 (.close 55))))))))) (.step 18 (.step 22 (.close 40)))) (.step 18 (.step 21 (.close 3)))) (.step 40 (.split 16 0 (.step 55 (.split 34 0 (.split 36 0 (.split 38 0 (.step 40 (.step 15 (.step 9 (.step 12 (.close 23))))) (.step 5 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 12)))) (.step 3 (.close 12))))))) (.run (.step 31 (.step 18 (.split 12 0 (.split 14 0 (.split 16 0 (.step 18 (.step 12 (.close 3))) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 3 (.close 12)))))))
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
def root : Box := ⟨3221225472, 17350747283341930566433056814635378094421879396292588682511137316830266279841187091155481979423074363869924201745158867291449104943218780031064530407942120102600329883819984284682934272832622118194347815147334420178198855680⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 74 1 (.split 2 0 (.reuse 0) (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 38 0 (.step 3 (.close 40)) (.step 5 (.close 3))) (.step 3 (.step 5 (.close 23)))) (.step 3 (.close 31))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 23 (.step 31 (.split 35 0 (.split 43 0 (.step 12 (.split 16 0 (.step 40 (.step 34 (.step 18 (.close 5)))) (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.close 40)))))) (.step 3 (.step 12 (.step 31 (.close 21))))))) (.run (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 23 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 44 (.step 11 (.step 40 (.step 77 (.close 3))))) (.step 23 (.close 31))) (.step 23 (.close 31))) (.step 23 (.close 31))) (.step 18 (.close 32)))) (.step 18 (.close 44))) (.step 11 (.step 18 (.close 55)))) (.step 11 (.step 18 (.close 77)))) (.step 11 (.step 77 (.step 17 (.step 12 (.step 18 (.step 5 (.close 23)))))))) (.step 23 (.split 14 0 (.split 16 0 (.split 17 0 (.step 40 (.step 23 (.close 3))) (.step 3 (.close 77))) (.step 18 (.close 21))) (.step 17 (.close 3))))) (.step 18 (.step 3 (.close 77)))) (.step 23 (.step 31 (.close 77))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520981542654921261869820368706048126747639186781733646192222688776401164500418274829841045424854600131233293061207459189555534858340804198695552582100272385459549039754422805846419618819253922958409728⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 71 1 (.split 72 1 (.reuse 0) (.run (.step 69 (.step 29 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 75 (.split 21 0 (.split 51 0 (.step 31 (.close 12)) (.step 18 (.step 26 (.step 22 (.close 3))))) (.step 18 (.step 26 (.step 23 (.close 31)))))) (.step 18 (.close 75))) (.step 18 (.close 75))) (.step 40 (.close 75))) (.step 31 (.close 75))))))) (.run (.split 72 1 (.split 74 1 (.split 2 0 (.split 12 0 (.split 10 0 (.split 21 0 (.split 16 0 (.split 22 0 (.split 35 0 (.split 38 0 (.split 39 0 (.step 74 (.close 31)) (.step 67 (.step 74 (.close 23)))) (.step 31 (.step 32 (.close 74)))) (.step 74 (.step 18 (.close 55)))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.step 18 (.step 31 (.close 74)))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 10 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 55 (.close 74)) (.step 12 (.step 21 (.step 22 (.close 31))))) (.step 31 (.close 55))) (.step 22 (.step 32 (.step 40 (.step 55 (.close 15)))))) (.step 31 (.close 66))) (.step 18 (.step 23 (.step 31 (.close 32))))) (.step 12 (.close 3))) (.step 23 (.close 31))) (.step 18 (.close 22))) (.step 18 (.close 74)))) (.split 14 0 (.step 31 (.split 38 0 (.split 39 0 (.split 40 0 (.step 3 (.close 74)) (.step 18 (.close 31))) (.step 23 (.close 58))) (.step 23 (.close 74)))) (.step 23 (.close 74)))) (.step 74 (.close 77))) (.step 29 (.step 74 (.close 75)))))) (.run (.step 69 (.split 72 1 (.step 3 (.step 18 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 12))))) (.step 3 (.close 15))))))
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
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630616877957120, 17350758325419215096788520990895667098404201311933144248350637238599394105592668300219735475343401033074429437830566637161702207080293134745818976448346964171894752385402396315045138717405929934921487927181191978642152882176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 66 (.step 3 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 64 1 (.split 71 1 (.split 2 0 (.split 12 0 (.split 10 0 (.split 21 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 14 0 (.split 30 0 (.split 34 0 (.step 55 (.close 31)) (.step 31 (.close 15))) (.step 31 (.close 23))) (.step 12 (.close 66))) (.step 12 (.step 67 (.step 31 (.close 3))))) (.step 31 (.step 32 (.close 66)))) (.split 30 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 14 0 (.step 40 (.close 55)) (.step 12 (.close 3))) (.step 31 (.close 66))) (.step 12 (.step 31 (.close 23)))) (.step 31 (.close 66))) (.step 31 (.close 32)))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 18 (.step 31 (.step 23 (.close 4))))) (.step 18 (.close 66))) (.split 16 0 (.split 17 0 (.split 30 0 (.step 12 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 34 (.close 66)) (.step 31 (.close 15))) (.step 22 (.close 66))) (.step 21 (.close 66))) (.step 31 (.close 15)))) (.step 3 (.close 66))) (.step 18 (.close 66))) (.step 3 (.close 66)))) (.split 14 0 (.step 31 (.split 38 0 (.split 39 0 (.split 40 0 (.step 3 (.step 23 (.close 66))) (.step 18 (.close 31))) (.step 23 (.close 58))) (.step 18 (.step 23 (.step 5 (.close 15)))))) (.step 12 (.close 3)))) (.step 66 (.close 3))) (.step 66 (.close 3))) (.step 66 (.close 77))) (.step 66 (.close 75))) (.step 63 (.step 66 (.close 68))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201311933144248350637238599394105592668300219735475343401033074429437830566637161702207080293134745818976448346964171894752385402396315045138717405929934921487927181191978642152882176⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 63 1 (.split 64 1 (.split 65 1 (.reuse 0) (.run (.split 72 1 (.split 74 1 (.split 71 1 (.step 3 (.step 43 (.step 18 (.step 63 (.step 3 (.close 15)))))) (.step 63 (.step 3 (.close 74)))) (.step 3 (.step 18 (.close 77)))) (.step 3 (.step 31 (.close 74)))))) (.run (.step 3 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 71 1 (.split 2 0 (.split 12 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 16 0 (.split 21 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 54 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 55 (.close 5)) (.step 32 (.step 40 (.step 21 (.close 55))))) (.step 32 (.close 3))) (.step 31 (.close 23))) (.step 32 (.step 40 (.close 55)))) (.step 31 (.close 67))) (.step 31 (.close 55))) (.step 18 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 67))) (.step 67 (.close 18))) (.step 18 (.step 31 (.close 67)))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 10 0 (.step 32 (.step 66 (.step 21 (.step 40 (.step 18 (.step 31 (.close 3))))))) (.step 12 (.close 3))) (.step 23 (.close 31))) (.step 18 (.close 67))) (.step 18 (.close 21)))) (.split 14 0 (.step 31 (.step 23 (.step 32 (.step 58 (.split 38 0 (.step 3 (.close 67)) (.step 18 (.close 31))))))) (.step 23 (.close 67)))) (.step 67 (.close 3))) (.step 67 (.close 77))) (.step 67 (.close 75))) (.step 63 (.step 67 (.close 68)))))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416711979597824, 17350758325419215096788520990895658187387370018591022412659484200307836254178368790457245266029253289929868501177518829004151622588728066919017867961437310968650859907859299658913814673675304982207650148662042764737254522880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 72 1 (.split 2 0 (.split 12 0 (.split 67 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 34 0 (.split 43 0 (.split 38 0 (.step 61 (.close 31)) (.step 40 (.step 42 (.close 61)))) (.step 3 (.close 27))) (.step 3 (.close 40))) (.step 18 (.close 61))) (.step 18 (.close 61))) (.step 18 (.close 61))) (.step 34 (.step 61 (.close 3)))) (.step 18 (.step 31 (.step 3 (.close 61))))) (.step 3 (.close 12))) (.step 3 (.split 10 0 (.step 34 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 22 (.step 27 (.step 40 (.close 61)))) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 18 (.close 22))) (.step 3 (.close 61)))) (.step 3 (.close 12))))) (.step 27 (.split 10 0 (.split 12 0 (.split 21 0 (.split 30 0 (.split 35 0 (.step 61 (.close 31)) (.step 3 (.close 40))) (.step 3 (.close 5))) (.step 3 (.close 18))) (.step 3 (.step 5 (.close 61)))) (.step 3 (.close 5))))) (.step 40 (.close 3))) (.step 61 (.step 40 (.close 18)))) (.step 36 (.step 40 (.split 34 0 (.split 38 0 (.split 42 0 (.step 61 (.close 3)) (.step 40 (.close 61))) (.step 40 (.close 61))) (.step 22 (.close 74)))))) (.step 3 (.close 61))) (.step 11 (.step 32 (.step 40 (.step 51 (.step 55 (.step 68 (.step 74 (.step 77 (.split 65 1 (.split 2 0 (.step 74 (.split 34 0 (.step 42 (.step 61 (.step 67 (.step 18 (.close 23))))) (.step 17 (.step 18 (.close 40))))) (.step 40 (.close 67))) (.step 3 (.close 61)))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581416668465955783876795037096133372043725863149382255697677677595620655947450266671089554590852107150586945224122716127169440306578404341443822263583834845894105119484542976⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 44 (.step 26 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 62 (.close 5)) (.step 9 (.step 26 (.step 40 (.close 62))))) (.step 3 (.step 26 (.step 31 (.close 23))))) (.step 3 (.step 18 (.close 62)))) (.step 3 (.close 23))) (.step 3 (.step 18 (.close 62)))) (.step 3 (.step 18 (.close 62)))) (.step 27 (.step 44 (.step 52 (.step 23 (.step 55 (.close 3))))))) (.step 9 (.step 26 (.split 14 0 (.split 17 0 (.split 21 0 (.split 34 0 (.split 35 0 (.step 62 (.close 31)) (.step 15 (.step 21 (.close 62)))) (.step 3 (.step 15 (.close 23)))) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 15 (.close 23)))))) (.step 3 (.step 18 (.close 62)))) (.step 3 (.step 40 (.close 62)))) (.step 27 (.step 23 (.close 44)))) (.step 55 (.close 74))) (.step 3 (.close 7))) (.step 67 (.step 55 (.close 67)))) (.step 66 (.split 38 0 (.step 55 (.close 66)) (.step 23 (.step 26 (.step 31 (.close 55)))))))))))) (.split 59 1 (.split 63 1 (.reuse 1) (.run (.step 11 (.step 12 (.step 34 (.step 40 (.step 51 (.step 55 (.step 67 (.step 68 (.step 74 (.step 77 (.split 2 0 (.split 16 0 (.split 65 1 (.split 35 0 (.step 61 (.step 18 (.step 23 (.close 31)))) (.step 23 (.step 32 (.close 31)))) (.step 3 (.close 18))) (.step 18 (.close 61))) (.step 23 (.step 40 (.close 58)))))))))))))))) (.run (.step 27 (.step 44 (.step 55 (.step 61 (.step 40 (.close 3)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424216390805426959499520205295348581507696991823088578534430008221147195775050968793726844302462468122028160872777654859239847747664191029087386452337711286192418275196928⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 56 1 (.reuse 0) (.run (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 3 (.split 72 1 (.split 74 1 (.split 58 1 (.split 14 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 31 (.step 5 (.close 58))) (.step 31 (.close 3))) (.step 3 (.close 31))) (.step 3 (.step 5 (.close 31)))) (.step 3 (.step 5 (.close 31)))) (.step 5 (.step 18 (.close 31)))) (.step 5 (.step 18 (.close 31)))) (.step 3 (.close 31))) (.step 5 (.step 18 (.close 31)))) (.step 5 (.close 58))) (.step 5 (.close 77))) (.step 31 (.step 3 (.close 38))))) (.step 31 (.step 5 (.close 74)))) (.step 22 (.step 43 (.step 3 (.close 31))))) (.step 31 (.step 58 (.step 63 (.close 67))))) (.step 31 (.step 58 (.step 63 (.step 66 (.close 5)))))) (.step 3 (.step 31 (.step 5 (.close 12)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 17350758325419215096788520990895658187387370018583107839812352053479971442619952577237733360428988702568007766449159079009658781779407016465650600986867951708389783322457069611248195768182032296123891980913000732290664366080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.step 3 (.split 74 1 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 16 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 17 0 (.step 9 (.step 55 (.close 57))) (.step 3 (.close 23))) (.step 21 (.step 3 (.close 57)))) (.step 22 (.close 57))) (.step 21 (.step 57 (.close 3)))) (.step 31 (.close 57))) (.step 3 (.step 31 (.close 32)))) (.step 18 (.step 21 (.close 57)))) (.step 3 (.step 31 (.step 23 (.close 57))))) (.split 16 0 (.split 17 0 (.step 15 (.step 9 (.step 57 (.step 23 (.step 40 (.close 3)))))) (.step 3 (.close 23))) (.step 18 (.close 23)))) (.split 38 0 (.split 39 0 (.split 55 0 (.step 15 (.close 57)) (.step 12 (.step 18 (.close 57)))) (.step 12 (.step 21 (.close 57)))) (.step 15 (.step 21 (.close 57))))) (.step 3 (.step 15 (.step 12 (.step 31 (.close 21)))))) (.step 3 (.step 31 (.split 14 0 (.step 57 (.close 5)) (.step 12 (.step 5 (.close 23))))))) (.step 23 (.close 57)))) (.step 57 (.close 75))) (.step 22 (.step 29 (.step 57 (.split 2 0 (.split 30 0 (.split 38 0 (.split 40 0 (.step 74 (.close 12)) (.step 23 (.close 57))) (.step 31 (.close 74))) (.step 23 (.close 57))) (.step 23 (.close 57))))))) (.step 3 (.close 57))) (.step 21 (.step 23 (.step 29 (.step 32 (.step 51 (.step 55 (.step 68 (.step 74 (.step 75 (.split 2 0 (.split 65 1 (.split 14 0 (.step 57 (.step 23 (.close 31))) (.step 12 (.close 23))) (.step 3 (.close 31))) (.step 3 (.step 23 (.close 15)))))))))))))))
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
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 17350758325419215096788520990895667098404201320045581424223769024050010341588014578501186517945538126362593677708293460286279188683270033834167529187678503033886743071093833507849809220522039738876426302607905061140696137728⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 0) (.run (.step 12 (.step 23 (.step 29 (.step 51 (.step 55 (.step 67 (.step 68 (.step 75 (.split 65 1 (.split 2 0 (.step 74 (.split 21 0 (.split 30 0 (.split 35 0 (.split 16 0 (.step 15 (.step 40 (.step 55 (.close 3)))) (.step 18 (.close 66))) (.step 15 (.step 21 (.step 32 (.close 55))))) (.step 15 (.step 18 (.step 23 (.close 32))))) (.step 23 (.close 31)))) (.step 15 (.step 23 (.close 57)))) (.step 3 (.close 57))))))))))))) (.run (.step 55 (.step 57 (.close 62))))) (.run (.step 22 (.step 23 (.step 57 (.split 34 0 (.split 38 0 (.split 42 0 (.step 61 (.close 3)) (.step 3 (.step 5 (.close 57)))) (.step 5 (.step 32 (.close 61)))) (.step 23 (.close 57)))))))) (.run (.step 48 (.step 5 (.close 57))))) (.run (.step 3 (.step 48 (.step 57 (.step 58 (.step 21 (.close 57))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 17350758325419215096788520981547226272896323308945298204895531193116171754735238150900949345406598760049745795123557009877112676858187375595539744658026001494300491215133583287577121547606994300861499951486505760105281093632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 64 1 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 17 0 (.split 30 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 53 (.close 5)) (.step 3 (.close 32))) (.step 3 (.step 21 (.step 22 (.close 53))))) (.step 3 (.step 21 (.step 31 (.close 23))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 53)))) (.step 55 (.split 16 0 (.step 52 (.step 53 (.close 3))) (.step 3 (.step 17 (.step 18 (.close 32))))))) (.step 9 (.step 21 (.split 14 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.step 53 (.close 3)) (.step 3 (.step 15 (.close 5)))) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 15 (.close 23)))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 32 (.step 40 (.close 5))))) (.step 32 (.close 3))) (.step 27 (.step 61 (.step 40 (.close 53))))) (.step 3 (.step 31 (.close 5)))) (.step 58 (.close 53))) (.step 57 (.close 53))) (.step 27 (.step 32 (.step 44 (.step 55 (.step 61 (.split 54 1 (.split 12 0 (.step 23 (.step 55 (.close 53))) (.step 21 (.close 23))) (.step 23 (.close 3))))))))) (.step 9 (.step 21 (.step 26 (.step 31 (.step 32 (.step 40 (.step 55 (.step 31 (.close 53)))))))))) (.step 48 (.step 55 (.step 23 (.close 74))))) (.step 3 (.close 7))) (.step 32 (.step 48 (.step 55 (.step 23 (.close 66)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 17350758325419215096788520981551788713513945512264504685548354783121685883598654823830269831548864532234524167041738653088756995021332000796302009082430679017203467931275812640318708500107087985069586794558807846317536051200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 59 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 63 1 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 52 (.close 5)) (.step 3 (.step 12 (.step 21 (.close 5))))) (.step 3 (.step 31 (.close 23)))) (.step 9 (.step 53 (.step 40 (.close 52))))) (.step 31 (.close 52))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 34 (.step 55 (.close 3)))) (.step 9 (.step 34 (.step 55 (.step 3 (.step 15 (.step 18 (.close 12)))))))) (.step 18 (.step 3 (.close 12)))) (.step 3 (.step 34 (.step 40 (.close 5))))) (.step 12 (.close 3))) (.step 12 (.step 27 (.step 34 (.step 61 (.step 40 (.close 3))))))) (.step 3 (.step 31 (.close 5)))) (.step 58 (.close 52))) (.step 57 (.close 52))) (.step 12 (.step 27 (.step 34 (.step 44 (.step 55 (.step 61 (.split 54 1 (.step 23 (.step 52 (.close 18))) (.step 23 (.close 3)))))))))) (.step 9 (.step 26 (.step 40 (.step 57 (.step 75 (.step 12 (.close 31)))))))) (.step 12 (.step 55 (.step 23 (.close 74))))) (.step 3 (.close 7))) (.step 12 (.step 48 (.step 55 (.step 23 (.step 32 (.close 67))))))) (.step 26 (.step 44 (.step 55 (.step 52 (.step 18 (.close 31))))))) (.step 3 (.close 54))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197074286134067472126418660977565275490347534184361762920091618893727582398073690024382487596273604249397942222821854846792929536638976⟩
def references : Fin 4 → Box := ![Part8.root, Part10.root, Part11.root, Part12.root]
def proof : Chunks.Proof 4 := (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.reuse 0) (.run (.step 61 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.step 58 (.step 18 (.split 74 1 (.step 48 (.step 31 (.step 58 (.step 3 (.step 27 (.close 61)))))) (.step 58 (.step 61 (.step 69 (.step 48 (.close 12)))))))) (.step 31 (.step 40 (.close 75)))) (.step 18 (.step 58 (.step 74 (.split 72 1 (.split 14 0 (.split 12 0 (.step 58 (.close 31)) (.step 31 (.step 48 (.close 34)))) (.step 36 (.step 49 (.close 58)))) (.step 31 (.step 40 (.step 48 (.close 32))))))))) (.step 3 (.close 58))) (.step 32 (.step 67 (.split 72 1 (.step 58 (.close 67)) (.step 31 (.step 40 (.close 48))))))) (.step 12 (.step 66 (.split 72 1 (.split 12 0 (.step 58 (.close 31)) (.step 31 (.step 34 (.close 15)))) (.step 31 (.step 40 (.close 75))))))) (.step 58 (.close 62)))))) (.reuse 1)) (.run (.step 51 (.step 57 (.split 56 1 (.split 67 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 55 1 (.split 58 1 (.split 59 1 (.split 63 1 (.step 3 (.step 18 (.step 3 (.close 7)))) (.step 18 (.close 51))) (.step 3 (.close 7))) (.step 3 (.close 51))) (.step 3 (.close 18))) (.step 3 (.close 22))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 54))) (.step 3 (.close 18))))))) (.step 3 (.step 32 (.step 57 (.step 58 (.split 51 1 (.split 59 1 (.reuse 2) (.run (.step 26 (.step 44 (.step 55 (.step 53 (.close 31))))))) (.run (.step 3 (.close 54))))))))) (.step 3 (.step 58 (.step 61 (.split 50 1 (.reuse 3) (.run (.step 55 (.step 52 (.step 31 (.step 53 (.step 21 (.close 23))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831374585610514237203076900558771356552336808219366679757403847334624378735146227425083741408310752373858369271884208406528⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 9 (.step 10 (.step 27 (.step 47 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 55 1 (.split 63 1 (.step 3 (.step 18 (.step 3 (.close 7)))) (.step 11 (.step 3 (.close 9)))) (.step 3 (.close 8))) (.step 3 (.close 7))) (.step 3 (.close 46))) (.step 3 (.close 46))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 3 (.step 46 (.close 52)))))))))) (.run (.step 44 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.step 31 (.close 7)) (.step 31 (.close 12))) (.step 31 (.close 40))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.close 12))) (.step 31 (.step 3 (.close 45)))) (.step 31 (.close 40))) (.step 31 (.close 53))) (.step 31 (.close 52))))))) (.run (.step 31 (.step 43 (.step 68 (.step 58 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.step 43 (.split 64 1 (.split 71 1 (.step 3 (.split 74 1 (.step 43 (.step 3 (.step 18 (.close 23)))) (.step 5 (.step 18 (.step 31 (.close 12)))))) (.step 31 (.step 43 (.close 74)))) (.step 31 (.step 24 (.close 67))))) (.step 12 (.step 31 (.step 66 (.close 43))))) (.step 3 (.step 23 (.step 5 (.step 31 (.close 12)))))) (.step 5 (.step 31 (.step 61 (.close 43))))) (.step 31 (.step 43 (.step 3 (.step 5 (.close 57)))))) (.step 3 (.step 31 (.step 5 (.close 53))))) (.step 3 (.step 31 (.step 52 (.step 5 (.close 52))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350752809766951994801222262167450756473574410477913331324779238040477880601799311673740171637460433025350973872632458614058321407932627109941140362030095385017860825356001098377753382720390934591509566358761779400960638976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 42 1 (.split 51 1 (.split 58 1 (.split 55 1 (.split 56 1 (.split 72 1 (.split 2 0 (.split 12 0 (.split 67 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 34 0 (.step 42 (.step 32 (.step 3 (.close 5)))) (.step 3 (.close 40))) (.step 18 (.close 42))) (.step 18 (.close 42))) (.step 18 (.close 42))) (.step 34 (.step 42 (.close 3)))) (.step 18 (.step 31 (.step 3 (.close 42))))) (.step 3 (.close 12))) (.step 3 (.split 10 0 (.step 34 (.step 42 (.step 21 (.step 18 (.step 9 (.step 12 (.step 3 (.close 31)))))))) (.step 3 (.close 12))))) (.step 3 (.step 27 (.split 10 0 (.split 12 0 (.split 21 0 (.split 51 0 (.step 40 (.close 42)) (.step 3 (.close 5))) (.step 3 (.close 18))) (.step 3 (.step 5 (.close 42)))) (.step 3 (.close 5)))))) (.step 40 (.close 3))) (.step 5 (.close 42))) (.step 32 (.step 40 (.step 42 (.step 5 (.close 3)))))) (.step 42 (.close 31))) (.step 3 (.close 42))) (.step 31 (.close 40))) (.step 42 (.step 40 (.close 77)))) (.step 11 (.step 32 (.step 36 (.step 40 (.step 55 (.step 58 (.step 61 (.step 77 (.split 2 0 (.step 67 (.split 34 0 (.step 61 (.step 42 (.step 74 (.step 18 (.close 23))))) (.step 17 (.step 18 (.close 40))))) (.step 40 (.close 74)))))))))))) (.step 3 (.step 5 (.step 42 (.close 5))))) (.step 32 (.step 42 (.step 58 (.step 67 (.split 34 0 (.split 36 0 (.split 42 0 (.step 42 (.close 15)) (.step 40 (.close 42))) (.step 21 (.close 67))) (.step 17 (.step 18 (.close 67))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379629067307375696416072275904174934903858425993299334577344716180122187532979068042002434391377643060392520266967678976⟩
def references : Fin 2 → Box := ![Part14.root, Part15.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.reuse 0) (.step 40 (.step 58 (.step 27 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.reuse 1) (.run (.step 11 (.step 12 (.step 32 (.step 34 (.step 40 (.step 55 (.step 58 (.step 67 (.step 74 (.step 77 (.split 65 1 (.split 2 0 (.split 36 0 (.step 61 (.step 67 (.split 42 0 (.step 42 (.step 18 (.close 55))) (.step 18 (.close 40))))) (.step 40 (.close 42))) (.step 23 (.step 40 (.close 42)))) (.step 3 (.step 18 (.close 42)))))))))))))))) (.run (.step 3 (.step 27 (.step 42 (.step 44 (.step 32 (.step 40 (.step 55 (.close 5)))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 23 (.step 32 (.step 36 (.step 40 (.step 61 (.step 62 (.split 55 1 (.split 2 0 (.split 21 0 (.split 22 0 (.step 9 (.split 10 0 (.split 34 0 (.step 61 (.step 40 (.close 42))) (.step 3 (.close 40))) (.step 3 (.step 4 (.close 12))))) (.step 3 (.close 42))) (.step 3 (.step 4 (.close 23)))) (.step 5 (.close 57))) (.step 4 (.step 5 (.step 40 (.close 12)))))))))))))))) (.run (.step 21 (.step 32 (.step 42 (.close 3)))))) (.run (.step 27 (.step 42 (.step 52 (.step 40 (.step 52 (.step 12 (.close 55))))))))) (.run (.step 3 (.step 5 (.step 24 (.step 27 (.step 42 (.step 31 (.step 24 (.step 42 (.close 23)))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 17350758325419215096788520990895667098404201320045581416675836976144863078441439106753869965585145329983409466527956798376185113819903750898637262528238303911508556705319863791390915769581585514508176565147148329520490086400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 59 1 (.split 63 1 (.step 43 (.split 64 1 (.split 65 1 (.split 71 1 (.step 3 (.split 72 1 (.split 74 1 (.step 21 (.split 58 1 (.split 12 0 (.split 14 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 31 (.step 5 (.close 58))) (.step 31 (.close 3))) (.step 3 (.close 31))) (.step 3 (.step 5 (.close 31)))) (.step 5 (.close 31))) (.step 3 (.step 18 (.close 31)))) (.step 5 (.step 18 (.close 31)))) (.step 3 (.close 31))) (.step 5 (.step 18 (.close 31)))) (.step 31 (.step 3 (.close 5)))) (.step 5 (.close 42)))) (.step 5 (.step 18 (.close 42)))) (.step 31 (.step 3 (.close 38))))) (.step 31 (.step 42 (.close 74)))) (.step 43 (.step 31 (.close 68)))) (.step 31 (.step 58 (.close 67))))) (.step 31 (.step 58 (.step 63 (.step 66 (.close 5)))))) (.step 3 (.step 21 (.step 31 (.close 5)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562847330891521477239966414049162735015459507855994849458212300191264923243558078061586901671617158501530337280⟩
def references : Fin 2 → Box := ![Part16.root, Part17.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.reuse 0) (.step 43 (.split 39 1 (.split 42 1 (.split 49 1 (.split 54 1 (.split 56 1 (.reuse 1) (.run (.step 21 (.step 43 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 72 1 (.split 12 0 (.split 14 0 (.step 28 (.split 21 0 (.split 49 0 (.step 41 (.close 31)) (.step 21 (.step 3 (.close 59)))) (.step 21 (.close 59)))) (.step 18 (.step 5 (.close 31)))) (.step 31 (.close 58))) (.step 31 (.close 41))) (.step 5 (.close 3))) (.step 3 (.close 4))) (.step 3 (.close 58))) (.step 3 (.close 4))) (.step 22 (.step 31 (.step 41 (.step 5 (.close 41)))))) (.step 18 (.step 22 (.step 41 (.close 3))))) (.step 41 (.close 67))) (.step 31 (.step 41 (.step 63 (.step 66 (.step 5 (.close 41))))))))))) (.run (.step 31 (.step 43 (.step 48 (.step 5 (.close 57))))))) (.run (.step 3 (.step 21 (.step 31 (.step 42 (.step 16 (.close 58)))))))) (.run (.step 31 (.step 28 (.close 45))))) (.run (.step 31 (.step 41 (.step 42 (.close 58)))))))) (.run (.step 7 (.step 36 (.step 57 (.step 74 (.step 75 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 74 1 (.split 39 1 (.step 31 (.close 7)) (.step 31 (.close 36))) (.step 31 (.close 36))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 22 (.step 31 (.close 12)))) (.step 31 (.close 39))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 39))) (.step 31 (.step 28 (.close 39)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350758320032835933598087636165669219771963874226972450653466677994476360275344220108725521721376356149655113430763748136424091719281743696070995611077743877727076612216689781830424047251469228885051421779689678440288485376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 74 1 (.step 21 (.split 39 1 (.step 75 (.split 51 1 (.step 29 (.split 54 1 (.split 67 1 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 55 0 (.step 38 (.step 32 (.close 38))) (.step 31 (.step 32 (.close 23)))) (.step 21 (.step 18 (.step 31 (.close 55))))) (.step 21 (.close 38))) (.step 38 (.close 55))) (.step 40 (.close 38))) (.step 21 (.step 31 (.close 23)))) (.step 40 (.step 38 (.close 74)))) (.step 38 (.step 18 (.close 32)))) (.step 40 (.step 66 (.step 38 (.step 32 (.step 38 (.close 18))))))) (.step 21 (.step 38 (.step 23 (.step 12 (.step 3 (.close 15))))))) (.step 66 (.split 64 1 (.split 71 1 (.step 3 (.step 31 (.close 38))) (.step 31 (.step 12 (.close 23)))) (.step 21 (.step 31 (.close 38)))))) (.step 31 (.step 32 (.step 38 (.close 3))))) (.step 3 (.close 38))) (.step 57 (.close 38)))) (.step 3 (.close 38)))) (.step 32 (.close 3)))) (.step 32 (.step 40 (.step 66 (.step 67 (.step 69 (.step 23 (.step 74 (.step 38 (.close 3)))))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 40 (.step 38 (.step 55 (.close 3))))))))) (.step 21 (.step 32 (.step 40 (.step 27 (.close 61)))))) (.step 31 (.step 3 (.close 38)))) (.step 31 (.step 32 (.step 40 (.step 38 (.close 58)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562851922368242941742672128758506872498766548606082936811861781956253771518166278290233695070005038708484472832⟩
def references : Fin 2 → Box := ![Part18.root, Part19.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.step 3 (.step 9 (.step 31 (.step 57 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.reuse 1) (.run (.step 3 (.step 9 (.step 21 (.step 32 (.step 52 (.step 57 (.step 58 (.step 61 (.split 58 1 (.step 40 (.split 59 1 (.step 38 (.close 52)) (.step 26 (.step 38 (.close 52))))) (.step 32 (.close 40))))))))))))) (.run (.step 31 (.close 45)))) (.run (.step 3 (.step 31 (.close 38))))) (.run (.step 31 (.close 39)))))))))))) (.run (.step 34 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.split 64 1 (.step 7 (.split 71 1 (.split 74 1 (.step 40 (.step 31 (.close 37))) (.step 31 (.close 34))) (.step 31 (.close 74)))) (.step 31 (.close 67)))) (.step 15 (.step 31 (.close 21)))) (.step 31 (.close 34))) (.step 31 (.close 53))) (.step 31 (.close 52)))))) (.run (.step 18 (.step 31 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 18 (.step 31 (.split 63 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 31)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562851922368242941742672128758506872498766551979367279320334168373940595760734813504842219618843758573132972032⟩
def references : Fin 1 → Box := ![Part20.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 26 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.step 18 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.split 72 1 (.step 18 (.close 7)) (.step 18 (.close 23))) (.step 18 (.close 74))))) (.step 18 (.close 66))) (.step 3 (.step 18 (.close 12)))) (.step 18 (.close 23))) (.step 18 (.close 53))) (.step 18 (.close 52)))) (.step 3 (.close 18))) (.step 18 (.close 42))) (.step 5 (.close 18))) (.step 18 (.step 66 (.step 38 (.close 67)))))))) (.run (.step 18 (.step 43 (.step 68 (.split 35 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.step 31 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.split 71 1 (.split 72 1 (.step 24 (.step 18 (.step 43 (.step 3 (.step 24 (.step 4 (.step 18 (.close 15)))))))) (.step 4 (.step 18 (.step 24 (.close 15))))) (.step 18 (.step 24 (.close 74))))) (.step 18 (.step 24 (.close 67)))) (.step 18 (.step 66 (.close 24)))) (.step 3 (.step 18 (.close 24)))) (.step 18 (.step 3 (.close 61)))) (.step 43 (.step 18 (.close 63))))) (.step 18 (.step 4 (.close 5)))) (.step 4 (.step 24 (.step 57 (.close 24))))) (.step 3 (.step 18 (.step 48 (.close 53))))) (.step 3 (.step 18 (.step 48 (.close 52))))) (.step 5 (.step 18 (.step 42 (.close 3))))) (.step 21 (.step 31 (.step 41 (.step 43 (.step 4 (.step 18 (.close 63)))))))) (.step 18 (.step 21 (.step 31 (.close 38))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758320032835933598087636165669219771963866114535274784024001855385538770318038126816820264843153785972279317030943687079069236099968539651807649479982485196582622048388120734312842787822999340282917096629406396008366080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.step 27 (.split 36 1 (.split 42 1 (.split 49 1 (.split 51 1 (.split 55 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 2 (.split 16 0 (.split 17 0 (.split 22 0 (.step 23 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 34 (.step 40 (.step 23 (.close 3)))) (.step 23 (.close 17))) (.step 23 (.close 31))) (.step 3 (.step 17 (.step 5 (.close 17))))) (.step 18 (.close 17)))) (.step 18 (.close 17))) (.step 11 (.step 18 (.close 17)))) (.step 18 (.step 17 (.close 3)))) (.step 11 (.split 35 0 (.split 36 0 (.split 38 0 (.step 17 (.close 23)) (.step 18 (.step 17 (.close 5)))) (.step 17 (.close 31))) (.step 17 (.step 23 (.close 5)))))) (.step 23 (.split 14 2 (.split 16 0 (.step 12 (.close 23)) (.step 3 (.close 17))) (.step 17 (.close 3))))) (.step 18 (.step 3 (.close 17)))) (.step 23 (.step 17 (.close 5)))) (.step 11 (.step 17 (.close 3)))) (.step 74 (.close 17))) (.step 3 (.close 17))) (.step 67 (.close 17))) (.step 12 (.step 34 (.step 17 (.close 66))))) (.step 12 (.step 18 (.step 17 (.step 34 (.step 58 (.close 17))))))) (.step 3 (.close 51))) (.step 3 (.step 27 (.step 23 (.close 34))))) (.step 31 (.close 17))) (.step 31 (.close 17)))) (.step 31 (.close 17))) (.step 3 (.close 18))) (.step 66 (.step 67 (.step 69 (.step 40 (.step 74 (.step 75 (.step 3 (.close 17))))))))) (.step 3 (.step 18 (.step 17 (.close 34))))))
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
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562851922368242941742672128758506872498766551979367279320337164452299911704866947386641979963818134280034320384⟩
def references : Fin 1 → Box := ![Part22.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 18 (.step 31 (.step 34 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 50 1 (.split 54 1 (.step 58 (.split 56 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 27 (.step 34 (.step 44 (.step 55 (.step 23 (.step 17 (.close 3)))))))))) (.run (.step 36 (.step 40 (.step 44 (.step 61 (.step 17 (.close 3)))))))) (.run (.step 31 (.step 5 (.close 17)))))) (.run (.step 23 (.step 9 (.step 31 (.step 34 (.step 40 (.close 57)))))))) (.run (.step 3 (.step 17 (.step 27 (.step 32 (.step 34 (.step 48 (.step 53 (.step 23 (.step 55 (.step 61 (.split 54 1 (.split 71 1 (.split 74 1 (.split 14 2 (.split 16 0 (.step 55 (.close 53)) (.step 3 (.close 17))) (.step 23 (.step 17 (.close 3)))) (.step 17 (.close 23))) (.step 17 (.close 53))) (.step 12 (.step 21 (.step 23 (.close 3))))))))))))))))) (.run (.step 5 (.step 23 (.step 31 (.close 17)))))) (.run (.step 23 (.step 34 (.step 36 (.step 40 (.step 42 (.step 17 (.close 5))))))))) (.run (.step 31 (.step 5 (.close 17))))) (.run (.step 17 (.step 31 (.step 32 (.step 40 (.step 57 (.step 66 (.step 67 (.step 74 (.split 54 1 (.split 58 1 (.step 75 (.split 2 0 (.split 12 0 (.split 34 0 (.step 23 (.step 77 (.step 40 (.step 38 (.close 17))))) (.step 5 (.step 17 (.close 31)))) (.step 12 (.close 23))) (.step 5 (.close 17)))) (.step 17 (.close 38))) (.step 12 (.step 23 (.close 31)))))))))))))) (.run (.step 17 (.step 18 (.close 3))))) (.run (.step 18 (.step 3 (.close 17))))) (.run (.step 18 (.step 3 (.close 19))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2658455991569831745807614123781914624, 11567177727212027336665677129878029776979793501849579361393287618789583452599871711041287171866501659693872681719021850754497160368789142836145112686434715181192542945383538185166447644299945271646748882894795936800502185984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 54 1 (.step 3 (.split 74 1 (.split 2 0 (.split 10 0 (.split 12 2 (.split 14 0 (.split 21 0 (.split 16 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 17 0 (.step 9 (.step 12 (.step 40 (.step 15 (.close 3))))) (.step 3 (.close 23))) (.step 12 (.step 21 (.step 3 (.close 5))))) (.step 22 (.step 15 (.close 5)))) (.step 21 (.step 15 (.close 31)))) (.step 31 (.close 15))) (.step 3 (.step 15 (.step 12 (.step 15 (.close 31)))))) (.step 18 (.step 21 (.step 3 (.close 15))))) (.step 18 (.step 15 (.close 3)))) (.step 40 (.split 16 0 (.split 17 0 (.step 15 (.close 3)) (.step 3 (.close 12))) (.step 3 (.close 17))))) (.split 38 0 (.split 39 0 (.split 55 0 (.step 15 (.close 3)) (.step 12 (.step 18 (.close 15)))) (.step 21 (.step 15 (.close 3)))) (.step 15 (.close 31)))) (.step 3 (.step 12 (.close 3)))) (.step 3 (.step 12 (.step 31 (.split 35 0 (.step 58 (.close 15)) (.step 15 (.close 5))))))) (.step 23 (.close 15)))) (.step 15 (.close 18))) (.step 15 (.close 31))) (.step 15 (.close 31))) (.step 15 (.close 31))) (.step 18 (.close 15))) (.step 18 (.close 15))) (.step 18 (.close 15))) (.step 15 (.step 26 (.step 31 (.step 23 (.close 75)))))))
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
def root : Box := ⟨2658455991569831745807614123781914624, 17350758325419215096788520990895667098404201320045581416668473154045954768055273601532205810452170723767640495004539362019762879199981766840662020295633991598483292484993508046491371521163218872029834295306132485740933677056⟩
def references : Fin 1 → Box := ![Part24.root]
def proof : Chunks.Proof 1 := (.step 23 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.reuse 0) (.run (.step 12 (.step 22 (.step 23 (.step 29 (.step 31 (.step 55 (.step 57 (.step 75 (.split 2 0 (.step 66 (.split 30 0 (.split 38 0 (.split 22 0 (.step 57 (.step 40 (.step 15 (.close 55)))) (.step 23 (.close 15))) (.step 31 (.close 15))) (.step 23 (.step 15 (.close 31))))) (.step 23 (.close 74))))))))))))) (.run (.step 3 (.step 15 (.close 31))))) (.run (.step 12 (.step 21 (.step 23 (.step 29 (.step 31 (.step 32 (.step 55 (.step 68 (.step 74 (.step 75 (.split 65 1 (.split 2 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 40 0 (.step 15 (.close 55)) (.step 23 (.close 15))) (.step 15 (.close 23))) (.step 23 (.close 15))) (.step 22 (.step 15 (.close 4)))) (.step 23 (.close 15))) (.step 3 (.close 15))))))))))))))) (.run (.step 12 (.step 15 (.step 31 (.step 66 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.split 40 0 (.step 15 (.close 21)) (.step 15 (.close 5))) (.step 15 (.close 5))) (.step 23 (.close 15))) (.step 23 (.close 15))) (.step 21 (.step 18 (.close 15)))) (.step 15 (.close 23))))))))) (.run (.step 3 (.step 9 (.step 15 (.step 18 (.step 15 (.step 26 (.step 12 (.step 23 (.close 55))))))))))) (.run (.step 3 (.step 12 (.step 22 (.step 23 (.step 34 (.step 40 (.step 62 (.split 2 0 (.split 16 0 (.step 9 (.step 57 (.split 21 0 (.step 40 (.step 61 (.close 3))) (.step 3 (.close 23))))) (.step 3 (.step 4 (.step 15 (.close 18))))) (.step 3 (.step 5 (.close 15))))))))))))))
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
def root : Box := ⟨2658455991569831745807614123781914624, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562851922368242941742672128758506872498766551979367279320337164452299911707525403378211811709625748400595009536⟩
def references : Fin 1 → Box := ![Part25.root]
def proof : Chunks.Proof 1 := (.step 18 (.step 31 (.split 14 1 (.split 21 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.step 5 (.step 22 (.step 15 (.step 31 (.step 3 (.step 12 (.step 5 (.close 48)))))))))) (.run (.step 3 (.step 12 (.step 31 (.step 48 (.step 9 (.step 15 (.step 58 (.step 15 (.step 5 (.step 15 (.close 61))))))))))))) (.run (.step 21 (.step 22 (.step 15 (.step 23 (.step 26 (.close 53)))))))) (.run (.step 12 (.step 15 (.step 26 (.close 52)))))) (.run (.step 31 (.step 9 (.step 15 (.step 43 (.close 15))))))) (.run (.step 3 (.step 12 (.step 21 (.step 23 (.step 32 (.step 34 (.step 40 (.step 58 (.step 61 (.step 62 (.split 55 1 (.step 57 (.split 2 0 (.split 17 0 (.step 9 (.split 21 0 (.split 22 0 (.split 51 0 (.step 40 (.close 43)) (.step 3 (.close 15))) (.step 3 (.close 23))) (.step 3 (.close 23)))) (.step 3 (.close 23))) (.step 3 (.step 5 (.close 15))))) (.step 4 (.step 5 (.step 15 (.close 22))))))))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 21 (.step 31 (.step 12 (.step 43 (.step 15 (.step 41 (.step 3 (.step 43 (.close 41)))))))))))))) (.run (.step 15 (.step 31 (.step 38 (.step 18 (.close 40))))))) (.run (.step 4 (.step 9 (.step 24 (.step 15 (.close 24))))))) (.run (.step 12 (.step 3 (.close 17)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562851922368242941742672128758506872498766551979367279320337164452299911707525403378211811709625748400595009536⟩
def references : Fin 3 → Box := ![Part21.root, Part23.root, Part26.root]
def proof : Chunks.Proof 3 := (.split 12 1 (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 22 (.step 74 (.split 22 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.step 18 (.step 61 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.step 7 (.step 67 (.split 72 1 (.step 23 (.step 18 (.close 7))) (.step 18 (.close 22))))) (.step 18 (.close 66))) (.step 18 (.close 22))) (.step 18 (.close 53))) (.step 18 (.close 52))))) (.step 3 (.close 18))) (.step 18 (.close 42))) (.step 5 (.close 18))) (.step 18 (.step 38 (.close 66)))) (.step 18 (.close 20)))))))) (.run (.step 7 (.step 21 (.split 17 1 (.split 22 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.split 72 1 (.step 18 (.close 7)) (.step 18 (.close 15))) (.step 18 (.close 21))))) (.step 18 (.close 66)))) (.step 3 (.step 18 (.close 12)))) (.step 18 (.close 21))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 3 (.close 18))) (.step 18 (.close 42))) (.step 5 (.close 18))) (.step 18 (.step 38 (.close 66)))) (.step 18 (.close 19))) (.step 18 (.close 19))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes
  · exact Part23.excludes
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨3223322624, 17350758325419215096778723224274352413530305619242778145011039050304276829741923911077788412990373290146950260988954915383286172056604520444060148404603884508357974770573365574192348392448528002707987482216820228018131697664⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 56 1 (.split 58 1 (.step 31 (.step 58 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.step 5 (.step 18 (.split 74 1 (.step 3 (.step 31 (.step 23 (.step 3 (.close 12))))) (.step 5 (.close 77))))) (.step 31 (.step 40 (.close 75)))) (.step 18 (.step 23 (.step 74 (.close 5))))) (.step 3 (.close 5))) (.step 18 (.step 63 (.step 67 (.close 5))))) (.step 63 (.step 66 (.step 75 (.step 5 (.step 66 (.close 18))))))) (.step 3 (.step 23 (.step 5 (.step 26 (.close 62)))))))) (.step 5 (.step 61 (.step 18 (.step 43 (.step 12 (.close 66))))))) (.step 5 (.step 31 (.step 5 (.close 66))))) (.step 3 (.step 23 (.step 31 (.step 57 (.split 72 1 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 5 (.close 15)) (.step 5 (.close 23))) (.step 5 (.close 23))) (.step 5 (.close 15))) (.step 5 (.close 23))) (.step 23 (.step 5 (.close 57))))))))) (.step 3 (.step 23 (.step 32 (.step 40 (.step 53 (.step 5 (.step 53 (.step 5 (.step 57 (.step 23 (.step 5 (.close 23))))))))))))) (.step 3 (.step 5 (.step 12 (.step 23 (.step 34 (.step 40 (.step 52 (.step 53 (.step 5 (.step 52 (.step 5 (.step 57 (.step 23 (.step 5 (.close 61)))))))))))))))) (.step 5 (.step 42 (.step 18 (.step 43 (.step 12 (.close 66))))))) (.step 5 (.step 18 (.step 31 (.step 5 (.close 66)))))) (.step 31 (.step 32 (.step 40 (.step 5 (.step 38 (.close 5))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581424223769024050017052045154106623067197079836888831379633992562851922368242941742672128758506872498766551979367279320337164452299911707525405913513012166084551394003517440⟩
def references : Fin 2 → Box := ![Part27.root, Part28.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 10 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 12 1 (.split 14 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 18 (.step 31 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 17))) (.step 3 (.close 31))))))) (.step 3 (.step 18 (.step 43 (.step 58 (.split 12 1 (.split 14 1 (.split 21 1 (.reuse 1) (.run (.step 3 (.step 5 (.close 18))))) (.run (.step 5 (.step 23 (.close 17))))) (.run (.step 3 (.step 12 (.step 15 (.step 23 (.step 31 (.split 35 1 (.split 72 1 (.split 36 0 (.split 42 0 (.split 50 0 (.step 5 (.close 15)) (.step 5 (.close 15))) (.step 5 (.close 15))) (.step 5 (.close 15))) (.step 15 (.step 5 (.close 21)))) (.step 15 (.step 23 (.step 5 (.close 26)))))))))))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part29.excludes
end FiveColour.Packed.ProjectedChunks.Case81
