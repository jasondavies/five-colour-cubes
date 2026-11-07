module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case140
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987242992706910916578060275939629940244344429137393208278600838977473509973063206277913910514438694235590743228552606411518839209394670433335643287706105002746981382933391526470877184⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11592891989185068313591, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646221349807102293740064093958240592194881717248, 0⟩]
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
def root : Box := ⟨4294967296, 5783586113859450862119940351690653348640933377273476735325727336923502722666980202958084233981616103375238169584759233140503598002762972046448415812647418914656350817316057889075645388529612029377913514245185725220857577472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 71 1 (.split 10 0 (.split 30 0 (.step 55 (.close 3)) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 55 (.close 3))) (.step 3 (.close 55))) (.step 3 (.close 40))) (.step 31 (.step 3 (.close 55)))) (.step 31 (.step 3 (.close 55)))) (.step 3 (.step 31 (.close 55)))) (.step 3 (.step 31 (.close 23)))) (.step 18 (.step 3 (.step 31 (.close 55))))) (.step 18 (.step 3 (.step 31 (.close 55))))) (.split 71 1 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 43 0 (.step 12 (.split 16 0 (.step 23 (.step 3 (.close 17))) (.step 18 (.close 21)))) (.step 3 (.close 11))) (.step 3 (.step 12 (.step 17 (.step 18 (.close 21)))))) (.step 18 (.close 23))) (.step 3 (.step 12 (.step 18 (.close 23))))) (.step 40 (.split 36 0 (.split 42 0 (.split 43 0 (.step 12 (.step 23 (.close 18))) (.step 3 (.close 9))) (.step 3 (.close 23))) (.step 3 (.close 40))))) (.step 3 (.step 23 (.close 17)))) (.step 12 (.split 34 0 (.split 36 0 (.step 11 (.step 74 (.close 55))) (.step 18 (.close 36))) (.step 18 (.close 74))))))))
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
def root : Box := ⟨1329227995784915872903807064575311872, 5783586113859450862119940351695220244766971219167136111200573819939146269169675358459745526251230860709005008896308967914788286116848615238762122631247445458693503135339080318408124607811475625171707054146295640224325173248⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 31 (.split 63 1 (.split 64 1 (.step 3 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.step 12 (.step 9 (.split 51 0 (.split 65 0 (.split 67 0 (.split 71 1 (.step 23 (.step 55 (.close 31))) (.step 57 (.close 55))) (.step 3 (.step 23 (.step 15 (.step 3 (.close 55)))))) (.step 31 (.close 55))) (.step 22 (.step 3 (.close 21)))))) (.step 9 (.step 12 (.step 31 (.close 15))))) (.step 3 (.step 12 (.step 23 (.close 15))))) (.step 3 (.step 12 (.step 23 (.close 31))))) (.step 3 (.step 22 (.close 23)))) (.step 18 (.step 21 (.step 3 (.close 15))))) (.step 12 (.split 10 0 (.split 16 0 (.split 17 0 (.step 15 (.step 9 (.step 12 (.close 3)))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 12)))))) (.step 12 (.step 32 (.step 3 (.step 74 (.split 16 0 (.step 21 (.step 66 (.step 3 (.close 67)))) (.step 18 (.close 21)))))))) (.step 12 (.step 55 (.step 66 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 15 (.step 55 (.close 21))) (.step 23 (.close 15))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 18 (.close 66)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4294967296, 5783586113859450862119940351695220244766971219167136111200573819939146269169675358459745526251230860709005008896308967914788286116848615238762122631247445458693503135339080318408124607811475625171707054146295640224325173248⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 12 0 (.split 43 1 (.split 51 1 (.split 63 1 (.step 18 (.split 64 1 (.reuse 0) (.run (.step 69 (.split 14 0 (.split 21 0 (.split 34 0 (.split 36 0 (.split 39 0 (.step 74 (.split 40 0 (.split 16 0 (.step 32 (.step 55 (.close 3))) (.step 18 (.close 21))) (.step 18 (.close 23)))) (.step 32 (.step 67 (.close 3)))) (.step 31 (.close 67))) (.step 31 (.close 67))) (.step 18 (.close 67))) (.step 12 (.step 32 (.step 67 (.split 34 0 (.step 11 (.step 67 (.close 18))) (.step 3 (.close 67))))))))))) (.run (.step 32 (.step 69 (.split 14 0 (.split 16 0 (.split 17 0 (.split 64 1 (.split 21 0 (.split 22 0 (.step 12 (.step 74 (.split 34 0 (.split 35 0 (.step 55 (.close 31)) (.step 32 (.close 55))) (.step 31 (.close 15))))) (.step 3 (.close 66))) (.step 18 (.close 66))) (.step 66 (.close 3))) (.step 51 (.step 18 (.close 66)))) (.step 66 (.step 18 (.close 66)))) (.step 12 (.close 3))))))) (.run (.step 3 (.close 51)))) (.run (.step 3 (.close 47)))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339638752275966864533871615339449948297310482795445109463838313991671221688144242715614745231751068233622939580212035730387653344299110520798085698549037261539711822541490512042393600⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 72 1 (.split 74 1 (.reuse 0) (.run (.step 18 (.step 27 (.split 51 1 (.split 67 1 (.step 11 (.split 10 0 (.split 14 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 40 0 (.split 42 0 (.split 35 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 77 (.step 66 (.close 77))) (.step 18 (.close 55))) (.step 23 (.step 32 (.close 77)))) (.step 12 (.step 23 (.step 44 (.close 55))))) (.step 23 (.close 77))) (.step 18 (.step 23 (.close 74)))) (.step 18 (.close 40))) (.step 32 (.step 67 (.step 77 (.close 23))))) (.step 18 (.step 23 (.step 40 (.close 74))))) (.step 23 (.step 66 (.close 77)))) (.step 17 (.step 77 (.close 74)))) (.step 18 (.step 12 (.close 77))))) (.step 3 (.close 69))) (.step 3 (.close 51))))))) (.run (.step 9 (.step 31 (.step 69 (.split 51 1 (.split 67 1 (.step 29 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 75 (.step 67 (.close 75))) (.step 31 (.step 40 (.close 75)))) (.step 32 (.close 75))) (.step 26 (.step 12 (.step 40 (.step 3 (.step 21 (.close 55))))))) (.step 31 (.step 23 (.close 21)))) (.step 40 (.close 75))) (.step 31 (.step 38 (.step 23 (.step 18 (.close 40)))))) (.step 12 (.step 40 (.step 67 (.close 75))))) (.step 26 (.step 66 (.split 16 0 (.split 17 0 (.step 12 (.step 75 (.close 23))) (.step 22 (.step 12 (.close 75)))) (.step 21 (.step 3 (.close 23))))))) (.step 31 (.step 12 (.close 75))))) (.step 3 (.close 69))) (.step 3 (.close 51))))))))
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
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416713053339648, 11567172216946143397859013989258505539824339642808494551023448230207580794670511227058949570369338012904625791145202635989838236338420728472619560768982023422395072818706685673151517929166305980932587665654892553750708224000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 32 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 27 (.step 61 (.split 42 0 (.step 55 (.close 3)) (.step 3 (.close 23))))) (.step 3 (.close 40))) (.step 3 (.close 40))) (.step 3 (.close 61))) (.step 18 (.close 61))) (.step 18 (.close 61))) (.step 18 (.close 61))) (.step 12 (.step 34 (.step 22 (.step 61 (.step 3 (.close 18))))))) (.step 44 (.step 61 (.close 40)))) (.step 40 (.close 61))) (.step 36 (.step 40 (.step 61 (.split 34 0 (.split 42 0 (.step 61 (.close 3)) (.step 18 (.close 40))) (.step 18 (.close 40))))))) (.step 3 (.close 55))) (.step 11 (.step 32 (.step 40 (.step 51 (.step 55 (.step 67 (.step 61 (.step 23 (.step 40 (.close 3))))))))))) (.step 11 (.step 34 (.step 40 (.step 51 (.step 55 (.step 66 (.step 61 (.step 40 (.close 3)))))))))) (.step 27 (.step 44 (.step 55 (.step 61 (.step 40 (.close 3))))))))))
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
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384266463182848, 11567172216946143397859013989258505539824339642808494551023451829338616429227617475489755719154825108662320432678509116594296325808485265662915816001530906535080792755435192489867616495779150376372338872467037245881792331776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 9 (.step 12 (.step 32 (.split 51 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.step 57 (.split 22 0 (.step 57 (.step 55 (.split 39 0 (.step 31 (.close 12)) (.step 21 (.close 31))))) (.step 3 (.close 23))))) (.step 3 (.step 22 (.step 23 (.close 3))))) (.step 18 (.step 21 (.close 57)))) (.step 12 (.step 23 (.step 9 (.step 40 (.close 57)))))) (.step 23 (.close 3))) (.step 26 (.step 57 (.close 23)))) (.step 22 (.step 23 (.step 57 (.split 16 0 (.split 22 0 (.step 57 (.close 3)) (.step 23 (.close 31))) (.step 21 (.close 74))))))) (.step 3 (.close 55))) (.step 23 (.step 29 (.step 32 (.step 51 (.step 55 (.step 67 (.step 57 (.step 23 (.close 3)))))))))) (.step 12 (.step 23 (.step 29 (.step 51 (.step 55 (.step 66 (.step 57 (.step 23 (.close 57)))))))))) (.step 26 (.step 55 (.step 57 (.step 23 (.close 3)))))) (.step 22 (.step 23 (.step 57 (.split 16 0 (.split 22 0 (.step 57 (.close 3)) (.step 3 (.close 23))) (.step 3 (.close 23))))))) (.step 3 (.close 51)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106661350146048, 11567172216946143397859013989258505539824339642808494551023451829338616432501008083385897589168014805489919584895151162637361115291776633759049612406205461418350885081339349640754300623339221385589595418352430299210319921152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 32 (.split 54 1 (.split 58 1 (.split 59 1 (.split 72 1 (.split 74 1 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 55 (.split 36 0 (.step 32 (.step 53 (.close 3))) (.step 3 (.step 21 (.close 55))))) (.step 9 (.step 21 (.close 55)))) (.step 3 (.step 21 (.step 23 (.step 31 (.close 53)))))) (.step 3 (.step 23 (.close 55)))) (.step 3 (.step 18 (.close 55)))) (.step 3 (.step 18 (.close 55)))) (.step 9 (.step 21 (.step 32 (.step 55 (.split 17 0 (.split 21 0 (.split 22 0 (.step 12 (.step 40 (.step 3 (.close 15)))) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 3 (.close 23)))))))) (.step 27 (.step 23 (.step 32 (.step 44 (.step 53 (.step 12 (.close 55)))))))) (.step 21 (.step 26 (.step 32 (.step 40 (.step 55 (.close 3))))))) (.step 53 (.close 55))) (.step 27 (.step 32 (.step 53 (.step 55 (.step 61 (.close 40))))))) (.step 21 (.step 32 (.step 53 (.step 55 (.step 57 (.step 3 (.close 23)))))))))))
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
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339642808494551023451829338616432504204753901421165212949561053227787192237727135450045750256410485705993066756901413354078530876365419221963400807541767434534145448021503363961061376⟩
def references : Fin 4 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 4 := (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 26 (.step 44 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 63 1 (.split 34 0 (.split 36 0 (.step 55 (.step 62 (.close 3))) (.step 3 (.step 23 (.step 22 (.step 26 (.close 55)))))) (.step 3 (.step 31 (.close 55)))) (.step 55 (.close 66))) (.step 3 (.step 18 (.close 55)))) (.step 3 (.step 18 (.close 55)))) (.step 27 (.step 44 (.step 55 (.step 12 (.step 23 (.step 18 (.close 55)))))))) (.step 9 (.step 26 (.split 16 0 (.split 17 0 (.step 12 (.step 55 (.close 31))) (.step 3 (.close 23))) (.step 3 (.close 23))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.run (.step 3 (.step 12 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 72 1 (.split 74 1 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 55 (.step 52 (.close 23))) (.step 12 (.step 32 (.step 40 (.close 52))))) (.step 3 (.step 12 (.step 31 (.close 52))))) (.step 3 (.close 55))) (.step 3 (.close 23))) (.step 3 (.step 18 (.close 55)))) (.step 3 (.step 18 (.close 55)))) (.step 12 (.close 3))) (.step 12 (.step 11 (.step 17 (.step 23 (.step 44 (.step 55 (.close 3)))))))) (.step 12 (.step 26 (.step 40 (.step 52 (.step 32 (.close 55))))))) (.step 52 (.close 55))) (.step 12 (.step 34 (.step 52 (.step 55 (.step 61 (.step 3 (.close 40)))))))) (.step 9 (.step 12 (.step 52 (.step 55 (.step 57 (.close 23))))))) (.step 52 (.close 53)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248387054239744, 11567172216946143397859013989258505539824339642808494551023451829338616432504204753901421165212952268741060723656984860561699771586410662388054877276369444596907484361421145524576201701911185187185344989468653057178341474304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 27 (.step 34 (.step 36 (.step 44 (.split 40 1 (.split 49 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 32 (.split 34 0 (.step 27 (.step 42 (.step 40 (.close 3)))) (.step 3 (.close 40)))) (.step 3 (.close 42))) (.step 18 (.close 42))) (.step 18 (.close 42))) (.step 18 (.close 42))) (.step 12 (.step 32 (.step 34 (.step 21 (.step 3 (.close 23))))))) (.step 42 (.close 77))) (.step 32 (.step 40 (.close 18)))) (.step 11 (.step 32 (.step 36 (.step 67 (.step 74 (.step 23 (.step 40 (.close 3))))))))) (.step 3 (.close 42))) (.step 32 (.step 67 (.split 34 0 (.split 36 0 (.step 42 (.close 15)) (.step 18 (.close 40))) (.step 18 (.close 40)))))) (.step 11 (.step 12 (.step 32 (.step 34 (.step 40 (.step 55 (.step 67 (.step 74 (.step 77 (.step 23 (.step 3 (.close 66))))))))))))) (.step 3 (.step 27 (.step 32 (.step 42 (.step 40 (.close 3))))))) (.step 42 (.close 40))) (.step 3 (.step 21 (.step 23 (.step 32 (.step 36 (.step 40 (.step 27 (.step 61 (.step 57 (.step 23 (.close 43)))))))))))) (.step 3 (.close 42))) (.step 42 (.close 52))) (.step 3 (.step 27 (.step 31 (.step 42 (.close 23))))))))))))
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
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339642808494551023451829338616432504204753901421165212952268741060723656984860561699771586410662388054877276369444596907484361421145524576201701911185187185344989468653057178341474304⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.split 40 1 (.split 34 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.step 31 (.step 44 (.split 49 1 (.split 50 1 (.step 74 (.split 54 1 (.step 31 (.close 40)) (.step 31 (.close 12)))) (.step 21 (.step 31 (.close 12)))) (.step 12 (.step 31 (.close 40)))))))) (.run (.step 31 (.step 36 (.split 49 1 (.split 50 1 (.step 74 (.split 54 1 (.step 31 (.close 36)) (.step 22 (.close 31)))) (.step 21 (.step 22 (.close 31)))) (.step 12 (.step 22 (.step 31 (.close 21))))))))) (.run (.step 31 (.step 34 (.split 49 1 (.split 50 1 (.step 74 (.split 54 1 (.step 31 (.close 34)) (.step 15 (.close 31)))) (.step 15 (.step 21 (.close 31)))) (.step 12 (.close 52))))))) (.run (.step 3 (.step 31 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.step 61 (.step 18 (.split 64 1 (.split 71 1 (.step 23 (.step 3 (.step 23 (.close 3)))) (.step 23 (.close 12))) (.step 31 (.close 67))))) (.step 31 (.close 66))) (.step 3 (.step 31 (.close 12)))) (.step 31 (.close 57))) (.step 31 (.close 53))) (.step 31 (.close 52))))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339642808494551023451829338616432504204753901421165212952268741060723656984862855198387576482173998875772578456385395157470196399184249331729531772788192772474585895991947373003669504⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 35 1 (.reuse 0) (.run (.step 9 (.step 21 (.step 31 (.step 32 (.split 49 1 (.split 51 1 (.split 54 1 (.split 58 1 (.step 75 (.split 59 1 (.split 67 1 (.split 74 1 (.step 29 (.split 12 0 (.split 16 0 (.split 17 0 (.split 14 0 (.split 21 0 (.split 22 0 (.step 32 (.step 38 (.close 55))) (.step 31 (.step 23 (.close 32)))) (.step 31 (.close 23))) (.step 32 (.step 40 (.close 38)))) (.step 31 (.step 23 (.step 18 (.close 74))))) (.step 21 (.step 18 (.step 31 (.step 32 (.close 12)))))) (.step 21 (.step 66 (.split 17 0 (.split 21 0 (.step 38 (.step 12 (.close 38))) (.step 18 (.close 38))) (.step 3 (.step 12 (.close 38)))))))) (.step 23 (.step 32 (.step 40 (.step 38 (.step 12 (.step 18 (.close 31)))))))) (.step 3 (.close 38))) (.step 26 (.step 32 (.step 40 (.step 38 (.close 3))))))) (.step 32 (.step 40 (.close 3)))) (.step 32 (.step 38 (.step 57 (.close 23))))) (.step 3 (.close 38))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 32 (.step 40 (.step 38 (.close 3))))))))))))))) (.run (.step 18 (.step 26 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 74 (.split 58 1 (.step 18 (.close 23)) (.step 18 (.close 12)))) (.step 18 (.close 23))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 23 (.close 32))))))))
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
def root : Box := ⟨2787593149816327892691964784081049483214848, 11567172216946143397859013989258505539824339642808494551023451829338616432504204753901421165212952268741060723656984862855198387576482173998875772578456385395159115700956506953413064158927411610218357201934112715089802952704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.step 27 (.step 34 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 77 (.split 58 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 11 (.split 34 0 (.split 36 0 (.split 35 0 (.split 40 0 (.split 42 0 (.step 12 (.step 17 (.step 23 (.close 55)))) (.step 18 (.step 12 (.close 40)))) (.step 12 (.step 18 (.close 17)))) (.step 12 (.step 23 (.close 17)))) (.step 18 (.step 12 (.step 23 (.step 17 (.close 31)))))) (.step 17 (.step 12 (.step 3 (.step 17 (.close 31))))))) (.step 12 (.step 23 (.step 40 (.step 17 (.step 32 (.step 17 (.close 31)))))))) (.step 3 (.close 17))) (.step 3 (.step 12 (.step 11 (.step 23 (.step 17 (.close 3))))))) (.step 61 (.close 17)))) (.step 12 (.step 23 (.close 3)))) (.step 3 (.close 17))) (.step 3 (.step 12 (.step 27 (.step 32 (.step 34 (.step 23 (.step 17 (.close 3))))))))) (.step 12 (.step 31 (.close 17)))) (.step 23 (.step 31 (.close 17)))) (.step 23 (.step 42 (.close 17)))) (.step 12 (.step 31 (.close 17)))) (.step 12 (.step 31 (.step 32 (.step 40 (.step 74 (.step 17 (.step 23 (.close 26))))))))) (.step 31 (.close 17)))))))
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
def root : Box := ⟨2658455991569831745807614124855656448, 11567172216946143397859013989258505539824339642808494551023451829338616432504204753901421165210179599046939908797406446375316943140794384066145283934544252292482808178219818899704075289721424651821854546398187522610383814656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.step 12 (.step 15 (.split 21 0 (.step 40 (.split 35 0 (.step 55 (.close 3)) (.step 15 (.close 23)))) (.step 15 (.close 3)))))) (.step 3 (.step 12 (.step 18 (.step 15 (.close 3)))))) (.step 3 (.step 12 (.step 18 (.step 15 (.close 3)))))) (.step 12 (.close 3))) (.step 12 (.close 23))) (.step 15 (.close 75))) (.step 12 (.step 22 (.step 29 (.step 66 (.step 74 (.step 23 (.close 15)))))))) (.step 3 (.close 15))) (.step 12 (.step 21 (.step 23 (.step 29 (.step 32 (.step 55 (.step 66 (.step 74 (.step 75 (.step 40 (.step 15 (.close 3))))))))))))) (.step 12 (.step 66 (.split 16 0 (.split 17 0 (.step 15 (.close 21)) (.step 22 (.close 15))) (.step 21 (.step 15 (.close 18))))))) (.step 3 (.step 9 (.step 12 (.step 15 (.step 23 (.close 3))))))) (.step 3 (.step 12 (.step 22 (.step 23 (.step 34 (.step 9 (.step 40 (.step 61 (.step 23 (.close 15))))))))))) (.step 15 (.close 23))) (.step 3 (.close 15))) (.step 15 (.close 53))) (.step 3 (.step 26 (.step 15 (.close 31))))) (.step 12 (.step 15 (.step 31 (.close 3))))) (.step 3 (.step 12 (.step 21 (.step 23 (.step 32 (.step 34 (.step 40 (.step 57 (.step 27 (.step 61 (.step 62 (.step 43 (.step 55 (.step 3 (.step 15 (.close 3))))))))))))))))) (.step 15 (.step 22 (.close 31)))))
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
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339642808494551023451829338616432504204753901421165212952268741060723656984862855198387576482173998875772578456385395159115700956506953413064158928740838214142117807016522150083297280⟩
def references : Fin 3 → Box := ![Part10.root, Part11.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 12 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 43 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.step 57 (.step 31 (.split 64 1 (.split 72 1 (.step 24 (.step 40 (.step 3 (.close 18)))) (.step 18 (.close 75))) (.step 18 (.close 67))))) (.step 18 (.close 66))) (.step 3 (.step 18 (.close 12)))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 31 (.close 38)))))))))) (.run (.step 18 (.step 22 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 74 (.split 58 1 (.step 18 (.close 22)) (.step 18 (.close 12)))) (.step 18 (.close 22))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 22 (.close 32)))))))) (.run (.step 18 (.step 21 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.step 74 (.split 58 1 (.step 18 (.close 21)) (.step 18 (.close 12)))) (.step 18 (.close 21))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.close 38))))))) (.reuse 1)) (.step 9 (.step 22 (.step 26 (.step 32 (.split 21 1 (.split 34 1 (.split 35 1 (.reuse 2) (.run (.step 15 (.close 38)))) (.run (.step 15 (.close 31)))) (.run (.step 18 (.step 15 (.close 24))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4294967296, 11567172216946143397859013998602383924714595450585613999497648462719948415349255491727607441870667811184432011221094300433175014323141624005597118750746852664536012721377957336204158816468825931303964735576742867871127830528⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 65 1 (.reuse 0) (.run (.step 3 (.step 31 (.split 12 1 (.split 14 1 (.split 21 1 (.split 35 1 (.split 39 1 (.split 54 1 (.split 58 1 (.split 72 1 (.split 74 1 (.split 12 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 68 (.step 66 (.step 67 (.close 68)))) (.step 3 (.step 21 (.close 31)))) (.step 3 (.close 31))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 12 (.step 18 (.close 42))))) (.step 3 (.step 31 (.step 21 (.close 66))))) (.step 3 (.step 18 (.step 66 (.step 12 (.step 42 (.close 74))))))) (.step 3 (.step 31 (.step 66 (.step 21 (.close 74)))))) (.step 3 (.step 18 (.step 61 (.close 66))))) (.step 3 (.step 31 (.step 57 (.close 66))))) (.step 3 (.step 18 (.step 42 (.close 66))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 24 (.close 68))) (.step 3 (.step 12 (.step 18 (.close 17))))) (.step 3 (.step 24 (.step 15 (.close 67)))))))))
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
def root : Box := ⟨16546956789305961896186184622292741386824339327255337058691808188648596662272647460385980005831425763501354680654007792449941192573506196958749334502853199842367945848531539768980266049761934732756390778196300371329024, 23134344423119528469337161273728954514829332289755893710825568566072334776906499395773707279587133766394405335871852653089029671579907895664540119367412385818609781757388394920429505772242972755483630050929234568446562271232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 29 (.step 31 (.step 38 (.step 40 (.step 69 (.split 65 1 (.split 12 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 67 1 (.step 75 (.split 16 0 (.split 17 0 (.split 21 0 (.split 51 0 (.step 75 (.close 40)) (.step 40 (.close 75))) (.step 40 (.close 75))) (.step 31 (.step 40 (.step 51 (.step 12 (.close 22)))))) (.step 38 (.step 40 (.step 66 (.step 23 (.close 67))))))) (.step 3 (.close 69))) (.step 3 (.close 51))) (.step 40 (.step 57 (.close 75)))) (.step 3 (.step 40 (.step 57 (.close 75))))) (.step 18 (.close 75))) (.step 18 (.close 75))) (.step 18 (.step 22 (.step 66 (.close 74))))) (.step 18 (.step 21 (.step 66 (.close 67))))) (.step 12 (.step 18 (.step 40 (.step 74 (.close 75)))))) (.step 15 (.close 75))) (.step 3 (.step 67 (.step 74 (.close 75)))))))))))
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
def root : Box := ⟨16159137489556603414244320920207755260570643874272790096378718934227145178000632285533183599444751722169291680326179484814395695872564645467528646975442577971062447117706581805644791064220639387457412869336615354368, 23134344433892286795713129099869159137404783647204391266611950862107439284304478748974020017151261604092173580494556217798653928639694184350441862465516557592679039493137533907340893713089639025119442427791078723238915735552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 32 (.step 47 (.step 51 (.step 69 (.step 74 (.split 65 1 (.split 12 1 (.split 21 1 (.split 22 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 54 1 (.split 58 1 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 49 1 (.split 50 1 (.split 59 1 (.split 36 0 (.split 40 0 (.split 43 0 (.step 74 (.close 3)) (.step 18 (.close 55))) (.step 74 (.close 3))) (.step 51 (.close 74))) (.step 55 (.close 26))) (.step 32 (.close 55))) (.step 12 (.close 55))) (.step 32 (.step 29 (.step 74 (.close 53))))) (.step 66 (.step 31 (.step 40 (.close 55))))) (.step 55 (.step 69 (.close 74)))) (.step 51 (.step 18 (.step 55 (.close 74))))) (.step 67 (.step 18 (.close 74)))) (.step 74 (.close 55))) (.step 12 (.step 55 (.split 54 0 (.step 74 (.close 3)) (.step 22 (.close 74)))))) (.step 11 (.step 36 (.step 55 (.step 74 (.close 12)))))) (.step 22 (.step 29 (.step 55 (.step 74 (.close 12)))))) (.step 31 (.close 40))) (.step 31 (.close 74))) (.step 11 (.step 36 (.step 55 (.step 61 (.step 67 (.step 74 (.close 3)))))))) (.step 18 (.close 23))) (.step 18 (.close 74))) (.step 22 (.step 29 (.step 55 (.step 57 (.step 66 (.step 74 (.close 3)))))))) (.step 68 (.step 74 (.close 3))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129099869159137404783647204391266611950862107439284304478748974020017151261604092173580494556217798653928639694184350441862465516557592679039493137533907340893713089639025119442427791078723238915735552⟩
def references : Fin 3 → Box := ![Part14.root, Part15.root, Part16.root]
def proof : Chunks.Proof 3 := (.split 71 2 (.step 3 (.split 72 2 (.split 74 2 (.reuse 0) (.run (.step 11 (.step 17 (.step 18 (.step 23 (.split 65 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 67 1 (.step 77 (.split 34 0 (.split 36 0 (.split 40 0 (.split 51 0 (.step 77 (.close 23)) (.step 23 (.close 77))) (.step 23 (.close 77))) (.step 18 (.step 23 (.step 51 (.step 32 (.close 36)))))) (.step 23 (.step 66 (.close 77))))) (.step 3 (.close 69))) (.step 3 (.close 51))) (.step 23 (.step 61 (.close 77)))) (.step 3 (.step 23 (.step 61 (.close 77))))) (.step 31 (.close 77))) (.step 31 (.close 77))) (.step 42 (.close 77))) (.step 31 (.step 36 (.step 66 (.close 74))))) (.step 23 (.step 32 (.step 66 (.step 74 (.close 77)))))) (.step 17 (.step 31 (.step 34 (.close 66))))) (.step 3 (.step 67 (.step 74 (.close 77))))))))))) (.reuse 1))) (.reuse 2))
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
def root : Box := ⟨4294967296, 23134344433892286795713129099878284018640028037641673609823351444757225741318975868835178402187060154426590935267568043421288671439251468969589051280137935002121790369134039229980338141466143014468162957691244471623408943104⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 64 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 67 (.step 69 (.split 21 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 40 1 (.split 42 1 (.split 54 1 (.split 58 1 (.split 12 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 34 0 (.split 36 0 (.step 55 (.split 39 1 (.split 54 0 (.step 67 (.close 3)) (.step 51 (.close 67))) (.step 67 (.close 42)))) (.step 51 (.step 67 (.close 3)))) (.step 66 (.step 67 (.close 3)))) (.step 51 (.step 18 (.close 67)))) (.step 67 (.close 55))) (.step 67 (.close 55))) (.step 29 (.step 55 (.step 66 (.step 67 (.close 3)))))) (.step 11 (.step 42 (.step 51 (.step 55 (.close 67)))))) (.step 29 (.step 51 (.step 55 (.step 67 (.close 12)))))) (.step 31 (.close 40))) (.step 31 (.close 67))) (.step 31 (.close 36))) (.step 31 (.close 34))) (.step 18 (.close 23))) (.step 18 (.close 67)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨12156783893206034058141819913157698684606776071022764355456027333078084408436254335155391744962218147328704745931545280807798294166245435472324828615568252989437056064657154899968, 23134344433892286795713129099878292929656859339096232613832333200233266282177703211749976862020956246752420111767644835073084499117194491605162035425851210978695053177401909011373101872132281854524096643875095812005638963200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 26 (.step 44 (.split 63 2 (.split 64 2 (.split 71 2 (.step 55 (.step 62 (.split 12 1 (.split 14 1 (.split 16 1 (.split 21 1 (.split 34 1 (.split 35 1 (.split 17 1 (.split 22 1 (.split 36 1 (.step 62 (.split 40 1 (.split 42 1 (.split 16 0 (.step 62 (.split 17 0 (.split 21 0 (.split 34 0 (.split 36 0 (.step 62 (.close 42)) (.step 3 (.step 23 (.step 22 (.step 23 (.close 57)))))) (.step 3 (.step 40 (.step 15 (.close 40))))) (.step 3 (.step 23 (.close 42)))) (.step 3 (.step 23 (.close 61))))) (.step 3 (.step 42 (.close 62)))) (.step 31 (.close 40))) (.step 31 (.close 62)))) (.step 31 (.close 62))) (.step 18 (.close 62))) (.step 18 (.close 62))) (.step 9 (.step 21 (.step 26 (.step 32 (.step 40 (.step 55 (.step 31 (.close 12))))))))) (.step 15 (.step 31 (.close 34)))) (.step 18 (.close 62))) (.step 18 (.close 62))) (.step 12 (.step 27 (.step 34 (.step 42 (.step 44 (.step 23 (.step 55 (.step 18 (.close 32)))))))))) (.step 15 (.close 62))))) (.step 55 (.close 66))) (.step 55 (.close 67))) (.step 55 (.close 66)))))))
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
def root : Box := ⟨11871859270709017634904121008943065121686304756858168315875026692459066805113529624175187250939666159500688228448774688288865521646724058078442215444890872059997125067432525824, 23134344433892286795713129099878292929656859339104147186679472545323202362850331921831101065192195025629670129562617546276493518866644616439121812865518336464327569636261152692470917910851243331487357225248427228714397335552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 27 (.step 32 (.step 34 (.step 36 (.step 40 (.step 44 (.split 63 2 (.split 64 2 (.split 65 1 (.split 71 1 (.split 12 1 (.split 21 1 (.step 61 (.split 22 1 (.split 54 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 35 1 (.split 39 0 (.split 34 0 (.step 61 (.split 36 0 (.step 61 (.close 32)) (.step 22 (.close 40)))) (.step 3 (.close 40))) (.step 42 (.close 61))) (.step 32 (.step 40 (.close 3)))) (.step 36 (.step 40 (.close 61)))) (.step 42 (.step 18 (.close 61)))) (.step 34 (.step 61 (.close 31)))) (.step 34 (.step 40 (.step 61 (.close 21))))) (.step 3 (.close 55))) (.step 32 (.step 40 (.step 51 (.step 61 (.close 15)))))) (.step 12 (.step 34 (.step 40 (.step 51 (.step 61 (.close 32))))))) (.step 22 (.step 40 (.step 61 (.close 15))))) (.step 18 (.close 23)))) (.step 18 (.close 61))) (.step 22 (.step 34 (.step 40 (.step 57 (.step 61 (.close 3))))))) (.step 61 (.close 74))) (.step 3 (.close 61))) (.step 23 (.step 32 (.step 42 (.step 67 (.step 74 (.split 34 0 (.split 42 0 (.step 61 (.close 23)) (.step 40 (.close 61))) (.step 18 (.step 34 (.close 40)))))))))) (.step 12 (.step 23 (.step 34 (.step 66 (.step 74 (.split 42 0 (.step 61 (.close 32)) (.step 40 (.close 61)))))))))))))))))
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
def root : Box := ⟨10797393106903671318745292418446356461287273083924599919441813374268410193611570888765697646649338057159810185520450148295699838533186319253620436434076397547290624, 23134344433892286795713129099878292929656859339104147186679479743585273631964544418692713362763169217145059412629230507485409697806773690819714323330616102689699009509718166325903115044076932122366859638872716612976565551104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 9 (.step 12 (.step 21 (.step 22 (.step 23 (.step 26 (.step 32 (.step 57 (.split 63 2 (.split 64 2 (.split 58 1 (.split 65 1 (.split 71 1 (.split 34 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 12 0 (.split 14 1 (.split 34 0 (.split 35 0 (.split 39 0 (.split 16 0 (.split 17 0 (.step 57 (.close 12)) (.step 3 (.step 22 (.close 23)))) (.step 3 (.step 21 (.close 23)))) (.step 21 (.step 23 (.step 32 (.step 36 (.close 57)))))) (.step 23 (.step 32 (.close 57)))) (.step 15 (.step 57 (.close 3)))) (.step 23 (.close 57))) (.step 15 (.step 57 (.close 18)))) (.step 21 (.step 23 (.step 32 (.step 51 (.close 57)))))) (.step 12 (.step 23 (.step 51 (.step 57 (.step 21 (.close 57))))))) (.step 31 (.close 40))) (.step 31 (.close 57))) (.step 21 (.step 23 (.step 36 (.step 57 (.close 3)))))) (.step 31 (.close 34))) (.step 57 (.close 74))) (.step 3 (.close 57))) (.step 57 (.close 23))) (.step 21 (.step 31 (.step 32 (.step 55 (.step 67 (.step 74 (.split 14 0 (.step 57 (.close 23)) (.step 23 (.close 57)))))))))) (.step 31 (.step 51 (.step 57 (.step 66 (.split 39 0 (.step 66 (.close 26)) (.step 23 (.close 57)))))))))))))))))
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
def root : Box := ⟨9820171823688425610039569090482797456649926138129194368449874104288401389214023664649810276977712471452660052382680213027651769637656179159989877735424, 23134344433892286795713129099878292929656859339104147186679479743585273638511325634484997102789548610800257717062514599571539276773356427011981916139965212456239194161526480627676483299197074140801372730643502719633620729856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 21 (.step 32 (.step 57 (.step 61 (.split 63 2 (.step 55 (.step 62 (.split 72 2 (.split 74 2 (.split 12 1 (.split 14 1 (.split 16 1 (.step 52 (.split 21 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 54 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 17 1 (.split 22 1 (.split 74 1 (.step 53 (.step 32 (.step 23 (.step 53 (.close 55))))) (.step 27 (.step 32 (.step 44 (.step 23 (.step 53 (.close 12))))))) (.step 18 (.close 53))) (.step 18 (.close 53))) (.step 22 (.step 26 (.step 53 (.step 15 (.close 23)))))) (.step 3 (.close 53))) (.step 9 (.step 26 (.step 40 (.step 53 (.close 15)))))) (.step 53 (.close 57))) (.step 31 (.close 53))) (.step 21 (.step 22 (.step 31 (.close 12))))) (.step 15 (.step 31 (.close 34)))) (.step 18 (.close 53)))) (.step 18 (.close 53))) (.step 18 (.step 27 (.step 32 (.step 34 (.step 23 (.step 53 (.step 23 (.step 44 (.step 17 (.close 3))))))))))) (.step 15 (.close 53))) (.step 17 (.step 18 (.step 44 (.step 55 (.step 53 (.close 61))))))) (.step 26 (.step 31 (.step 55 (.step 53 (.close 75)))))))) (.step 55 (.close 66)))))))))
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
def root : Box := ⟨9590011546570728134804266689924606891259693494266791375439330179969141981654319985009580348611047335402988332404961145534816181286773612465218387968, 23134344433892286795713129099878292929656859339104147186679479743585273638517718975516044254879418121926874121656687728567717137690315980465294677461068092446245581060600512184611808854133714904491250184834685127940903010304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 12 (.step 57 (.step 61 (.split 64 2 (.step 55 (.split 72 2 (.split 74 2 (.split 16 1 (.step 52 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 40 1 (.split 42 1 (.split 54 1 (.split 72 1 (.split 12 0 (.split 17 1 (.split 22 1 (.split 74 1 (.step 52 (.step 55 (.step 34 (.step 23 (.step 42 (.step 40 (.step 52 (.close 3)))))))) (.step 27 (.step 34 (.step 44 (.step 23 (.step 52 (.close 42))))))) (.step 18 (.close 52))) (.step 18 (.close 52))) (.step 12 (.step 3 (.close 17)))) (.step 9 (.step 12 (.step 26 (.step 40 (.close 52)))))) (.step 12 (.step 52 (.close 55)))) (.step 31 (.close 52))) (.step 31 (.close 52))) (.step 31 (.close 52))) (.step 9 (.step 12 (.step 21 (.step 31 (.step 40 (.step 52 (.step 26 (.step 40 (.step 38 (.close 3))))))))))) (.step 15 (.step 31 (.close 34)))) (.step 18 (.close 52)))) (.step 18 (.close 52))) (.step 18 (.step 44 (.step 55 (.step 52 (.close 77)))))) (.step 26 (.step 31 (.step 38 (.step 55 (.step 52 (.close 57)))))))) (.step 55 (.close 67))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨7746749634260725768967757516009035622989117378487670538491978069621942866050523583888936059840413494307709515922537447424, 23134344433892286795713129099878292929656859339104147186679479743585273638517718975516044254879418121932038621412861545747028976034322004213954089046726539471906899773681807428645491243393005611051525847706491471886397997056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 61 (.split 49 2 (.split 50 2 (.split 54 2 (.step 18 (.split 59 2 (.split 63 2 (.split 64 2 (.split 71 2 (.step 43 (.step 31 (.step 61 (.split 74 2 (.step 43 (.step 27 (.split 12 1 (.step 61 (.split 14 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.step 43 (.split 63 1 (.step 42 (.step 31 (.step 12 (.step 42 (.close 74))))) (.step 31 (.close 66)))) (.step 3 (.step 31 (.close 43)))) (.step 31 (.close 43))) (.step 3 (.close 18))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 12 (.step 23 (.close 17))))) (.step 31 (.close 15))))) (.step 23 (.close 77)))))) (.step 31 (.step 43 (.close 74)))) (.step 31 (.step 43 (.close 67)))) (.step 31 (.step 43 (.close 66)))) (.step 3 (.step 31 (.step 61 (.close 62)))))) (.step 31 (.step 43 (.close 57)))) (.step 3 (.step 21 (.step 31 (.close 53))))) (.step 3 (.step 31 (.step 42 (.step 52 (.close 43)))))))))
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
def root : Box := ⟨7565185189707740008757575699227573850575309939929365760246072333615178580127464437391539120937903803034872578433875968, 23134344433892286795713129104550232122101987242992706910916578060275939629940244344429137393208278600838977473509973058619280681930369378436617465652968402565904843448674536829571811500116176737107422803777094650779932819456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 32 (.step 34 (.step 36 (.step 27 (.step 42 (.step 40 (.step 43 (.step 44 (.step 67 (.split 63 2 (.split 40 1 (.split 65 1 (.split 12 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 51 1 (.split 54 2 (.split 63 1 (.split 67 1 (.split 71 2 (.split 64 1 (.split 12 0 (.split 54 1 (.split 71 1 (.step 42 (.split 54 0 (.step 42 (.close 31)) (.step 23 (.close 42)))) (.step 36 (.step 40 (.close 42)))) (.step 36 (.step 40 (.close 42)))) (.step 34 (.step 40 (.step 42 (.close 36))))) (.step 42 (.close 40))) (.step 36 (.step 40 (.step 61 (.step 67 (.split 34 0 (.split 42 0 (.step 42 (.close 23)) (.step 40 (.close 42))) (.step 18 (.step 34 (.close 40))))))))) (.step 3 (.close 42))) (.step 34 (.step 40 (.step 66 (.step 67 (.step 42 (.step 36 (.close 42)))))))) (.step 21 (.step 40 (.step 61 (.split 22 0 (.step 57 (.close 12)) (.step 23 (.close 42))))))) (.step 3 (.close 42))) (.step 18 (.close 23))) (.step 18 (.close 42))) (.step 18 (.close 22))) (.step 21 (.step 34 (.step 40 (.split 21 1 (.step 42 (.step 36 (.step 15 (.close 23)))) (.step 3 (.step 15 (.close 18)))))))) (.step 3 (.step 42 (.close 74)))) (.step 24 (.step 42 (.close 3)))) (.step 23 (.step 34 (.step 66 (.split 36 0 (.split 42 0 (.step 42 (.close 23)) (.step 40 (.close 42))) (.step 40 (.close 42))))))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨6880495847970214534832462685906260822389694967504843371212766518160768628265454424210055659330381354631168, 23134344433892286795713129104550232122101987242992706910916578060275939629940244344429137393208278600838977473509973063206277913910512401658259256257142284159034821785236784304749490273961928914077038943814200871031305928704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 21 (.step 31 (.step 32 (.step 29 (.step 38 (.step 40 (.step 57 (.step 66 (.step 68 (.step 74 (.split 49 2 (.split 59 2 (.split 74 2 (.split 65 1 (.split 12 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 49 1 (.split 51 1 (.split 59 1 (.step 38 (.split 67 1 (.step 32 (.step 38 (.split 17 0 (.split 21 0 (.split 22 0 (.split 51 0 (.step 38 (.step 23 (.close 12))) (.step 23 (.step 31 (.step 22 (.step 3 (.close 38)))))) (.step 31 (.step 23 (.step 12 (.close 74))))) (.step 23 (.step 31 (.close 38)))) (.step 31 (.step 23 (.step 38 (.close 74))))))) (.step 3 (.close 38)))) (.step 26 (.step 38 (.step 23 (.step 38 (.close 40)))))) (.step 3 (.close 38))) (.step 3 (.step 12 (.step 40 (.step 38 (.close 3)))))) (.step 18 (.close 38))) (.step 18 (.close 38))) (.step 18 (.close 38))) (.step 18 (.step 32 (.step 40 (.step 38 (.close 17)))))) (.step 15 (.close 38))) (.step 3 (.step 21 (.close 38)))) (.step 17 (.step 18 (.step 32 (.step 40 (.step 66 (.step 69 (.step 38 (.close 74))))))))) (.step 3 (.step 15 (.step 26 (.step 40 (.step 52 (.step 38 (.close 57)))))))) (.step 12 (.step 40 (.step 52 (.step 57 (.step 38 (.close 3)))))))))))))))))))
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
def root : Box := ⟨4936513671963618126464907547672051514948207596900739594340794368, 23134344433892286795713129104550232122101987242992706910916578060275939629940244344429137393208278600838977473509973063206277913910512401658259256257142284159038112794351426716833800212327043615087004415545468030758003146752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 57 (.split 35 2 (.split 39 2 (.split 49 2 (.split 50 2 (.split 58 2 (.step 31 (.split 59 2 (.split 63 2 (.split 64 2 (.split 71 2 (.step 24 (.step 18 (.split 72 2 (.step 24 (.step 9 (.split 35 1 (.split 39 1 (.step 57 (.split 49 1 (.split 50 1 (.split 51 1 (.split 58 1 (.split 59 1 (.split 63 1 (.step 24 (.step 18 (.step 15 (.step 21 (.close 24))))) (.step 18 (.close 66))) (.step 3 (.step 15 (.step 18 (.close 12))))) (.step 18 (.close 24))) (.step 3 (.close 18))) (.step 18 (.close 53))) (.step 18 (.close 52)))) (.step 18 (.step 24 (.close 42)))) (.step 15 (.step 18 (.step 21 (.close 38))))))) (.step 15 (.step 18 (.close 75)))))) (.step 18 (.step 24 (.close 74)))) (.step 18 (.step 24 (.close 67)))) (.step 18 (.step 24 (.close 66)))) (.step 3 (.step 18 (.step 57 (.close 62)))))) (.step 18 (.step 24 (.close 61)))) (.step 3 (.step 15 (.step 18 (.step 53 (.close 24)))))) (.step 3 (.step 12 (.step 18 (.close 52))))) (.step 18 (.step 24 (.close 42)))) (.step 15 (.step 18 (.step 31 (.step 38 (.close 24)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨4181389724724491839037947176121572077338624, 23134344433892286795713129104550232122101987242992706910916578060275939629940244344429137393208278600838977473509973063206277913910512401658259256257142284159038112794351426716833802999920193431414897107510252111803191394304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 23 (.step 31 (.step 11 (.step 17 (.step 34 (.step 42 (.step 43 (.step 61 (.step 67 (.step 68 (.step 74 (.split 35 2 (.split 50 2 (.split 59 2 (.split 72 2 (.split 40 1 (.split 65 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 42 1 (.split 50 1 (.split 51 1 (.split 59 1 (.step 17 (.split 67 1 (.step 12 (.split 58 1 (.step 67 (.step 23 (.step 17 (.step 23 (.step 17 (.close 31)))))) (.step 17 (.close 3)))) (.step 3 (.close 17)))) (.step 3 (.step 17 (.step 23 (.close 3))))) (.step 3 (.close 17))) (.step 3 (.step 23 (.step 17 (.close 53))))) (.step 12 (.step 23 (.step 17 (.close 31))))) (.step 17 (.close 42))) (.step 31 (.step 12 (.close 17)))) (.step 12 (.step 23 (.step 31 (.step 17 (.close 38)))))) (.step 17 (.close 31))) (.step 3 (.step 12 (.close 17)))) (.step 23 (.step 31 (.close 17)))) (.step 12 (.step 23 (.step 31 (.step 38 (.step 67 (.step 69 (.step 17 (.close 74))))))))) (.step 3 (.step 23 (.step 42 (.step 44 (.step 53 (.step 17 (.close 61)))))))) (.step 23 (.step 32 (.step 53 (.step 61 (.step 17 (.close 3))))))) (.step 12 (.step 23 (.step 32 (.step 38 (.step 74 (.step 17 (.close 31))))))))))))))))))))))
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
def root : Box := ⟨3987683987354747618711421185136001024, 23134344433892286795713129104550232122101987242992706910916578060275939629940244344429137393208278600838977473509973063206277913910514438694235590743228552606411518839209394670433335643287706105002746981382933391526470877184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 15 (.step 18 (.step 9 (.step 21 (.step 15 (.step 31 (.step 32 (.step 43 (.step 66 (.split 39 2 (.split 64 2 (.split 21 1 (.split 40 1 (.split 65 1 (.split 36 1 (.split 39 1 (.split 42 1 (.split 51 1 (.split 58 2 (.split 64 1 (.split 67 1 (.split 71 2 (.split 63 1 (.split 12 3 (.split 34 0 (.step 23 (.split 58 1 (.split 71 1 (.split 39 0 (.step 15 (.close 18)) (.step 21 (.close 15))) (.step 22 (.step 15 (.close 18)))) (.step 22 (.step 15 (.close 18))))) (.step 15 (.close 23))) (.step 15 (.close 23))) (.step 15 (.close 23))) (.step 22 (.step 23 (.step 66 (.split 39 0 (.step 74 (.close 15)) (.step 21 (.step 15 (.close 23)))))))) (.step 3 (.close 15))) (.step 21 (.step 23 (.step 66 (.step 15 (.step 22 (.step 57 (.close 67)))))))) (.step 22 (.step 23 (.split 16 0 (.split 22 0 (.step 15 (.close 21)) (.step 23 (.close 15))) (.step 21 (.step 15 (.close 18))))))) (.step 3 (.close 15))) (.step 15 (.close 3))) (.step 21 (.step 23 (.step 15 (.step 22 (.step 15 (.close 42))))))) (.step 15 (.close 3))) (.step 3 (.step 15 (.close 74)))) (.step 3 (.step 15 (.step 24 (.step 31 (.step 42 (.close 43))))))) (.step 15 (.close 24))) (.step 15 (.step 21 (.step 23 (.step 31 (.step 67 (.split 51 0 (.split 58 0 (.step 67 (.close 15)) (.step 22 (.step 15 (.close 23)))) (.step 15 (.close 23))))))))) (.step 3 (.step 21 (.step 23 (.step 42 (.split 17 0 (.split 22 0 (.step 15 (.close 22)) (.step 23 (.close 15))) (.step 22 (.step 15 (.close 18))))))))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part29

namespace Part30
def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987242992706910916578060275939629940244344429137393208278600838977473509973063206277913910514438694235590743228552606411518839209394670433335643287706105002746981382933391526470877184⟩
def references : Fin 12 → Box := ![Part18.root, Part19.root, Part20.root, Part21.root, Part22.root, Part23.root, Part24.root, Part25.root, Part26.root, Part27.root, Part28.root, Part29.root]
def proof : Chunks.Proof 12 := (.split 12 2 (.step 18 (.split 14 2 (.split 21 2 (.split 35 2 (.split 39 2 (.step 31 (.step 68 (.split 40 2 (.split 49 2 (.split 50 2 (.split 54 2 (.split 58 2 (.split 59 2 (.split 63 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 66 (.split 21 1 (.split 22 1 (.split 40 1 (.split 42 1 (.split 54 1 (.split 58 1 (.split 12 1 (.split 16 0 (.split 17 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.split 39 1 (.split 54 0 (.step 66 (.close 3)) (.step 51 (.close 66))) (.step 11 (.step 32 (.step 66 (.close 3)))))) (.step 51 (.step 66 (.close 55)))) (.step 66 (.close 55))) (.step 66 (.close 55))) (.step 66 (.close 55))) (.step 66 (.step 18 (.close 32)))) (.step 66 (.close 15))) (.step 11 (.step 51 (.step 55 (.step 66 (.close 32)))))) (.step 15 (.step 29 (.step 51 (.step 55 (.close 66)))))) (.step 31 (.close 40))) (.step 31 (.close 66))) (.step 18 (.close 23))) (.step 18 (.close 66)))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)))) (.reuse 7)) (.reuse 8)) (.reuse 9)) (.reuse 10))) (.reuse 11))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part23.excludes
  · exact Part24.excludes
  · exact Part25.excludes
  · exact Part26.excludes
  · exact Part27.excludes
  · exact Part28.excludes
  · exact Part29.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part30

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part30.excludes
end FiveColour.Packed.ProjectedChunks.Case140
