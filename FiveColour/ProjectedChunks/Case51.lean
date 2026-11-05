module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case51
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759869379394596642197669783870791221248⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37630511536740893520887, 5789234131009374248507346766749886964179117598075761631441503938856419104125729984377942245333425284026394393415169773689373755704242316349912225571028696891635007459092358541327061333498215709696615525420286517587399934977, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907329742994904791441810729640082411191744291197656906926870849228364607196099261860895482072263214682283451924959312029237224942326947742140057765807199560437152655962561052672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 52 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 48 (.step 3 (.step 55 (.close 7)))) (.split 38 0 (.step 7 (.close 3)) (.step 3 (.close 7)))) (.split 30 0 (.step 55 (.close 3)) (.step 7 (.close 3)))) (.split 22 0 (.split 30 0 (.step 55 (.close 3)) (.step 7 (.close 3))) (.step 7 (.close 18)))) (.split 30 0 (.split 17 0 (.split 22 0 (.step 55 (.close 3)) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 3 (.step 48 (.step 3 (.step 4 (.close 7))))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 17 (.close 18))))) (.step 3 (.step 7 (.step 17 (.close 18))))) (.step 7 (.step 18 (.close 3))))) (.split 11 0 (.split 38 0 (.step 7 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.step 55 (.close 3)))) (.step 55 (.split 67 1 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.split 22 0 (.step 55 (.step 7 (.step 58 (.close 3)))) (.step 7 (.close 3)))) (.step 48 (.close 7))) (.step 48 (.step 7 (.close 18)))) (.step 48 (.step 3 (.step 7 (.step 8 (.step 18 (.step 3 (.close 7)))))))) (.step 55 (.close 7)))) (.step 7 (.step 3 (.step 9 (.step 3 (.close 27)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075743702186563710326317312853837380693889657622864945658497925949331159554953215521879912576489320220933772169227524461125626605167071582543054586762138822897565696⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.split 57 1 (.reuse 0) (.run (.step 3 (.split 52 1 (.split 10 0 (.step 60 (.split 30 0 (.step 60 (.step 3 (.step 18 (.step 3 (.close 16))))) (.step 3 (.step 49 (.step 3 (.close 17)))))) (.step 3 (.step 48 (.step 3 (.close 49))))) (.step 48 (.step 3 (.step 49 (.step 3 (.close 19))))))))) (.run (.split 52 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.split 22 0 (.split 30 0 (.split 46 0 (.step 43 (.step 48 (.step 55 (.close 7)))) (.split 51 0 (.split 34 0 (.step 3 (.step 22 (.step 31 (.step 21 (.close 48))))) (.step 16 (.close 3))) (.step 3 (.close 16)))) (.step 3 (.step 7 (.step 3 (.step 7 (.close 16)))))) (.step 3 (.step 7 (.step 3 (.step 5 (.step 3 (.close 16)))))))) (.step 3 (.step 7 (.step 3 (.step 5 (.step 3 (.close 16))))))) (.step 3 (.step 7 (.step 43 (.step 3 (.close 16)))))) (.step 3 (.step 43 (.step 3 (.step 51 (.close 3)))))) (.step 3 (.step 7 (.step 3 (.step 7 (.close 16)))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 48 (.step 7 (.step 9 (.step 7 (.close 16)))))))) (.step 3 (.step 28 (.step 60 (.close 3))))) (.step 3 (.step 48 (.step 16 (.close 45))))))) (.run (.step 48 (.step 58 (.step 18 (.step 3 (.step 5 (.step 28 (.step 7 (.step 3 (.close 31)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966317649180977032861940016616768361105608460486015634259053152913993556129296986071225807460207646401861464863871563124338365908167673267151232286058348544⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 53 1 (.reuse 0) (.run (.split 52 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.split 11 0 (.step 3 (.step 4 (.step 3 (.close 48)))) (.split 34 0 (.step 56 (.step 3 (.close 34))) (.step 3 (.step 4 (.step 3 (.close 14)))))) (.step 3 (.close 4))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 7 (.close 18)))) (.step 7 (.step 18 (.close 3)))) (.step 8 (.split 17 0 (.step 7 (.step 18 (.close 3))) (.step 19 (.step 3 (.step 7 (.close 18))))))) (.step 3 (.step 7 (.step 3 (.step 7 (.close 14)))))) (.step 3 (.step 7 (.close 8)))) (.step 4 (.step 44 (.step 48 (.close 17))))) (.step 3 (.step 8 (.step 60 (.close 3))))) (.step 3 (.step 24 (.step 43 (.step 51 (.close 3)))))) (.step 3 (.step 5 (.step 18 (.step 3 (.step 48 (.step 51 (.step 3 (.close 48))))))))) (.step 3 (.step 48 (.step 19 (.close 25))))))) (.run (.step 3 (.split 53 1 (.split 55 1 (.split 56 1 (.split 11 0 (.split 38 0 (.step 54 (.step 7 (.close 3))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 7 (.step 27 (.close 34))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 7 (.step 8 (.step 27 (.step 34 (.close 44))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 9797766621314684873895708907333611310075747213530570140523794422237966124016217118538173185601260874282180016251659619556746977940300401825030968960447952090268640153134942654862910603770663056776888320⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.split 22 0 (.step 55 (.step 7 (.step 58 (.close 3)))) (.step 7 (.close 3)))) (.step 48 (.close 7))) (.step 48 (.step 7 (.close 18)))) (.step 48 (.step 3 (.step 7 (.step 8 (.step 18 (.step 3 (.close 7)))))))) (.step 55 (.close 7)))) (.step 7 (.step 3 (.step 9 (.step 3 (.close 27)))))) (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 11 0 (.split 34 0 (.step 62 (.close 3)) (.step 9 (.step 7 (.step 55 (.step 7 (.close 16)))))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 53 (.split 11 0 (.split 16 0 (.split 17 0 (.split 30 0 (.step 55 (.close 7)) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 3 (.close 7)))))) (.step 3 (.step 48 (.step 3 (.close 17))))) (.step 5 (.step 48 (.step 5 (.step 48 (.step 7 (.step 9 (.step 7 (.step 21 (.step 7 (.step 16 (.step 7 (.close 26))))))))))))) (.step 48 (.step 53 (.step 7 (.step 16 (.close 21)))))) (.step 3 (.step 4 (.step 48 (.step 35 (.step 50 (.step 48 (.close 27)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 9797766621314684873895708907333611310075747213530566870329857041619672155761275854247223266045779329306320991440068250079331233817185513558132092593306579671247290061384315282545091813968813881890439168⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.split 22 0 (.step 55 (.step 7 (.step 58 (.close 3)))) (.step 7 (.close 3)))) (.step 48 (.close 7))) (.step 48 (.step 7 (.close 18)))) (.step 48 (.step 3 (.step 7 (.step 8 (.step 17 (.close 3))))))) (.step 55 (.close 7)))) (.step 7 (.step 3 (.step 9 (.step 3 (.close 27)))))) (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 11 0 (.split 34 0 (.step 62 (.close 3)) (.step 9 (.step 7 (.step 55 (.step 7 (.close 16)))))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 52 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 3 (.close 7)))))) (.step 3 (.step 48 (.step 3 (.close 17))))) (.step 5 (.step 48 (.step 5 (.step 16 (.step 48 (.step 7 (.step 9 (.step 7 (.step 22 (.step 7 (.step 21 (.close 26))))))))))))) (.step 48 (.close 52))) (.step 3 (.step 4 (.step 48 (.step 49 (.step 34 (.step 48 (.close 27)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768255444527386074741220752012962974214626175412773094685138378919474051297220685733493421843034394218218468152729756970362946248135489768227078144⟩
def references : Fin 3 → Box := ![Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 3 := (.split 49 1 (.split 50 1 (.reuse 0) (.step 55 (.split 51 1 (.reuse 1) (.run (.step 3 (.step 54 (.step 57 (.step 61 (.split 55 1 (.split 11 0 (.split 38 0 (.step 53 (.step 7 (.close 3))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 7 (.step 27 (.close 34))))) (.step 3 (.step 7 (.step 9 (.close 53))))))))))))) (.step 55 (.split 50 1 (.split 51 1 (.reuse 2) (.run (.step 3 (.step 54 (.step 57 (.step 61 (.split 55 1 (.split 11 0 (.split 38 0 (.step 52 (.step 7 (.close 3))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 7 (.step 27 (.close 34))))) (.step 3 (.step 7 (.step 9 (.close 52))))))))))) (.run (.step 55 (.split 53 1 (.split 55 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 51 1 (.split 67 1 (.split 10 0 (.split 36 0 (.step 52 (.close 3)) (.step 9 (.step 52 (.step 55 (.close 7))))) (.step 52 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.close 3))))) (.step 52 (.close 3))) (.step 52 (.close 3))) (.step 9 (.step 52 (.step 55 (.step 7 (.close 16)))))) (.step 27 (.step 52 (.step 48 (.close 7))))) (.step 27 (.step 52 (.step 48 (.close 7))))) (.step 27 (.step 52 (.step 48 (.close 7))))) (.step 27 (.step 55 (.step 7 (.step 48 (.step 7 (.step 44 (.close 52)))))))) (.step 5 (.step 9 (.step 21 (.step 48 (.step 7 (.step 16 (.close 52)))))))) (.step 48 (.close 52))) (.step 3 (.step 4 (.step 27 (.step 34 (.step 48 (.close 44))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496087086157417190034294038011212863205740661804321282664727926291293207901023334714523541710883172118458100468718284382399806967343998828544⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 46 1 (.split 47 1 (.reuse 0) (.run (.step 3 (.split 49 1 (.split 52 1 (.split 55 1 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 50 (.step 3 (.step 5 (.step 3 (.step 17 (.close 18)))))) (.step 3 (.step 8 (.step 28 (.step 3 (.step 48 (.close 50))))))) (.step 48 (.step 50 (.close 3)))) (.step 48 (.step 50 (.step 3 (.close 21))))) (.step 48 (.step 49 (.step 50 (.step 3 (.close 21)))))) (.step 3 (.step 48 (.close 50)))) (.step 3 (.step 48 (.step 49 (.step 3 (.close 50)))))) (.step 48 (.step 50 (.step 3 (.step 16 (.close 21)))))) (.step 48 (.step 3 (.close 50)))) (.step 48 (.step 49 (.step 48 (.close 3)))))))) (.run (.split 47 1 (.step 3 (.split 49 1 (.split 52 1 (.split 55 1 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 50 (.step 49 (.step 60 (.step 49 (.step 3 (.close 17)))))) (.step 3 (.step 8 (.step 28 (.step 3 (.step 48 (.close 49))))))) (.step 48 (.step 49 (.close 3)))) (.step 48 (.step 49 (.step 3 (.close 21))))) (.step 48 (.step 49 (.close 3)))) (.step 3 (.step 48 (.step 49 (.close 3))))) (.step 3 (.step 48 (.close 49)))) (.step 48 (.step 49 (.step 3 (.close 21))))) (.step 48 (.step 3 (.close 49)))) (.step 48 (.step 49 (.step 48 (.close 3)))))) (.step 49 (.step 3 (.step 49 (.step 48 (.step 3 (.step 17 (.close 18))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515087042155977050166022829408021160073200469012344868827260410038790409614022472098126001578824483096902100658072944677579487444992⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 45 1 (.reuse 0) (.run (.step 48 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 48 (.step 31 (.step 3 (.step 4 (.step 8 (.step 7 (.step 3 (.step 17 (.close 18))))))))) (.step 3 (.step 7 (.step 48 (.close 54))))) (.step 48 (.close 53))) (.step 48 (.close 52))) (.step 3 (.step 48 (.close 50)))) (.step 3 (.step 48 (.close 49))))))) (.run (.step 3 (.split 45 1 (.split 46 1 (.step 3 (.split 51 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 34 0 (.split 45 0 (.split 49 1 (.step 55 (.step 7 (.close 9))) (.step 9 (.step 3 (.step 27 (.close 46))))) (.step 3 (.step 7 (.step 27 (.close 46))))) (.step 7 (.close 9))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 46))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 3 (.step 7 (.close 27)))) (.step 7 (.close 46))) (.split 11 0 (.split 38 0 (.step 46 (.step 7 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.step 46 (.close 52)))))) (.step 3 (.step 7 (.close 27)))) (.step 54 (.step 7 (.step 3 (.step 10 (.step 30 (.step 9 (.step 3 (.close 27)))))))))) (.step 3 (.step 8 (.close 10)))) (.step 3 (.step 7 (.step 8 (.step 27 (.step 46 (.close 52))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225215024284136453122862303379606157926290523134599960255853580143376029398501553830444170708836391677399173255101677568⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 46 0 (.step 7 (.close 31)) (.step 28 (.step 31 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 37)))))) (.step 7 (.step 31 (.close 16)))) (.step 28 (.step 31 (.close 60)))) (.step 28 (.step 59 (.step 76 (.step 59 (.step 3 (.step 7 (.close 16)))))))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 22 (.step 16 (.close 21)))))))) (.step 3 (.step 4 (.step 7 (.step 37 (.close 51)))))) (.step 3 (.step 31 (.step 16 (.close 45))))) (.step 5 (.step 7 (.step 31 (.step 21 (.step 16 (.step 22 (.step 16 (.close 45))))))))) (.step 5 (.step 31 (.step 7 (.step 16 (.step 45 (.step 21 (.step 22 (.step 45 (.close 52)))))))))) (.step 31 (.step 28 (.step 50 (.step 31 (.step 50 (.step 3 (.close 45)))))))) (.step 31 (.step 28 (.step 49 (.step 31 (.step 49 (.close 3)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 9797766621314684873895708907333611310075747216966320922571584929003810029806465188704763139753448951978793403645367911238956208229485094820716719074356381108166409260072588517065149459771836028835332096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.split 22 0 (.split 30 0 (.split 46 0 (.step 43 (.step 48 (.step 41 (.close 3)))) (.split 51 0 (.split 34 0 (.step 3 (.step 21 (.step 22 (.close 31)))) (.step 16 (.close 3))) (.step 3 (.close 16)))) (.step 3 (.step 7 (.step 3 (.step 7 (.close 16)))))) (.step 3 (.step 7 (.step 3 (.step 5 (.step 3 (.close 16)))))))) (.step 3 (.step 7 (.step 3 (.step 5 (.step 3 (.close 16))))))) (.step 3 (.step 7 (.step 43 (.step 3 (.close 16)))))) (.step 3 (.step 43 (.step 3 (.step 41 (.close 3)))))) (.step 3 (.step 7 (.step 3 (.step 7 (.close 16)))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 48 (.step 7 (.step 9 (.step 7 (.close 16)))))))) (.step 5 (.step 28 (.step 58 (.close 31))))) (.step 3 (.step 28 (.step 60 (.step 3 (.close 16)))))) (.step 28 (.step 41 (.split 59 1 (.step 59 (.step 3 (.step 4 (.close 7)))) (.step 5 (.step 21 (.step 22 (.step 26 (.close 41))))))))) (.step 3 (.step 5 (.step 43 (.step 24 (.step 59 (.step 60 (.step 3 (.step 41 (.step 3 (.close 19))))))))))) (.step 3 (.step 48 (.step 16 (.close 41))))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 41))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 48 (.step 7 (.step 9 (.step 21 (.close 26)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 4898883310657342436947858505931971705553515434341103012552357296195872284851088327147756360951181440295252157463117783175219417072656040412658587159033716454345329837215761770419840469359732638531715072⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 46 0 (.step 7 (.step 22 (.close 31))) (.step 28 (.step 31 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 37)))))) (.step 7 (.step 22 (.close 31)))) (.step 28 (.step 31 (.step 51 (.step 3 (.close 37)))))) (.step 22 (.step 28 (.step 51 (.step 59 (.step 3 (.step 7 (.close 16)))))))) (.step 5 (.step 7 (.step 31 (.step 16 (.close 22)))))) (.step 3 (.step 4 (.step 7 (.step 37 (.close 51)))))) (.step 3 (.step 31 (.step 16 (.step 39 (.close 51)))))) (.step 5 (.step 7 (.step 22 (.step 31 (.step 16 (.step 21 (.step 16 (.close 22))))))))) (.step 5 (.step 22 (.step 31 (.step 7 (.step 16 (.step 21 (.step 22 (.step 21 (.close 52)))))))))) (.step 31 (.step 28 (.step 50 (.step 31 (.step 50 (.step 3 (.close 39)))))))) (.step 31 (.step 28 (.step 49 (.step 31 (.step 49 (.close 3))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872270360586904047501897498942677645680046895178646782421085727644481431221992543941020983011492372383006720⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 45 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.step 45 (.step 7 (.step 31 (.close 3)))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 22 (.step 16 (.close 21)))))))) (.step 3 (.step 4 (.step 5 (.step 4 (.step 7 (.step 37 (.step 39 (.close 37))))))))) (.step 3 (.step 31 (.step 16 (.close 39))))) (.step 5 (.step 7 (.step 31 (.step 38 (.step 16 (.step 22 (.step 16 (.step 39 (.close 45)))))))))) (.step 5 (.step 7 (.step 31 (.step 39 (.step 38 (.step 45 (.close 52)))))))) (.step 28 (.step 31 (.step 39 (.step 45 (.step 37 (.close 50))))))) (.step 28 (.step 31 (.step 37 (.step 39 (.step 45 (.close 49)))))))))) (.run (.step 38 (.step 28 (.step 45 (.split 46 1 (.split 47 1 (.split 49 1 (.step 41 (.split 52 1 (.split 53 1 (.split 59 1 (.step 41 (.step 3 (.step 7 (.close 16)))) (.step 5 (.step 7 (.step 21 (.step 22 (.close 31)))))) (.step 3 (.step 4 (.step 37 (.close 39))))) (.step 3 (.step 31 (.step 16 (.close 39)))))) (.step 3 (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 31 (.close 39))))))))) (.step 21 (.step 31 (.close 41)))) (.step 31 (.step 37 (.close 41)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872270360586904047501897498942677645680046895178646782421085727644481431221992543941020983011492372383006720⟩
def references : Fin 3 → Box := ![Part8.root, Part9.root, Part11.root]
def proof : Chunks.Proof 3 := (.split 36 1 (.split 38 1 (.reuse 0) (.split 42 1 (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.reuse 1) (.run (.step 3 (.step 48 (.step 5 (.step 49 (.step 58 (.step 16 (.step 48 (.step 9 (.step 52 (.step 21 (.step 7 (.close 26)))))))))))))) (.run (.step 21 (.step 28 (.step 41 (.step 3 (.step 50 (.step 3 (.step 16 (.close 21)))))))))) (.run (.step 49 (.step 3 (.step 28 (.step 50 (.step 41 (.step 49 (.step 3 (.step 21 (.close 22))))))))))) (.run (.step 3 (.step 4 (.step 21 (.step 31 (.step 48 (.step 4 (.step 16 (.step 21 (.close 41))))))))))) (.run (.step 3 (.step 10 (.step 7 (.close 9)))))) (.run (.step 7 (.step 31 (.step 38 (.step 28 (.step 60 (.step 76 (.step 41 (.split 49 1 (.step 41 (.step 3 (.step 7 (.step 16 (.close 21))))) (.step 3 (.step 5 (.step 7 (.step 16 (.step 21 (.close 31))))))))))))))))) (.reuse 2))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 4898883310657342436947858505931971705553515434341103012552357296195872284851088327147756360948832899952223066413032513135872360613724635985395764522975960382802221775893024507117086851852457207106895872⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 46 0 (.step 7 (.step 16 (.close 31))) (.step 28 (.step 31 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 37)))))) (.step 7 (.step 31 (.close 16)))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 37)))))) (.step 28 (.step 59 (.step 37 (.step 3 (.step 7 (.step 21 (.close 31)))))))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 21 (.close 22))))))) (.step 3 (.step 4 (.step 7 (.step 14 (.step 37 (.step 39 (.step 45 (.close 49))))))))) (.step 3 (.step 31 (.step 16 (.close 37))))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 21 (.step 22 (.close 37)))))))) (.step 5 (.step 16 (.step 31 (.step 7 (.close 16)))))) (.step 31 (.step 28 (.step 49 (.step 31 (.step 50 (.step 3 (.step 21 (.step 31 (.close 37)))))))))) (.step 31 (.step 28 (.step 49 (.close 3))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 4898883310657342436947858505931971705553515434341103012552357296195872284853796012395923681835527219708876064032175917693156873971618961541256477412217657012912915357517311705493750763534503296970522624⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 37 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.step 45 (.step 7 (.step 31 (.close 3)))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 21 (.close 22))))))) (.step 3 (.step 4 (.step 5 (.step 4 (.step 7 (.step 14 (.close 37)))))))) (.step 3 (.step 31 (.step 16 (.close 37))))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 21 (.step 22 (.close 37)))))))) (.step 5 (.step 7 (.step 16 (.step 31 (.close 52)))))) (.step 16 (.step 28 (.step 31 (.step 45 (.step 3 (.step 37 (.step 14 (.step 39 (.step 45 (.close 49))))))))))) (.step 16 (.step 31 (.step 37 (.close 49)))))))) (.run (.step 16 (.step 28 (.step 37 (.step 38 (.step 41 (.split 52 1 (.split 53 1 (.step 37 (.step 3 (.step 7 (.step 21 (.close 31))))) (.step 3 (.step 4 (.step 14 (.close 37))))) (.step 3 (.step 16 (.step 31 (.close 37))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875037076187987961584376921275777874072438102419149160448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 38 0 (.split 45 0 (.split 46 0 (.step 7 (.close 18)) (.step 8 (.step 18 (.step 3 (.close 7))))) (.step 7 (.close 18))) (.step 3 (.step 7 (.step 5 (.step 17 (.close 19)))))) (.step 7 (.step 18 (.close 17)))) (.step 8 (.step 18 (.close 60)))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 19 (.close 20))))))) (.step 8 (.step 56 (.step 73 (.step 56 (.step 3 (.step 7 (.close 18)))))))) (.step 3 (.step 18 (.step 19 (.close 25))))) (.step 4 (.step 7 (.step 18 (.step 17 (.step 19 (.step 17 (.close 25)))))))) (.step 4 (.step 18 (.step 7 (.step 17 (.step 19 (.step 25 (.step 35 (.step 36 (.close 48)))))))))) (.step 18 (.step 8 (.step 50 (.step 18 (.step 50 (.close 3))))))) (.step 18 (.step 8 (.step 49 (.step 18 (.step 49 (.step 3 (.close 25)))))))) (.step 3 (.step 4 (.step 18 (.step 7 (.step 25 (.step 17 (.step 25 (.step 35 (.close 48)))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 41 (.step 49 (.step 50 (.step 7 (.step 19 (.step 20 (.step 25 (.close 51)))))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875037076187987961584376921275777874072438102419149160448⟩
def references : Fin 3 → Box := ![Part12.root, Part14.root, Part15.root]
def proof : Chunks.Proof 3 := (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.step 31 (.split 36 1 (.reuse 1) (.run (.step 37 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 59 1 (.step 37 (.step 7 (.close 31))) (.step 7 (.step 16 (.step 22 (.close 31))))) (.step 28 (.step 31 (.step 37 (.close 3))))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 21 (.close 22))))))) (.step 3 (.step 4 (.step 5 (.step 4 (.step 7 (.step 14 (.close 37)))))))) (.step 3 (.step 31 (.step 16 (.close 37))))) (.step 5 (.step 7 (.step 31 (.step 16 (.step 21 (.step 22 (.close 37)))))))) (.step 5 (.step 7 (.step 16 (.step 31 (.close 52)))))) (.step 16 (.step 28 (.step 31 (.step 39 (.step 45 (.step 49 (.step 39 (.step 3 (.close 14)))))))))) (.step 16 (.step 31 (.step 37 (.close 49))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 3 (.step 7 (.step 41 (.step 3 (.close 7)))))))))))) (.reuse 2))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part14.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 4898883310657342436947858505931971701868005253851316535753964150702423300962214875397026012969633225421226311031900970430060728269399928929405395758990134336023308941934727073055062327584038201061277696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 38 0 (.split 45 0 (.split 46 0 (.step 7 (.close 18)) (.step 8 (.step 18 (.step 3 (.close 7))))) (.step 7 (.close 18))) (.step 3 (.step 7 (.step 5 (.step 17 (.close 19)))))) (.step 7 (.step 18 (.close 17)))) (.step 8 (.step 18 (.step 51 (.step 3 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 19 (.close 20))))))) (.step 8 (.step 36 (.step 51 (.step 56 (.step 3 (.step 7 (.close 18)))))))) (.step 3 (.step 18 (.step 19 (.step 20 (.close 51)))))) (.step 4 (.step 7 (.step 18 (.step 17 (.step 19 (.step 17 (.step 20 (.close 25))))))))) (.step 4 (.step 18 (.step 7 (.step 17 (.step 19 (.step 20 (.step 35 (.step 25 (.close 36)))))))))) (.step 18 (.step 8 (.step 50 (.step 18 (.step 50 (.close 3))))))) (.step 18 (.step 8 (.step 49 (.step 18 (.step 49 (.step 3 (.close 20)))))))) (.step 3 (.step 4 (.step 18 (.step 7 (.step 36 (.step 17 (.step 19 (.step 17 (.step 19 (.step 35 (.close 48)))))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 41 (.step 49 (.step 50 (.step 7 (.step 19 (.step 20 (.step 25 (.close 51)))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 4898883310657342436947858505931971701868005253851316535753964150702423300962214875397026012969633225421226311031900970430060728269399928929405395758988639219848319428249404703471193570054930182069813248⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 38 0 (.split 45 0 (.split 46 0 (.step 7 (.close 18)) (.step 8 (.step 18 (.step 3 (.close 7))))) (.step 7 (.close 18))) (.step 3 (.step 7 (.step 5 (.step 17 (.close 19)))))) (.step 7 (.step 18 (.close 17)))) (.step 8 (.step 18 (.step 50 (.step 3 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 19)))))) (.step 8 (.step 56 (.step 19 (.step 3 (.step 7 (.step 17 (.close 18)))))))) (.step 3 (.step 18 (.close 19)))) (.step 4 (.step 7 (.step 18 (.step 17 (.close 19)))))) (.step 4 (.step 18 (.step 7 (.step 17 (.step 19 (.close 35))))))) (.step 18 (.step 8 (.step 50 (.close 3))))) (.step 18 (.step 8 (.step 49 (.step 18 (.step 49 (.step 3 (.close 19)))))))) (.step 3 (.step 4 (.step 18 (.step 7 (.step 19 (.step 17 (.step 19 (.close 35))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 41 (.step 19 (.close 49))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759868080052731408262533249750005710848⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 19 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.step 25 (.step 7 (.step 18 (.close 3)))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 19)))))) (.step 3 (.step 18 (.close 19)))) (.step 4 (.step 7 (.step 18 (.step 17 (.close 19)))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 19 (.step 35 (.close 52)))))))) (.step 8 (.step 18 (.step 19 (.close 50))))) (.step 8 (.step 18 (.step 49 (.step 19 (.close 3)))))) (.step 3 (.step 4 (.step 7 (.step 18 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 5 (.step 7 (.step 19 (.close 41)))))))))))) (.run (.step 19 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.split 57 1 (.split 59 1 (.step 19 (.step 7 (.close 18))) (.step 7 (.step 18 (.step 17 (.close 19))))) (.step 8 (.step 18 (.step 19 (.close 3))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 19)))))) (.step 3 (.step 18 (.close 19)))) (.step 4 (.step 7 (.step 18 (.step 17 (.close 19)))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 19 (.step 35 (.close 52)))))))) (.step 8 (.step 18 (.step 19 (.close 50))))) (.step 8 (.step 18 (.step 49 (.step 19 (.close 3)))))) (.step 3 (.step 4 (.step 7 (.step 18 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 5 (.step 7 (.step 19 (.close 41))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320922571584929006717384703647616266957972359613695461257201648110924504219351542503247882753563999323379953410744946653723286063917571185556645182701568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 45 1 (.split 59 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.split 30 0 (.split 34 0 (.step 3 (.step 48 (.step 3 (.close 4)))) (.step 3 (.step 4 (.step 3 (.close 14))))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 7 (.step 14 (.close 17))))) (.step 7 (.step 14 (.step 3 (.close 17))))) (.step 8 (.split 17 0 (.step 7 (.step 14 (.step 3 (.close 17)))) (.step 14 (.step 3 (.step 4 (.close 7))))))) (.step 3 (.step 7 (.step 3 (.step 7 (.close 14)))))) (.step 3 (.step 7 (.close 8)))) (.step 4 (.step 44 (.step 48 (.close 14))))) (.step 4 (.step 8 (.step 48 (.close 14))))) (.step 3 (.step 8 (.step 60 (.step 3 (.close 14)))))) (.step 3 (.step 4 (.step 24 (.step 43 (.step 60 (.step 3 (.step 14 (.step 3 (.close 37)))))))))) (.step 3 (.step 5 (.step 18 (.step 3 (.step 34 (.step 3 (.close 48)))))))) (.step 8 (.step 14 (.step 56 (.split 55 1 (.split 59 1 (.step 56 (.step 3 (.step 4 (.close 7)))) (.step 4 (.step 14 (.step 3 (.step 7 (.step 34 (.close 44))))))) (.step 3 (.step 14 (.close 3)))))))) (.step 3 (.step 48 (.close 14)))) (.step 3 (.step 7 (.step 27 (.step 34 (.step 14 (.close 44))))))) (.step 3 (.step 4 (.step 48 (.step 35 (.step 50 (.step 58 (.step 27 (.step 48 (.close 44)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392770705233522178122089021299518645651302247670981370559454974255824896⟩
def references : Fin 1 → Box := ![Part20.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.reuse 0) (.run (.step 3 (.step 34 (.step 4 (.step 34 (.step 4 (.step 48 (.step 49 (.step 58 (.step 27 (.step 34 (.close 44))))))))))))) (.run (.step 49 (.step 8 (.step 50 (.step 3 (.step 14 (.step 50 (.step 3 (.close 14)))))))))) (.run (.step 34 (.step 8 (.step 14 (.step 49 (.step 3 (.step 49 (.step 3 (.close 14)))))))))) (.run (.step 3 (.step 8 (.step 3 (.step 7 (.close 27))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 24 (.step 14 (.step 49 (.step 50 (.step 7 (.step 37 (.step 39 (.step 45 (.close 51))))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 49 (.step 50 (.step 60 (.split 42 1 (.split 53 1 (.step 43 (.step 24 (.split 16 0 (.step 43 (.step 14 (.step 41 (.close 14)))) (.step 3 (.close 14))))) (.step 8 (.step 14 (.close 3)))) (.step 3 (.step 4 (.step 37 (.step 14 (.close 41)))))))))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 28 (.step 41 (.step 43 (.step 49 (.step 50 (.step 51 (.step 14 (.step 7 (.step 37 (.close 39)))))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.step 43 (.step 49 (.step 4 (.step 14 (.step 7 (.step 41 (.step 37 (.step 14 (.step 37 (.close 50)))))))))))))))) (.run (.step 3 (.step 7 (.step 31 (.step 50 (.step 7 (.step 3 (.close 14)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759869378126946041969440382374088015872⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 17 (.step 8 (.step 18 (.step 60 (.step 73 (.step 14 (.split 38 1 (.split 50 1 (.step 14 (.step 3 (.step 7 (.step 14 (.close 17))))) (.step 3 (.step 4 (.step 7 (.step 14 (.step 17 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.close 14))))))))))))) (.run (.step 7 (.step 17 (.step 8 (.step 18 (.step 25 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 50 1 (.step 14 (.split 52 1 (.split 56 1 (.split 59 1 (.step 14 (.step 3 (.step 7 (.close 14)))) (.step 4 (.step 7 (.step 14 (.close 17))))) (.step 3 (.step 5 (.close 14)))) (.step 3 (.step 14 (.step 17 (.step 14 (.close 18))))))) (.step 3 (.step 4 (.step 7 (.step 17 (.step 14 (.close 18))))))) (.step 14 (.close 17))) (.step 14 (.close 17))) (.step 3 (.step 4 (.step 7 (.step 14 (.close 17)))))) (.step 3 (.step 5 (.close 14))))))))))) (.run (.step 7 (.step 17 (.step 8 (.step 18 (.step 19 (.step 35 (.step 14 (.split 38 1 (.split 52 1 (.split 56 1 (.step 19 (.step 3 (.step 7 (.close 14)))) (.step 3 (.step 5 (.close 14)))) (.step 3 (.step 14 (.step 17 (.step 14 (.close 18)))))) (.step 3 (.step 5 (.close 14)))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719444300392772390230188875038574227166225759869379394596642197669783870791221248⟩
def references : Fin 4 → Box := ![Part16.root, Part17.root, Part19.root, Part22.root]
def proof : Chunks.Proof 4 := (.split 10 1 (.split 11 1 (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.reuse 1) (.run (.step 25 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.step 25 (.step 7 (.step 18 (.close 3)))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 19 (.step 20 (.close 19)))))))) (.step 3 (.step 18 (.step 19 (.close 20))))) (.step 4 (.step 7 (.step 18 (.step 17 (.step 19 (.step 17 (.step 20 (.close 25))))))))) (.step 4 (.step 7 (.step 17 (.step 18 (.step 19 (.step 20 (.step 25 (.step 48 (.close 52)))))))))) (.step 8 (.step 18 (.step 19 (.step 20 (.step 3 (.step 25 (.close 50)))))))) (.step 8 (.step 18 (.step 49 (.step 20 (.close 3)))))) (.step 3 (.step 4 (.step 7 (.step 18 (.step 20 (.close 25))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 5 (.step 7 (.step 19 (.step 20 (.step 25 (.step 41 (.close 49)))))))))))))))))) (.reuse 2)) (.reuse 3)) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 11 1 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 3 (.step 7 (.step 49 (.step 7 (.step 3 (.close 41))))))) (.step 3 (.step 7 (.step 14 (.step 3 (.close 7))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part19.excludes
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part23

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part23.excludes
end FiveColour.Packed.ProjectedChunks.Case51
