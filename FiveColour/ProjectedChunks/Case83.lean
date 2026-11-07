module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case83
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496907729085965681469739598109715145987095657528829206996915643125630385520640⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11592891989185051536311, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487664061762293317802547158855163062708886045696, 0⟩]
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
def root : Box := ⟨3221225472, 5783586108473071698929506996965222366134733773348527137630275073014641211963365061407257151770905019981373183719519790822093350474905949501118222832302576361988560489913199369905048662365219176276402332304061453707669143552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 39 0 (.step 55 (.step 40 (.step 55 (.close 3)))) (.step 27 (.step 40 (.close 3)))) (.step 3 (.step 29 (.step 23 (.close 31))))) (.step 3 (.close 23))) (.step 3 (.step 18 (.close 23)))) (.step 18 (.step 3 (.close 21)))) (.step 18 (.step 3 (.close 40)))) (.split 16 0 (.split 34 0 (.split 35 0 (.split 17 0 (.step 23 (.split 22 0 (.step 27 (.step 40 (.close 3))) (.step 3 (.close 55)))) (.step 18 (.close 55))) (.step 23 (.split 24 0 (.split 17 0 (.step 42 (.step 40 (.close 3))) (.step 3 (.close 23))) (.step 23 (.close 29))))) (.step 3 (.step 17 (.close 34)))) (.step 11 (.step 18 (.close 55))))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.split 21 0 (.split 22 0 (.split 24 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 65 0 (.step 23 (.close 31)) (.step 3 (.close 15))) (.step 3 (.close 15))) (.step 21 (.step 3 (.close 23)))) (.step 34 (.step 3 (.close 12)))) (.step 29 (.close 3))) (.step 3 (.close 23))) (.step 3 (.step 18 (.step 15 (.close 23)))))) (.step 18 (.step 22 (.close 40)))) (.step 18 (.step 21 (.close 3)))) (.split 16 0 (.split 17 0 (.step 15 (.step 9 (.step 23 (.close 3)))) (.step 3 (.close 12))) (.step 3 (.close 17))))) (.step 3 (.step 31 (.split 12 0 (.split 16 0 (.split 14 0 (.step 18 (.close 23)) (.step 3 (.close 12))) (.step 7 (.close 18))) (.step 3 (.close 12)))))))
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
def root : Box := ⟨10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579558101483520, 17350758325419215096778723214921340236387974119565902765140055240619506863005372417453778513176160041487847656483139263695400997607936018408437653760653874166357381506631935032601450155235893376603160572629314655342590689280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 74 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 74 (.close 3)) (.step 23 (.step 40 (.close 55)))) (.step 29 (.step 74 (.close 3)))) (.step 31 (.close 55))) (.step 31 (.close 55))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.split 34 0 (.split 36 0 (.split 42 0 (.step 36 (.step 27 (.step 55 (.close 18)))) (.step 18 (.close 29))) (.step 18 (.close 29))) (.step 18 (.close 29)))) (.step 18 (.close 74))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 74 (.close 3)) (.step 12 (.step 29 (.close 27)))) (.step 18 (.close 74))) (.step 18 (.close 61))) (.step 18 (.close 74)))) (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 22 (.step 57 (.step 55 (.close 15)))) (.step 3 (.close 74))) (.step 23 (.close 31))) (.step 18 (.close 22))) (.step 18 (.close 74))) (.step 12 (.close 74))) (.step 12 (.close 3)))) (.step 47 (.split 12 0 (.split 51 0 (.step 74 (.step 11 (.close 3))) (.step 3 (.close 22))) (.step 12 (.step 22 (.step 9 (.close 11))))))) (.step 11 (.step 69 (.step 74 (.close 55))))) (.step 29 (.step 69 (.step 74 (.close 55))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990886533306152125628145825492823296337566082577772889986381197430566508684422447767664866465692745129534045716257442955581951795584904363969809970970264169565042550223534233698971731791056130277376⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 6 0 (.reuse 0) (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 9 (.split 21 0 (.split 34 0 (.step 55 (.step 3 (.close 9))) (.step 9 (.close 11))) (.step 9 (.close 3)))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.close 11))) (.step 3 (.close 11))) (.step 11 (.step 9 (.step 11 (.close 3))))) (.split 30 0 (.split 14 0 (.split 16 0 (.step 9 (.close 11)) (.step 11 (.close 9))) (.step 11 (.close 9))) (.step 3 (.close 9)))))) (.run (.step 11 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.step 77 (.step 23 (.close 3))) (.step 18 (.close 40))) (.step 23 (.close 77))) (.step 23 (.close 77))) (.step 17 (.step 3 (.step 18 (.step 23 (.close 40))))))))) (.run (.step 69 (.step 29 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.step 75 (.step 3 (.close 9))) (.step 9 (.step 75 (.close 3)))) (.step 40 (.close 75))) (.step 38 (.step 18 (.close 75)))) (.step 40 (.close 75))))))) (.reuse 1)) (.run (.step 69 (.split 72 1 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 55))) (.step 3 (.close 55)))))) (.run (.step 3 (.step 74 (.split 72 1 (.step 68 (.step 3 (.step 18 (.close 77)))) (.step 3 (.close 75)))))))
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
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630616877957120, 17350758325419215096788520990895667098404201311933144244572989303597362966874315326085970228087693756778676076885898810676339476574618193537351030323149951683223523782208816630132754075868640642560052588764378170054280216576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 66 (.step 3 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 66 (.close 3)) (.step 12 (.step 40 (.close 3)))) (.step 29 (.step 66 (.close 31)))) (.step 31 (.close 55))) (.step 31 (.close 55))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 47 (.split 34 0 (.split 36 0 (.step 12 (.split 16 0 (.split 30 0 (.split 35 0 (.step 27 (.close 55)) (.step 23 (.close 66))) (.step 18 (.close 32))) (.step 18 (.close 27)))) (.step 18 (.close 29))) (.step 18 (.close 29))))) (.step 18 (.close 66))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 12 (.close 66)) (.step 11 (.step 12 (.close 66)))) (.step 18 (.close 12))) (.step 18 (.close 12)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 12 (.step 29 (.close 66))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.close 66)))) (.step 47 (.split 16 0 (.split 17 0 (.step 12 (.split 21 0 (.split 22 0 (.step 9 (.step 15 (.step 55 (.close 21)))) (.step 11 (.close 31))) (.step 11 (.close 9)))) (.step 11 (.close 31))) (.step 11 (.close 31))))) (.step 66 (.close 55))) (.step 66 (.close 55))) (.step 66 (.close 77))) (.step 66 (.close 75))) (.step 66 (.close 68)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416711979597824, 17350752809766951994801222262167459667490405703827949732307775751417902831348056611951274302598930591847338260895977970543817679677004127202578488179705576217789426118419444134050647121165585532211735584674116854664346468352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 74 1 (.split 67 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 72 1 (.split 6 0 (.split 12 0 (.split 22 0 (.split 30 0 (.split 39 0 (.split 40 0 (.split 49 0 (.step 40 (.close 3)) (.step 27 (.step 40 (.close 3)))) (.step 27 (.close 40))) (.step 27 (.step 40 (.close 55)))) (.step 3 (.close 61))) (.step 3 (.close 61))) (.step 34 (.step 27 (.step 40 (.close 3))))) (.split 22 0 (.step 22 (.step 9 (.step 27 (.step 40 (.close 3))))) (.step 3 (.close 61)))) (.step 40 (.close 3))) (.step 27 (.step 22 (.step 3 (.close 23))))) (.step 27 (.step 36 (.step 18 (.close 61))))) (.step 27 (.step 40 (.split 35 0 (.split 63 0 (.step 61 (.close 18)) (.step 18 (.close 55))) (.step 18 (.close 21)))))) (.step 27 (.step 34 (.step 40 (.step 61 (.close 40)))))) (.step 27 (.step 3 (.step 40 (.step 61 (.step 3 (.close 12))))))) (.step 11 (.step 36 (.step 40 (.split 34 0 (.split 42 0 (.step 61 (.close 3)) (.step 18 (.step 22 (.close 61)))) (.step 22 (.close 74))))))) (.step 3 (.close 55))) (.step 11 (.step 44 (.step 61 (.close 40))))) (.step 3 (.close 61))) (.step 11 (.step 32 (.step 40 (.step 51 (.step 74 (.step 77 (.split 65 1 (.split 34 0 (.step 42 (.step 61 (.step 23 (.step 40 (.close 3))))) (.step 18 (.step 23 (.close 61)))) (.step 3 (.close 61)))))))))) (.step 11 (.step 34 (.step 40 (.step 51 (.step 55 (.step 67 (.step 74 (.step 27 (.step 66 (.step 61 (.step 23 (.step 3 (.close 77)))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890818020781845656318743159238278478607442105959944316732927794170584719760996148346122905981953574456552894112933589755394193762804154529902148496429080296531611877376⟩
def references : Fin 3 → Box := ![Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 3 := (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 3 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 24 0 (.step 67 (.step 3 (.step 18 (.close 23)))) (.step 47 (.step 67 (.step 23 (.step 3 (.close 27)))))) (.split 10 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 67 (.close 3)) (.step 18 (.close 67))) (.step 18 (.close 23))) (.step 18 (.close 67))) (.step 12 (.close 3)))) (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 32 (.step 21 (.step 29 (.step 66 (.step 3 (.close 67)))))) (.step 18 (.close 67))) (.step 18 (.close 21))) (.step 12 (.close 67))) (.step 12 (.close 3)))) (.step 47 (.split 12 0 (.step 67 (.step 11 (.close 9))) (.step 12 (.step 21 (.step 9 (.close 11))))))) (.step 67 (.close 55))) (.step 67 (.close 77))) (.step 67 (.close 75))) (.step 67 (.close 68))))))) (.reuse 1)) (.run (.step 3 (.step 44 (.step 26 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.step 62 (.step 40 (.step 55 (.close 3)))) (.step 9 (.step 62 (.close 3)))) (.step 26 (.close 62))) (.step 3 (.close 62))) (.step 55 (.close 62))) (.step 27 (.step 44 (.step 53 (.step 3 (.close 62)))))) (.step 27 (.step 44 (.step 52 (.step 55 (.close 18)))))) (.step 55 (.close 74))) (.step 3 (.close 7))) (.step 55 (.close 67))) (.step 66 (.step 55 (.close 66))))))))) (.step 40 (.split 59 1 (.reuse 2) (.run (.step 55 (.step 61 (.close 62)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 11567177737984785663036746082060580323243797207111077065483096964071143339321865075296738322975050392475855576964005627532299539292413130596443474136449673593748284323906887311403060642179686178984201570283533805513766600704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 72 1 (.split 67 1 (.split 71 1 (.split 10 0 (.split 12 0 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 74 1 (.split 14 0 (.split 16 0 (.split 36 0 (.split 17 0 (.step 57 (.close 3)) (.step 3 (.close 23))) (.step 9 (.step 3 (.close 57)))) (.step 21 (.step 9 (.close 23)))) (.split 24 0 (.split 36 0 (.split 39 0 (.step 15 (.step 9 (.close 23))) (.step 21 (.step 9 (.close 23)))) (.step 3 (.close 23))) (.step 23 (.close 27)))) (.step 23 (.close 3))) (.step 9 (.step 21 (.step 40 (.close 57))))) (.step 9 (.step 31 (.step 3 (.step 23 (.close 21)))))) (.step 3 (.step 9 (.step 31 (.step 23 (.close 21)))))) (.step 9 (.step 31 (.step 3 (.close 23))))) (.step 9 (.step 23 (.split 34 0 (.split 35 0 (.split 36 0 (.split 16 0 (.split 17 0 (.step 15 (.close 57)) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 15 (.close 57))) (.step 21 (.close 57))) (.step 15 (.close 3)))))) (.step 9 (.step 3 (.step 15 (.step 12 (.step 3 (.close 23))))))) (.step 22 (.step 23 (.step 29 (.split 16 0 (.split 22 0 (.step 57 (.close 3)) (.step 23 (.close 57))) (.step 21 (.close 74))))))) (.step 3 (.close 55))) (.step 26 (.step 29 (.step 57 (.close 23))))) (.step 3 (.close 57))) (.step 21 (.step 23 (.step 29 (.step 51 (.step 55 (.step 68 (.step 74 (.step 9 (.step 67 (.step 57 (.step 3 (.step 26 (.close 55)))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923629336920627398440563190915400398397339482451051576189760481847083608730453220539741619073417438104448404755484139055270197723056883338342897618283134976⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 51 1 (.split 54 1 (.reuse 0) (.step 23 (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 1) (.run (.step 12 (.step 23 (.step 29 (.step 51 (.step 55 (.step 67 (.step 74 (.step 75 (.split 65 1 (.split 16 0 (.step 15 (.step 57 (.step 23 (.close 57)))) (.step 21 (.step 9 (.step 15 (.step 18 (.close 23)))))) (.step 3 (.close 57))))))))))))) (.run (.step 55 (.step 57 (.close 62))))) (.run (.step 3 (.step 22 (.step 23 (.step 57 (.split 16 0 (.split 22 0 (.split 10 0 (.step 57 (.close 12)) (.step 3 (.step 9 (.close 61)))) (.step 23 (.close 57))) (.step 3 (.step 21 (.close 61)))))))))))) (.run (.step 51 (.split 67 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 58 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 54))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455307164305180212048509908272658497200365389373254310807350991731375619988988986794263464177949112052979847447429300311412582620594176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 52 (.step 57 (.step 61 (.split 51 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 52 (.step 55 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 12 (.close 40))) (.step 9 (.step 3 (.step 40 (.close 52))))) (.step 9 (.step 53 (.step 52 (.step 12 (.close 40)))))) (.step 3 (.step 9 (.step 34 (.step 18 (.step 15 (.close 52))))))) (.step 55 (.close 52))) (.step 3 (.step 23 (.close 52)))) (.step 55 (.close 52))) (.step 53 (.step 55 (.close 52)))) (.step 34 (.step 52 (.close 40)))))) (.step 27 (.step 34 (.step 44 (.step 23 (.step 55 (.close 52))))))) (.step 9 (.step 12 (.step 26 (.step 40 (.step 55 (.step 52 (.close 3)))))))) (.step 55 (.close 74))) (.step 3 (.close 70))) (.step 55 (.close 67))) (.step 3 (.close 54))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312709644568453678229065101026783367772262247405062440501332690536849231604598045509544126761320332136042229851223118556240568909824⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 32 (.step 57 (.step 61 (.split 51 1 (.split 63 1 (.split 67 1 (.split 71 1 (.step 62 (.split 72 1 (.split 74 1 (.step 55 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 53 (.step 21 (.step 9 (.close 40)))) (.step 9 (.step 3 (.step 40 (.close 53))))) (.step 9 (.step 21 (.step 52 (.step 3 (.step 29 (.step 15 (.close 53)))))))) (.step 55 (.close 53))) (.step 3 (.step 9 (.close 53)))) (.step 55 (.close 53))) (.step 21 (.step 18 (.close 53)))) (.step 55 (.step 53 (.close 3))))) (.step 23 (.step 27 (.step 32 (.step 44 (.step 55 (.step 53 (.close 3)))))))) (.step 9 (.step 21 (.step 26 (.step 40 (.step 55 (.close 53)))))))) (.step 55 (.close 74))) (.step 3 (.close 70))) (.step 55 (.close 66))) (.step 3 (.close 54)))))))) (.reuse 1)) (.run (.step 9 (.step 27 (.step 47 (.step 53 (.step 62 (.split 51 1 (.split 67 1 (.split 49 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.close 47))) (.step 3 (.close 47))) (.step 3 (.step 9 (.close 52)))) (.step 3 (.close 46))) (.step 3 (.close 46))))))))))
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
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350752809766951994801222262167459667490405711932472327778465123512456144023820706321008136959939265074425266087737677524681936611786636441972673378957094019808860823554562046530115655365825845612602153452484029640182071296⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 51 1 (.split 58 1 (.split 67 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 72 1 (.split 6 0 (.split 12 0 (.step 42 (.close 40)) (.step 32 (.step 21 (.step 27 (.step 34 (.close 40)))))) (.step 32 (.step 21 (.split 22 0 (.step 9 (.step 27 (.close 40))) (.step 3 (.close 11)))))) (.step 40 (.close 3))) (.step 27 (.step 21 (.step 3 (.close 23))))) (.step 27 (.step 36 (.step 18 (.close 42))))) (.step 40 (.split 63 0 (.step 42 (.close 3)) (.step 18 (.close 42))))) (.step 27 (.step 34 (.step 40 (.step 42 (.close 18)))))) (.step 27 (.step 3 (.step 42 (.step 3 (.close 12)))))) (.step 3 (.close 12))) (.step 42 (.close 40))) (.step 3 (.close 42))) (.step 42 (.close 77))) (.step 11 (.step 32 (.step 36 (.step 40 (.step 77 (.split 34 0 (.step 42 (.step 61 (.step 23 (.step 40 (.close 3))))) (.step 18 (.step 23 (.close 42)))))))))) (.step 3 (.close 42))) (.step 11 (.step 32 (.step 67 (.split 34 0 (.split 36 0 (.step 42 (.close 15)) (.step 21 (.close 42))) (.step 21 (.close 67))))))) (.step 11 (.step 12 (.step 32 (.step 34 (.step 40 (.step 55 (.step 67 (.step 74 (.step 77 (.split 65 1 (.split 36 0 (.step 42 (.step 18 (.close 23))) (.step 18 (.step 23 (.close 42)))) (.step 3 (.close 42))))))))))))) (.step 3 (.step 27 (.step 42 (.step 44 (.step 32 (.step 40 (.close 55)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158554670789637782293759363827451745685366136982614935631476892068509560743549806016296602250505857139920051634176⟩
def references : Fin 2 → Box := ![Part9.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 44 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 58 1 (.step 31 (.close 7)) (.step 3 (.close 40))) (.step 3 (.step 29 (.step 31 (.close 12))))) (.step 31 (.close 40))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 9 (.step 18 (.step 29 (.step 31 (.close 12)))))) (.step 9 (.step 31 (.close 40)))) (.step 31 (.close 53))) (.step 31 (.close 52)))))) (.run (.step 3 (.step 68 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 31 (.step 68 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.split 74 1 (.step 43 (.split 71 1 (.step 3 (.step 27 (.step 18 (.close 23)))) (.step 18 (.step 23 (.close 12))))) (.step 23 (.close 77)))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 3 (.step 9 (.step 27 (.step 31 (.close 12)))))))) (.step 27 (.step 31 (.step 61 (.close 43))))) (.step 31 (.step 27 (.close 57)))) (.step 3 (.step 31 (.close 53)))) (.step 3 (.step 31 (.close 52)))))))) (.step 27 (.step 40 (.step 44 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.reuse 1) (.run (.step 3 (.step 21 (.step 23 (.step 32 (.step 36 (.step 40 (.step 61 (.step 62 (.split 22 0 (.step 9 (.step 27 (.step 57 (.close 40)))) (.step 23 (.close 42))))))))))))) (.run (.step 21 (.step 32 (.step 42 (.close 3)))))) (.run (.step 42 (.close 52)))) (.run (.step 24 (.step 27 (.step 42 (.step 31 (.step 42 (.close 43))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372461800561940358166010287114963594769940842730607780554125630303935445787410153145788539732897577488613376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 31 (.step 32 (.step 38 (.step 57 (.step 66 (.step 74 (.split 36 1 (.split 42 1 (.split 49 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 74 1 (.step 21 (.split 39 1 (.split 51 1 (.step 75 (.split 54 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 38 (.step 55 (.step 38 (.step 21 (.step 9 (.close 55)))))) (.step 21 (.step 31 (.close 23)))) (.step 40 (.close 38))) (.step 21 (.step 18 (.close 38)))) (.step 40 (.close 38)))) (.step 3 (.close 38))) (.step 21 (.step 32 (.close 67)))) (.step 66 (.close 38))) (.step 57 (.close 38)))) (.step 3 (.close 38))) (.step 32 (.close 3)))) (.step 23 (.step 32 (.step 66 (.step 67 (.step 69 (.step 40 (.step 38 (.close 77))))))))) (.step 3 (.step 21 (.close 38)))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 40 (.step 38 (.close 3)))))))) (.step 21 (.step 40 (.step 27 (.close 61))))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 32 (.step 55 (.step 57 (.step 61 (.split 58 1 (.step 75 (.split 71 1 (.step 52 (.step 29 (.step 38 (.close 3)))) (.step 12 (.close 55)))) (.step 22 (.step 27 (.step 32 (.close 52)))))))))))))) (.step 31 (.close 3))) (.step 31 (.close 39))))))))))))
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
def root : Box := ⟨3533694129556768659166595001485837031654967793751237916243212405806465024, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496907729082592397127231122727219099846906298401205927679817257769935654879232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 27 (.step 29 (.step 27 (.split 40 1 (.split 54 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 51 1 (.split 30 0 (.split 72 1 (.split 6 0 (.split 12 0 (.step 27 (.close 15)) (.step 34 (.close 27))) (.split 12 0 (.split 34 0 (.step 27 (.close 9)) (.step 3 (.close 29))) (.step 34 (.step 27 (.close 9))))) (.step 29 (.close 27))) (.step 27 (.step 3 (.close 9)))) (.step 3 (.close 12))) (.step 3 (.close 29))) (.step 3 (.close 29))) (.step 29 (.close 27))) (.step 3 (.close 29))) (.step 11 (.step 29 (.step 36 (.split 34 0 (.split 42 0 (.step 27 (.close 3)) (.step 18 (.step 23 (.close 27)))) (.step 18 (.step 23 (.close 74)))))))) (.step 3 (.close 27))) (.step 11 (.step 29 (.step 32 (.step 67 (.split 65 1 (.split 34 0 (.split 36 0 (.step 27 (.step 36 (.step 27 (.close 23)))) (.step 23 (.close 67))) (.step 29 (.close 27))) (.step 3 (.close 27)))))))) (.step 11 (.step 12 (.step 18 (.step 27 (.step 29 (.step 34 (.step 66 (.split 24 2 (.step 67 (.step 74 (.split 65 1 (.split 36 0 (.step 27 (.close 21)) (.step 23 (.step 27 (.close 29)))) (.step 3 (.close 27))))) (.step 27 (.close 29))))))))))) (.step 3 (.step 29 (.step 36 (.split 34 0 (.split 42 0 (.split 10 0 (.step 27 (.close 9)) (.step 3 (.step 9 (.close 27)))) (.step 23 (.step 26 (.close 27)))) (.step 3 (.step 15 (.step 23 (.close 27))))))))) (.step 27 (.close 3)))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496907729082592397127231122727219099846906298401205927679817257769935654879232⟩
def references : Fin 3 → Box := ![Part11.root, Part12.root, Part13.root]
def proof : Chunks.Proof 3 := (.split 24 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 36 (.step 57 (.step 74 (.step 75 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 74 1 (.split 39 1 (.split 54 1 (.split 58 1 (.step 31 (.close 7)) (.step 22 (.close 40))) (.step 22 (.close 31))) (.step 3 (.close 40))) (.step 31 (.close 36))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 9 (.step 22 (.step 26 (.step 29 (.step 31 (.close 12))))))) (.step 31 (.close 53))) (.step 31 (.close 52)))))))))) (.reuse 1)) (.run (.step 7 (.step 34 (.step 66 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 39 1 (.split 58 1 (.step 31 (.close 7)) (.step 3 (.close 40))) (.step 3 (.close 40))) (.step 31 (.close 34))) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 34))) (.step 15 (.step 31 (.close 34)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.close 37))))))))) (.run (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.step 18 (.step 31 (.split 63 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 31))))) (.reuse 2))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496907729085965681469739595113636786671148866936420536204366096489800303378432⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 18 (.step 26 (.step 27 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.split 72 1 (.split 24 1 (.split 54 1 (.step 18 (.close 7)) (.step 3 (.close 23))) (.step 11 (.step 18 (.close 12)))) (.step 18 (.close 23))) (.step 18 (.close 74))))) (.step 18 (.close 66))) (.step 18 (.close 23))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 66 (.step 38 (.close 67)))))))))) (.run (.step 43 (.step 68 (.split 24 1 (.split 35 1 (.split 39 1 (.step 31 (.split 49 1 (.split 50 1 (.split 54 1 (.step 18 (.step 68 (.split 58 1 (.split 59 1 (.split 63 1 (.step 43 (.split 64 1 (.step 3 (.split 72 1 (.step 24 (.split 71 1 (.step 3 (.step 9 (.step 18 (.close 15)))) (.step 18 (.close 74)))) (.step 9 (.step 18 (.step 31 (.close 74)))))) (.step 18 (.close 67)))) (.step 18 (.close 66))) (.step 3 (.step 18 (.close 62)))) (.step 18 (.step 3 (.close 61)))))) (.step 24 (.step 57 (.close 24)))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52))))) (.step 18 (.step 24 (.step 27 (.step 3 (.close 42)))))) (.step 18 (.step 21 (.step 31 (.close 38))))) (.step 18 (.close 27)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496907729085965681469739598109715143199499849253974443272746286784462016479232⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 61 (.step 74 (.step 77 (.split 22 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.step 7 (.step 67 (.split 72 1 (.split 24 1 (.split 54 1 (.split 58 1 (.split 64 1 (.step 18 (.close 7)) (.step 11 (.close 18))) (.step 11 (.close 18))) (.step 3 (.close 22))) (.step 18 (.close 22))) (.step 18 (.close 22))))) (.step 18 (.close 66))) (.step 18 (.close 62))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 38 (.close 66)))) (.step 18 (.close 7)))))))))) (.run (.step 7 (.step 21 (.step 42 (.step 67 (.step 77 (.split 17 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 71 1 (.split 72 1 (.split 24 1 (.split 39 1 (.split 54 1 (.step 18 (.close 7)) (.step 3 (.close 23))) (.step 11 (.step 18 (.close 12)))) (.step 18 (.close 21))) (.step 18 (.close 21))) (.step 18 (.close 74))) (.step 18 (.close 66))) (.step 18 (.close 62))) (.step 18 (.close 61))) (.step 18 (.step 42 (.close 53)))) (.step 18 (.step 42 (.close 52)))) (.step 18 (.step 38 (.close 66)))) (.step 18 (.close 19))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2787593149816327892691964784081048409473024, 11567177732598406499846312727330591355628391062750984382345349645167653573767736004321491189045763418602092387097559571172149971579000475362954913656775050231439244585658261849177089143257281933417973666811115246892701712384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.split 36 1 (.step 34 (.split 39 1 (.split 42 1 (.split 51 1 (.split 58 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 11 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.step 17 (.step 55 (.step 17 (.step 34 (.step 3 (.step 17 (.close 3))))))) (.step 18 (.close 17))) (.step 23 (.close 17))) (.step 23 (.close 17))) (.step 17 (.step 3 (.step 17 (.close 12)))))) (.step 3 (.close 17))) (.step 67 (.close 17))) (.step 12 (.step 34 (.close 66)))) (.step 61 (.close 17))) (.step 3 (.close 17))) (.step 31 (.close 17))) (.step 42 (.close 17)))) (.step 31 (.close 17))) (.step 31 (.close 17))) (.step 3 (.close 17))) (.step 31 (.step 40 (.step 66 (.step 67 (.step 69 (.step 23 (.step 74 (.step 17 (.close 32)))))))))) (.step 3 (.step 18 (.step 17 (.close 34))))) (.step 3 (.step 27 (.step 34 (.step 23 (.step 42 (.step 44 (.step 17 (.close 3))))))))) (.step 23 (.step 9 (.step 31 (.step 34 (.close 57)))))) (.step 3 (.step 27 (.step 32 (.step 34 (.step 42 (.step 53 (.step 55 (.step 57 (.step 61 (.split 54 1 (.step 77 (.split 71 1 (.step 53 (.step 11 (.step 17 (.close 3)))) (.step 17 (.close 53)))) (.step 9 (.step 12 (.close 23)))))))))))))) (.step 23 (.step 31 (.close 17)))))
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
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663036746082051455442008552816673794722271692782290327951654226678303323576171811896380297114918018101460105957015972911692478687812665051499507543406591200144800115024582998961246424226389564401880064327680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 71 1 (.split 72 1 (.split 14 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 51 1 (.split 54 1 (.split 16 1 (.split 17 1 (.step 26 (.split 67 1 (.split 10 0 (.split 12 2 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 74 1 (.split 14 0 (.split 16 0 (.split 36 0 (.split 17 0 (.step 9 (.step 12 (.step 15 (.close 40)))) (.step 3 (.close 23))) (.step 9 (.step 3 (.step 15 (.close 21))))) (.step 21 (.step 3 (.close 15)))) (.split 24 0 (.step 15 (.close 17)) (.step 12 (.close 3)))) (.step 23 (.close 3))) (.step 21 (.step 23 (.step 15 (.close 23))))) (.step 9 (.step 31 (.close 15)))) (.step 3 (.step 15 (.step 3 (.close 23))))) (.step 9 (.step 18 (.step 15 (.close 3))))) (.step 9 (.step 23 (.split 34 0 (.split 35 0 (.split 36 0 (.split 16 0 (.step 15 (.close 18)) (.step 3 (.close 23))) (.step 15 (.close 3))) (.step 15 (.close 18))) (.step 15 (.close 3)))))) (.step 9 (.step 3 (.close 15)))) (.step 3 (.close 9)))) (.step 3 (.close 22))) (.step 3 (.close 21))) (.step 15 (.close 23))) (.step 3 (.close 15))) (.step 3 (.step 15 (.close 31)))) (.step 9 (.step 22 (.step 15 (.close 31))))) (.step 15 (.close 31))) (.step 3 (.close 15))) (.step 12 (.step 3 (.close 17)))) (.step 15 (.step 18 (.close 75)))) (.step 12 (.step 22 (.step 23 (.step 29 (.step 31 (.step 75 (.split 16 0 (.step 15 (.step 57 (.step 23 (.step 3 (.close 15))))) (.step 21 (.step 15 (.close 3))))))))))) (.step 3 (.close 15))))
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
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663036746082060589234260628508573550642339214465506091036753254407983735516328994222704777916226503611279901229167747498779607244739577768323667439531796450960236945838464689959349246641919817234899510755328⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 12 (.step 21 (.step 23 (.step 29 (.step 31 (.step 32 (.step 55 (.step 57 (.step 74 (.step 75 (.split 65 1 (.split 12 2 (.step 66 (.step 9 (.step 40 (.step 15 (.close 3))))) (.step 15 (.close 18))) (.step 3 (.close 15))))))))))))))) (.run (.step 12 (.step 29 (.step 31 (.step 66 (.split 16 0 (.split 17 0 (.step 15 (.close 21)) (.step 22 (.close 15))) (.step 21 (.step 15 (.close 18)))))))))) (.run (.step 3 (.step 9 (.step 15 (.step 23 (.step 26 (.step 12 (.step 23 (.close 55)))))))))) (.run (.step 3 (.step 12 (.step 22 (.step 23 (.step 34 (.step 40 (.step 57 (.step 62 (.split 16 0 (.step 9 (.step 27 (.step 15 (.step 57 (.step 23 (.close 15)))))) (.step 3 (.step 21 (.close 15)))))))))))))) (.run (.step 15 (.step 22 (.step 26 (.close 53)))))) (.run (.step 12 (.step 15 (.step 26 (.close 52)))))) (.run (.step 24 (.step 31 (.step 3 (.close 15)))))) (.run (.step 3 (.step 12 (.step 21 (.step 23 (.step 32 (.step 34 (.step 40 (.step 43 (.step 57 (.step 61 (.step 62 (.split 40 1 (.split 17 0 (.step 9 (.step 27 (.step 15 (.step 3 (.close 23))))) (.step 3 (.step 22 (.close 15)))) (.step 3 (.step 27 (.step 15 (.close 23)))))))))))))))))) (.run (.step 15 (.step 22 (.step 26 (.step 29 (.step 31 (.close 38))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496907729085965681469739598109715145987095657526293905796456878479627765415936⟩
def references : Fin 3 → Box := ![Part16.root, Part17.root, Part19.root]
def proof : Chunks.Proof 3 := (.split 12 1 (.split 14 1 (.reuse 0) (.step 3 (.step 17 (.step 18 (.step 31 (.step 27 (.step 42 (.step 61 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.reuse 1) (.run (.step 31 (.step 32 (.step 38 (.step 40 (.step 57 (.step 66 (.step 67 (.step 74 (.split 54 1 (.split 58 1 (.split 74 1 (.split 72 1 (.split 6 0 (.step 23 (.step 17 (.close 31))) (.step 9 (.close 11))) (.step 29 (.close 38))) (.step 17 (.close 23))) (.step 17 (.close 38))) (.step 9 (.step 12 (.step 23 (.close 26))))))))))))))) (.run (.step 17 (.step 3 (.close 18))))) (.run (.step 17 (.step 3 (.close 18))))) (.run (.step 18 (.step 3 (.close 19)))))))))))))))) (.step 18 (.step 15 (.step 23 (.step 31 (.split 21 1 (.split 24 1 (.reuse 2) (.run (.step 3 (.step 12 (.step 27 (.step 29 (.step 34 (.split 16 0 (.split 17 0 (.step 57 (.split 22 0 (.step 9 (.split 36 0 (.step 27 (.close 15)) (.step 3 (.step 22 (.close 29))))) (.step 3 (.step 23 (.close 15))))) (.step 3 (.step 22 (.step 15 (.close 18))))) (.step 3 (.step 21 (.close 27))))))))))) (.run (.step 9 (.step 24 (.step 15 (.step 24 (.close 27))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2305843012434919424, 11567166706680259459057249741293517029996089433841408237039293467959091136560183730026882956880633323148681721217682532873787088498849689514343927818828008389916054155173021439328255538438641768432808560052374028249605341184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.split 58 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 14 1 (.split 16 1 (.split 10 1 (.split 30 1 (.split 36 1 (.split 42 1 (.split 17 1 (.step 26 (.split 51 1 (.step 9 (.split 30 0 (.split 74 1 (.split 6 2 (.split 12 0 (.split 14 0 (.split 16 0 (.step 9 (.close 11)) (.step 11 (.close 9))) (.step 11 (.close 9))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 11 (.close 9))) (.step 9 (.step 3 (.close 11))))) (.step 3 (.close 9)))) (.step 3 (.close 11))) (.step 9 (.close 3))) (.step 9 (.close 3))) (.step 3 (.close 9))) (.step 3 (.close 9))) (.step 3 (.close 11))) (.step 11 (.close 9))) (.step 11 (.step 22 (.step 29 (.step 31 (.split 16 0 (.split 10 0 (.step 9 (.close 11)) (.step 9 (.close 3))) (.step 11 (.close 9)))))))) (.step 3 (.close 9))) (.step 9 (.step 11 (.step 21 (.step 29 (.step 32 (.split 6 2 (.step 74 (.split 10 0 (.split 17 0 (.split 65 1 (.step 9 (.close 11)) (.step 3 (.close 9))) (.step 11 (.close 9))) (.step 9 (.close 3)))) (.step 9 (.close 11))))))))) (.step 11 (.step 12 (.step 29 (.step 31 (.step 66 (.split 64 1 (.split 65 1 (.split 16 0 (.split 17 0 (.step 9 (.step 22 (.step 9 (.close 11)))) (.step 11 (.close 9))) (.step 11 (.close 9))) (.step 3 (.close 9))) (.step 21 (.step 32 (.step 66 (.close 3))))))))))) (.step 3 (.step 11 (.step 22 (.split 16 0 (.split 22 0 (.split 10 0 (.step 9 (.close 11)) (.step 9 (.close 11))) (.step 11 (.close 9))) (.step 11 (.close 9))))))) (.step 24 (.step 9 (.close 31)))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496907729085965681469739598109715145987095657528829206996915643125630385520640⟩
def references : Fin 2 → Box := ![Part20.root, Part21.root]
def proof : Chunks.Proof 2 := (.split 6 1 (.split 10 1 (.reuse 0) (.run (.split 12 1 (.split 14 1 (.split 24 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.step 18 (.step 31 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))))) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 18))) (.step 3 (.close 17))) (.step 3 (.close 31))))) (.step 3 (.step 9 (.step 11 (.step 9 (.step 31 (.split 24 1 (.split 39 1 (.reuse 1) (.run (.step 3 (.step 9 (.step 11 (.step 21 (.step 32 (.step 42 (.step 43 (.split 40 1 (.split 6 2 (.split 34 0 (.step 61 (.split 14 0 (.split 17 0 (.step 9 (.close 11)) (.step 11 (.close 9))) (.step 11 (.close 9)))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11)))))))))))) (.run (.step 9 (.step 11 (.step 27 (.split 10 0 (.split 30 0 (.split 65 0 (.split 6 2 (.split 12 0 (.split 34 0 (.split 35 0 (.step 27 (.close 9)) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part22.excludes
end FiveColour.Packed.ProjectedChunks.Case83
