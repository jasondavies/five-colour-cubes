module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case82
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439027885657660779310766230433955840⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨3221225472, 5783586108473071698929506996965222366134733773348527137630275073014641211963365061407257151770905019981373183719519790822093350474905949501118224684974237311982908882719376211410831396169146342628551344667283974116450762752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 55 (.step 40 (.split 26 0 (.step 55 (.close 3)) (.step 27 (.close 29))))) (.step 29 (.step 3 (.step 23 (.close 31))))) (.step 3 (.step 23 (.close 3)))) (.step 18 (.step 23 (.close 3)))) (.step 18 (.step 23 (.close 3)))) (.step 3 (.step 23 (.close 24)))) (.split 16 0 (.step 23 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 27 (.step 40 (.close 3))) (.step 3 (.close 40))) (.step 3 (.step 23 (.close 17)))) (.step 3 (.close 23))) (.step 3 (.step 12 (.close 23))))) (.step 11 (.step 18 (.close 21))))) (.split 14 0 (.split 16 0 (.step 9 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 40 (.step 15 (.step 3 (.close 12)))) (.step 15 (.step 3 (.step 15 (.close 23))))) (.step 31 (.close 32))) (.step 23 (.step 3 (.close 15)))) (.step 3 (.step 15 (.step 23 (.close 21))))) (.step 18 (.step 22 (.close 23))))) (.step 18 (.step 21 (.close 3)))) (.step 23 (.split 16 0 (.step 15 (.step 23 (.close 3))) (.step 3 (.close 12)))))) (.step 18 (.step 31 (.split 12 0 (.split 14 0 (.split 16 0 (.step 18 (.close 23)) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 3 (.step 12 (.close 3))))))))
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
def root : Box := ⟨10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579558101483520, 17350758325419215096778723214921340236387974119565902765140055240619506863005372417453778513176160041487847656483139263695400997607936018408437655613325535116351729899438111874107232889039820542955310793917203868875940167680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.split 12 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 31)) (.step 29 (.close 74))) (.step 29 (.step 74 (.close 3)))) (.step 29 (.step 31 (.close 55)))) (.step 31 (.close 74))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.step 47 (.step 74 (.close 3)))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 9 (.step 29 (.step 57 (.step 55 (.close 15))))) (.step 23 (.close 74))) (.step 23 (.close 31))) (.step 22 (.close 18))) (.step 31 (.step 23 (.close 18))))) (.split 16 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 8 0 (.split 54 0 (.step 74 (.close 3)) (.step 12 (.step 23 (.close 31)))) (.step 11 (.close 74))) (.step 11 (.step 3 (.close 74)))) (.step 18 (.close 74))) (.step 18 (.close 23))) (.step 18 (.close 74)))) (.split 8 0 (.step 31 (.step 66 (.step 18 (.close 74)))) (.step 11 (.close 74)))) (.step 11 (.step 69 (.step 74 (.close 55))))) (.step 29 (.step 69 (.step 74 (.close 55))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990886533306152125628145825492823296337566082577772889986381197430566508684422447767664866465692745129534045716257442957434623456534898712362616147811769952298846477389886383920259621004589479755776⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 8 0 (.reuse 0) (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.step 23 (.split 22 0 (.split 34 0 (.split 36 0 (.step 27 (.step 55 (.close 3))) (.step 9 (.close 11))) (.step 3 (.close 40))) (.step 3 (.close 9))))) (.step 3 (.close 11))) (.step 11 (.step 3 (.close 9)))) (.step 11 (.step 9 (.split 34 0 (.step 11 (.close 3)) (.step 3 (.close 9)))))) (.split 10 0 (.split 14 0 (.step 9 (.close 11)) (.step 11 (.close 9))) (.step 3 (.close 9)))))) (.run (.step 11 (.split 26 0 (.split 34 0 (.split 35 0 (.step 77 (.split 36 0 (.step 77 (.step 3 (.close 12))) (.step 18 (.close 23)))) (.step 23 (.close 77))) (.step 3 (.step 17 (.step 18 (.close 77))))) (.step 23 (.close 77)))))) (.run (.step 69 (.step 29 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 75 (.step 3 (.close 12))) (.step 18 (.close 75))) (.step 18 (.close 75))) (.step 40 (.close 75))) (.step 40 (.close 75))))))) (.reuse 1)) (.run (.step 69 (.split 72 1 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 55))) (.step 3 (.close 55)))))) (.run (.step 3 (.step 74 (.split 72 1 (.split 74 1 (.split 8 0 (.step 31 (.step 68 (.step 3 (.close 12)))) (.step 3 (.close 11))) (.step 3 (.close 77))) (.step 3 (.close 75)))))))
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
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630616877957120, 17350758325419215096788520990895667098404201311933144244572989303597362966874315326085970228087693756778676076885898810676339476574618193537351032175821612633217872175014993471638536809672567808912202810052267383587629694976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 66 (.step 3 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 64 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 12 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 31)) (.step 29 (.step 3 (.close 66)))) (.step 29 (.step 66 (.close 31)))) (.step 29 (.close 66))) (.step 31 (.close 66))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 47 (.step 66 (.close 11)))) (.step 66 (.close 3))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 12 (.close 66)) (.step 11 (.step 3 (.close 66)))) (.step 11 (.close 12))) (.step 11 (.step 18 (.close 12)))) (.step 11 (.step 18 (.close 12))))) (.split 8 0 (.step 31 (.close 66)) (.step 11 (.close 66)))) (.step 66 (.close 3))) (.step 66 (.close 3))) (.step 66 (.close 77))) (.step 66 (.close 75))) (.step 66 (.close 68)))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320037666840043678675691909575646114449157154275436203327082694298937955082967175700011546023512163130394958109920914726046880522915802160457889120219291038136343638093356202983424⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 59 1 (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 3 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 12 0 (.step 67 (.step 40 (.split 8 0 (.step 3 (.step 18 (.close 23))) (.step 9 (.step 3 (.close 11)))))) (.split 16 0 (.split 17 0 (.step 32 (.step 21 (.step 9 (.step 29 (.step 66 (.step 3 (.close 67))))))) (.step 31 (.step 23 (.close 11)))) (.step 21 (.close 18)))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 8 0 (.step 67 (.close 3)) (.step 9 (.close 67))) (.step 11 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 23))) (.step 18 (.close 67))) (.step 11 (.close 67)))) (.split 8 0 (.step 31 (.step 66 (.step 18 (.close 67)))) (.step 11 (.close 67)))) (.step 67 (.close 3))) (.step 67 (.close 77))) (.step 67 (.close 75))) (.step 67 (.close 68))))))) (.reuse 1)) (.run (.step 3 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 44 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.step 62 (.close 31)) (.step 27 (.step 29 (.close 3)))) (.step 3 (.close 23))) (.step 26 (.split 21 0 (.split 26 0 (.step 62 (.close 3)) (.step 27 (.close 29))) (.step 3 (.close 23))))) (.step 18 (.close 62))) (.step 18 (.close 62))) (.step 44 (.step 52 (.step 55 (.close 18))))) (.step 9 (.step 11 (.close 62))))) (.step 23 (.close 26))) (.step 55 (.close 74))) (.step 3 (.close 7))) (.step 55 (.step 32 (.close 67)))) (.step 66 (.step 55 (.step 12 (.close 66))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 17350758325419215096788520990895667098404201320045581412890825219043916925432955656099890776178416297475333599799540755379500898701125222726715418299723001631918682379196780230332173629833770487133801131341258894327129571328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 67 1 (.split 71 1 (.split 8 0 (.split 10 0 (.split 12 0 (.step 23 (.split 26 0 (.split 30 0 (.split 34 0 (.split 14 0 (.split 35 0 (.split 16 0 (.step 57 (.close 3)) (.step 3 (.close 23))) (.step 21 (.close 57))) (.step 23 (.step 9 (.close 40)))) (.step 31 (.close 57))) (.step 3 (.step 31 (.close 55)))) (.split 14 0 (.step 57 (.close 23)) (.step 23 (.close 29))))) (.step 9 (.split 26 0 (.step 23 (.split 39 0 (.step 15 (.close 57)) (.step 21 (.close 57)))) (.step 15 (.step 23 (.close 57)))))) (.step 23 (.step 31 (.step 15 (.step 3 (.close 57)))))) (.step 9 (.close 11))) (.step 22 (.step 29 (.split 10 0 (.step 74 (.close 12)) (.step 12 (.close 74)))))) (.step 3 (.close 55))) (.step 26 (.step 29 (.step 57 (.close 23))))) (.step 3 (.close 57))) (.step 23 (.step 29 (.step 32 (.step 51 (.step 55 (.step 67 (.step 9 (.step 57 (.step 3 (.step 26 (.step 3 (.close 57))))))))))))) (.step 12 (.step 23 (.step 29 (.step 51 (.step 55 (.step 66 (.step 9 (.step 68 (.step 57 (.step 40 (.step 3 (.step 26 (.close 57)))))))))))))) (.step 26 (.step 55 (.step 57 (.step 23 (.close 3)))))) (.step 22 (.step 23 (.step 57 (.split 16 0 (.split 22 0 (.step 9 (.step 57 (.close 3))) (.step 3 (.step 23 (.close 12)))) (.step 3 (.step 21 (.close 23)))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043916925432955656099890776178416297475333599799540755379500898701125222726715418299723001631918682379196780230332173629833770487133801131341258894327129571328⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 54 1 (.split 58 1 (.reuse 0) (.run (.step 40 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 74 1 (.split 67 1 (.split 71 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 72 1 (.split 12 0 (.split 21 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 39 0 (.step 40 (.close 55)) (.step 27 (.step 40 (.close 55)))) (.step 3 (.close 32))) (.step 27 (.close 15))) (.step 3 (.close 61))) (.step 3 (.close 23))) (.step 22 (.step 27 (.step 34 (.step 57 (.step 23 (.close 3))))))) (.step 40 (.close 3))) (.step 18 (.step 27 (.close 61)))) (.step 18 (.step 3 (.step 23 (.close 61))))) (.step 27 (.step 34 (.step 40 (.step 61 (.close 3)))))) (.step 3 (.step 18 (.step 12 (.close 40))))) (.step 27 (.split 72 1 (.split 34 0 (.step 61 (.close 11)) (.step 11 (.close 61))) (.step 9 (.step 11 (.close 31)))))) (.step 11 (.step 36 (.split 10 0 (.step 74 (.close 12)) (.step 12 (.close 74)))))) (.step 3 (.close 55))) (.step 11 (.step 44 (.step 61 (.close 40))))) (.step 3 (.close 61))) (.step 11 (.step 32 (.step 40 (.step 51 (.step 55 (.step 67 (.step 27 (.step 68 (.step 61 (.step 23 (.step 3 (.step 44 (.close 61)))))))))))))) (.step 11 (.step 34 (.step 40 (.step 51 (.step 55 (.step 66 (.step 27 (.step 61 (.step 23 (.step 3 (.close 77)))))))))))) (.step 44 (.step 55 (.step 61 (.step 40 (.close 3))))))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635883701843190724303217294794053595643915735143662319339448429819800998047882560512335607950482718939548034635127979339382509720196397018217808687792128⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 51 (.split 67 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 58 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 54)))))) (.run (.step 3 (.step 57 (.step 61 (.split 51 1 (.split 63 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 53 (.split 54 1 (.split 58 1 (.split 64 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 34 0 (.step 53 (.close 23)) (.step 18 (.step 21 (.close 53)))) (.step 27 (.step 29 (.close 3)))) (.step 3 (.close 23))) (.split 10 0 (.split 21 0 (.split 22 0 (.split 26 0 (.step 53 (.close 3)) (.step 27 (.close 29))) (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 3 (.close 12)))) (.step 18 (.close 53))) (.step 18 (.close 53))) (.step 55 (.close 53))) (.step 9 (.step 11 (.close 53)))) (.step 32 (.close 3))) (.step 61 (.close 53))) (.step 57 (.close 53)))) (.step 27 (.step 32 (.step 44 (.step 23 (.step 11 (.step 55 (.close 53)))))))) (.step 21 (.step 26 (.step 29 (.step 32 (.step 55 (.close 53))))))) (.step 55 (.close 74))) (.step 3 (.close 70))) (.step 32 (.step 55 (.step 12 (.close 66))))) (.step 3 (.close 54))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312709644568453678229065101026783367772262247405062442354004351486843579997404222351049909495124259302394380072511007769773918388224⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 3 (.step 52 (.step 57 (.step 61 (.split 51 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 52 (.split 54 1 (.split 58 1 (.split 63 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 52 (.close 3)) (.step 53 (.step 52 (.close 3)))) (.step 31 (.close 52))) (.step 27 (.step 29 (.close 3)))) (.step 3 (.close 23))) (.step 34 (.split 26 0 (.step 52 (.close 12)) (.step 12 (.close 52))))) (.step 18 (.close 52))) (.step 18 (.close 52))) (.step 34 (.step 52 (.close 3)))) (.step 9 (.step 11 (.close 52)))) (.step 12 (.close 3))) (.step 61 (.close 52))) (.step 57 (.close 52)))) (.step 12 (.step 27 (.step 34 (.step 44 (.step 23 (.step 11 (.step 55 (.close 52))))))))) (.step 9 (.step 12 (.step 26 (.split 58 1 (.step 40 (.step 29 (.step 55 (.close 52)))) (.step 40 (.close 3))))))) (.step 55 (.close 74))) (.step 3 (.close 70))) (.step 12 (.step 55 (.step 32 (.close 67))))) (.step 3 (.close 54))))))))) (.run (.step 9 (.step 27 (.step 47 (.step 53 (.step 62 (.split 51 1 (.split 67 1 (.split 49 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.close 47))) (.step 3 (.close 47))) (.step 3 (.step 9 (.close 52)))) (.step 3 (.close 46))) (.step 3 (.close 46))))))))))
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
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350752809766951994801222262167459667490405711928515041354902649229559372801718848142058332945296774836437705115125590176995307907369785551166718672767148373823834826509034612191687478041922138169360231282451414756934811648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 51 1 (.split 58 1 (.split 67 1 (.split 72 1 (.step 44 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.step 42 (.close 40)) (.step 27 (.close 15))) (.step 3 (.close 23))) (.step 21 (.step 32 (.step 27 (.step 34 (.step 3 (.close 23))))))) (.step 18 (.close 42))) (.step 18 (.close 42))) (.step 27 (.step 34 (.step 42 (.close 3))))) (.step 3 (.step 18 (.step 12 (.close 23))))) (.step 27 (.split 34 0 (.step 42 (.close 11)) (.step 11 (.close 42)))))) (.step 40 (.close 42))) (.step 3 (.close 11))) (.step 27 (.step 42 (.close 31)))) (.step 3 (.close 42))) (.step 42 (.close 77))) (.step 11 (.step 32 (.step 36 (.step 40 (.step 55 (.step 61 (.step 67 (.step 27 (.step 74 (.step 42 (.step 40 (.close 3))))))))))))) (.step 3 (.close 42))) (.step 32 (.step 42 (.step 67 (.split 34 0 (.split 36 0 (.split 42 0 (.step 27 (.close 42)) (.step 18 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 67))))))) (.step 11 (.step 12 (.step 32 (.step 34 (.step 40 (.step 55 (.step 67 (.step 74 (.step 77 (.split 65 1 (.split 36 0 (.step 27 (.step 42 (.step 18 (.close 23)))) (.step 18 (.step 36 (.close 40)))) (.step 3 (.close 42))))))))))))) (.step 3 (.step 27 (.step 42 (.step 44 (.step 40 (.close 55))))))) (.step 3 (.step 21 (.step 23 (.step 32 (.step 36 (.step 40 (.step 27 (.step 61 (.step 9 (.step 57 (.step 42 (.step 23 (.close 3)))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559367874803329960215142788645326212092549297707100664024483491958407895403962399535679869790515890859464982528⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 44 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.step 31 (.close 7)) (.step 3 (.step 29 (.close 77)))) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66)))) (.step 31 (.close 12))) (.step 31 (.close 40))) (.step 31 (.close 53))) (.step 31 (.close 52)))))) (.run (.step 3 (.step 68 (.step 31 (.step 68 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.step 61 (.step 18 (.split 74 1 (.step 43 (.step 27 (.step 23 (.step 42 (.step 22 (.close 55)))))) (.step 11 (.step 23 (.close 74))))))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 3 (.step 31 (.close 61)))) (.step 31 (.close 57))) (.step 9 (.step 31 (.close 53)))) (.step 9 (.step 31 (.close 52)))))))))) (.step 27 (.step 40 (.step 42 (.split 40 1 (.split 49 1 (.split 50 1 (.reuse 1) (.run (.step 21 (.step 32 (.step 42 (.close 3)))))) (.run (.step 27 (.step 42 (.step 44 (.close 52)))))) (.run (.step 3 (.step 24 (.step 27 (.step 42 (.step 31 (.step 24 (.step 42 (.close 23)))))))))))))) (.run (.step 7 (.step 36 (.step 57 (.step 74 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 74 1 (.split 39 1 (.step 31 (.step 40 (.step 31 (.close 7)))) (.step 31 (.close 36))) (.step 31 (.close 36))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 22 (.step 31 (.close 12)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 39)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350752809766951994796323378856802325053457861531070688173946490860866567220885610375253963989114579277282142986368095419115880733698076198414475950045403308447850474503974471532699088622153902567268257227427571677739876352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 42 1 (.split 49 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 74 1 (.step 21 (.split 39 1 (.step 75 (.split 51 1 (.step 29 (.split 54 1 (.split 67 1 (.split 8 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 49 0 (.split 51 0 (.step 38 (.step 32 (.close 38))) (.step 21 (.step 3 (.close 38)))) (.step 21 (.step 38 (.close 3)))) (.step 31 (.step 32 (.step 23 (.step 32 (.close 38)))))) (.step 40 (.step 31 (.step 18 (.close 74))))) (.step 38 (.step 18 (.close 32)))) (.step 40 (.step 66 (.step 38 (.close 18))))) (.step 21 (.step 38 (.step 23 (.close 3))))) (.step 66 (.split 64 1 (.split 71 1 (.step 3 (.close 38)) (.step 31 (.step 12 (.close 23)))) (.step 21 (.step 31 (.close 38)))))) (.step 40 (.step 66 (.step 67 (.step 38 (.close 11)))))) (.step 3 (.close 38))) (.step 57 (.close 38)))) (.step 3 (.close 38)))) (.step 32 (.close 3)))) (.step 32 (.step 66 (.step 67 (.step 69 (.step 40 (.step 29 (.step 23 (.step 11 (.step 38 (.close 74))))))))))) (.step 3 (.step 21 (.close 38)))) (.step 3 (.step 21 (.step 26 (.step 29 (.step 40 (.step 38 (.close 3)))))))) (.step 21 (.step 40 (.step 27 (.close 61))))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 32 (.step 40 (.step 52 (.step 57 (.step 61 (.step 75 (.step 55 (.split 58 1 (.step 40 (.step 38 (.step 26 (.step 38 (.close 3))))) (.step 22 (.step 27 (.close 52)))))))))))))))) (.step 29 (.step 31 (.close 3)))) (.step 31 (.close 39)))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354670349575856338457188751378132973723396743678570599764326663188903771066419118080⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.step 3 (.step 9 (.step 31 (.step 32 (.step 38 (.step 57 (.reuse 1)))))))) (.run (.step 7 (.step 34 (.step 38 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.split 64 1 (.step 7 (.step 66 (.split 71 1 (.split 74 1 (.split 39 1 (.step 31 (.close 7)) (.step 31 (.close 11))) (.step 31 (.close 34))) (.step 31 (.close 74))))) (.step 31 (.close 67)))) (.step 15 (.step 31 (.close 21)))) (.step 31 (.close 34))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.close 37))))))))) (.run (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 18 (.step 31 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))))) (.step 18 (.close 31))))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 31)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935945435639043483226069824934195533734467018978649163584424518877184⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 3 (.step 57 (.step 66 (.step 67 (.step 74 (.split 49 1 (.split 50 1 (.split 59 1 (.split 65 1 (.split 74 1 (.split 30 1 (.split 39 1 (.split 51 1 (.split 54 1 (.split 58 1 (.step 29 (.split 63 1 (.step 3 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 29 (.step 27 (.close 3))) (.step 18 (.close 23))) (.step 18 (.close 23))) (.step 18 (.close 23))) (.step 27 (.step 17 (.close 18)))) (.step 9 (.close 11)))) (.step 29 (.close 66)))) (.step 27 (.close 29))) (.step 29 (.close 27))) (.step 3 (.close 29))) (.step 27 (.close 29))) (.step 3 (.close 29))) (.step 27 (.step 29 (.step 11 (.step 66 (.step 18 (.close 67))))))) (.step 3 (.close 29))) (.step 3 (.step 26 (.step 27 (.close 29))))) (.step 3 (.step 27 (.step 29 (.step 26 (.step 29 (.close 53))))))) (.step 3 (.step 27 (.step 52 (.step 57 (.step 29 (.step 26 (.step 29 (.close 52)))))))))))))))) (.run (.step 26 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.split 72 1 (.step 23 (.step 18 (.close 7))) (.step 18 (.close 23))) (.step 18 (.close 74))))) (.step 18 (.close 66)))) (.step 18 (.close 12))) (.step 18 (.close 23))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 66 (.step 38 (.close 67))))) (.step 18 (.step 29 (.close 66)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128631309488126249824916623521853328054999501064110080⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 31 (.step 68 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 18 (.step 68 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.step 31 (.split 72 1 (.step 24 (.step 9 (.step 40 (.step 15 (.step 18 (.close 24)))))) (.step 18 (.step 29 (.step 31 (.close 74))))))) (.step 18 (.step 31 (.close 67)))) (.step 18 (.close 66))) (.step 3 (.step 18 (.close 12)))) (.step 18 (.step 3 (.close 61)))))) (.step 24 (.step 57 (.close 24)))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52)))) (.step 18 (.step 24 (.step 3 (.close 42))))) (.step 18 (.step 21 (.step 31 (.close 38))))) (.step 18 (.close 29))))))) (.run (.step 7 (.step 22 (.step 74 (.split 22 1 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 18 (.split 63 1 (.step 7 (.step 67 (.split 72 1 (.step 23 (.split 64 1 (.step 18 (.close 7)) (.step 18 (.close 15)))) (.step 18 (.close 74))))) (.step 18 (.close 66)))) (.step 18 (.close 22))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 38 (.close 66)))) (.step 18 (.step 29 (.close 66)))) (.step 18 (.close 20))))))))
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
def root : Box := ⟨2787593149816327892691964784081048409473024, 11567177732598406499846312727330591355628391062750984382345349645167653567220954788529207449019384024941729582908101661906708554268411715422027911114439154389232089613574829144875821232681776374775335133456412009823501025280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 42 1 (.step 34 (.step 77 (.split 51 1 (.step 11 (.split 58 1 (.split 67 1 (.split 10 0 (.split 14 2 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 55 (.step 12 (.close 3))) (.step 12 (.close 55))) (.step 12 (.close 17))) (.step 18 (.step 12 (.close 17)))) (.step 17 (.step 12 (.close 23)))) (.step 23 (.step 17 (.close 31)))) (.step 23 (.step 17 (.step 12 (.close 74))))) (.step 17 (.step 23 (.close 31)))) (.step 18 (.step 17 (.close 23)))) (.step 27 (.close 29))) (.step 17 (.step 3 (.step 17 (.close 74))))) (.step 18 (.step 17 (.close 74)))) (.step 17 (.step 18 (.step 17 (.close 67))))) (.step 17 (.step 66 (.step 67 (.step 23 (.step 17 (.close 31))))))) (.step 17 (.step 3 (.step 12 (.close 29))))) (.step 3 (.close 17))) (.step 61 (.close 17)))) (.step 3 (.close 17))))) (.step 31 (.close 17))) (.step 42 (.close 17))) (.step 31 (.close 17))) (.step 31 (.close 17))) (.step 3 (.close 17))) (.step 31 (.step 66 (.step 67 (.step 69 (.step 23 (.step 40 (.step 74 (.split 39 1 (.step 17 (.close 29)) (.step 17 (.close 32))))))))))) (.step 3 (.step 17 (.close 34)))) (.step 3 (.step 27 (.step 34 (.step 23 (.step 42 (.step 44 (.step 17 (.close 3))))))))) (.step 23 (.step 9 (.step 31 (.step 34 (.close 57)))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188504780569358784210725405119858117443584⟩
def references : Fin 2 → Box := ![Part14.root, Part15.root]
def proof : Chunks.Proof 2 := (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 21 (.step 42 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.split 72 1 (.step 18 (.close 7)) (.step 18 (.close 21))) (.step 18 (.close 74))))) (.step 18 (.close 66)))) (.step 18 (.close 21))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.step 38 (.close 66)))) (.step 18 (.step 29 (.close 66)))) (.step 18 (.close 19))) (.step 18 (.close 19)))))))) (.step 3 (.step 17 (.step 18 (.step 31 (.step 27 (.step 42 (.step 61 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 40 1 (.split 50 1 (.reuse 1) (.run (.step 3 (.step 27 (.step 32 (.step 34 (.step 42 (.step 53 (.step 57 (.step 61 (.step 77 (.step 55 (.split 54 1 (.step 23 (.step 17 (.step 44 (.step 17 (.close 3))))) (.step 12 (.close 23))))))))))))))) (.run (.step 23 (.step 31 (.close 17))))) (.run (.step 31 (.step 32 (.step 38 (.step 57 (.step 66 (.step 67 (.step 74 (.split 54 1 (.split 58 1 (.split 72 1 (.split 74 1 (.split 8 0 (.step 40 (.step 29 (.step 23 (.step 17 (.close 31))))) (.step 9 (.close 11))) (.step 17 (.close 23))) (.step 38 (.close 17))) (.step 17 (.close 40))) (.step 12 (.step 23 (.close 31))))))))))))) (.run (.step 3 (.step 27 (.step 47 (.step 29 (.close 17))))))) (.run (.step 17 (.step 3 (.close 18))))) (.run (.step 17 (.step 3 (.close 18))))) (.run (.step 18 (.step 3 (.close 19))))))))))))))))
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
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663036746082060580323243797207111077065483096964071150043225830046595288109993097542472409111224336407687198789285594733501922137417853828565748616166393909403674492058015783812885095447032452309149139599360⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 14 1 (.split 26 1 (.split 36 1 (.split 42 1 (.split 16 1 (.split 30 1 (.split 51 1 (.split 54 1 (.split 17 1 (.split 67 1 (.split 74 1 (.step 26 (.split 8 0 (.split 12 2 (.split 26 0 (.split 30 0 (.split 34 0 (.split 14 0 (.split 35 0 (.split 16 0 (.step 9 (.step 15 (.step 23 (.step 12 (.close 15))))) (.step 3 (.close 23))) (.step 21 (.step 15 (.close 3)))) (.step 15 (.close 17))) (.step 15 (.close 3))) (.step 3 (.step 15 (.close 3)))) (.split 16 0 (.step 15 (.close 29)) (.step 18 (.step 15 (.close 3))))) (.step 9 (.step 15 (.close 18)))) (.step 9 (.close 11)))) (.step 23 (.step 9 (.close 15)))) (.step 3 (.close 15))) (.step 18 (.close 15))) (.step 9 (.step 15 (.close 18)))) (.step 3 (.close 15))) (.step 3 (.close 15))) (.step 18 (.close 15))) (.step 15 (.close 31))) (.step 15 (.close 31))) (.step 15 (.close 29))) (.step 12 (.step 3 (.close 17)))) (.step 15 (.step 26 (.step 29 (.step 3 (.step 23 (.close 3))))))) (.step 12 (.step 22 (.step 23 (.step 29 (.step 31 (.step 55 (.step 57 (.step 66 (.step 9 (.step 74 (.step 15 (.step 3 (.step 15 (.close 23))))))))))))))) (.step 3 (.close 15))) (.step 12 (.step 21 (.step 23 (.step 29 (.step 31 (.step 32 (.step 55 (.step 74 (.step 75 (.split 21 0 (.split 65 1 (.split 8 0 (.step 57 (.step 66 (.split 17 0 (.step 15 (.close 55)) (.step 18 (.close 67))))) (.step 9 (.close 11))) (.step 3 (.close 15))) (.step 23 (.close 15))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439025350354042471212733978678132736⟩
def references : Fin 2 → Box := ![Part16.root, Part17.root]
def proof : Chunks.Proof 2 := (.split 12 1 (.reuse 0) (.step 23 (.step 31 (.split 21 1 (.split 35 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 1) (.run (.step 12 (.step 15 (.step 29 (.step 31 (.step 66 (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.close 15)) (.step 23 (.close 15))) (.step 22 (.close 66))) (.step 21 (.close 66)))))))))) (.run (.step 3 (.step 9 (.step 15 (.step 26 (.step 23 (.close 55)))))))) (.run (.step 3 (.step 12 (.step 22 (.step 23 (.step 34 (.step 9 (.step 40 (.step 57 (.step 27 (.step 61 (.step 15 (.step 3 (.step 15 (.close 23)))))))))))))))) (.run (.step 9 (.step 15 (.step 22 (.step 26 (.close 53))))))) (.run (.step 12 (.step 15 (.step 26 (.close 52)))))) (.run (.step 24 (.step 31 (.step 3 (.close 15)))))) (.run (.step 3 (.step 12 (.step 21 (.step 23 (.step 32 (.step 34 (.step 40 (.step 43 (.step 57 (.step 27 (.step 61 (.step 9 (.step 62 (.split 40 1 (.split 17 0 (.step 15 (.step 3 (.close 23))) (.step 3 (.close 23))) (.step 3 (.close 31)))))))))))))))))) (.run (.step 9 (.step 15 (.step 22 (.step 26 (.step 31 (.close 38)))))))) (.run (.step 9 (.step 24 (.step 15 (.close 24)))))))))
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
def root : Box := ⟨2417851639229261570637824, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439027885657660779310766230433955840⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 31 (.step 42 (.step 61 (.step 66 (.step 67 (.step 74 (.split 35 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 10 1 (.split 12 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 42 1 (.split 51 1 (.split 54 1 (.step 11 (.split 58 1 (.split 63 1 (.step 3 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.step 11 (.step 9 (.close 3))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 9 (.step 11 (.close 31)))) (.step 9 (.close 47)))) (.step 11 (.close 66))) (.step 11 (.close 3)))) (.step 9 (.close 11))) (.step 3 (.close 11))) (.step 9 (.step 11 (.close 31)))) (.step 11 (.close 42))) (.step 9 (.step 11 (.close 31)))) (.step 3 (.step 9 (.step 11 (.step 29 (.step 11 (.close 31))))))) (.step 3 (.close 11))) (.step 27 (.close 47))) (.step 9 (.close 11))) (.step 3 (.close 11))) (.step 9 (.step 29 (.step 31 (.step 11 (.step 66 (.close 75))))))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 11 (.close 61))))) (.step 3 (.step 9 (.step 42 (.step 11 (.step 44 (.step 11 (.close 53)))))))) (.step 3 (.step 9 (.step 42 (.step 52 (.step 61 (.step 11 (.step 44 (.step 11 (.close 52)))))))))) (.step 23 (.step 31 (.close 11)))) (.step 9 (.step 31 (.step 38 (.step 47 (.step 11 (.close 38)))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439027885657660779310766230433955840⟩
def references : Fin 2 → Box := ![Part18.root, Part19.root]
def proof : Chunks.Proof 2 := (.split 8 1 (.split 10 1 (.reuse 0) (.run (.split 12 1 (.split 14 1 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 18 (.step 31 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 29))) (.step 18 (.close 31))) (.step 18 (.close 31))))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 29))) (.step 3 (.close 17))) (.step 3 (.close 31))))) (.reuse 1))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part20.excludes
end FiveColour.Packed.ProjectedChunks.Case82
