module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case101
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231548175077138580140037819542512687120384⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨3221225472, 5783586108473071698929506996965222366134733773348527137630275073014641211963365061407257151770905019981373183719519790822093350474905949501118222832300809514923782105583616072404305743849391691111876113117710446009673318400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 34 0 (.split 22 0 (.split 36 0 (.split 39 0 (.step 55 (.close 3)) (.step 27 (.step 40 (.close 3)))) (.step 3 (.step 23 (.close 31)))) (.step 3 (.close 23))) (.step 31 (.step 3 (.close 23)))) (.step 3 (.step 23 (.close 24)))) (.step 18 (.step 3 (.step 23 (.close 3))))) (.step 18 (.split 17 0 (.step 3 (.step 18 (.step 23 (.close 3)))) (.step 7 (.close 18))))) (.split 16 0 (.split 17 0 (.step 23 (.split 22 0 (.split 34 0 (.split 36 0 (.step 55 (.split 39 0 (.step 55 (.step 3 (.close 23))) (.step 27 (.step 34 (.step 23 (.close 32)))))) (.step 3 (.close 40))) (.step 3 (.step 23 (.close 17)))) (.step 3 (.close 55)))) (.step 11 (.step 18 (.close 55)))) (.step 11 (.step 18 (.split 17 0 (.step 3 (.step 17 (.step 18 (.close 21)))) (.step 17 (.close 18))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.split 21 0 (.split 22 0 (.split 35 0 (.split 30 0 (.step 40 (.split 34 0 (.step 55 (.close 31)) (.step 15 (.close 3)))) (.step 3 (.step 31 (.close 23)))) (.step 21 (.split 49 0 (.step 38 (.step 15 (.step 3 (.close 22)))) (.step 15 (.step 12 (.close 3)))))) (.step 3 (.step 23 (.close 15)))) (.step 3 (.step 18 (.step 15 (.close 40)))))) (.step 18 (.step 22 (.close 40)))) (.step 18 (.step 21 (.close 3)))) (.split 16 0 (.split 17 0 (.step 15 (.step 9 (.step 23 (.close 3)))) (.step 3 (.close 12))) (.step 3 (.close 17))))))
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
def root : Box := ⟨10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579558101483520, 17350758325419215096778723214921340236387974119565902765140055240619506863005372417453778513176160041487847656483139263695400997607936018408437653760652107319292603122302351735100707236720065892706284953670040127636691222528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 3)) (.step 31 (.close 55))) (.step 29 (.step 74 (.close 3)))) (.step 31 (.close 55))) (.split 34 0 (.split 35 0 (.step 55 (.close 31)) (.step 32 (.close 3))) (.step 31 (.close 40)))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 22 (.step 57 (.step 66 (.close 55)))) (.step 23 (.close 74))) (.step 23 (.close 31))) (.step 22 (.close 18))) (.step 31 (.step 23 (.close 18))))) (.split 16 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 39 0 (.split 54 0 (.step 74 (.close 3)) (.step 12 (.step 23 (.close 31)))) (.step 36 (.step 34 (.close 74)))) (.step 18 (.close 74))) (.step 18 (.close 74))) (.step 18 (.close 23))) (.step 18 (.close 74)))) (.split 12 0 (.step 18 (.step 66 (.close 74))) (.step 12 (.close 31)))) (.step 69 (.step 74 (.step 55 (.close 3))))) (.step 69 (.step 74 (.step 55 (.close 3))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 17350758325419215096788520990886533306152125628145825492823296337566082577772889986381197430566508684422447767664866465692745129534045716257442955581950028737839585585480387672763426646526722739637358080012457263350230810624⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.reuse 0) (.run (.step 3 (.step 31 (.split 12 0 (.split 16 0 (.split 14 0 (.split 17 0 (.step 18 (.close 23)) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 7 (.close 18))) (.step 3 (.step 12 (.close 3)))))))) (.run (.step 11 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.step 77 (.step 23 (.step 44 (.close 55)))) (.step 18 (.close 40))) (.step 23 (.close 77))) (.step 23 (.close 77))) (.step 23 (.close 77)))))) (.run (.split 74 1 (.step 29 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 75 (.step 40 (.step 26 (.close 55)))) (.step 31 (.close 23))) (.step 40 (.close 75))) (.step 38 (.step 18 (.close 75)))) (.step 40 (.close 75)))) (.step 40 (.close 69))))) (.reuse 1)) (.run (.step 69 (.split 72 1 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 55))) (.step 3 (.close 55)))))) (.run (.split 72 1 (.split 74 1 (.split 71 1 (.step 68 (.step 18 (.step 3 (.close 15)))) (.split 54 0 (.split 12 0 (.split 14 0 (.split 34 0 (.split 35 0 (.step 18 (.step 68 (.close 3))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.close 74))) (.step 3 (.close 68))) (.step 3 (.close 74)))) (.step 3 (.step 18 (.step 12 (.step 61 (.step 12 (.close 74))))))) (.step 3 (.step 31 (.step 15 (.step 57 (.step 15 (.close 74)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 17350758325419215096788520990895658187387370018583107836034696920215869034787387106242355815602307234756865122437878291315379872333603000876590144396571406147282336461476892995402871074903226728986078609912623011734724018176⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 64 1 (.reuse 0) (.run (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 67 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 3)) (.step 31 (.close 55))) (.step 32 (.close 3))) (.step 31 (.close 55))) (.step 21 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 67))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 21 (.step 32 (.step 66 (.step 40 (.close 3))))) (.step 23 (.close 67))) (.step 23 (.close 31))) (.step 31 (.step 23 (.close 18)))) (.step 21 (.close 18)))) (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.step 67 (.close 3)) (.step 12 (.close 67))) (.step 18 (.close 67))) (.step 18 (.close 23))) (.step 18 (.close 67)))) (.split 12 0 (.step 18 (.step 66 (.step 31 (.close 67)))) (.step 12 (.close 31)))) (.step 67 (.close 3))) (.step 3 (.close 55))) (.step 67 (.close 77))) (.step 67 (.close 75))) (.step 67 (.split 36 0 (.split 54 0 (.split 12 0 (.split 14 0 (.split 35 0 (.step 18 (.step 68 (.close 3))) (.step 3 (.close 21))) (.step 3 (.close 67))) (.step 3 (.close 67))) (.step 3 (.close 67))) (.step 3 (.close 31))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201311933144244572989303597362966874315326085970228087693756778676076885898810676339476574618193537351030323148184836158745397879233332632011157352813158663176969805103642348380749824⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.reuse 0) (.run (.step 66 (.split 65 1 (.split 72 1 (.split 74 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 3)) (.step 31 (.close 55))) (.step 29 (.step 66 (.close 31)))) (.step 31 (.close 55))) (.split 34 0 (.step 12 (.step 67 (.step 55 (.close 31)))) (.step 3 (.close 66)))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.step 18 (.close 66))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.step 66 (.close 3)) (.step 9 (.close 11))) (.step 31 (.close 23))) (.step 31 (.close 66))) (.step 31 (.close 66)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.close 66)) (.step 11 (.step 12 (.close 66)))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 18 (.close 12)))) (.split 12 0 (.step 18 (.close 66)) (.step 12 (.close 3)))) (.step 66 (.close 3))) (.step 3 (.close 55))) (.step 66 (.close 3))) (.step 66 (.close 77))) (.step 66 (.close 75))) (.step 66 (.split 14 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 68 (.close 3)) (.step 3 (.close 66))) (.step 3 (.close 31))) (.step 3 (.close 18))) (.step 3 (.close 34))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416711979597824, 17350758325419215096788520990895658187387370018591022408881836265305805115460015816323480018773546013634115140232851002518788892083053125710549921836238531632914852920336136676500687113622188205949339191285954428443482390528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 12 0 (.split 22 0 (.split 34 0 (.split 30 0 (.split 39 0 (.split 40 0 (.split 49 0 (.step 40 (.close 3)) (.step 27 (.step 40 (.close 55)))) (.step 3 (.close 40))) (.step 42 (.close 61))) (.step 3 (.close 61))) (.step 3 (.close 40))) (.step 3 (.close 61))) (.step 34 (.step 22 (.step 9 (.step 57 (.step 23 (.close 31))))))) (.split 12 0 (.step 18 (.close 61)) (.step 3 (.close 23)))) (.step 36 (.step 18 (.close 61)))) (.split 35 0 (.split 63 0 (.step 61 (.close 18)) (.step 18 (.close 55))) (.step 18 (.close 40)))) (.step 34 (.step 61 (.close 40)))) (.split 12 0 (.step 18 (.step 61 (.close 3))) (.step 3 (.close 12)))) (.step 40 (.close 61))) (.step 3 (.close 12))) (.step 61 (.close 77))) (.step 36 (.step 40 (.step 61 (.split 34 0 (.split 42 0 (.split 10 0 (.step 61 (.close 21)) (.step 12 (.close 61))) (.step 40 (.close 61))) (.step 18 (.step 34 (.close 40)))))))) (.step 3 (.close 61))) (.step 32 (.step 40 (.step 51 (.step 74 (.step 77 (.split 65 1 (.split 34 0 (.split 40 0 (.split 42 0 (.step 42 (.step 61 (.step 55 (.close 12)))) (.step 18 (.close 67))) (.step 40 (.close 61))) (.step 18 (.step 34 (.close 40)))) (.step 3 (.close 67))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890818020781845656318743159238278478607442105959944316732927794170584719760996148346122905981951807609488115728604006457893450844288327046005272877469805768825712410624⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 44 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 34 0 (.step 62 (.close 23)) (.step 9 (.step 3 (.step 26 (.step 31 (.close 55)))))) (.split 35 0 (.step 62 (.close 3)) (.step 15 (.close 62)))) (.step 26 (.close 62))) (.step 3 (.close 23))) (.step 55 (.close 62))) (.step 53 (.step 18 (.close 62)))) (.step 27 (.step 44 (.step 52 (.step 55 (.close 18))))))) (.step 23 (.close 26))) (.step 55 (.close 74))) (.step 3 (.close 70))) (.step 26 (.step 55 (.close 67)))) (.step 44 (.step 66 (.step 55 (.close 66)))))))) (.split 59 1 (.split 63 1 (.reuse 1) (.run (.step 11 (.step 12 (.step 34 (.step 40 (.step 51 (.step 55 (.step 67 (.step 68 (.step 74 (.step 77 (.split 65 1 (.split 42 0 (.step 61 (.step 66 (.close 18))) (.step 18 (.close 40))) (.step 3 (.close 61))))))))))))))) (.run (.step 27 (.step 44 (.step 55 (.step 61 (.step 40 (.close 3)))))))))
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
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 17350758325419215096788520990895658187387370018583107836034704118477940303901599603103968113173281426272254405504491252524296051273732075257182654861669172372653776334933906628835068208128915519865581023536912395996892233728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 67 1 (.split 74 1 (.split 10 0 (.split 12 0 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 57 (.close 3)) (.step 3 (.close 23))) (.step 18 (.step 21 (.close 57)))) (.step 55 (.split 36 0 (.split 39 0 (.split 42 0 (.step 23 (.close 3)) (.step 3 (.close 23))) (.step 12 (.step 21 (.step 9 (.close 23))))) (.step 3 (.close 23))))) (.step 9 (.step 21 (.step 40 (.close 57))))) (.step 31 (.close 57))) (.step 3 (.step 31 (.step 23 (.close 32))))) (.step 3 (.step 23 (.close 57)))) (.split 39 0 (.split 58 0 (.step 15 (.close 57)) (.step 22 (.close 57))) (.step 12 (.step 21 (.close 57))))) (.split 39 0 (.step 31 (.step 15 (.step 3 (.close 55)))) (.step 3 (.step 12 (.close 23))))) (.step 23 (.close 57))) (.step 3 (.close 15))) (.step 57 (.close 75))) (.step 22 (.step 23 (.step 57 (.split 16 0 (.split 22 0 (.split 10 0 (.step 57 (.close 12)) (.step 12 (.close 57))) (.step 23 (.close 57))) (.step 21 (.step 23 (.close 31)))))))) (.step 3 (.close 57))) (.step 21 (.step 23 (.step 29 (.step 32 (.step 51 (.step 55 (.step 68 (.step 74 (.step 75 (.split 21 0 (.split 12 0 (.step 67 (.step 40 (.step 3 (.step 23 (.close 3))))) (.step 15 (.close 57))) (.step 23 (.close 31))))))))))))))
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
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 17350758325419215096788520990895667098404201320045581412890825219043923635883701843190724303217294794053595643915735143662319339448429819800998046029887084538548823705583179409028109475659584732260694356149854476569438846976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 57 (.step 61 (.split 51 1 (.split 59 1 (.split 63 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 58 1 (.split 64 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 34 0 (.step 53 (.close 31)) (.step 31 (.close 53))) (.split 10 0 (.split 36 0 (.step 53 (.close 3)) (.step 15 (.close 53))) (.step 3 (.close 12)))) (.step 55 (.close 53))) (.step 3 (.close 23))) (.step 55 (.close 53))) (.step 21 (.step 18 (.close 53)))) (.step 55 (.close 53))) (.step 32 (.close 3))) (.step 61 (.close 53))) (.step 57 (.close 53))) (.step 27 (.step 44 (.step 55 (.step 61 (.split 54 1 (.step 23 (.step 77 (.step 32 (.close 3)))) (.step 23 (.close 3)))))))) (.step 21 (.step 26 (.step 32 (.step 40 (.step 55 (.step 53 (.close 15)))))))) (.step 55 (.close 74))) (.step 3 (.close 70))) (.step 32 (.step 55 (.step 66 (.close 12))))) (.step 26 (.step 44 (.step 55 (.close 53))))) (.step 3 (.step 53 (.close 7))))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455307164305180212048509908272658497200365389373254310807350989964528555210604657210965963435030596225495950571810341036884876721127424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 53 (.step 3 (.step 61 (.split 51 1 (.split 59 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 52 (.split 54 1 (.split 58 1 (.split 63 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 35 0 (.step 52 (.close 23)) (.step 9 (.step 53 (.step 40 (.step 52 (.close 3)))))) (.step 34 (.split 34 0 (.step 52 (.close 12)) (.step 3 (.close 15))))) (.step 34 (.step 18 (.close 52)))) (.step 3 (.close 23))) (.step 55 (.close 52))) (.step 53 (.step 18 (.close 52)))) (.step 34 (.step 52 (.close 3)))) (.step 12 (.close 3))) (.step 61 (.close 52))) (.step 57 (.close 52)))) (.step 12 (.step 34 (.step 44 (.step 53 (.step 23 (.step 55 (.step 52 (.close 18))))))))) (.step 9 (.step 26 (.step 57 (.split 50 1 (.split 58 1 (.step 40 (.step 75 (.close 52))) (.step 40 (.close 3))) (.step 21 (.close 52))))))) (.step 55 (.close 74))) (.step 3 (.close 70))) (.step 12 (.step 55 (.step 67 (.close 21))))) (.step 26 (.step 44 (.step 55 (.close 52))))) (.step 3 (.step 52 (.close 7)))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312709644568453678229065101026783367772262247405062440501330923689784453220268462212043383842804504652145354232263844028534669443072⟩
def references : Fin 4 → Box := ![Part6.root, Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 4 := (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 1) (.run (.step 12 (.step 23 (.step 29 (.step 51 (.step 55 (.step 67 (.step 74 (.step 75 (.split 65 1 (.split 16 0 (.split 21 0 (.split 22 0 (.step 15 (.step 57 (.step 55 (.close 21)))) (.step 23 (.close 66))) (.step 23 (.close 57))) (.step 21 (.step 15 (.step 18 (.close 57))))) (.step 3 (.close 66))))))))))))) (.run (.step 9 (.step 26 (.step 55 (.step 57 (.step 23 (.close 3)))))))) (.run (.step 3 (.step 22 (.step 23 (.step 57 (.split 16 0 (.split 22 0 (.split 10 0 (.step 57 (.close 12)) (.step 12 (.close 57))) (.step 23 (.close 57))) (.step 3 (.step 21 (.close 23))))))))))) (.run (.step 51 (.split 59 1 (.split 67 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 58 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 51))) (.step 3 (.close 54))) (.step 3 (.close 54)))))) (.reuse 2)) (.reuse 3)) (.run (.step 9 (.step 27 (.step 47 (.step 52 (.step 53 (.split 51 1 (.split 59 1 (.split 67 1 (.split 49 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.close 47))) (.step 3 (.close 47))) (.step 3 (.close 46))) (.step 3 (.close 46))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 3 (.close 46))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350752809766951994801222262167459667490405703823992445884206078872941494915707228209261988025813013017030199996456356677242905530312881195762108135859457063696414304050731395589341044279926286661996651119627579486944362496⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 51 1 (.split 58 1 (.split 42 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 12 0 (.split 34 0 (.step 42 (.step 3 (.close 12))) (.step 3 (.close 40))) (.step 34 (.step 21 (.step 9 (.step 40 (.close 3)))))) (.step 27 (.step 32 (.step 18 (.close 42))))) (.step 36 (.step 18 (.close 42)))) (.split 63 0 (.step 42 (.close 3)) (.step 18 (.close 42)))) (.step 34 (.step 42 (.close 18)))) (.split 12 0 (.step 18 (.step 42 (.close 3))) (.step 3 (.close 12)))) (.step 40 (.close 42))) (.step 3 (.close 12))) (.step 31 (.close 40))) (.step 42 (.close 40))) (.step 3 (.close 42))) (.step 42 (.close 77))) (.step 32 (.step 36 (.step 40 (.step 61 (.step 77 (.split 34 0 (.split 40 0 (.split 42 0 (.step 42 (.step 61 (.step 55 (.close 12)))) (.step 18 (.close 74))) (.step 40 (.close 42))) (.step 18 (.step 34 (.close 40)))))))))) (.step 3 (.step 18 (.close 42)))) (.step 32 (.step 42 (.step 67 (.split 34 0 (.split 36 0 (.split 42 0 (.step 42 (.close 21)) (.step 40 (.close 42))) (.step 18 (.step 36 (.close 67)))) (.step 18 (.step 34 (.close 40)))))))) (.step 11 (.step 12 (.step 32 (.step 34 (.step 40 (.step 55 (.step 67 (.step 74 (.step 77 (.split 65 1 (.split 36 0 (.split 21 0 (.split 22 0 (.split 42 0 (.step 42 (.close 3)) (.step 40 (.close 42))) (.step 18 (.close 42))) (.step 23 (.close 42))) (.step 23 (.step 36 (.close 42)))) (.step 3 (.step 18 (.close 42)))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158554670789637782293759363827451745685364370135550157247147308771008817825033978532399726631546582612214152167424⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 44 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.step 31 (.close 7)) (.step 31 (.close 40))) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.close 40))) (.step 31 (.close 57))) (.step 31 (.close 53))) (.step 31 (.close 52)))))) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 31 (.step 68 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.split 71 1 (.split 74 1 (.step 43 (.step 3 (.step 18 (.close 23)))) (.step 23 (.close 77))) (.step 31 (.close 74)))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 3 (.step 31 (.close 62)))))) (.step 43 (.step 31 (.step 61 (.close 43))))) (.step 31 (.step 3 (.close 57)))) (.step 3 (.step 31 (.close 53)))) (.step 3 (.step 31 (.close 52)))))) (.step 27 (.step 40 (.step 42 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.reuse 1) (.run (.step 42 (.step 55 (.close 62))))) (.run (.step 3 (.step 21 (.step 23 (.step 32 (.step 36 (.step 40 (.step 61 (.step 62 (.split 22 0 (.step 9 (.step 57 (.step 23 (.close 43)))) (.step 3 (.step 23 (.close 12)))))))))))))) (.run (.step 21 (.step 32 (.step 42 (.close 3)))))) (.run (.step 42 (.step 52 (.close 23))))) (.run (.step 3 (.step 42 (.step 43 (.step 31 (.step 42 (.close 43))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350752804380572831610788907442024229475790461332504525813870267043879956428646433422188843812151858621015879123623404705032356489851383729460157694648002432354650458533512849446062025009680734256183089752369912481027457024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 65 1 (.split 74 1 (.step 21 (.split 39 1 (.split 51 1 (.step 75 (.split 54 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 38 (.close 55)) (.step 31 (.step 38 (.close 23)))) (.step 40 (.close 38))) (.step 21 (.step 18 (.close 38)))) (.step 40 (.step 38 (.close 18)))) (.step 21 (.split 14 0 (.split 17 0 (.step 38 (.split 21 0 (.step 38 (.close 3)) (.step 15 (.step 23 (.close 31))))) (.step 22 (.step 23 (.close 3)))) (.step 15 (.close 38))))) (.split 71 1 (.split 12 0 (.step 3 (.step 31 (.step 12 (.close 23)))) (.step 15 (.close 38))) (.step 31 (.step 38 (.close 12)))))) (.step 3 (.close 38))) (.step 21 (.step 32 (.close 67)))) (.step 66 (.close 38))) (.step 57 (.close 38)))) (.step 3 (.close 51))) (.step 32 (.close 3)))) (.step 32 (.step 66 (.step 67 (.step 69 (.step 23 (.step 40 (.step 74 (.step 38 (.close 77)))))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 32 (.step 40 (.step 57 (.step 38 (.close 55)))))))))) (.step 3 (.step 21 (.step 40 (.step 27 (.close 61)))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424713774431401999524729891650021243217920269897929539218857543668616592060342213356414803378176⟩
def references : Fin 2 → Box := ![Part12.root, Part13.root]
def proof : Chunks.Proof 2 := (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 36 (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 74 1 (.split 39 1 (.split 54 1 (.step 31 (.step 40 (.step 31 (.close 7)))) (.step 22 (.close 31))) (.step 31 (.close 36))) (.step 31 (.close 36))))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.close 36))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 39)))))))) (.step 3 (.step 9 (.step 31 (.step 38 (.step 57 (.step 66 (.step 74 (.split 36 1 (.split 42 1 (.split 49 1 (.reuse 1) (.run (.step 3 (.step 9 (.step 12 (.step 21 (.step 32 (.step 52 (.step 57 (.step 61 (.split 58 1 (.step 75 (.step 55 (.split 71 1 (.split 10 0 (.split 12 0 (.step 38 (.step 26 (.step 38 (.close 40)))) (.step 12 (.step 38 (.step 26 (.close 52))))) (.step 3 (.close 52))) (.step 12 (.step 22 (.close 38)))))) (.step 32 (.step 40 (.close 3)))))))))))))) (.run (.step 31 (.close 45)))) (.run (.step 31 (.close 39)))))))))))) (.run (.step 7 (.step 34 (.step 75 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 39 1 (.step 31 (.close 7)) (.step 31 (.close 34))) (.step 31 (.close 34))) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.close 34))) (.step 15 (.step 31 (.close 34)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 45))) (.step 31 (.close 39))) (.step 3 (.step 31 (.close 37)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750845221134557915601384484729909347490578749691818672128⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 22 1 (.split 30 1 (.reuse 0) (.run (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.step 18 (.step 31 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 7))) (.step 18 (.close 52))) (.step 3 (.close 18))) (.step 3 (.close 31))))) (.run (.step 26 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.step 18 (.close 7)) (.step 18 (.close 23))) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.close 23))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 66 (.step 38 (.close 67)))))))) (.run (.step 43 (.step 68 (.split 35 1 (.split 39 1 (.step 31 (.split 49 1 (.split 50 1 (.split 54 1 (.step 18 (.step 68 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.step 43 (.split 71 1 (.split 72 1 (.step 24 (.step 3 (.step 18 (.close 24)))) (.step 18 (.close 75))) (.step 18 (.close 74))))) (.step 18 (.step 67 (.close 24)))) (.step 18 (.close 66))) (.step 3 (.step 18 (.close 62)))) (.step 18 (.step 3 (.close 61)))))) (.step 24 (.step 18 (.step 57 (.close 24))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52))))) (.step 18 (.step 42 (.close 3)))) (.step 18 (.step 21 (.step 31 (.step 38 (.close 66))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758320032835933598087636165669219771963874226972439320526472119418572137003671376999340803234448176750898617677073253739990265889313308463453603507245172372742770447421735157578262707428774745882021507555470936276729856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.step 34 (.split 51 1 (.step 77 (.split 63 1 (.split 64 1 (.split 67 1 (.step 11 (.split 10 0 (.split 14 2 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 23 (.split 34 0 (.split 35 0 (.step 34 (.step 17 (.step 23 (.step 17 (.close 3))))) (.step 23 (.step 17 (.close 31)))) (.step 17 (.step 3 (.step 17 (.close 31)))))) (.step 18 (.step 12 (.step 17 (.close 21))))) (.step 18 (.close 17))) (.step 17 (.step 18 (.close 17)))) (.step 17 (.step 18 (.close 17)))) (.step 17 (.split 71 1 (.step 23 (.step 17 (.split 36 0 (.step 3 (.close 12)) (.step 3 (.close 17))))) (.step 17 (.close 74))))) (.step 17 (.step 3 (.close 12))))) (.step 3 (.close 17))) (.step 67 (.close 17))) (.step 12 (.step 34 (.close 66))))) (.step 3 (.close 17)))) (.step 31 (.step 17 (.close 66)))) (.step 31 (.step 17 (.close 66)))) (.step 31 (.close 17))) (.step 3 (.close 17))) (.step 31 (.step 66 (.step 67 (.step 69 (.step 23 (.step 40 (.step 17 (.step 74 (.close 17)))))))))) (.step 3 (.step 18 (.step 17 (.close 34))))) (.step 3 (.step 27 (.step 34 (.step 23 (.step 44 (.step 17 (.close 55)))))))) (.step 18 (.step 36 (.step 40 (.step 44 (.step 61 (.close 17))))))) (.step 3 (.step 23 (.step 9 (.step 31 (.step 34 (.close 57))))))))
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
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231545516618611709107835553125398720020480⟩
def references : Fin 1 → Box := ![Part16.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 18 (.step 31 (.step 27 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 39 1 (.split 40 1 (.split 50 1 (.reuse 0) (.run (.step 3 (.step 27 (.step 32 (.step 34 (.step 53 (.step 57 (.step 61 (.split 54 1 (.step 77 (.step 55 (.split 71 1 (.split 12 0 (.step 23 (.step 17 (.step 44 (.step 17 (.close 53))))) (.step 12 (.close 23))) (.step 17 (.close 53))))) (.step 12 (.step 23 (.close 3))))))))))))) (.run (.step 12 (.step 23 (.step 31 (.close 17)))))) (.run (.step 23 (.step 36 (.step 40 (.step 42 (.close 17))))))) (.run (.step 31 (.step 32 (.step 38 (.step 57 (.step 61 (.step 66 (.step 67 (.step 74 (.split 54 1 (.split 72 1 (.split 74 1 (.split 12 0 (.step 23 (.split 30 0 (.split 35 2 (.step 17 (.close 31)) (.step 40 (.step 38 (.close 17)))) (.step 3 (.close 17)))) (.step 12 (.close 23))) (.step 17 (.close 23))) (.step 38 (.close 17))) (.step 12 (.step 23 (.close 31)))))))))))))) (.run (.step 17 (.step 3 (.close 18))))) (.run (.step 17 (.step 18 (.close 3))))) (.run (.step 17 (.step 18 (.close 19))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663036746082051455442008552816673794722271689183159292317097120429872517427386324800622602473384711620855647867545908374502182432580114401539757045085533110030583273539454327081909797400618145182043080753152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 71 1 (.split 72 1 (.split 14 1 (.split 36 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 42 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 12 2 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 14 0 (.split 16 0 (.split 36 0 (.split 17 0 (.step 9 (.step 15 (.step 12 (.step 23 (.close 3))))) (.step 3 (.close 23))) (.step 22 (.step 15 (.close 3)))) (.step 3 (.close 23))) (.step 55 (.split 39 0 (.step 15 (.close 17)) (.step 12 (.close 3))))) (.step 21 (.step 15 (.step 3 (.close 22))))) (.step 31 (.close 15))) (.step 3 (.step 15 (.step 3 (.close 23))))) (.step 3 (.step 18 (.close 15)))) (.step 9 (.split 39 0 (.step 15 (.close 18)) (.step 21 (.close 15))))) (.step 23 (.step 9 (.close 15)))) (.step 3 (.close 15))) (.step 3 (.close 15))) (.step 26 (.step 15 (.close 31)))) (.step 3 (.close 15))) (.step 18 (.close 15))) (.step 18 (.close 15))) (.step 18 (.close 15))) (.step 22 (.close 31))) (.step 12 (.step 15 (.close 18)))) (.step 21 (.step 15 (.step 18 (.close 75))))) (.step 12 (.step 22 (.step 23 (.step 31 (.step 75 (.split 16 0 (.split 21 0 (.split 22 0 (.step 15 (.step 57 (.step 55 (.close 21)))) (.step 23 (.close 74))) (.step 23 (.close 15))) (.step 21 (.step 15 (.close 18)))))))))) (.step 3 (.step 15 (.close 24)))))
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
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663036746082060589234260628508573550642339218064637126671310360656414541665114481318462472557759810087297362086657669012748261709367951002996158402747633127004274622712715954693922506089735581179073322287104⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 12 (.step 21 (.step 23 (.step 29 (.step 31 (.step 32 (.step 55 (.step 68 (.step 74 (.step 75 (.split 65 1 (.split 17 0 (.split 21 0 (.split 22 0 (.step 15 (.step 40 (.close 3))) (.step 23 (.close 15))) (.step 23 (.close 15))) (.step 22 (.step 15 (.close 18)))) (.step 3 (.close 15))))))))))))))) (.run (.step 12 (.step 31 (.step 66 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.close 21)) (.step 23 (.close 15))) (.step 22 (.step 15 (.close 18)))) (.step 23 (.close 15)))))))) (.run (.step 3 (.step 21 (.step 15 (.step 55 (.close 62))))))) (.run (.step 3 (.step 12 (.step 22 (.step 23 (.step 34 (.step 40 (.step 62 (.split 16 0 (.step 9 (.split 22 0 (.step 15 (.step 61 (.close 40))) (.step 3 (.step 15 (.close 21))))) (.step 3 (.step 21 (.close 15))))))))))))) (.run (.step 22 (.step 15 (.step 23 (.step 15 (.step 23 (.close 57)))))))) (.run (.step 21 (.step 15 (.step 53 (.close 18)))))) (.run (.step 12 (.step 21 (.step 15 (.step 26 (.close 52))))))) (.run (.step 15 (.step 24 (.step 31 (.step 3 (.close 15))))))) (.run (.step 3 (.step 12 (.step 21 (.step 23 (.step 32 (.step 34 (.step 40 (.step 61 (.step 62 (.split 40 1 (.split 17 0 (.step 9 (.split 36 0 (.split 51 0 (.split 22 0 (.step 15 (.close 22)) (.step 3 (.step 15 (.close 22)))) (.step 3 (.close 15))) (.step 3 (.step 15 (.close 23))))) (.step 3 (.step 22 (.close 15)))) (.step 3 (.step 31 (.close 15)))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231548175074603278939581360739519280709632⟩
def references : Fin 3 → Box := ![Part15.root, Part17.root, Part19.root]
def proof : Chunks.Proof 3 := (.split 12 1 (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 22 (.split 22 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 72 1 (.step 23 (.step 18 (.close 7))) (.step 18 (.close 22))))) (.step 18 (.close 67))) (.step 18 (.close 66)))) (.step 18 (.close 22))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 66 (.step 38 (.close 67))))) (.step 18 (.close 20))))))) (.run (.step 21 (.split 17 1 (.split 22 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.step 18 (.close 7)) (.step 18 (.close 21))) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.close 21))) (.step 18 (.close 61))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 42))) (.step 18 (.step 38 (.close 67)))) (.step 18 (.step 7 (.close 19)))) (.step 18 (.step 7 (.close 19))))))) (.reuse 1)) (.step 23 (.step 31 (.split 21 1 (.split 35 1 (.reuse 2) (.run (.step 21 (.step 22 (.step 15 (.step 38 (.close 18))))))) (.run (.step 9 (.step 15 (.step 24 (.step 18 (.step 15 (.close 24)))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part17.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231548175077138580140037819542512687120384⟩
def references : Fin 1 → Box := ![Part20.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.reuse 0) (.run (.split 12 1 (.split 14 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.step 18 (.step 31 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))))) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 7))) (.step 18 (.close 52))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 17))) (.step 3 (.close 31)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part21

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part21.excludes
end FiveColour.Packed.ProjectedChunks.Case101
