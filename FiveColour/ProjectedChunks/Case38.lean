module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case38
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721535917890207744⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨37630511536740859966423, 5789234131009369111655880410916383799149935097950111679937790244350696937832588910803674238545500183085609357535611307840729301634221804252716538090356296810875202044827950228461282219658217406305038239415791728186442646529, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333607532427808700155424991973343179088590124986613361869506463616058715241551421320018266029796606670665782908409084907698948166357345335057019116506840634427228966925369344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 57 1 (.split 59 1 (.split 52 1 (.split 67 1 (.split 5 0 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 48 (.step 3 (.step 7 (.step 10 (.close 48))))) (.step 3 (.step 28 (.close 3)))) (.step 7 (.close 3))) (.step 7 (.close 48))) (.step 7 (.close 58))) (.split 16 0 (.split 17 0 (.split 43 0 (.split 51 0 (.step 3 (.step 4 (.close 48))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 7 (.close 17))) (.step 7 (.step 18 (.close 3))))) (.step 7 (.close 3))) (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 43 0 (.split 51 0 (.step 3 (.step 4 (.close 8))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 7 (.close 8))) (.step 7 (.step 8 (.close 3)))) (.split 16 0 (.split 17 0 (.split 25 0 (.split 34 0 (.step 8 (.close 3)) (.step 4 (.close 3))) (.step 3 (.close 28))) (.step 7 (.close 8))) (.step 7 (.close 8)))) (.step 3 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.step 48 (.close 3)))) (.split 67 1 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.step 58 (.split 17 0 (.step 55 (.step 7 (.step 3 (.close 58)))) (.step 7 (.close 3)))) (.step 7 (.close 58))) (.step 48 (.step 7 (.step 3 (.close 17))))) (.step 7 (.close 3)))) (.step 48 (.step 3 (.step 7 (.close 8))))) (.step 7 (.step 3 (.close 62))))) (.step 3 (.split 52 1 (.split 10 0 (.step 60 (.step 3 (.close 48))) (.step 3 (.close 49))) (.step 48 (.step 3 (.close 60)))))))
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216962965697198491383587046510367216899573738619030867535914622262553063115121778601136276733218731474038235597660073501818968437838098499741190499897356320768⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 53 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 67 1 (.split 10 0 (.split 16 0 (.split 57 1 (.split 59 1 (.split 5 0 (.step 28 (.split 11 0 (.step 3 (.split 17 0 (.split 22 0 (.step 55 (.close 7)) (.step 3 (.close 4))) (.step 3 (.close 4)))) (.step 3 (.close 4)))) (.step 10 (.close 59))) (.step 5 (.step 28 (.close 58)))) (.step 28 (.step 51 (.close 60)))) (.step 5 (.step 43 (.step 50 (.step 7 (.step 28 (.step 3 (.close 8)))))))) (.step 58 (.split 57 1 (.step 3 (.step 7 (.close 59))) (.step 28 (.step 3 (.close 16)))))) (.step 3 (.step 7 (.close 26)))))) (.run (.step 58 (.step 5 (.close 31))))) (.run (.split 52 1 (.split 55 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.close 4)) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 3)))) (.step 8 (.split 25 0 (.step 56 (.close 48)) (.step 3 (.step 14 (.close 56)))))) (.step 8 (.close 3))) (.step 4 (.step 36 (.close 48)))) (.step 8 (.step 51 (.close 60)))) (.step 3 (.step 24 (.step 43 (.close 51))))) (.step 48 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.close 56))) (.step 8 (.step 3 (.close 17)))) (.step 3 (.close 51))))) (.step 48 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.close 56))) (.step 8 (.step 3 (.close 14)))) (.step 3 (.close 51))))) (.step 3 (.step 7 (.close 8)))) (.step 5 (.step 18 (.step 30 (.step 8 (.close 58)))))) (.step 3 (.step 8 (.step 48 (.close 19)))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 9797766621314684873895708907333611310075747216966320925768255444527386074741220752012962974214626175412773094685138378919474053106472080066558975336331034978967028360073267370996759364661365791776571392⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 50 1 (.split 51 1 (.step 58 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.step 58 (.split 17 0 (.step 55 (.step 7 (.step 3 (.close 58)))) (.step 7 (.close 3)))) (.step 7 (.close 49))) (.step 48 (.step 7 (.step 3 (.close 17))))) (.step 7 (.close 3)))) (.step 48 (.step 3 (.step 7 (.close 8))))) (.step 7 (.step 3 (.close 52)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 5 0 (.split 11 0 (.split 34 0 (.split 36 0 (.step 52 (.close 3)) (.step 55 (.close 7))) (.step 55 (.close 52))) (.step 48 (.close 7))) (.step 9 (.close 52))) (.step 48 (.close 7))) (.step 48 (.close 7))) (.step 48 (.close 7)))) (.step 48 (.close 49))) (.step 5 (.step 48 (.close 58)))) (.step 4 (.step 48 (.close 18))))) (.step 3 (.step 54 (.step 7 (.step 48 (.close 52)))))) (.step 55 (.split 53 1 (.split 56 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 52 (.step 55 (.step 7 (.close 52)))) (.step 27 (.step 52 (.close 21)))) (.step 55 (.close 52))) (.step 9 (.step 27 (.step 48 (.close 52))))) (.step 48 (.close 52))) (.step 48 (.close 44)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258493109954742702384210604007694103596633028146790946027889814942437258560771243922374072759807920345114128560690619651930700575115096742690816⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 3 (.close 54)))))) (.run (.step 55 (.split 51 1 (.step 58 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.step 58 (.split 17 0 (.step 55 (.step 7 (.step 3 (.close 58)))) (.step 7 (.close 3)))) (.step 7 (.close 50))) (.step 48 (.step 7 (.step 3 (.close 17))))) (.step 7 (.close 3)))) (.step 48 (.step 3 (.step 7 (.close 8))))) (.step 7 (.step 3 (.close 53)))) (.split 17 0 (.split 22 0 (.split 5 0 (.split 11 0 (.split 34 0 (.split 36 0 (.step 53 (.close 3)) (.step 55 (.close 7))) (.step 55 (.close 53))) (.step 48 (.close 7))) (.step 9 (.close 53))) (.step 48 (.close 7))) (.step 48 (.close 7)))) (.step 48 (.close 50))) (.step 5 (.step 48 (.close 58)))) (.step 4 (.step 35 (.step 48 (.close 8)))))) (.step 3 (.step 54 (.step 7 (.step 48 (.close 53))))))))) (.reuse 1)) (.run (.step 3 (.split 52 1 (.split 55 1 (.split 30 0 (.split 34 0 (.split 36 0 (.split 43 0 (.step 49 (.step 50 (.step 3 (.step 50 (.close 8))))) (.step 8 (.step 48 (.step 3 (.close 50))))) (.step 48 (.step 50 (.step 3 (.close 21))))) (.step 48 (.step 49 (.step 50 (.step 3 (.close 21)))))) (.step 3 (.close 50))) (.step 48 (.step 50 (.close 58)))) (.step 48 (.step 3 (.close 50)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515087042155977050166022829408021160073200469012344868829069661433123475167515768738886750139031826607302734471189470553603036938240⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 45 1 (.split 46 1 (.reuse 0) (.run (.split 47 1 (.step 3 (.split 52 1 (.split 55 1 (.split 30 0 (.split 36 0 (.split 43 0 (.step 50 (.step 49 (.step 3 (.step 49 (.close 18))))) (.step 8 (.step 48 (.step 3 (.close 49))))) (.step 48 (.step 49 (.step 3 (.close 21))))) (.step 3 (.step 49 (.close 3)))) (.step 48 (.step 49 (.close 48)))) (.step 48 (.step 3 (.close 49))))) (.step 49 (.step 3 (.close 50)))))) (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 48 (.step 31 (.step 48 (.step 4 (.close 18))))) (.step 48 (.close 53))) (.step 48 (.close 52))) (.step 48 (.close 50))) (.step 48 (.close 49))))) (.run (.split 45 1 (.split 46 1 (.step 3 (.split 53 1 (.split 55 1 (.split 56 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 54 (.split 38 0 (.step 70 (.split 49 1 (.step 7 (.close 3)) (.step 52 (.step 7 (.close 3))))) (.step 3 (.step 7 (.close 9))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.close 47))) (.step 3 (.step 7 (.step 27 (.close 46)))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070819612416902153342427555758679335880405010435516860832613450894501111135101152599692900564992⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 55 1 (.split 56 1 (.split 57 1 (.split 5 0 (.split 30 0 (.split 34 0 (.split 53 1 (.step 28 (.step 3 (.step 43 (.close 58)))) (.step 24 (.step 3 (.close 28)))) (.step 28 (.step 7 (.step 31 (.close 37))))) (.step 28 (.step 3 (.close 7)))) (.step 5 (.step 10 (.step 8 (.close 41))))) (.step 60 (.close 3))) (.step 28 (.step 41 (.close 3)))) (.step 5 (.step 41 (.step 58 (.close 31))))) (.step 5 (.step 43 (.step 59 (.step 7 (.step 28 (.step 3 (.close 8)))))))) (.step 5 (.step 41 (.step 43 (.step 50 (.step 60 (.step 5 (.close 41)))))))) (.step 58 (.split 53 1 (.split 57 1 (.split 5 0 (.step 3 (.step 7 (.close 41))) (.step 3 (.close 8))) (.step 3 (.close 41))) (.step 3 (.close 41))))) (.step 3 (.step 7 (.close 58)))) (.step 3 (.step 28 (.step 41 (.step 48 (.close 16)))))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 21 (.step 5 (.step 48 (.step 7 (.step 9 (.close 21)))))))) (.step 48 (.step 5 (.step 48 (.step 58 (.close 26)))))) (.step 21 (.step 28 (.step 41 (.step 50 (.close 55)))))) (.step 28 (.step 49 (.step 3 (.step 49 (.close 48)))))) (.step 21 (.step 31 (.step 48 (.step 4 (.step 10 (.step 16 (.close 41)))))))) (.step 10 (.close 46))) (.step 7 (.step 28 (.step 31 (.step 38 (.step 76 (.step 41 (.step 7 (.close 31))))))))))
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
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872270360586904047501897498942679454931441228244200275717726488393041638565502944574834099537368395932499968⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.close 7))) (.step 7 (.close 37))) (.step 7 (.close 39))) (.step 7 (.step 22 (.close 58)))) (.step 28 (.step 31 (.step 3 (.close 37))))) (.step 22 (.step 59 (.close 7)))) (.step 4 (.step 7 (.step 28 (.close 56))))) (.step 3 (.step 28 (.step 31 (.close 39))))) (.step 7 (.step 22 (.step 21 (.close 58))))) (.step 7 (.step 29 (.step 31 (.close 52))))) (.step 28 (.step 50 (.step 31 (.step 50 (.close 3)))))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 31)))))) (.step 45 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 55 1 (.step 45 (.step 7 (.step 31 (.close 3)))) (.step 31 (.close 39))) (.step 7 (.step 8 (.close 39)))) (.step 29 (.step 31 (.close 39)))) (.step 7 (.step 31 (.close 45)))) (.step 31 (.step 39 (.close 60)))) (.step 31 (.step 37 (.step 45 (.close 49))))))) (.step 28 (.step 38 (.step 39 (.split 49 1 (.step 41 (.step 7 (.close 31))) (.step 7 (.step 16 (.step 21 (.close 41))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646225306108056384960023375719349889697510367261388382142602357374124735779480414861667539615744⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.close 7))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 28 (.step 31 (.step 3 (.close 37))))) (.step 59 (.step 7 (.close 16)))) (.step 7 (.step 31 (.close 37)))) (.step 4 (.step 7 (.step 8 (.step 28 (.close 37)))))) (.step 3 (.step 31 (.close 37)))) (.step 7 (.step 29 (.step 31 (.close 37))))) (.step 7 (.step 31 (.close 16)))) (.step 28 (.step 49 (.step 50 (.step 3 (.close 31)))))) (.step 28 (.step 31 (.close 49)))) (.split 46 1 (.split 47 1 (.split 50 1 (.split 53 1 (.split 55 1 (.step 37 (.step 7 (.close 31))) (.step 31 (.close 37))) (.step 7 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 31 (.step 45 (.step 3 (.close 50))))) (.step 37 (.close 49)))) (.step 16 (.step 28 (.step 37 (.step 38 (.step 41 (.step 7 (.close 31)))))))) (.split 46 1 (.split 47 1 (.split 50 1 (.split 53 1 (.split 55 1 (.step 37 (.step 7 (.close 31))) (.step 31 (.close 37))) (.step 7 (.close 37))) (.step 7 (.step 31 (.close 37)))) (.step 28 (.step 31 (.step 39 (.close 50))))) (.step 37 (.close 49)))))))
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
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895559371364629164715370542796639060337024974723973896702948497365663744⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 28 (.split 52 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 55 1 (.split 57 1 (.split 5 0 (.split 30 0 (.split 46 0 (.split 53 1 (.step 28 (.close 3)) (.step 3 (.close 28))) (.step 28 (.close 48))) (.step 3 (.step 7 (.close 28)))) (.step 5 (.step 10 (.close 28)))) (.step 28 (.close 60))) (.step 5 (.step 28 (.close 48)))) (.step 5 (.step 43 (.step 59 (.step 7 (.step 28 (.step 3 (.close 8)))))))) (.step 5 (.step 43 (.step 50 (.step 60 (.step 5 (.close 28))))))) (.step 28 (.split 53 1 (.step 3 (.step 7 (.close 28))) (.step 3 (.close 8))))) (.step 3 (.step 7 (.close 58)))) (.step 3 (.step 28 (.close 48))))) (.step 3 (.step 7 (.close 54)))) (.step 48 (.step 5 (.step 48 (.step 9 (.close 58)))))) (.step 48 (.step 5 (.step 48 (.step 9 (.step 58 (.close 26))))))) (.step 28 (.step 3 (.step 49 (.close 50))))) (.step 28 (.step 3 (.step 49 (.close 3))))) (.step 28 (.step 31 (.step 48 (.step 4 (.step 10 (.step 16 (.close 28)))))))) (.step 7 (.step 28 (.close 29)))) (.step 28 (.step 21 (.step 3 (.close 58))))) (.step 7 (.step 28 (.close 29)))))
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895559371364629164715370542796639060337024974723973896702948497365663744⟩
def references : Fin 5 → Box := ![Part4.root, Part5.root, Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 5 := (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.close 7))) (.step 7 (.close 37))) (.step 7 (.close 45))) (.step 31 (.close 60))) (.step 59 (.close 45))) (.step 28 (.step 31 (.close 45)))) (.step 4 (.step 7 (.step 8 (.step 28 (.step 37 (.close 39))))))) (.step 3 (.step 31 (.close 45)))) (.step 7 (.step 31 (.close 45)))) (.step 7 (.step 29 (.step 31 (.close 45))))) (.step 28 (.step 50 (.step 31 (.step 50 (.close 3)))))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 31)))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.run (.step 31 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 7 (.step 41 (.step 3 (.close 7)))))))) (.reuse 4))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631854287161708843652182650314201779300856241265311744⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 22 1 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 5 0 (.step 7 (.step 18 (.close 19))) (.step 8 (.close 7))) (.step 8 (.step 18 (.step 3 (.close 19))))) (.step 5 (.step 7 (.step 8 (.close 59))))) (.step 36 (.step 56 (.close 7)))) (.step 3 (.step 8 (.step 18 (.close 20))))) (.step 7 (.step 11 (.step 18 (.close 20))))) (.step 7 (.step 11 (.step 17 (.step 18 (.close 36)))))) (.step 8 (.step 18 (.step 50 (.step 3 (.close 18)))))) (.step 8 (.step 49 (.step 18 (.step 49 (.close 3)))))) (.step 4 (.step 18 (.close 48)))) (.step 4 (.step 5 (.step 8 (.step 28 (.step 41 (.step 49 (.step 7 (.step 19 (.close 20)))))))))) (.step 4 (.step 5 (.step 28 (.step 3 (.step 8 (.step 49 (.step 19 (.close 51))))))))) (.split 25 1 (.step 25 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 56 1 (.step 25 (.step 7 (.step 18 (.close 3)))) (.step 7 (.step 20 (.close 19)))) (.step 11 (.step 18 (.close 20)))) (.step 7 (.step 18 (.close 25)))) (.step 18 (.step 20 (.close 50)))) (.step 8 (.step 18 (.step 49 (.close 3))))) (.step 18 (.close 25))) (.step 7 (.step 19 (.step 20 (.close 60)))))) (.step 7 (.step 20 (.step 28 (.step 25 (.close 49))))))))))
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
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 4898883310657342436947858505931971705553515434341103012552357296198779639748270754709956118805772190504843657117983833795418861944210109457748379433478721770642721178912513485564823321868206303287967744⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.step 7 (.step 18 (.close 19))) (.step 8 (.close 7))) (.step 7 (.step 8 (.close 18)))) (.step 8 (.step 18 (.step 3 (.close 19))))) (.step 7 (.step 8 (.close 19)))) (.step 56 (.step 7 (.close 18)))) (.step 7 (.step 18 (.close 19)))) (.step 7 (.step 18 (.close 19)))) (.step 8 (.step 18 (.close 50)))) (.step 8 (.step 49 (.step 18 (.step 49 (.close 3)))))) (.step 4 (.step 7 (.step 8 (.step 18 (.close 19)))))) (.step 4 (.step 5 (.step 8 (.step 24 (.step 41 (.close 19))))))) (.step 4 (.step 5 (.step 28 (.step 3 (.step 8 (.step 49 (.step 19 (.close 50))))))))) (.step 19 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 56 1 (.step 19 (.step 7 (.close 18))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 50))) (.step 8 (.step 18 (.step 49 (.close 3))))) (.step 18 (.close 19))) (.step 7 (.step 19 (.close 41)))) (.step 7 (.step 28 (.step 19 (.close 49))))))) (.step 19 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 56 1 (.step 19 (.step 7 (.close 18))) (.step 7 (.close 19))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 50))) (.step 8 (.step 18 (.step 49 (.close 3))))) (.step 18 (.close 19))) (.step 7 (.step 19 (.close 41)))) (.step 7 (.step 28 (.step 19 (.close 49)))))))))
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
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993512314372461856235306444415223878076369766068972945386739985450298197263237871194584240441669178324467728912275234737451104328482816⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 45 1 (.split 53 1 (.split 57 1 (.split 56 1 (.split 16 0 (.split 17 0 (.split 59 1 (.step 8 (.step 3 (.close 34))) (.step 4 (.close 48))) (.step 8 (.step 7 (.step 18 (.close 3))))) (.step 8 (.step 7 (.step 18 (.close 14))))) (.step 3 (.step 24 (.step 8 (.close 59))))) (.step 60 (.close 3))) (.step 8 (.step 14 (.close 3)))) (.step 4 (.step 48 (.close 14)))) (.step 4 (.step 24 (.step 51 (.step 24 (.step 8 (.step 3 (.close 56)))))))) (.step 4 (.step 14 (.step 24 (.step 49 (.step 60 (.step 4 (.close 14)))))))) (.step 48 (.split 56 1 (.split 57 1 (.split 16 0 (.split 17 0 (.step 3 (.step 7 (.step 8 (.step 3 (.close 7))))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 14))) (.step 3 (.close 14))) (.step 3 (.close 14))))) (.step 48 (.step 14 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.close 14))) (.step 3 (.close 14))) (.step 3 (.close 14)))))) (.step 3 (.step 7 (.close 48)))) (.step 5 (.step 18 (.step 30 (.step 8 (.step 3 (.step 34 (.close 58)))))))) (.step 3 (.step 48 (.close 14)))) (.step 3 (.step 7 (.close 48)))) (.step 4 (.step 48 (.step 58 (.step 27 (.close 48)))))) (.step 4 (.step 48 (.step 58 (.step 34 (.close 44)))))) (.step 8 (.step 3 (.step 49 (.step 50 (.close 14)))))) (.step 8 (.step 34 (.step 49 (.step 3 (.close 14)))))))
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
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556398928213668202491008521280159744⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 8 (.step 3 (.step 7 (.close 27)))))) (.run (.step 5 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.step 49 (.step 7 (.step 37 (.close 51)))))))))))) (.run (.step 4 (.step 49 (.step 50 (.step 60 (.split 42 1 (.split 53 1 (.step 43 (.step 24 (.split 5 0 (.step 43 (.close 41)) (.step 8 (.close 3))))) (.step 14 (.close 3))) (.step 3 (.close 41))))))))) (.run (.step 3 (.step 5 (.step 4 (.step 7 (.step 28 (.step 41 (.step 14 (.step 24 (.step 8 (.step 49 (.step 7 (.step 37 (.close 56))))))))))))))) (.run (.step 4 (.step 7 (.step 43 (.step 4 (.step 14 (.step 28 (.step 41 (.step 49 (.step 7 (.step 37 (.step 14 (.close 37)))))))))))))) (.run (.step 5 (.step 28 (.step 24 (.step 43 (.step 49 (.step 50 (.step 60 (.split 16 0 (.split 34 0 (.step 24 (.step 14 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 14)))))))))))) (.run (.step 7 (.step 8 (.step 73 (.split 25 1 (.step 17 (.step 14 (.step 7 (.step 18 (.close 3))))) (.step 3 (.step 5 (.close 14))))))))) (.run (.step 7 (.step 8 (.step 18 (.split 22 1 (.split 25 1 (.step 17 (.split 38 1 (.split 50 1 (.step 14 (.step 7 (.close 18))) (.step 7 (.step 14 (.close 18)))) (.step 5 (.close 14)))) (.step 3 (.close 14))) (.step 14 (.close 25)))))))) (.run (.step 7 (.step 8 (.step 19 (.step 35 (.split 25 1 (.step 17 (.step 14 (.step 7 (.step 18 (.close 3))))) (.step 3 (.step 5 (.close 14))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430720410017983365120⟩
def references : Fin 4 → Box := ![Part9.root, Part10.root, Part11.root, Part13.root]
def proof : Chunks.Proof 4 := (.split 10 1 (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 5 0 (.step 7 (.step 18 (.close 19))) (.step 8 (.close 7))) (.step 18 (.close 60))) (.step 5 (.step 7 (.step 8 (.close 59))))) (.step 56 (.close 25))) (.step 3 (.step 18 (.close 25)))) (.step 7 (.step 18 (.close 25)))) (.step 7 (.step 18 (.close 25)))) (.step 8 (.step 18 (.step 50 (.step 3 (.close 18)))))) (.step 8 (.step 49 (.step 18 (.step 49 (.close 3)))))) (.step 4 (.step 7 (.step 8 (.step 18 (.close 25)))))) (.step 4 (.step 5 (.step 8 (.step 28 (.step 41 (.step 49 (.step 7 (.step 19 (.close 20)))))))))) (.step 4 (.step 5 (.step 28 (.step 3 (.step 8 (.step 49 (.step 25 (.close 50))))))))))))) (.reuse 1)) (.step 7 (.reuse 2))) (.reuse 3)) (.run (.step 18 (.split 11 1 (.split 25 1 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 3 (.step 49 (.step 7 (.close 41))))) (.step 28 (.step 3 (.close 7)))) (.step 7 (.step 14 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2251801961168896, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070821649452878487828513824204367745258566061905372028406194989954421800949345429483451626553344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 8 (.split 52 1 (.split 55 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 45 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 68 (.close 8)) (.step 3 (.close 28))) (.step 7 (.close 8))) (.step 7 (.close 8))) (.step 7 (.close 8))) (.step 8 (.close 3))) (.step 4 (.step 8 (.close 48)))) (.step 8 (.close 60))) (.step 3 (.step 24 (.step 43 (.step 51 (.step 10 (.step 8 (.close 28)))))))) (.step 4 (.step 8 (.close 48)))) (.step 8 (.split 56 1 (.step 3 (.step 7 (.close 8))) (.step 3 (.close 8))))) (.step 8 (.split 56 1 (.step 3 (.step 7 (.close 8))) (.step 3 (.close 8))))) (.step 3 (.step 7 (.close 8)))) (.step 5 (.step 18 (.step 30 (.step 8 (.close 48)))))) (.step 3 (.step 8 (.close 48))))) (.step 3 (.step 7 (.close 48)))) (.step 4 (.step 48 (.step 8 (.close 44))))) (.step 4 (.step 48 (.step 58 (.step 48 (.close 44)))))) (.step 8 (.step 3 (.step 49 (.close 50))))) (.step 8 (.step 3 (.step 49 (.close 3))))) (.step 8 (.step 3 (.step 7 (.close 27))))) (.step 5 (.step 4 (.step 7 (.step 8 (.step 28 (.step 49 (.step 45 (.close 50))))))))) (.step 4 (.step 8 (.step 43 (.step 60 (.split 42 1 (.step 24 (.split 11 0 (.step 10 (.step 8 (.close 41))) (.step 8 (.close 3)))) (.step 3 (.close 41)))))))))
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721535917890207744⟩
def references : Fin 2 → Box := ![Part14.root, Part15.root]
def proof : Chunks.Proof 2 := (.split 5 1 (.reuse 0) (.split 11 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 36 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 4 (.step 7 (.step 28 (.step 41 (.step 24 (.step 8 (.step 3 (.step 49 (.step 45 (.close 51)))))))))))))) (.run (.step 4 (.step 7 (.step 43 (.step 4 (.step 8 (.step 28 (.step 41 (.step 49 (.step 7 (.step 37 (.step 8 (.step 37 (.close 50))))))))))))))) (.run (.step 3 (.step 5 (.step 8 (.step 28 (.step 24 (.step 43 (.step 47 (.close 3)))))))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 7 (.step 8 (.close 11))))) (.run (.step 8 (.step 24 (.close 48))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part16.excludes
end FiveColour.Packed.ProjectedChunks.Case38
