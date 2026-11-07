module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case151
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 14696649931972027310843567413265583015629262651307423938320615792288773154838020595935173605717644463105175303345326977828138302626100091496850794625007529270445119409878094273833412394513569251137159168⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37630511536740893520887, 5789234131009374248507346766749886964179117598075761631441503938856419104125729984377942245333425284026394393415169773689373755704242316349912225571028696891635007459092358541327061333498215709696615525420286517587399934977, 0⟩]
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
def root : Box := ⟨4294967296, 4898883310657342436947858505931971701868001735642512442229206807832778944011750382651850100830794504100103190411864350211184316107263726305311962047735046986018695669146693605478874093878736758079750144⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 59 1 (.split 11 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 47 1 (.split 51 0 (.split 53 0 (.step 55 (.step 60 (.close 3))) (.step 18 (.close 48))) (.step 3 (.close 48))) (.step 50 (.close 3))) (.step 18 (.step 3 (.close 48)))) (.step 18 (.close 48))) (.step 31 (.step 18 (.close 48)))) (.step 31 (.step 18 (.close 48)))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 12 (.step 18 (.step 3 (.close 48)))) (.step 3 (.close 8))) (.step 3 (.close 60))) (.step 3 (.step 12 (.step 18 (.close 4))))) (.step 18 (.close 31)))) (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 48 (.step 55 (.step 3 (.close 48)))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 3 (.close 58)))) (.split 59 1 (.split 16 0 (.split 17 0 (.split 45 0 (.split 47 1 (.split 49 0 (.split 50 0 (.split 52 0 (.step 3 (.step 51 (.step 3 (.close 16)))) (.step 3 (.close 31))) (.step 3 (.step 22 (.close 48)))) (.step 3 (.step 22 (.close 48)))) (.step 32 (.step 50 (.close 3)))) (.step 31 (.step 48 (.step 21 (.step 3 (.close 48)))))) (.step 22 (.step 18 (.close 59)))) (.step 31 (.step 18 (.close 12)))) (.step 3 (.step 31 (.close 48))))))
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
def root : Box := ⟨4294967296, 9797766621314684873895708907333611306390237033044135615707889977576203376928351677159002817796921222013965973601125594359510535880928721815229463473574550868477042773333882382647750251160316848682041344⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 43 1 (.split 46 1 (.step 3 (.split 53 1 (.reuse 0) (.run (.step 51 (.split 59 1 (.split 34 0 (.split 47 1 (.split 49 0 (.split 50 0 (.split 52 0 (.split 55 0 (.step 3 (.step 51 (.step 3 (.close 12)))) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 50 (.close 3))) (.step 3 (.step 14 (.step 18 (.close 31))))) (.step 3 (.step 18 (.close 48)))))))) (.run (.step 32 (.step 51 (.step 69 (.split 10 0 (.step 60 (.step 49 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 55 (.close 3)) (.step 31 (.close 49))) (.step 18 (.close 49))) (.step 31 (.close 48))) (.step 18 (.close 49))) (.step 12 (.close 3))) (.step 12 (.step 31 (.step 3 (.close 49))))) (.step 12 (.step 49 (.close 3)))))) (.step 12 (.close 3)))))))) (.run (.step 3 (.close 47)))) (.run (.step 3 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 48 (.step 53 (.close 3))) (.step 21 (.close 32))) (.step 31 (.close 48))) (.step 31 (.close 48))) (.step 3 (.close 48))) (.step 3 (.close 50))) (.step 3 (.close 50))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 18 (.close 50)))))))
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
def root : Box := ⟨4294967296, 9797766621314684873895708907333611306390237033044135618904560493099779421865814925715372435772528584682068005105739416727407327386083004729834109702103839004460266750911948151909312046481609135801499648⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 38 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 49 1 (.reuse 0) (.run (.step 3 (.split 50 1 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.step 48 (.step 52 (.close 3))) (.step 31 (.step 32 (.close 48)))) (.step 31 (.close 48))) (.step 3 (.close 48))) (.step 3 (.close 49))) (.step 3 (.close 49))) (.step 3 (.close 12))) (.step 3 (.step 31 (.close 49)))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 55 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.step 52 (.close 3)) (.step 3 (.close 58))) (.step 3 (.close 48))) (.step 3 (.close 48))) (.step 3 (.close 48))) (.step 3 (.close 12))) (.step 3 (.close 58))) (.step 3 (.close 48)))))))) (.run (.step 31 (.close 60)))) (.run (.step 31 (.step 3 (.close 12))))) (.run (.step 31 (.close 49)))) (.run (.step 31 (.step 32 (.split 49 1 (.split 56 1 (.step 3 (.split 53 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 28 (.step 32 (.split 45 0 (.split 46 1 (.step 31 (.close 3)) (.step 12 (.step 31 (.close 49)))) (.step 31 (.step 3 (.close 48)))))) (.step 31 (.close 60))) (.step 31 (.step 5 (.close 59)))) (.step 21 (.step 18 (.close 41)))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 24 (.step 32 (.step 43 (.step 41 (.step 12 (.step 18 (.close 31)))))))))) (.step 28 (.step 41 (.step 3 (.split 59 1 (.step 41 (.close 3)) (.step 3 (.close 41))))))) (.step 3 (.step 21 (.step 31 (.close 48))))))))) (.run (.step 18 (.step 3 (.close 32)))))
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
def root : Box := ⟨4294967296, 9797766621314684873895708907333611317446767574513495049299739929588848438223982563654162753280945479932920043363988006823481717555005175261479739675046288898435165584387195918784806851978115781119442944⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 11 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 18 (.step 3 (.close 32))))) (.run (.step 18 (.step 3 (.close 32))))) (.run (.step 12 (.step 18 (.split 34 1 (.split 36 1 (.split 42 1 (.split 50 1 (.split 53 1 (.step 3 (.split 59 1 (.split 34 0 (.split 36 0 (.split 38 1 (.split 56 1 (.split 42 0 (.step 8 (.step 12 (.split 47 1 (.step 18 (.step 3 (.close 48))) (.step 32 (.step 18 (.close 50)))))) (.step 3 (.step 12 (.step 18 (.close 4))))) (.step 12 (.step 24 (.step 18 (.close 32))))) (.step 12 (.step 24 (.step 18 (.close 32))))) (.step 3 (.step 12 (.step 18 (.step 31 (.close 32)))))) (.step 18 (.step 14 (.step 31 (.close 32))))) (.step 3 (.step 18 (.close 48))))) (.step 8 (.step 14 (.step 3 (.split 59 1 (.step 14 (.close 3)) (.step 3 (.close 14))))))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 3 (.step 12 (.close 31)))) (.step 3 (.step 12 (.close 31)))) (.step 3 (.step 14 (.close 31)))))))) (.run (.step 18 (.step 58 (.step 3 (.split 11 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.step 58 (.step 5 (.close 31))) (.step 48 (.close 52))) (.step 32 (.step 48 (.step 50 (.close 48))))) (.step 48 (.step 49 (.close 48)))) (.step 3 (.close 31))) (.step 5 (.step 32 (.step 41 (.step 3 (.step 31 (.close 48))))))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 5 (.step 12 (.step 18 (.step 48 (.step 14 (.step 3 (.close 50)))))))))))))
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
def root : Box := ⟨4294967296, 9797766621314684873895708907333611317446767581378292709430349644579471301996923063610189939118906943739627198877779006944515652067732487380295069732256892898481186408238334177776644799754559291777875968⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 45 1 (.split 52 1 (.reuse 0) (.run (.step 55 (.step 18 (.step 31 (.split 11 1 (.split 38 1 (.split 46 1 (.split 53 1 (.split 56 1 (.split 11 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 55 (.step 32 (.step 48 (.step 3 (.close 22))))) (.step 31 (.close 48))) (.step 3 (.close 55))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 31 (.step 48 (.close 21))))) (.step 3 (.step 18 (.step 48 (.close 12))))) (.step 48 (.step 3 (.close 49)))) (.step 3 (.step 21 (.step 31 (.step 41 (.close 48)))))) (.step 3 (.step 12 (.step 14 (.step 18 (.close 48))))))))))) (.run (.step 31 (.step 48 (.step 3 (.split 16 1 (.split 17 1 (.split 22 1 (.split 11 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.step 48 (.step 4 (.close 18))) (.step 48 (.close 3))) (.step 48 (.close 50))) (.step 48 (.close 49))) (.step 21 (.step 31 (.step 48 (.step 4 (.close 41)))))) (.step 4 (.step 12 (.step 14 (.step 18 (.close 48)))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 18))))))))
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
def root : Box := ⟨4294967296, 14696649931972027310843567413257846392658371458550119394445373915654732525845264768895508501017623726747117819328100419281926657622636898851354696638627245502438238374929638045331422981360844297824370688⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.step 3 (.split 59 2 (.reuse 0) (.run (.step 3 (.step 55 (.step 58 (.split 36 1 (.split 38 1 (.split 42 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 62 (.close 3)) (.step 3 (.close 58))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.close 48))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.close 48))) (.step 3 (.close 58))) (.step 3 (.close 48))) (.step 52 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 34 0 (.step 62 (.close 3)) (.step 3 (.step 31 (.close 48)))) (.step 3 (.close 62))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.close 48))) (.step 3 (.close 58))) (.step 3 (.close 48))))) (.step 48 (.close 53))) (.step 48 (.close 52))) (.step 48 (.close 62))) (.step 31 (.close 52))) (.step 31 (.step 48 (.close 62)))) (.step 31 (.close 52)))))))))
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
def root : Box := ⟨11321887274464624056724663742964806672750763661249321285128618900736872487176446556258380175532976302624405125092291534699311753889774377897684302754298088130952480948224, 14696649931972027310843567413265583015629255618322214581336399866881112214347118471773679723933127256280021724474876979068540858096096909020167762520671775200929584199826388985546860008250325558244671488⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 10 (.step 31 (.step 51 (.step 58 (.step 60 (.split 52 1 (.split 11 1 (.split 38 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 45 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.step 28 (.split 67 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 59 (.step 48 (.close 49))) (.step 31 (.step 43 (.close 59)))) (.step 31 (.close 59))) (.step 31 (.step 41 (.step 18 (.close 50))))) (.step 12 (.step 43 (.step 50 (.step 59 (.close 3)))))) (.step 3 (.close 59)))) (.step 3 (.step 31 (.close 60)))) (.step 5 (.step 58 (.step 51 (.step 49 (.close 59)))))) (.step 3 (.close 51))) (.step 3 (.step 21 (.step 31 (.step 50 (.close 53)))))) (.step 49 (.close 58))) (.step 31 (.step 48 (.step 49 (.step 50 (.close 59)))))) (.step 5 (.step 18 (.step 49 (.close 59))))) (.step 18 (.close 59))) (.step 5 (.step 18 (.step 49 (.close 50))))) (.step 28 (.step 32 (.step 41 (.split 22 1 (.step 59 (.step 3 (.step 21 (.close 41)))) (.step 5 (.close 41))))))) (.step 12 (.step 41 (.step 43 (.step 50 (.step 51 (.step 24 (.step 14 (.close 59))))))))) (.step 3 (.step 48 (.step 49 (.step 50 (.close 59)))))))))))))
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
def root : Box := ⟨10544329205960616522212199627389019981725852621020117108829895873308994329698799696060251608055994196445127134297314597945019373567564764896113707455157022752768, 14696649931972027310843567413265583015629262647875018555080748008347530473693772955675427070677866476210603930471096778268338231597168946349632059272094640077328214212742100695390124084055295660063195136⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 30 (.step 48 (.step 51 (.step 58 (.step 60 (.split 52 1 (.split 34 1 (.split 11 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.step 8 (.split 38 1 (.split 67 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 56 (.step 48 (.close 49))) (.step 18 (.step 24 (.close 56)))) (.step 24 (.step 32 (.step 49 (.close 56))))) (.step 18 (.close 56))) (.step 18 (.step 24 (.step 49 (.close 56))))) (.step 3 (.close 56))) (.step 24 (.step 32 (.step 49 (.step 51 (.step 43 (.close 56)))))))) (.step 48 (.close 60))) (.step 5 (.step 18 (.step 48 (.step 49 (.step 50 (.step 56 (.close 58)))))))) (.step 3 (.close 51))) (.step 48 (.close 50))) (.step 48 (.close 49))) (.step 4 (.step 31 (.step 49 (.close 56))))) (.step 31 (.close 56))) (.step 8 (.step 12 (.split 42 1 (.step 56 (.step 3 (.step 12 (.close 14)))) (.step 4 (.close 14)))))) (.step 4 (.step 14 (.step 31 (.close 49))))) (.step 3 (.step 48 (.step 49 (.step 50 (.close 56))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨9820171823688425610039569090482797456649926138129194368449874104288401389214023664649810276977712471452660052382680213027651769637656179159989877735424, 14696649931972027310843567413265583015629262647875025101861963800631270500073166610873731503961958562340182897053832970535931040946278712889816711080408941850696469332884119129903215854841402317118373888⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 48 (.step 55 (.step 58 (.split 59 1 (.step 31 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 53 (.step 48 (.close 3))) (.step 3 (.close 32))) (.step 3 (.close 58))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.close 48))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.close 48))) (.step 3 (.close 58))) (.step 3 (.close 48)))) (.step 55 (.step 62 (.split 36 1 (.split 56 1 (.split 11 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 53 1 (.split 17 0 (.step 53 (.close 3)) (.step 3 (.step 48 (.close 53)))) (.step 3 (.close 48))) (.step 3 (.close 32))) (.step 3 (.step 21 (.close 53)))) (.step 3 (.step 52 (.step 31 (.close 48))))) (.step 3 (.close 48))) (.step 31 (.step 48 (.close 53)))) (.step 31 (.close 53))))))))))
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
def root : Box := ⟨9590011546570728134804266689924606891259693494266791375439330179969141981654319985009580348611047335402988332404961145534816181286773612465218387968, 14696649931972027310843567413265583015629262647875025108255304831678422589942677737490136098135087558518043814013386423848692362049158702896203610154440498786022024269524882819780670046023810624400654336⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 48 (.step 55 (.step 58 (.split 50 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 36 1 (.split 38 1 (.split 59 1 (.step 31 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 52 (.step 48 (.close 3))) (.step 3 (.close 58))) (.step 3 (.close 58))) (.step 3 (.close 58))) (.step 3 (.close 48))) (.step 3 (.close 48))) (.step 3 (.close 48))) (.step 3 (.close 12))) (.step 3 (.close 58))) (.step 3 (.close 48)))) (.step 55 (.step 62 (.split 56 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 53 1 (.split 16 0 (.step 62 (.close 3)) (.step 3 (.step 48 (.close 52)))) (.step 3 (.close 48))) (.step 3 (.close 52))) (.step 3 (.close 62))) (.step 3 (.close 52))) (.step 48 (.close 52)))))) (.step 31 (.step 48 (.close 52)))) (.step 31 (.close 52))) (.step 18 (.close 52))) (.step 18 (.close 52))) (.step 18 (.close 52))) (.step 53 (.step 55 (.split 36 1 (.split 42 1 (.split 56 1 (.split 22 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 53 1 (.split 16 0 (.split 17 0 (.step 52 (.close 3)) (.step 3 (.step 48 (.close 52)))) (.step 3 (.close 53))) (.step 3 (.close 48))) (.step 3 (.close 32))) (.step 3 (.step 21 (.close 52)))) (.step 3 (.step 21 (.close 52)))) (.step 18 (.close 52))) (.step 31 (.step 48 (.close 52)))) (.step 31 (.close 52))) (.step 31 (.close 52)))))))))))
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
def root : Box := ⟨4294967296, 14696649931972027310843567413265583015629262647875025108255310928843559925865004654672225537913028473748791206535165445639629130353336085250930407627298044668778195806499729317091012717851309234332893184⟩
def references : Fin 5 → Box := ![Part5.root, Part6.root, Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 5 := (.split 47 2 (.split 49 2 (.split 50 2 (.split 53 2 (.split 56 2 (.split 57 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 58 (.step 69 (.split 17 1 (.split 22 1 (.split 36 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 49 1 (.split 50 1 (.split 34 0 (.step 60 (.close 3)) (.step 31 (.close 60))) (.step 48 (.close 3))) (.step 48 (.close 3))) (.step 51 (.step 31 (.close 60)))) (.step 58 (.step 50 (.step 18 (.close 60))))) (.step 12 (.close 60))) (.step 50 (.step 51 (.close 60)))) (.step 58 (.close 60))) (.step 50 (.step 51 (.close 60)))) (.step 50 (.close 3))) (.step 49 (.close 3))) (.step 49 (.step 50 (.close 60)))) (.step 32 (.close 60))) (.step 31 (.close 60))) (.step 18 (.close 60))) (.step 18 (.close 60))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.run (.step 12 (.step 47 (.step 48 (.step 51 (.step 69 (.split 52 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 60 (.step 50 (.close 3))) (.step 48 (.close 50))) (.step 48 (.close 49))) (.step 31 (.close 50))) (.step 48 (.close 50))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨7387876161823964852302320018776927588452451113212271250240305013296072832155726989640174922790921682651247043149824, 14696649931972027310843567413265583015629262651307423938320615792288773154835312910687008747453988873180954497758459105116150503069821761987446966540778818526891191050153727098763724870108880750000472064⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 10 (.step 31 (.step 32 (.step 49 (.step 58 (.step 60 (.split 52 2 (.split 53 2 (.split 56 1 (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 45 1 (.split 49 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 59 1 (.step 28 (.split 53 1 (.split 67 1 (.split 11 0 (.split 17 0 (.split 22 0 (.step 41 (.step 3 (.close 48))) (.step 31 (.step 32 (.close 41)))) (.step 31 (.step 32 (.step 18 (.close 41))))) (.step 12 (.step 32 (.step 43 (.step 41 (.close 3)))))) (.step 3 (.close 26))) (.step 32 (.step 43 (.step 41 (.step 3 (.step 12 (.close 60)))))))) (.step 3 (.step 41 (.close 48)))) (.step 3 (.step 5 (.step 28 (.step 32 (.step 41 (.close 48))))))) (.step 3 (.step 21 (.step 41 (.close 48))))) (.step 3 (.close 41))) (.step 3 (.step 21 (.step 31 (.step 48 (.close 41)))))) (.step 21 (.step 31 (.step 48 (.step 4 (.step 12 (.close 41))))))) (.step 5 (.step 18 (.close 41)))) (.step 5 (.step 18 (.close 41)))) (.step 18 (.close 41))) (.step 4 (.step 12 (.step 18 (.step 32 (.step 43 (.step 41 (.step 24 (.step 41 (.close 14)))))))))) (.step 28 (.step 41 (.split 22 1 (.step 59 (.step 3 (.step 21 (.step 41 (.close 48))))) (.step 18 (.close 41)))))) (.step 14 (.step 18 (.step 24 (.step 43 (.step 49 (.step 51 (.step 41 (.close 56))))))))) (.step 3 (.step 21 (.step 48 (.step 41 (.close 49))))))))))))))
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
def root : Box := ⟨3894222643901120721397876541882368, 14696649931972027310843567413265583015629262651307423938320615792288773154835312910687008747453988873180954497758459105116150503069821761987446966540778818526891191050156323247192992283923145998165082112⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 12 (.step 14 (.step 18 (.step 30 (.step 48 (.step 50 (.step 58 (.step 60 (.split 38 2 (.split 52 2 (.split 56 2 (.split 34 1 (.split 36 1 (.split 42 1 (.split 45 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 59 1 (.step 8 (.split 67 1 (.split 34 0 (.split 38 1 (.split 56 1 (.split 36 0 (.split 38 0 (.split 42 0 (.step 14 (.step 3 (.close 48))) (.step 18 (.step 12 (.close 14)))) (.step 12 (.step 14 (.step 3 (.close 4))))) (.step 18 (.step 12 (.step 14 (.close 31))))) (.step 12 (.step 24 (.step 14 (.step 3 (.step 32 (.close 60))))))) (.step 12 (.step 24 (.step 32 (.step 14 (.step 43 (.step 14 (.close 31)))))))) (.step 14 (.close 3))) (.step 3 (.close 14)))) (.step 3 (.step 14 (.close 48)))) (.step 5 (.step 12 (.step 18 (.step 48 (.step 14 (.step 48 (.step 32 (.close 58))))))))) (.step 3 (.step 12 (.step 14 (.close 48))))) (.step 3 (.close 14))) (.step 3 (.step 48 (.close 14)))) (.step 4 (.step 12 (.step 14 (.close 48))))) (.step 3 (.step 31 (.close 14)))) (.step 4 (.step 31 (.close 14)))) (.step 4 (.step 14 (.close 31)))) (.step 24 (.step 31 (.step 41 (.step 43 (.step 50 (.step 51 (.step 14 (.close 59))))))))) (.step 3 (.step 12 (.step 48 (.step 14 (.close 50)))))) (.step 12 (.step 24 (.step 32 (.step 41 (.step 43 (.step 60 (.step 14 (.close 31)))))))))))))))))))
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
def root : Box := ⟨4294967296, 14696649931972027310843567413265583015629262651307423938320615792288773154838020595935173605717644463105175303345326977828138302626100091496850794625007529270445119409878094273833412394513569251137159168⟩
def references : Fin 3 → Box := ![Part10.root, Part11.root, Part12.root]
def proof : Chunks.Proof 3 := (.step 18 (.step 31 (.split 11 2 (.split 38 2 (.step 55 (.split 46 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 48 (.step 51 (.step 69 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 47 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 16 0 (.split 17 0 (.split 49 1 (.split 50 1 (.step 49 (.step 60 (.step 48 (.close 3)))) (.step 48 (.close 3))) (.step 48 (.close 3))) (.step 50 (.step 49 (.step 3 (.close 49))))) (.step 58 (.step 49 (.close 3)))) (.step 49 (.close 3))) (.step 49 (.close 3))) (.step 48 (.close 49))) (.step 49 (.close 3))) (.step 49 (.close 3))) (.step 31 (.close 49))) (.step 32 (.close 49))) (.step 31 (.close 49))) (.step 31 (.close 49))) (.step 18 (.close 49))) (.step 18 (.close 49)))))))))))) (.reuse 1)) (.reuse 2))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case151
