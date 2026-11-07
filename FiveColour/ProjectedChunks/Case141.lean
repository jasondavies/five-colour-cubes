module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case141
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832589376755928668997108682832894707710076462020591537455646557167570371154622406493550142303538630521549672475708231706497879131967835682908788838197502738898984022354952192⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩]
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
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339634696057390253540763535145171875499029040707506839823264090299810180582116437636741824471729722909746522102883928191210397205058556300877223998864353764236199786324258219497619456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 1 (.split 22 1 (.split 35 1 (.split 38 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 74 1 (.step 31 (.split 72 1 (.split 2 0 (.split 14 0 (.split 16 0 (.step 31 (.step 3 (.step 32 (.step 3 (.close 18))))) (.step 18 (.close 31))) (.split 34 0 (.step 67 (.step 18 (.step 3 (.close 31)))) (.step 3 (.step 12 (.close 31))))) (.split 14 0 (.step 31 (.step 66 (.step 3 (.step 18 (.close 5))))) (.step 23 (.step 12 (.step 18 (.close 31)))))) (.step 29 (.split 2 0 (.split 63 1 (.split 16 0 (.split 17 0 (.step 75 (.close 31)) (.step 18 (.step 31 (.close 12)))) (.step 18 (.step 31 (.close 12)))) (.step 66 (.close 3))) (.step 31 (.step 3 (.step 12 (.close 75)))))))) (.step 18 (.step 69 (.split 2 0 (.step 69 (.split 63 1 (.step 18 (.step 31 (.step 3 (.close 5)))) (.step 12 (.step 18 (.close 66))))) (.step 23 (.step 66 (.step 67 (.step 31 (.close 18))))))))) (.step 3 (.close 66))) (.step 31 (.step 18 (.step 5 (.close 12))))) (.step 3 (.close 51))) (.step 3 (.close 47))) (.step 31 (.split 43 1 (.step 51 (.step 31 (.step 63 (.step 66 (.step 5 (.close 18)))))) (.step 3 (.close 10))))) (.step 9 (.step 31 (.step 32 (.split 51 1 (.step 75 (.step 3 (.step 29 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.step 66 (.step 31 (.close 3)))) (.step 31 (.close 69))) (.step 18 (.step 31 (.close 74)))) (.step 18 (.step 31 (.close 77)))) (.step 3 (.step 31 (.close 77))))))) (.step 3 (.close 21))))))) (.step 18 (.close 32))) (.step 18 (.close 32))))
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
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339634696057390253540763535145171875499029040707506839823264090299810180582116437636741824471729722909746522102883928191210397205058557762380255126342180131867378484999318398025334784⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 18 (.close 32)))) (.run (.step 12 (.step 18 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.step 27 (.split 51 1 (.split 56 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 34 0 (.split 35 1 (.split 36 0 (.step 11 (.step 67 (.split 38 0 (.split 42 0 (.step 12 (.step 3 (.close 18))) (.step 3 (.step 12 (.close 31)))) (.step 12 (.step 18 (.close 5)))))) (.step 3 (.step 12 (.step 18 (.step 31 (.close 32)))))) (.step 12 (.step 32 (.step 3 (.close 38))))) (.step 18 (.step 5 (.step 17 (.step 31 (.close 32)))))) (.step 23 (.step 31 (.step 17 (.step 5 (.close 32)))))) (.step 17 (.close 77))) (.step 3 (.close 12))) (.step 5 (.close 17))) (.step 3 (.close 12)))) (.step 3 (.step 12 (.close 31)))) (.step 12 (.step 18 (.close 5)))) (.step 3 (.step 12 (.close 31)))) (.step 31 (.close 12))))))) (.run (.step 3 (.step 18 (.step 31 (.split 14 1 (.split 74 1 (.split 35 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 5 (.step 3 (.close 31))) (.step 3 (.step 5 (.close 32)))) (.step 5 (.close 31))) (.step 3 (.step 5 (.close 12)))) (.step 5 (.close 74))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 31 (.step 5 (.step 12 (.close 75)))))) (.step 31 (.step 32 (.step 5 (.close 38))))) (.step 5 (.close 77))) (.step 5 (.close 17))))))))
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
def root : Box := ⟨4294967296, 23134333391815002265362563816272539653001741065417238379830951705730071083880018822481353363894000874126468754825662803999606392533769069051109454144835882449508648208339714170418975881596540922778200140680031900497120067584⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 74 2 (.split 65 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.split 14 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 31 (.split 16 0 (.step 63 (.step 3 (.close 18))) (.step 3 (.close 18)))) (.step 3 (.close 18))) (.step 3 (.close 63))) (.step 3 (.step 18 (.step 12 (.close 23))))) (.step 3 (.step 31 (.close 21)))) (.step 63 (.step 3 (.close 66)))) (.step 10 (.step 18 (.close 63)))) (.step 18 (.step 21 (.step 31 (.step 5 (.step 3 (.close 22))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 12 (.step 18 (.close 17)))))))))) (.run (.step 18 (.step 27 (.split 65 1 (.split 14 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 51 1 (.step 11 (.split 35 1 (.split 56 1 (.split 34 0 (.step 77 (.step 66 (.step 31 (.step 3 (.close 5))))) (.step 17 (.step 18 (.step 66 (.step 5 (.close 77)))))) (.step 5 (.step 18 (.step 66 (.close 74))))) (.step 23 (.step 32 (.step 66 (.step 31 (.step 74 (.close 77)))))))) (.step 3 (.close 51))) (.step 31 (.close 77))) (.step 5 (.step 18 (.step 12 (.close 67))))) (.step 31 (.step 66 (.close 74)))) (.step 5 (.step 17 (.step 31 (.close 66))))) (.step 17 (.close 31))) (.step 3 (.step 23 (.step 66 (.step 67 (.close 77))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129099878292929656859322879272865139657611978331117260307525794616938133160112630521832991598416855934954712553921526637361505678747306967044063312620971099963579962916051185855081127099985783798366208⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 56 2 (.split 63 2 (.split 64 2 (.split 71 2 (.step 3 (.split 72 2 (.reuse 0) (.run (.step 29 (.step 31 (.step 38 (.split 65 1 (.split 14 1 (.split 16 1 (.split 17 1 (.step 75 (.step 66 (.step 3 (.close 18)))) (.step 18 (.step 66 (.close 74)))) (.step 18 (.step 66 (.close 67)))) (.step 12 (.step 67 (.step 69 (.step 74 (.step 3 (.step 31 (.close 17)))))))) (.step 3 (.step 66 (.step 67 (.close 75))))))))))) (.run (.step 32 (.step 47 (.step 51 (.step 69 (.step 74 (.step 3 (.close 74))))))))) (.run (.step 47 (.step 51 (.step 67 (.step 3 (.step 18 (.step 67 (.step 31 (.close 63)))))))))) (.run (.step 47 (.step 51 (.step 66 (.step 18 (.step 31 (.step 69 (.split 56 1 (.step 66 (.step 5 (.close 31))) (.step 31 (.close 66))))))))))) (.run (.step 3 (.step 18 (.split 63 2 (.split 64 2 (.split 65 1 (.step 31 (.step 5 (.split 71 1 (.split 51 1 (.split 63 1 (.step 28 (.step 41 (.step 18 (.close 5)))) (.step 31 (.step 41 (.step 5 (.close 66))))) (.step 3 (.close 18))) (.step 22 (.close 74))))) (.step 3 (.step 10 (.step 41 (.step 43 (.step 31 (.close 63))))))) (.step 31 (.close 67))) (.step 5 (.step 31 (.step 63 (.close 66)))))))))
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
def root : Box := ⟨4181389724724491839037947176121572077338624, 23134344433892286795713129104550232122101987226767832589376755928668997108682832894707710076462017883852207481698903914781230401600906682269591550830965271342966304403622269168388413907323187017811557082628308560769380777984⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 5 (.step 12 (.step 17 (.step 18 (.step 27 (.step 67 (.step 68 (.step 74 (.step 75 (.split 35 2 (.split 65 1 (.split 72 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 51 1 (.step 11 (.split 56 1 (.split 67 1 (.split 35 0 (.split 36 0 (.step 17 (.step 5 (.close 3))) (.step 18 (.step 12 (.step 17 (.close 5))))) (.step 12 (.step 17 (.step 3 (.close 31))))) (.step 3 (.close 17))) (.step 5 (.close 17)))) (.step 3 (.close 17))) (.step 3 (.step 5 (.step 17 (.close 31))))) (.step 5 (.close 17))) (.step 3 (.step 5 (.step 17 (.close 31))))) (.step 12 (.step 23 (.step 31 (.step 32 (.step 17 (.close 5))))))) (.step 17 (.close 31))) (.step 12 (.step 23 (.step 31 (.step 67 (.step 69 (.step 38 (.step 74 (.split 36 0 (.step 17 (.close 5)) (.step 5 (.close 17))))))))))) (.step 3 (.step 5 (.step 12 (.step 17 (.close 18)))))) (.step 12 (.step 17 (.step 23 (.step 32 (.step 74 (.step 38 (.close 17)))))))))))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832589376755928668997108682832894707710076462020591537455646557167570371154622406493550142303538630521549672475708231706497879131967835682908788838197502738898984022354952192⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.step 18 (.step 31 (.split 2 2 (.split 14 2 (.split 35 2 (.step 68 (.split 38 2 (.reuse 0) (.run (.step 3 (.step 5 (.step 10 (.step 18 (.step 41 (.split 63 2 (.split 71 2 (.split 64 1 (.split 65 1 (.step 31 (.step 5 (.step 59 (.split 51 1 (.step 69 (.step 31 (.step 5 (.step 12 (.step 41 (.close 5)))))) (.step 3 (.close 18)))))) (.step 3 (.step 10 (.step 41 (.step 31 (.step 24 (.step 18 (.close 63)))))))) (.step 31 (.step 41 (.close 67)))) (.step 31 (.close 74))) (.step 5 (.step 31 (.step 63 (.close 66))))))))))))) (.run (.step 3 (.step 29 (.step 31 (.step 32 (.step 38 (.step 66 (.step 68 (.step 74 (.split 74 2 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 51 1 (.step 38 (.step 32 (.step 3 (.step 12 (.step 3 (.close 18)))))) (.step 3 (.close 22))) (.step 18 (.close 38))) (.step 18 (.close 38))) (.step 18 (.close 38))) (.step 12 (.step 18 (.step 38 (.step 3 (.close 17)))))) (.step 5 (.step 17 (.step 18 (.step 23 (.step 32 (.step 66 (.step 69 (.step 38 (.close 74)))))))))))))))))))) (.reuse 1)) (.run (.step 3 (.step 5 (.split 35 1 (.split 65 1 (.step 75 (.split 63 2 (.split 64 2 (.step 5 (.step 23 (.step 66 (.step 67 (.step 5 (.close 74)))))) (.step 23 (.close 67))) (.step 23 (.close 66)))) (.step 5 (.close 23))) (.step 5 (.step 32 (.step 38 (.close 66)))))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case141
