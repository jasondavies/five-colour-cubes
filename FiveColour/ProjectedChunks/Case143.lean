module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case143
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 23134322349737717735021796285272283483885134813317202352766244487352153458927202491314932076713772185564659526219838426654130820177421794578697792322685594472097454233382586607716314808008272834562903889688012443037042999296⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨18740915245514456087539, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475066830037980738387460577625234839625950792211697196357563187971868412046230991680761629786926547894765880320, 0⟩]
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
def root : Box := ⟨4294967296, 11567161174868858867508448700980813070724093481457900356577175617604274334026998231396500499035494541793868747682231163958534248350147339910902938467434779207305437562291777011139165441926341298037872398386314512982086778880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 56 1 (.split 59 1 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 39 1 (.step 31 (.step 27 (.step 5 (.step 31 (.close 3))))) (.step 32 (.step 31 (.close 42)))) (.step 3 (.close 44))) (.step 18 (.close 61))) (.step 18 (.close 42))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 42 (.split 58 1 (.step 5 (.step 3 (.close 5))) (.step 27 (.step 31 (.close 61))))) (.step 3 (.close 31))) (.step 3 (.close 5))) (.step 3 (.close 18))) (.step 3 (.close 18)))) (.step 44 (.split 2 0 (.split 16 0 (.split 17 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 62 (.step 42 (.close 62))) (.step 3 (.step 21 (.step 5 (.close 23))))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.close 62))) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 5 (.step 21 (.step 5 (.close 23)))))))) (.step 61 (.step 31 (.step 5 (.step 3 (.close 61)))))) (.step 32 (.split 56 1 (.split 16 0 (.split 74 1 (.split 17 0 (.step 62 (.split 22 0 (.split 34 0 (.split 36 0 (.step 32 (.step 3 (.close 5))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.close 17)))) (.step 3 (.close 62))) (.step 32 (.step 44 (.step 3 (.close 23))))) (.step 3 (.step 18 (.close 44)))) (.step 3 (.step 21 (.step 22 (.close 61))))))))
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
def root : Box := ⟨4294967296, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080432005045007367178293679910858269553654965607600541051769157003050701565060953921291989860533564717087271791617538977241953730560⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 40 1 (.split 42 1 (.split 49 1 (.reuse 0) (.run (.split 56 1 (.split 2 0 (.split 16 0 (.split 17 0 (.step 52 (.split 74 1 (.split 22 0 (.split 36 0 (.split 38 0 (.step 52 (.step 32 (.step 34 (.step 3 (.close 5))))) (.step 3 (.step 21 (.step 5 (.close 23))))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.close 52))) (.step 27 (.step 34 (.step 31 (.step 23 (.step 32 (.step 3 (.close 18))))))))) (.step 3 (.step 34 (.step 42 (.step 18 (.close 52)))))) (.step 3 (.step 42 (.step 18 (.close 44))))) (.step 3 (.step 23 (.step 34 (.step 42 (.step 5 (.close 52))))))) (.step 3 (.step 31 (.close 61)))))) (.run (.step 31 (.close 21)))) (.run (.step 43 (.split 49 1 (.split 50 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 5 (.step 31 (.step 5 (.step 3 (.close 23))))) (.step 3 (.step 5 (.close 31)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 31)))) (.step 3 (.step 5 (.step 21 (.close 31))))) (.step 3 (.step 5 (.step 31 (.close 21)))))))) (.run (.step 21 (.step 31 (.split 49 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 58 (.split 34 0 (.step 42 (.step 31 (.close 5))) (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.close 42))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 31 (.close 5)))) (.step 3 (.step 21 (.step 31 (.close 5))))))))) (.run (.step 31 (.close 21)))) (.run (.step 31 (.close 21)))) (.run (.step 18 (.step 3 (.close 32)))))
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
def root : Box := ⟨4294967296, 11567161174868858867513347584291470413161041331859301996192754379928368911373805982548404357972128944084213254005644541298280388775437742671198262714442754743044962328235788748019965493164388610149603432116748705226146447360⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.split 55 1 (.split 14 1 (.step 3 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 18 (.step 3 (.close 32))))) (.run (.step 18 (.step 3 (.close 32)))))) (.run (.step 18 (.step 31 (.step 34 (.split 38 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 34 0 (.split 39 1 (.split 36 0 (.split 50 1 (.split 38 0 (.step 61 (.step 18 (.step 27 (.step 23 (.close 44))))) (.step 18 (.step 5 (.close 23)))) (.step 27 (.step 32 (.step 34 (.step 18 (.step 23 (.close 44))))))) (.step 18 (.step 23 (.close 5)))) (.step 32 (.step 34 (.step 18 (.close 42))))) (.step 18 (.close 34))) (.step 11 (.step 31 (.step 34 (.step 23 (.step 18 (.close 5))))))) (.step 11 (.step 17 (.close 31)))) (.step 3 (.close 17))) (.step 5 (.close 61))) (.step 3 (.close 17))) (.step 5 (.close 42)))))))) (.run (.step 18 (.step 31 (.step 58 (.split 14 1 (.split 39 1 (.step 3 (.step 58 (.step 48 (.step 3 (.step 32 (.step 3 (.close 52))))))) (.step 32 (.step 42 (.close 3)))) (.step 18 (.step 34 (.step 32 (.close 44)))))))))) (.run (.step 3 (.step 31 (.step 58 (.step 5 (.split 17 1 (.split 22 1 (.split 14 1 (.step 3 (.step 42 (.step 23 (.step 61 (.step 3 (.step 17 (.close 62))))))) (.step 23 (.close 17))) (.step 3 (.close 18))) (.step 3 (.close 18)))))))))
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
def root : Box := ⟨4294967296, 23134322349737717735016897401961626141448186962907886132766658060836509449305074161234047985717100581981029133138672063573109636175003461967488722384021783282682356990814523422049090110311054670084948902833425651372769935360⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 59 2 (.split 74 2 (.reuse 0) (.run (.step 18 (.step 27 (.step 44 (.split 14 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 51 1 (.step 11 (.split 55 1 (.split 56 1 (.split 67 1 (.split 2 0 (.split 36 0 (.split 38 0 (.split 39 1 (.split 49 1 (.step 77 (.close 31)) (.step 23 (.step 44 (.step 52 (.step 55 (.close 77)))))) (.step 42 (.close 3))) (.step 18 (.step 23 (.step 5 (.close 42))))) (.step 18 (.step 23 (.close 77)))) (.step 23 (.step 77 (.close 5)))) (.step 3 (.close 77))) (.step 5 (.close 61))) (.step 5 (.step 18 (.step 42 (.step 48 (.step 58 (.close 77)))))))) (.step 3 (.step 18 (.close 42)))) (.step 31 (.close 42))) (.step 5 (.close 42))) (.step 31 (.close 36))) (.step 5 (.step 17 (.close 31)))) (.step 17 (.step 3 (.step 5 (.close 17)))))))))) (.run (.step 3 (.step 58 (.split 14 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 17 1 (.step 62 (.split 40 1 (.split 55 1 (.split 56 1 (.split 39 1 (.split 58 1 (.split 2 0 (.split 16 0 (.split 17 0 (.step 62 (.close 3)) (.step 3 (.close 62))) (.step 3 (.close 62))) (.step 3 (.step 44 (.step 5 (.close 21))))) (.step 61 (.close 62))) (.step 42 (.close 62))) (.step 3 (.step 31 (.close 61)))) (.step 58 (.close 62))) (.step 3 (.step 5 (.close 62))))) (.step 3 (.step 18 (.close 62)))) (.step 3 (.step 42 (.close 58)))) (.step 22 (.step 31 (.close 21)))) (.step 31 (.close 34))) (.step 3 (.step 18 (.close 62)))) (.step 27 (.step 34 (.step 42 (.step 44 (.step 48 (.step 53 (.step 23 (.step 55 (.step 18 (.close 32)))))))))))))))
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
def root : Box := ⟨9820171823688425610039569090482797456649926138129194368449874104288401389214023664649810276977712471452660052382680213027651769637656179159989877735424, 23134322349737717735016897401961626141448186962915800713161722255569528241007593249083993710748561195346358312119341467353896559675334027165969542988355553617791808163009771204461443663999743430605591078842935262037374140416⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 32 (.step 58 (.step 53 (.step 61 (.split 74 2 (.split 2 1 (.split 14 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 17 1 (.step 62 (.split 22 1 (.split 40 1 (.split 42 1 (.split 55 1 (.split 56 1 (.step 52 (.split 58 1 (.split 74 1 (.split 2 0 (.split 17 0 (.split 22 0 (.step 53 (.close 5)) (.step 3 (.close 53))) (.step 3 (.close 53))) (.step 3 (.step 21 (.close 53)))) (.step 32 (.step 44 (.step 31 (.close 53))))) (.step 53 (.close 61)))) (.step 21 (.step 31 (.close 53)))) (.step 32 (.step 48 (.step 53 (.close 5))))) (.step 31 (.close 44))) (.step 3 (.step 21 (.step 31 (.step 5 (.close 52)))))) (.step 18 (.close 53)))) (.step 18 (.close 53))) (.step 21 (.step 22 (.close 31)))) (.step 31 (.close 34))) (.step 18 (.close 53))) (.step 18 (.step 27 (.step 34 (.step 53 (.step 55 (.step 23 (.step 53 (.close 17))))))))) (.step 3 (.step 23 (.step 52 (.step 5 (.step 53 (.close 5))))))) (.step 17 (.step 18 (.step 23 (.step 44 (.step 53 (.step 55 (.close 61))))))))))))))
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
def root : Box := ⟨9590011546570728134804266689924606891259693494266791375439330179969141981654319985009580348611047335402988332404961145534816181286773612465218387968, 23134322349737717735016897401961626141448186962915800713161722255569528241013986590115040862838430706472974716713514596350074420592293580619282304309458433607798195062083802761396769218936384194295468533034117670344656420864⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 58 (.step 52 (.step 61 (.split 74 2 (.split 2 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 17 1 (.step 62 (.split 22 1 (.split 40 1 (.split 42 1 (.split 55 1 (.split 56 1 (.step 52 (.split 39 1 (.split 58 1 (.split 74 1 (.split 2 0 (.split 16 0 (.split 17 0 (.step 52 (.close 3)) (.step 3 (.close 52))) (.step 3 (.close 52))) (.step 3 (.step 34 (.step 5 (.close 21))))) (.step 34 (.step 44 (.step 31 (.step 52 (.close 3)))))) (.step 52 (.close 61))) (.step 42 (.close 52)))) (.step 31 (.step 52 (.close 5)))) (.step 48 (.step 52 (.close 5)))) (.step 31 (.close 44))) (.step 31 (.step 42 (.step 5 (.close 52))))) (.step 18 (.close 52)))) (.step 18 (.close 52))) (.step 31 (.step 42 (.close 52)))) (.step 22 (.step 31 (.close 21)))) (.step 31 (.close 34))) (.step 18 (.close 52))) (.step 3 (.step 5 (.step 23 (.step 52 (.close 5)))))) (.step 17 (.step 18 (.step 23 (.step 44 (.step 52 (.step 42 (.step 55 (.close 61))))))))))))))
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
def root : Box := ⟨4294967296, 23134322349737717735016897401961626141448186962915800713161722255569528241013986590115040862838433414163392424784745207612649651459017253587244419415213510092769008939947102214961224536148803480366729843091664020323163963392⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 3 := (.split 39 2 (.step 31 (.split 40 2 (.split 49 2 (.split 50 2 (.split 56 2 (.split 58 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 34 (.step 36 (.step 44 (.step 42 (.step 61 (.close 3)))))))))) (.run (.step 3 (.step 18 (.step 31 (.step 43 (.step 58 (.split 49 1 (.split 50 1 (.split 59 1 (.split 74 1 (.split 14 0 (.split 16 0 (.split 38 1 (.step 5 (.step 58 (.split 34 0 (.step 43 (.step 3 (.close 31))) (.step 3 (.close 58))))) (.step 28 (.step 43 (.step 59 (.close 5))))) (.step 18 (.step 5 (.close 31)))) (.step 18 (.step 5 (.close 31)))) (.step 5 (.close 31))) (.step 3 (.step 5 (.close 59)))) (.step 21 (.close 58))) (.step 31 (.close 58)))))))))) (.reuse 1)) (.reuse 2)) (.run (.step 43 (.step 3 (.step 18 (.step 61 (.split 49 2 (.split 50 2 (.split 59 2 (.step 43 (.step 42 (.step 61 (.split 74 1 (.step 3 (.step 31 (.step 21 (.step 31 (.close 17))))) (.step 17 (.step 18 (.close 23))))))) (.step 5 (.step 31 (.step 42 (.step 52 (.step 53 (.step 43 (.close 62)))))))) (.step 5 (.step 21 (.step 31 (.close 53))))) (.step 5 (.step 31 (.step 42 (.step 52 (.close 43))))))))))))) (.run (.step 5 (.step 12 (.step 34 (.step 36 (.step 43 (.step 44 (.step 42 (.step 3 (.close 5)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4181389724724491839037947176121572077338624, 23134322349737717735016897401961626141448186962915800713161722255569528241013986590115040862838433414163392429709995982161959552993897266105196145050180918900949842433483777745676448760893279723477904395670903202196850999296⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 5 (.step 17 (.step 27 (.step 31 (.step 34 (.step 42 (.step 43 (.step 58 (.step 61 (.split 50 2 (.split 59 2 (.split 40 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 42 1 (.split 50 1 (.split 51 1 (.step 11 (.split 55 1 (.split 56 1 (.split 67 1 (.split 59 1 (.split 2 0 (.split 36 0 (.split 38 0 (.step 17 (.close 31)) (.step 18 (.step 17 (.close 5)))) (.step 17 (.step 3 (.close 17)))) (.step 17 (.step 5 (.close 3)))) (.step 23 (.step 17 (.step 3 (.close 18))))) (.step 3 (.close 17))) (.step 5 (.step 17 (.close 21)))) (.step 5 (.step 18 (.step 48 (.step 17 (.close 58))))))) (.step 3 (.close 17))) (.step 3 (.step 11 (.step 23 (.step 32 (.step 48 (.step 17 (.step 44 (.step 17 (.close 18)))))))))) (.step 3 (.step 5 (.close 17)))) (.step 17 (.step 31 (.step 17 (.close 42))))) (.step 5 (.step 17 (.close 23)))) (.step 3 (.step 5 (.step 17 (.close 23))))) (.step 3 (.step 5 (.close 17)))) (.step 5 (.step 23 (.step 17 (.close 31))))) (.step 3 (.step 11 (.step 23 (.step 42 (.step 44 (.step 53 (.step 55 (.step 17 (.close 61)))))))))) (.step 11 (.step 23 (.step 32 (.step 53 (.step 55 (.step 61 (.step 17 (.close 3)))))))))))))))))))
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
def root : Box := ⟨4294967296, 23134322349737717735021796285272283483885134813317202352766244487352153458927202491314932076713772185564659526219838426654130820177421794578697792322685594472097454233382586607716314808008272834562903889688012443037042999296⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.step 3 (.step 18 (.split 14 2 (.split 38 2 (.reuse 0) (.run (.step 21 (.step 31 (.step 41 (.step 43 (.step 3 (.step 18 (.step 58 (.split 49 1 (.split 59 1 (.split 74 1 (.split 56 1 (.step 5 (.step 58 (.split 34 0 (.step 43 (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 5 (.close 31)))))) (.step 28 (.step 43 (.split 14 0 (.split 16 0 (.step 59 (.close 5)) (.step 18 (.close 41))) (.step 31 (.close 5)))))) (.step 5 (.close 31))) (.step 3 (.step 5 (.close 41)))) (.step 3 (.step 5 (.step 21 (.close 41)))))))))))))) (.reuse 1))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case143
