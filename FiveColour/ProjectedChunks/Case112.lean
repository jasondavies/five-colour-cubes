module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case112
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079166450589158585345283312557861340749338639804069091894963296504675806186831872⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428103608535382820839502517187328220872637725612953037113167359257830256167358084505511881620637780560536276625963897335110125002859585249260433337684753595672559616⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 45 1 (.split 55 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.close 48)) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 18 (.close 3)))) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.close 7))) (.step 58 (.close 3))) (.step 48 (.close 3))) (.step 3 (.close 7))) (.split 67 1 (.step 48 (.step 58 (.split 10 0 (.split 11 0 (.split 34 0 (.split 16 0 (.step 55 (.step 7 (.close 58))) (.step 18 (.close 48))) (.step 31 (.close 48))) (.step 3 (.close 48))) (.step 3 (.step 18 (.close 12)))))) (.step 3 (.close 70)))) (.step 3 (.step 48 (.split 55 1 (.split 10 0 (.split 45 1 (.split 11 0 (.split 17 0 (.split 43 0 (.step 60 (.close 3)) (.step 31 (.close 60))) (.step 18 (.close 60))) (.step 60 (.close 3))) (.step 48 (.close 60))) (.step 31 (.step 3 (.step 18 (.close 48))))) (.step 58 (.close 60)))))) (.split 57 1 (.step 3 (.step 58 (.split 45 1 (.split 55 1 (.split 59 1 (.split 11 0 (.split 16 0 (.split 10 0 (.split 17 0 (.step 28 (.split 22 0 (.step 31 (.step 3 (.close 48))) (.step 3 (.close 31)))) (.step 18 (.close 31))) (.step 3 (.close 31))) (.step 18 (.close 31))) (.step 3 (.step 43 (.close 59)))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 5 (.step 31 (.close 48))))) (.step 31 (.step 48 (.close 4)))))) (.step 28 (.step 51 (.step 60 (.step 3 (.close 16))))))))
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959694905460647464469174318179182005046179800195600271401316668653718141385594890081780162240723231876842391305451111198466180334739406281823075470164361216⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.reuse 0) (.run (.step 51 (.split 57 1 (.step 3 (.split 45 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 17 0 (.step 3 (.step 51 (.step 18 (.split 34 0 (.step 48 (.close 31)) (.step 3 (.close 31)))))) (.step 18 (.step 3 (.close 18)))) (.step 8 (.step 18 (.close 56)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 24 (.close 51)))) (.step 18 (.step 51 (.close 58)))) (.step 4 (.step 18 (.close 48))))) (.step 44 (.step 51 (.step 60 (.step 3 (.close 12))))))))) (.run (.split 53 1 (.split 56 1 (.split 57 1 (.step 55 (.close 3)) (.step 48 (.step 3 (.close 60)))) (.step 3 (.step 31 (.step 48 (.close 60))))) (.step 3 (.step 18 (.step 48 (.close 60))))))) (.run (.step 51 (.step 3 (.close 54))))) (.run (.step 55 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 10 0 (.split 11 0 (.split 34 0 (.split 16 0 (.step 55 (.step 7 (.close 53))) (.step 18 (.close 48))) (.step 31 (.close 48))) (.step 3 (.close 48))) (.step 3 (.step 18 (.close 12)))))) (.step 3 (.close 70))) (.split 11 0 (.split 16 0 (.split 34 0 (.split 38 0 (.step 62 (.close 3)) (.step 3 (.close 58))) (.step 9 (.step 26 (.step 31 (.close 48))))) (.step 18 (.close 53))) (.step 3 (.step 18 (.close 48))))) (.step 3 (.step 48 (.step 50 (.step 48 (.close 3)))))) (.step 3 (.step 21 (.step 31 (.close 58))))) (.step 3 (.step 18 (.step 48 (.close 12))))) (.step 3 (.step 53 (.close 7)))))))
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959694911853988495516326408048693131662584394368729267579177585613271594698356211184660152247110130950873948240776666135106944024616860473005483777446641664⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.reuse 0) (.run (.step 55 (.split 50 1 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 10 0 (.split 11 0 (.split 34 0 (.split 16 0 (.step 55 (.step 7 (.close 52))) (.step 18 (.close 48))) (.step 31 (.close 48))) (.step 3 (.close 48))) (.step 18 (.close 12))))) (.step 3 (.close 70))) (.split 45 1 (.split 11 0 (.split 16 0 (.split 34 0 (.split 38 0 (.step 62 (.close 3)) (.step 3 (.close 58))) (.step 9 (.step 26 (.step 31 (.close 48))))) (.step 18 (.close 52))) (.step 3 (.step 18 (.close 12)))) (.step 48 (.close 3)))) (.step 3 (.step 48 (.step 49 (.step 48 (.close 3)))))) (.step 3 (.step 31 (.step 49 (.close 52))))) (.step 3 (.step 18 (.step 34 (.close 48))))) (.step 3 (.step 52 (.close 7)))) (.step 52 (.step 55 (.split 53 1 (.split 55 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 36 0 (.split 38 0 (.step 52 (.split 30 0 (.step 52 (.close 3)) (.step 18 (.close 52)))) (.step 3 (.step 21 (.close 48)))) (.step 52 (.step 31 (.close 52)))) (.step 21 (.close 53))) (.step 3 (.step 34 (.close 52)))) (.step 31 (.step 48 (.close 52)))) (.step 48 (.close 52))) (.step 3 (.close 48)))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456544832487424, 14696649931972027310843563361000416961428110644959694911853994598635726573400631696224734468365203328234955004885560166315260691176634582826792716311888581570683966745848367520459732776348438928990142464⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 47 1 (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 55 1 (.split 10 0 (.step 60 (.split 30 0 (.split 45 1 (.split 11 0 (.split 16 0 (.step 49 (.close 55)) (.step 18 (.close 49))) (.step 49 (.close 3))) (.step 48 (.close 49))) (.step 31 (.step 3 (.step 18 (.close 48)))))) (.step 3 (.close 49))) (.step 48 (.step 49 (.close 3)))))) (.step 48 (.step 51 (.step 49 (.step 3 (.close 49)))))) (.step 28 (.step 48 (.step 51 (.step 49 (.close 48)))))) (.step 8 (.step 48 (.step 51 (.step 49 (.step 3 (.close 48))))))) (.step 3 (.step 48 (.step 49 (.close 3))))) (.step 3 (.step 48 (.step 50 (.step 48 (.close 3)))))) (.step 55 (.step 48 (.close 49))))) (.step 48 (.step 49 (.step 3 (.step 50 (.step 51 (.step 49 (.step 12 (.step 32 (.step 3 (.close 48))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837821305112336769945558783645540743836221324119003534316592065849232771683419994780953651720374462255963454574807744512⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 42 1 (.split 43 1 (.step 48 (.step 58 (.split 46 1 (.split 47 1 (.reuse 0) (.run (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 55 1 (.split 10 0 (.step 60 (.split 45 1 (.split 17 0 (.split 22 0 (.split 43 0 (.step 50 (.close 3)) (.step 31 (.close 50))) (.step 18 (.close 50))) (.step 18 (.close 50))) (.step 48 (.close 50)))) (.step 31 (.step 3 (.step 18 (.close 48))))) (.step 32 (.step 48 (.step 50 (.close 3))))))) (.step 48 (.step 51 (.step 50 (.step 26 (.step 44 (.close 48))))))) (.step 28 (.step 48 (.step 51 (.step 50 (.step 3 (.close 48))))))) (.step 8 (.step 48 (.step 51 (.step 50 (.close 48)))))) (.step 3 (.step 48 (.step 50 (.close 3))))) (.step 3 (.step 48 (.step 50 (.step 48 (.close 3)))))) (.step 55 (.step 48 (.close 49))))))) (.reuse 1)))) (.run (.step 10 (.step 30 (.step 47 (.split 45 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 58 (.step 3 (.step 7 (.close 46)))) (.step 3 (.close 46))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 3 (.step 27 (.step 46 (.close 52))))) (.step 3 (.close 47)))))))) (.run (.step 58 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 60 (.split 53 1 (.step 31 (.close 7)) (.step 3 (.close 31)))) (.step 31 (.close 53))) (.step 31 (.close 52)))) (.step 31 (.close 50))) (.step 31 (.close 49))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808404421007984981332222981525633141163707595242199127322884341705849982509295390583720867188092809370402816⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 3 (.step 58 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 52 1 (.split 53 1 (.step 21 (.split 56 1 (.split 57 1 (.step 3 (.step 58 (.split 45 1 (.split 55 1 (.split 59 1 (.split 11 0 (.split 16 0 (.split 10 0 (.split 17 0 (.step 28 (.split 22 0 (.step 31 (.step 3 (.close 48))) (.step 3 (.close 31)))) (.step 18 (.close 31))) (.step 3 (.close 31))) (.step 18 (.close 31))) (.step 3 (.step 43 (.step 31 (.close 18))))) (.step 3 (.step 21 (.step 41 (.close 48))))) (.step 3 (.step 5 (.step 31 (.close 48))))) (.step 21 (.step 31 (.close 48)))))) (.step 28 (.step 51 (.step 60 (.step 3 (.close 31)))))) (.step 28 (.step 58 (.split 59 1 (.step 59 (.close 3)) (.step 3 (.step 21 (.close 41)))))))) (.step 5 (.step 51 (.step 24 (.step 60 (.split 16 0 (.step 43 (.step 31 (.close 56))) (.step 18 (.close 41)))))))) (.step 3 (.step 21 (.step 48 (.close 41))))) (.step 3 (.step 21 (.step 49 (.step 41 (.close 58)))))) (.step 21 (.step 32 (.step 41 (.close 50))))) (.step 21 (.step 48 (.step 28 (.step 49 (.step 41 (.step 51 (.step 60 (.step 49 (.step 3 (.close 31))))))))))) (.step 31 (.step 3 (.close 41)))))))) (.run (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 57 1 (.step 31 (.close 7)) (.step 31 (.close 3))) (.step 3 (.step 31 (.close 56)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 50))) (.step 31 (.close 49))) (.step 31 (.step 7 (.close 39)))) (.step 3 (.step 31 (.close 39))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079166450589158585345283312557858417746063977995634000794829993665568252750725120⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 57 1 (.step 31 (.close 7)) (.step 31 (.close 3))) (.step 3 (.step 31 (.close 14)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 50))) (.step 31 (.close 49))) (.step 31 (.step 7 (.close 37)))) (.step 3 (.step 31 (.step 37 (.close 3))))) (.step 7 (.step 31 (.close 37)))))) (.run (.split 38 1 (.split 46 1 (.step 3 (.split 47 1 (.split 49 1 (.step 18 (.split 53 1 (.step 3 (.step 7 (.close 31))) (.step 3 (.close 18)))) (.step 18 (.close 52))) (.step 18 (.close 31)))) (.step 31 (.close 49))) (.step 3 (.close 31))))) (.run (.step 48 (.split 38 1 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 60 (.split 56 1 (.step 18 (.close 7)) (.step 3 (.close 18)))) (.step 18 (.close 53))) (.step 18 (.close 52)))) (.step 18 (.close 50))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 49 (.step 41 (.close 50))))))))) (.run (.split 22 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 57 1 (.step 18 (.close 7)) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 59)))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 49 (.step 41 (.close 50)))))) (.step 18 (.step 7 (.close 20))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2596148429267413814265251385835520, 9797766621314684873895712959598777356905878862334476998638093398744512703609907368447437461194017343583977568702823270205294489622873756287070231806286675463208033600821347037948590120669467782565330944⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 46 1 (.split 47 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.split 59 1 (.split 36 1 (.split 42 1 (.step 34 (.split 55 1 (.split 16 0 (.split 17 0 (.step 3 (.split 22 0 (.split 34 0 (.split 36 0 (.step 48 (.close 14)) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.step 14 (.close 18))))) (.step 18 (.step 3 (.close 14)))) (.step 18 (.step 14 (.close 3)))) (.step 12 (.step 18 (.close 58))))) (.step 4 (.close 31))) (.step 4 (.close 31))) (.step 18 (.step 34 (.close 48))))) (.step 12 (.step 8 (.step 51 (.step 60 (.step 3 (.close 14))))))) (.step 5 (.step 31 (.step 51 (.step 24 (.step 43 (.step 60 (.split 16 0 (.step 43 (.step 14 (.close 59))) (.step 3 (.close 14)))))))))) (.step 34 (.step 8 (.step 48 (.step 51 (.split 34 1 (.split 42 1 (.split 59 1 (.step 56 (.close 3)) (.step 3 (.close 14))) (.step 3 (.close 14))) (.step 4 (.close 14)))))))) (.step 3 (.step 34 (.step 48 (.close 14))))) (.step 3 (.step 34 (.step 48 (.close 14))))) (.step 12 (.step 48 (.step 8 (.step 51 (.step 60 (.step 50 (.step 3 (.close 14))))))))) (.step 12 (.step 14 (.step 18 (.step 34 (.close 49)))))) (.step 4 (.step 14 (.step 31 (.step 49 (.step 50 (.step 60 (.split 16 0 (.split 17 0 (.step 43 (.split 22 0 (.split 56 1 (.step 24 (.step 43 (.step 14 (.close 41)))) (.step 41 (.close 3))) (.step 3 (.step 14 (.close 41))))) (.step 3 (.step 5 (.step 14 (.close 41))))) (.step 3 (.step 5 (.step 14 (.close 41)))))))))))))
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079166450589158585345283312557861340749338639804069091894963296504675806186831872⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 11 1 (.split 16 1 (.reuse 0) (.run (.split 17 1 (.split 22 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 57 1 (.step 18 (.close 7)) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 41)))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 41 (.close 50))))) (.step 18 (.step 7 (.close 19)))) (.step 7 (.step 18 (.close 19)))))) (.step 3 (.step 31 (.step 48 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 1) (.run (.step 18 (.step 3 (.close 14))))) (.run (.step 18 (.step 8 (.step 14 (.close 3)))))) (.run (.step 18 (.step 14 (.step 3 (.close 19))))))))))) (.run (.split 11 1 (.split 38 1 (.split 46 1 (.step 3 (.split 47 1 (.split 49 1 (.step 18 (.split 53 1 (.step 3 (.step 7 (.close 31))) (.step 3 (.close 14)))) (.step 18 (.close 52))) (.step 18 (.close 31)))) (.step 31 (.close 49))) (.step 3 (.close 31))) (.step 3 (.close 14)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case112
