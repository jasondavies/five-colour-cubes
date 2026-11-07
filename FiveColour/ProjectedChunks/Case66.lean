module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case66
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5648033303795598179437473169482855732974184157209738101222077141193873535545222527970250829507298801117885930449628551390535203499047764690718083442882640378311863315321813270070523050023667626967416741130936500770308098⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨25870188955332800404854, 5653543574944814750672969936779461275257770268855883317050768144265371539051058604403869402159033013261169810879268681636863343259231352980090841884530421197632408968721498099663395240153487909455453404202846298366279681, 0⟩]
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
def root : Box := ⟨2, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142524123424363017425387522⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 7 0 (.split 23 0 (.split 33 0 (.split 25 0 (.split 9 0 (.split 18 0 (.split 29 0 (.split 31 0 (.step 4 (.close 49)) (.step 4 (.close 16))) (.step 18 (.close 16))) (.step 55 (.close 18))) (.split 38 0 (.split 13 0 (.step 12 (.step 4 (.close 21))) (.step 12 (.close 16))) (.step 18 (.step 12 (.close 21))))) (.step 47 (.split 9 0 (.split 18 0 (.split 31 0 (.split 40 0 (.step 18 (.close 49)) (.step 4 (.close 16))) (.step 4 (.close 16))) (.step 18 (.close 24))) (.step 18 (.step 12 (.close 21)))))) (.step 51 (.step 55 (.step 4 (.close 12))))) (.step 69 (.split 25 0 (.step 55 (.step 18 (.close 12))) (.step 18 (.step 28 (.step 24 (.close 12))))))) (.split 13 0 (.split 18 0 (.step 47 (.step 55 (.step 18 (.close 38)))) (.split 31 0 (.step 47 (.step 55 (.step 18 (.close 12)))) (.step 4 (.step 6 (.close 24))))) (.split 31 0 (.split 33 0 (.step 47 (.step 55 (.step 16 (.step 18 (.close 37))))) (.step 5 (.step 6 (.close 24)))) (.step 5 (.close 16))))) (.split 7 0 (.split 13 0 (.split 33 0 (.step 55 (.step 51 (.step 18 (.close 21)))) (.step 51 (.close 16))) (.split 31 0 (.split 33 0 (.step 68 (.step 51 (.step 12 (.step 18 (.close 21))))) (.step 5 (.close 22))) (.step 5 (.close 16)))) (.split 31 0 (.split 33 0 (.split 40 0 (.step 47 (.step 51 (.step 68 (.split 38 0 (.step 18 (.close 12)) (.step 18 (.close 21)))))) (.step 5 (.step 6 (.close 24)))) (.step 5 (.close 22))) (.step 5 (.step 16 (.step 10 (.step 22 (.close 21)))))))))
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
def root : Box := ⟨2, 5648033303795598179437473169482855732974184157209738101222077141193873535545222527970250829507298801117885930449628551390535203499047764690718083442882640378311863315321813270070523050023667626967416741130936500770308098⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 60 1 (.split 3 0 (.reuse 0) (.run (.split 7 0 (.split 19 0 (.split 9 0 (.split 23 0 (.split 13 0 (.split 18 0 (.split 25 0 (.split 38 0 (.split 40 0 (.step 18 (.close 30)) (.step 8 (.step 4 (.close 16)))) (.step 18 (.close 43))) (.step 18 (.step 47 (.step 6 (.close 12))))) (.step 55 (.step 18 (.close 6)))) (.step 55 (.step 18 (.close 21)))) (.step 69 (.split 25 0 (.step 55 (.step 10 (.close 18))) (.step 6 (.close 9))))) (.split 25 0 (.step 12 (.split 38 0 (.split 47 0 (.split 18 0 (.split 40 0 (.step 4 (.step 8 (.close 18))) (.step 18 (.close 24))) (.step 55 (.close 18))) (.step 18 (.step 8 (.close 24)))) (.step 18 (.step 28 (.step 24 (.close 14)))))) (.step 6 (.close 18)))) (.split 9 0 (.split 13 0 (.split 33 0 (.step 55 (.step 51 (.step 18 (.close 21)))) (.step 6 (.close 51))) (.step 6 (.step 12 (.step 10 (.step 22 (.step 24 (.step 16 (.step 18 (.close 22))))))))) (.step 6 (.step 12 (.split 38 0 (.step 51 (.step 55 (.close 18))) (.step 18 (.step 16 (.step 21 (.close 22))))))))) (.split 13 0 (.split 18 0 (.split 25 0 (.split 38 0 (.step 55 (.step 10 (.close 6))) (.step 18 (.close 6))) (.step 6 (.close 18))) (.step 6 (.close 18))) (.step 6 (.close 18)))))) (.run (.step 31 (.step 63 (.split 7 0 (.split 13 0 (.step 18 (.close 4)) (.step 5 (.step 16 (.close 18)))) (.step 5 (.step 10 (.step 18 (.close 16))))))))) (.run (.step 5 (.step 24 (.step 43 (.split 7 0 (.split 13 0 (.step 24 (.step 4 (.close 28))) (.step 5 (.step 12 (.close 24)))) (.step 5 (.step 6 (.close 24)))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case66
