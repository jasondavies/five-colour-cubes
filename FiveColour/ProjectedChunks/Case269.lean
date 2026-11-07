module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case269
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142524123424363018499129345⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200381904584084138982742526263297⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 13 0 (.split 7 0 (.split 25 0 (.step 31 (.close 51)) (.step 47 (.step 5 (.close 51)))) (.step 47 (.step 5 (.close 51)))) (.step 49 (.split 7 0 (.step 49 (.step 5 (.close 28))) (.step 47 (.step 5 (.close 51)))))) (.split 7 0 (.split 33 0 (.step 50 (.step 31 (.close 16))) (.step 32 (.step 43 (.step 51 (.close 5))))) (.step 47 (.split 33 0 (.step 24 (.close 31)) (.step 5 (.step 24 (.close 12))))))) (.step 68 (.step 69 (.step 31 (.close 16))))) (.split 23 0 (.step 51 (.step 68 (.step 31 (.close 6)))) (.step 69 (.split 13 0 (.step 51 (.step 24 (.close 31))) (.step 12 (.step 16 (.step 22 (.step 5 (.close 6))))))))) (.split 19 0 (.split 23 0 (.step 68 (.split 7 0 (.split 25 0 (.split 33 0 (.split 56 0 (.step 31 (.close 35)) (.step 31 (.close 16))) (.step 51 (.step 5 (.close 32)))) (.step 47 (.step 31 (.close 24)))) (.step 47 (.step 68 (.close 31))))) (.step 69 (.split 13 0 (.step 69 (.step 24 (.close 31))) (.step 12 (.step 16 (.step 21 (.step 24 (.close 6)))))))) (.split 7 0 (.split 29 0 (.step 51 (.step 24 (.split 25 0 (.step 21 (.close 31)) (.step 24 (.step 28 (.close 31)))))) (.step 32 (.step 22 (.close 41)))) (.step 6 (.step 22 (.step 21 (.step 10 (.step 22 (.close 24))))))))))
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
def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142524123424363017425387521⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 9 0 (.reuse 0) (.run (.split 18 0 (.split 7 0 (.split 19 0 (.split 33 0 (.split 25 0 (.split 56 0 (.split 13 0 (.step 12 (.step 5 (.close 21))) (.step 12 (.close 16))) (.step 31 (.step 12 (.close 24)))) (.step 47 (.step 31 (.step 12 (.close 24))))) (.step 51 (.step 12 (.step 5 (.close 24))))) (.split 33 0 (.split 44 0 (.step 12 (.step 24 (.close 22))) (.step 51 (.step 12 (.step 24 (.close 31))))) (.step 12 (.close 51)))) (.split 25 0 (.split 13 0 (.split 19 0 (.step 47 (.step 24 (.split 33 0 (.step 49 (.step 16 (.close 31))) (.step 12 (.close 68))))) (.step 12 (.step 16 (.step 22 (.step 5 (.close 10)))))) (.step 12 (.close 16))) (.step 6 (.close 29)))) (.split 7 0 (.split 19 0 (.split 33 0 (.split 25 0 (.step 12 (.step 24 (.step 16 (.step 21 (.close 5))))) (.step 24 (.step 31 (.step 12 (.close 21))))) (.step 12 (.step 24 (.step 23 (.close 14))))) (.step 12 (.step 22 (.step 24 (.step 16 (.step 21 (.close 5))))))) (.step 12 (.step 16 (.step 21 (.step 47 (.step 21 (.step 22 (.close 5)))))))))))
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
def root : Box := ⟨1073741825, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470110054323345631251250586596844581225918917243881185079197697⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 33 0 (.split 23 0 (.split 41 0 (.split 25 0 (.split 56 0 (.split 73 0 (.split 13 0 (.step 31 (.split 46 0 (.step 5 (.close 12)) (.step 12 (.close 5)))) (.step 12 (.step 10 (.close 31)))) (.step 69 (.split 13 0 (.step 28 (.close 31)) (.step 10 (.step 12 (.close 31)))))) (.step 28 (.step 31 (.step 16 (.close 12))))) (.step 28 (.step 6 (.close 12)))) (.split 44 0 (.split 46 0 (.step 6 (.step 69 (.step 5 (.close 16)))) (.step 12 (.step 5 (.step 6 (.close 24))))) (.step 69 (.step 8 (.step 5 (.close 10)))))) (.step 69 (.split 13 0 (.step 69 (.step 28 (.step 24 (.close 31)))) (.step 6 (.step 10 (.step 12 (.step 16 (.step 24 (.close 21))))))))) (.split 9 0 (.split 13 0 (.step 51 (.step 6 (.split 46 0 (.split 38 0 (.step 23 (.close 8)) (.step 24 (.close 31))) (.step 12 (.step 8 (.step 24 (.close 5))))))) (.step 6 (.step 12 (.step 51 (.step 5 (.step 24 (.close 11))))))) (.step 6 (.step 12 (.step 51 (.split 38 0 (.split 47 0 (.step 5 (.close 26)) (.step 24 (.close 8))) (.step 24 (.close 31)))))))))
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
def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142524123424363018499129345⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 3 0 (.reuse 0) (.split 7 0 (.split 19 0 (.reuse 1) (.run (.split 9 0 (.split 13 0 (.split 33 0 (.split 44 0 (.split 38 0 (.step 6 (.step 51 (.step 24 (.step 48 (.close 26))))) (.step 24 (.step 28 (.step 21 (.close 22))))) (.step 10 (.step 47 (.step 51 (.step 10 (.close 29)))))) (.step 6 (.close 51))) (.step 6 (.step 12 (.step 10 (.step 22 (.step 24 (.step 16 (.step 22 (.close 21))))))))) (.step 6 (.step 12 (.split 38 0 (.step 51 (.split 47 0 (.step 22 (.close 68)) (.step 10 (.step 21 (.step 5 (.close 22)))))) (.step 32 (.step 10 (.step 21 (.close 22)))))))))) (.run (.split 13 0 (.split 40 0 (.split 19 0 (.split 33 0 (.step 47 (.split 60 0 (.step 6 (.close 12)) (.step 6 (.close 31)))) (.step 6 (.close 5))) (.step 6 (.close 31))) (.step 6 (.close 5))) (.step 6 (.close 31))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case269
