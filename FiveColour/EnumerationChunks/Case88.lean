module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case88
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142524123424363018499129345⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
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
def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111622066283937055552687185853354754273719928622902931357697⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 29 0 (.split 13 0 (.split 33 0 (.split 25 0 (.split 31 0 (.step 5 (.step 38 (.close 39))) (.step 5 (.step 12 (.step 5 (.close 16))))) (.step 47 (.split 31 0 (.step 5 (.step 38 (.close 39))) (.step 5 (.close 16))))) (.step 31 (.step 51 (.step 5 (.step 8 (.step 5 (.close 12))))))) (.step 49 (.split 33 0 (.step 49 (.step 68 (.step 28 (.close 38)))) (.step 5 (.step 14 (.step 5 (.step 22 (.close 8)))))))) (.split 25 0 (.split 33 0 (.split 56 0 (.split 41 0 (.step 31 (.close 16)) (.step 32 (.close 5))) (.step 31 (.step 50 (.step 31 (.close 16))))) (.step 32 (.step 51 (.step 5 (.step 12 (.step 5 (.close 16))))))) (.step 31 (.step 47 (.step 50 (.step 31 (.step 16 (.step 22 (.close 32))))))))) (.step 69 (.step 31 (.step 60 (.step 31 (.step 8 (.close 16))))))) (.split 23 0 (.step 51 (.step 68 (.split 25 0 (.split 41 0 (.step 31 (.close 16)) (.step 5 (.step 24 (.step 5 (.close 12))))) (.step 31 (.step 47 (.step 31 (.close 16))))))) (.step 69 (.split 41 0 (.step 51 (.step 24 (.step 31 (.close 16)))) (.step 24 (.step 22 (.close 5))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200381904582903547362025114959873⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 18 0 (.reuse 0) (.run (.split 19 0 (.split 23 0 (.split 29 0 (.step 68 (.split 33 0 (.split 25 0 (.split 56 0 (.step 31 (.step 5 (.step 12 (.step 5 (.close 16))))) (.step 31 (.step 41 (.step 5 (.step 12 (.step 5 (.close 16))))))) (.step 31 (.step 41 (.step 28 (.step 5 (.step 12 (.step 5 (.close 16)))))))) (.step 5 (.step 51 (.step 24 (.step 5 (.close 12))))))) (.split 33 0 (.step 50 (.close 5)) (.step 32 (.step 5 (.step 24 (.step 5 (.close 12))))))) (.step 69 (.split 41 0 (.step 69 (.step 24 (.step 41 (.split 13 0 (.step 24 (.close 31)) (.step 12 (.step 16 (.step 5 (.step 9 (.close 21))))))))) (.step 24 (.step 21 (.step 5 (.step 8 (.close 16)))))))) (.split 29 0 (.split 31 0 (.step 51 (.split 25 0 (.split 13 0 (.step 24 (.step 21 (.close 12))) (.step 12 (.step 16 (.step 21 (.close 5))))) (.step 24 (.step 41 (.step 22 (.step 9 (.close 12))))))) (.step 68 (.split 13 0 (.step 24 (.step 51 (.step 5 (.step 12 (.step 14 (.close 16)))))) (.step 12 (.step 16 (.step 5 (.close 17))))))) (.step 32 (.step 22 (.step 51 (.step 22 (.step 24 (.step 41 (.close 5)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1237940039285380274899124225, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111622066283937055552687185853355992213759214003177830481921⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 29 0 (.split 25 0 (.split 33 0 (.step 49 (.split 13 0 (.step 31 (.close 14)) (.step 14 (.step 31 (.step 5 (.close 12)))))) (.step 51 (.step 12 (.close 5)))) (.step 31 (.step 47 (.step 49 (.step 31 (.step 12 (.close 21))))))) (.split 33 0 (.split 25 0 (.step 32 (.step 12 (.step 5 (.step 16 (.step 5 (.close 21)))))) (.step 31 (.step 12 (.step 8 (.step 14 (.close 21)))))) (.step 12 (.step 32 (.step 5 (.step 8 (.close 14))))))) (.step 69 (.split 41 0 (.step 69 (.step 49 (.step 24 (.split 38 0 (.step 12 (.step 5 (.close 9))) (.step 24 (.close 31)))))) (.step 12 (.step 5 (.step 14 (.step 5 (.close 24)))))))) (.split 23 0 (.split 33 0 (.split 44 0 (.split 46 0 (.step 68 (.step 51 (.step 12 (.step 16 (.step 5 (.step 21 (.close 22))))))) (.step 12 (.close 31))) (.step 51 (.split 25 0 (.step 12 (.step 24 (.step 21 (.close 22)))) (.step 24 (.step 9 (.close 28)))))) (.step 12 (.close 51))) (.step 12 (.step 69 (.step 22 (.step 16 (.step 22 (.step 5 (.step 8 (.close 9)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741825, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111622066283937055552687185853354754273719928622904005099521⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 29 0 (.split 25 0 (.split 33 0 (.split 56 0 (.split 41 0 (.step 31 (.close 8)) (.step 69 (.step 5 (.close 8)))) (.step 28 (.step 31 (.close 16)))) (.step 51 (.split 13 0 (.step 8 (.step 5 (.close 12))) (.step 5 (.step 8 (.step 5 (.step 12 (.step 5 (.close 16))))))))) (.step 31 (.step 47 (.split 13 0 (.split 31 0 (.step 28 (.close 6)) (.step 6 (.close 5))) (.step 6 (.close 28)))))) (.split 33 0 (.split 25 0 (.step 32 (.split 13 0 (.split 31 0 (.step 31 (.close 8)) (.step 32 (.step 5 (.close 8)))) (.step 12 (.step 24 (.step 32 (.step 5 (.step 8 (.close 9)))))))) (.step 6 (.close 28))) (.step 6 (.step 32 (.step 51 (.step 5 (.close 8))))))) (.step 69 (.split 41 0 (.step 69 (.split 25 0 (.split 13 0 (.step 28 (.step 24 (.step 31 (.close 12)))) (.step 10 (.step 12 (.step 16 (.step 5 (.close 21)))))) (.step 6 (.step 9 (.close 12))))) (.step 6 (.step 68 (.step 32 (.close 8))))))) (.split 33 0 (.split 44 0 (.split 13 0 (.split 46 0 (.split 38 0 (.step 6 (.step 51 (.step 24 (.step 23 (.close 22))))) (.step 24 (.step 28 (.step 21 (.close 22))))) (.step 12 (.step 24 (.step 48 (.step 6 (.step 16 (.step 21 (.close 22)))))))) (.step 6 (.step 12 (.step 68 (.step 16 (.step 22 (.close 21))))))) (.step 51 (.step 10 (.step 28 (.step 6 (.close 9)))))) (.step 6 (.step 51 (.close 16))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1237940039285380275972866049, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142522942832742301087825921⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 33 0 (.split 25 0 (.split 56 0 (.step 12 (.split 38 0 (.step 31 (.step 8 (.close 9))) (.step 31 (.step 8 (.close 14))))) (.step 31 (.step 49 (.step 51 (.step 12 (.step 28 (.step 5 (.close 14)))))))) (.step 6 (.close 28))) (.step 6 (.step 12 (.step 51 (.split 38 0 (.step 31 (.step 8 (.close 9))) (.step 8 (.step 5 (.close 14)))))))) (.step 6 (.step 12 (.step 69 (.step 24 (.step 28 (.step 5 (.close 21)))))))) (.step 6 (.step 12 (.split 38 0 (.step 51 (.split 47 0 (.step 68 (.step 10 (.step 5 (.close 22)))) (.step 24 (.step 32 (.step 5 (.step 8 (.close 9))))))) (.step 32 (.step 24 (.step 51 (.step 10 (.step 5 (.close 21)))))))))) (.step 6 (.step 12 (.split 38 0 (.split 47 0 (.split 64 0 (.split 19 0 (.step 68 (.split 33 0 (.step 10 (.step 5 (.step 16 (.step 5 (.close 22))))) (.step 51 (.step 5 (.step 9 (.close 8)))))) (.step 22 (.step 51 (.step 22 (.step 10 (.step 5 (.close 14))))))) (.step 32 (.split 19 0 (.step 23 (.split 33 0 (.step 9 (.step 5 (.close 21))) (.step 23 (.close 11)))) (.step 9 (.step 15 (.close 21)))))) (.step 32 (.step 24 (.split 19 0 (.split 33 0 (.step 10 (.step 5 (.step 16 (.step 5 (.close 21))))) (.step 24 (.close 8))) (.step 10 (.step 16 (.close 21))))))) (.step 32 (.split 19 0 (.step 24 (.step 68 (.step 9 (.close 21)))) (.step 10 (.step 16 (.close 21))))))))) (.step 6 (.step 12 (.close 9)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741825, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142522942832742301087825921⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 9 0 (.split 18 0 (.reuse 0) (.run (.split 13 0 (.split 19 0 (.split 23 0 (.split 33 0 (.split 25 0 (.split 56 0 (.split 38 0 (.split 46 0 (.split 47 0 (.step 5 (.step 9 (.close 11))) (.step 31 (.step 32 (.close 5)))) (.step 12 (.step 28 (.step 5 (.step 24 (.step 22 (.close 17))))))) (.step 24 (.step 31 (.step 32 (.step 5 (.close 9)))))) (.step 24 (.step 31 (.step 51 (.step 24 (.step 21 (.step 9 (.close 12)))))))) (.step 6 (.close 28))) (.step 6 (.step 51 (.step 68 (.step 32 (.close 8)))))) (.step 6 (.step 69 (.step 24 (.step 10 (.step 24 (.close 21))))))) (.step 6 (.split 38 0 (.step 51 (.split 46 0 (.split 47 0 (.split 41 0 (.step 21 (.step 10 (.step 5 (.close 22)))) (.step 23 (.step 8 (.close 22)))) (.step 10 (.step 21 (.close 14)))) (.step 10 (.step 12 (.step 24 (.step 21 (.close 22))))))) (.step 10 (.step 21 (.step 22 (.close 5))))))) (.step 6 (.step 12 (.split 19 0 (.split 23 0 (.step 68 (.step 10 (.step 16 (.close 21)))) (.step 10 (.step 21 (.step 24 (.step 16 (.step 5 (.step 22 (.close 5)))))))) (.step 10 (.step 21 (.step 22 (.step 5 (.close 16))))))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1180591620717411303425, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921440184414732698150730230640553016527159297⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 3 0 (.split 18 0 (.split 19 0 (.step 47 (.split 33 0 (.step 68 (.split 56 0 (.step 31 (.step 60 (.step 5 (.step 12 (.close 21))))) (.step 51 (.step 31 (.step 16 (.step 5 (.step 21 (.close 38)))))))) (.step 5 (.step 24 (.step 51 (.step 5 (.step 12 (.step 5 (.close 16))))))))) (.split 25 0 (.step 51 (.step 47 (.step 24 (.step 68 (.close 31))))) (.step 6 (.step 28 (.step 12 (.close 29)))))) (.split 19 0 (.split 25 0 (.step 68 (.step 41 (.step 31 (.close 10)))) (.step 6 (.step 28 (.step 12 (.close 29))))) (.step 6 (.split 23 0 (.step 51 (.step 47 (.step 21 (.step 5 (.step 12 (.step 5 (.close 16))))))) (.step 69 (.step 21 (.step 22 (.step 10 (.step 5 (.step 12 (.step 5 (.close 16)))))))))))) (.split 25 0 (.split 40 0 (.split 19 0 (.split 33 0 (.step 47 (.split 56 0 (.split 60 0 (.step 6 (.step 5 (.close 12))) (.step 5 (.step 6 (.step 10 (.close 12))))) (.step 24 (.step 31 (.close 6))))) (.step 6 (.step 5 (.close 8)))) (.step 6 (.step 28 (.step 12 (.close 21))))) (.step 5 (.step 6 (.step 5 (.close 8))))) (.step 6 (.close 28)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1237941219877000992310427649, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142524123424363018499129345⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 18 0 (.split 19 0 (.split 25 0 (.split 23 0 (.split 33 0 (.step 47 (.split 56 0 (.split 41 0 (.step 49 (.step 6 (.step 5 (.step 12 (.close 21))))) (.step 6 (.step 5 (.step 12 (.step 5 (.close 14)))))) (.step 24 (.step 31 (.step 6 (.step 12 (.close 14))))))) (.step 6 (.step 12 (.step 47 (.step 5 (.step 14 (.step 5 (.step 21 (.close 22))))))))) (.step 6 (.step 12 (.step 68 (.step 10 (.step 26 (.close 21))))))) (.step 6 (.step 28 (.step 12 (.close 29))))) (.step 6 (.step 12 (.split 38 0 (.step 51 (.step 16 (.step 10 (.step 22 (.close 5))))) (.step 16 (.step 21 (.step 10 (.step 22 (.close 5))))))))) (.step 6 (.step 12 (.split 38 0 (.split 47 0 (.split 64 0 (.step 16 (.step 68 (.step 10 (.close 22)))) (.step 15 (.step 21 (.close 5)))) (.step 16 (.step 21 (.close 5)))) (.step 16 (.step 21 (.close 5))))))) (.step 6 (.step 12 (.step 10 (.close 16))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1, 5648033303795598179437473169482855732970034641640857108263564733330182374394210081738008392607303141205945399551307053588216324447088786566724092727047826758470111623598779477921441545544200383142524123424363018499129345⟩
def references : Fin 5 → Box := ![Part1.root, Part2.root, Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 5 := (.split 7 0 (.split 3 0 (.split 9 0 (.reuse 0) (.split 18 0 (.reuse 1) (.run (.split 19 0 (.split 23 0 (.split 29 0 (.split 33 0 (.split 25 0 (.split 56 0 (.step 12 (.step 5 (.step 16 (.step 5 (.close 21))))) (.step 24 (.step 31 (.close 12)))) (.step 24 (.step 31 (.close 12)))) (.step 12 (.step 5 (.step 14 (.step 5 (.step 21 (.close 8))))))) (.step 12 (.step 32 (.step 16 (.step 24 (.close 9)))))) (.step 12 (.step 69 (.split 38 0 (.step 24 (.step 16 (.step 69 (.step 5 (.step 9 (.close 21)))))) (.step 16 (.close 21)))))) (.step 12 (.split 38 0 (.split 47 0 (.step 22 (.step 51 (.step 21 (.step 16 (.step 5 (.step 8 (.close 9))))))) (.step 16 (.step 21 (.step 22 (.close 23))))) (.step 16 (.step 21 (.close 5))))))))) (.reuse 2)) (.split 9 0 (.split 13 0 (.reuse 3) (.run (.split 18 0 (.split 3 0 (.split 19 0 (.split 23 0 (.step 47 (.split 29 0 (.step 49 (.split 33 0 (.step 49 (.step 5 (.close 38))) (.step 5 (.step 16 (.close 21))))) (.step 12 (.step 24 (.step 68 (.step 16 (.step 21 (.close 22)))))))) (.step 6 (.step 12 (.step 68 (.step 10 (.step 16 (.step 26 (.close 21)))))))) (.step 6 (.step 12 (.split 31 0 (.step 10 (.step 16 (.step 22 (.step 24 (.step 22 (.close 21)))))) (.step 16 (.close 5)))))) (.step 6 (.step 12 (.step 10 (.close 16))))) (.step 6 (.step 12 (.split 29 0 (.step 10 (.step 16 (.step 21 (.step 68 (.step 21 (.close 22)))))) (.step 21 (.step 32 (.step 10 (.step 16 (.step 41 (.close 5)))))))))))) (.reuse 4)))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part8.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case88

namespace FiveColour.Packed.EnumerationChunks.Projected.Case88
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 332 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 332 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 332 0).upper i := by decide +kernel
lemma budget_model : (⟨25870188955332800404854, 5653543574944814750672969936779461275257770268855883317050768144265371539051058604403869402159033013261169810879268681636863343259231352980090841884530421197632408968721498099663395240153487909455453404202846298366279681, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 332), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨25870188955332800404854, 5653543574944814750672969936779461275257770268855883317050768144265371539051058604403869402159033013261169810879268681636863343259231352980090841884530421197632408968721498099663395240153487909455453404202846298366279681, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 332) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 332 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 332 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 332) (Archive.root 332) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 332 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 332 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case88

namespace FiveColour.Packed.EnumerationChunks.Case88
def root : Box := Archive.root 332
def families : Fin 78 → List Cut := Enumeration.families 332
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case88.original_covered points
end FiveColour.Packed.EnumerationChunks.Case88
