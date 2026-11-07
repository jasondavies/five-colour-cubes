module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case267
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685986170210923578369⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨29118013835820315960724, 5515657523237893750769616401267666472621798185321392991078523722325154067336513172972623469413915576853109158325054316899139412133020816947250683093707241424624660859922039682066589617310816688746414035206932982137857, 0⟩]
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
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195691172757316434803968200486755430683882117063723890770945⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.split 31 0 (.step 4 (.split 26 0 (.split 27 0 (.split 32 0 (.step 31 (.close 49)) (.step 4 (.close 18))) (.step 4 (.close 71))) (.step 4 (.close 50)))) (.split 26 0 (.split 45 0 (.split 1 0 (.step 71 (.close 49)) (.step 4 (.close 30))) (.step 4 (.close 58))) (.step 4 (.close 47)))) (.split 31 0 (.split 33 0 (.step 4 (.step 71 (.split 26 0 (.step 32 (.step 4 (.close 18))) (.step 4 (.close 31))))) (.split 44 0 (.step 4 (.close 18)) (.step 51 (.step 4 (.close 18))))) (.split 1 0 (.step 32 (.split 33 0 (.step 4 (.close 18)) (.step 32 (.step 4 (.close 18))))) (.step 4 (.step 32 (.close 4)))))) (.step 4 (.split 29 0 (.step 69 (.step 4 (.close 26))) (.step 32 (.step 69 (.step 4 (.close 26))))))) (.step 4 (.split 23 0 (.split 29 0 (.split 26 0 (.step 43 (.close 4)) (.step 4 (.close 23))) (.step 40 (.split 33 0 (.step 4 (.close 43)) (.step 32 (.close 4))))) (.step 23 (.step 24 (.step 43 (.close 4))))))) (.split 21 0 (.split 23 0 (.step 4 (.step 51 (.split 26 0 (.step 51 (.close 63)) (.step 4 (.step 23 (.close 31)))))) (.split 1 0 (.split 26 0 (.step 51 (.split 31 0 (.step 23 (.step 4 (.close 26))) (.step 4 (.step 23 (.close 24))))) (.step 23 (.split 29 0 (.step 4 (.step 23 (.close 31))) (.step 26 (.step 22 (.close 63)))))) (.step 4 (.close 10)))) (.step 4 (.step 23 (.step 51 (.close 24)))))))
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
def root : Box := ⟨1237940039285380274899124225, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643194121897323469764613009253130954752019895813582882781266945⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 21 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.step 4 (.step 71 (.split 26 0 (.split 27 0 (.step 18 (.close 12)) (.step 4 (.close 18))) (.step 4 (.close 31))))) (.split 44 0 (.step 4 (.close 18)) (.step 51 (.step 4 (.close 18))))) (.split 1 0 (.split 41 0 (.split 26 0 (.step 12 (.step 4 (.close 14))) (.step 4 (.close 47))) (.step 69 (.step 4 (.close 14)))) (.step 4 (.step 12 (.close 14))))) (.split 27 0 (.split 41 0 (.split 33 0 (.step 71 (.step 4 (.step 32 (.step 12 (.close 4))))) (.step 12 (.step 32 (.close 4)))) (.step 12 (.step 32 (.step 4 (.close 14))))) (.step 12 (.step 32 (.step 4 (.close 18)))))) (.split 41 0 (.split 44 0 (.step 4 (.step 12 (.split 32 0 (.step 4 (.step 23 (.close 26))) (.step 4 (.close 14))))) (.step 69 (.step 4 (.step 12 (.step 55 (.step 4 (.close 26))))))) (.step 4 (.step 40 (.close 69))))) (.step 4 (.step 18 (.step 4 (.step 40 (.split 23 0 (.split 33 0 (.split 26 0 (.step 49 (.step 4 (.close 44))) (.step 4 (.close 23))) (.step 12 (.step 40 (.close 36)))) (.step 23 (.close 24)))))))))
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
def root : Box := ⟨1237940039285380274899124225, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826558833783818933105021183120973497345⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 21 0 (.split 26 0 (.split 23 0 (.step 4 (.step 12 (.step 51 (.step 4 (.step 32 (.close 4)))))) (.step 12 (.step 4 (.split 32 0 (.step 51 (.step 26 (.step 23 (.step 4 (.close 18))))) (.step 4 (.close 68)))))) (.step 63 (.split 33 0 (.split 1 0 (.split 23 0 (.split 35 0 (.step 12 (.step 4 (.close 22))) (.step 23 (.step 12 (.step 21 (.close 40))))) (.step 12 (.step 22 (.step 4 (.close 21))))) (.step 4 (.close 22))) (.step 4 (.close 23))))) (.step 12 (.step 23 (.close 24)))))) (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.step 4 (.split 27 0 (.step 55 (.split 26 0 (.step 12 (.step 4 (.close 18))) (.step 4 (.step 12 (.step 23 (.close 21)))))) (.step 4 (.close 43)))) (.step 12 (.step 32 (.step 4 (.close 22))))) (.step 12 (.split 31 0 (.split 32 0 (.split 33 0 (.split 35 0 (.step 23 (.step 4 (.close 26))) (.step 21 (.close 4))) (.step 4 (.step 22 (.step 23 (.close 4))))) (.step 21 (.close 35))) (.step 16 (.close 15))))) (.step 12 (.step 23 (.close 24)))) (.step 12 (.split 31 0 (.split 32 0 (.split 33 0 (.split 35 0 (.split 41 0 (.step 51 (.step 4 (.close 21))) (.step 4 (.step 23 (.close 24)))) (.step 21 (.close 4))) (.step 22 (.close 4))) (.step 21 (.close 35))) (.step 16 (.close 15)))))))
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
def root : Box := ⟨1329227995784915872903807060280344577, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827888061779603848977924990181253841921⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.step 4 (.split 27 0 (.split 9 0 (.split 29 0 (.step 4 (.step 55 (.close 48))) (.step 12 (.step 4 (.step 31 (.close 23))))) (.step 12 (.close 63))) (.step 4 (.close 43)))) (.split 31 0 (.split 33 0 (.split 37 0 (.split 41 0 (.step 47 (.step 4 (.close 48))) (.step 4 (.close 11))) (.step 4 (.close 23))) (.step 4 (.close 23))) (.step 4 (.close 23)))) (.split 31 0 (.split 33 0 (.split 37 0 (.split 41 0 (.step 55 (.step 63 (.close 12))) (.step 4 (.close 15))) (.step 4 (.close 23))) (.step 4 (.close 23))) (.step 4 (.close 15)))) (.step 4 (.close 23))) (.split 21 0 (.split 26 0 (.split 31 0 (.split 33 0 (.split 1 0 (.step 12 (.step 51 (.close 63))) (.step 4 (.close 15))) (.step 4 (.close 22))) (.step 12 (.step 4 (.close 15)))) (.step 23 (.split 9 0 (.split 23 0 (.split 29 0 (.step 4 (.step 23 (.close 31))) (.step 31 (.step 15 (.close 40)))) (.step 12 (.step 15 (.step 22 (.step 4 (.close 26)))))) (.step 12 (.close 4))))) (.step 4 (.close 23)))) (.split 26 0 (.split 31 0 (.split 33 0 (.split 35 0 (.step 12 (.split 1 0 (.step 55 (.step 15 (.close 48))) (.step 4 (.close 15)))) (.step 23 (.step 12 (.step 21 (.close 38))))) (.step 12 (.step 4 (.close 23)))) (.step 12 (.step 4 (.close 15)))) (.step 23 (.split 31 0 (.split 33 0 (.step 38 (.step 12 (.step 38 (.step 23 (.close 63))))) (.step 4 (.close 23))) (.step 4 (.close 15)))))))
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
def root : Box := ⟨1298074214633706907132624082305025, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482684832122805336146945⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 27 0 (.split 31 0 (.split 32 0 (.split 9 0 (.step 4 (.close 18)) (.split 33 0 (.step 4 (.close 12)) (.step 12 (.close 4)))) (.split 9 0 (.split 26 0 (.step 50 (.step 4 (.close 18))) (.step 4 (.close 12))) (.step 12 (.close 17)))) (.step 68 (.split 1 0 (.step 43 (.split 41 0 (.step 18 (.step 14 (.close 4))) (.step 12 (.step 18 (.close 4))))) (.step 4 (.close 14))))) (.split 37 0 (.split 45 0 (.step 47 (.split 1 0 (.step 68 (.split 9 0 (.split 29 0 (.step 71 (.close 25)) (.step 12 (.close 18))) (.step 12 (.close 17)))) (.step 4 (.close 43)))) (.step 4 (.close 58))) (.step 4 (.close 18)))) (.step 4 (.step 40 (.step 68 (.step 4 (.close 10)))))) (.step 4 (.close 43))) (.step 4 (.split 21 0 (.step 51 (.step 4 (.close 43))) (.step 4 (.close 24))))) (.step 4 (.split 19 0 (.split 21 0 (.step 68 (.split 9 0 (.step 40 (.step 4 (.close 69))) (.step 12 (.close 4)))) (.step 4 (.close 24))) (.step 23 (.close 24))))) (.step 4 (.split 18 0 (.split 19 0 (.step 68 (.split 23 0 (.step 4 (.close 12)) (.step 4 (.close 15)))) (.step 4 (.close 15))) (.step 4 (.close 15))))))
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
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482684832122805336146945⟩
def references : Fin 4 → Box := ![Part0.root, Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 4 := (.split 11 0 (.split 12 0 (.split 9 0 (.split 18 0 (.reuse 0) (.run (.split 19 0 (.split 21 0 (.split 23 0 (.step 4 (.split 29 0 (.split 31 0 (.split 26 0 (.split 27 0 (.step 4 (.close 21)) (.step 4 (.close 10))) (.step 4 (.step 29 (.close 63)))) (.step 40 (.step 4 (.close 51)))) (.step 32 (.step 55 (.split 26 0 (.step 32 (.close 4)) (.step 4 (.close 38))))))) (.split 1 0 (.split 26 0 (.split 31 0 (.step 23 (.step 69 (.step 4 (.close 21)))) (.step 4 (.step 23 (.close 24)))) (.step 23 (.split 29 0 (.step 4 (.step 23 (.close 31))) (.step 21 (.step 23 (.close 31)))))) (.step 4 (.close 10)))) (.step 4 (.step 23 (.step 68 (.step 4 (.close 26)))))) (.split 21 0 (.split 26 0 (.split 1 0 (.split 23 0 (.step 51 (.split 31 0 (.step 23 (.step 4 (.close 21))) (.step 4 (.step 23 (.close 21))))) (.split 31 0 (.step 51 (.step 21 (.step 23 (.step 4 (.close 63))))) (.step 21 (.step 22 (.step 4 (.close 24)))))) (.step 4 (.close 22))) (.step 23 (.split 1 0 (.split 27 0 (.split 23 0 (.step 38 (.step 23 (.close 31))) (.step 21 (.step 22 (.step 21 (.close 26))))) (.step 4 (.close 21))) (.step 4 (.close 21))))) (.step 23 (.close 24)))))) (.reuse 1)) (.reuse 2)) (.reuse 3))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1152921504606846977, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827888061778365908939792531410961564673⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.step 4 (.split 26 0 (.step 47 (.step 4 (.step 31 (.close 23)))) (.step 4 (.close 47)))) (.split 31 0 (.split 27 0 (.split 32 0 (.step 23 (.step 47 (.step 4 (.close 26)))) (.step 4 (.close 6))) (.step 4 (.close 6))) (.step 4 (.close 23)))) (.step 4 (.close 23))) (.split 21 0 (.split 31 0 (.split 33 0 (.split 1 0 (.split 27 0 (.step 23 (.step 47 (.step 4 (.close 31)))) (.step 4 (.close 6))) (.step 4 (.close 22))) (.step 4 (.close 22))) (.step 4 (.close 23))) (.step 4 (.close 23)))) (.split 21 0 (.split 26 0 (.split 31 0 (.split 33 0 (.split 1 0 (.split 27 0 (.step 55 (.step 31 (.close 9))) (.step 4 (.close 6))) (.step 4 (.close 21))) (.step 4 (.close 23))) (.step 4 (.close 55))) (.step 6 (.close 28))) (.step 4 (.close 23)))) (.split 21 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 1 0 (.split 18 0 (.step 47 (.split 19 0 (.step 47 (.step 4 (.close 48))) (.step 6 (.step 4 (.step 15 (.close 63)))))) (.step 6 (.step 12 (.step 23 (.step 47 (.step 21 (.step 4 (.close 31)))))))) (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.close 21))) (.step 4 (.close 9)))) (.step 6 (.step 4 (.close 23)))) (.step 6 (.step 4 (.close 15)))) (.step 6 (.step 12 (.split 31 0 (.split 33 0 (.split 32 0 (.split 37 0 (.step 55 (.step 9 (.step 15 (.step 31 (.close 22))))) (.step 4 (.close 23))) (.step 4 (.close 23))) (.step 4 (.close 23))) (.step 4 (.close 15)))))) (.step 24 (.step 9 (.step 6 (.step 4 (.close 23))))))))
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
def root : Box := ⟨1125899906842625, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359852580542645547868430343865345⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 27 0 (.split 32 0 (.step 47 (.step 4 (.close 18))) (.split 1 0 (.step 47 (.step 50 (.step 4 (.close 18)))) (.step 4 (.close 35)))) (.step 47 (.close 4))) (.step 4 (.close 43))) (.step 4 (.close 43))) (.step 4 (.step 51 (.step 4 (.close 24))))) (.step 4 (.split 19 0 (.step 68 (.step 47 (.step 4 (.close 18)))) (.step 23 (.close 24))))) (.step 4 (.split 18 0 (.step 68 (.step 4 (.close 22))) (.step 4 (.close 23))))) (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.split 37 0 (.step 47 (.split 1 0 (.step 14 (.step 47 (.step 4 (.close 18)))) (.split 48 0 (.step 4 (.close 6)) (.step 4 (.close 34))))) (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.close 18))) (.step 4 (.close 8)))) (.split 37 0 (.split 44 0 (.split 45 0 (.step 47 (.step 14 (.step 18 (.step 50 (.close 4))))) (.step 4 (.close 58))) (.step 47 (.close 4))) (.step 4 (.close 18)))) (.split 1 0 (.split 29 0 (.step 47 (.step 4 (.close 34))) (.step 4 (.close 43))) (.step 4 (.close 6)))) (.split 26 0 (.split 29 0 (.step 14 (.step 4 (.close 43))) (.step 4 (.close 43))) (.step 4 (.close 6)))) (.split 31 0 (.step 4 (.close 43)) (.step 6 (.step 4 (.close 14))))) (.split 29 0 (.split 31 0 (.step 4 (.step 6 (.close 43))) (.step 6 (.step 4 (.close 14)))) (.step 4 (.step 6 (.close 50)))))))
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
def root : Box := ⟨1125899906842625, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685986170209849836545⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.split 9 0 (.reuse 0) (.run (.split 11 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 26 0 (.split 23 0 (.split 27 0 (.step 18 (.split 45 0 (.split 46 0 (.step 43 (.step 47 (.step 58 (.step 4 (.close 12))))) (.step 18 (.step 47 (.close 49)))) (.step 4 (.step 8 (.close 58))))) (.step 6 (.close 4))) (.step 4 (.close 43))) (.step 6 (.close 4))) (.step 4 (.close 43))) (.step 6 (.step 24 (.step 51 (.step 4 (.close 24)))))) (.step 4 (.step 6 (.step 24 (.step 68 (.step 4 (.close 23))))))) (.step 6 (.step 31 (.close 12)))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 37 0 (.split 44 0 (.step 14 (.close 4)) (.step 47 (.close 4))) (.step 4 (.close 12))) (.step 6 (.step 12 (.close 4)))) (.step 4 (.close 12))) (.step 4 (.close 12))) (.step 4 (.close 12)))))) (.run (.split 9 0 (.split 11 0 (.split 12 0 (.step 4 (.split 18 0 (.step 47 (.step 4 (.close 8))) (.step 4 (.close 9)))) (.split 29 0 (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.close 9))) (.step 4 (.close 9))) (.step 4 (.close 9)))) (.split 12 0 (.split 29 0 (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.close 8))) (.step 4 (.close 8))) (.step 4 (.close 8))) (.step 24 (.close 4)))) (.step 4 (.step 31 (.step 12 (.step 31 (.step 4 (.close 8)))))))))
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
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685986170209849836545⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part8.root]
def proof : Chunks.Proof 3 := (.split 5 0 (.split 6 0 (.reuse 0) (.split 9 0 (.split 11 0 (.reuse 1) (.run (.split 12 0 (.step 4 (.split 18 0 (.step 47 (.step 4 (.close 12))) (.step 4 (.close 23)))) (.split 29 0 (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.close 15))) (.step 4 (.close 9))) (.step 4 (.close 15)))))) (.run (.split 11 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.step 4 (.step 71 (.step 47 (.step 55 (.split 33 0 (.step 4 (.close 12)) (.step 12 (.close 4))))))) (.step 6 (.close 28))) (.step 6 (.step 12 (.step 4 (.step 15 (.step 23 (.close 26))))))) (.step 4 (.close 23))) (.step 6 (.step 12 (.split 23 0 (.step 4 (.step 15 (.step 22 (.close 31)))) (.step 15 (.step 22 (.step 4 (.step 9 (.close 26))))))))) (.step 6 (.step 12 (.split 19 0 (.split 23 0 (.step 4 (.step 15 (.step 21 (.step 23 (.step 24 (.close 63)))))) (.step 15 (.step 21 (.step 4 (.step 9 (.close 23)))))) (.step 15 (.step 21 (.step 22 (.close 4)))))))) (.step 6 (.step 12 (.step 4 (.step 9 (.close 15)))))) (.step 12 (.step 4 (.close 6))))))) (.reuse 2))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1073741825, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195691172757316434803968200486755430683882117063724964512769⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.step 4 (.step 71 (.split 26 0 (.split 27 0 (.step 18 (.close 26)) (.step 4 (.close 18))) (.step 4 (.close 28))))) (.split 44 0 (.step 4 (.close 18)) (.step 51 (.step 4 (.close 8))))) (.split 41 0 (.split 33 0 (.step 4 (.close 18)) (.step 6 (.step 4 (.close 18)))) (.step 6 (.step 69 (.step 4 (.close 18)))))) (.split 26 0 (.step 32 (.split 41 0 (.split 27 0 (.step 4 (.step 32 (.close 58))) (.step 6 (.close 4))) (.step 6 (.step 32 (.step 4 (.close 18)))))) (.step 6 (.close 28)))) (.split 41 0 (.split 44 0 (.step 4 (.split 31 0 (.step 55 (.step 4 (.close 31))) (.step 6 (.step 4 (.close 22))))) (.step 69 (.step 55 (.split 26 0 (.step 10 (.step 4 (.close 28))) (.step 4 (.close 6)))))) (.step 6 (.step 40 (.close 69))))) (.step 4 (.step 18 (.step 4 (.step 40 (.split 23 0 (.split 33 0 (.split 26 0 (.split 27 0 (.step 4 (.close 43)) (.step 4 (.close 6))) (.step 4 (.close 6))) (.step 6 (.step 40 (.close 36)))) (.step 23 (.close 24)))))))) (.split 21 0 (.split 23 0 (.split 33 0 (.split 44 0 (.step 4 (.split 31 0 (.step 51 (.close 63)) (.step 6 (.step 4 (.close 26))))) (.step 51 (.step 4 (.step 6 (.close 29))))) (.step 6 (.step 40 (.close 51)))) (.step 6 (.split 32 0 (.step 51 (.step 4 (.step 23 (.step 4 (.step 9 (.step 23 (.close 26))))))) (.step 4 (.step 10 (.step 4 (.close 24))))))) (.step 4 (.step 23 (.close 24))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1073741825, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826560131856795626772642935471230419969⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 11 0 (.split 18 0 (.reuse 0) (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.split 31 0 (.split 41 0 (.split 33 0 (.split 53 0 (.step 4 (.close 31)) (.step 4 (.close 6))) (.step 6 (.step 4 (.close 22)))) (.step 6 (.step 40 (.step 4 (.close 51))))) (.step 6 (.step 40 (.step 55 (.step 30 (.close 43)))))) (.step 6 (.close 28))) (.step 6 (.split 32 0 (.split 35 0 (.step 23 (.step 69 (.step 4 (.close 63)))) (.step 9 (.step 21 (.close 4)))) (.step 4 (.step 10 (.step 4 (.close 24))))))) (.step 4 (.step 23 (.close 24)))) (.step 6 (.split 31 0 (.split 32 0 (.step 51 (.split 29 0 (.step 23 (.step 4 (.step 9 (.step 21 (.close 4))))) (.step 32 (.step 23 (.step 9 (.step 4 (.close 12))))))) (.step 10 (.step 21 (.close 4)))) (.step 23 (.split 32 0 (.split 35 0 (.step 51 (.split 44 0 (.step 4 (.close 24)) (.step 9 (.close 8)))) (.step 4 (.close 21))) (.step 4 (.close 35))))))))) (.run (.split 1 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.split 27 0 (.split 33 0 (.split 53 0 (.step 12 (.step 4 (.close 18))) (.step 8 (.step 12 (.step 4 (.close 18))))) (.step 12 (.step 43 (.step 8 (.close 58))))) (.step 18 (.close 6))) (.step 4 (.close 6))) (.step 68 (.close 63))) (.step 4 (.close 43))) (.step 12 (.step 24 (.step 51 (.step 4 (.close 24)))))) (.step 12 (.step 24 (.split 19 0 (.step 68 (.close 23)) (.step 23 (.close 24)))))) (.step 4 (.close 43)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1237940039285380275972866049, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482684832122806409888769⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.split 29 0 (.split 41 0 (.split 33 0 (.split 27 0 (.step 71 (.step 4 (.step 12 (.close 31)))) (.step 6 (.close 4))) (.step 6 (.step 12 (.step 4 (.close 18))))) (.step 6 (.step 12 (.step 69 (.step 4 (.close 18)))))) (.step 6 (.step 12 (.step 32 (.step 4 (.close 18)))))) (.step 6 (.close 28))) (.step 6 (.step 12 (.step 4 (.split 32 0 (.step 55 (.step 69 (.step 4 (.close 26)))) (.step 4 (.close 43))))))) (.step 6 (.step 12 (.step 4 (.split 32 0 (.split 35 0 (.step 43 (.close 4)) (.step 4 (.close 23))) (.step 4 (.close 43))))))) (.step 6 (.step 12 (.split 32 0 (.split 35 0 (.step 51 (.step 4 (.step 51 (.step 4 (.close 26))))) (.step 23 (.step 32 (.step 4 (.step 9 (.close 55)))))) (.step 32 (.step 4 (.close 43))))))) (.step 6 (.step 12 (.split 32 0 (.split 35 0 (.split 47 0 (.split 64 0 (.split 19 0 (.split 21 0 (.step 4 (.step 55 (.step 4 (.close 69)))) (.step 23 (.close 24))) (.split 1 0 (.step 51 (.split 41 0 (.step 23 (.step 4 (.close 26))) (.step 26 (.close 4)))) (.step 9 (.step 4 (.close 14))))) (.step 23 (.step 32 (.step 63 (.step 23 (.close 4)))))) (.step 24 (.step 32 (.step 55 (.step 48 (.step 58 (.step 24 (.close 4)))))))) (.step 32 (.step 4 (.step 9 (.step 15 (.close 21)))))) (.step 32 (.step 4 (.close 68))))))) (.step 12 (.close 4))) (.step 12 (.close 4))))
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
def root : Box := ⟨1073741825, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685985044311016735745⟩
def references : Fin 2 → Box := ![Part11.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 6 0 (.split 9 0 (.split 12 0 (.reuse 0) (.run (.split 11 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 1 0 (.split 23 0 (.split 27 0 (.split 26 0 (.step 12 (.step 55 (.step 71 (.split 33 0 (.step 4 (.step 9 (.close 31))) (.step 51 (.step 4 (.close 9))))))) (.step 6 (.close 28))) (.step 6 (.close 4))) (.step 6 (.split 32 0 (.step 55 (.close 31)) (.step 4 (.close 9))))) (.step 4 (.close 23))) (.step 4 (.close 23))) (.step 6 (.step 12 (.split 23 0 (.split 31 0 (.step 51 (.step 4 (.step 9 (.step 15 (.step 4 (.close 21)))))) (.step 4 (.close 15))) (.step 9 (.step 22 (.step 4 (.step 15 (.close 26))))))))) (.step 6 (.step 12 (.split 19 0 (.split 23 0 (.split 31 0 (.split 32 0 (.step 55 (.step 9 (.close 31))) (.step 4 (.close 9))) (.step 4 (.close 15))) (.step 9 (.step 21 (.step 4 (.step 15 (.close 23)))))) (.step 9 (.step 21 (.step 22 (.step 4 (.close 15))))))))) (.step 12 (.step 31 (.step 4 (.close 14))))))) (.reuse 1)) (.run (.split 12 0 (.split 21 0 (.split 26 0 (.split 32 0 (.split 37 0 (.split 45 0 (.split 54 0 (.split 68 0 (.split 70 0 (.split 1 0 (.step 47 (.split 11 0 (.step 6 (.close 4)) (.step 12 (.step 4 (.close 6))))) (.step 4 (.step 23 (.close 6)))) (.step 6 (.close 4))) (.step 4 (.step 6 (.close 10)))) (.step 6 (.close 31))) (.step 4 (.step 6 (.close 9)))) (.step 6 (.close 4))) (.step 6 (.close 4))) (.step 6 (.close 28))) (.step 6 (.close 4))) (.step 6 (.step 4 (.step 6 (.close 9)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685986170210923578369⟩
def references : Fin 2 → Box := ![Part9.root, Part13.root]
def proof : Chunks.Proof 2 := (.split 3 0 (.reuse 0) (.split 5 0 (.reuse 1) (.run (.split 6 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 32 0 (.split 37 0 (.split 45 0 (.split 54 0 (.split 68 0 (.split 70 0 (.split 19 0 (.step 47 (.split 33 0 (.split 53 0 (.step 4 (.close 6)) (.step 51 (.step 4 (.close 6)))) (.step 6 (.close 4)))) (.step 6 (.close 4))) (.step 6 (.close 8))) (.step 6 (.close 8))) (.step 6 (.close 4))) (.step 4 (.step 6 (.close 8)))) (.step 6 (.close 4))) (.step 6 (.close 71))) (.step 6 (.close 4))) (.step 4 (.step 6 (.close 4)))) (.step 6 (.close 4))) (.step 6 (.close 4))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part14.excludes
end FiveColour.Packed.ProjectedChunks.Case267
