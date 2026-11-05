module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
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
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643194121897323469764613009253130953514079856528202607882142721⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 21 0 (.split 23 0 (.split 29 0 (.split 31 0 (.step 4 (.split 26 0 (.split 27 0 (.split 32 0 (.step 31 (.step 4 (.close 12))) (.step 4 (.close 18))) (.step 4 (.step 11 (.close 18)))) (.step 4 (.step 10 (.step 12 (.close 29)))))) (.split 26 0 (.split 37 0 (.split 45 0 (.split 1 0 (.step 71 (.step 12 (.step 17 (.step 18 (.close 30))))) (.step 4 (.close 30))) (.step 4 (.step 14 (.step 18 (.close 30))))) (.step 4 (.close 18))) (.step 4 (.step 11 (.step 4 (.close 18)))))) (.split 31 0 (.split 33 0 (.step 4 (.step 71 (.split 26 0 (.step 32 (.step 4 (.step 11 (.close 12)))) (.step 4 (.step 10 (.close 12)))))) (.split 44 0 (.step 4 (.close 18)) (.step 51 (.step 4 (.step 11 (.close 18)))))) (.split 1 0 (.step 32 (.split 33 0 (.step 4 (.step 14 (.step 11 (.close 17)))) (.step 32 (.step 4 (.step 14 (.step 11 (.close 17))))))) (.step 4 (.step 32 (.close 4)))))) (.step 4 (.split 29 0 (.step 69 (.step 4 (.step 10 (.close 12)))) (.step 32 (.step 55 (.step 69 (.step 4 (.step 10 (.close 12))))))))) (.step 4 (.split 23 0 (.split 29 0 (.split 26 0 (.step 43 (.close 4)) (.step 4 (.step 11 (.close 15)))) (.step 40 (.split 33 0 (.step 4 (.step 26 (.step 4 (.close 30)))) (.step 32 (.close 4))))) (.step 23 (.step 24 (.step 43 (.close 4))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1532495540865888858358347027150309183618739122183602177, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643194123429819010630501867611477980664389040146941730065744897⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 21 0 (.split 23 0 (.step 4 (.split 29 0 (.split 31 0 (.split 26 0 (.split 27 0 (.step 4 (.step 12 (.close 18))) (.step 4 (.close 10))) (.step 4 (.step 29 (.step 4 (.step 12 (.close 18)))))) (.step 4 (.step 40 (.step 4 (.step 22 (.step 4 (.close 30))))))) (.step 32 (.step 55 (.split 26 0 (.step 32 (.close 4)) (.step 4 (.step 23 (.step 10 (.step 12 (.close 18)))))))))) (.split 1 0 (.split 26 0 (.split 31 0 (.step 23 (.step 69 (.step 4 (.step 18 (.step 12 (.close 21)))))) (.step 4 (.step 23 (.step 4 (.step 16 (.step 10 (.close 21))))))) (.step 23 (.split 29 0 (.step 4 (.step 23 (.step 10 (.step 18 (.step 12 (.close 21)))))) (.step 21 (.step 4 (.step 23 (.step 10 (.step 18 (.step 12 (.close 21)))))))))) (.step 4 (.close 10)))) (.step 4 (.step 23 (.step 68 (.step 4 (.step 21 (.close 4))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826558833782580993065735802846074373121⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 21 0 (.split 23 0 (.step 4 (.step 51 (.split 26 0 (.step 51 (.step 4 (.close 12))) (.step 4 (.step 23 (.step 10 (.step 12 (.close 18)))))))) (.split 1 0 (.split 26 0 (.step 51 (.split 31 0 (.step 23 (.step 4 (.step 18 (.step 12 (.close 21))))) (.step 4 (.step 23 (.step 4 (.close 10)))))) (.step 23 (.split 29 0 (.step 4 (.step 23 (.step 10 (.step 18 (.step 12 (.close 21)))))) (.step 26 (.step 22 (.step 4 (.step 10 (.close 12)))))))) (.step 4 (.close 10)))) (.step 4 (.step 23 (.step 51 (.step 4 (.step 22 (.step 4 (.close 10)))))))))) (.split 19 0 (.reuse 1) (.run (.split 21 0 (.split 26 0 (.split 1 0 (.split 23 0 (.step 51 (.split 31 0 (.step 23 (.step 4 (.step 18 (.step 12 (.close 21))))) (.step 4 (.step 23 (.step 4 (.close 10)))))) (.split 31 0 (.step 51 (.step 21 (.step 23 (.step 4 (.step 21 (.step 4 (.close 12))))))) (.step 21 (.step 22 (.step 4 (.step 10 (.close 16))))))) (.step 4 (.step 21 (.close 4)))) (.step 23 (.split 1 0 (.split 27 0 (.split 23 0 (.step 38 (.step 4 (.step 23 (.step 10 (.step 18 (.step 12 (.close 21))))))) (.step 21 (.step 22 (.step 4 (.step 21 (.step 4 (.close 10))))))) (.step 4 (.step 10 (.close 21)))) (.step 4 (.step 10 (.close 21)))))) (.step 4 (.step 23 (.step 4 (.step 21 (.step 22 (.close 10))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1237940039285380274899124225, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643194121897323469764613009253130954752019895813582882781266945⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 21 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.step 4 (.step 71 (.split 26 0 (.split 27 0 (.step 18 (.step 4 (.close 12))) (.step 4 (.step 11 (.close 12)))) (.step 4 (.step 10 (.close 12)))))) (.split 44 0 (.step 4 (.step 12 (.close 18))) (.step 51 (.step 4 (.step 11 (.step 12 (.close 18))))))) (.split 1 0 (.split 41 0 (.split 26 0 (.step 12 (.step 4 (.close 14))) (.step 4 (.step 11 (.step 4 (.close 12))))) (.step 12 (.step 69 (.step 4 (.step 11 (.close 14)))))) (.step 4 (.step 12 (.step 4 (.close 14)))))) (.split 27 0 (.split 41 0 (.split 33 0 (.step 71 (.step 4 (.step 32 (.step 4 (.step 12 (.close 4)))))) (.step 12 (.step 4 (.step 32 (.close 4))))) (.step 12 (.step 32 (.step 4 (.close 14))))) (.step 12 (.step 32 (.step 4 (.step 11 (.close 14))))))) (.split 41 0 (.split 44 0 (.step 4 (.step 12 (.split 32 0 (.step 4 (.step 23 (.step 18 (.close 21)))) (.step 4 (.close 14))))) (.step 69 (.step 4 (.step 12 (.step 55 (.step 4 (.step 10 (.close 18)))))))) (.step 4 (.step 12 (.step 40 (.step 55 (.step 4 (.step 14 (.close 30))))))))) (.step 4 (.step 18 (.step 4 (.step 40 (.split 23 0 (.split 33 0 (.split 26 0 (.step 49 (.step 4 (.step 12 (.step 4 (.close 14))))) (.step 4 (.step 11 (.close 12)))) (.step 12 (.step 36 (.step 40 (.step 4 (.step 14 (.close 30))))))) (.step 12 (.step 23 (.step 4 (.step 14 (.step 10 (.close 21)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1532495540865888858358347028388249222904119397082726401, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826558833783818933105021183120973497345⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.step 4 (.split 27 0 (.step 55 (.split 26 0 (.step 12 (.step 4 (.close 18))) (.step 4 (.step 12 (.step 23 (.step 10 (.close 18))))))) (.step 4 (.step 12 (.step 10 (.close 14)))))) (.step 12 (.step 4 (.step 32 (.step 4 (.step 15 (.close 10))))))) (.step 12 (.split 31 0 (.split 32 0 (.split 33 0 (.split 35 0 (.step 4 (.step 23 (.step 4 (.step 18 (.step 10 (.close 21)))))) (.step 21 (.close 4))) (.step 4 (.step 22 (.step 23 (.close 4))))) (.step 4 (.step 21 (.step 4 (.close 10))))) (.step 4 (.step 16 (.close 15)))))) (.step 4 (.step 12 (.step 23 (.step 4 (.step 14 (.step 21 (.close 10)))))))) (.step 12 (.split 31 0 (.split 32 0 (.split 33 0 (.split 35 0 (.split 41 0 (.step 23 (.step 51 (.step 4 (.step 10 (.close 18))))) (.step 4 (.step 23 (.step 4 (.step 10 (.close 21)))))) (.step 21 (.close 4))) (.step 4 (.step 22 (.close 4)))) (.step 4 (.step 21 (.step 4 (.close 10))))) (.step 16 (.close 15))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1329227995784915872903807060280344577, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643194121897323469764613010582358950536935768717389943061611521⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 21 0 (.split 23 0 (.split 26 0 (.step 4 (.split 27 0 (.split 9 0 (.split 29 0 (.step 4 (.step 55 (.step 4 (.step 12 (.close 15))))) (.step 12 (.step 4 (.step 23 (.step 31 (.step 4 (.close 15))))))) (.step 12 (.step 4 (.step 12 (.close 15))))) (.step 4 (.step 12 (.close 14))))) (.split 31 0 (.split 33 0 (.split 37 0 (.split 41 0 (.step 47 (.step 4 (.step 31 (.close 15)))) (.step 4 (.close 11))) (.step 4 (.step 11 (.close 12)))) (.step 4 (.step 11 (.step 12 (.close 15))))) (.step 4 (.step 11 (.step 12 (.close 15)))))) (.split 31 0 (.split 33 0 (.split 37 0 (.split 41 0 (.step 55 (.step 63 (.close 12))) (.step 4 (.step 11 (.close 12)))) (.step 4 (.step 12 (.step 11 (.close 15))))) (.step 4 (.step 12 (.step 15 (.step 11 (.close 21)))))) (.step 4 (.step 12 (.close 15))))) (.step 4 (.step 12 (.step 15 (.close 23))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1329227995784915872903807060280344577, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827888061779603848977924990181253841921⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 21 0 (.split 26 0 (.split 31 0 (.split 33 0 (.split 1 0 (.step 12 (.step 23 (.step 51 (.step 4 (.step 15 (.close 18)))))) (.step 4 (.step 12 (.close 15)))) (.step 4 (.step 12 (.step 15 (.step 21 (.close 22)))))) (.step 4 (.step 12 (.step 4 (.close 15))))) (.step 23 (.split 31 0 (.split 9 0 (.split 23 0 (.split 29 0 (.step 4 (.step 12 (.step 23 (.step 10 (.step 15 (.close 18)))))) (.step 12 (.step 31 (.step 15 (.step 4 (.step 11 (.close 21))))))) (.step 12 (.step 15 (.step 22 (.step 4 (.step 10 (.close 18))))))) (.step 12 (.close 4))) (.step 4 (.step 12 (.step 11 (.close 15))))))) (.step 4 (.step 12 (.step 15 (.step 22 (.close 11)))))))) (.run (.split 21 0 (.split 26 0 (.split 31 0 (.split 33 0 (.split 35 0 (.step 12 (.split 1 0 (.step 23 (.step 55 (.step 15 (.step 4 (.close 21))))) (.step 4 (.close 15)))) (.step 23 (.step 12 (.step 21 (.step 4 (.close 15)))))) (.step 4 (.step 12 (.step 4 (.step 15 (.step 21 (.close 22))))))) (.step 4 (.step 12 (.step 4 (.close 15))))) (.step 23 (.split 31 0 (.split 33 0 (.step 38 (.step 12 (.step 38 (.step 23 (.step 10 (.step 15 (.close 18))))))) (.step 4 (.step 12 (.step 11 (.step 15 (.step 21 (.close 22))))))) (.step 4 (.step 12 (.close 15)))))) (.step 4 (.step 12 (.step 15 (.step 21 (.step 22 (.close 11)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1298074214633706907132624082305025, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826560131858033566811928315745055802369⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 27 0 (.split 31 0 (.split 32 0 (.split 9 0 (.step 4 (.step 12 (.step 14 (.close 18)))) (.step 18 (.split 33 0 (.step 4 (.close 12)) (.step 12 (.close 4))))) (.split 1 0 (.split 9 0 (.split 26 0 (.step 50 (.step 4 (.step 12 (.step 14 (.close 18))))) (.step 4 (.close 12))) (.step 12 (.step 4 (.close 14)))) (.step 4 (.close 12)))) (.step 68 (.split 1 0 (.step 43 (.split 41 0 (.step 18 (.step 14 (.close 4))) (.step 12 (.step 18 (.close 4))))) (.step 4 (.step 12 (.close 14)))))) (.split 37 0 (.split 45 0 (.step 47 (.split 1 0 (.step 68 (.split 9 0 (.split 29 0 (.step 71 (.step 12 (.step 4 (.close 14)))) (.step 12 (.close 18))) (.step 12 (.step 4 (.close 14))))) (.step 4 (.step 12 (.close 14))))) (.step 4 (.step 12 (.step 14 (.step 18 (.close 30)))))) (.step 4 (.step 12 (.step 14 (.close 18)))))) (.step 4 (.step 40 (.step 68 (.step 4 (.close 10)))))) (.step 4 (.step 12 (.step 14 (.step 18 (.step 10 (.step 21 (.close 30)))))))) (.step 4 (.step 51 (.split 21 0 (.step 51 (.step 4 (.step 12 (.close 10)))) (.step 4 (.step 12 (.step 14 (.step 18 (.step 10 (.close 21)))))))))) (.step 4 (.split 19 0 (.split 21 0 (.step 68 (.split 9 0 (.step 40 (.step 4 (.step 10 (.close 4)))) (.step 12 (.close 4)))) (.step 4 (.step 12 (.step 14 (.step 18 (.step 21 (.close 10))))))) (.step 12 (.step 23 (.step 4 (.close 24))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482684832122805336146945⟩
def references : Fin 5 → Box := ![Part2.root, Part3.root, Part4.root, Part6.root, Part7.root]
def proof : Chunks.Proof 5 := (.split 11 0 (.split 12 0 (.split 9 0 (.reuse 0) (.split 18 0 (.split 19 0 (.reuse 1) (.run (.split 21 0 (.split 26 0 (.split 23 0 (.step 4 (.step 12 (.step 51 (.step 4 (.step 32 (.close 4)))))) (.step 12 (.step 4 (.split 32 0 (.step 51 (.step 26 (.step 4 (.step 23 (.step 4 (.close 18)))))) (.step 4 (.step 16 (.step 18 (.step 10 (.close 21))))))))) (.step 63 (.split 33 0 (.split 1 0 (.split 23 0 (.split 35 0 (.step 4 (.step 12 (.step 4 (.step 10 (.close 11))))) (.step 23 (.step 12 (.step 4 (.step 21 (.step 4 (.close 11))))))) (.step 12 (.step 22 (.step 4 (.step 10 (.close 11)))))) (.step 4 (.step 10 (.close 12)))) (.step 4 (.step 12 (.step 4 (.step 11 (.step 15 (.step 21 (.close 22)))))))))) (.step 4 (.step 12 (.step 23 (.step 4 (.step 14 (.step 22 (.close 10)))))))))) (.reuse 2))) (.reuse 3)) (.split 12 0 (.reuse 4) (.run (.step 4 (.split 18 0 (.split 19 0 (.step 68 (.split 23 0 (.step 4 (.close 12)) (.step 4 (.step 10 (.close 12))))) (.step 4 (.step 12 (.step 10 (.close 15))))) (.step 4 (.step 12 (.close 15))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1152921504606846977, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826558833782580993066888724350681220097⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.step 4 (.step 47 (.split 26 0 (.step 47 (.step 4 (.step 31 (.step 4 (.close 15))))) (.step 4 (.step 6 (.step 4 (.step 6 (.close 28)))))))) (.split 31 0 (.split 27 0 (.split 32 0 (.step 23 (.step 47 (.step 4 (.step 18 (.step 12 (.close 21)))))) (.step 4 (.close 6))) (.step 4 (.close 6))) (.step 4 (.step 6 (.step 9 (.step 15 (.close 21))))))) (.step 4 (.step 6 (.step 9 (.close 23))))) (.split 21 0 (.split 31 0 (.split 33 0 (.split 1 0 (.step 47 (.split 27 0 (.step 23 (.step 47 (.step 4 (.step 18 (.step 22 (.close 12)))))) (.step 4 (.close 6)))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.step 9 (.step 21 (.close 22)))))) (.step 4 (.step 6 (.step 9 (.step 15 (.step 21 (.close 22))))))) (.step 4 (.step 6 (.step 9 (.step 22 (.close 15))))))) (.split 21 0 (.split 26 0 (.split 31 0 (.split 33 0 (.split 1 0 (.split 27 0 (.step 55 (.step 31 (.close 9))) (.step 4 (.close 6))) (.step 4 (.step 9 (.close 21)))) (.step 4 (.step 9 (.step 21 (.close 22))))) (.step 4 (.step 15 (.step 21 (.step 23 (.step 4 (.close 8))))))) (.step 6 (.step 4 (.close 10)))) (.step 4 (.step 6 (.step 9 (.step 21 (.step 22 (.close 15)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1152921504606846977, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359852580542646699664035043869697⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 11 0 (.split 12 0 (.reuse 0) (.run (.split 21 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 1 0 (.split 18 0 (.step 47 (.split 19 0 (.step 4 (.step 47 (.step 4 (.step 15 (.step 12 (.close 18)))))) (.step 6 (.step 4 (.step 12 (.step 15 (.step 4 (.step 18 (.close 21))))))))) (.step 6 (.step 12 (.step 23 (.step 47 (.step 21 (.step 4 (.step 15 (.step 18 (.close 21)))))))))) (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 15)))) (.step 4 (.step 6 (.close 9))))) (.step 6 (.step 4 (.step 9 (.step 15 (.close 21)))))) (.step 6 (.step 4 (.step 9 (.close 15))))) (.step 6 (.step 12 (.split 31 0 (.split 33 0 (.split 32 0 (.split 37 0 (.step 55 (.step 9 (.step 15 (.step 31 (.step 4 (.close 21)))))) (.step 4 (.step 9 (.step 15 (.close 21))))) (.step 4 (.step 9 (.step 15 (.close 21))))) (.step 4 (.step 9 (.step 15 (.step 21 (.close 22)))))) (.step 4 (.step 9 (.close 15))))))) (.step 24 (.step 9 (.step 6 (.step 4 (.step 15 (.close 23))))))))) (.run (.split 12 0 (.step 4 (.split 18 0 (.step 47 (.step 4 (.close 12))) (.step 4 (.step 6 (.step 9 (.close 15)))))) (.step 24 (.split 29 0 (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 15)))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.step 9 (.close 15)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685985044309942993921⟩
def references : Fin 2 → Box := ![Part8.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 6 0 (.reuse 0) (.split 9 0 (.reuse 1) (.run (.split 11 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.step 4 (.step 71 (.step 47 (.step 55 (.split 33 0 (.step 4 (.close 12)) (.step 4 (.step 12 (.close 4)))))))) (.step 6 (.step 4 (.close 10)))) (.step 6 (.step 12 (.step 4 (.step 15 (.step 23 (.step 9 (.step 18 (.close 21))))))))) (.step 4 (.step 6 (.step 9 (.step 12 (.step 15 (.step 21 (.close 22)))))))) (.step 6 (.step 12 (.split 23 0 (.step 4 (.step 15 (.step 22 (.step 4 (.close 9))))) (.step 15 (.step 22 (.step 4 (.step 9 (.step 4 (.close 18)))))))))) (.step 6 (.step 12 (.split 19 0 (.split 23 0 (.step 4 (.step 15 (.step 21 (.step 23 (.step 24 (.step 4 (.step 9 (.close 18)))))))) (.step 15 (.step 21 (.step 4 (.step 9 (.step 4 (.close 22))))))) (.step 15 (.step 21 (.step 4 (.step 22 (.close 4))))))))) (.step 6 (.step 12 (.step 4 (.step 9 (.step 4 (.step 12 (.close 15)))))))) (.step 4 (.step 12 (.step 4 (.close 6))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1298074214633706908258523989147649, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195691172757316434803969531012825430233461929129308160263169⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.split 37 0 (.step 47 (.split 1 0 (.step 14 (.step 47 (.step 4 (.step 12 (.close 18))))) (.split 48 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 12)))))) (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 12)))) (.step 4 (.step 6 (.close 8))))) (.split 37 0 (.split 44 0 (.split 45 0 (.step 47 (.step 14 (.step 18 (.step 50 (.close 4))))) (.step 4 (.step 6 (.step 12 (.step 14 (.close 18)))))) (.step 18 (.step 47 (.close 4)))) (.step 4 (.step 6 (.step 8 (.step 12 (.close 14))))))) (.split 1 0 (.split 26 0 (.split 29 0 (.step 47 (.step 4 (.step 12 (.close 14)))) (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.close 18))))))) (.step 4 (.close 6))) (.step 4 (.close 6)))) (.split 1 0 (.split 26 0 (.split 29 0 (.step 14 (.step 4 (.step 6 (.step 8 (.step 12 (.close 18)))))) (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.step 18 (.close 21)))))))) (.step 4 (.close 6))) (.step 4 (.close 6)))) (.split 1 0 (.split 26 0 (.split 29 0 (.split 31 0 (.step 4 (.step 6 (.step 8 (.step 12 (.step 18 (.close 21)))))) (.step 6 (.step 4 (.step 8 (.step 12 (.close 14)))))) (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.step 18 (.step 21 (.close 22))))))))) (.step 4 (.close 6))) (.step 4 (.close 6)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1237940039286506174805966849, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482684833248705242989569⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 26 0 (.split 23 0 (.split 27 0 (.step 18 (.split 45 0 (.split 46 0 (.step 43 (.step 47 (.step 58 (.step 4 (.close 12))))) (.step 18 (.step 47 (.step 14 (.close 49))))) (.step 4 (.step 8 (.step 12 (.step 14 (.close 18))))))) (.step 6 (.close 4))) (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.close 18))))))) (.step 4 (.step 6 (.close 4)))) (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.step 18 (.close 21)))))))) (.step 4 (.step 6 (.step 24 (.step 51 (.step 4 (.step 8 (.close 12)))))))) (.step 4 (.step 6 (.step 24 (.step 68 (.step 4 (.step 9 (.step 4 (.close 12))))))))) (.step 4 (.step 6 (.step 31 (.step 4 (.step 8 (.close 12))))))) (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.split 37 0 (.split 44 0 (.step 14 (.close 4)) (.step 18 (.step 47 (.close 4)))) (.step 4 (.step 6 (.step 8 (.close 12))))) (.step 6 (.step 12 (.close 4)))) (.step 4 (.step 6 (.step 8 (.close 12))))) (.step 4 (.step 6 (.step 8 (.close 12))))) (.step 4 (.step 6 (.step 8 (.close 12))))) (.step 4 (.step 6 (.close 12))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1125899906842625, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482684833248705242989569⟩
def references : Fin 2 → Box := ![Part12.root, Part13.root]
def proof : Chunks.Proof 2 := (.split 9 0 (.split 11 0 (.run (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 27 0 (.split 32 0 (.step 47 (.step 4 (.close 18))) (.split 1 0 (.step 47 (.step 50 (.step 4 (.close 18)))) (.step 4 (.step 8 (.close 32))))) (.step 47 (.close 4))) (.step 4 (.step 6 (.step 8 (.step 16 (.step 18 (.close 32))))))) (.step 4 (.step 6 (.step 8 (.step 18 (.step 16 (.step 21 (.close 32)))))))) (.step 4 (.step 51 (.step 4 (.step 6 (.step 8 (.close 16))))))) (.step 4 (.split 19 0 (.step 68 (.step 47 (.step 4 (.close 18)))) (.step 6 (.step 23 (.step 4 (.step 8 (.close 24)))))))) (.step 4 (.split 18 0 (.step 68 (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.step 9 (.close 15)))))))) (.split 18 0 (.reuse 0) (.run (.split 1 0 (.split 26 0 (.split 29 0 (.split 31 0 (.step 4 (.step 6 (.step 8 (.step 12 (.step 18 (.close 21)))))) (.step 6 (.step 4 (.step 8 (.step 12 (.close 14)))))) (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.step 18 (.step 21 (.close 22))))))))) (.step 4 (.close 6))) (.step 4 (.close 6)))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1073741825, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492261997689564576117427609643826695780448531343990894622745607275521⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.step 4 (.step 71 (.split 26 0 (.split 27 0 (.step 18 (.step 4 (.close 9))) (.step 4 (.step 6 (.close 8)))) (.step 4 (.step 9 (.step 10 (.close 12))))))) (.split 44 0 (.step 4 (.step 6 (.close 18))) (.step 51 (.step 4 (.step 6 (.close 8)))))) (.split 1 0 (.split 41 0 (.split 26 0 (.split 33 0 (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.close 17)))))) (.step 6 (.step 4 (.step 8 (.step 14 (.step 17 (.close 18))))))) (.step 4 (.close 6))) (.step 6 (.step 69 (.step 4 (.step 8 (.step 12 (.step 14 (.close 17)))))))) (.step 4 (.step 27 (.close 4))))) (.split 26 0 (.step 32 (.split 41 0 (.split 27 0 (.step 4 (.step 32 (.step 4 (.step 8 (.close 12))))) (.step 6 (.close 4))) (.step 6 (.step 32 (.step 4 (.step 8 (.step 12 (.step 14 (.close 17))))))))) (.step 4 (.step 6 (.step 4 (.close 12)))))) (.split 41 0 (.split 44 0 (.step 4 (.split 31 0 (.step 55 (.step 4 (.step 6 (.step 18 (.step 12 (.close 21)))))) (.step 4 (.step 6 (.step 4 (.close 22)))))) (.step 10 (.step 69 (.step 4 (.step 55 (.split 26 0 (.step 10 (.step 4 (.step 6 (.step 4 (.close 9))))) (.step 4 (.close 6)))))))) (.step 4 (.step 6 (.step 40 (.step 55 (.step 30 (.step 4 (.step 12 (.step 4 (.close 32))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1532495540865888858358347027150309183618739123257344001, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826558833782580993065735802847148114945⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.step 4 (.split 31 0 (.split 41 0 (.split 33 0 (.split 53 0 (.step 4 (.step 10 (.step 18 (.step 12 (.close 21))))) (.step 4 (.close 6))) (.step 4 (.step 6 (.step 4 (.step 9 (.close 8)))))) (.step 4 (.step 6 (.step 40 (.step 4 (.step 22 (.step 4 (.close 8)))))))) (.step 4 (.step 6 (.step 40 (.step 55 (.step 30 (.step 4 (.step 12 (.step 4 (.close 32))))))))))) (.step 6 (.step 4 (.close 10)))) (.step 6 (.split 32 0 (.split 35 0 (.step 23 (.step 69 (.step 4 (.step 9 (.step 4 (.step 12 (.close 18))))))) (.step 9 (.step 4 (.step 21 (.close 4))))) (.step 4 (.step 10 (.step 4 (.step 18 (.step 16 (.close 21))))))))) (.step 4 (.step 6 (.step 23 (.step 4 (.step 8 (.step 21 (.close 16)))))))) (.step 6 (.split 31 0 (.split 32 0 (.step 51 (.split 29 0 (.step 4 (.step 23 (.step 4 (.step 9 (.step 21 (.close 4)))))) (.step 32 (.step 4 (.step 23 (.step 4 (.step 9 (.step 4 (.close 12))))))))) (.step 4 (.step 10 (.step 21 (.close 4))))) (.step 23 (.split 32 0 (.split 35 0 (.step 51 (.split 44 0 (.step 4 (.step 16 (.step 18 (.close 21)))) (.step 9 (.close 8)))) (.step 4 (.step 9 (.close 21)))) (.step 4 (.step 10 (.step 16 (.step 18 (.close 21)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1073741825, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692826558833782580993065735802847148114945⟩
def references : Fin 2 → Box := ![Part15.root, Part16.root]
def proof : Chunks.Proof 2 := (.split 18 0 (.split 19 0 (.split 21 0 (.reuse 0) (.run (.step 4 (.step 18 (.step 4 (.step 40 (.split 23 0 (.split 33 0 (.split 26 0 (.split 27 0 (.step 4 (.step 8 (.close 9))) (.step 4 (.close 6))) (.step 4 (.close 6))) (.step 6 (.step 40 (.step 4 (.step 8 (.close 32)))))) (.step 6 (.step 23 (.step 4 (.step 8 (.step 16 (.close 21))))))))))))) (.run (.split 21 0 (.split 23 0 (.split 33 0 (.split 44 0 (.step 4 (.split 31 0 (.step 51 (.step 4 (.step 6 (.close 12)))) (.step 4 (.step 6 (.step 4 (.step 22 (.step 4 (.close 16)))))))) (.step 10 (.step 51 (.step 4 (.step 6 (.step 4 (.close 9))))))) (.step 4 (.step 6 (.step 40 (.close 51))))) (.step 6 (.split 32 0 (.step 51 (.step 4 (.step 23 (.step 4 (.step 9 (.step 23 (.step 18 (.step 12 (.close 21))))))))) (.step 4 (.step 10 (.step 4 (.step 18 (.step 16 (.close 21))))))))) (.step 4 (.step 6 (.step 23 (.step 4 (.step 8 (.step 22 (.close 16)))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1329227995784915872903807061354086401, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359852580542645546742531510764545⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 1 0 (.split 23 0 (.split 27 0 (.split 26 0 (.step 12 (.step 55 (.step 71 (.split 33 0 (.step 4 (.step 9 (.step 4 (.close 15)))) (.step 4 (.step 51 (.step 4 (.close 9)))))))) (.step 6 (.step 4 (.step 10 (.step 12 (.close 15)))))) (.step 4 (.step 6 (.close 4)))) (.step 6 (.step 12 (.split 32 0 (.step 23 (.step 55 (.step 9 (.step 4 (.step 15 (.close 21)))))) (.step 4 (.close 9)))))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.step 9 (.step 15 (.step 21 (.close 22))))))) (.step 6 (.step 12 (.split 23 0 (.split 31 0 (.step 51 (.step 4 (.step 9 (.step 15 (.step 4 (.close 21)))))) (.step 4 (.step 9 (.close 15)))) (.step 9 (.step 22 (.step 4 (.step 15 (.step 4 (.close 18)))))))))) (.step 6 (.step 12 (.split 19 0 (.split 23 0 (.split 31 0 (.split 32 0 (.step 23 (.step 55 (.step 9 (.step 4 (.step 15 (.close 21)))))) (.step 4 (.close 9))) (.step 4 (.step 9 (.close 15)))) (.step 9 (.step 21 (.step 4 (.step 15 (.step 4 (.close 22))))))) (.step 9 (.step 21 (.step 4 (.step 22 (.step 4 (.close 15)))))))))) (.step 4 (.step 12 (.step 31 (.step 4 (.step 6 (.step 8 (.close 14)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1073741825, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359852580542645546742531510764545⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 12 0 (.split 11 0 (.reuse 0) (.run (.split 1 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.step 18 (.split 27 0 (.split 33 0 (.split 53 0 (.step 12 (.step 4 (.step 8 (.close 14)))) (.step 8 (.step 12 (.step 4 (.step 14 (.close 18)))))) (.step 12 (.step 43 (.step 8 (.step 14 (.close 18)))))) (.step 12 (.step 18 (.close 6))))) (.step 4 (.close 6))) (.step 4 (.step 12 (.step 40 (.step 68 (.step 4 (.close 6))))))) (.step 4 (.step 6 (.step 8 (.step 12 (.step 14 (.step 18 (.close 21)))))))) (.step 4 (.step 12 (.step 24 (.step 51 (.step 4 (.step 6 (.close 8)))))))) (.step 4 (.step 12 (.step 24 (.split 19 0 (.step 68 (.step 4 (.step 6 (.close 9)))) (.step 6 (.step 23 (.step 4 (.step 8 (.step 14 (.close 21))))))))))) (.step 4 (.step 6 (.step 8 (.step 12 (.close 14)))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1237940039285380275972866049, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195691172757316434803968200486756668623921402443999863636993⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 21 0 (.split 23 0 (.split 26 0 (.split 29 0 (.split 41 0 (.split 33 0 (.split 27 0 (.step 71 (.step 4 (.step 12 (.step 4 (.close 8))))) (.step 6 (.close 4))) (.step 6 (.step 12 (.step 4 (.step 8 (.step 14 (.close 18))))))) (.step 6 (.step 12 (.step 69 (.step 4 (.step 8 (.close 14))))))) (.step 6 (.step 12 (.step 32 (.step 4 (.step 8 (.close 14))))))) (.step 6 (.step 4 (.close 12)))) (.step 6 (.step 12 (.step 4 (.split 32 0 (.step 55 (.step 69 (.step 4 (.step 9 (.close 18))))) (.step 4 (.step 8 (.step 14 (.close 18))))))))) (.step 6 (.step 12 (.step 4 (.step 40 (.split 32 0 (.split 35 0 (.step 43 (.close 4)) (.step 4 (.step 9 (.step 15 (.close 21))))) (.step 4 (.step 8 (.step 14 (.close 21)))))))))) (.step 6 (.step 12 (.split 32 0 (.split 35 0 (.step 51 (.step 4 (.step 51 (.step 4 (.step 9 (.close 8)))))) (.step 23 (.step 32 (.step 4 (.step 9 (.step 4 (.step 15 (.step 4 (.close 18))))))))) (.step 4 (.step 32 (.step 4 (.step 8 (.step 14 (.step 18 (.close 21))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1073741825, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685985044311016735745⟩
def references : Fin 2 → Box := ![Part19.root, Part20.root]
def proof : Chunks.Proof 2 := (.split 6 0 (.split 9 0 (.reuse 0) (.split 11 0 (.split 12 0 (.split 18 0 (.reuse 1) (.run (.step 6 (.step 12 (.split 32 0 (.split 35 0 (.split 47 0 (.split 64 0 (.split 19 0 (.split 21 0 (.step 4 (.step 55 (.step 4 (.step 9 (.close 8))))) (.step 23 (.step 4 (.step 8 (.close 14))))) (.split 1 0 (.step 51 (.split 41 0 (.step 23 (.step 4 (.step 9 (.close 8)))) (.step 23 (.step 26 (.close 4))))) (.step 9 (.step 4 (.close 14))))) (.step 23 (.step 32 (.step 63 (.step 23 (.close 4)))))) (.step 24 (.step 32 (.step 55 (.step 48 (.step 58 (.step 24 (.close 4)))))))) (.step 23 (.step 32 (.step 4 (.step 9 (.step 15 (.close 21))))))) (.step 32 (.step 4 (.step 21 (.close 8))))))))) (.run (.step 6 (.step 12 (.close 4))))) (.run (.step 12 (.close 4))))) (.run (.split 12 0 (.split 21 0 (.split 26 0 (.split 32 0 (.split 37 0 (.split 45 0 (.split 54 0 (.split 68 0 (.split 70 0 (.split 1 0 (.step 47 (.split 11 0 (.step 6 (.close 4)) (.step 12 (.step 4 (.close 6))))) (.step 4 (.step 23 (.step 4 (.close 6))))) (.step 4 (.step 6 (.close 4)))) (.step 4 (.step 6 (.close 10)))) (.step 6 (.step 4 (.close 9)))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.close 4)))) (.step 4 (.step 6 (.close 4)))) (.step 6 (.step 4 (.close 10)))) (.step 4 (.step 6 (.close 4)))) (.step 6 (.step 4 (.step 6 (.step 4 (.close 9))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1, 5521043902406090842867833640676237537725116307197237920842821697029259918322350196657057116294352142605259555959194120002925301392556795122361174648492263643195692705252857300692827889359853818482685986170210923578369⟩
def references : Fin 3 → Box := ![Part11.root, Part14.root, Part21.root]
def proof : Chunks.Proof 3 := (.split 3 0 (.split 5 0 (.reuse 0) (.split 6 0 (.reuse 1) (.run (.split 9 0 (.split 11 0 (.split 12 0 (.step 4 (.split 18 0 (.step 47 (.step 4 (.close 8))) (.step 4 (.step 6 (.close 9))))) (.step 24 (.split 29 0 (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 6 (.close 9)))))) (.split 12 0 (.split 29 0 (.split 44 0 (.split 48 0 (.step 4 (.close 6)) (.step 4 (.step 6 (.close 8)))) (.step 4 (.step 6 (.close 8)))) (.step 4 (.step 6 (.close 8)))) (.step 4 (.step 24 (.close 4))))) (.step 4 (.step 6 (.step 31 (.step 12 (.step 31 (.step 4 (.close 8))))))))))) (.split 5 0 (.reuse 2) (.run (.split 6 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 32 0 (.split 37 0 (.split 45 0 (.split 54 0 (.split 68 0 (.split 70 0 (.split 19 0 (.step 47 (.split 33 0 (.split 53 0 (.step 4 (.close 6)) (.step 51 (.step 4 (.close 6)))) (.step 6 (.close 4)))) (.step 6 (.close 4))) (.step 6 (.step 4 (.close 8)))) (.step 4 (.step 6 (.close 8)))) (.step 4 (.step 6 (.close 4)))) (.step 4 (.step 6 (.close 8)))) (.step 4 (.step 6 (.close 4)))) (.step 6 (.step 4 (.close 8)))) (.step 4 (.step 6 (.close 4)))) (.step 4 (.step 6 (.close 4)))) (.step 4 (.step 6 (.close 4)))) (.step 4 (.step 6 (.close 4)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part14.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part22.excludes
end FiveColour.Packed.ProjectedChunks.Case267
