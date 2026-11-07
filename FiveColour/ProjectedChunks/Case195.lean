module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case195
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527932549105291222426537039558082560⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11592783902519016073891, 5789228615351851005602038370335591275294198528381158883517967318771042520589602239994119809768722215152051327244015790705835775921264311184485905152867059912521957706666366336798257069976655305003540165295547166803485524992, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345973337012623795121722220211928750726687227904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 17 0 (.split 30 0 (.split 38 0 (.step 9 (.step 57 (.step 43 (.close 3)))) (.step 38 (.step 3 (.close 5)))) (.step 38 (.step 3 (.close 68)))) (.step 43 (.close 20))) (.step 29 (.step 7 (.close 5)))) (.step 29 (.close 58))) (.split 17 0 (.step 29 (.step 7 (.close 5))) (.step 43 (.close 27)))) (.split 25 0 (.split 17 0 (.split 26 0 (.split 24 0 (.step 43 (.close 67)) (.step 43 (.close 27))) (.step 75 (.close 7))) (.split 24 0 (.split 26 0 (.step 24 (.step 61 (.step 43 (.close 20)))) (.step 7 (.close 19))) (.step 7 (.close 24)))) (.step 75 (.split 17 0 (.step 5 (.close 27)) (.step 7 (.close 4)))))) (.split 17 0 (.split 25 0 (.split 26 0 (.split 22 0 (.split 24 0 (.step 38 (.step 43 (.close 11))) (.step 42 (.close 7))) (.step 24 (.step 42 (.step 7 (.step 38 (.step 24 (.close 19))))))) (.split 22 0 (.step 38 (.close 43)) (.step 7 (.close 24)))) (.step 38 (.split 22 0 (.step 5 (.close 27)) (.step 7 (.close 4))))) (.split 22 0 (.split 24 0 (.split 25 0 (.step 67 (.step 7 (.step 24 (.close 3)))) (.step 7 (.close 4))) (.step 7 (.close 24))) (.step 24 (.step 19 (.step 7 (.step 19 (.close 20)))))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730809198703285668566194320791249281351680⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 52 (.step 5 (.step 9 (.step 15 (.close 43))))) (.step 37 (.step 42 (.close 24)))) (.step 29 (.close 43))) (.step 29 (.step 5 (.close 3)))) (.split 26 0 (.split 30 0 (.step 29 (.close 27)) (.step 42 (.step 7 (.close 15)))) (.step 11 (.close 29)))) (.split 24 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 37 (.step 24 (.close 42))) (.step 24 (.step 33 (.step 25 (.close 24))))) (.step 11 (.step 4 (.step 24 (.close 29))))) (.step 5 (.close 24))) (.step 11 (.step 43 (.close 27))))) (.split 22 0 (.split 24 0 (.split 25 0 (.step 74 (.close 43)) (.step 5 (.close 24))) (.step 11 (.step 43 (.close 27)))) (.step 11 (.step 17 (.step 74 (.step 7 (.close 24))))))) (.split 17 0 (.split 22 0 (.step 67 (.split 24 0 (.step 37 (.step 38 (.step 24 (.step 7 (.close 68))))) (.step 11 (.step 38 (.step 37 (.step 27 (.close 3))))))) (.step 17 (.step 24 (.step 19 (.close 43))))) (.step 24 (.split 22 0 (.step 11 (.step 17 (.step 19 (.close 20)))) (.step 19 (.step 7 (.step 13 (.close 20))))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730809198704553319166422550192745984557056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 52 (.step 43 (.close 3))) (.step 29 (.step 38 (.close 54)))) (.step 15 (.step 43 (.close 15)))) (.step 29 (.close 7))) (.step 29 (.close 7))) (.split 26 0 (.split 30 0 (.step 29 (.close 7)) (.step 7 (.close 19))) (.step 29 (.close 7)))) (.split 24 0 (.split 25 0 (.step 66 (.step 45 (.step 43 (.close 33)))) (.step 7 (.close 3))) (.step 7 (.close 24)))) (.split 22 0 (.split 24 0 (.split 25 0 (.step 66 (.split 26 0 (.step 43 (.close 20)) (.step 7 (.close 19)))) (.step 7 (.close 3))) (.step 7 (.close 24))) (.step 7 (.step 17 (.step 24 (.step 13 (.step 20 (.close 24)))))))) (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 66 (.step 38 (.step 7 (.step 13 (.close 43))))) (.step 7 (.close 3))) (.step 7 (.close 24))) (.step 7 (.step 17 (.step 24 (.step 13 (.step 19 (.close 24))))))) (.step 7 (.step 17 (.step 24 (.step 42 (.step 13 (.step 19 (.close 20))))))))) (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.split 24 0 (.split 25 0 (.step 66 (.step 43 (.step 42 (.step 7 (.close 13))))) (.step 15 (.close 3))) (.step 68 (.step 15 (.close 7)))) (.step 17 (.step 66 (.step 7 (.close 13)))))) (.step 17 (.step 15 (.step 66 (.step 7 (.close 13)))))) (.step 17 (.step 24 (.split 17 0 (.step 17 (.step 42 (.step 13 (.close 15)))) (.step 13 (.close 15))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527932549104082295453999806264901632⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 22 0 (.step 29 (.split 30 0 (.split 38 0 (.step 15 (.step 43 (.close 38))) (.step 38 (.step 3 (.close 5)))) (.step 38 (.step 13 (.close 68))))) (.step 75 (.split 25 0 (.split 26 0 (.step 24 (.close 43)) (.step 29 (.close 7))) (.step 9 (.step 4 (.close 29)))))) (.split 25 0 (.step 9 (.step 29 (.close 7))) (.step 29 (.close 3)))) (.split 24 0 (.split 30 0 (.split 26 0 (.split 17 0 (.step 29 (.step 38 (.step 13 (.close 24)))) (.step 17 (.step 4 (.close 24)))) (.step 29 (.close 7))) (.step 24 (.close 38))) (.step 24 (.close 29)))) (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.split 24 0 (.step 29 (.step 15 (.close 5))) (.step 9 (.close 29))) (.step 17 (.step 4 (.close 24))))) (.step 23 (.step 17 (.close 13)))) (.step 24 (.step 4 (.close 17))))))) (.split 12 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.step 15 (.split 24 0 (.split 25 0 (.split 22 0 (.step 29 (.step 43 (.close 13))) (.step 17 (.close 13))) (.step 9 (.step 4 (.close 7)))) (.step 9 (.step 17 (.close 29))))) (.step 24 (.close 13))) (.step 24 (.close 13))) (.step 15 (.close 13))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527931281454690993044212938736402432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.split 22 0 (.step 9 (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 29 (.close 43))) (.step 29 (.step 38 (.step 9 (.close 3))))) (.step 29 (.step 43 (.step 5 (.step 9 (.close 7)))))) (.split 43 0 (.step 29 (.close 7)) (.step 9 (.close 11)))) (.split 22 0 (.split 24 0 (.split 34 0 (.step 74 (.split 35 0 (.step 7 (.close 9)) (.step 24 (.step 4 (.close 9))))) (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 7 (.close 9)))) (.split 17 0 (.split 22 0 (.step 67 (.split 24 0 (.step 38 (.step 7 (.close 9))) (.step 11 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 11)))) (.split 16 0 (.split 24 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 17 0 (.split 34 0 (.split 22 0 (.split 35 0 (.step 9 (.close 5)) (.step 9 (.close 11))) (.step 11 (.close 3))) (.step 17 (.close 37))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.split 43 0 (.split 17 0 (.step 67 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 11 (.close 29))) (.step 11 (.close 27))) (.step 11 (.close 7)))) (.split 14 0 (.split 24 0 (.split 16 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 9 (.close 7)) (.step 9 (.close 3))) (.step 9 (.close 7))) (.step 9 (.close 29))) (.step 23 (.step 24 (.close 9)))) (.step 9 (.close 29))) (.split 16 0 (.step 9 (.step 17 (.step 9 (.close 5)))) (.step 17 (.close 3))))))
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
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527932549104082296606921310871748608⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 24 0 (.split 22 0 (.step 29 (.split 30 0 (.split 38 0 (.step 9 (.close 3)) (.step 38 (.step 3 (.close 5)))) (.step 38 (.close 7)))) (.step 75 (.split 25 0 (.split 26 0 (.step 7 (.close 9)) (.step 11 (.close 7))) (.step 7 (.close 29))))) (.split 25 0 (.step 9 (.step 29 (.close 7))) (.step 29 (.close 3)))) (.split 24 0 (.split 30 0 (.split 17 0 (.step 29 (.step 38 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 24 (.close 29)))) (.split 16 0 (.split 17 0 (.step 15 (.split 24 0 (.split 22 0 (.step 29 (.split 30 0 (.step 9 (.step 5 (.close 9))) (.step 4 (.step 9 (.close 7))))) (.step 23 (.step 11 (.close 7)))) (.step 9 (.step 11 (.close 9))))) (.step 23 (.step 11 (.close 7)))) (.step 24 (.step 4 (.close 11))))) (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 34 0 (.step 9 (.step 15 (.split 35 0 (.step 7 (.close 9)) (.step 9 (.close 3))))) (.step 15 (.close 4))) (.step 9 (.close 29))) (.step 9 (.close 4))) (.step 9 (.close 29))) (.step 15 (.step 5 (.close 7))))) (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.step 29 (.split 30 0 (.step 9 (.close 3)) (.step 7 (.close 9)))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 12 0 (.step 24 (.step 9 (.close 29))) (.step 4 (.step 9 (.close 7))))) (.step 15 (.close 7)))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527932549105291222426535940046454784⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 3 := (.split 6 0 (.split 8 0 (.reuse 0) (.split 10 0 (.reuse 1) (.run (.split 14 0 (.split 24 0 (.split 26 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 7 (.close 9)) (.step 29 (.step 4 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 17 (.step 4 (.close 9)))) (.step 66 (.split 12 0 (.step 7 (.close 9)) (.step 9 (.close 7))))) (.split 16 0 (.split 17 0 (.step 9 (.split 22 0 (.step 68 (.close 29)) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 17 (.step 15 (.step 66 (.step 7 (.close 9))))))))) (.split 8 0 (.reuse 2) (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 16 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 9 (.close 7)) (.step 9 (.close 3))) (.step 9 (.close 7))) (.step 9 (.close 11))) (.step 23 (.step 11 (.close 7)))) (.step 9 (.close 11))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 11 (.close 3)) (.step 5 (.close 11))) (.step 5 (.close 11))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.step 11 (.close 7)))) (.step 9 (.close 11))) (.split 26 0 (.split 14 0 (.split 16 0 (.step 24 (.step 9 (.close 3))) (.step 7 (.close 9))) (.step 5 (.step 11 (.close 7)))) (.step 4 (.step 9 (.close 7))))))))
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
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345973337012623795121722220211928751826198855680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 24 0 (.split 34 0 (.split 35 0 (.split 26 0 (.split 36 0 (.split 38 0 (.step 68 (.close 3)) (.step 18 (.close 58))) (.step 29 (.step 43 (.close 7)))) (.step 7 (.close 19))) (.step 29 (.step 38 (.step 33 (.close 68))))) (.step 29 (.split 22 0 (.split 30 0 (.step 43 (.step 7 (.close 3))) (.step 7 (.close 19))) (.step 7 (.close 19))))) (.split 43 0 (.step 29 (.close 7)) (.step 7 (.close 9)))) (.split 22 0 (.split 24 0 (.split 34 0 (.split 35 0 (.step 7 (.close 19)) (.step 29 (.step 4 (.close 24)))) (.step 7 (.close 19))) (.step 7 (.close 24))) (.step 7 (.close 19)))) (.split 17 0 (.split 22 0 (.split 24 0 (.split 35 0 (.step 7 (.close 19)) (.step 29 (.close 38))) (.step 7 (.close 24))) (.step 7 (.close 19))) (.step 7 (.close 19)))))
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
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527931281453482067224599409073324032⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 27 (.step 43 (.step 15 (.step 13 (.close 15))))) (.step 29 (.close 43))) (.step 29 (.step 4 (.step 15 (.close 24))))) (.step 29 (.close 37))) (.step 11 (.step 29 (.close 7)))) (.step 11 (.step 24 (.split 24 0 (.split 25 0 (.split 26 0 (.split 34 0 (.step 25 (.close 7)) (.step 7 (.close 17))) (.step 7 (.close 19))) (.step 3 (.close 5))) (.step 7 (.close 24)))))) (.step 11 (.step 24 (.split 24 0 (.split 25 0 (.step 74 (.close 7)) (.step 5 (.close 7))) (.step 7 (.close 24)))))) (.step 11 (.split 24 0 (.split 25 0 (.step 24 (.step 67 (.split 17 0 (.step 7 (.close 15)) (.step 7 (.close 19))))) (.step 5 (.close 7))) (.step 7 (.close 24))))))) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 25 0 (.step 9 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 43 (.step 29 (.step 24 (.step 7 (.close 13))))) (.step 4 (.close 7))) (.step 18 (.step 29 (.step 15 (.step 7 (.close 13)))))) (.step 29 (.step 38 (.close 68)))) (.step 15 (.step 18 (.step 29 (.step 13 (.step 7 (.close 15))))))) (.step 24 (.close 7)))) (.step 29 (.close 3))) (.step 9 (.step 24 (.close 29)))) (.step 24 (.close 7))) (.split 16 0 (.step 24 (.step 9 (.step 15 (.step 29 (.step 13 (.close 15)))))) (.step 13 (.close 15))))))
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
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527932549105291221273615534951235584⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 14 0 (.split 24 0 (.split 26 0 (.split 34 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 7 (.close 13)) (.step 29 (.step 33 (.step 3 (.step 24 (.step 7 (.close 13))))))) (.step 7 (.close 19))) (.step 7 (.close 19))) (.step 7 (.close 19))) (.split 16 0 (.split 17 0 (.step 9 (.step 15 (.step 13 (.close 15)))) (.step 13 (.close 15))) (.step 13 (.close 15)))) (.step 7 (.step 15 (.close 3)))) (.step 7 (.close 24))) (.step 7 (.close 24))) (.split 24 0 (.split 26 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 7 (.close 15))) (.step 7 (.close 15)))))) (.run (.split 14 0 (.split 24 0 (.split 26 0 (.split 34 0 (.split 10 0 (.split 16 0 (.step 9 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 3 (.close 9)))) (.split 10 0 (.split 16 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.split 10 0 (.split 12 0 (.step 11 (.close 7)) (.step 9 (.close 7))) (.step 7 (.close 9)))) (.split 24 0 (.split 10 0 (.split 30 0 (.split 34 0 (.step 9 (.step 11 (.close 3))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 11 (.close 5))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433802953270351418791226765744795345974730810527932549105291222426537039558082560⟩
def references : Fin 2 → Box := ![Part6.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 4 0 (.reuse 0) (.split 6 0 (.reuse 1) (.run (.split 8 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 10 0 (.split 26 0 (.split 30 0 (.step 9 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 29))) (.step 29 (.close 7))) (.split 10 0 (.split 16 0 (.step 24 (.step 9 (.step 11 (.close 7)))) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.split 10 0 (.split 14 0 (.split 16 0 (.step 9 (.close 3)) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case195
