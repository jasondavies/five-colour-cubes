module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case205
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450975262794700797509632⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11592783902519083183027, 5789228615357111141503591527908565328988052238931866842109466783872516018158651860904340855333424994291657941685580562196867513399766593215024954541188249413884004349401981041481010002029536037373500234088386757515328619520, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983158300269420517377986095744054700489476785756438528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 25 0 (.split 24 0 (.split 30 0 (.split 38 0 (.split 39 0 (.step 29 (.step 57 (.step 43 (.step 3 (.close 13))))) (.step 38 (.step 5 (.step 9 (.step 20 (.step 13 (.close 15))))))) (.step 38 (.step 5 (.close 3)))) (.split 34 0 (.split 36 0 (.step 53 (.step 3 (.step 9 (.step 13 (.close 20))))) (.step 38 (.step 3 (.step 9 (.step 20 (.close 13)))))) (.step 38 (.step 43 (.step 9 (.step 3 (.step 13 (.step 15 (.close 33))))))))) (.split 34 0 (.split 30 0 (.step 29 (.step 27 (.close 3))) (.step 42 (.step 7 (.step 4 (.step 9 (.close 20)))))) (.split 36 0 (.step 43 (.step 9 (.step 17 (.step 15 (.step 7 (.close 19)))))) (.step 29 (.step 5 (.close 7)))))) (.split 24 0 (.step 29 (.step 7 (.step 27 (.step 3 (.close 7))))) (.split 30 0 (.split 34 0 (.step 5 (.close 27)) (.step 5 (.step 7 (.step 5 (.close 15))))) (.step 5 (.step 7 (.close 4)))))) (.split 24 0 (.split 25 0 (.split 34 0 (.split 30 0 (.step 43 (.step 11 (.step 19 (.step 20 (.close 38))))) (.step 42 (.step 43 (.step 3 (.step 11 (.step 19 (.step 13 (.step 20 (.close 24))))))))) (.step 43 (.close 3))) (.step 43 (.step 3 (.step 4 (.close 15))))) (.split 30 0 (.step 43 (.step 11 (.close 27))) (.step 7 (.step 19 (.close 20)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684692869144872697588890584624116612988928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 24 0 (.split 30 0 (.step 43 (.step 66 (.step 11 (.step 19 (.close 3))))) (.step 38 (.step 11 (.close 13)))) (.step 42 (.step 29 (.close 7)))) (.step 38 (.split 24 0 (.step 5 (.step 27 (.step 3 (.close 4)))) (.step 7 (.close 4))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 24 (.step 19 (.step 5 (.step 9 (.step 13 (.close 19)))))) (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 24 (.step 33 (.close 24)))) (.step 7 (.close 4))) (.step 7 (.step 19 (.close 20))))) (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 24 (.step 19 (.step 5 (.step 9 (.step 13 (.close 19)))))) (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 24 (.step 33 (.close 20)))) (.step 7 (.close 4))) (.step 7 (.step 19 (.close 20)))) (.step 24 (.step 19 (.step 7 (.step 19 (.step 20 (.close 9)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983158300270814313952894259690400682881517308350562304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 52 (.step 5 (.step 9 (.step 19 (.step 20 (.close 38)))))) (.step 5 (.step 15 (.step 5 (.step 23 (.step 3 (.close 5))))))) (.split 35 0 (.step 43 (.step 9 (.step 15 (.close 17)))) (.step 29 (.step 38 (.step 5 (.step 15 (.close 17))))))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.step 15 (.close 3))))) (.step 37 (.step 9 (.close 17))))) (.split 30 0 (.step 29 (.step 5 (.close 3))) (.step 5 (.step 37 (.step 3 (.step 4 (.step 3 (.close 5)))))))) (.split 30 0 (.split 25 0 (.split 34 0 (.split 39 0 (.step 29 (.step 11 (.step 7 (.close 5)))) (.step 27 (.step 3 (.close 5)))) (.split 36 0 (.step 52 (.close 5)) (.step 5 (.step 7 (.close 17))))) (.split 34 0 (.step 27 (.step 3 (.close 5))) (.step 5 (.close 15)))) (.split 25 0 (.step 42 (.step 43 (.step 11 (.step 17 (.step 7 (.close 15)))))) (.step 5 (.step 3 (.step 7 (.close 15))))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 17 (.step 13 (.step 15 (.close 19)))))) (.step 24 (.step 4 (.step 15 (.step 17 (.close 19)))))) (.step 17 (.step 5 (.step 15 (.step 9 (.close 17)))))) (.step 24 (.step 67 (.step 13 (.step 24 (.close 3)))))) (.step 23 (.step 63 (.step 4 (.step 3 (.close 5)))))) (.split 25 0 (.step 11 (.split 30 0 (.step 68 (.step 17 (.step 4 (.close 27)))) (.step 7 (.step 17 (.step 15 (.close 19)))))) (.step 7 (.step 4 (.close 15)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444053036643934872976664639207112704⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.step 74 (.step 37 (.step 24 (.step 11 (.step 15 (.close 3)))))) (.step 24 (.step 67 (.step 13 (.step 24 (.close 3)))))) (.step 23 (.step 63 (.step 4 (.step 3 (.close 5)))))) (.split 25 0 (.step 11 (.step 61 (.step 17 (.step 29 (.close 7))))) (.step 7 (.step 4 (.close 15))))) (.step 24 (.split 24 0 (.split 25 0 (.step 11 (.step 17 (.step 20 (.step 3 (.step 13 (.close 19)))))) (.step 7 (.step 4 (.close 13)))) (.step 7 (.step 17 (.step 18 (.step 15 (.close 19)))))))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 67 (.split 30 0 (.step 37 (.step 24 (.step 11 (.step 15 (.close 3))))) (.step 24 (.step 42 (.close 3))))) (.step 23 (.step 38 (.step 24 (.step 3 (.close 5)))))) (.split 35 0 (.split 43 0 (.step 67 (.split 49 0 (.step 7 (.step 4 (.close 15))) (.step 17 (.step 3 (.close 5))))) (.step 7 (.step 9 (.close 11)))) (.step 17 (.step 11 (.step 24 (.step 4 (.step 27 (.close 7)))))))) (.step 24 (.split 24 0 (.step 19 (.step 7 (.step 11 (.step 13 (.step 5 (.step 17 (.step 19 (.close 20)))))))) (.step 7 (.step 17 (.step 18 (.step 15 (.close 19)))))))) (.split 22 0 (.step 24 (.split 24 0 (.step 19 (.step 7 (.step 11 (.step 13 (.step 5 (.step 17 (.step 19 (.close 20)))))))) (.step 7 (.step 17 (.step 18 (.step 15 (.close 19))))))) (.step 19 (.step 20 (.step 7 (.step 5 (.step 11 (.step 13 (.close 17)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684694198372868482504763488431176893333504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 24 0 (.split 25 0 (.split 22 0 (.step 29 (.split 30 0 (.split 38 0 (.step 15 (.step 57 (.step 43 (.step 3 (.step 13 (.close 17)))))) (.step 38 (.step 5 (.step 3 (.close 15))))) (.step 38 (.step 15 (.step 3 (.step 13 (.close 20))))))) (.step 75 (.split 34 0 (.step 43 (.step 9 (.step 15 (.step 24 (.step 13 (.step 4 (.step 19 (.close 20)))))))) (.step 15 (.step 13 (.step 4 (.step 9 (.step 15 (.close 19))))))))) (.step 9 (.step 29 (.close 3)))) (.split 25 0 (.step 9 (.step 29 (.step 3 (.close 7)))) (.step 29 (.close 3)))) (.split 24 0 (.split 22 0 (.split 25 0 (.split 30 0 (.step 29 (.step 66 (.step 24 (.step 3 (.close 4))))) (.step 18 (.step 24 (.step 9 (.step 13 (.close 15)))))) (.step 9 (.step 4 (.step 5 (.close 15))))) (.step 24 (.close 4))) (.step 24 (.step 29 (.step 3 (.close 7)))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 9 (.step 38 (.step 4 (.step 15 (.step 13 (.close 19))))))) (.step 18 (.step 24 (.step 9 (.close 13))))) (.step 38 (.step 24 (.step 9 (.step 5 (.step 13 (.close 15))))))) (.step 24 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 38 (.step 23 (.step 3 (.step 4 (.step 3 (.close 15))))))) (.step 24 (.step 29 (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773281032428850745880471699487457280⟩
def references : Fin 4 → Box := ![Part0.root, Part1.root, Part3.root, Part4.root]
def proof : Chunks.Proof 4 := (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.step 43 (.step 66 (.step 11 (.step 19 (.step 3 (.step 19 (.close 20))))))) (.split 34 0 (.step 42 (.step 43 (.step 3 (.step 11 (.step 19 (.step 13 (.close 20))))))) (.step 33 (.step 38 (.step 24 (.step 4 (.close 9))))))) (.step 43 (.step 3 (.step 4 (.close 15))))) (.split 30 0 (.step 43 (.step 11 (.close 27))) (.step 7 (.step 19 (.close 20))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 24 (.step 20 (.step 24 (.step 11 (.step 13 (.step 3 (.close 19))))))) (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 24 (.step 33 (.close 20)))) (.step 7 (.close 4))) (.step 7 (.step 19 (.close 20))))))) (.reuse 1)) (.reuse 2)) (.split 14 0 (.reuse 3) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 25 0 (.split 30 0 (.step 29 (.step 15 (.close 5))) (.step 38 (.step 3 (.step 9 (.close 13))))) (.step 5 (.step 9 (.step 4 (.step 5 (.close 15)))))) (.step 9 (.step 29 (.step 3 (.close 7)))))) (.step 24 (.step 4 (.step 15 (.step 7 (.close 13)))))) (.step 24 (.step 4 (.step 15 (.step 7 (.close 13)))))) (.step 24 (.split 17 0 (.step 24 (.step 4 (.step 15 (.step 7 (.close 13))))) (.step 13 (.close 17))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983158300269420517377987363394654928718878282459643904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 52 (.step 3 (.step 9 (.close 19)))) (.step 43 (.step 29 (.step 18 (.close 13))))) (.step 15 (.step 43 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 33 (.close 3))) (.step 33 (.step 13 (.step 3 (.step 9 (.step 19 (.close 20))))))) (.step 38 (.step 9 (.close 13)))) (.step 15 (.step 33 (.step 13 (.step 3 (.close 9))))))) (.split 34 0 (.split 30 0 (.step 29 (.close 7)) (.step 7 (.close 3))) (.step 7 (.step 3 (.step 5 (.step 3 (.step 7 (.close 15)))))))) (.split 25 0 (.split 30 0 (.split 34 0 (.step 43 (.step 27 (.close 7))) (.step 7 (.step 5 (.step 7 (.close 15))))) (.step 7 (.step 19 (.close 20)))) (.step 5 (.step 7 (.close 4))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 13))) (.step 42 (.step 4 (.step 24 (.close 9))))) (.step 15 (.step 17 (.step 4 (.step 9 (.close 5)))))) (.step 33 (.split 34 0 (.split 35 0 (.step 33 (.step 13 (.close 24))) (.step 33 (.close 13))) (.step 13 (.step 15 (.step 17 (.step 4 (.close 9)))))))) (.step 5 (.step 7 (.close 3)))) (.step 7 (.step 19 (.close 20))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684692869146140348189118814025613316194304⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 13))) (.step 42 (.step 4 (.step 24 (.close 9))))) (.step 15 (.step 17 (.step 4 (.step 9 (.close 5)))))) (.step 33 (.split 34 0 (.split 35 0 (.step 33 (.step 13 (.step 20 (.close 3)))) (.step 33 (.close 13))) (.step 13 (.step 15 (.step 17 (.step 4 (.close 9)))))))) (.step 5 (.step 7 (.close 3)))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 17 (.step 24 (.split 35 0 (.step 13 (.step 20 (.close 24))) (.step 19 (.step 13 (.step 20 (.step 3 (.close 4)))))))))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 13))) (.step 38 (.step 9 (.close 13)))) (.step 15 (.step 17 (.step 4 (.step 9 (.close 5)))))) (.step 33 (.split 34 0 (.step 42 (.step 13 (.step 4 (.step 24 (.close 9))))) (.step 13 (.step 15 (.step 17 (.step 4 (.close 9)))))))) (.step 5 (.step 7 (.close 3)))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 17 (.step 24 (.step 42 (.step 13 (.step 38 (.step 24 (.step 3 (.step 11 (.close 19))))))))))) (.step 7 (.step 24 (.split 34 0 (.split 35 0 (.split 30 0 (.step 20 (.step 13 (.close 19))) (.step 13 (.step 20 (.step 19 (.close 3))))) (.step 19 (.step 4 (.close 9)))) (.step 13 (.step 14 (.close 17)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444054304294535101206066135910318080⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 25 0 (.split 30 0 (.step 66 (.step 43 (.close 11))) (.split 35 0 (.step 13 (.step 3 (.step 9 (.close 15)))) (.step 3 (.step 15 (.close 13))))) (.step 5 (.step 15 (.close 3)))) (.split 30 0 (.step 68 (.step 15 (.step 3 (.close 7)))) (.step 7 (.step 15 (.close 17)))))) (.step 24 (.split 24 0 (.split 25 0 (.step 17 (.step 5 (.step 9 (.close 13)))) (.step 3 (.step 5 (.close 7)))) (.step 7 (.step 15 (.close 17)))))) (.split 22 0 (.step 24 (.split 24 0 (.split 25 0 (.step 17 (.step 5 (.step 9 (.close 13)))) (.step 3 (.step 5 (.close 7)))) (.step 7 (.step 15 (.close 17))))) (.step 7 (.step 13 (.close 15))))) (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.split 25 0 (.step 17 (.step 5 (.step 9 (.close 13)))) (.step 3 (.step 5 (.close 7)))) (.step 7 (.step 15 (.close 17))))) (.step 7 (.step 13 (.close 15)))) (.step 7 (.step 13 (.step 15 (.close 17))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684692869144872697588891737545621219835904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 24 0 (.split 25 0 (.split 22 0 (.step 29 (.split 30 0 (.split 38 0 (.step 9 (.step 3 (.close 5))) (.step 38 (.step 5 (.step 3 (.close 9))))) (.step 38 (.step 7 (.step 4 (.close 9)))))) (.step 75 (.split 34 0 (.step 43 (.step 9 (.close 3))) (.step 7 (.close 9))))) (.step 9 (.step 5 (.close 15)))) (.split 25 0 (.step 9 (.step 29 (.step 3 (.close 7)))) (.step 29 (.close 3)))) (.split 24 0 (.split 22 0 (.split 25 0 (.split 30 0 (.step 29 (.step 68 (.step 74 (.step 43 (.step 4 (.close 9)))))) (.step 7 (.close 9))) (.step 7 (.step 4 (.step 5 (.step 9 (.close 15)))))) (.step 7 (.close 9))) (.step 24 (.step 29 (.step 3 (.close 7)))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 24 (.step 9 (.step 4 (.step 9 (.close 7))))) (.step 7 (.close 9))) (.step 7 (.step 15 (.step 5 (.step 7 (.close 9)))))) (.step 7 (.close 9))) (.step 7 (.step 4 (.step 5 (.step 9 (.close 15)))))) (.step 24 (.step 29 (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773281032428850747033393204094304256⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 25 0 (.split 34 0 (.split 35 0 (.step 9 (.step 5 (.step 7 (.close 9)))) (.step 38 (.step 9 (.close 3)))) (.split 30 0 (.step 29 (.step 43 (.step 5 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 9 (.step 3 (.close 5)))) (.step 9 (.step 29 (.step 3 (.close 7)))))) (.step 24 (.step 4 (.close 11)))) (.step 24 (.step 4 (.close 11)))) (.step 24 (.split 30 0 (.step 24 (.step 4 (.close 11))) (.step 3 (.step 7 (.step 9 (.close 11))))))))) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 25 0 (.split 34 0 (.step 9 (.step 15 (.split 35 0 (.step 9 (.step 3 (.close 7))) (.step 9 (.close 3))))) (.step 15 (.close 4))) (.step 9 (.step 3 (.close 4)))) (.step 9 (.step 5 (.close 7)))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.step 9 (.split 35 0 (.step 24 (.close 9)) (.step 9 (.step 3 (.close 7))))) (.step 7 (.step 9 (.step 3 (.close 15))))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.close 9))) (.step 4 (.step 9 (.step 7 (.close 11)))))) (.split 24 0 (.split 30 0 (.step 15 (.step 5 (.close 7))) (.step 4 (.step 9 (.close 15)))) (.step 29 (.close 9))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450975262794700797509632⟩
def references : Fin 3 → Box := ![Part5.root, Part8.root, Part10.root]
def proof : Chunks.Proof 3 := (.split 6 0 (.split 10 0 (.reuse 0) (.split 12 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 25 0 (.split 35 0 (.step 43 (.step 9 (.close 13))) (.step 15 (.step 3 (.close 13)))) (.step 9 (.step 4 (.step 3 (.close 7))))) (.step 9 (.step 29 (.step 3 (.close 7)))))) (.step 24 (.step 7 (.step 4 (.step 9 (.close 13)))))) (.step 24 (.step 7 (.step 4 (.step 9 (.close 13)))))) (.split 17 0 (.step 24 (.step 7 (.step 4 (.step 9 (.close 13))))) (.step 7 (.step 13 (.step 15 (.close 17)))))) (.split 16 0 (.step 15 (.step 3 (.step 7 (.step 11 (.close 13))))) (.step 3 (.step 13 (.close 15)))))))) (.split 10 0 (.reuse 2) (.run (.split 14 0 (.split 12 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 25 0 (.split 30 0 (.step 29 (.split 38 0 (.step 9 (.step 4 (.step 9 (.close 7)))) (.step 4 (.step 3 (.close 7))))) (.step 7 (.close 9))) (.step 7 (.step 4 (.step 3 (.step 7 (.close 9))))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 16 0 (.step 24 (.step 9 (.step 15 (.step 29 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 9 (.close 11)))))) (.split 24 0 (.split 25 0 (.step 15 (.close 7)) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 9 (.close 7))))) (.split 12 0 (.split 16 0 (.step 15 (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 4 (.step 15 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part8.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part11.excludes
end FiveColour.Packed.ProjectedChunks.Case205
