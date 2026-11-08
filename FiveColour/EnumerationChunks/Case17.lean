module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case17
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450975262794700797509632⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11592783902519083183027, 5789228615357111141503591527908565328988052238931866842109466783872516018158651860904340855333424994291657941685580562196867513399766593215024954541188249413884004349401981041481010002029536037373500234088386757515328619520, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950278075705609889398603484873632838059062823585096546909333582090515488178176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 36 0 (.step 29 (.split 38 0 (.step 55 (.step 53 (.close 13))) (.step 38 (.step 3 (.close 5))))) (.step 57 (.step 3 (.step 9 (.close 13))))) (.split 42 0 (.split 35 0 (.split 63 0 (.step 38 (.step 5 (.step 9 (.close 19)))) (.step 27 (.step 38 (.step 5 (.step 13 (.step 19 (.close 42))))))) (.step 29 (.close 38))) (.step 38 (.step 5 (.step 9 (.step 20 (.step 13 (.step 19 (.close 39))))))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.step 9 (.step 15 (.step 3 (.step 5 (.close 19)))))) (.step 15 (.step 43 (.step 3 (.close 9))))) (.step 43 (.step 15 (.step 9 (.step 3 (.step 18 (.step 22 (.step 3 (.close 33))))))))) (.step 29 (.step 38 (.step 15 (.step 43 (.step 3 (.close 33)))))))) (.split 34 0 (.split 36 0 (.split 35 0 (.step 53 (.step 38 (.step 3 (.step 9 (.close 13))))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 43 (.step 9 (.step 3 (.step 13 (.close 33))))))) (.step 38 (.step 43 (.step 15 (.step 9 (.step 18 (.close 33)))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 55 (.step 3 (.step 5 (.close 7)))) (.step 29 (.close 3))) (.step 29 (.close 5))) (.step 29 (.step 5 (.close 7)))) (.step 38 (.split 34 0 (.step 58 (.step 5 (.step 24 (.close 3)))) (.step 7 (.step 5 (.step 3 (.step 7 (.close 15))))))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842552674667782933068171133580977578651068993422528291703696716780797952⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 24 0 (.reuse 0) (.run (.split 25 0 (.split 34 0 (.split 30 0 (.split 42 0 (.split 39 0 (.step 29 (.step 7 (.close 11))) (.step 42 (.close 27))) (.split 36 0 (.step 62 (.step 5 (.step 9 (.step 27 (.close 7))))) (.step 43 (.step 7 (.close 27))))) (.step 42 (.split 35 0 (.step 42 (.step 43 (.step 11 (.step 24 (.step 20 (.close 27)))))) (.step 29 (.step 3 (.close 7)))))) (.split 30 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 29 (.step 5 (.close 7))) (.step 7 (.step 5 (.step 15 (.step 17 (.close 27)))))) (.step 5 (.step 7 (.step 5 (.close 15))))) (.split 35 0 (.step 43 (.step 7 (.close 15))) (.step 29 (.close 7)))) (.step 7 (.step 29 (.close 5))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 27 (.step 3 (.close 5))) (.step 4 (.step 5 (.step 3 (.close 19))))) (.step 5 (.step 7 (.step 4 (.close 9))))) (.split 38 0 (.step 5 (.step 27 (.close 3))) (.step 3 (.step 5 (.close 21))))) (.step 7 (.step 29 (.close 5)))) (.step 5 (.step 7 (.step 4 (.close 19))))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842552674667782933069667711257604423239309566691229765515824391704805376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.split 36 0 (.step 42 (.step 4 (.step 9 (.step 19 (.step 13 (.close 20)))))) (.step 38 (.step 24 (.step 3 (.close 4)))))) (.step 43 (.step 3 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.step 13 (.step 19 (.close 20)))))))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.step 17 (.close 24)))) (.step 33 (.step 37 (.step 33 (.step 20 (.close 4)))))) (.step 4 (.step 33 (.step 13 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 43 (.step 3 (.step 5 (.close 7)))) (.step 5 (.step 7 (.close 3)))) (.step 38 (.step 5 (.step 29 (.close 3))))) (.step 7 (.step 29 (.close 5))))) (.split 30 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 29 (.step 7 (.step 17 (.close 19)))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 9 (.close 11)))) (.step 43 (.step 9 (.close 27)))) (.step 7 (.step 24 (.close 19))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984654877946047361966226669012756174301604460680445952⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 25 0 (.split 34 0 (.split 30 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.step 75 (.step 5 (.step 9 (.step 19 (.close 13)))))) (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 24)))))) (.step 42 (.close 3)))) (.step 75 (.split 35 0 (.step 43 (.step 5 (.step 17 (.close 24)))) (.step 38 (.step 43 (.close 3)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 43 (.step 3 (.step 5 (.close 7)))) (.step 5 (.step 7 (.close 3)))) (.step 38 (.step 5 (.step 29 (.close 3))))) (.step 7 (.step 29 (.close 5))))) (.split 30 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 29 (.step 7 (.step 17 (.close 19)))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 9 (.close 11)))) (.step 43 (.step 9 (.close 27)))) (.step 7 (.step 24 (.close 19))))))) (.split 22 0 (.reuse 1) (.run (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.close 20)))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 43 (.step 3 (.close 15)))))) (.step 24 (.step 33 (.split 34 0 (.step 61 (.step 33 (.close 20))) (.step 17 (.step 24 (.step 3 (.close 20)))))))) (.step 7 (.step 4 (.close 13)))) (.step 7 (.step 24 (.step 27 (.close 3))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983159761771057848280904299428887416772496441688981504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 43 (.close 3)))) (.split 39 0 (.step 38 (.step 11 (.close 13))) (.step 24 (.close 42)))) (.step 38 (.split 34 0 (.split 36 0 (.step 43 (.step 3 (.step 5 (.close 7)))) (.step 5 (.step 7 (.close 3)))) (.step 7 (.step 5 (.step 3 (.close 15))))))) (.split 30 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 29 (.step 7 (.step 17 (.close 19)))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 9 (.close 11)))) (.step 43 (.step 9 (.close 27)))) (.step 7 (.step 24 (.close 19))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.step 19 (.close 3))))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 38 (.step 3 (.step 19 (.close 15))))))) (.step 24 (.step 33 (.step 42 (.step 4 (.step 11 (.step 19 (.close 15)))))))) (.step 7 (.step 4 (.close 13)))) (.step 7 (.step 24 (.step 19 (.step 4 (.step 19 (.close 20)))))))))
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
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950278075705609889398603484873632839452859398493260493255315974131038082301952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 52 (.step 27 (.step 5 (.step 19 (.step 20 (.close 38)))))) (.step 42 (.step 9 (.step 15 (.step 5 (.step 17 (.close 19))))))) (.split 35 0 (.split 43 0 (.step 57 (.step 58 (.step 15 (.step 17 (.step 19 (.close 20)))))) (.step 15 (.step 9 (.step 5 (.step 9 (.close 11)))))) (.step 38 (.step 15 (.step 29 (.step 5 (.step 20 (.close 17)))))))) (.split 35 0 (.split 36 0 (.step 52 (.close 5)) (.step 43 (.step 5 (.step 15 (.step 17 (.close 9)))))) (.step 38 (.step 29 (.step 37 (.step 15 (.close 17))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.step 24 (.step 15 (.close 13)))))) (.step 43 (.step 5 (.step 15 (.close 24))))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.step 15 (.step 17 (.close 9))))) (.step 37 (.step 5 (.step 9 (.close 11))))) (.step 3 (.step 38 (.close 9)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 27 (.close 3)) (.step 5 (.step 15 (.step 9 (.step 4 (.step 5 (.step 17 (.close 21)))))))) (.split 35 0 (.step 5 (.step 9 (.step 5 (.close 15)))) (.step 3 (.step 5 (.close 15))))) (.split 35 0 (.split 36 0 (.step 5 (.step 9 (.step 5 (.close 15)))) (.step 5 (.step 7 (.step 5 (.close 15))))) (.step 3 (.step 5 (.step 15 (.step 16 (.close 28))))))) (.step 5 (.split 34 0 (.step 43 (.step 5 (.step 3 (.step 11 (.step 3 (.close 15)))))) (.step 3 (.step 5 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1684996666696914987166689836735301825266267872391177820592643506176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983158300270814313952894259690400682881517308350562304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.step 11 (.step 17 (.step 13 (.step 15 (.close 19))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.step 15 (.close 19))))))) (.step 24 (.step 4 (.step 17 (.step 38 (.step 13 (.step 15 (.close 19)))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 5 (.step 13 (.step 20 (.step 11 (.step 17 (.step 19 (.close 24)))))))) (.step 3 (.step 19 (.step 24 (.close 13))))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.step 75 (.split 34 0 (.step 24 (.step 4 (.step 17 (.step 3 (.close 5))))) (.step 3 (.close 5)))) (.step 3 (.step 5 (.close 7))))) (.split 30 0 (.split 35 0 (.split 43 0 (.split 25 0 (.split 34 0 (.split 39 0 (.step 68 (.step 17 (.step 4 (.step 15 (.step 7 (.close 20)))))) (.step 27 (.close 3))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 4 (.step 17 (.step 3 (.step 14 (.close 15))))))) (.step 7 (.close 11))) (.step 42 (.step 17 (.step 11 (.step 4 (.step 15 (.step 7 (.close 19)))))))) (.step 7 (.step 17 (.step 24 (.close 19)))))))
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
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984654877947441158541134832959102156693644983274569728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 61 (.step 68 (.step 4 (.step 11 (.close 15))))) (.step 24 (.step 4 (.step 17 (.step 38 (.step 13 (.step 15 (.close 19)))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 67 (.step 13 (.step 20 (.close 3))))) (.step 3 (.step 19 (.step 20 (.step 9 (.close 13)))))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.split 34 0 (.step 24 (.step 4 (.step 17 (.step 3 (.close 5))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 7))))) (.split 30 0 (.split 35 0 (.split 43 0 (.split 25 0 (.step 61 (.step 17 (.step 24 (.step 15 (.step 7 (.step 4 (.close 15))))))) (.step 7 (.step 4 (.step 17 (.step 3 (.step 14 (.close 15))))))) (.step 7 (.close 11))) (.step 42 (.step 17 (.step 11 (.step 4 (.step 15 (.step 7 (.close 19)))))))) (.step 7 (.step 17 (.step 24 (.close 19)))))) (.split 24 0 (.split 25 0 (.step 24 (.split 30 0 (.step 11 (.step 17 (.step 74 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 20 (.step 11 (.step 17 (.step 3 (.close 19)))))))) (.step 7 (.step 4 (.step 14 (.step 3 (.step 7 (.close 17))))))) (.step 7 (.step 17 (.step 24 (.step 29 (.step 18 (.step 7 (.close 19))))))))))
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
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983159761772451644855812463375233399164536964283105280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 68 (.step 4 (.step 11 (.close 15))))) (.step 24 (.step 4 (.step 17 (.close 38))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.step 42 (.step 3 (.close 13))))) (.split 30 0 (.split 34 0 (.step 24 (.step 4 (.step 17 (.step 3 (.close 5))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 7))))) (.split 30 0 (.split 35 0 (.split 43 0 (.split 25 0 (.split 49 0 (.step 67 (.step 7 (.step 4 (.close 15)))) (.step 17 (.step 3 (.close 5)))) (.step 7 (.step 4 (.step 17 (.step 3 (.step 14 (.close 15))))))) (.step 7 (.close 11))) (.step 42 (.step 17 (.step 11 (.step 4 (.step 15 (.step 7 (.close 19)))))))) (.step 7 (.step 17 (.step 24 (.close 19)))))) (.split 24 0 (.split 25 0 (.step 24 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 3 (.step 13 (.close 20)))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.close 20)))))))) (.step 7 (.step 4 (.step 14 (.step 3 (.step 7 (.close 17))))))) (.step 7 (.step 17 (.step 24 (.step 19 (.step 4 (.step 15 (.close 19))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444053036643934872976664639207112704⟩
def references : Fin 4 → Box := ![Part5.root, Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 4 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.reuse 0) (.run (.split 30 0 (.split 35 0 (.split 43 0 (.split 25 0 (.split 39 0 (.step 29 (.step 52 (.step 7 (.step 5 (.close 15))))) (.split 49 0 (.step 29 (.step 27 (.step 3 (.close 5)))) (.step 27 (.close 5)))) (.split 34 0 (.step 27 (.step 3 (.close 5))) (.step 5 (.step 15 (.close 17))))) (.split 25 0 (.step 52 (.step 11 (.step 5 (.close 7)))) (.step 5 (.step 7 (.close 9))))) (.split 43 0 (.step 29 (.step 3 (.step 7 (.step 15 (.close 17))))) (.step 5 (.step 9 (.step 7 (.close 11)))))) (.split 35 0 (.split 43 0 (.split 51 0 (.step 67 (.step 24 (.step 5 (.step 17 (.step 7 (.close 15)))))) (.step 7 (.step 17 (.step 24 (.close 19))))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.close 42)))))) (.reuse 1)) (.reuse 2)) (.split 17 0 (.reuse 3) (.run (.split 22 0 (.split 24 0 (.split 25 0 (.step 24 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 3 (.step 13 (.close 20)))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.close 20)))))))) (.step 7 (.step 4 (.step 14 (.step 3 (.step 7 (.close 17))))))) (.step 7 (.step 17 (.step 24 (.step 19 (.step 4 (.step 15 (.close 19)))))))) (.split 24 0 (.split 25 0 (.step 19 (.step 20 (.step 11 (.step 13 (.step 5 (.step 17 (.close 19))))))) (.split 35 0 (.step 14 (.step 7 (.step 17 (.step 4 (.step 7 (.close 18)))))) (.step 3 (.step 4 (.step 13 (.step 4 (.close 17))))))) (.step 11 (.step 17 (.step 19 (.step 7 (.close 15))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983158300269420518707214091528970573393283846036783104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 29 (.split 36 0 (.split 30 0 (.step 15 (.step 57 (.step 3 (.close 5)))) (.step 38 (.step 53 (.step 3 (.step 13 (.close 15)))))) (.step 57 (.step 3 (.step 13 (.close 15)))))) (.step 9 (.step 38 (.split 51 0 (.step 43 (.close 15)) (.step 4 (.step 15 (.step 17 (.step 19 (.close 20))))))))) (.split 30 0 (.step 29 (.step 38 (.step 15 (.step 53 (.step 20 (.step 3 (.close 5))))))) (.step 38 (.close 9)))) (.step 15 (.split 30 0 (.step 29 (.step 58 (.step 15 (.close 13)))) (.step 18 (.step 9 (.step 37 (.step 15 (.close 19)))))))) (.step 9 (.step 29 (.close 3)))) (.split 25 0 (.step 9 (.step 29 (.step 3 (.step 7 (.step 17 (.close 27)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 5 (.step 9 (.step 4 (.step 5 (.step 15 (.step 17 (.close 21))))))) (.step 3 (.step 5 (.close 15)))) (.step 4 (.step 21 (.step 23 (.step 5 (.close 15)))))) (.step 4 (.step 5 (.step 15 (.close 21))))) (.step 3 (.close 4))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 62 (.step 29 (.step 43 (.step 4 (.close 15))))) (.step 68 (.step 38 (.step 23 (.step 15 (.step 13 (.step 17 (.close 19)))))))) (.step 15 (.step 18 (.step 9 (.step 24 (.close 13)))))) (.step 24 (.step 4 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33)))))))) (.step 43 (.step 4 (.close 29)))) (.step 43 (.step 9 (.step 17 (.step 24 (.close 27))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1461501637332232146199469748589186826717286629376, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684694198372868482504763488431176893333504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 9 (.step 38 (.step 17 (.step 4 (.step 15 (.close 19)))))) (.step 21 (.step 9 (.step 15 (.step 17 (.step 19 (.step 20 (.close 38)))))))) (.step 38 (.step 18 (.step 9 (.step 15 (.step 17 (.step 19 (.close 20)))))))) (.step 15 (.step 18 (.step 9 (.step 24 (.close 13)))))) (.step 24 (.step 4 (.step 17 (.step 15 (.step 9 (.close 19))))))) (.step 24 (.step 4 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33)))))))) (.step 43 (.step 4 (.step 21 (.step 5 (.step 15 (.step 21 (.close 28)))))))) (.split 25 0 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 9 (.step 17 (.step 24 (.step 15 (.close 27))))))) (.step 4 (.step 17 (.step 24 (.step 9 (.step 27 (.close 7))))))) (.step 3 (.step 7 (.step 15 (.step 7 (.step 15 (.close 17))))))) (.step 3 (.close 4)))) (.split 22 0 (.step 24 (.split 24 0 (.step 24 (.step 37 (.step 4 (.step 9 (.step 15 (.step 13 (.close 19))))))) (.step 7 (.step 17 (.step 15 (.close 19)))))) (.step 24 (.step 3 (.step 7 (.step 19 (.close 15))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1393797904136159731261855295847583948210176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773281032428850745880471699487457280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 15 (.split 34 0 (.split 35 0 (.split 42 0 (.step 52 (.step 5 (.step 9 (.step 13 (.close 15))))) (.step 15 (.step 3 (.close 5)))) (.step 15 (.step 5 (.close 13)))) (.step 15 (.step 29 (.step 5 (.step 13 (.close 17))))))) (.split 30 0 (.step 15 (.step 3 (.step 5 (.close 16)))) (.step 3 (.close 4)))) (.split 25 0 (.step 15 (.step 9 (.split 34 0 (.split 30 0 (.step 29 (.step 3 (.step 7 (.step 15 (.close 17))))) (.step 5 (.step 17 (.close 7)))) (.step 5 (.step 15 (.close 17)))))) (.step 5 (.close 15)))) (.step 24 (.split 24 0 (.split 25 0 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 3 (.close 4))) (.step 17 (.step 7 (.step 4 (.step 9 (.close 15)))))))) (.split 22 0 (.step 24 (.split 24 0 (.split 25 0 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 3 (.close 4))) (.step 17 (.step 7 (.step 4 (.step 9 (.close 15))))))) (.step 13 (.close 17)))) (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.split 25 0 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 3 (.close 4))) (.step 17 (.step 7 (.step 4 (.step 9 (.close 15))))))) (.step 13 (.close 17))) (.step 17 (.step 3 (.step 11 (.close 13)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773281032428850745880471699487457280⟩
def references : Fin 3 → Box := ![Part10.root, Part11.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 24 0 (.split 25 0 (.split 30 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.step 43 (.step 17 (.step 24 (.close 15))))) (.step 18 (.step 9 (.step 15 (.step 17 (.step 20 (.close 19))))))) (.step 68 (.step 38 (.step 23 (.step 15 (.step 13 (.step 17 (.close 19)))))))) (.step 15 (.step 18 (.step 9 (.step 24 (.close 13)))))) (.step 24 (.step 4 (.step 17 (.step 15 (.step 9 (.step 20 (.close 19)))))))) (.step 24 (.step 4 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33)))))))) (.step 43 (.step 4 (.close 29)))) (.split 25 0 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 9 (.step 17 (.step 24 (.step 15 (.close 27))))))) (.step 4 (.step 17 (.step 24 (.step 9 (.step 27 (.close 7))))))) (.step 3 (.step 7 (.step 15 (.step 7 (.step 15 (.close 17))))))) (.step 3 (.close 4)))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950278075705609889398603484873632838059062823586364197509561811492012191383552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 43 (.step 3 (.close 9)))) (.step 43 (.step 11 (.step 19 (.step 20 (.step 19 (.close 38))))))) (.split 36 0 (.split 39 0 (.step 29 (.step 52 (.step 3 (.close 19)))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 29 (.step 3 (.step 24 (.close 13))))))) (.step 15 (.split 35 0 (.step 43 (.close 15)) (.step 15 (.step 3 (.close 17)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 3 (.close 9)))) (.step 42 (.step 3 (.step 13 (.step 9 (.close 20)))))) (.split 39 0 (.split 38 0 (.step 43 (.step 13 (.step 9 (.step 3 (.close 33))))) (.step 13 (.step 18 (.close 33)))) (.step 33 (.step 13 (.close 19))))) (.split 36 0 (.split 38 0 (.step 42 (.step 13 (.step 9 (.step 3 (.close 33))))) (.step 3 (.step 9 (.step 13 (.close 18))))) (.step 33 (.step 13 (.close 19))))) (.step 15 (.step 33 (.split 35 0 (.step 33 (.step 13 (.step 15 (.step 3 (.step 11 (.close 15)))))) (.step 15 (.step 3 (.step 13 (.close 17))))))))) (.split 34 0 (.split 36 0 (.split 30 0 (.step 58 (.step 5 (.step 24 (.close 3)))) (.step 7 (.close 3))) (.step 7 (.step 3 (.step 5 (.step 3 (.step 7 (.close 28))))))) (.step 7 (.step 15 (.step 3 (.close 28)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983158300269420517377987363394654928718878282459643904⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.split 24 0 (.reuse 0) (.run (.split 34 0 (.split 25 0 (.split 30 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 29 (.step 7 (.close 19))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 9 (.close 11)))) (.step 42 (.step 29 (.step 3 (.close 7))))) (.step 7 (.step 24 (.close 19)))) (.step 5 (.step 7 (.step 4 (.close 19))))) (.step 7 (.step 15 (.step 5 (.step 7 (.step 15 (.close 17))))))))) (.run (.split 24 0 (.split 30 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 24)))))) (.step 75 (.step 42 (.step 43 (.close 3))))) (.step 15 (.step 17 (.step 43 (.step 3 (.close 4)))))) (.step 5 (.step 7 (.close 3)))) (.step 7 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 5 (.step 13 (.step 3 (.step 4 (.close 5)))))) (.step 24 (.step 33 (.close 13)))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 9)))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.close 15)))))) (.step 7 (.step 24 (.close 19))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684692869146140348189118814025613316194304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 68 (.step 11 (.close 19))) (.step 43 (.step 5 (.step 20 (.step 9 (.step 19 (.close 13))))))) (.split 39 0 (.step 38 (.step 9 (.close 13))) (.step 3 (.step 19 (.close 24))))) (.step 15 (.step 17 (.step 38 (.step 13 (.step 5 (.step 9 (.close 15)))))))) (.step 5 (.step 7 (.close 3)))) (.step 7 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 24 (.close 4)))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 9)))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.close 15)))))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.step 19 (.close 9))))) (.step 19 (.step 13 (.step 4 (.close 20))))) (.step 13 (.step 17 (.close 14))))))) (.step 7 (.split 22 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 42 (.step 11 (.step 3 (.close 19)))))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 13 (.step 4 (.close 20))))) (.step 13 (.step 17 (.close 14))))) (.step 19 (.step 20 (.step 13 (.step 15 (.step 4 (.step 9 (.close 19)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984654877947441158541136100609702384923046479977775104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 15 (.split 30 0 (.split 34 0 (.split 35 0 (.split 43 0 (.step 66 (.step 15 (.close 3))) (.step 15 (.close 11))) (.step 15 (.step 3 (.close 13)))) (.step 15 (.step 3 (.step 13 (.close 17))))) (.split 34 0 (.split 35 0 (.split 49 0 (.step 13 (.step 3 (.step 9 (.close 15)))) (.step 15 (.step 11 (.step 13 (.close 17))))) (.step 3 (.step 15 (.close 13)))) (.step 13 (.step 15 (.step 3 (.close 13))))))) (.split 30 0 (.step 5 (.step 15 (.close 3))) (.step 3 (.close 7)))) (.split 25 0 (.step 15 (.split 30 0 (.split 35 0 (.split 34 0 (.split 39 0 (.step 68 (.step 15 (.close 3))) (.step 11 (.step 27 (.close 3)))) (.step 5 (.step 7 (.close 15)))) (.step 5 (.step 15 (.step 7 (.close 17))))) (.step 7 (.close 17)))) (.step 5 (.step 7 (.close 15))))) (.split 24 0 (.split 30 0 (.step 24 (.split 25 0 (.step 17 (.step 66 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 3 (.step 5 (.close 7))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.step 15 (.close 17))))) (.split 22 0 (.split 24 0 (.split 30 0 (.step 24 (.split 25 0 (.step 17 (.step 61 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 3 (.step 5 (.close 7))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 13 (.step 15 (.close 17)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444054304294535101206066135910318080⟩
def references : Fin 3 → Box := ![Part15.root, Part16.root, Part17.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 68 (.step 11 (.step 19 (.step 13 (.step 3 (.close 20)))))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 13)))))) (.split 39 0 (.step 43 (.close 3)) (.step 3 (.step 19 (.close 24))))) (.step 15 (.step 17 (.step 43 (.step 3 (.close 4)))))) (.step 5 (.step 7 (.close 3)))) (.step 7 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 5 (.step 13 (.step 3 (.step 4 (.close 5)))))) (.step 24 (.step 33 (.close 13)))) (.step 13 (.step 33 (.step 20 (.close 4))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.close 15)))))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 13 (.step 24 (.step 3 (.close 20)))))) (.step 13 (.step 17 (.close 14))))))))) (.reuse 1)) (.split 16 0 (.reuse 2) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.step 24 (.split 25 0 (.step 17 (.step 42 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 3 (.step 5 (.close 7))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 17 (.step 7 (.close 13)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450974109873196190662656⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 15 (.split 35 0 (.split 36 0 (.step 52 (.step 9 (.step 3 (.step 13 (.close 15))))) (.step 15 (.step 3 (.close 13)))) (.step 15 (.step 3 (.step 13 (.close 17)))))) (.split 30 0 (.step 9 (.step 4 (.step 15 (.close 28)))) (.step 3 (.close 7)))) (.split 25 0 (.step 15 (.step 9 (.split 30 0 (.step 29 (.step 3 (.close 7))) (.step 3 (.step 7 (.close 17)))))) (.step 3 (.close 4)))) (.step 24 (.split 24 0 (.step 24 (.step 43 (.step 4 (.step 13 (.close 15))))) (.step 3 (.step 7 (.step 15 (.close 17))))))) (.split 22 0 (.step 24 (.split 24 0 (.step 24 (.step 39 (.step 4 (.close 13)))) (.step 3 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 13 (.step 15 (.close 17)))))) (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.step 24 (.step 38 (.step 7 (.step 4 (.step 9 (.close 13)))))) (.step 3 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.step 13 (.step 4 (.close 17)))))) (.split 16 0 (.split 17 0 (.step 15 (.step 3 (.step 7 (.step 11 (.close 13))))) (.step 3 (.step 13 (.close 15)))) (.step 3 (.step 13 (.close 17)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629983158300269420517377986095744054701642398290363285504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 29 (.split 36 0 (.step 9 (.step 3 (.close 7))) (.step 57 (.step 3 (.close 7))))) (.step 9 (.step 38 (.step 5 (.step 7 (.close 9)))))) (.split 30 0 (.step 29 (.step 38 (.step 9 (.close 3)))) (.step 38 (.close 7)))) (.step 15 (.split 35 0 (.split 39 0 (.step 29 (.split 30 0 (.step 9 (.step 7 (.step 5 (.close 9)))) (.step 7 (.close 9)))) (.step 9 (.step 38 (.step 5 (.step 7 (.close 9)))))) (.step 29 (.step 38 (.step 9 (.close 3))))))) (.step 9 (.close 29))) (.split 25 0 (.step 9 (.step 29 (.step 3 (.close 7)))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 5 (.close 9)) (.step 3 (.step 5 (.close 9)))) (.step 4 (.step 9 (.step 5 (.close 21))))) (.step 4 (.step 5 (.step 9 (.step 15 (.close 21)))))) (.step 3 (.close 4))))) (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 62 (.step 29 (.step 43 (.step 4 (.close 9))))) (.step 68 (.step 38 (.step 9 (.close 3))))) (.step 7 (.step 15 (.step 43 (.step 3 (.close 21)))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 4 (.step 9 (.step 15 (.close 28)))))) (.step 43 (.step 9 (.close 11))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684692869144872697588891737545621219835904⟩
def references : Fin 1 → Box := ![Part20.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 24 0 (.split 25 0 (.split 30 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.step 11 (.close 3))) (.step 7 (.close 9))) (.step 68 (.step 38 (.step 9 (.close 3))))) (.step 7 (.step 15 (.step 43 (.step 3 (.close 21)))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 4 (.step 9 (.step 15 (.close 28)))))) (.split 25 0 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 9 (.close 11)))) (.step 4 (.step 11 (.close 7)))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 3 (.close 4)))))) (.run (.split 17 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 9 (.step 11 (.close 3))) (.step 21 (.close 9))) (.step 7 (.step 38 (.step 3 (.step 7 (.close 9)))))) (.step 7 (.step 15 (.step 38 (.step 3 (.step 7 (.close 9))))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 4 (.step 9 (.step 15 (.close 28)))))) (.split 25 0 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 9 (.close 11)))) (.step 4 (.step 11 (.close 7)))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 3 (.close 4)))) (.step 7 (.step 11 (.close 4))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1393796574908163946345983544962028274712576, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984654877947441158541134832959102157846566487881416704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 15 (.split 30 0 (.split 34 0 (.split 35 0 (.step 9 (.step 52 (.step 5 (.step 7 (.close 9))))) (.split 39 0 (.step 29 (.step 38 (.step 9 (.close 3)))) (.step 9 (.close 5)))) (.split 35 0 (.step 48 (.step 9 (.close 7))) (.step 29 (.step 38 (.step 43 (.step 5 (.close 9))))))) (.split 34 0 (.split 36 0 (.step 42 (.step 48 (.step 9 (.close 7)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))))) (.split 30 0 (.step 15 (.step 9 (.step 5 (.close 16)))) (.step 3 (.close 4)))) (.split 25 0 (.step 15 (.step 9 (.split 30 0 (.step 11 (.step 5 (.close 9))) (.step 5 (.step 11 (.close 7)))))) (.step 5 (.step 9 (.close 11))))) (.step 24 (.split 24 0 (.split 25 0 (.step 15 (.split 34 0 (.split 36 0 (.step 48 (.step 11 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 3 (.close 4))) (.step 11 (.step 3 (.close 7)))))) (.split 22 0 (.step 24 (.split 24 0 (.split 25 0 (.step 15 (.split 34 0 (.split 36 0 (.step 48 (.step 11 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 3 (.close 4))) (.step 11 (.step 3 (.close 7))))) (.step 7 (.close 11)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨1329227995784915874056728565960933376, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339447684694198372868482504764641352681500180480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 9 (.step 4 (.step 7 (.close 9)))) (.split 49 0 (.step 9 (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 9 (.close 11)))) (.split 39 0 (.split 42 0 (.step 9 (.close 3)) (.step 7 (.step 5 (.close 9)))) (.step 4 (.step 5 (.close 9))))) (.step 57 (.step 9 (.step 5 (.close 7))))) (.step 9 (.step 38 (.step 7 (.close 5))))) (.split 36 0 (.split 38 0 (.step 9 (.step 5 (.step 7 (.close 9)))) (.step 15 (.step 3 (.close 4)))) (.step 15 (.step 7 (.close 5))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 9 (.split 16 0 (.step 15 (.step 9 (.close 7))) (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 3)))) (.step 29 (.step 38 (.close 7)))) (.step 7 (.step 9 (.step 7 (.close 15)))))) (.split 16 0 (.split 30 0 (.step 9 (.close 29)) (.step 4 (.step 7 (.close 9)))) (.step 4 (.close 9)))) (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 16 0 (.step 9 (.step 7 (.close 11))) (.step 29 (.close 9))) (.step 4 (.step 5 (.close 9)))) (.step 4 (.close 9))) (.step 9 (.step 5 (.close 7)))) (.step 29 (.close 9))) (.step 4 (.step 9 (.close 7)))) (.step 4 (.step 9 (.close 5))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨1267650600229382323002383794176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078489444054304294535102358987640517165056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 24 0 (.split 25 0 (.split 34 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 9 (.step 7 (.step 4 (.close 9)))) (.step 7 (.close 9))) (.step 52 (.step 7 (.step 4 (.close 9))))) (.step 7 (.close 9))) (.split 36 0 (.split 38 0 (.split 39 0 (.split 51 0 (.step 9 (.close 3)) (.step 7 (.close 9))) (.step 4 (.step 9 (.step 7 (.close 9))))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.step 38 (.step 3 (.step 7 (.close 9))))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 15))) (.step 7 (.step 4 (.step 9 (.step 15 (.close 28)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 15 (.step 9 (.split 35 0 (.step 52 (.step 7 (.step 4 (.close 9)))) (.step 4 (.step 9 (.step 7 (.close 11))))))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 3 (.step 7 (.step 9 (.close 11)))))) (.split 16 0 (.split 24 0 (.split 17 0 (.step 15 (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 11 (.close 7)))) (.step 3 (.step 7 (.close 11))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450975262794700797509632⟩
def references : Fin 4 → Box := ![Part21.root, Part22.root, Part23.root, Part24.root]
def proof : Chunks.Proof 4 := (.split 10 0 (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.split 25 0 (.step 15 (.split 34 0 (.split 36 0 (.step 42 (.step 48 (.step 9 (.close 7)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 3 (.close 4))) (.step 11 (.step 3 (.close 7))))) (.step 7 (.close 11))) (.step 11 (.close 7)))))) (.split 14 0 (.reuse 2) (.run (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 15 (.step 4 (.step 7 (.close 11)))) (.step 4 (.step 9 (.close 5)))) (.step 15 (.step 5 (.close 7)))) (.step 15 (.step 3 (.close 7)))) (.step 4 (.step 15 (.close 7)))) (.step 4 (.step 9 (.close 5)))) (.step 29 (.close 9)))))) (.split 12 0 (.reuse 3) (.run (.split 14 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 36 0 (.split 38 0 (.step 15 (.step 3 (.close 7))) (.step 4 (.step 7 (.step 9 (.close 15))))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 7 (.close 9))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 29 (.close 9)))) (.step 4 (.step 15 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part23.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431950279842554359664449629984656339449078490773282300079450975262794700797509632⟩
def references : Fin 6 → Box := ![Part3.root, Part4.root, Part9.root, Part13.root, Part19.root, Part25.root]
def proof : Chunks.Proof 6 := (.split 6 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.reuse 0) (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.close 20))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 38 (.step 3 (.step 19 (.close 15))))))) (.step 24 (.step 33 (.step 42 (.step 4 (.step 11 (.step 19 (.close 15)))))))) (.step 7 (.step 4 (.close 13)))) (.step 7 (.step 24 (.step 19 (.step 4 (.step 19 (.close 20))))))) (.split 24 0 (.split 25 0 (.step 24 (.step 19 (.step 20 (.step 19 (.step 9 (.close 13)))))) (.step 7 (.step 4 (.step 18 (.close 5))))) (.step 7 (.step 19 (.step 20 (.step 4 (.step 7 (.close 19))))))))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part9.excludes
  · exact Part13.excludes
  · exact Part19.excludes
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part26

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part26.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case17

namespace FiveColour.Packed.EnumerationChunks.Projected.Case17
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 261 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 261 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 261 0).upper i := by decide +kernel
lemma budget_model : (⟨11592783902519083183027, 5789228615357111141503591527908565328988052238931866842109466783872516018158651860904340855333424994291657941685580562196867513399766593215024954541188249413884004349401981041481010002029536037373500234088386757515328619520, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 261), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11592783902519083183027, 5789228615357111141503591527908565328988052238931866842109466783872516018158651860904340855333424994291657941685580562196867513399766593215024954541188249413884004349401981041481010002029536037373500234088386757515328619520, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 261) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 261 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 261 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 261) (Archive.root 261) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 261 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 261 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case17

namespace FiveColour.Packed.EnumerationChunks.Case17
def root : Box := Archive.root 261
def families : Fin 78 → List Cut := Enumeration.families 261
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case17.original_covered points
end FiveColour.Packed.EnumerationChunks.Case17
