module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case16
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356938251595859146627258110504337408⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11592783902519066405619, 5789228615357111146520043253955950920611677468081988178351555838035331549072275774391194391757107785588393962429266766932008325959275370688911558313772706980649642054329298584095605580087976326543880150211487193694858118144, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824311276823845110188232872089498855480074695913096217057340391845527552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 39 0 (.split 36 0 (.step 29 (.split 38 0 (.step 55 (.step 53 (.close 13))) (.step 38 (.step 3 (.close 5))))) (.step 57 (.step 3 (.step 9 (.close 13))))) (.split 42 0 (.split 35 0 (.split 63 0 (.step 38 (.step 5 (.step 9 (.close 19)))) (.step 27 (.step 38 (.step 5 (.step 13 (.step 19 (.close 42))))))) (.step 29 (.close 38))) (.step 38 (.step 5 (.step 9 (.step 20 (.step 13 (.step 19 (.close 39))))))))) (.split 35 0 (.split 36 0 (.split 42 0 (.step 52 (.step 9 (.step 15 (.step 3 (.step 5 (.close 19)))))) (.step 15 (.step 43 (.step 3 (.close 9))))) (.step 43 (.step 15 (.step 9 (.step 3 (.step 18 (.step 22 (.step 3 (.close 33))))))))) (.step 29 (.step 38 (.step 15 (.step 43 (.step 3 (.close 33)))))))) (.split 34 0 (.split 36 0 (.split 35 0 (.step 53 (.step 38 (.step 3 (.step 9 (.close 13))))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 43 (.step 9 (.step 3 (.step 13 (.close 33))))))) (.step 38 (.step 43 (.step 15 (.step 9 (.step 18 (.close 33)))))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864855622980220958549882620527955420999374745819414528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.split 36 0 (.step 42 (.step 4 (.step 9 (.step 19 (.step 13 (.close 20)))))) (.step 38 (.step 24 (.step 3 (.close 4)))))) (.step 43 (.step 3 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.step 13 (.step 19 (.close 20)))))))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.step 17 (.close 24)))) (.step 33 (.step 37 (.step 33 (.step 20 (.close 4)))))) (.step 4 (.step 33 (.step 13 (.step 15 (.close 17)))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 27 (.close 29)) (.step 5 (.step 7 (.step 4 (.close 21))))) (.step 7 (.step 29 (.close 3)))) (.step 7 (.step 29 (.close 3)))) (.step 7 (.step 24 (.close 27))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.close 20)))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 43 (.step 3 (.close 15)))))) (.step 24 (.step 33 (.split 34 0 (.step 61 (.step 33 (.close 20))) (.step 17 (.step 24 (.step 3 (.close 20)))))))) (.step 7 (.step 24 (.close 27))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864855622980220958549882620527955420999374745819414528⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 17 0 (.split 22 0 (.split 26 0 (.reuse 0) (.run (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 30 0 (.step 9 (.step 27 (.step 3 (.step 21 (.close 29))))) (.step 38 (.step 9 (.step 27 (.step 3 (.close 7)))))) (.step 29 (.step 3 (.close 7)))) (.step 38 (.close 29))) (.split 38 0 (.step 57 (.split 42 0 (.step 29 (.step 3 (.close 7))) (.step 7 (.step 27 (.step 5 (.close 21)))))) (.step 29 (.close 3)))) (.split 36 0 (.split 38 0 (.split 42 0 (.step 29 (.step 3 (.close 7))) (.step 7 (.close 29))) (.step 29 (.close 3))) (.step 29 (.step 7 (.close 5))))))) (.run (.split 26 0 (.split 34 0 (.split 30 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.step 75 (.step 5 (.step 9 (.step 19 (.close 13)))))) (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 24)))))) (.step 42 (.close 3)))) (.step 75 (.split 35 0 (.step 43 (.step 5 (.step 17 (.close 24)))) (.step 38 (.step 43 (.close 3)))))) (.step 75 (.split 34 0 (.split 35 0 (.split 30 0 (.step 27 (.close 7)) (.step 7 (.step 19 (.close 20)))) (.step 38 (.step 29 (.step 3 (.close 7))))) (.step 7 (.step 29 (.close 3)))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084481858289452800824212788137282394401751957504⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 43 (.close 3)))) (.split 39 0 (.step 38 (.step 11 (.close 13))) (.step 24 (.close 42)))) (.step 38 (.split 30 0 (.step 38 (.step 29 (.step 3 (.close 7)))) (.step 7 (.close 24))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 25 (.step 11 (.step 19 (.close 3))))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 38 (.step 3 (.step 19 (.close 15))))))) (.step 24 (.step 33 (.step 42 (.step 4 (.step 11 (.step 19 (.close 15)))))))) (.step 7 (.step 24 (.close 27))))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 42 (.close 20))) (.step 24 (.step 4 (.step 19 (.close 20))))) (.step 24 (.step 17 (.step 38 (.step 3 (.step 19 (.close 15))))))) (.step 24 (.step 33 (.step 42 (.step 4 (.step 11 (.step 19 (.close 15)))))))) (.step 7 (.step 24 (.close 27)))) (.step 24 (.split 26 0 (.step 19 (.step 20 (.step 19 (.step 9 (.close 13))))) (.step 7 (.step 4 (.close 19)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252108335950622245948371878616544971809633108884073520793507524513890304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 52 (.step 27 (.step 5 (.step 19 (.step 20 (.close 38)))))) (.step 42 (.step 9 (.step 15 (.step 5 (.step 17 (.close 19))))))) (.split 35 0 (.split 43 0 (.step 57 (.step 58 (.step 15 (.step 17 (.step 19 (.close 20)))))) (.step 15 (.step 9 (.step 5 (.step 9 (.close 11)))))) (.step 38 (.step 15 (.step 29 (.step 5 (.step 20 (.close 17)))))))) (.split 35 0 (.split 36 0 (.step 52 (.close 5)) (.step 43 (.step 5 (.step 15 (.step 17 (.close 9)))))) (.step 38 (.step 29 (.step 37 (.step 15 (.close 17))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 43 (.step 11 (.step 24 (.step 15 (.close 13)))))) (.step 43 (.step 5 (.step 15 (.close 24))))) (.step 42 (.close 3))) (.split 35 0 (.split 36 0 (.step 43 (.step 5 (.step 15 (.step 17 (.close 9))))) (.step 37 (.step 5 (.step 9 (.close 11))))) (.step 3 (.step 38 (.close 9)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 27 (.step 15 (.close 29))) (.step 5 (.step 27 (.step 4 (.step 5 (.step 15 (.close 17))))))) (.step 74 (.step 27 (.step 15 (.close 29))))) (.split 36 0 (.split 38 0 (.split 42 0 (.step 27 (.step 15 (.close 29))) (.step 7 (.step 5 (.step 17 (.close 15))))) (.step 3 (.step 5 (.close 15)))) (.step 7 (.step 29 (.close 5))))) (.split 34 0 (.step 67 (.step 38 (.step 4 (.step 7 (.step 9 (.close 15)))))) (.step 3 (.step 7 (.step 17 (.close 15))))))))
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
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864855622981614755124790784474301403391415268413538304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 61 (.step 68 (.step 4 (.step 11 (.close 15))))) (.step 24 (.step 4 (.step 17 (.step 38 (.step 13 (.step 15 (.close 19)))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 67 (.step 13 (.step 20 (.close 3))))) (.step 3 (.step 19 (.step 20 (.step 9 (.close 13)))))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 19)))))))) (.step 74 (.step 11 (.step 24 (.step 4 (.step 74 (.step 17 (.step 7 (.close 15))))))))) (.step 24 (.split 26 0 (.split 30 0 (.step 11 (.step 17 (.step 74 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 20 (.step 11 (.step 17 (.step 3 (.close 19))))))) (.step 7 (.step 4 (.step 17 (.step 19 (.close 15)))))))))
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
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252086027708988159134119674434924346081280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 68 (.step 4 (.step 11 (.close 15))))) (.step 24 (.step 4 (.step 17 (.close 38))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.step 42 (.step 3 (.close 13))))) (.step 67 (.step 38 (.step 24 (.step 4 (.step 17 (.step 7 (.close 15)))))))) (.step 24 (.split 26 0 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 3 (.step 13 (.close 20)))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.close 20))))))) (.step 7 (.step 4 (.step 17 (.step 19 (.close 15)))))))) (.split 22 0 (.step 24 (.split 26 0 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 3 (.step 13 (.close 20)))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.close 20))))))) (.step 7 (.step 4 (.step 17 (.step 19 (.close 15))))))) (.split 30 0 (.step 24 (.step 19 (.step 20 (.step 7 (.step 5 (.step 11 (.step 13 (.close 17)))))))) (.step 13 (.step 7 (.step 19 (.step 20 (.step 11 (.close 17))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530431948468824312961820511807104716616454568640124460367288239972559055196025520128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.split 30 0 (.split 38 0 (.split 42 0 (.step 55 (.step 17 (.step 15 (.close 38)))) (.step 15 (.step 43 (.step 17 (.close 3))))) (.step 15 (.step 38 (.step 5 (.close 3))))) (.step 38 (.step 53 (.step 3 (.step 13 (.close 15))))))) (.step 62 (.step 43 (.step 9 (.step 15 (.step 4 (.step 17 (.close 24)))))))) (.step 57 (.step 9 (.step 15 (.step 13 (.step 3 (.step 19 (.close 20)))))))) (.split 22 0 (.split 30 0 (.step 29 (.step 38 (.step 15 (.step 53 (.step 20 (.step 3 (.close 5))))))) (.step 38 (.close 9))) (.step 68 (.step 38 (.step 23 (.step 15 (.step 13 (.step 17 (.close 19))))))))) (.split 35 0 (.split 22 0 (.step 15 (.step 43 (.step 9 (.close 15)))) (.step 43 (.step 3 (.close 15)))) (.step 15 (.step 29 (.step 15 (.step 5 (.step 19 (.close 20)))))))) (.split 30 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.step 43 (.step 17 (.step 24 (.close 15))))) (.step 18 (.step 9 (.step 15 (.step 17 (.step 20 (.close 19))))))) (.step 68 (.step 38 (.step 23 (.step 15 (.step 13 (.step 17 (.close 19)))))))) (.step 15 (.step 18 (.step 9 (.step 24 (.close 13)))))) (.step 24 (.step 4 (.step 17 (.step 15 (.step 9 (.step 20 (.close 19)))))))) (.step 24 (.step 4 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084481858290782028819997704010186201462032302080⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 26 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.step 29 (.step 3 (.step 9 (.step 7 (.step 15 (.step 17 (.close 27))))))) (.step 75 (.close 29))) (.split 34 0 (.split 43 0 (.split 22 0 (.step 66 (.step 29 (.step 3 (.close 7)))) (.step 4 (.step 7 (.step 17 (.step 24 (.close 15)))))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.step 15 (.step 7 (.close 28)))))))) (.run (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 0 (.split 17 0 (.split 22 0 (.step 29 (.step 38 (.step 4 (.step 15 (.step 13 (.close 19)))))) (.step 17 (.step 4 (.step 24 (.step 7 (.close 15)))))) (.step 17 (.step 18 (.step 24 (.step 7 (.close 15)))))) (.split 42 0 (.step 27 (.step 17 (.step 23 (.step 24 (.step 15 (.close 38)))))) (.step 3 (.step 17 (.close 24))))) (.step 18 (.step 38 (.step 4 (.close 3))))) (.step 38 (.step 43 (.step 24 (.close 15))))) (.step 38 (.step 43 (.step 15 (.step 3 (.close 7)))))) (.step 24 (.step 18 (.step 38 (.close 9)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356936983944049992578241984626425856⟩
def references : Fin 5 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root, Part8.root]
def proof : Chunks.Proof 5 := (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.step 11 (.step 17 (.step 13 (.step 15 (.close 19))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.step 15 (.close 19))))))) (.step 24 (.step 4 (.step 17 (.step 38 (.step 13 (.step 15 (.close 19)))))))) (.step 24 (.step 17 (.step 3 (.step 13 (.close 17)))))) (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 5 (.step 13 (.step 20 (.step 11 (.step 17 (.step 19 (.close 24)))))))) (.step 3 (.step 19 (.step 24 (.close 13))))) (.step 5 (.step 13 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.step 75 (.step 24 (.step 4 (.step 17 (.close 27))))) (.step 3 (.step 7 (.step 17 (.step 24 (.close 19))))))))) (.reuse 2)) (.reuse 3))) (.split 14 0 (.reuse 4) (.run (.split 16 0 (.split 26 0 (.split 17 0 (.split 22 0 (.step 15 (.split 34 0 (.split 35 0 (.split 42 0 (.step 52 (.step 5 (.step 9 (.step 13 (.close 15))))) (.step 15 (.step 3 (.close 5)))) (.step 15 (.step 5 (.close 13)))) (.step 15 (.step 29 (.step 5 (.step 13 (.close 17))))))) (.step 24 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15)))))))) (.step 24 (.step 15 (.step 17 (.step 4 (.step 9 (.step 13 (.close 15)))))))) (.step 15 (.step 24 (.step 15 (.step 24 (.close 29)))))) (.split 17 0 (.step 24 (.step 15 (.step 23 (.step 17 (.step 7 (.step 9 (.close 13))))))) (.step 17 (.step 7 (.step 3 (.step 11 (.close 13))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252108335950622245948371878615151175234726212588327766630868498622971904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 43 (.step 3 (.close 9)))) (.step 43 (.step 11 (.step 19 (.step 20 (.step 19 (.close 38))))))) (.split 36 0 (.split 39 0 (.step 29 (.step 52 (.step 3 (.close 19)))) (.step 38 (.step 9 (.close 13)))) (.step 38 (.step 29 (.step 3 (.step 24 (.close 13))))))) (.step 15 (.split 35 0 (.step 43 (.close 15)) (.step 15 (.step 3 (.close 17)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 3 (.close 9)))) (.step 42 (.step 3 (.step 13 (.step 9 (.close 20)))))) (.split 39 0 (.split 38 0 (.step 43 (.step 13 (.step 9 (.step 3 (.close 33))))) (.step 13 (.step 18 (.close 33)))) (.step 33 (.step 13 (.close 19))))) (.split 36 0 (.split 38 0 (.step 42 (.step 13 (.step 9 (.step 3 (.close 33))))) (.step 3 (.step 9 (.step 13 (.close 18))))) (.step 33 (.step 13 (.close 19))))) (.step 15 (.step 33 (.split 35 0 (.step 33 (.step 13 (.step 15 (.step 3 (.step 11 (.close 15)))))) (.step 15 (.step 3 (.step 13 (.close 17))))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 52 (.step 9 (.step 24 (.step 21 (.step 19 (.close 27)))))) (.step 7 (.step 24 (.close 29)))) (.step 7 (.step 4 (.close 21)))) (.step 7 (.step 29 (.close 3)))) (.step 7 (.step 15 (.step 7 (.close 28))))) (.step 7 (.step 24 (.close 29))))))
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
def root : Box := ⟨1496577676626844588241840919301702041529172700954624, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864855622980220958549883888178555649228776242522619904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 68 (.step 11 (.step 19 (.step 13 (.step 3 (.close 20)))))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 13)))))) (.split 39 0 (.step 43 (.close 3)) (.step 3 (.step 19 (.close 24))))) (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 5 (.step 13 (.step 3 (.step 4 (.close 5)))))) (.step 24 (.step 33 (.close 13)))) (.step 13 (.step 33 (.step 20 (.close 4))))) (.step 33 (.step 13 (.close 19))))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.step 13 (.close 15)))) (.step 13 (.step 33 (.close 15)))) (.step 15 (.step 17 (.step 33 (.step 3 (.close 11))))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 13 (.step 24 (.step 3 (.close 20)))))) (.step 13 (.step 17 (.close 14))))))))
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
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084481858289452802091863388365511795898455162880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 68 (.step 11 (.close 19))) (.step 43 (.step 5 (.step 20 (.step 9 (.step 19 (.close 13))))))) (.split 39 0 (.step 38 (.step 9 (.close 13))) (.step 3 (.step 19 (.close 24))))) (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 24 (.close 4)))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 9)))))) (.step 33 (.step 13 (.close 19))))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.step 13 (.close 15)))) (.step 13 (.step 33 (.close 15)))) (.step 15 (.step 17 (.step 33 (.step 3 (.close 11))))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 25 (.close 3)))) (.step 13 (.step 20 (.step 19 (.close 9))))) (.step 19 (.step 13 (.step 4 (.close 20))))) (.step 13 (.step 17 (.close 14))))))) (.step 7 (.split 22 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 42 (.step 11 (.step 3 (.close 19)))))) (.step 13 (.step 20 (.close 4)))) (.step 19 (.step 13 (.step 4 (.close 20))))) (.step 13 (.step 17 (.close 14))))) (.step 19 (.step 20 (.step 13 (.step 15 (.step 4 (.step 9 (.close 19)))))))))))
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
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252086027710255809734347903836421049286656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 43 0 (.step 66 (.step 15 (.close 3))) (.step 15 (.close 11))) (.step 15 (.step 3 (.close 13)))) (.step 15 (.step 3 (.step 13 (.close 17))))) (.split 34 0 (.split 35 0 (.split 49 0 (.step 13 (.step 3 (.step 9 (.close 15)))) (.step 15 (.step 11 (.step 13 (.close 17))))) (.step 3 (.step 15 (.close 13)))) (.step 13 (.step 15 (.step 3 (.close 13)))))) (.step 15 (.step 4 (.step 7 (.close 17)))))) (.step 24 (.split 26 0 (.split 30 0 (.step 17 (.step 66 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17)))) (.step 3 (.step 7 (.step 15 (.close 17))))))) (.split 22 0 (.step 24 (.split 26 0 (.split 30 0 (.step 17 (.step 61 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17)))) (.step 3 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 13 (.step 15 (.close 17)))))) (.split 17 0 (.split 22 0 (.step 24 (.split 26 0 (.split 30 0 (.step 17 (.step 42 (.step 13 (.step 3 (.step 9 (.close 15)))))) (.step 13 (.step 15 (.close 17)))) (.step 3 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 13 (.step 7 (.close 17))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1329229263435516101133208558057291776, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356938251594650220807643481329631232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 22 0 (.step 15 (.split 36 0 (.step 52 (.step 9 (.step 3 (.step 13 (.close 15))))) (.step 15 (.step 3 (.close 13))))) (.step 24 (.step 4 (.step 9 (.close 13))))) (.step 15 (.step 18 (.step 15 (.step 13 (.close 17)))))) (.step 15 (.close 5))) (.step 15 (.step 7 (.step 15 (.step 24 (.step 3 (.close 28))))))) (.step 24 (.split 26 0 (.step 24 (.step 39 (.step 4 (.close 13)))) (.step 4 (.step 7 (.close 15)))))) (.split 17 0 (.step 24 (.split 26 0 (.step 24 (.step 38 (.step 4 (.step 9 (.close 13))))) (.step 4 (.step 7 (.close 15))))) (.step 7 (.step 13 (.step 4 (.close 17)))))) (.split 16 0 (.step 15 (.step 3 (.step 11 (.close 13)))) (.step 3 (.close 17)))))
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
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942863359045303594113961642047260462873006861700070113280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 34 0 (.split 35 0 (.split 26 0 (.split 30 0 (.step 9 (.split 38 0 (.step 55 (.step 9 (.close 11))) (.step 29 (.step 42 (.close 5))))) (.split 36 0 (.step 42 (.step 9 (.step 7 (.step 4 (.close 9))))) (.step 7 (.close 9)))) (.split 43 0 (.split 54 0 (.split 63 0 (.split 51 0 (.step 27 (.close 3)) (.step 9 (.close 3))) (.step 11 (.step 5 (.close 7)))) (.step 9 (.step 3 (.close 5)))) (.step 9 (.step 11 (.step 3 (.close 7)))))) (.split 36 0 (.split 38 0 (.step 42 (.step 29 (.step 9 (.close 3)))) (.step 5 (.step 29 (.step 9 (.close 3))))) (.step 29 (.step 38 (.step 5 (.close 9)))))) (.split 35 0 (.split 36 0 (.split 26 0 (.split 30 0 (.step 9 (.step 29 (.step 17 (.step 5 (.step 7 (.close 9)))))) (.step 7 (.close 9))) (.step 29 (.close 7))) (.step 29 (.step 43 (.step 5 (.step 7 (.close 9)))))) (.step 29 (.step 38 (.step 43 (.step 5 (.close 9))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 62 (.step 9 (.step 7 (.step 4 (.close 9))))) (.step 7 (.close 9))) (.step 24 (.step 4 (.step 9 (.close 7))))) (.step 7 (.step 17 (.step 43 (.step 3 (.close 7)))))) (.step 7 (.step 9 (.close 11)))) (.split 30 0 (.step 75 (.step 24 (.step 4 (.close 11)))) (.step 3 (.step 7 (.step 9 (.close 11))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1393796574908163947554908211655152842571776, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942863359045304987910536550211206808855398902222664237056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 9 (.step 11 (.close 3))) (.step 42 (.step 11 (.close 3)))) (.split 38 0 (.step 9 (.step 11 (.close 3))) (.step 5 (.close 9)))) (.split 36 0 (.step 42 (.step 29 (.split 38 0 (.step 9 (.close 3)) (.step 4 (.step 5 (.close 9)))))) (.step 5 (.step 9 (.step 7 (.step 9 (.close 11))))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 9 (.step 11 (.close 3))) (.step 5 (.close 9))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 17 (.close 7))))) (.split 43 0 (.split 54 0 (.step 11 (.close 29)) (.step 9 (.step 5 (.step 11 (.close 15))))) (.step 5 (.step 9 (.close 11))))) (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 52 (.step 7 (.step 4 (.close 9)))) (.step 11 (.step 3 (.close 7)))) (.step 5 (.step 7 (.close 9)))) (.step 5 (.step 7 (.close 9)))) (.step 5 (.step 42 (.close 7)))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 11 (.close 7))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 11 (.close 3)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 3)))))
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
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252086027708988160343045494049553520787456⟩
def references : Fin 2 → Box := ![Part15.root, Part16.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 61 (.step 68 (.step 4 (.step 9 (.close 7))))) (.step 24 (.step 4 (.step 9 (.close 7))))) (.step 7 (.step 17 (.step 43 (.step 3 (.close 7)))))) (.step 7 (.step 9 (.close 11)))) (.step 74 (.step 11 (.step 4 (.step 7 (.close 9)))))) (.step 7 (.step 9 (.close 11)))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 68 (.step 4 (.step 9 (.close 7))))) (.step 24 (.step 4 (.step 9 (.close 7))))) (.step 7 (.step 17 (.step 38 (.step 3 (.step 7 (.close 9))))))) (.step 7 (.step 9 (.close 11)))) (.step 67 (.step 38 (.step 24 (.step 4 (.step 9 (.close 7))))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 11 (.close 3)))))) (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 61 (.split 36 0 (.split 42 0 (.step 11 (.close 3)) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 3))) (.step 7 (.close 11))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 42 0 (.step 11 (.close 3)) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 11 (.step 3 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 3))) (.step 7 (.close 11))) (.step 11 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252086027710255810943273723451050223992832⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.split 14 0 (.split 26 0 (.split 34 0 (.split 36 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 38 0 (.step 52 (.step 7 (.step 4 (.close 9)))) (.step 5 (.step 7 (.step 4 (.close 9))))) (.step 42 (.step 29 (.step 4 (.close 9))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 5 (.step 7 (.close 9))))) (.step 7 (.step 15 (.step 5 (.step 7 (.close 9)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 43 0 (.step 66 (.step 4 (.step 9 (.close 7)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 3 (.step 7 (.step 9 (.close 11))))) (.step 3 (.step 7 (.step 9 (.close 11)))))) (.split 16 0 (.split 26 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.step 17 (.step 66 (.step 7 (.step 4 (.close 9))))) (.step 7 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.step 11 (.close 7)))) (.step 7 (.close 11))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356938251595859146627258110504337408⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 10 0 (.split 14 0 (.split 16 0 (.split 26 0 (.split 17 0 (.split 34 0 (.step 9 (.split 35 0 (.split 36 0 (.split 38 0 (.step 9 (.close 7)) (.step 5 (.close 9))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.step 3 (.step 5 (.close 7)))))) (.step 29 (.step 66 (.step 7 (.step 5 (.close 9)))))) (.step 24 (.step 9 (.step 17 (.step 9 (.step 3 (.close 7))))))) (.step 29 (.step 7 (.close 9)))) (.split 17 0 (.step 24 (.step 9 (.step 23 (.step 17 (.step 9 (.close 7)))))) (.step 7 (.step 9 (.close 11))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.step 15 (.step 23 (.step 17 (.close 7))))) (.step 17 (.step 3 (.close 7)))) (.step 17 (.step 3 (.close 7)))) (.step 17 (.step 3 (.close 7))))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 24 (.step 15 (.split 26 0 (.split 30 0 (.step 17 (.step 9 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 4 (.step 9 (.close 7)))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.close 17))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356938251595859146627258110504337408⟩
def references : Fin 7 → Box := ![Part9.root, Part10.root, Part11.root, Part12.root, Part13.root, Part14.root, Part19.root]
def proof : Chunks.Proof 7 := (.split 8 0 (.split 10 0 (.reuse 0) (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.run (.split 26 0 (.split 34 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 62 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 5 (.step 20 (.step 9 (.close 24)))))) (.step 75 (.step 42 (.step 43 (.close 3))))) (.split 35 0 (.split 36 0 (.split 39 0 (.split 38 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 5 (.step 13 (.step 3 (.step 4 (.close 5)))))) (.step 24 (.step 33 (.close 13)))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 9)))))) (.step 33 (.step 13 (.close 19))))) (.split 35 0 (.split 30 0 (.step 15 (.step 17 (.step 13 (.close 15)))) (.step 13 (.step 33 (.close 15)))) (.step 15 (.step 17 (.step 33 (.step 3 (.close 11))))))) (.step 7 (.step 24 (.close 27)))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5))) (.reuse 6))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part20.excludes
end FiveColour.Packed.EnumerationChunks.Case16
