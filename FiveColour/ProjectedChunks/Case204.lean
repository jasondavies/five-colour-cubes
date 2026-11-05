module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case204
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356938251595859146627258110504337408⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11592783902519066405619, 5789228615357111146520043253955950920611677468081988178351555838035331549072275774391194391757107785588393962429266766932008325959275370688911558313772706980649642054329298584095605580087976326543880150211487193694858118144, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252108335950622245949868456291778019822965518206429012213594676843773952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 68 (.step 29 (.step 57 (.step 43 (.close 3))))) (.split 42 0 (.split 35 0 (.step 27 (.step 24 (.step 5 (.step 13 (.step 19 (.close 38)))))) (.step 29 (.close 38))) (.step 38 (.step 5 (.step 9 (.step 19 (.step 13 (.close 20)))))))) (.split 35 0 (.step 43 (.step 58 (.step 9 (.step 15 (.step 17 (.step 19 (.close 20))))))) (.step 29 (.step 38 (.step 15 (.step 20 (.step 3 (.close 5)))))))) (.split 34 0 (.split 36 0 (.split 17 0 (.step 53 (.step 3 (.step 9 (.step 13 (.close 20))))) (.step 42 (.step 3 (.step 11 (.close 20))))) (.step 38 (.step 39 (.step 3 (.step 9 (.step 13 (.close 20))))))) (.step 38 (.step 43 (.step 9 (.step 3 (.step 13 (.step 15 (.close 33))))))))) (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 30 0 (.step 9 (.step 27 (.close 3))) (.step 38 (.step 7 (.step 4 (.step 9 (.close 20)))))) (.step 29 (.step 3 (.close 7)))) (.step 38 (.step 4 (.step 5 (.close 3))))) (.split 38 0 (.step 57 (.step 43 (.step 29 (.close 3)))) (.step 7 (.step 5 (.close 21))))) (.split 36 0 (.split 38 0 (.split 42 0 (.step 29 (.step 3 (.close 7))) (.step 7 (.step 15 (.step 5 (.step 17 (.close 27)))))) (.step 7 (.step 5 (.step 15 (.close 16))))) (.step 29 (.step 4 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084481858289452800824212788137282394401751957504⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 17 0 (.split 34 0 (.split 30 0 (.step 43 (.step 11 (.step 19 (.step 20 (.close 38))))) (.step 42 (.step 43 (.step 3 (.step 11 (.step 19 (.step 13 (.step 20 (.close 24))))))))) (.step 43 (.close 3))) (.split 30 0 (.split 34 0 (.step 24 (.step 20 (.step 24 (.step 11 (.step 13 (.step 3 (.close 19))))))) (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 24 (.step 33 (.close 20))))) (.step 75 (.split 34 0 (.split 17 0 (.step 43 (.step 11 (.step 19 (.step 21 (.step 19 (.close 27)))))) (.step 7 (.close 19))) (.step 7 (.step 15 (.close 17)))))))) (.run (.split 17 0 (.split 26 0 (.split 30 0 (.split 22 0 (.step 43 (.step 66 (.step 11 (.step 19 (.close 3))))) (.split 34 0 (.step 24 (.step 19 (.step 5 (.step 9 (.step 13 (.close 19)))))) (.step 17 (.step 24 (.step 3 (.close 19)))))) (.step 42 (.step 33 (.step 24 (.close 4))))) (.step 38 (.split 30 0 (.step 38 (.step 7 (.step 4 (.step 9 (.step 15 (.close 19)))))) (.step 7 (.step 19 (.close 20)))))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 24 (.step 19 (.step 5 (.step 9 (.step 13 (.close 19)))))) (.step 17 (.step 24 (.step 3 (.close 19))))) (.step 24 (.step 33 (.close 20)))) (.step 7 (.step 19 (.close 20)))) (.step 24 (.step 19 (.step 7 (.step 19 (.step 20 (.close 9))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864855622981614755124790784474301403391415268413538304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 52 (.step 5 (.step 9 (.step 19 (.step 20 (.close 38)))))) (.step 5 (.step 15 (.step 5 (.step 23 (.step 3 (.close 5))))))) (.split 35 0 (.step 43 (.step 9 (.step 15 (.close 17)))) (.step 29 (.step 38 (.step 5 (.step 15 (.close 17))))))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.step 15 (.close 3))))) (.step 37 (.step 9 (.close 17))))) (.split 34 0 (.split 36 0 (.split 38 0 (.step 27 (.step 15 (.close 29))) (.step 5 (.step 27 (.step 4 (.step 5 (.close 15)))))) (.step 43 (.step 5 (.close 27)))) (.step 66 (.split 36 0 (.step 43 (.step 5 (.close 17))) (.step 7 (.step 5 (.close 17))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.step 17 (.step 13 (.step 15 (.close 19)))))) (.step 24 (.step 4 (.step 15 (.step 17 (.close 19)))))) (.step 17 (.step 5 (.step 15 (.step 9 (.close 17)))))) (.step 24 (.step 67 (.step 13 (.step 24 (.close 3)))))) (.step 11 (.step 24 (.step 4 (.step 17 (.step 27 (.close 7)))))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 74 (.step 37 (.step 24 (.step 11 (.step 15 (.close 3)))))) (.step 24 (.step 67 (.step 13 (.step 24 (.close 3)))))) (.step 11 (.step 24 (.step 4 (.step 17 (.step 27 (.close 7))))))) (.step 11 (.step 17 (.step 24 (.step 74 (.step 7 (.step 13 (.step 5 (.step 19 (.close 20))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084481858290782028819997704010186201462032302080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 29 (.split 38 0 (.split 39 0 (.step 15 (.step 43 (.step 57 (.close 3)))) (.step 38 (.step 15 (.step 5 (.step 13 (.step 19 (.close 20))))))) (.step 38 (.step 37 (.step 3 (.close 5)))))) (.split 34 0 (.split 36 0 (.split 35 0 (.step 9 (.step 38 (.step 24 (.step 3 (.close 13))))) (.step 38 (.close 9))) (.step 18 (.step 9 (.step 37 (.step 24 (.close 33)))))) (.step 15 (.step 18 (.step 9 (.step 37 (.close 19))))))) (.step 29 (.step 3 (.close 7)))) (.split 17 0 (.step 75 (.split 26 0 (.split 34 0 (.step 43 (.step 9 (.step 15 (.step 24 (.step 13 (.step 4 (.step 19 (.close 20)))))))) (.step 15 (.step 13 (.step 4 (.step 9 (.step 15 (.close 19))))))) (.step 29 (.step 3 (.close 7))))) (.step 23 (.step 17 (.close 24))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 17 0 (.split 26 0 (.step 24 (.step 9 (.step 38 (.step 4 (.step 15 (.step 13 (.close 19))))))) (.step 29 (.step 3 (.close 7)))) (.step 17 (.step 18 (.close 24)))) (.step 38 (.step 18 (.step 17 (.step 11 (.step 20 (.step 7 (.step 15 (.close 19))))))))) (.step 38 (.step 43 (.step 15 (.close 3))))) (.step 24 (.step 4 (.step 15 (.step 7 (.step 9 (.step 13 (.step 19 (.close 20)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356936983944049992578241984626425856⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.step 67 (.split 26 0 (.split 30 0 (.step 37 (.step 24 (.step 11 (.step 15 (.close 3))))) (.step 24 (.step 42 (.close 3)))) (.step 11 (.step 24 (.step 4 (.step 17 (.step 24 (.step 15 (.close 7))))))))) (.step 11 (.step 17 (.step 24 (.step 19 (.step 3 (.step 7 (.step 13 (.close 20))))))))) (.step 24 (.split 22 0 (.step 11 (.step 17 (.step 19 (.step 3 (.step 7 (.step 13 (.close 20))))))) (.step 19 (.step 7 (.step 11 (.step 13 (.step 17 (.step 5 (.close 20))))))))))))) (.split 14 0 (.reuse 2) (.run (.split 16 0 (.split 26 0 (.split 17 0 (.step 15 (.split 22 0 (.split 30 0 (.step 29 (.step 15 (.close 5))) (.step 38 (.step 3 (.step 9 (.close 13))))) (.step 17 (.step 3 (.step 9 (.close 13)))))) (.step 17 (.step 4 (.step 15 (.step 9 (.close 13)))))) (.step 15 (.step 7 (.step 5 (.step 7 (.step 9 (.step 7 (.close 17)))))))) (.step 24 (.step 15 (.step 17 (.step 3 (.step 7 (.step 9 (.close 13)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942863359045303594113961643314909854175416648567598612480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 52 (.step 3 (.step 9 (.close 19)))) (.step 43 (.step 29 (.step 18 (.close 13))))) (.step 15 (.step 43 (.close 15)))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 33 (.close 3))) (.step 33 (.step 13 (.step 3 (.step 9 (.step 19 (.close 20))))))) (.step 38 (.step 9 (.close 13)))) (.step 15 (.step 33 (.step 13 (.step 3 (.close 9))))))) (.split 34 0 (.split 36 0 (.split 38 0 (.split 30 0 (.step 29 (.close 7)) (.step 7 (.step 19 (.close 20)))) (.step 7 (.close 4))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 15 (.step 3 (.close 7)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 13))) (.step 42 (.step 4 (.step 24 (.close 9))))) (.step 15 (.step 17 (.step 4 (.step 9 (.close 5)))))) (.step 33 (.split 34 0 (.split 35 0 (.step 33 (.step 13 (.close 24))) (.step 33 (.close 13))) (.step 13 (.step 15 (.step 17 (.step 4 (.close 9)))))))) (.step 7 (.step 19 (.close 20))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084481858289452802091863388365511795898455162880⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 13))) (.step 42 (.step 4 (.step 24 (.close 9))))) (.step 15 (.step 17 (.step 4 (.step 9 (.close 5)))))) (.step 33 (.split 34 0 (.split 35 0 (.step 33 (.step 13 (.step 20 (.close 3)))) (.step 33 (.close 13))) (.step 13 (.step 15 (.step 17 (.step 4 (.close 9)))))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 17 (.step 24 (.split 35 0 (.step 13 (.step 20 (.close 24))) (.step 19 (.step 13 (.step 20 (.step 3 (.close 4)))))))))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 43 (.step 11 (.close 13))) (.step 38 (.step 9 (.close 13)))) (.step 15 (.step 17 (.step 4 (.step 9 (.close 5)))))) (.step 33 (.split 34 0 (.step 42 (.step 13 (.step 4 (.step 24 (.close 9))))) (.step 13 (.step 15 (.step 17 (.step 4 (.close 9)))))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 17 (.step 24 (.step 42 (.step 13 (.step 38 (.step 24 (.step 3 (.step 11 (.close 19))))))))))) (.step 7 (.step 24 (.split 34 0 (.split 35 0 (.split 30 0 (.step 20 (.step 13 (.close 19))) (.step 13 (.step 20 (.step 19 (.close 3))))) (.step 19 (.step 4 (.close 9)))) (.step 13 (.step 14 (.close 17)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356938251594650220807643481329631232⟩
def references : Fin 2 → Box := ![Part4.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.reuse 0) (.split 12 0 (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.split 26 0 (.split 30 0 (.step 66 (.step 43 (.close 11))) (.split 35 0 (.step 13 (.step 3 (.step 9 (.close 15)))) (.step 3 (.step 15 (.close 13))))) (.step 15 (.step 3 (.close 7)))) (.step 17 (.step 7 (.close 13))))) (.step 17 (.step 15 (.step 17 (.step 7 (.close 13)))))) (.step 17 (.step 24 (.step 17 (.step 7 (.close 13)))))))) (.run (.split 14 0 (.split 16 0 (.split 26 0 (.split 17 0 (.step 15 (.split 35 0 (.split 30 0 (.step 43 (.step 9 (.step 3 (.close 13)))) (.step 13 (.step 3 (.step 9 (.close 15))))) (.step 15 (.step 3 (.close 13))))) (.step 17 (.step 15 (.step 13 (.step 3 (.step 9 (.close 15))))))) (.step 15 (.close 7))) (.step 24 (.step 4 (.step 13 (.step 7 (.close 15)))))) (.step 15 (.step 3 (.step 11 (.close 13))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084481858289452800824213997063102009030926663680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.split 26 0 (.step 55 (.step 9 (.step 7 (.close 11)))) (.step 9 (.step 3 (.close 7))))) (.step 29 (.step 5 (.close 9)))) (.step 29 (.step 38 (.step 9 (.close 3))))) (.step 29 (.split 30 0 (.step 66 (.step 9 (.step 5 (.close 9)))) (.step 7 (.step 5 (.step 7 (.close 9))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 9 (.step 7 (.step 4 (.close 9)))) (.step 24 (.step 4 (.close 9)))) (.step 7 (.step 17 (.step 3 (.step 7 (.close 9)))))) (.step 7 (.close 9))) (.step 11 (.step 4 (.step 7 (.close 9)))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 74 (.step 43 (.close 11))) (.step 7 (.close 9))) (.step 11 (.step 4 (.step 7 (.close 9))))) (.step 7 (.close 9)))) (.split 17 0 (.split 22 0 (.step 67 (.split 26 0 (.split 30 0 (.step 43 (.close 11)) (.step 7 (.close 9))) (.step 11 (.step 3 (.close 7))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356936983945258918397856613801132032⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 49 0 (.split 17 0 (.split 22 0 (.split 38 0 (.split 39 0 (.split 50 0 (.step 5 (.step 9 (.close 7))) (.step 9 (.close 5))) (.step 9 (.step 11 (.close 3)))) (.step 5 (.close 9))) (.step 11 (.step 3 (.close 7)))) (.step 11 (.step 3 (.close 7)))) (.step 17 (.step 5 (.step 7 (.close 9))))) (.step 11 (.step 5 (.close 7)))) (.split 43 0 (.split 17 0 (.split 34 0 (.split 35 0 (.split 22 0 (.step 67 (.step 7 (.step 4 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.step 24 (.close 11)))) (.step 5 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.step 11 (.close 29))) (.step 11 (.step 5 (.close 7)))))) (.run (.split 14 0 (.split 16 0 (.split 26 0 (.split 34 0 (.step 9 (.split 35 0 (.split 36 0 (.split 38 0 (.step 9 (.close 7)) (.step 5 (.step 4 (.close 9)))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.step 3 (.close 7))))) (.step 29 (.step 43 (.step 9 (.step 5 (.step 7 (.close 9))))))) (.step 9 (.step 7 (.step 5 (.close 10))))) (.step 24 (.step 9 (.step 3 (.close 7))))) (.split 16 0 (.split 17 0 (.step 9 (.step 15 (.step 17 (.step 5 (.step 7 (.close 9)))))) (.step 17 (.close 3))) (.step 17 (.close 3))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967417167139181145516572782394273482432904358968469173545720898209850963728231089162070968530433801142252110020947288942864857084483252087356938251595859146627258110504337408⟩
def references : Fin 2 → Box := ![Part7.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 8 0 (.reuse 0) (.split 10 0 (.reuse 1) (.run (.split 14 0 (.split 26 0 (.split 34 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.step 9 (.step 7 (.step 4 (.close 9)))) (.step 29 (.step 4 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 17 (.step 9 (.close 3)))) (.step 7 (.step 15 (.step 3 (.close 7))))) (.step 66 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 29 (.close 7)) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 4 (.step 9 (.close 7)))))) (.step 17 (.step 15 (.step 17 (.step 7 (.step 4 (.close 9))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case204
