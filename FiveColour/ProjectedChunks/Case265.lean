module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case265
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5648027922681707746912947025153414994101027227966404914970923959714719697867800118656278490936516943622623255930420971702830525833573100232087281202227912944084755504127882300391805385403558262004826403855235112522219521⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨26555015581127267047262, 5653548961318841084741090189984673252039280880295413649867165766736366040885097268639480623903064209551010223234778331005102876109009372315541598094912376117678585947030567660746033573297699013350455109036688858969800705, 0⟩]
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
def root : Box := ⟨1, 5648027922681707746912947025153414994101027227966404914970923959714719697867800118656278490936516943622623255930420971702830523747648260465573527054088133679815965094127606425724524526650929648269928622765439333091508225⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 7 0 (.split 13 0 (.split 27 0 (.step 40 (.split 28 0 (.split 32 0 (.step 55 (.step 5 (.close 12))) (.step 24 (.step 23 (.step 35 (.step 19 (.step 12 (.step 14 (.close 16)))))))) (.step 31 (.step 4 (.step 12 (.close 13)))))) (.step 43 (.split 28 0 (.split 38 0 (.step 68 (.step 24 (.step 23 (.step 20 (.step 12 (.step 19 (.close 21))))))) (.step 23 (.step 35 (.step 23 (.step 5 (.step 12 (.step 19 (.close 21)))))))) (.step 40 (.step 12 (.close 19)))))) (.split 27 0 (.split 28 0 (.step 40 (.step 55 (.split 32 0 (.step 16 (.step 14 (.step 5 (.step 19 (.close 20))))) (.step 23 (.step 35 (.step 16 (.step 12 (.close 19)))))))) (.step 23 (.step 31 (.step 4 (.step 12 (.close 13)))))) (.step 40 (.step 43 (.step 23 (.step 40 (.step 14 (.step 16 (.step 5 (.close 21)))))))))) (.split 13 0 (.split 27 0 (.split 28 0 (.step 40 (.step 55 (.split 32 0 (.split 34 0 (.step 23 (.step 12 (.close 21))) (.step 16 (.step 4 (.step 23 (.close 21))))) (.step 23 (.step 35 (.step 23 (.step 12 (.step 19 (.close 21))))))))) (.step 23 (.step 31 (.step 4 (.step 12 (.close 13)))))) (.step 10 (.step 23 (.step 30 (.step 4 (.close 10)))))) (.step 10 (.step 16 (.step 40 (.split 41 0 (.step 55 (.step 68 (.step 40 (.step 12 (.step 14 (.close 21)))))) (.step 24 (.step 40 (.step 5 (.step 12 (.close 21))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524750123642650625, 5648027922681707746912947025153414994101027227966404914970923959714719697867800118656278490936516943622623255930420971702830525833573100232087281202227912944084755504127882300391805385402260187790192696946976588533071873⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 7 0 (.split 13 0 (.split 27 0 (.split 28 0 (.step 40 (.split 31 0 (.step 55 (.split 32 0 (.split 33 0 (.step 23 (.step 16 (.step 19 (.close 12)))) (.step 23 (.step 24 (.step 20 (.close 21))))) (.step 23 (.step 35 (.step 23 (.step 12 (.step 19 (.close 21)))))))) (.step 40 (.step 5 (.step 14 (.step 16 (.close 21))))))) (.split 53 0 (.step 31 (.step 4 (.step 12 (.close 13)))) (.step 5 (.step 23 (.close 31))))) (.step 40 (.step 43 (.split 28 0 (.step 40 (.step 24 (.close 28))) (.step 40 (.step 4 (.close 5))))))) (.split 31 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 62 0 (.step 31 (.step 55 (.step 37 (.step 23 (.close 12))))) (.step 16 (.step 31 (.step 40 (.step 24 (.step 12 (.step 4 (.close 13)))))))) (.step 14 (.step 23 (.step 5 (.step 16 (.close 21)))))) (.step 40 (.step 41 (.step 23 (.step 24 (.step 40 (.step 12 (.close 16)))))))) (.step 28 (.close 4))) (.step 16 (.step 28 (.step 23 (.step 22 (.close 26))))))) (.split 13 0 (.split 27 0 (.step 8 (.split 32 0 (.split 34 0 (.split 28 0 (.step 30 (.step 6 (.close 7))) (.step 31 (.step 4 (.step 6 (.close 7))))) (.step 16 (.step 31 (.close 7)))) (.step 8 (.close 30)))) (.step 30 (.close 5))) (.step 16 (.step 10 (.step 8 (.split 32 0 (.split 62 0 (.step 31 (.step 30 (.close 6))) (.step 30 (.step 6 (.close 7)))) (.step 8 (.close 30)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1, 5648027922681707746912947025153414994101027227966404914970923959714719697867800118656278490936516943622623255930420971702830525833573100232087281202227912944084755504127882300391805385403558262004826403854109212615376897⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 11 0 (.split 25 0 (.split 31 0 (.reuse 0) (.run (.split 33 0 (.split 7 0 (.step 43 (.split 13 0 (.split 27 0 (.step 40 (.step 14 (.step 4 (.step 5 (.close 16))))) (.step 43 (.step 12 (.step 14 (.close 17))))) (.step 16 (.step 5 (.step 16 (.step 19 (.close 20))))))) (.step 16 (.step 24 (.step 40 (.step 5 (.step 10 (.close 14))))))) (.step 31 (.step 34 (.step 5 (.step 22 (.step 21 (.close 10))))))))) (.reuse 1)) (.run (.split 31 0 (.split 33 0 (.split 7 0 (.split 13 0 (.split 25 0 (.step 43 (.split 27 0 (.step 40 (.step 64 (.step 23 (.step 5 (.step 12 (.step 13 (.step 14 (.close 16)))))))) (.split 28 0 (.split 34 0 (.split 38 0 (.step 14 (.step 16 (.step 4 (.step 19 (.close 20))))) (.step 23 (.step 35 (.step 14 (.step 4 (.step 13 (.close 19))))))) (.step 14 (.close 19))) (.step 23 (.step 34 (.step 4 (.step 19 (.close 20)))))))) (.step 40 (.split 27 0 (.step 23 (.step 43 (.step 55 (.step 14 (.step 13 (.close 16)))))) (.step 40 (.step 14 (.step 16 (.step 6 (.close 21)))))))) (.step 14 (.step 16 (.step 13 (.close 12))))) (.step 16 (.step 8 (.step 23 (.step 10 (.step 14 (.step 5 (.close 21)))))))) (.step 56 (.step 43 (.split 7 0 (.step 56 (.step 24 (.step 14 (.step 4 (.step 6 (.close 12)))))) (.step 5 (.step 8 (.step 16 (.step 23 (.step 10 (.close 14)))))))))) (.step 64 (.step 14 (.step 37 (.step 5 (.step 14 (.close 6)))))))))
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
def root : Box := ⟨1, 5648027922681707746912947025153414994101027227966404914970923959714719697867800118656278490936516943622623255930420971702830525833573100232087281202227912944084755504127882300391805385403558262004826403855235112522219521⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.reuse 0) (.run (.split 7 0 (.split 13 0 (.split 11 0 (.split 25 0 (.split 27 0 (.split 28 0 (.step 43 (.split 31 0 (.split 38 0 (.step 68 (.step 24 (.step 23 (.step 12 (.close 19))))) (.step 23 (.step 35 (.step 23 (.close 5))))) (.step 14 (.step 24 (.step 31 (.step 5 (.close 16))))))) (.step 24 (.step 31 (.step 4 (.step 12 (.close 13)))))) (.step 10 (.split 31 0 (.split 33 0 (.step 28 (.close 6)) (.step 56 (.step 28 (.close 6)))) (.step 14 (.step 68 (.close 28)))))) (.split 27 0 (.step 8 (.step 40 (.step 43 (.step 23 (.close 8))))) (.step 28 (.close 4)))) (.step 14 (.step 8 (.split 33 0 (.step 43 (.split 36 0 (.split 38 0 (.step 68 (.step 55 (.step 6 (.close 10)))) (.step 23 (.step 28 (.step 24 (.step 23 (.step 12 (.close 16))))))) (.step 23 (.step 28 (.step 4 (.step 20 (.step 13 (.close 19)))))))) (.step 24 (.step 34 (.step 56 (.step 4 (.step 6 (.close 19)))))))))) (.step 14 (.split 25 0 (.step 10 (.step 23 (.step 24 (.step 40 (.step 16 (.close 21)))))) (.step 23 (.step 8 (.step 6 (.close 16))))))) (.split 31 0 (.split 33 0 (.split 25 0 (.split 27 0 (.step 23 (.close 8)) (.step 8 (.close 10))) (.step 8 (.close 7))) (.step 10 (.step 8 (.close 7)))) (.step 24 (.step 43 (.step 14 (.step 5 (.step 8 (.step 6 (.close 7)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case265
