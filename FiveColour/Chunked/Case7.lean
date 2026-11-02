module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.Chunked.Case7
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859317986157849565251358925870694205595654923255086579712⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨2147483648, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168959310607092057633030929658991617421751496872407304280407996866271388498919424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 38 0 (.step 55 (.step 40 (.split 43 0 (.step 40 (.step 3 (.step 12 (.step 15 (.close 16))))) (.step 3 (.step 4 (.close 9)))))) (.step 40 (.step 43 (.step 3 (.step 5 (.step 21 (.close 12))))))) (.step 3 (.step 18 (.step 31 (.step 3 (.step 18 (.step 11 (.step 3 (.close 21))))))))) (.step 29 (.step 3 (.close 5)))) (.step 29 (.step 27 (.close 3)))) (.split 24 0 (.step 18 (.step 3 (.step 40 (.split 25 0 (.step 18 (.step 40 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 15)))))))) (.step 18 (.split 25 0 (.step 3 (.step 18 (.step 11 (.step 23 (.close 27))))) (.step 3 (.close 5)))))) (.step 18 (.step 43 (.split 24 0 (.split 25 0 (.step 9 (.step 3 (.step 18 (.step 15 (.step 3 (.close 21)))))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 23 (.close 3))))))) (.step 18 (.split 22 0 (.split 24 0 (.step 18 (.step 3 (.step 40 (.split 25 0 (.step 18 (.step 40 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 15)))))))) (.step 18 (.split 25 0 (.step 3 (.step 18 (.step 11 (.step 23 (.close 27))))) (.step 3 (.close 5))))) (.step 7 (.close 18))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168959310607092057633030929658993078924782624350233671911586695541331567025586176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.step 18 (.split 17 0 (.split 22 0 (.split 24 0 (.step 18 (.step 3 (.step 40 (.split 25 0 (.step 18 (.step 40 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 15)))))))) (.step 18 (.split 25 0 (.step 3 (.step 18 (.step 11 (.step 23 (.close 27))))) (.step 3 (.close 5))))) (.step 7 (.close 18))) (.step 7 (.close 18)))))) (.run (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 40 (.split 38 0 (.split 39 0 (.split 54 0 (.step 31 (.step 3 (.step 40 (.close 3)))) (.step 9 (.step 15 (.step 5 (.step 3 (.close 17)))))) (.step 11 (.step 23 (.step 40 (.close 3))))) (.step 3 (.step 5 (.step 12 (.close 17)))))) (.step 5 (.step 3 (.close 29)))) (.split 25 0 (.split 30 0 (.step 29 (.close 27)) (.step 3 (.step 11 (.step 18 (.step 23 (.close 27)))))) (.step 18 (.step 27 (.close 5))))) (.step 18 (.step 11 (.step 18 (.step 3 (.step 23 (.step 17 (.step 27 (.step 3 (.close 7)))))))))) (.step 3 (.step 18 (.step 15 (.step 17 (.step 3 (.close 21))))))) (.step 18 (.step 11 (.step 23 (.split 22 0 (.step 18 (.step 3 (.step 17 (.step 27 (.step 3 (.close 7)))))) (.step 7 (.step 17 (.close 18)))))))) (.split 17 0 (.step 18 (.step 11 (.step 23 (.step 67 (.split 25 0 (.step 18 (.step 3 (.step 17 (.step 7 (.step 3 (.close 15)))))) (.step 3 (.close 5))))))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 18)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168959310607092057633030929658993078924782625679461667696502568445138627305930752⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 21 0 (.split 17 0 (.split 24 0 (.split 22 0 (.split 25 0 (.step 9 (.split 34 0 (.split 30 0 (.step 40 (.split 38 0 (.step 55 (.step 3 (.close 5))) (.step 21 (.step 3 (.step 5 (.close 12)))))) (.step 3 (.step 18 (.step 31 (.step 15 (.close 17)))))) (.step 15 (.step 3 (.step 15 (.close 5)))))) (.step 29 (.close 3))) (.step 3 (.step 18 (.step 23 (.step 26 (.step 3 (.close 4))))))) (.step 29 (.step 3 (.close 5)))) (.step 3 (.step 18 (.step 22 (.step 3 (.step 4 (.close 15))))))) (.step 18 (.step 9 (.step 43 (.split 24 0 (.step 68 (.step 15 (.step 3 (.step 4 (.close 17))))) (.step 3 (.step 4 (.step 15 (.step 17 (.close 21)))))))))) (.step 3 (.step 18 (.step 21 (.close 3))))) (.step 40 (.split 16 0 (.step 55 (.split 17 0 (.split 24 0 (.split 25 0 (.step 15 (.step 9 (.step 23 (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 12 (.step 15 (.close 5)))))) (.step 23 (.step 3 (.close 5)))) (.step 3 (.step 4 (.step 15 (.close 17)))))) (.step 3 (.close 17)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1152921506754330624, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168959310607092057633030929658993078924782624350233671911586696694253071632433152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 55 (.split 36 0 (.split 17 0 (.step 40 (.close 9)) (.step 3 (.step 4 (.close 9)))) (.step 9 (.step 3 (.close 5))))) (.step 9 (.step 3 (.close 5)))) (.step 9 (.step 5 (.step 3 (.close 11))))) (.step 3 (.step 9 (.step 18 (.step 9 (.step 3 (.close 4))))))) (.step 29 (.step 3 (.close 5)))) (.step 29 (.step 3 (.close 5)))) (.step 18 (.step 9 (.close 3)))) (.step 3 (.step 18 (.step 11 (.step 21 (.close 3)))))) (.step 40 (.split 16 0 (.step 55 (.split 17 0 (.split 24 0 (.split 21 0 (.split 25 0 (.step 15 (.step 9 (.step 11 (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 9 (.step 5 (.close 12)))))) (.step 3 (.step 4 (.close 9)))) (.step 11 (.step 3 (.close 5)))) (.step 3 (.step 4 (.close 11))))) (.step 3 (.close 11))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1152921506754330624, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168959310607092057633030929658993078924782625679462935347102797827461628615983104⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.step 9 (.step 3 (.close 4))) (.step 9 (.close 3))) (.step 9 (.close 3))) (.step 3 (.step 9 (.close 3)))) (.step 9 (.step 5 (.close 3)))) (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.split 56 0 (.split 65 0 (.split 16 0 (.step 9 (.step 3 (.close 4))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9))))) (.step 40 (.split 24 0 (.split 25 0 (.step 55 (.step 15 (.close 3))) (.step 3 (.step 5 (.close 9)))) (.step 11 (.close 9))))))) (.run (.step 3 (.step 18 (.step 31 (.split 12 0 (.split 14 0 (.split 16 0 (.step 18 (.step 9 (.step 18 (.step 9 (.step 3 (.close 12)))))) (.step 3 (.close 7))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 18 (.close 9))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168959310607092057633030929658993078924782625679462935347102797827461628615983104⟩
def references : Fin 2 → Box := ![Part2.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 6 0 (.split 10 0 (.reuse 0) (.run (.split 12 0 (.split 14 0 (.split 16 0 (.step 18 (.split 17 0 (.split 22 0 (.step 3 (.split 24 0 (.step 18 (.split 25 0 (.split 30 0 (.step 31 (.step 3 (.step 18 (.step 11 (.step 3 (.close 21)))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 4 (.close 12)))))) (.step 31 (.step 3 (.step 31 (.close 21)))))) (.step 7 (.close 3))) (.step 7 (.close 3)))) (.step 7 (.step 3 (.close 4)))) (.step 3 (.step 31 (.split 16 0 (.split 17 0 (.step 3 (.step 18 (.step 3 (.step 15 (.split 22 0 (.split 30 0 (.step 27 (.step 3 (.step 15 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.close 7))))))) (.step 3 (.step 7 (.step 3 (.close 4))))) (.step 3 (.step 7 (.step 3 (.step 4 (.step 12 (.close 17)))))))))) (.step 3 (.step 18 (.step 31 (.split 14 0 (.split 16 0 (.step 18 (.step 29 (.step 15 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.step 4 (.close 15)))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396462067592797657080971249983993023962637889321478361450442531251940540790713205229865500968930113649556510144425306236380197683200, 11567166695907501132681281905800300230278306584820557911959530162423469315261452563348252189224843330073525373204673242299452592961899835370325349684531872718027903426286261608011675267090736287713602175010480579817642131456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 0 (.split 6 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 23 (.split 22 0 (.split 24 0 (.split 25 0 (.step 11 (.step 23 (.step 40 (.split 34 0 (.step 40 (.close 3)) (.step 3 (.step 5 (.step 17 (.step 3 (.step 15 (.close 21)))))))))) (.step 5 (.step 3 (.step 12 (.close 21))))) (.step 11 (.step 23 (.step 27 (.step 3 (.close 5)))))) (.step 11 (.step 18 (.step 3 (.step 23 (.step 31 (.close 77)))))))) (.step 11 (.step 18 (.step 23 (.step 77 (.step 3 (.close 5))))))) (.step 11 (.step 18 (.step 77 (.step 18 (.step 42 (.step 3 (.step 18 (.step 7 (.close 18)))))))))) (.step 11 (.step 77 (.step 17 (.step 23 (.step 18 (.step 27 (.step 5 (.close 3))))))))) (.step 23 (.split 14 0 (.split 16 0 (.step 40 (.step 23 (.close 3))) (.step 3 (.step 17 (.step 18 (.close 15))))) (.step 11 (.step 17 (.close 3)))))) (.step 3 (.step 31 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 31 (.split 22 0 (.step 23 (.split 24 0 (.step 3 (.step 11 (.step 17 (.step 3 (.step 19 (.close 21)))))) (.step 11 (.step 17 (.step 3 (.close 27)))))) (.step 3 (.close 7)))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 3 (.step 4 (.step 12 (.close 17))))))) (.step 3 (.step 7 (.step 17 (.step 3 (.step 4 (.step 12 (.close 18)))))))) (.step 3 (.step 4 (.step 15 (.close 17)))))))) (.step 11 (.step 3 (.step 5 (.close 9))))) (.step 11 (.step 23 (.step 43 (.step 58 (.step 3 (.close 5))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567172211559764234668580634528507661192102192933666997071883059692865531460339987564072317884845273882113206989566793635383409608964026539057669267643373669094517548934877785191598260512752875025179760474073311916334252032⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 72 1 (.split 74 1 (.split 2 0 (.reuse 0) (.run (.split 6 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 43 (.step 3 (.step 5 (.step 12 (.step 5 (.close 15)))))) (.step 5 (.step 3 (.step 12 (.close 21))))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.step 7 (.step 3 (.close 5))))) (.step 3 (.step 7 (.step 3 (.close 5))))) (.step 23 (.split 30 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 40 (.close 5)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 12)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.step 12 (.step 17 (.close 21)))))) (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 29 (.step 23 (.step 12 (.step 5 (.close 15)))))))) (.step 3 (.step 7 (.step 3 (.close 5))))) (.step 3 (.step 31 (.split 12 0 (.step 3 (.step 5 (.close 9))) (.step 9 (.step 3 (.close 5))))))))) (.reuse 1)) (.run (.step 29 (.split 74 1 (.split 2 0 (.split 14 0 (.step 75 (.split 6 0 (.split 10 0 (.step 75 (.step 31 (.split 16 0 (.step 75 (.step 18 (.step 23 (.close 3)))) (.step 3 (.step 18 (.close 15)))))) (.step 3 (.step 18 (.split 16 0 (.step 75 (.close 3)) (.step 3 (.close 7)))))) (.step 9 (.step 11 (.step 26 (.step 3 (.close 5))))))) (.step 40 (.step 3 (.step 18 (.step 69 (.step 18 (.step 9 (.close 12)))))))) (.step 3 (.step 31 (.step 40 (.step 3 (.step 31 (.close 5))))))) (.step 23 (.step 40 (.close 69)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579557027741696, 5783586113859450862115041468379996006203985526872075099498853040142911995424099761541233160871006829425377118720618177416182575918712789333774384115153489417205159021283808032314452051173943151008893565282478829901449265152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 21 0 (.split 17 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 55 (.step 3 (.close 5))) (.step 3 (.step 23 (.step 5 (.close 12))))) (.step 3 (.step 31 (.close 21)))) (.step 29 (.step 40 (.step 55 (.close 3))))) (.step 29 (.step 31 (.step 66 (.step 3 (.step 31 (.close 17))))))) (.step 3 (.step 18 (.step 31 (.step 38 (.close 3)))))) (.step 29 (.step 18 (.close 5)))) (.step 29 (.step 11 (.step 18 (.step 27 (.close 3)))))) (.step 3 (.step 18 (.step 51 (.step 18 (.step 22 (.step 3 (.step 4 (.close 5))))))))) (.step 18 (.step 22 (.step 29 (.step 23 (.step 4 (.close 15))))))) (.step 18 (.step 3 (.step 67 (.step 18 (.step 3 (.step 18 (.step 15 (.step 3 (.close 21)))))))))) (.step 74 (.step 11 (.step 18 (.step 17 (.step 3 (.close 5))))))) (.split 21 0 (.split 24 0 (.step 66 (.split 30 0 (.split 25 0 (.step 40 (.step 55 (.step 18 (.step 5 (.close 15))))) (.step 22 (.close 29))) (.step 3 (.step 18 (.step 22 (.step 3 (.step 15 (.step 3 (.close 4))))))))) (.step 23 (.step 29 (.step 3 (.step 12 (.step 14 (.close 17))))))) (.step 3 (.step 18 (.step 22 (.step 23 (.step 15 (.close 4)))))))) (.step 3 (.step 18 (.step 31 (.step 66 (.step 3 (.step 29 (.step 3 (.close 15))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11567172216946143397854115105943281301261353946457214955162813091819105176202721713564283079729239807030363781045997353744109904547095925163245884423486255994242043539289026824427125529061016563098726222959877601693774381056⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 71 1 (.reuse 0) (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.reuse 1) (.run (.split 10 0 (.split 12 0 (.split 21 0 (.split 24 0 (.split 30 0 (.step 47 (.split 14 0 (.split 34 0 (.split 35 0 (.step 22 (.step 11 (.step 3 (.close 9)))) (.step 21 (.step 74 (.close 3)))) (.step 31 (.close 9))) (.step 11 (.step 3 (.step 9 (.close 12)))))) (.step 3 (.step 9 (.step 11 (.step 3 (.step 15 (.close 21))))))) (.step 11 (.step 3 (.step 9 (.step 15 (.close 21)))))) (.step 3 (.step 11 (.close 9)))) (.step 22 (.step 29 (.step 66 (.step 9 (.close 3)))))) (.step 3 (.step 11 (.step 9 (.step 3 (.step 12 (.close 15))))))))) (.run (.split 6 0 (.split 10 0 (.split 12 0 (.split 21 0 (.step 58 (.split 25 0 (.split 30 0 (.split 14 0 (.step 40 (.step 43 (.close 74))) (.step 11 (.step 23 (.step 43 (.step 49 (.step 18 (.close 5))))))) (.step 3 (.close 5))) (.step 5 (.step 18 (.step 29 (.close 5)))))) (.step 3 (.step 5 (.step 12 (.close 18))))) (.step 3 (.step 22 (.step 23 (.close 15))))) (.step 3 (.close 5))) (.step 3 (.step 11 (.step 9 (.step 15 (.close 21)))))))) (.run (.step 11 (.step 69 (.step 74 (.step 3 (.close 15))))))) (.run (.step 29 (.step 69 (.step 74 (.step 31 (.close 3))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748386640691200, 5783586108473071698929506996969784806752355968567168313013623299341565579188966595471601591544511571444335222050693530118773452380359533019159763366621295796779008468927911654398646996813931457609707367746757414316255739904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 30 0 (.split 42 0 (.step 55 (.step 3 (.close 5))) (.step 3 (.step 23 (.step 5 (.close 12))))) (.step 3 (.step 4 (.close 21)))) (.step 3 (.step 31 (.close 21)))) (.step 21 (.step 29 (.step 40 (.step 3 (.step 5 (.step 12 (.close 21)))))))) (.step 29 (.step 31 (.step 66 (.step 3 (.step 31 (.close 17))))))) (.step 29 (.step 18 (.close 5)))) (.step 29 (.step 11 (.step 18 (.step 27 (.close 3)))))) (.step 3 (.step 18 (.close 67)))) (.step 18 (.step 21 (.step 23 (.close 4))))) (.step 18 (.step 3 (.step 51 (.close 67))))) (.step 67 (.step 3 (.step 4 (.close 5))))) (.split 21 0 (.split 24 0 (.step 66 (.split 30 0 (.split 25 0 (.step 40 (.step 55 (.step 18 (.step 5 (.close 15))))) (.step 21 (.step 3 (.step 5 (.close 22))))) (.step 3 (.step 18 (.step 21 (.close 3)))))) (.step 23 (.step 29 (.step 3 (.step 12 (.step 14 (.close 17))))))) (.step 3 (.step 18 (.step 21 (.step 23 (.step 4 (.close 15)))))))) (.step 3 (.step 18 (.step 31 (.step 66 (.step 3 (.step 29 (.step 3 (.close 15))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748386640691200, 11567172216946143397859013993930440276761051895965817490610133931617286262093729057958571730942313403664872514023366867554099341909929416397322129741445905408236910208876297454578207448152596981238623051081169043742790778880⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.reuse 0) (.run (.split 10 0 (.split 12 0 (.split 21 0 (.split 24 0 (.split 30 0 (.step 47 (.split 14 0 (.split 34 0 (.step 21 (.step 40 (.step 9 (.step 11 (.step 3 (.close 9)))))) (.step 31 (.close 9))) (.step 11 (.step 3 (.step 9 (.close 12)))))) (.step 3 (.step 9 (.step 11 (.step 3 (.step 15 (.close 21))))))) (.step 11 (.step 3 (.step 9 (.step 15 (.close 21)))))) (.step 3 (.step 11 (.close 9)))) (.step 21 (.step 29 (.step 66 (.step 9 (.close 3)))))) (.step 3 (.step 11 (.step 9 (.step 3 (.step 12 (.close 15))))))))) (.run (.split 6 0 (.split 10 0 (.split 12 0 (.split 21 0 (.step 58 (.split 25 0 (.split 30 0 (.split 14 0 (.step 40 (.step 43 (.close 67))) (.step 11 (.step 23 (.step 43 (.step 49 (.step 18 (.close 5))))))) (.step 3 (.close 5))) (.step 5 (.step 18 (.step 29 (.close 5)))))) (.step 3 (.step 5 (.step 12 (.close 18))))) (.step 3 (.step 21 (.step 5 (.step 23 (.close 15)))))) (.step 3 (.close 5))) (.step 3 (.step 11 (.step 9 (.step 15 (.close 21)))))))) (.run (.step 11 (.step 67 (.step 3 (.step 15 (.close 17))))))) (.run (.step 29 (.step 67 (.step 31 (.step 21 (.step 3 (.step 5 (.close 9))))))))) (.run (.step 67 (.close 3)))) (.run (.step 3 (.step 53 (.step 3 (.step 12 (.step 18 (.close 27)))))))) (.run (.step 3 (.step 63 (.step 3 (.close 67))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630615804215296, 5783586108473071698929506996965226821643149420023545345677069199707419316725182145462829605269305557288032021888197876987935883101088487039966611922598996436495837499130829161693494823850472676506245682514685453934134296576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 21 0 (.split 17 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 34 0 (.split 42 0 (.step 55 (.step 3 (.close 5))) (.step 3 (.step 23 (.step 5 (.close 12))))) (.step 3 (.step 31 (.close 15)))) (.step 29 (.step 31 (.step 3 (.step 31 (.close 21)))))) (.step 29 (.step 66 (.step 3 (.close 5))))) (.step 3 (.step 18 (.step 31 (.step 38 (.close 3)))))) (.step 29 (.step 18 (.close 5)))) (.step 29 (.step 11 (.step 18 (.step 27 (.close 3)))))) (.step 3 (.step 18 (.step 51 (.step 18 (.step 40 (.step 3 (.close 5)))))))) (.step 18 (.step 31 (.step 23 (.close 4))))) (.step 18 (.step 3 (.step 66 (.close 3))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 25 0 (.split 38 0 (.split 40 0 (.step 15 (.step 40 (.step 11 (.step 12 (.step 3 (.close 17)))))) (.step 11 (.step 12 (.step 3 (.step 15 (.step 17 (.step 27 (.close 31)))))))) (.step 12 (.step 3 (.close 5)))) (.step 29 (.close 12))) (.step 3 (.step 12 (.step 3 (.step 15 (.close 17)))))) (.step 3 (.step 12 (.step 18 (.step 15 (.close 17)))))) (.step 11 (.step 12 (.step 3 (.step 12 (.step 15 (.close 18))))))) (.step 11 (.step 18 (.step 3 (.step 17 (.step 15 (.close 18))))))) (.step 11 (.step 18 (.step 66 (.step 3 (.close 15))))))) (.split 21 0 (.split 24 0 (.step 66 (.step 3 (.close 5))) (.step 23 (.step 29 (.step 3 (.step 12 (.step 14 (.close 17))))))) (.step 3 (.step 18 (.step 15 (.close 3)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630615804215296, 11567172216946143397859013989253943099206717443533634799036481515292474008207419239036706606338249618286883670078816495634273459257328645414768305211278372413265290728868489770477507946419095654857900657192463311996850274304⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 10 0 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.close 66)))))) (.run (.split 10 0 (.split 12 0 (.split 21 0 (.split 24 0 (.split 30 0 (.step 47 (.split 14 0 (.split 16 0 (.split 17 0 (.split 34 0 (.split 38 0 (.step 40 (.step 9 (.step 11 (.step 3 (.close 9))))) (.step 12 (.step 21 (.close 31)))) (.step 9 (.step 11 (.close 15)))) (.step 3 (.step 11 (.step 9 (.close 15))))) (.step 3 (.step 11 (.step 9 (.close 15))))) (.step 11 (.step 3 (.step 9 (.close 12)))))) (.step 3 (.step 9 (.step 11 (.step 3 (.step 15 (.close 21))))))) (.step 11 (.step 3 (.step 9 (.step 15 (.close 21)))))) (.step 3 (.step 11 (.close 9)))) (.step 29 (.step 66 (.step 3 (.close 5))))) (.step 3 (.step 11 (.step 9 (.step 3 (.close 12)))))))) (.run (.split 6 0 (.split 10 0 (.split 12 0 (.split 21 0 (.step 58 (.split 25 0 (.split 30 0 (.split 14 0 (.step 40 (.step 43 (.step 66 (.close 5)))) (.step 11 (.step 23 (.step 12 (.step 3 (.close 5)))))) (.step 3 (.close 5))) (.step 5 (.step 18 (.step 29 (.close 5)))))) (.step 3 (.step 5 (.step 12 (.close 18))))) (.step 3 (.step 12 (.step 23 (.step 15 (.close 21)))))) (.step 3 (.close 5))) (.step 3 (.step 11 (.step 9 (.step 15 (.close 21)))))))) (.run (.step 11 (.step 66 (.step 34 (.step 3 (.close 18))))))) (.run (.step 29 (.step 66 (.step 31 (.step 3 (.step 5 (.close 9)))))))) (.run (.step 66 (.close 3)))) (.run (.step 3 (.step 52 (.step 3 (.step 53 (.step 3 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨8104522595470689372094546608771799123071184047348509570304018222052056272290836223436927829974812098219136497287696853871865529444163623648216552410378835326291370709770720772096, 5783586108473071698929506996965222366134733777400788439143267694063945655067617597076614422700867081429135655690215753452874192699044805696992218068878855735906059966862423715160736606733955666857114165714130493511592574976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 55 (.split 25 0 (.step 55 (.step 7 (.step 9 (.step 3 (.step 5 (.step 16 (.close 21))))))) (.step 9 (.step 5 (.step 18 (.step 26 (.step 3 (.step 5 (.step 28 (.close 12)))))))))) (.step 27 (.step 18 (.step 5 (.step 3 (.step 15 (.step 17 (.close 21)))))))) (.step 27 (.step 3 (.step 18 (.step 23 (.step 26 (.step 3 (.close 7)))))))) (.step 3 (.step 9 (.step 18 (.step 23 (.step 3 (.close 7))))))) (.step 18 (.step 27 (.step 18 (.step 23 (.step 55 (.close 3))))))) (.step 18 (.step 27 (.step 18 (.step 23 (.step 53 (.step 18 (.close 7)))))))) (.step 27 (.step 23 (.step 52 (.step 55 (.step 3 (.close 7))))))) (.step 9 (.split 14 0 (.split 16 0 (.split 17 0 (.step 26 (.split 21 0 (.split 25 0 (.split 24 0 (.step 26 (.step 40 (.step 55 (.step 3 (.step 5 (.close 15)))))) (.step 27 (.step 5 (.step 3 (.close 15))))) (.step 3 (.step 5 (.step 15 (.step 27 (.step 16 (.close 21))))))) (.step 3 (.step 15 (.step 18 (.step 3 (.step 4 (.step 17 (.close 21))))))))) (.step 3 (.step 18 (.step 17 (.step 15 (.close 21)))))) (.step 18 (.step 3 (.step 17 (.step 4 (.step 15 (.close 21))))))) (.step 15 (.close 17))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨8104522595470689372094546608771799123071184047348509570304018222052056272290836223436927829974812098219136497287696853871865529444163623648216552410378835326291370709770720772096, 11567172216946143397859013993930444732269467546693096992614624809355306532523092729415970960859261449827787102273405263379997255748900927715108621814302543396523541613010232345274589313485666401266589894173094713933905788928⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.step 3 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 10 0 (.reuse 0) (.run (.step 18 (.step 31 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 18 (.step 52 (.step 3 (.close 7)))) (.step 3 (.step 18 (.step 27 (.close 3))))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 4 (.close 17))))))) (.step 3 (.step 15 (.step 11 (.step 17 (.close 3)))))))))) (.run (.step 9 (.step 62 (.step 3 (.step 9 (.step 4 (.close 11)))))))) (.run (.step 3 (.step 9 (.step 27 (.step 31 (.step 3 (.step 26 (.step 3 (.step 40 (.close 5))))))))))) (.run (.step 23 (.step 27 (.step 44 (.step 55 (.close 3))))))) (.run (.step 9 (.step 23 (.step 26 (.step 29 (.step 40 (.close 3)))))))) (.run (.step 55 (.step 22 (.step 23 (.step 15 (.close 21))))))) (.run (.step 3 (.step 26 (.step 44 (.step 62 (.step 7 (.close 3)))))))) (.run (.step 3 (.step 55 (.step 23 (.close 67)))))) (.run (.step 3 (.step 55 (.step 23 (.close 66)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546693096992614624809355306532523092729415970960859261449827787102273405263379997255748900927715108621814302543396523541613010232345274589313485666401266589894173094713933905788928⟩
def references : Fin 4 → Box := ![Part9.root, Part11.root, Part13.root, Part15.root]
def proof : Chunks.Proof 4 := (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.reuse 0) (.run (.split 71 1 (.split 72 1 (.split 74 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 35 0 (.split 38 0 (.split 2 0 (.step 7 (.close 3)) (.step 3 (.step 4 (.close 7)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 12))))) (.run (.step 3 (.split 71 1 (.step 43 (.split 72 1 (.split 74 1 (.step 68 (.split 2 0 (.step 18 (.step 63 (.step 3 (.close 9)))) (.step 3 (.close 5)))) (.step 3 (.close 18))) (.step 3 (.step 9 (.step 26 (.step 15 (.close 21))))))) (.step 63 (.close 74)))))) (.reuse 1)) (.split 64 1 (.split 65 1 (.reuse 2) (.run (.step 3 (.step 63 (.step 3 (.close 66)))))) (.run (.step 66 (.close 3))))) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part11.excludes
  · exact Part13.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416710905856000, 5783586108473071698929506996965222366134733773352484427831492680561640391018032390581584500612231685715751553561673972909160590855305953126566057679144169834873891260359280833627832801985160201416977393483340248478389370880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 14 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 40 (.step 27 (.step 18 (.step 55 (.close 3))))) (.step 27 (.close 5))) (.step 27 (.step 18 (.step 23 (.step 31 (.close 21)))))) (.step 3 (.step 18 (.step 22 (.step 3 (.step 23 (.close 3))))))) (.step 18 (.step 27 (.step 18 (.step 23 (.step 31 (.step 18 (.close 21)))))))) (.step 27 (.step 61 (.step 3 (.step 5 (.close 15)))))) (.step 18 (.step 27 (.step 18 (.step 31 (.step 18 (.close 21))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 43 0 (.step 22 (.step 27 (.step 34 (.step 5 (.step 3 (.close 21)))))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.step 15 (.step 21 (.close 22)))))) (.step 3 (.step 4 (.step 17 (.step 15 (.close 21)))))) (.step 3 (.step 5 (.step 12 (.step 15 (.close 21)))))) (.step 3 (.step 4 (.step 17 (.step 15 (.close 21)))))) (.step 3 (.step 4 (.step 15 (.step 17 (.step 18 (.close 21))))))) (.step 3 (.step 4 (.step 17 (.step 18 (.step 15 (.close 21))))))) (.step 3 (.step 17 (.step 18 (.step 15 (.close 21)))))) (.step 23 (.step 27 (.step 34 (.step 18 (.step 5 (.close 3)))))))) (.step 3 (.step 18 (.step 31 (.step 18 (.step 27 (.step 31 (.step 15 (.close 21))))))))) (.step 27 (.split 10 0 (.split 12 0 (.step 31 (.step 40 (.close 61))) (.step 3 (.step 5 (.step 12 (.step 15 (.close 21)))))) (.step 3 (.close 5))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416710905856000, 11567172216946143397859013993930440276761051895969774777033703604162254302430043412999133832527932793103497522920853223155803851784654478814302018461279468151053168438305919295127115467512077719720253341767834752097169965056⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 64 1 (.split 65 1 (.split 67 1 (.step 40 (.split 74 1 (.split 6 0 (.split 71 1 (.reuse 0) (.run (.step 11 (.split 2 0 (.split 10 0 (.step 51 (.step 74 (.step 3 (.close 5)))) (.step 17 (.step 3 (.step 18 (.step 22 (.close 27)))))) (.step 22 (.step 27 (.step 31 (.step 18 (.close 5))))))))) (.run (.step 11 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 40 (.step 3 (.close 5))) (.step 27 (.step 5 (.close 9)))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 4 (.close 11)))) (.step 3 (.close 11))) (.step 11 (.step 3 (.close 5)))) (.step 22 (.split 21 0 (.split 30 0 (.step 34 (.step 27 (.step 9 (.close 3)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 4 (.step 9 (.close 11))))))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 3 (.step 5 (.step 9 (.close 11)))))))) (.run (.step 11 (.step 27 (.step 61 (.step 3 (.step 18 (.step 5 (.close 15)))))))))) (.run (.step 3 (.step 27 (.step 31 (.close 3)))))) (.run (.step 3 (.step 18 (.step 24 (.step 18 (.step 12 (.step 21 (.close 27))))))))) (.run (.step 11 (.step 40 (.step 55 (.step 74 (.step 77 (.split 65 1 (.split 2 0 (.split 10 0 (.step 51 (.step 74 (.step 42 (.step 23 (.step 27 (.step 40 (.step 3 (.step 5 (.close 3))))))))) (.step 17 (.step 3 (.step 18 (.step 23 (.close 27)))))) (.step 23 (.step 27 (.step 31 (.step 18 (.close 5)))))) (.step 3 (.step 18 (.close 12)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087300938137600, 5783586108473071698929506996965222366134733773348527145181885432838213702923272616529291289943533516693566973040393917553080243372729742795712894136969374633526008061693503892849509412550472095496781354229370583773404463104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 43 0 (.split 30 0 (.split 40 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 24 0 (.step 29 (.step 31 (.close 3))) (.step 5 (.step 3 (.step 15 (.step 21 (.close 28)))))) (.step 3 (.step 5 (.step 3 (.step 15 (.close 21)))))) (.step 3 (.step 5 (.step 22 (.step 15 (.close 21)))))) (.step 3 (.step 5 (.step 7 (.step 22 (.step 16 (.step 12 (.close 21)))))))) (.step 5 (.step 4 (.step 15 (.step 21 (.close 28)))))) (.step 3 (.step 5 (.step 7 (.step 15 (.step 21 (.close 28))))))) (.step 3 (.step 5 (.step 7 (.step 9 (.close 15)))))) (.step 5 (.step 7 (.step 3 (.step 5 (.step 3 (.step 15 (.step 21 (.close 28))))))))) (.step 3 (.step 5 (.step 4 (.step 15 (.close 21)))))) (.step 5 (.step 7 (.step 3 (.step 5 (.step 3 (.step 15 (.step 21 (.close 28))))))))) (.step 5 (.step 7 (.step 18 (.step 3 (.step 4 (.step 15 (.step 21 (.close 28))))))))) (.step 5 (.step 18 (.step 5 (.step 18 (.step 29 (.step 5 (.close 12)))))))) (.step 48 (.split 30 0 (.step 22 (.split 40 0 (.split 43 0 (.split 49 0 (.step 31 (.step 3 (.step 5 (.step 15 (.close 21))))) (.step 3 (.step 5 (.step 15 (.step 12 (.close 16)))))) (.step 3 (.close 9))) (.step 4 (.step 5 (.close 15))))) (.step 3 (.step 4 (.step 15 (.close 21))))))) (.step 3 (.step 7 (.step 3 (.step 5 (.step 3 (.step 12 (.step 15 (.close 28))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087300938137600, 11567172216946143397859013993930444732269467542640835698653242548129574580378747748868647828101927885092218419623583427480203306422585864813829297882393062294143489707841312522963362119302182828638606482460105402699014471680⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.reuse 0) (.run (.step 48 (.split 10 0 (.split 25 0 (.step 22 (.split 30 0 (.step 22 (.split 40 0 (.split 43 0 (.split 49 0 (.step 31 (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.close 9))) (.step 4 (.step 5 (.close 9))))) (.step 3 (.step 4 (.close 9))))) (.step 29 (.step 3 (.close 5)))) (.step 3 (.step 4 (.step 9 (.step 12 (.close 15))))))))) (.run (.step 5 (.step 3 (.step 28 (.step 15 (.close 9))))))) (.run (.step 5 (.step 18 (.step 12 (.close 17)))))) (.run (.step 5 (.step 29 (.split 2 0 (.step 75 (.split 6 0 (.split 10 0 (.split 12 0 (.split 21 0 (.split 30 0 (.step 31 (.step 48 (.step 59 (.close 3)))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 4 (.close 15)))) (.step 22 (.step 26 (.step 3 (.step 5 (.step 12 (.step 3 (.step 4 (.close 5))))))))) (.step 3 (.step 4 (.close 12)))) (.step 9 (.step 22 (.step 3 (.close 5)))))) (.step 3 (.step 5 (.step 31 (.close 37))))))))) (.run (.step 51 (.step 63 (.close 74))))) (.run (.step 3 (.close 7)))) (.run (.step 3 (.step 5 (.step 18 (.step 22 (.step 3 (.step 10 (.step 28 (.step 24 (.step 3 (.step 4 (.close 15))))))))))))) (.run (.step 3 (.step 51 (.step 63 (.step 50 (.step 67 (.step 3 (.close 5))))))))) (.run (.step 18 (.step 51 (.step 63 (.step 49 (.step 66 (.step 74 (.step 5 (.step 28 (.step 5 (.close 3))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨7371020360979572953596786290992712677572111758625860211672277930167234692172165726730716260112614780354430419981960634569864423105321860610471551272329484462400208896, 11567172216946143397859013993930444732269467546697054282815842416902305711577760058590298309700588115562165469652934058192409545361860925081580593841851181070985390083194679402879014174322600702614890211928621208167806664704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.step 58 (.step 18 (.step 48 (.split 74 1 (.split 6 0 (.split 12 0 (.step 18 (.step 31 (.step 23 (.close 12)))) (.step 40 (.step 9 (.step 18 (.step 29 (.step 40 (.step 15 (.step 12 (.close 21))))))))) (.step 40 (.step 9 (.step 18 (.step 9 (.close 5)))))) (.step 18 (.step 11 (.step 23 (.step 27 (.step 31 (.step 23 (.close 12))))))))))) (.step 18 (.step 74 (.step 31 (.step 58 (.step 29 (.step 31 (.step 40 (.step 9 (.step 12 (.close 15))))))))))) (.step 3 (.step 7 (.step 3 (.step 12 (.close 18)))))) (.step 3 (.step 5 (.close 18)))) (.step 18 (.step 32 (.step 67 (.step 31 (.step 58 (.close 9))))))) (.step 18 (.step 63 (.step 18 (.step 66 (.step 31 (.step 12 (.step 58 (.close 9))))))))) (.step 3 (.step 26 (.step 48 (.step 58 (.step 3 (.close 4))))))) (.step 27 (.step 40 (.step 58 (.step 3 (.step 40 (.step 44 (.step 4 (.close 9)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815842416902305711577760058590298309700588115562165469652934058192409545361860925081580593841851181070985390083194679402879014174322600702614890211928621208167806664704⟩
def references : Fin 4 → Box := ![Part16.root, Part18.root, Part20.root, Part21.root]
def proof : Chunks.Proof 4 := (.split 55 1 (.split 56 1 (.split 58 1 (.reuse 0) (.split 59 1 (.split 63 1 (.reuse 1) (.run (.step 11 (.step 40 (.step 55 (.step 74 (.step 77 (.split 64 1 (.split 65 1 (.split 2 0 (.split 10 0 (.step 51 (.step 74 (.split 16 0 (.split 21 0 (.split 22 0 (.step 23 (.step 27 (.step 34 (.step 40 (.close 3))))) (.step 3 (.step 18 (.step 23 (.close 17))))) (.step 18 (.step 15 (.close 21)))) (.step 18 (.step 21 (.close 17)))))) (.step 12 (.step 3 (.step 17 (.step 18 (.step 23 (.close 27))))))) (.step 12 (.step 23 (.step 27 (.step 18 (.close 5)))))) (.step 3 (.step 18 (.close 12)))) (.step 51 (.close 66)))))))))) (.run (.step 27 (.step 3 (.step 40 (.step 44 (.step 55 (.step 61 (.step 40 (.close 3))))))))))) (.split 58 1 (.split 59 1 (.reuse 2) (.run (.step 3 (.step 22 (.step 5 (.step 26 (.step 31 (.step 48 (.step 5 (.step 9 (.step 7 (.step 22 (.step 26 (.step 3 (.step 15 (.close 16)))))))))))))))) (.run (.step 3 (.step 5 (.step 18 (.step 23 (.step 12 (.step 27 (.step 12 (.close 42))))))))))) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part18.excludes
  · exact Part20.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384264315699200, 5783586108473071698929506996965222366134733773348527141407926607147707985238824283971828547812099392034821186197494097911914170450645427899882424191859490204743352967658165809795023349238523858375098309609972153759700090880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 55 (.split 36 0 (.split 38 0 (.step 55 (.step 3 (.step 7 (.step 4 (.close 5))))) (.step 3 (.step 5 (.close 12)))) (.step 9 (.step 18 (.step 22 (.step 23 (.close 12))))))) (.step 9 (.step 21 (.step 18 (.step 31 (.step 40 (.step 3 (.close 12)))))))) (.step 9 (.step 31 (.step 57 (.step 3 (.close 5)))))) (.step 3 (.step 9 (.step 18 (.step 31 (.step 38 (.close 3))))))) (.step 9 (.step 29 (.step 3 (.close 5))))) (.step 29 (.step 3 (.step 5 (.step 3 (.close 4)))))) (.step 9 (.step 18 (.step 43 (.close 57))))) (.step 40 (.step 55 (.split 24 0 (.step 15 (.step 9 (.step 23 (.step 29 (.step 23 (.step 3 (.close 5))))))) (.step 23 (.close 3)))))) (.step 9 (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.split 58 0 (.split 14 0 (.step 57 (.step 3 (.close 4))) (.step 15 (.close 4))) (.step 22 (.step 15 (.step 27 (.step 40 (.step 3 (.close 4))))))) (.step 15 (.step 3 (.step 31 (.step 3 (.step 5 (.step 17 (.step 3 (.close 21))))))))) (.step 15 (.step 21 (.step 3 (.step 40 (.step 31 (.step 3 (.close 5)))))))) (.step 3 (.step 15 (.step 18 (.step 29 (.step 31 (.step 3 (.step 4 (.step 17 (.close 21)))))))))) (.step 15 (.step 57 (.close 3)))))) (.step 3 (.step 18 (.step 9 (.step 15 (.step 3 (.step 29 (.step 18 (.step 31 (.close 21)))))))))) (.step 9 (.step 11 (.step 3 (.close 5))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384264315699200, 11567172216946143397859013993930444732269467542640835694879283722439068862694299416311185085970493760433472632780683607839037233500501549917998827937283177865360834613805974439908876055990234591516923437839554051180703252480⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.reuse 0) (.run (.step 3 (.step 9 (.step 31 (.split 14 0 (.step 58 (.split 16 0 (.step 3 (.step 40 (.close 5))) (.step 3 (.close 4)))) (.step 3 (.step 5 (.step 12 (.step 17 (.close 21))))))))))) (.run (.step 23 (.step 5 (.step 3 (.step 9 (.close 15))))))) (.run (.step 9 (.step 26 (.step 29 (.step 23 (.step 57 (.step 3 (.step 18 (.close 5)))))))))) (.run (.step 23 (.step 29 (.step 57 (.split 2 0 (.split 10 0 (.step 22 (.step 74 (.step 3 (.close 5)))) (.step 3 (.step 9 (.step 15 (.step 18 (.step 22 (.step 23 (.close 3)))))))) (.step 3 (.step 9 (.step 22 (.step 23 (.close 15))))))))))) (.run (.step 3 (.step 9 (.step 3 (.close 7)))))) (.run (.step 3 (.step 9 (.step 29 (.close 31)))))) (.run (.step 23 (.step 29 (.step 55 (.step 74 (.step 75 (.split 65 1 (.split 2 0 (.split 6 0 (.step 51 (.step 21 (.step 57 (.step 18 (.step 23 (.close 3)))))) (.step 9 (.step 4 (.close 11)))) (.step 3 (.step 9 (.step 21 (.step 23 (.close 15)))))) (.step 3 (.step 9 (.step 21 (.step 24 (.close 15))))))))))))) (.run (.step 23 (.step 29 (.step 55 (.step 74 (.step 75 (.split 65 1 (.split 2 0 (.split 64 1 (.split 6 0 (.step 51 (.step 15 (.step 66 (.step 3 (.step 18 (.step 5 (.close 21))))))) (.step 9 (.step 4 (.close 11)))) (.step 51 (.close 66))) (.step 9 (.step 3 (.step 12 (.step 15 (.step 23 (.close 21))))))) (.step 3 (.step 9 (.step 15 (.step 24 (.step 21 (.close 22))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216826650525696, 11567172216946143397859013989258505539824339642808494558578747699342678706664323423757286213663466991559706337245640968106223752348956667709523694374999031017557203235569383536164112033678115989980433096498389335850620026880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 35 0 (.split 38 0 (.split 2 0 (.step 7 (.close 3)) (.step 3 (.step 4 (.close 7)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 12))) (.step 3 (.split 72 1 (.split 74 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 35 0 (.step 54 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 11 (.close 17))))) (.step 3 (.step 7 (.close 9)))))) (.step 3 (.step 22 (.step 3 (.step 12 (.step 18 (.close 27))))))) (.step 3 (.close 51))) (.step 3 (.step 54 (.step 62 (.step 7 (.close 3)))))) (.step 3 (.step 27 (.step 31 (.step 36 (.step 55 (.step 3 (.step 7 (.step 17 (.step 34 (.close 44))))))))))) (.step 3 (.step 7 (.step 4 (.step 3 (.step 9 (.close 21))))))) (.step 3 (.step 7 (.step 18 (.step 3 (.step 9 (.step 21 (.close 26)))))))) (.step 3 (.step 9 (.step 18 (.step 3 (.step 22 (.step 3 (.step 21 (.close 26))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 5783586108473071698929506996965222366134733773348527141407923008016672353955108643437164269039801993104725696880829663350520870463872258805719965363985161975327725356833816143965608910185750470884953048453838191955833520128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 55 (.split 25 0 (.step 53 (.close 5)) (.step 9 (.step 5 (.step 18 (.step 21 (.step 3 (.step 5 (.step 28 (.close 12)))))))))) (.step 27 (.step 18 (.step 5 (.step 3 (.step 15 (.step 17 (.close 21)))))))) (.step 27 (.step 3 (.step 18 (.step 23 (.step 40 (.close 3))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 3 (.step 4 (.close 22)))))))) (.step 18 (.step 27 (.step 18 (.step 23 (.step 53 (.close 3))))))) (.step 18 (.step 27 (.step 18 (.step 23 (.step 53 (.close 3))))))) (.step 27 (.step 23 (.step 52 (.step 55 (.step 3 (.close 7))))))) (.step 9 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 25 0 (.split 30 0 (.step 21 (.step 40 (.step 53 (.close 3)))) (.step 3 (.step 18 (.step 17 (.step 15 (.close 21)))))) (.step 3 (.step 15 (.step 5 (.step 21 (.step 27 (.step 12 (.close 22)))))))) (.step 3 (.step 15 (.step 18 (.step 3 (.step 4 (.step 17 (.close 21)))))))) (.step 3 (.step 18 (.step 17 (.step 15 (.close 21)))))) (.step 18 (.step 3 (.step 17 (.step 4 (.step 15 (.close 21))))))) (.step 15 (.close 17))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11567172216946143397859013989258505539824339642804537272155174427666671683092310942532784939799300651729453969190035029844781511597097505757373828440546939576750775669458489521821242953753148426805605158242485380281432801280⟩
def references : Fin 1 → Box := ![Part26.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 10 0 (.reuse 0) (.run (.step 18 (.step 31 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 18 (.step 52 (.step 3 (.close 7)))) (.step 3 (.step 18 (.step 27 (.close 3))))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 4 (.close 17))))))) (.step 3 (.step 15 (.step 11 (.step 17 (.close 3)))))))))) (.run (.step 9 (.step 53 (.step 9 (.step 4 (.step 3 (.close 11)))))))) (.run (.step 3 (.step 9 (.step 27 (.step 31 (.step 3 (.step 21 (.step 3 (.step 5 (.close 12))))))))))) (.run (.step 23 (.step 27 (.step 55 (.split 6 0 (.step 23 (.step 44 (.step 7 (.step 3 (.close 17))))) (.step 9 (.close 11)))))))) (.run (.step 9 (.step 23 (.step 29 (.step 38 (.step 40 (.step 18 (.step 26 (.step 3 (.step 12 (.close 15)))))))))))) (.run (.step 55 (.step 22 (.step 23 (.step 15 (.close 21))))))) (.run (.step 3 (.step 53 (.step 7 (.close 3)))))) (.run (.step 3 (.step 55 (.step 23 (.step 32 (.step 23 (.step 66 (.step 23 (.close 18)))))))))) (.run (.step 3 (.step 55 (.step 23 (.close 66)))))) (.run (.step 53 (.step 26 (.step 40 (.close 55)))))) (.run (.step 22 (.step 31 (.step 5 (.step 48 (.step 5 (.step 9 (.step 21 (.step 7 (.step 22 (.close 53)))))))))))) (.run (.step 48 (.step 53 (.step 58 (.step 3 (.close 4)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701360239400566521222005514459608991133244337732938276855205577760809018163865818819535515744071684265878446343490008229545742600951268645562039669882880⟩
def references : Fin 4 → Box := ![Part22.root, Part24.root, Part25.root, Part27.root]
def proof : Chunks.Proof 4 := (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.reuse 1) (.run (.step 9 (.step 3 (.step 26 (.step 55 (.step 57 (.step 18 (.close 23))))))))) (.run (.step 3 (.step 22 (.step 23 (.step 40 (.step 57 (.split 2 0 (.split 10 0 (.step 22 (.split 25 0 (.split 30 0 (.split 38 0 (.step 61 (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.step 9 (.step 21 (.step 12 (.step 15 (.step 12 (.close 17))))))))) (.step 3 (.step 4 (.step 9 (.step 23 (.close 21)))))) (.step 3 (.step 5 (.step 9 (.step 23 (.close 12))))))) (.step 3 (.step 4 (.step 9 (.step 15 (.step 22 (.step 21 (.close 23)))))))) (.step 3 (.step 5 (.step 9 (.step 22 (.step 23 (.close 12)))))))))))))) (.run (.step 3 (.step 5 (.step 22 (.step 9 (.step 31 (.step 48 (.close 57))))))))) (.run (.step 3 (.step 40 (.step 48 (.step 9 (.step 57 (.step 5 (.step 57 (.close 58))))))))))) (.step 3 (.reuse 2))) (.step 55 (.split 51 1 (.split 54 1 (.split 58 1 (.reuse 3) (.run (.step 27 (.step 53 (.step 40 (.step 55 (.step 61 (.step 40 (.step 3 (.step 4 (.close 5))))))))))) (.run (.step 9 (.step 21 (.step 53 (.step 55 (.step 57 (.step 18 (.close 23))))))))) (.run (.step 3 (.step 53 (.step 7 (.close 3))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes
  · exact Part24.excludes
  · exact Part25.excludes
  · exact Part27.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 5783586108473071698929506996965222366134733773348527141407923008016672350684914706056545975071547051840434746961274181805545011439060667436242549619862047087060826480466674771546587560093999843512635229664036342780947070976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 55 (.split 25 0 (.step 55 (.step 7 (.step 9 (.step 3 (.step 5 (.step 16 (.close 21))))))) (.step 9 (.step 5 (.step 18 (.step 27 (.step 7 (.step 16 (.step 28 (.close 12)))))))))) (.step 27 (.step 18 (.step 5 (.step 3 (.step 15 (.step 17 (.close 21)))))))) (.step 27 (.step 3 (.step 18 (.step 23 (.step 40 (.close 3))))))) (.step 3 (.step 9 (.step 18 (.step 23 (.step 3 (.close 7))))))) (.step 18 (.step 27 (.step 18 (.step 23 (.step 55 (.close 3))))))) (.step 18 (.step 27 (.step 18 (.step 23 (.step 53 (.step 17 (.step 18 (.close 7))))))))) (.step 27 (.step 23 (.step 52 (.step 17 (.step 3 (.step 5 (.close 15)))))))) (.step 9 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 25 0 (.split 30 0 (.step 55 (.close 52)) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 15 (.step 5 (.step 12 (.step 16 (.close 12))))))) (.step 3 (.step 15 (.step 17 (.step 4 (.step 3 (.close 7))))))) (.step 3 (.step 17 (.step 7 (.step 3 (.close 4)))))) (.step 18 (.step 3 (.step 12 (.close 17))))) (.step 15 (.close 17))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part29

namespace Part30
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11567172216946143397859013989258505539824339642804537272155174427666671679822117005152166645831045710465163019270479548299805652572285914387896412696423824688483876793091348149402221603661397799433287339452683531106546352128⟩
def references : Fin 1 → Box := ![Part29.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 10 0 (.reuse 0) (.run (.step 18 (.step 31 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 18 (.close 52)) (.step 3 (.step 18 (.step 27 (.close 3))))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 4 (.close 17))))))) (.step 3 (.step 15 (.step 11 (.step 17 (.close 3)))))))))) (.run (.step 9 (.step 52 (.step 3 (.step 9 (.close 4))))))) (.run (.step 3 (.step 9 (.step 27 (.step 31 (.step 3 (.step 40 (.step 3 (.close 5)))))))))) (.run (.step 23 (.step 27 (.step 55 (.split 6 0 (.step 17 (.step 23 (.step 31 (.step 18 (.step 3 (.close 7)))))) (.step 9 (.close 11)))))))) (.run (.step 9 (.step 23 (.step 29 (.step 40 (.step 26 (.step 18 (.step 55 (.step 3 (.close 15))))))))))) (.run (.step 55 (.step 22 (.step 23 (.step 12 (.close 16))))))) (.run (.step 3 (.step 52 (.step 7 (.close 3)))))) (.run (.step 3 (.step 55 (.step 23 (.step 66 (.step 21 (.step 18 (.step 5 (.step 16 (.step 5 (.close 17)))))))))))) (.run (.step 3 (.step 55 (.step 12 (.close 66)))))) (.run (.step 52 (.step 26 (.step 40 (.close 55)))))) (.run (.step 22 (.step 31 (.step 5 (.step 48 (.step 5 (.step 9 (.step 16 (.step 7 (.step 22 (.step 28 (.step 3 (.step 26 (.close 3))))))))))))))) (.run (.step 48 (.step 52 (.step 58 (.step 3 (.close 4)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part29.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part30

namespace Part31
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11567172216946143397859013989258505539824339642808494558578747699342675354712340938108011320159990109792295282263764234192022405162032174343891992563425310129597282817518086651239539818269542129607121320817306299267342663680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 9 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 35 0 (.split 38 0 (.split 2 0 (.step 7 (.close 3)) (.step 3 (.step 4 (.close 7)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.close 11))) (.step 3 (.split 74 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 35 0 (.step 70 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 11)))))) (.step 3 (.close 11))) (.step 3 (.step 11 (.step 3 (.close 9))))) (.step 3 (.step 9 (.step 11 (.step 27 (.close 3)))))) (.step 3 (.step 11 (.step 3 (.step 9 (.close 27)))))) (.step 3 (.step 7 (.step 4 (.step 3 (.close 9)))))) (.step 3 (.step 7 (.step 8 (.step 10 (.step 18 (.step 3 (.close 9))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part31

namespace Part32
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053221884866420150401002711620508869367493974611050361101540739111133558829026907279953980673580689505684930889325640338022285180928⟩
def references : Fin 3 → Box := ![Part28.root, Part30.root, Part31.root]
def proof : Chunks.Proof 3 := (.split 43 1 (.split 49 1 (.reuse 0) (.step 55 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.reuse 1) (.run (.step 27 (.step 52 (.step 40 (.step 55 (.step 61 (.step 34 (.step 18 (.step 5 (.step 23 (.step 3 (.close 5))))))))))))) (.run (.step 9 (.step 52 (.step 55 (.step 57 (.step 23 (.close 3)))))))) (.run (.step 3 (.step 52 (.step 7 (.close 3)))))) (.run (.step 52 (.step 55 (.step 52 (.step 21 (.step 3 (.step 5 (.close 22))))))))))) (.step 3 (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 2) (.run (.step 3 (.step 46 (.step 9 (.split 55 1 (.split 56 1 (.split 58 1 (.split 74 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 35 0 (.step 54 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 11)))) (.step 3 (.step 9 (.step 11 (.close 27))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9))))))))) (.run (.step 3 (.step 9 (.step 27 (.step 46 (.close 3))))))) (.run (.step 3 (.step 9 (.step 27 (.step 46 (.step 3 (.close 7))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part28.excludes
  · exact Part30.excludes
  · exact Part31.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part32

namespace Part33
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11567172216946143397854115110619787389832519696295652639433672250117652706898173668905916742078566996706045864220344043817119715264080003356527954405506568986220201087182465339660184931717822336634330664177869522967651680256⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 55 0 (.step 45 (.split 24 0 (.step 45 (.step 3 (.step 29 (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 7 (.step 21 (.step 22 (.close 27)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 15 (.step 26 (.step 28 (.close 31))))))))) (.step 29 (.step 31 (.step 3 (.close 7))))) (.step 7 (.step 26 (.step 29 (.step 23 (.close 31)))))) (.step 7 (.step 26 (.step 29 (.step 26 (.close 31)))))) (.step 3 (.step 7 (.step 26 (.step 4 (.close 15)))))) (.step 7 (.step 29 (.step 31 (.step 5 (.close 37)))))) (.step 29 (.step 31 (.step 7 (.step 15 (.step 16 (.close 21))))))) (.step 29 (.step 31 (.step 26 (.step 45 (.step 3 (.close 7))))))) (.step 3 (.step 7 (.step 29 (.step 31 (.step 5 (.close 37))))))) (.step 5 (.step 7 (.step 11 (.step 23 (.step 29 (.step 31 (.close 17)))))))) (.step 29 (.step 31 (.step 45 (.close 3))))) (.step 3 (.step 9 (.step 29 (.step 24 (.step 31 (.step 15 (.step 26 (.close 15))))))))) (.step 29 (.step 31 (.step 67 (.close 3))))) (.step 29 (.step 31 (.step 66 (.step 3 (.close 5)))))) (.step 3 (.step 23 (.step 26 (.step 29 (.step 7 (.step 9 (.step 31 (.step 26 (.step 15 (.close 16))))))))))) (.step 3 (.step 5 (.step 31 (.step 29 (.step 11 (.step 23 (.step 34 (.close 40))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part33

namespace Part34
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554250565137350927255266490769676123630961488590244152545429662151688458833243321843216295932771804454365998005670646906880⟩
def references : Fin 1 → Box := ![Part33.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 31 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.reuse 0) (.run (.step 5 (.step 45 (.step 58 (.step 28 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 2 0 (.step 45 (.step 31 (.step 3 (.step 9 (.step 3 (.step 5 (.close 12))))))) (.step 3 (.step 5 (.step 31 (.close 37))))) (.step 22 (.step 31 (.step 39 (.step 45 (.close 3)))))) (.step 3 (.step 4 (.step 9 (.step 22 (.close 15)))))) (.step 31 (.step 41 (.step 45 (.close 3))))) (.step 31 (.step 37 (.step 45 (.step 3 (.close 21)))))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 28 (.step 31 (.step 26 (.step 9 (.step 37 (.step 22 (.step 37 (.close 21))))))))))))) (.run (.step 26 (.step 29 (.step 31 (.step 26 (.step 40 (.step 31 (.step 39 (.step 7 (.step 9 (.step 37 (.close 45))))))))))))) (.run (.step 3 (.step 23 (.step 26 (.step 31 (.step 40 (.step 9 (.step 44 (.step 29 (.step 31 (.step 7 (.step 21 (.step 26 (.step 37 (.step 22 (.step 37 (.close 45)))))))))))))))))) (.run (.step 3 (.step 23 (.step 26 (.step 31 (.step 40 (.step 9 (.step 31 (.step 44 (.step 57 (.step 58 (.close 52)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part33.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part34

namespace Part35
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 5783586108473071698929506996965222366134733773348527145181885432838213702923272616529291289943533516693569494768790486799749829231296151986996419240282684422112756752471375619042885234029602608537093988830382207964785147904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 12 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 5 (.step 40 (.step 27 (.step 18 (.step 42 (.close 3)))))) (.step 27 (.close 5))) (.step 27 (.step 18 (.step 31 (.step 40 (.close 5)))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 3 (.step 23 (.close 3)))))))) (.step 18 (.step 27 (.step 18 (.step 31 (.step 18 (.step 36 (.step 18 (.close 21))))))))) (.step 5 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 21 (.step 40 (.close 3))) (.step 27 (.step 5 (.close 15)))) (.step 3 (.step 4 (.step 17 (.step 15 (.close 21)))))) (.step 3 (.step 4 (.step 15 (.step 17 (.step 18 (.close 21))))))) (.step 3 (.step 4 (.step 17 (.step 18 (.step 15 (.close 21))))))))) (.step 18 (.step 58 (.step 27 (.step 18 (.step 31 (.step 18 (.step 3 (.step 4 (.close 21)))))))))) (.step 27 (.step 61 (.split 17 0 (.split 21 0 (.split 22 0 (.step 42 (.step 3 (.close 5))) (.step 18 (.step 17 (.step 23 (.step 19 (.step 31 (.close 15))))))) (.step 18 (.step 15 (.step 17 (.step 3 (.close 21)))))) (.step 18 (.step 17 (.step 31 (.step 18 (.step 15 (.close 21)))))))))) (.step 3 (.step 5 (.step 18 (.step 31 (.step 18 (.step 27 (.step 31 (.step 15 (.close 21)))))))))) (.step 5 (.step 27 (.split 10 0 (.split 12 0 (.step 31 (.step 40 (.close 42))) (.step 3 (.step 5 (.step 12 (.step 15 (.close 21)))))) (.step 3 (.close 5)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part35

namespace Part36
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11567172216946143397859013993925877836143429700747176322778396065113934385828035079016261429341335348914106786741463824235075718760866035365158785615107294033570658492419761419222445685368268132166009672164793837391319138304⟩
def references : Fin 1 → Box := ![Part35.root]
def proof : Chunks.Proof 1 := (.split 65 1 (.split 67 1 (.step 40 (.split 74 1 (.split 6 0 (.split 71 1 (.reuse 0) (.run (.step 11 (.step 58 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 23 (.step 40 (.step 27 (.step 18 (.step 23 (.step 3 (.close 12))))))) (.step 18 (.step 23 (.close 27)))) (.step 18 (.step 22 (.close 27)))) (.step 18 (.step 21 (.close 27)))) (.step 17 (.step 27 (.step 36 (.step 42 (.close 3)))))) (.step 17 (.step 3 (.step 18 (.step 23 (.close 27)))))) (.step 23 (.step 27 (.step 31 (.step 18 (.close 5)))))))))) (.run (.step 5 (.step 11 (.split 2 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.step 21 (.step 40 (.close 3))) (.step 27 (.step 5 (.close 9)))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 4 (.close 11)))) (.step 3 (.close 11))) (.step 11 (.step 3 (.close 5)))) (.step 21 (.split 14 0 (.split 25 0 (.split 30 0 (.step 34 (.step 9 (.close 3))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 11 (.step 3 (.close 5)))))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 3 (.step 5 (.step 9 (.close 11))))))))) (.run (.step 11 (.step 27 (.step 42 (.step 3 (.step 5 (.step 23 (.step 3 (.close 5))))))))))) (.run (.step 3 (.step 27 (.step 31 (.close 3)))))) (.run (.step 3 (.step 5 (.step 18 (.step 24 (.step 18 (.step 12 (.step 21 (.close 27))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part35.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part36

namespace Part37
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11567172216946143397859013993930444732269467542640835698653242548129574580378747748868647828101927885092220941351979996726872892281152274005112822985706372082730238398619184249156737940781313341678919117061117026890394107904⟩
def references : Fin 1 → Box := ![Part36.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 11 (.step 40 (.step 42 (.step 58 (.step 67 (.split 10 0 (.split 21 0 (.split 30 0 (.split 35 0 (.split 2 0 (.split 25 0 (.split 38 0 (.split 40 0 (.split 50 0 (.split 55 0 (.step 67 (.close 3)) (.step 18 (.step 21 (.step 27 (.step 5 (.close 12)))))) (.step 21 (.step 27 (.step 32 (.close 42))))) (.step 18 (.step 21 (.step 5 (.step 27 (.step 17 (.close 31))))))) (.step 18 (.step 21 (.close 5)))) (.step 18 (.step 21 (.close 5)))) (.step 21 (.step 27 (.step 18 (.close 5))))) (.step 21 (.step 32 (.step 27 (.step 18 (.close 31)))))) (.step 18 (.step 3 (.step 21 (.step 27 (.step 21 (.close 17))))))) (.step 18 (.step 3 (.close 21)))) (.step 17 (.step 3 (.step 18 (.step 3 (.step 21 (.close 27)))))))))))))) (.run (.step 11 (.step 40 (.step 55 (.step 58 (.step 67 (.step 77 (.split 65 1 (.split 71 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 23 (.step 40 (.step 27 (.step 18 (.step 23 (.step 3 (.close 12))))))) (.step 18 (.step 23 (.close 27)))) (.step 18 (.step 23 (.close 27)))) (.step 18 (.step 21 (.close 27)))) (.step 12 (.step 17 (.step 27 (.close 34))))) (.step 12 (.step 3 (.step 17 (.step 18 (.step 23 (.close 27))))))) (.step 12 (.step 23 (.step 27 (.step 18 (.close 5)))))) (.step 66 (.close 3))) (.step 3 (.step 18 (.step 12 (.step 21 (.close 27))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part36.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part37

namespace Part38
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248384906756096, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253086865747496501936076628242532822245013693557462334016410842466330559436697664695426445812117088967009629862026543104⟩
def references : Fin 1 → Box := ![Part37.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 55 1 (.reuse 0) (.run (.step 5 (.step 27 (.step 40 (.step 42 (.step 3 (.step 5 (.step 18 (.step 32 (.step 4 (.step 11 (.step 4 (.close 12)))))))))))))) (.run (.step 27 (.step 3 (.step 40 (.step 42 (.step 5 (.step 44 (.step 40 (.step 55 (.close 3))))))))))) (.run (.step 27 (.step 42 (.step 5 (.step 22 (.step 11 (.step 15 (.step 22 (.step 5 (.close 31))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 23 (.step 40 (.step 61 (.step 62 (.split 55 1 (.split 2 0 (.split 6 0 (.split 10 0 (.step 21 (.split 12 0 (.split 21 0 (.step 40 (.step 3 (.step 5 (.step 3 (.close 4))))) (.step 3 (.step 4 (.step 18 (.close 23))))) (.step 9 (.split 14 0 (.step 57 (.step 5 (.step 3 (.close 4)))) (.step 12 (.close 15)))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 22 (.close 23))))))) (.step 9 (.close 11))) (.step 3 (.step 5 (.step 9 (.step 21 (.close 23)))))) (.step 4 (.step 5 (.step 21 (.step 27 (.step 9 (.close 23)))))))))))))))) (.run (.step 3 (.step 27 (.step 36 (.step 42 (.step 3 (.close 7)))))))) (.run (.step 21 (.step 27 (.step 42 (.step 3 (.step 53 (.step 3 (.close 5))))))))) (.run (.step 27 (.step 42 (.step 3 (.step 34 (.step 52 (.close 5)))))))) (.run (.step 3 (.step 11 (.step 27 (.close 7)))))) (.run (.step 3 (.step 5 (.step 7 (.step 31 (.step 40 (.close 27)))))))) (.run (.step 5 (.step 27 (.step 31 (.step 24 (.step 42 (.close 3))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part37.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part38

namespace Part39
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126547126813004582111031748020896968562031776794311496148049777697996758436535501201342675059337432875672689041555324928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 43 0 (.split 30 0 (.split 40 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 24 0 (.step 29 (.step 31 (.close 3))) (.step 5 (.step 3 (.step 15 (.step 21 (.close 28)))))) (.step 3 (.step 5 (.step 3 (.step 15 (.close 21)))))) (.step 3 (.step 5 (.step 21 (.close 15))))) (.step 3 (.step 5 (.step 7 (.step 21 (.step 28 (.step 12 (.step 15 (.close 16))))))))) (.step 5 (.step 4 (.step 15 (.step 21 (.close 28)))))) (.step 3 (.step 5 (.step 7 (.step 15 (.step 21 (.close 28))))))) (.step 3 (.step 5 (.step 7 (.step 9 (.close 15)))))) (.step 5 (.step 7 (.step 3 (.step 5 (.step 3 (.step 15 (.step 21 (.close 28))))))))) (.step 3 (.step 5 (.step 4 (.step 15 (.close 21)))))) (.step 5 (.step 7 (.step 3 (.step 5 (.step 3 (.step 15 (.step 21 (.close 28))))))))) (.step 5 (.step 7 (.step 18 (.step 3 (.step 4 (.step 15 (.step 21 (.close 28))))))))) (.step 5 (.step 18 (.step 5 (.step 18 (.step 29 (.step 5 (.close 12)))))))) (.step 48 (.split 30 0 (.split 40 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 29 (.step 21 (.step 31 (.close 3)))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 5 (.step 15 (.close 21))))) (.step 3 (.step 5 (.step 15 (.step 12 (.close 16)))))) (.step 3 (.close 9))) (.step 4 (.step 5 (.step 15 (.close 21))))) (.step 3 (.step 4 (.step 15 (.close 21))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part39

namespace Part40
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467542640835694879280123308033228137193167880378937185006664675777993710002514509234094797877018986678435522217999156765531423845805388550388207953053409468813161334636909463868538880⟩
def references : Fin 1 → Box := ![Part39.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 10 0 (.reuse 0) (.run (.step 3 (.step 7 (.step 3 (.step 5 (.step 3 (.step 12 (.step 15 (.close 28)))))))))) (.run (.step 48 (.split 10 0 (.split 25 0 (.split 12 0 (.split 30 0 (.step 21 (.step 31 (.step 3 (.step 5 (.close 9))))) (.step 3 (.step 4 (.step 9 (.close 15))))) (.step 21 (.step 9 (.step 3 (.close 5))))) (.step 29 (.step 3 (.close 5)))) (.step 3 (.step 4 (.step 9 (.step 12 (.close 15))))))))) (.run (.step 5 (.step 3 (.step 28 (.step 15 (.close 9))))))) (.run (.step 5 (.step 18 (.step 12 (.close 17)))))) (.run (.step 5 (.step 29 (.step 38 (.split 2 0 (.step 75 (.split 6 0 (.split 12 0 (.split 10 0 (.step 31 (.step 41 (.close 3))) (.step 3 (.step 4 (.close 12)))) (.step 21 (.step 26 (.step 31 (.close 3))))) (.step 9 (.step 21 (.step 5 (.close 3)))))) (.step 3 (.step 5 (.step 15 (.close 9)))))))))) (.run (.step 63 (.step 67 (.step 74 (.step 3 (.close 5))))))) (.run (.step 3 (.close 7)))) (.run (.step 3 (.step 5 (.step 18 (.step 21 (.step 3 (.step 10 (.step 28 (.step 43 (.step 3 (.step 15 (.step 22 (.step 15 (.close 26))))))))))))))) (.run (.step 3 (.step 63 (.step 50 (.close 67)))))) (.run (.step 18 (.step 63 (.step 49 (.step 66 (.step 67 (.step 28 (.step 5 (.step 31 (.step 5 (.close 37))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part39.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part40

namespace Part41
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467546697054282812156906721815925100961665444801953361802059682852542009723306501980878783214848477191098529278578084898591619972036850951692681345602985701295366599684016351929696256⟩
def references : Fin 1 → Box := ![Part40.root]
def proof : Chunks.Proof 1 := (.split 56 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 21 (.step 5 (.step 26 (.step 31 (.step 42 (.step 9 (.step 7 (.step 21 (.step 3 (.step 7 (.step 26 (.step 28 (.step 15 (.step 12 (.close 16)))))))))))))))))) (.run (.step 3 (.step 5 (.step 18 (.step 23 (.step 12 (.step 27 (.step 12 (.close 42)))))))))) (.run (.step 5 (.step 58 (.step 28 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 40 0 (.split 49 0 (.step 41 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 7 (.step 21 (.step 22 (.close 15))))))) (.step 5 (.step 4 (.step 15 (.step 21 (.close 31)))))) (.step 3 (.step 5 (.step 7 (.step 15 (.step 21 (.close 37))))))) (.step 5 (.step 3 (.step 4 (.step 15 (.step 21 (.close 37))))))) (.step 3 (.step 5 (.step 4 (.step 15 (.close 21)))))) (.step 5 (.step 3 (.step 4 (.step 15 (.step 21 (.close 37))))))) (.step 5 (.step 7 (.step 18 (.step 4 (.step 15 (.step 21 (.close 37)))))))) (.step 48 (.step 59 (.step 3 (.close 5))))) (.step 3 (.step 5 (.step 7 (.step 4 (.step 12 (.step 15 (.close 37)))))))) (.step 10 (.step 31 (.step 38 (.close 41))))) (.step 38 (.step 41 (.step 5 (.close 9))))) (.step 22 (.close 41))) (.step 3 (.close 7))) (.step 3 (.step 10 (.step 18 (.step 21 (.step 3 (.step 22 (.close 41)))))))) (.step 3 (.step 21 (.close 41)))) (.step 18 (.step 49 (.step 51 (.step 63 (.close 41)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part40.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part41

namespace Part42
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328372883776591027395682539081220876511041166738106827589234668324794308383271089659203758019274237180276275937280⟩
def references : Fin 1 → Box := ![Part41.root]
def proof : Chunks.Proof 1 := (.step 43 (.step 58 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 21 (.step 31 (.step 48 (.step 9 (.step 57 (.step 28 (.step 5 (.close 3)))))))))))) (.run (.step 3 (.step 7 (.step 4 (.step 9 (.step 3 (.step 18 (.step 21 (.close 26)))))))))) (.run (.step 3 (.step 21 (.step 5 (.step 31 (.step 21 (.step 42 (.step 7 (.step 9 (.step 7 (.close 21)))))))))))) (.run (.step 3 (.step 21 (.step 31 (.step 5 (.step 42 (.step 9 (.step 16 (.step 48 (.step 57 (.step 52 (.step 21 (.step 7 (.step 22 (.step 28 (.step 3 (.step 26 (.close 3))))))))))))))))))) (.run (.step 3 (.step 7 (.step 4 (.step 9 (.step 3 (.close 10)))))))) (.run (.step 7 (.step 31 (.step 38 (.step 45 (.step 58 (.step 60 (.step 28 (.step 41 (.split 54 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 2 0 (.step 45 (.step 31 (.step 3 (.step 9 (.step 3 (.step 5 (.close 12))))))) (.step 3 (.step 5 (.step 31 (.close 37))))) (.step 31 (.step 38 (.step 39 (.step 3 (.close 5)))))) (.step 3 (.step 4 (.step 9 (.step 21 (.step 15 (.step 22 (.step 15 (.close 26))))))))) (.step 21 (.step 31 (.step 38 (.step 5 (.step 39 (.step 5 (.close 37)))))))) (.step 31 (.step 37 (.step 38 (.step 41 (.close 3)))))) (.step 10 (.step 21 (.step 26 (.step 31 (.step 3 (.step 15 (.close 16)))))))))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 31 (.step 5 (.step 27 (.step 18 (.step 23 (.step 12 (.close 42))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part41.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part42

namespace Part43
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328372883776591027395682539081220876511041166738106827589234668324794308383271089659203758019274237180276275937280⟩
def references : Fin 4 → Box := ![Part32.root, Part34.root, Part38.root, Part42.root]
def proof : Chunks.Proof 4 := (.split 38 1 (.split 39 1 (.split 42 1 (.split 40 1 (.reuse 0) (.run (.step 40 (.step 43 (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 43 (.step 31 (.step 27 (.step 68 (.step 43 (.step 7 (.step 11 (.step 23 (.close 18))))))))) (.step 3 (.step 31 (.step 5 (.step 18 (.step 24 (.step 5 (.step 18 (.close 27))))))))) (.step 18 (.step 31 (.step 24 (.step 40 (.step 5 (.step 18 (.step 34 (.step 43 (.close 27)))))))))) (.step 3 (.step 9 (.step 23 (.step 5 (.step 7 (.step 27 (.step 31 (.close 3))))))))) (.step 5 (.step 27 (.step 24 (.step 31 (.close 61)))))) (.step 3 (.step 9 (.step 23 (.step 24 (.step 31 (.step 3 (.step 5 (.close 21))))))))) (.step 3 (.step 7 (.step 4 (.step 3 (.step 9 (.step 27 (.close 44)))))))) (.step 3 (.step 9 (.step 23 (.step 5 (.step 27 (.step 31 (.step 3 (.step 44 (.step 3 (.close 21))))))))))) (.step 3 (.step 9 (.step 23 (.step 5 (.step 27 (.step 31 (.step 3 (.step 34 (.step 31 (.close 52))))))))))) (.step 3 (.step 7 (.step 4 (.step 3 (.close 9))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part32.excludes
  · exact Part34.excludes
  · exact Part38.excludes
  · exact Part42.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part43

namespace Part44
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397854115110619787389832519696291695353010102577572684666561859313865354640492944899582172690464598729712896276992403693274563433326826192004487407211502646858810309146377495132789428338885134087640690196480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 55 0 (.split 59 0 (.split 63 0 (.split 64 0 (.step 39 (.step 3 (.close 7))) (.step 29 (.step 31 (.close 3)))) (.step 29 (.step 31 (.step 3 (.step 15 (.close 37)))))) (.step 7 (.step 29 (.step 23 (.step 26 (.step 5 (.step 15 (.close 21)))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 15 (.step 28 (.step 15 (.step 21 (.close 31)))))))))) (.step 29 (.step 31 (.step 3 (.close 7))))) (.step 7 (.step 29 (.step 31 (.close 21))))) (.step 7 (.step 29 (.step 31 (.step 16 (.close 21)))))) (.step 3 (.step 7 (.step 22 (.step 4 (.step 26 (.step 4 (.close 15)))))))) (.step 7 (.step 29 (.step 31 (.step 5 (.close 37)))))) (.step 29 (.step 31 (.step 7 (.step 15 (.step 16 (.close 21))))))) (.step 29 (.step 31 (.step 39 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 29 (.step 31 (.step 5 (.close 37))))))) (.step 5 (.step 7 (.step 11 (.step 23 (.step 29 (.step 31 (.close 17)))))))) (.step 29 (.step 31 (.step 39 (.close 3))))) (.step 3 (.step 9 (.step 29 (.step 24 (.step 31 (.step 15 (.close 39)))))))) (.step 29 (.step 31 (.step 51 (.close 67))))) (.step 29 (.step 31 (.step 51 (.step 31 (.close 66)))))) (.step 3 (.step 23 (.step 29 (.step 7 (.step 9 (.step 31 (.step 22 (.step 15 (.close 26)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part44

namespace Part45
def root : Box := ⟨5415370496329716527311175368952126814053252356422065803131208028704571983222444488064368062151364500398865205678528759439818752, 11567172216946143397854115110619787389832519696295652643211323784250719483450220169882153584177885821150401218749423922716022078247378509799703259348023897591373705359977677593757679453861626294446410870038244027163458142208⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 31 (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.split 55 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 6 0 (.step 45 (.step 7 (.step 5 (.step 15 (.step 17 (.close 21)))))) (.step 29 (.step 31 (.close 39)))) (.step 3 (.step 7 (.step 28 (.step 31 (.step 5 (.close 37))))))) (.step 5 (.step 7 (.step 11 (.step 23 (.step 29 (.step 31 (.close 17)))))))) (.step 29 (.step 31 (.close 39)))) (.step 3 (.step 29 (.step 9 (.step 24 (.step 31 (.step 15 (.close 39)))))))) (.step 29 (.step 31 (.close 39)))) (.step 29 (.step 31 (.step 37 (.close 39))))) (.step 3 (.step 7 (.step 9 (.step 23 (.step 29 (.step 31 (.step 22 (.step 26 (.step 15 (.close 16))))))))))) (.step 3 (.step 5 (.step 7 (.step 28 (.step 31 (.step 9 (.step 22 (.step 26 (.step 15 (.step 37 (.close 21)))))))))))) (.step 29 (.step 31 (.step 22 (.step 26 (.step 7 (.step 9 (.step 37 (.close 39))))))))) (.step 3 (.step 7 (.step 9 (.step 23 (.step 29 (.step 31 (.step 21 (.step 22 (.step 26 (.step 15 (.step 37 (.close 39)))))))))))))) (.step 7 (.step 9 (.step 22 (.step 23 (.step 26 (.step 29 (.step 31 (.step 22 (.step 26 (.step 37 (.step 21 (.close 39)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part45

namespace Part46
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397854115110619787389832519696295652643211323784250719483450220169882153584177885821150403740477820491962691664105944918990986784451337207379960454050755549319951055275340756807486723504639255651354837778432⟩
def references : Fin 2 → Box := ![Part44.root, Part45.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 58 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 31 (.step 22 (.step 23 (.step 27 (.step 34 (.close 36)))))))))) (.run (.step 5 (.step 22 (.step 28 (.step 39 (.step 51 (.split 2 0 (.step 39 (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.step 22 (.close 37)))))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 28 (.step 31 (.step 22 (.step 9 (.step 37 (.close 26))))))))))) (.run (.step 22 (.step 29 (.step 31 (.step 22 (.step 9 (.step 7 (.close 39))))))))) (.run (.step 3 (.step 22 (.step 23 (.step 31 (.step 36 (.step 29 (.step 40 (.step 9 (.step 29 (.step 31 (.step 7 (.step 21 (.step 22 (.step 26 (.step 37 (.close 26)))))))))))))))))) (.run (.step 3 (.step 22 (.step 23 (.step 31 (.step 36 (.step 40 (.step 9 (.step 31 (.step 57 (.step 7 (.step 29 (.step 31 (.step 37 (.step 21 (.close 26))))))))))))))))) (.reuse 1)) (.run (.step 3 (.step 5 (.step 31 (.close 36))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part44.excludes
  · exact Part45.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part46

namespace Part47
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11567166701293880295871715265202237301355671938583945197703489519632909495378872634374478181040586171753577635868040509149977344704868245523669169560826620916483765128827186963287930567823460203788120696483581586194801098752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 59 1 (.step 29 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.step 40 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 71 1 (.step 38 (.split 6 0 (.split 10 0 (.step 38 (.step 31 (.step 38 (.step 18 (.step 3 (.step 4 (.close 5))))))) (.step 3 (.step 18 (.step 38 (.step 3 (.close 15)))))) (.step 9 (.step 3 (.close 5))))) (.step 74 (.step 18 (.step 9 (.step 3 (.step 5 (.step 12 (.close 15)))))))) (.step 18 (.step 38 (.step 3 (.close 18))))) (.step 40 (.close 38))) (.step 3 (.step 31 (.step 38 (.step 3 (.step 11 (.step 5 (.close 12)))))))) (.step 23 (.step 40 (.step 38 (.close 3))))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.step 21 (.step 24 (.step 15 (.close 22))))))) (.step 29 (.step 40 (.step 67 (.step 3 (.step 21 (.step 3 (.close 5)))))))) (.step 29 (.step 40 (.step 66 (.step 3 (.step 31 (.step 3 (.step 5 (.close 9)))))))))) (.step 3 (.step 9 (.step 21 (.step 23 (.step 26 (.step 29 (.step 40 (.step 21 (.step 38 (.close 3))))))))))) (.step 3 (.step 5 (.step 29 (.step 38 (.step 48 (.step 38 (.step 50 (.step 58 (.step 74 (.split 63 1 (.split 2 0 (.step 48 (.split 6 0 (.split 10 0 (.step 31 (.close 38)) (.step 3 (.step 4 (.close 12)))) (.step 9 (.step 5 (.close 3))))) (.step 3 (.step 5 (.step 9 (.close 15))))) (.step 31 (.step 3 (.close 5)))))))))))))) (.step 3 (.step 18 (.step 29 (.step 32 (.step 40 (.close 38))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part47

namespace Part48
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592551670839450285977480433724213751038817712066020298884021841157400975144440366306575564320394408428257856887118429214998528⟩
def references : Fin 1 → Box := ![Part47.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 75 (.split 54 1 (.reuse 0) (.run (.step 9 (.step 21 (.step 29 (.step 38 (.step 40 (.step 57 (.step 18 (.step 5 (.close 15)))))))))))) (.run (.step 3 (.step 9 (.step 38 (.step 40 (.step 51 (.step 3 (.step 7 (.step 21 (.close 26))))))))))) (.run (.step 9 (.step 21 (.step 23 (.step 38 (.step 40 (.step 21 (.step 3 (.close 7)))))))))) (.run (.step 9 (.step 21 (.step 23 (.step 53 (.step 40 (.step 55 (.step 57 (.step 58 (.step 66 (.split 51 1 (.step 75 (.step 55 (.split 58 1 (.split 71 1 (.split 10 0 (.split 12 0 (.split 59 1 (.step 21 (.step 29 (.step 18 (.close 38)))) (.step 26 (.step 21 (.step 29 (.step 18 (.step 31 (.close 16))))))) (.step 15 (.step 21 (.step 29 (.step 38 (.step 3 (.step 16 (.step 18 (.step 3 (.close 17)))))))))) (.step 3 (.step 7 (.step 15 (.step 18 (.step 21 (.step 22 (.close 23)))))))) (.step 3 (.step 21 (.step 22 (.step 23 (.step 29 (.step 31 (.step 12 (.close 15))))))))) (.step 3 (.step 22 (.step 23 (.step 27 (.step 38 (.step 26 (.step 21 (.step 5 (.step 3 (.close 15))))))))))))) (.step 3 (.step 7 (.step 21 (.close 26)))))))))))))))) (.run (.step 3 (.step 9 (.close 7))))) (.run (.step 7 (.step 29 (.step 31 (.step 38 (.close 3))))))) (.run (.step 3 (.step 5 (.step 21 (.step 31 (.step 32 (.step 38 (.step 40 (.step 27 (.step 21 (.close 23)))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 29 (.step 38 (.close 3))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part47.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part48

namespace Part49
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234612672417218981940172638561150155483217220725077386499353354679979219080356132029788291175059104994426880⟩
def references : Fin 3 → Box := ![Part43.root, Part46.root, Part48.root]
def proof : Chunks.Proof 3 := (.split 35 1 (.split 36 1 (.reuse 0) (.step 7 (.step 31 (.split 38 1 (.reuse 1) (.run (.step 31 (.step 38 (.step 45 (.step 58 (.step 39 (.split 54 1 (.split 63 1 (.split 64 1 (.split 65 1 (.step 5 (.step 28 (.step 39 (.step 41 (.split 2 0 (.step 39 (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.step 31 (.close 37))))))))) (.step 3 (.step 10 (.step 21 (.step 22 (.step 4 (.step 15 (.step 28 (.step 15 (.close 26)))))))))) (.step 5 (.step 21 (.step 28 (.step 31 (.step 38 (.step 39 (.close 3)))))))) (.step 5 (.step 28 (.step 31 (.step 37 (.step 38 (.step 39 (.close 3)))))))) (.step 5 (.step 10 (.step 21 (.step 22 (.step 28 (.step 31 (.step 3 (.step 15 (.close 16)))))))))))))))))))) (.step 40 (.split 36 1 (.reuse 2) (.run (.step 7 (.step 29 (.step 31 (.step 38 (.step 3 (.step 4 (.step 3 (.close 7))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part43.excludes
  · exact Part46.excludes
  · exact Part48.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part49

namespace Part50
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397854115110619787389832519692239434055274757891525411362175959752329762616818690114430163579438568245027135136182889693017118037160799011956211717452933824380656954214207896190336707922121941457324978733056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 12 0 (.split 14 0 (.split 21 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 55 0 (.split 59 0 (.split 63 0 (.split 64 0 (.split 24 0 (.split 17 0 (.split 51 0 (.step 37 (.close 3)) (.step 3 (.step 7 (.close 4)))) (.step 7 (.close 4))) (.step 3 (.step 7 (.step 5 (.close 27))))) (.step 29 (.step 31 (.close 3)))) (.step 29 (.step 31 (.step 3 (.step 15 (.close 37)))))) (.step 7 (.step 15 (.step 29 (.step 5 (.step 21 (.close 22))))))) (.step 3 (.step 5 (.step 7 (.step 5 (.step 15 (.step 28 (.step 15 (.step 21 (.close 31)))))))))) (.step 29 (.step 31 (.step 3 (.close 7))))) (.step 7 (.step 15 (.step 29 (.step 31 (.close 21)))))) (.step 7 (.step 15 (.step 29 (.step 31 (.close 16)))))) (.step 3 (.step 7 (.step 15 (.step 4 (.step 26 (.step 4 (.close 21)))))))) (.step 7 (.step 29 (.step 31 (.step 5 (.close 37)))))) (.step 29 (.step 31 (.step 7 (.close 15))))) (.step 29 (.step 31 (.step 15 (.step 7 (.close 9)))))) (.step 3 (.step 7 (.step 29 (.step 31 (.step 5 (.close 37))))))) (.step 5 (.step 7 (.step 11 (.step 17 (.step 23 (.step 29 (.close 31)))))))) (.step 29 (.step 31 (.step 37 (.step 3 (.close 5)))))) (.step 3 (.step 9 (.step 15 (.step 29 (.step 24 (.step 21 (.step 26 (.step 21 (.close 22)))))))))) (.step 29 (.step 31 (.step 66 (.step 67 (.close 3)))))) (.step 29 (.step 31 (.close 66)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part50

namespace Part51
def root : Box := ⟨5415370496329716522614094682893944713882712277727952885268399174178926711106932344978151939505889973793357970663977896590180352, 11567172216946143397854115110619787389832519696295652643211323784250719483450220169882153584177885821150401218749421574175679049156328424529663912291564966186946442537341619837686136345800303557183108116420736751732033323008⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 31 (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.split 55 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 6 0 (.step 45 (.step 7 (.step 5 (.step 15 (.close 17))))) (.step 29 (.step 31 (.close 37)))) (.step 3 (.step 7 (.step 28 (.step 31 (.step 5 (.close 37))))))) (.step 5 (.step 7 (.step 11 (.step 17 (.step 23 (.step 29 (.close 31)))))))) (.step 29 (.step 31 (.close 37)))) (.step 3 (.step 29 (.step 9 (.step 15 (.step 24 (.step 21 (.step 26 (.step 21 (.close 22)))))))))) (.step 29 (.step 31 (.step 37 (.close 3))))) (.step 15 (.step 29 (.step 31 (.close 37))))) (.step 3 (.step 7 (.step 9 (.step 15 (.step 23 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22))))))))))) (.step 3 (.step 5 (.step 7 (.step 28 (.step 31 (.step 9 (.step 15 (.step 16 (.step 21 (.step 26 (.step 21 (.close 22))))))))))))) (.step 15 (.step 29 (.step 31 (.step 26 (.step 7 (.step 9 (.step 16 (.step 21 (.close 37)))))))))) (.step 3 (.step 7 (.step 9 (.step 15 (.step 23 (.step 29 (.step 31 (.step 21 (.step 26 (.step 16 (.step 22 (.close 37)))))))))))))) (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 26 (.step 29 (.step 31 (.step 21 (.step 26 (.step 21 (.close 37)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part51

namespace Part52
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397854115110619787389832519696295652643211323784250719483450220169882153584177885821150403740477818143422348635014894833720947437394878275975533191228119491563879512167279434070223420751021748375923412959232⟩
def references : Fin 2 → Box := ![Part50.root, Part51.root]
def proof : Chunks.Proof 2 := (.split 39 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 15 (.step 7 (.step 9 (.step 23 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22)))))))))))) (.run (.step 3 (.step 5 (.step 31 (.step 29 (.step 11 (.step 17 (.step 23 (.close 34)))))))))) (.run (.step 5 (.step 37 (.step 58 (.step 28 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 2 0 (.step 37 (.step 3 (.step 5 (.close 3)))) (.step 3 (.step 5 (.step 31 (.close 37))))) (.step 22 (.step 31 (.step 37 (.close 3))))) (.step 3 (.step 4 (.step 9 (.step 15 (.step 21 (.close 22))))))) (.step 31 (.step 37 (.close 3)))) (.step 15 (.step 31 (.close 37)))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 28 (.step 31 (.close 37)))))))) (.run (.step 15 (.step 29 (.step 31 (.step 39 (.step 9 (.step 7 (.step 16 (.step 26 (.close 37))))))))))) (.run (.step 3 (.step 15 (.step 23 (.step 31 (.step 34 (.step 29 (.step 40 (.step 9 (.step 29 (.step 7 (.step 21 (.step 31 (.close 37))))))))))))))) (.run (.step 3 (.step 15 (.step 16 (.step 17 (.step 31 (.step 34 (.step 40 (.step 9 (.step 16 (.close 52)))))))))))) (.reuse 1)) (.run (.step 3 (.step 5 (.step 31 (.close 34))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part50.excludes
  · exact Part51.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part52

namespace Part53
def root : Box := ⟨4697089645037150811387382308463235191639921341107634210713651743042619977812959247249288758524523951425585152, 11567172216946143397854115110619787389832519696295652643211323784250719483450220169882153584177885821150403742940445879239586359615562729460520089549389356062172516294758536620208655094880211892058525380327360695040694288384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 31 (.split 49 1 (.step 45 (.split 50 1 (.step 37 (.split 54 1 (.split 55 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 12 0 (.split 14 0 (.step 39 (.step 5 (.step 7 (.step 22 (.step 27 (.close 29)))))) (.step 7 (.step 29 (.step 31 (.step 5 (.close 37)))))) (.step 29 (.step 31 (.step 7 (.close 15))))) (.step 29 (.step 31 (.close 37)))) (.step 3 (.step 7 (.step 28 (.step 31 (.step 5 (.close 37))))))) (.step 5 (.step 7 (.step 11 (.step 17 (.step 23 (.step 29 (.close 31)))))))) (.step 29 (.step 31 (.close 37)))) (.step 3 (.step 29 (.step 9 (.step 15 (.step 24 (.step 21 (.step 31 (.step 21 (.close 22)))))))))) (.step 29 (.step 31 (.step 37 (.close 3))))) (.step 15 (.step 29 (.step 31 (.close 37))))) (.step 3 (.step 7 (.step 9 (.step 15 (.step 23 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22))))))))))) (.step 3 (.step 5 (.step 7 (.step 28 (.step 31 (.step 9 (.step 15 (.step 16 (.step 21 (.step 22 (.step 21 (.close 26))))))))))))) (.step 15 (.step 29 (.step 31 (.step 22 (.step 7 (.step 9 (.close 37))))))))) (.step 3 (.step 7 (.step 9 (.step 15 (.step 22 (.step 23 (.step 29 (.step 31 (.step 21 (.step 22 (.step 26 (.step 16 (.step 26 (.close 37)))))))))))))))) (.step 7 (.step 15 (.step 16 (.step 9 (.step 17 (.step 29 (.step 31 (.close 37)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part53

namespace Part54
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337916810195941030779952782200356648335016433508367761545114971815889082784940032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 35 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 7 (.close 3)) (.step 3 (.close 12))) (.step 3 (.step 18 (.step 3 (.close 9))))) (.step 3 (.step 18 (.step 3 (.step 9 (.close 15)))))) (.step 3 (.step 18 (.step 31 (.close 7))))) (.step 3 (.step 18 (.step 7 (.close 17))))) (.step 3 (.step 7 (.close 4)))) (.step 3 (.step 9 (.step 18 (.step 15 (.close 21)))))) (.step 3 (.step 7 (.step 18 (.step 31 (.close 53)))))) (.step 3 (.step 7 (.step 18 (.step 31 (.step 53 (.step 18 (.step 31 (.step 52 (.close 7)))))))))) (.step 3 (.step 18 (.step 27 (.close 31))))) (.step 3 (.step 7 (.step 4 (.close 18))))) (.step 3 (.step 18 (.step 29 (.close 38))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part54

namespace Part55
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 11567166701293880295871715265202237301355671938583945193925841584630878356660519660240712933784878895457824277385998067645770948976561798963356190952833856582606251273284534649404322899630474062837276412512692440313235505152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 2 0 (.step 29 (.split 6 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 58 (.split 22 0 (.split 43 0 (.step 29 (.step 5 (.close 3))) (.step 3 (.step 5 (.step 3 (.close 7))))) (.step 7 (.step 3 (.step 4 (.close 5)))))) (.step 3 (.step 5 (.close 4)))) (.step 5 (.step 7 (.step 3 (.step 4 (.close 5)))))) (.step 5 (.step 7 (.step 18 (.step 3 (.close 4)))))) (.step 5 (.step 18 (.step 5 (.step 3 (.close 12)))))) (.step 29 (.step 3 (.close 5)))) (.step 3 (.step 7 (.step 3 (.step 5 (.step 3 (.close 12))))))) (.step 29 (.step 3 (.close 5))))) (.step 5 (.step 3 (.close 28)))) (.step 5 (.step 18 (.step 12 (.close 17))))) (.step 29 (.step 5 (.step 12 (.close 18))))) (.step 3 (.close 7))) (.step 3 (.step 5 (.step 18 (.step 43 (.step 3 (.step 9 (.close 28)))))))) (.step 3 (.step 29 (.step 5 (.step 18 (.step 5 (.step 24 (.step 5 (.close 12))))))))) (.step 18 (.step 29 (.step 18 (.step 5 (.step 43 (.step 49 (.step 5 (.step 58 (.step 5 (.step 18 (.close 21)))))))))))) (.step 3 (.step 9 (.step 26 (.step 27 (.step 7 (.step 26 (.step 29 (.close 3))))))))) (.step 3 (.step 5 (.step 18 (.step 23 (.step 12 (.close 27))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part55

namespace Part56
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918619447335363845506275496997409083576640851878162178928088340639206427590656⟩
def references : Fin 1 → Box := ![Part55.root]
def proof : Chunks.Proof 1 := (.step 43 (.step 29 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.step 58 (.split 39 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.reuse 0) (.run (.step 5 (.step 28 (.step 58 (.step 28 (.step 58 (.split 63 1 (.split 49 0 (.step 28 (.step 5 (.step 22 (.close 5)))) (.step 3 (.step 5 (.step 9 (.close 12))))) (.step 28 (.step 5 (.close 12))))))))))) (.run (.step 3 (.step 5 (.step 9 (.step 29 (.step 3 (.step 5 (.close 16))))))))) (.run (.step 3 (.step 7 (.step 4 (.step 9 (.step 3 (.step 18 (.step 21 (.close 26)))))))))) (.run (.step 3 (.step 9 (.step 27 (.step 21 (.step 29 (.step 3 (.close 53))))))))) (.run (.step 3 (.step 9 (.step 27 (.step 29 (.step 16 (.step 48 (.step 52 (.step 22 (.step 29 (.close 52)))))))))))) (.run (.step 3 (.step 7 (.step 4 (.step 9 (.step 3 (.close 10)))))))) (.run (.step 7 (.step 28 (.step 5 (.step 29 (.step 3 (.close 7)))))))) (.run (.step 3 (.step 5 (.step 21 (.step 27 (.step 5 (.close 3))))))))) (.run (.step 10 (.step 28 (.step 5 (.step 58 (.step 28 (.step 58 (.split 54 1 (.split 63 1 (.split 49 0 (.step 28 (.step 5 (.step 21 (.close 5)))) (.step 3 (.step 5 (.step 9 (.close 12))))) (.step 28 (.step 5 (.close 12)))) (.step 9 (.step 21 (.step 3 (.step 5 (.close 12)))))))))))))) (.run (.step 7 (.step 28 (.step 5 (.step 29 (.step 3 (.close 7)))))))) (.run (.step 7 (.step 16 (.step 28 (.step 5 (.step 29 (.step 3 (.close 7))))))))) (.run (.step 3 (.step 7 (.step 4 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part55.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part56

namespace Part57
def root : Box := ⟨3533694129556768659166595001485837031654967793751237916243212404732723200, 5783586113859450862115041468379996006203985526872075103272815464964453347665654342529502051787928049841817549559449864936461689078301647678876972110297728209828729183145573994943390318190226480858844365980524030166387654656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 71 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 12 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 38 1 (.split 56 1 (.split 25 0 (.split 38 0 (.step 27 (.step 3 (.close 5))) (.step 29 (.close 27))) (.step 27 (.close 5))) (.step 5 (.close 12))) (.step 5 (.close 12))) (.step 3 (.step 5 (.step 27 (.close 3))))) (.step 31 (.step 27 (.close 3)))) (.step 3 (.step 5 (.step 18 (.step 23 (.close 3)))))) (.step 18 (.step 31 (.step 27 (.close 3))))) (.step 5 (.split 21 0 (.split 25 0 (.split 30 0 (.split 54 0 (.step 29 (.close 27)) (.step 34 (.step 27 (.step 3 (.close 5))))) (.step 3 (.step 4 (.step 17 (.step 15 (.close 21)))))) (.step 3 (.step 5 (.step 12 (.step 15 (.close 21)))))) (.step 3 (.step 4 (.step 17 (.step 18 (.step 15 (.close 21))))))))) (.step 18 (.step 42 (.step 58 (.step 27 (.close 3)))))) (.step 42 (.step 27 (.step 3 (.step 5 (.step 17 (.step 3 (.close 5)))))))) (.step 3 (.step 5 (.step 18 (.step 31 (.step 18 (.close 27))))))) (.step 5 (.step 27 (.step 3 (.close 5))))) (.step 11 (.step 58 (.split 2 0 (.split 10 0 (.split 21 0 (.split 25 0 (.split 30 0 (.split 38 0 (.step 36 (.step 27 (.step 3 (.close 5)))) (.step 18 (.step 23 (.step 5 (.close 12))))) (.step 18 (.step 23 (.close 27)))) (.step 18 (.step 23 (.step 5 (.close 12))))) (.step 18 (.step 22 (.close 23)))) (.step 17 (.step 3 (.step 18 (.step 23 (.close 27)))))) (.step 23 (.step 27 (.close 5))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part57

namespace Part58
def root : Box := ⟨3533694129556768659166595001485837031654967793751237916243212404732723200, 11567172216946143397859013993925877836143429700747176322778396065113934385828035079016261429341335348914104267475692642263061083669739632432851123329279455496139104932739810755887423500980628316414213586829131369815481516032⟩
def references : Fin 1 → Box := ![Part57.root]
def proof : Chunks.Proof 1 := (.split 65 1 (.split 67 1 (.step 29 (.split 74 1 (.split 6 0 (.reuse 0) (.run (.step 5 (.step 11 (.split 10 0 (.split 12 0 (.split 21 0 (.split 25 0 (.split 30 0 (.split 54 0 (.split 65 0 (.split 2 0 (.step 29 (.close 27)) (.step 3 (.step 5 (.step 9 (.close 11))))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 36 (.step 27 (.step 3 (.close 5))))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 3 (.step 5 (.step 9 (.close 11))))) (.step 3 (.step 4 (.close 11)))) (.split 2 0 (.split 25 0 (.split 30 0 (.step 34 (.split 14 0 (.split 16 0 (.split 38 0 (.step 27 (.step 3 (.close 5))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 11 (.step 3 (.close 5))))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9))))) (.step 3 (.step 4 (.step 9 (.close 11))))))))) (.run (.step 11 (.step 27 (.step 3 (.close 5))))))) (.run (.step 3 (.step 27 (.close 7))))) (.run (.step 3 (.step 5 (.step 18 (.step 24 (.step 18 (.step 12 (.step 21 (.close 27))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part57.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part58

namespace Part59
def root : Box := ⟨3533694129556768659166595001485837031654967793751237916243212404732723200, 11567172216946143397859013993930444732269467542640835698656928058310064366855546142014144184440713940971531352192044953719941874536111953936170518829934840935475900048930213903106647967946334456232358807361619301544682848256⟩
def references : Fin 1 → Box := ![Part58.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 11 (.step 27 (.step 29 (.step 58 (.split 2 0 (.split 10 0 (.split 21 0 (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.split 49 0 (.step 67 (.split 50 0 (.split 51 0 (.step 67 (.step 23 (.step 3 (.step 18 (.step 5 (.close 17)))))) (.step 3 (.step 18 (.step 3 (.step 21 (.close 15)))))) (.step 3 (.step 23 (.close 27))))) (.step 3 (.step 17 (.step 23 (.close 27))))) (.step 18 (.step 23 (.step 27 (.step 5 (.close 29)))))) (.step 18 (.step 23 (.step 5 (.step 29 (.step 5 (.close 12))))))) (.step 3 (.step 18 (.close 27)))) (.step 18 (.step 23 (.step 5 (.step 27 (.close 5)))))) (.step 18 (.step 21 (.close 23)))) (.step 3 (.step 17 (.step 18 (.step 23 (.close 27)))))) (.step 23 (.step 27 (.close 5)))))))))) (.run (.step 11 (.step 27 (.step 29 (.step 58 (.split 2 0 (.split 10 0 (.split 21 0 (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.split 49 0 (.step 67 (.step 74 (.step 34 (.split 65 1 (.step 27 (.step 3 (.close 5))) (.step 3 (.close 18)))))) (.step 3 (.step 12 (.step 17 (.step 23 (.close 27)))))) (.step 18 (.step 23 (.step 27 (.step 5 (.close 29)))))) (.step 12 (.step 18 (.step 23 (.step 5 (.step 29 (.step 5 (.close 27)))))))) (.step 3 (.step 18 (.step 27 (.close 15))))) (.step 12 (.step 18 (.step 23 (.step 5 (.step 27 (.close 5))))))) (.step 18 (.step 23 (.close 27)))) (.step 3 (.step 12 (.step 17 (.step 18 (.close 27)))))) (.step 12 (.step 23 (.step 27 (.close 5))))))))))) (.run (.step 5 (.close 27))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part58.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part59

namespace Part60
def root : Box := ⟨3533694129556768659166595001485837031654967793751237916243212404732723200, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337916811962788095558337111783654149077934949335851658420733929937495284077559808⟩
def references : Fin 1 → Box := ![Part59.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 27 (.step 3 (.close 5))))) (.run (.step 27 (.step 3 (.close 5))))) (.run (.step 3 (.step 5 (.step 23 (.step 27 (.step 29 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 2 0 (.split 12 0 (.split 21 0 (.split 22 0 (.step 9 (.step 29 (.step 3 (.close 5)))) (.step 3 (.step 4 (.step 9 (.close 23))))) (.step 3 (.step 4 (.step 9 (.step 18 (.close 23)))))) (.step 9 (.step 57 (.step 5 (.step 3 (.close 4)))))) (.step 3 (.step 5 (.step 9 (.step 23 (.close 12)))))) (.step 3 (.step 4 (.step 11 (.step 18 (.step 22 (.step 21 (.close 15)))))))) (.step 3 (.step 4 (.step 11 (.step 18 (.step 21 (.close 15))))))) (.step 23 (.step 9 (.step 5 (.close 3))))) (.step 3 (.step 4 (.step 9 (.step 15 (.close 23))))))))))))) (.run (.step 3 (.step 27 (.close 7))))) (.run (.step 27 (.step 3 (.close 5))))) (.run (.step 27 (.step 3 (.close 5))))) (.run (.step 3 (.step 11 (.step 27 (.close 7)))))) (.run (.step 3 (.step 5 (.step 7 (.step 27 (.close 29))))))) (.run (.step 5 (.close 27)))) (.run (.step 27 (.step 42 (.step 5 (.step 9 (.step 15 (.close 9)))))))) (.run (.step 3 (.step 5 (.step 7 (.step 29 (.close 27))))))) (.run (.step 3 (.step 5 (.step 29 (.close 27)))))) (.run (.step 3 (.step 5 (.step 7 (.step 29 (.close 27))))))) (.run (.step 3 (.step 7 (.step 18 (.step 27 (.close 7)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part59.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part60

namespace Part61
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214182428623890605080294909826495156679362059054547046462245407720210432⟩
def references : Fin 6 → Box := ![Part49.root, Part52.root, Part53.root, Part54.root, Part56.root, Part60.root]
def proof : Chunks.Proof 6 := (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 38 1 (.reuse 1) (.run (.step 16 (.step 31 (.step 38 (.step 37 (.step 58 (.split 54 1 (.split 63 1 (.split 64 1 (.split 65 1 (.step 5 (.step 28 (.step 41 (.split 71 1 (.split 2 0 (.step 37 (.step 3 (.step 5 (.close 3)))) (.step 3 (.step 5 (.step 31 (.close 37))))) (.step 31 (.step 37 (.close 3))))))) (.step 3 (.step 10 (.step 21 (.step 28 (.step 4 (.step 15 (.step 22 (.close 26))))))))) (.step 5 (.step 21 (.step 28 (.step 31 (.step 37 (.close 3))))))) (.step 5 (.step 15 (.step 28 (.step 31 (.close 37)))))) (.step 5 (.step 10 (.step 15 (.step 16 (.step 21 (.step 28 (.step 31 (.step 3 (.step 22 (.step 3 (.close 26))))))))))))))))))) (.reuse 2)) (.run (.step 29 (.step 31 (.step 37 (.step 38 (.close 3)))))))))) (.reuse 3)) (.reuse 4)) (.split 25 1 (.reuse 5) (.run (.step 3 (.step 5 (.step 27 (.step 29 (.step 27 (.step 5 (.close 3))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part49.excludes
  · exact Part52.excludes
  · exact Part53.excludes
  · exact Part54.excludes
  · exact Part56.excludes
  · exact Part60.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part61

namespace Part62
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567172216946143397854115110619787389832519696295652643207638274070229696970225106221133651794162302022531921488237563665165054379405623583503309524514584603863941081154985262927740723748296217148358461112434596470020112384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 54 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 24 0 (.split 25 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 49 0 (.split 50 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 11 (.step 18 (.step 3 (.step 7 (.close 18))))) (.step 3 (.step 7 (.step 4 (.step 12 (.close 18)))))) (.step 7 (.step 4 (.step 12 (.close 18))))) (.step 7 (.step 4 (.step 12 (.close 17))))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 11 (.step 17 (.close 18))))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 18 (.close 7)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 18 (.step 7 (.close 17))))) (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 67 (.close 3))))) (.step 11 (.step 18 (.step 66 (.close 3))))) (.step 3 (.step 18 (.step 11 (.step 7 (.step 17 (.step 18 (.step 17 (.close 19))))))))) (.step 11 (.step 18 (.step 27 (.step 7 (.step 17 (.step 18 (.step 17 (.close 19))))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 5 (.close 18))))))) (.step 3 (.step 4 (.step 18 (.step 11 (.close 23)))))) (.step 3 (.step 4 (.step 18 (.step 23 (.step 26 (.step 27 (.step 11 (.step 18 (.step 7 (.step 17 (.step 19 (.close 17))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part62

namespace Part63
def root : Box := ⟨3291009114642412084309938365114701009965471731267159728844701696, 5783591629511713964107239085095366868125894735225023512264238861626547736783701543274815007854993558757851736596865302263269978788357178970222307865022886919461037260889177424352726327933796458498532118018978467344970416128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 68 (.step 18 (.split 55 1 (.split 56 1 (.step 23 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.step 43 (.split 72 1 (.split 2 0 (.step 4 (.step 9 (.step 7 (.close 18)))) (.step 3 (.close 5))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.close 15)))))))) (.step 18 (.step 4 (.step 9 (.step 15 (.close 24)))))) (.step 3 (.close 7))) (.step 3 (.step 18 (.step 4 (.step 9 (.step 21 (.step 15 (.close 24)))))))) (.step 3 (.step 18 (.step 24 (.step 4 (.step 9 (.step 15 (.step 21 (.close 24))))))))) (.step 9 (.step 3 (.step 18 (.close 3))))) (.step 3 (.step 18 (.step 3 (.step 24 (.step 3 (.close 9)))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 18 (.step 4 (.step 21 (.close 22))))))))) (.step 3 (.step 4 (.step 5 (.close 18))))))) (.step 4 (.step 9 (.step 18 (.step 24 (.close 57)))))) (.step 3 (.step 7 (.step 9 (.close 26))))) (.step 3 (.step 9 (.step 18 (.step 3 (.step 4 (.step 21 (.step 18 (.step 3 (.step 26 (.step 3 (.close 27)))))))))))) (.step 3 (.step 9 (.step 18 (.step 4 (.step 27 (.step 18 (.step 3 (.step 4 (.close 52)))))))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 24 (.step 4 (.step 9 (.step 24 (.step 15 (.step 21 (.step 15 (.close 26))))))))))) (.step 3 (.step 5 (.step 24 (.step 31 (.step 3 (.step 4 (.close 5)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part63

namespace Part64
def root : Box := ⟨3291009114642412084309938365114701009965471731267159728844701696, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859316488118669907277963629666358809320881605340044460032⟩
def references : Fin 1 → Box := ![Part63.root]
def proof : Chunks.Proof 1 := (.step 18 (.step 23 (.split 24 1 (.split 25 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 39 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 18 (.step 21 (.step 23 (.step 3 (.step 21 (.step 24 (.step 27 (.close 42)))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 21 (.step 24 (.step 43 (.step 3 (.step 4 (.step 5 (.step 4 (.step 3 (.close 5)))))))))))))) (.run (.step 3 (.step 7 (.step 22 (.step 24 (.step 31 (.step 4 (.step 9 (.close 15)))))))))) (.run (.step 4 (.step 7 (.step 9 (.step 18 (.step 21 (.step 18 (.step 24 (.step 31 (.step 26 (.step 15 (.close 24))))))))))))) (.run (.step 3 (.step 7 (.step 15 (.step 24 (.step 31 (.close 37)))))))) (.run (.step 3 (.step 4 (.step 5 (.step 24 (.step 28 (.step 4 (.step 5 (.step 8 (.step 18 (.step 4 (.step 21 (.close 22)))))))))))))) (.run (.step 3 (.step 5 (.step 18 (.step 23 (.step 3 (.step 24 (.close 27)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part63.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part64

namespace Part65
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397854115110619787389832519696295652643207638274070229693696834498324991781780972605194932769271595517622100264896114255487369513119840029718908852088553914621452044780094086531402049090292067890747440889856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 24 0 (.split 25 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 49 0 (.split 50 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 11 (.step 18 (.step 3 (.step 7 (.close 18))))) (.step 3 (.step 7 (.step 4 (.step 12 (.close 18)))))) (.step 7 (.step 4 (.step 12 (.close 18))))) (.step 7 (.step 4 (.step 12 (.close 17))))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 11 (.step 17 (.close 18))))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 18 (.close 7)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 18 (.step 7 (.close 17))))) (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 51 (.step 19 (.step 3 (.close 20))))))) (.step 11 (.step 18 (.step 51 (.step 18 (.close 66)))))) (.step 3 (.step 18 (.step 11 (.step 7 (.step 17 (.step 18 (.step 17 (.close 19))))))))) (.step 11 (.step 18 (.step 27 (.step 7 (.step 17 (.step 18 (.step 17 (.close 19))))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 5 (.close 18))))))) (.step 3 (.step 4 (.step 18 (.step 11 (.close 22)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part65

namespace Part66
def root : Box := ⟨3369993333393832967488730139566630315351180455765195815489946779648, 11567172216946143397854115110619787389832519696295652643207634674939194062416315528305851079053609961830730256321126514963274967155901802055273423968230319988254228556331476572413648683055675612323714149232388692871564230656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.step 25 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 24 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 20 (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 17 (.step 4 (.step 14 (.close 18)))))) (.step 7 (.close 18))) (.step 11 (.step 18 (.step 7 (.close 17))))) (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.step 3 (.close 20)))))) (.step 11 (.step 18 (.step 20 (.step 3 (.close 19)))))) (.step 3 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 11 (.step 18 (.step 7 (.step 17 (.step 19 (.close 17)))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 18)))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.step 17 (.close 20))))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 20 (.step 19 (.step 20 (.close 27)))))))))) (.step 3 (.step 7 (.step 5 (.step 18 (.step 19 (.close 20))))))) (.step 11 (.step 18 (.step 19 (.step 20 (.step 7 (.close 27))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 18 (.step 19 (.close 20)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part66

namespace Part67
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859317984696346534122551870239627510794693733014968467456⟩
def references : Fin 2 → Box := ![Part65.root, Part66.root]
def proof : Chunks.Proof 2 := (.step 7 (.step 18 (.split 22 1 (.split 24 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 3 (.step 4 (.step 18 (.step 22 (.step 23 (.step 27 (.step 11 (.step 18 (.step 7 (.step 17 (.step 19 (.close 17)))))))))))))) (.run (.step 3 (.step 4 (.step 18 (.step 22 (.step 48 (.step 23 (.step 27 (.step 18 (.close 52))))))))))) (.run (.step 3 (.step 7 (.step 5 (.step 18 (.close 19))))))) (.run (.step 11 (.step 18 (.step 23 (.step 42 (.step 18 (.step 7 (.step 19 (.close 7)))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.close 18))))))) (.run (.step 3 (.step 4 (.step 18 (.step 22 (.step 11 (.step 23 (.step 3 (.step 29 (.step 38 (.step 3 (.step 18 (.step 19 (.close 20))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))) (.run (.step 11 (.step 18 (.step 23 (.step 27 (.step 18 (.step 7 (.close 17))))))))) (.step 18 (.split 24 1 (.split 25 1 (.reuse 1) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))) (.run (.step 11 (.step 18 (.step 20 (.step 27 (.step 7 (.step 17 (.close 19)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part65.excludes
  · exact Part66.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part67

namespace Part68
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519696295652643207638274070229696970225106221133651794162302022531921488237563665165054379405623583503309524514584602178944414458070277222553918140472218249721767419931836056977014784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 54 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 24 0 (.split 25 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 40 0 (.split 49 0 (.split 50 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 11 (.step 18 (.step 3 (.step 7 (.close 18))))) (.step 3 (.step 7 (.step 4 (.step 12 (.close 18)))))) (.step 7 (.step 4 (.step 12 (.close 18))))) (.step 7 (.step 4 (.step 12 (.close 17))))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 11 (.step 17 (.close 18))))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 18 (.close 7)))) (.step 7 (.step 5 (.close 18)))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 5 (.close 18)))) (.step 11 (.step 18 (.step 7 (.close 17))))) (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.step 3 (.close 19)))))) (.step 11 (.step 18 (.step 66 (.close 3))))) (.step 3 (.step 18 (.step 11 (.step 7 (.step 17 (.step 18 (.step 17 (.close 19))))))))) (.step 11 (.step 18 (.step 27 (.step 7 (.step 17 (.step 18 (.step 17 (.close 19))))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 5 (.close 18))))))) (.step 3 (.step 4 (.step 18 (.step 11 (.close 21)))))) (.step 3 (.step 4 (.step 18 (.step 21 (.step 23 (.step 27 (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part68

namespace Part69
def root : Box := ⟨3369993333393829977256380160539259670612012718250137599451963850752, 11567172216946143397854115110619787389832519696295652643207638274070229696973421776736657227839097057588424897854432995567733056625966339245569679202590221342337792430882861832275063738878005679691390919361650633308592144384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.step 67 (.split 24 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 24 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 25 (.close 3)) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 17 (.step 4 (.step 14 (.close 18)))))) (.step 7 (.close 18))) (.step 11 (.step 18 (.step 7 (.close 17))))) (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 3))))) (.step 3 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 18)))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 18 (.close 19)))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 27)))))))) (.step 3 (.step 7 (.step 5 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 19 (.close 27))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 18 (.close 19))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5))))))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 17 (.step 20 (.step 25 (.close 27))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part69

namespace Part70
def root : Box := ⟨2996078356528350982317553907068380190294663860584448, 11567172216946143397854115110619787389832519696295652643207638274070229696973421776736657227839097057588424897854432995567733056625966339245569679202590221342337792430882863328852740365722593920264659620835462760983516151808⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.split 24 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.step 19 (.step 67 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 24 0 (.split 25 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 20 (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 17 (.step 4 (.step 14 (.close 18)))))) (.step 7 (.close 18))) (.step 11 (.step 18 (.step 7 (.close 17))))) (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 18 (.close 19)))) (.step 11 (.step 18 (.step 19 (.close 3))))) (.step 3 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 11 (.step 18 (.step 7 (.step 17 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 18)))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 18 (.close 19))))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 27)))))))) (.step 3 (.step 7 (.step 5 (.step 18 (.close 19)))))) (.step 11 (.step 18 (.step 19 (.close 27))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.step 18 (.close 19))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5))))))) (.step 11 (.step 18 (.step 19 (.step 7 (.step 17 (.step 20 (.close 27))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part70

namespace Part71
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859317986157848171453454788443312343510976752670901010432⟩
def references : Fin 7 → Box := ![Part61.root, Part62.root, Part64.root, Part67.root, Part68.root, Part69.root, Part70.root]
def proof : Chunks.Proof 7 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.reuse 0) (.step 7 (.step 18 (.split 24 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.reuse 1) (.run (.step 3 (.step 4 (.step 18 (.step 26 (.step 44 (.step 48 (.step 23 (.step 27 (.step 18 (.close 52)))))))))))) (.run (.step 3 (.step 7 (.step 5 (.step 18 (.close 19))))))) (.run (.step 11 (.step 18 (.step 23 (.step 42 (.step 18 (.step 7 (.step 19 (.close 7)))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.close 18))))))) (.run (.step 3 (.step 4 (.step 18 (.step 23 (.step 26 (.step 3 (.step 11 (.step 23 (.step 29 (.step 38 (.step 3 (.step 18 (.step 19 (.close 20)))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))) (.run (.step 11 (.step 18 (.step 23 (.step 27 (.step 18 (.step 7 (.close 17)))))))))))) (.reuse 2)) (.reuse 3)) (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 49 1 (.reuse 4) (.run (.step 3 (.step 4 (.step 18 (.step 21 (.step 42 (.step 18 (.step 23 (.step 27 (.close 52))))))))))) (.run (.step 3 (.step 7 (.step 5 (.step 18 (.close 19))))))) (.run (.step 11 (.step 18 (.step 23 (.step 42 (.close 3))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.close 18))))))) (.run (.step 3 (.step 4 (.step 18 (.step 21 (.step 11 (.step 23 (.step 3 (.step 29 (.step 38 (.step 18 (.close 19))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.step 18 (.close 5)))))))) (.run (.step 11 (.step 18 (.step 23 (.step 27 (.step 18 (.step 7 (.close 17))))))))) (.reuse 5)) (.reuse 6)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part61.excludes
  · exact Part62.excludes
  · exact Part64.excludes
  · exact Part67.excludes
  · exact Part68.excludes
  · exact Part69.excludes
  · exact Part70.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part71

namespace Part72
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172211559764234668580634528507661192102192933666997071883059692865531460339987564072317884845273882113206989566793635383409608964026539057669267643373669094517548934877785191599654309327783189126106456465352438928375808⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 74 1 (.split 2 0 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 23 (.split 24 0 (.split 25 0 (.step 11 (.step 23 (.split 34 0 (.split 35 0 (.step 40 (.step 18 (.step 17 (.close 3)))) (.step 23 (.step 3 (.step 5 (.close 17))))) (.step 17 (.step 3 (.step 5 (.close 17))))))) (.step 23 (.step 27 (.step 3 (.close 5))))) (.step 11 (.step 23 (.step 27 (.step 3 (.close 5))))))) (.step 11 (.step 18 (.step 17 (.step 18 (.step 3 (.step 17 (.close 3)))))))) (.step 11 (.step 18 (.step 17 (.step 18 (.step 3 (.step 17 (.close 3)))))))) (.step 11 (.split 17 0 (.step 18 (.step 17 (.step 18 (.step 3 (.step 17 (.close 3)))))) (.step 17 (.step 3 (.close 7)))))) (.step 23 (.split 16 0 (.split 17 0 (.step 40 (.step 23 (.close 3))) (.step 3 (.close 17))) (.step 3 (.close 17))))) (.step 3 (.step 31 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 31 (.split 22 0 (.step 23 (.split 24 0 (.step 3 (.step 11 (.step 17 (.close 3)))) (.step 11 (.step 17 (.close 3))))) (.step 3 (.close 7)))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 3 (.step 4 (.step 12 (.close 17))))))) (.step 3 (.step 7 (.close 17)))) (.step 3 (.step 4 (.close 15))))))) (.step 11 (.step 3 (.step 5 (.close 9))))) (.step 11 (.step 23 (.step 17 (.close 5))))) (.step 11 (.step 17 (.close 3)))) (.step 23 (.step 29 (.step 40 (.step 69 (.step 3 (.step 11 (.step 23 (.step 3 (.close 5)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part72

namespace Part73
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467546697054282815846016033344698086848792670379351992324762781391981027695686895212065722286392712884367461144264652245651745780108727559660756244733444689290751365644549233736417280⟩
def references : Fin 1 → Box := ![Part72.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.reuse 0) (.run (.step 11 (.step 17 (.step 74 (.step 3 (.step 15 (.close 17)))))))) (.run (.step 3 (.step 11 (.step 17 (.step 23 (.step 17 (.close 3)))))))) (.run (.step 3 (.step 17 (.step 5 (.close 17)))))) (.run (.step 11 (.step 17 (.step 67 (.step 3 (.step 15 (.close 17)))))))) (.run (.step 11 (.step 17 (.step 66 (.step 3 (.step 12 (.close 17)))))))) (.run (.step 23 (.step 27 (.step 3 (.step 34 (.step 44 (.step 55 (.step 77 (.split 64 1 (.split 71 1 (.split 6 0 (.step 23 (.close 17)) (.step 9 (.close 11))) (.step 11 (.step 17 (.close 3)))) (.step 11 (.step 17 (.step 3 (.close 5)))))))))))))) (.run (.step 11 (.step 17 (.step 27 (.step 40 (.step 61 (.step 3 (.close 17))))))))) (.run (.step 3 (.step 5 (.step 17 (.close 12)))))) (.run (.step 5 (.step 12 (.step 18 (.step 27 (.step 40 (.step 48 (.step 11 (.step 17 (.step 58 (.step 12 (.step 17 (.close 21)))))))))))))) (.run (.step 3 (.step 5 (.step 23 (.step 9 (.step 15 (.step 5 (.close 23))))))))) (.run (.step 3 (.step 18 (.step 11 (.step 17 (.step 23 (.step 27 (.step 51 (.step 3 (.step 7 (.step 17 (.step 34 (.close 44))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part72.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part73

namespace Part74
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328372883776591027395682539081220876511041166738106827589234668324794309777067664567367704365256629220798870061056⟩
def references : Fin 1 → Box := ![Part73.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 23 (.step 27 (.step 31 (.step 34 (.step 48 (.step 55 (.step 23 (.step 61 (.step 67 (.split 51 1 (.split 54 1 (.split 71 1 (.split 59 1 (.split 74 1 (.split 6 0 (.split 10 0 (.split 12 0 (.step 23 (.close 17)) (.step 3 (.step 15 (.close 17)))) (.step 3 (.step 7 (.step 15 (.close 17))))) (.step 3 (.step 9 (.close 11)))) (.step 11 (.step 17 (.close 3)))) (.step 44 (.step 52 (.step 11 (.step 17 (.close 3)))))) (.step 3 (.step 11 (.step 17 (.step 3 (.close 5)))))) (.step 3 (.step 9 (.step 15 (.step 21 (.close 23)))))) (.step 3 (.step 7 (.step 17 (.step 34 (.close 44))))))))))))))))) (.run (.step 17 (.step 23 (.step 27 (.step 31 (.step 34 (.step 48 (.step 52 (.step 23 (.step 34 (.step 31 (.step 11 (.step 3 (.step 4 (.close 17)))))))))))))))) (.run (.step 3 (.step 8 (.step 11 (.step 3 (.step 7 (.close 27)))))))) (.run (.step 3 (.step 5 (.step 7 (.step 23 (.step 31 (.step 11 (.step 17 (.step 23 (.step 29 (.step 31 (.step 17 (.step 40 (.step 3 (.step 37 (.close 39))))))))))))))))) (.run (.step 5 (.step 7 (.step 11 (.step 17 (.step 18 (.step 23 (.step 17 (.step 18 (.step 27 (.step 31 (.step 17 (.close 34)))))))))))))) (.run (.step 11 (.step 17 (.step 23 (.step 27 (.step 31 (.step 34 (.step 40 (.step 42 (.step 3 (.step 5 (.close 17))))))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 5 (.step 17 (.step 18 (.step 12 (.step 23 (.step 12 (.close 17))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part73.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part74

namespace Part75
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184113620557301995282076516331891981187325322419437640065999289974784⟩
def references : Fin 1 → Box := ![Part74.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 7 (.step 23 (.step 31 (.step 36 (.step 29 (.step 5 (.step 23 (.step 40 (.step 66 (.step 7 (.step 31 (.step 17 (.step 37 (.close 39)))))))))))))))))) (.run (.step 3 (.step 5 (.step 23 (.step 40 (.step 42 (.step 66 (.step 67 (.step 74 (.step 75 (.split 36 1 (.split 42 1 (.step 23 (.split 54 1 (.split 58 1 (.step 29 (.step 38 (.step 11 (.step 17 (.step 5 (.close 15)))))) (.step 11 (.step 17 (.step 3 (.close 5))))) (.step 9 (.step 15 (.step 21 (.step 23 (.close 5))))))) (.step 3 (.step 5 (.step 29 (.step 31 (.close 17)))))) (.step 3 (.step 5 (.step 29 (.step 31 (.step 17 (.close 37)))))))))))))))))) (.run (.step 3 (.step 5 (.step 7 (.step 23 (.step 31 (.step 34 (.step 29 (.step 38 (.step 40 (.step 3 (.step 5 (.step 17 (.step 7 (.step 31 (.step 17 (.close 37)))))))))))))))))) (.run (.step 3 (.step 7 (.step 11 (.step 17 (.step 18 (.step 31 (.step 17 (.step 40 (.step 3 (.close 17)))))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 27 (.step 29 (.step 5 (.close 17))))))))) (.run (.step 11 (.step 17 (.step 23 (.step 27 (.step 29 (.step 27 (.step 3 (.close 5)))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.split 25 1 (.step 17 (.step 5 (.step 7 (.step 17 (.close 18))))) (.step 3 (.step 5 (.step 14 (.close 17)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part74.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part75

namespace Part76
def root : Box := ⟨2658455991569831745807614122708172800, 5783586108473071698929506996965222366134733773348527141407923008016672350681718035541022399026612296277126544664187617307456080980580890709586168959310607092057633030929658993078924782627008690931132018670731268688896327680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.split 10 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.split 38 0 (.split 40 0 (.split 42 0 (.step 55 (.step 3 (.step 4 (.step 3 (.step 7 (.close 15)))))) (.step 9 (.step 18 (.close 15)))) (.step 3 (.step 5 (.close 15)))) (.step 3 (.step 5 (.step 12 (.step 5 (.close 15))))))) (.step 9 (.step 22 (.step 3 (.close 15))))) (.step 9 (.step 21 (.step 15 (.step 3 (.close 5)))))) (.step 9 (.step 31 (.split 38 0 (.step 15 (.close 3)) (.step 15 (.close 3)))))) (.step 3 (.step 9 (.step 18 (.step 15 (.close 3)))))) (.step 9 (.step 29 (.step 3 (.close 5))))) (.split 16 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 27 (.step 15 (.close 3))) (.step 3 (.step 5 (.step 12 (.close 15))))) (.step 3 (.step 5 (.close 15)))) (.step 9 (.step 21 (.step 15 (.step 3 (.close 5)))))) (.step 3 (.step 15 (.close 5)))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 5 (.step 12 (.step 15 (.close 5)))))) (.step 3 (.step 4 (.step 17 (.step 15 (.close 18))))))) (.step 9 (.step 18 (.step 15 (.close 3))))) (.step 40 (.split 21 0 (.split 24 0 (.split 25 0 (.step 55 (.step 15 (.close 3))) (.step 3 (.step 5 (.step 12 (.close 5))))) (.step 23 (.step 9 (.step 12 (.close 15))))) (.step 3 (.step 4 (.step 15 (.close 17))))))) (.step 3 (.step 18 (.step 9 (.step 15 (.close 3)))))) (.step 9 (.step 11 (.step 3 (.close 5))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part76

namespace Part77
def root : Box := ⟨2658455991569831745807614122708172800, 11567172216946143397859013993930440276761051895965817490610133931617286262093729057958571730942313403664872514023366867554099341909929416397322129741445905408236910208876297454578207448153926209234407966954072850803071123456⟩
def references : Fin 1 → Box := ![Part76.root]
def proof : Chunks.Proof 1 := (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.reuse 0) (.run (.step 3 (.step 9 (.step 31 (.split 14 0 (.step 58 (.split 16 0 (.step 3 (.step 12 (.step 5 (.close 15)))) (.step 3 (.close 4)))) (.step 3 (.step 5 (.close 12))))))))) (.run (.step 23 (.step 5 (.step 3 (.step 9 (.close 15))))))) (.run (.step 9 (.step 15 (.step 23 (.step 26 (.step 23 (.step 5 (.step 3 (.close 4)))))))))) (.run (.step 23 (.step 29 (.step 75 (.split 2 0 (.split 6 0 (.step 66 (.step 22 (.step 57 (.step 23 (.close 3))))) (.step 9 (.step 4 (.close 11)))) (.step 3 (.step 9 (.step 12 (.step 22 (.step 15 (.close 5)))))))))))) (.run (.step 3 (.step 9 (.step 3 (.close 7)))))) (.run (.step 3 (.step 9 (.close 15))))) (.run (.step 23 (.step 29 (.step 55 (.step 75 (.split 65 1 (.split 71 1 (.split 2 0 (.split 6 0 (.step 66 (.step 21 (.step 23 (.step 3 (.close 15))))) (.step 9 (.step 4 (.close 11)))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 15 (.close 5))))))) (.step 66 (.step 67 (.close 3)))) (.step 3 (.step 9 (.close 15))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part76.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part77

namespace Part78
def root : Box := ⟨2658455991569831745807614122708172800, 11567172216946143397859013993930444732269467546697054282815846016033344698086848792670379351992324762781391981027695686895212065722286392712884367461144264652245651745780108727559659362449487764521129321256156315771422638080⟩
def references : Fin 1 → Box := ![Part77.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 0) (.run (.step 15 (.step 23 (.step 29 (.step 66 (.split 2 0 (.split 10 0 (.split 21 0 (.split 30 0 (.split 38 0 (.split 40 0 (.split 49 0 (.split 55 0 (.step 15 (.step 3 (.step 11 (.step 17 (.close 18))))) (.step 12 (.step 18 (.step 9 (.close 15))))) (.step 9 (.step 12 (.step 15 (.close 17))))) (.step 9 (.step 15 (.close 3)))) (.step 9 (.step 12 (.step 15 (.step 3 (.close 5)))))) (.step 3 (.step 9 (.close 15)))) (.step 3 (.step 9 (.step 15 (.step 4 (.close 18)))))) (.step 3 (.step 9 (.step 12 (.close 15))))) (.step 3 (.step 9 (.step 12 (.step 15 (.close 5)))))))))))) (.run (.step 9 (.step 3 (.step 15 (.step 23 (.step 26 (.step 23 (.close 3))))))))) (.run (.step 3 (.step 22 (.step 23 (.step 40 (.step 62 (.split 2 0 (.split 6 0 (.split 10 0 (.step 22 (.split 21 0 (.split 30 0 (.step 34 (.step 27 (.step 40 (.step 3 (.step 5 (.step 3 (.close 4))))))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 4 (.close 15))))) (.step 3 (.step 4 (.close 15)))) (.step 9 (.close 11))) (.step 3 (.step 5 (.step 9 (.step 12 (.close 15))))))))))))) (.run (.step 3 (.step 5 (.step 15 (.step 22 (.step 9 (.step 31 (.step 48 (.step 16 (.step 57 (.step 5 (.step 3 (.close 15)))))))))))))) (.run (.step 3 (.step 40 (.step 48 (.step 9 (.step 58 (.step 3 (.step 4 (.close 12)))))))))) (.run (.step 9 (.step 15 (.close 23))))) (.run (.step 3 (.step 9 (.step 15 (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part77.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part78

namespace Part79
def root : Box := ⟨2658455991569831745807614122708172800, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328372883776591027395682539081220876511041166738106827589234668324794308383272418887199542935147140987336556281856⟩
def references : Fin 1 → Box := ![Part78.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 9 (.step 15 (.step 3 (.step 21 (.close 53))))))) (.run (.step 9 (.step 15 (.step 3 (.step 34 (.step 52 (.close 3)))))))) (.run (.step 3 (.step 9 (.close 7))))) (.run (.step 7 (.step 15 (.step 26 (.step 29 (.step 31 (.step 26 (.step 15 (.close 3)))))))))) (.run (.step 3 (.step 5 (.step 9 (.step 23 (.step 24 (.step 31 (.step 34 (.step 31 (.step 5 (.step 15 (.step 31 (.step 3 (.close 5))))))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 23 (.step 34 (.step 40 (.step 62 (.split 40 1 (.split 54 1 (.split 55 1 (.split 58 1 (.split 2 0 (.split 6 0 (.split 10 0 (.step 21 (.split 14 0 (.split 17 0 (.step 9 (.split 21 0 (.step 40 (.step 3 (.close 5))) (.step 3 (.step 4 (.close 15))))) (.step 3 (.step 4 (.close 15)))) (.step 12 (.close 15)))) (.step 3 (.step 4 (.close 15)))) (.step 9 (.close 11))) (.step 3 (.step 5 (.step 9 (.step 12 (.close 15)))))) (.step 27 (.step 34 (.step 42 (.close 5))))) (.step 4 (.step 5 (.step 12 (.step 15 (.step 21 (.step 15 (.step 11 (.close 22))))))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 4 (.step 18 (.close 22)))))))) (.step 3 (.step 5 (.step 9 (.step 15 (.step 21 (.step 15 (.step 22 (.close 23)))))))))))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 21 (.step 31 (.step 43 (.step 15 (.step 48 (.step 16 (.step 9 (.step 28 (.step 41 (.step 3 (.step 5 (.close 3)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part78.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part79

namespace Part80
def root : Box := ⟨2658455991569831745807614122708172800, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184113620557301995282076514938096735507157160989328151832536976195584⟩
def references : Fin 1 → Box := ![Part79.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 24 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 15 (.step 22 (.step 29 (.step 31 (.step 22 (.step 15 (.step 3 (.step 7 (.close 26)))))))))))) (.run (.step 9 (.step 15 (.step 21 (.step 29 (.step 31 (.close 38)))))))) (.run (.step 7 (.step 15 (.step 29 (.step 31 (.step 3 (.step 15 (.step 3 (.step 21 (.close 22))))))))))) (.run (.step 3 (.step 7 (.step 9 (.step 15 (.step 18 (.close 15)))))))) (.run (.step 3 (.step 5 (.step 16 (.step 29 (.step 9 (.step 15 (.step 3 (.step 5 (.step 16 (.close 28)))))))))))) (.run (.step 3 (.step 5 (.step 23 (.step 27 (.step 29 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 57 (.split 2 0 (.split 21 0 (.split 25 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 34 (.step 9 (.step 27 (.step 3 (.close 5))))) (.step 9 (.step 21 (.step 15 (.step 3 (.step 5 (.close 22))))))) (.step 3 (.step 5 (.step 9 (.close 15))))) (.step 3 (.step 4 (.step 9 (.step 15 (.close 17)))))) (.step 3 (.step 5 (.step 9 (.step 12 (.close 15)))))) (.step 3 (.step 4 (.step 9 (.close 15))))) (.step 3 (.step 5 (.step 9 (.step 12 (.close 15))))))) (.step 3 (.step 4 (.step 22 (.step 9 (.close 15)))))) (.step 3 (.step 4 (.step 21 (.step 9 (.close 15)))))) (.step 12 (.step 15 (.step 23 (.step 3 (.close 9)))))) (.step 3 (.step 4 (.step 9 (.close 15)))))))))))) (.run (.step 3 (.step 4 (.step 7 (.step 18 (.step 23 (.close 9))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part79.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part80

namespace Part81
def root : Box := ⟨2535301200456458802995553894400, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859317986157849565251358925870694205594502001750478684160⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 12 1 (.split 14 1 (.split 24 1 (.split 25 1 (.split 35 1 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 7 (.close 3)) (.step 3 (.close 12))) (.step 3 (.step 18 (.step 3 (.close 9))))) (.step 3 (.step 18 (.step 3 (.step 9 (.close 15)))))) (.step 3 (.step 18 (.step 31 (.close 7))))) (.step 3 (.step 18 (.step 7 (.close 17))))) (.step 3 (.step 7 (.close 4)))) (.step 3 (.step 9 (.step 15 (.step 18 (.close 21)))))) (.step 3 (.step 7 (.step 18 (.step 31 (.step 52 (.close 53))))))) (.step 3 (.step 7 (.step 18 (.step 31 (.step 52 (.step 18 (.step 31 (.close 7))))))))) (.step 3 (.step 18 (.step 27 (.close 31))))) (.step 3 (.step 7 (.step 4 (.close 18))))) (.step 3 (.step 18 (.step 29 (.step 38 (.step 18 (.step 3 (.step 9 (.close 15))))))))) (.step 3 (.step 7 (.step 4 (.close 18))))) (.step 3 (.step 18 (.step 27 (.close 7))))) (.step 3 (.step 17 (.step 3 (.step 7 (.close 17)))))) (.step 3 (.step 9 (.step 15 (.close 3))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part81

namespace Part82
def root : Box := ⟨2305843011361177600, 11567166701293880295871715260525731212784506188745507509654982426332330825965067704899079271435554413467390359069912684617862840489756857915655542664878482117760472138018703424683014911772285852707773891783783186095936634880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.step 9 (.step 3 (.close 4))) (.step 9 (.close 3))) (.step 9 (.close 3))) (.step 3 (.step 9 (.close 3)))) (.step 9 (.step 5 (.close 3)))) (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.split 56 0 (.split 65 0 (.split 12 0 (.split 16 0 (.step 9 (.step 3 (.close 4))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 9 (.step 4 (.close 11)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9))))) (.step 40 (.split 24 0 (.split 25 0 (.split 30 0 (.split 38 0 (.step 55 (.step 9 (.step 3 (.close 11)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 11 (.close 9))))) (.step 3 (.step 18 (.close 9)))) (.step 3 (.step 9 (.step 3 (.close 5))))) (.step 11 (.step 5 (.step 3 (.close 9))))) (.step 11 (.step 29 (.split 2 0 (.split 10 0 (.step 22 (.split 30 0 (.split 38 0 (.step 9 (.step 3 (.close 4))) (.step 9 (.close 3))) (.step 3 (.close 9)))) (.step 3 (.close 9))) (.step 3 (.step 9 (.close 5))))))) (.step 3 (.step 7 (.close 9)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part82

namespace Part83
def root : Box := ⟨2305843011361177600, 11567166701293880295871715265202237301355671934531683899968144833585639542944955558488161050875353607757221209543045932993548131590130186441825560111086111525259512058275846634621800384409160926681989160924386222930660425728⟩
def references : Fin 1 → Box := ![Part82.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 58 1 (.reuse 0) (.run (.step 3 (.step 11 (.split 2 0 (.split 10 0 (.step 22 (.split 24 0 (.split 14 0 (.step 9 (.step 3 (.close 5))) (.step 11 (.step 5 (.close 3)))) (.step 27 (.step 5 (.close 9))))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))))))) (.run (.step 3 (.close 9)))) (.run (.step 9 (.step 11 (.step 29 (.split 65 1 (.split 71 1 (.split 2 0 (.split 10 0 (.step 21 (.split 30 0 (.split 40 0 (.step 9 (.step 3 (.close 4))) (.step 9 (.close 3))) (.step 3 (.close 9)))) (.step 3 (.close 9))) (.step 3 (.step 9 (.close 5)))) (.step 67 (.close 3))) (.step 3 (.close 9)))))))) (.run (.step 9 (.step 11 (.step 29 (.split 65 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 21 0 (.split 30 0 (.split 35 0 (.split 64 1 (.split 71 1 (.split 38 0 (.split 40 0 (.split 16 0 (.step 9 (.step 3 (.close 4))) (.step 3 (.step 11 (.close 9)))) (.step 9 (.close 3))) (.step 9 (.step 3 (.close 5)))) (.step 22 (.close 66))) (.step 21 (.close 66))) (.step 9 (.close 11))) (.step 9 (.step 3 (.close 4)))) (.step 9 (.step 4 (.close 11)))) (.step 11 (.close 9))) (.step 9 (.step 3 (.step 4 (.close 11))))) (.step 9 (.step 3 (.step 5 (.close 11))))) (.step 3 (.close 9)))))))) (.run (.step 3 (.step 5 (.step 10 (.step 22 (.step 9 (.step 31 (.step 3 (.close 5)))))))))) (.run (.step 3 (.step 10 (.step 40 (.step 48 (.step 5 (.close 9)))))))) (.run (.step 3 (.step 9 (.close 7))))) (.run (.step 3 (.step 9 (.close 7)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part82.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part83

namespace Part84
def root : Box := ⟨2305843011361177600, 11567166701293880295871715265202237301355671934531683899968144833585639542944955558488161050875356315445054148470418453694452808193726481639126641626077878952924809567243312614488063900546447210674429129668533413989116280832⟩
def references : Fin 1 → Box := ![Part83.root]
def proof : Chunks.Proof 1 := (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 9 (.step 10 (.step 29 (.step 31 (.step 26 (.step 7 (.close 9)))))))))) (.run (.step 3 (.step 5 (.step 9 (.step 10 (.step 11 (.step 24 (.step 9 (.step 31 (.close 5))))))))))) (.run (.step 3 (.step 5 (.step 9 (.step 11 (.split 40 1 (.split 55 1 (.split 58 1 (.split 2 0 (.split 10 0 (.step 21 (.split 12 0 (.split 14 0 (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.step 9 (.step 3 (.close 4))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 11 (.step 3 (.close 5)))) (.step 9 (.step 4 (.close 11))))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 27 (.step 42 (.step 5 (.close 9))))) (.step 4 (.step 5 (.step 21 (.step 9 (.step 22 (.step 9 (.close 11)))))))) (.step 3 (.step 5 (.step 9 (.close 11))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 21 (.step 31 (.step 48 (.close 9))))))))) (.run (.step 7 (.step 9 (.step 10 (.step 29 (.step 31 (.step 22 (.step 9 (.close 3)))))))))) (.run (.step 7 (.step 9 (.step 10 (.step 15 (.step 29 (.step 31 (.step 37 (.step 3 (.close 7))))))))))) (.run (.step 3 (.step 7 (.step 9 (.step 3 (.close 7))))))) (.run (.step 3 (.step 5 (.step 10 (.step 9 (.close 29)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part83.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part84

namespace Part85
def root : Box := ⟨2305843011361177600, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859317986157849565251358925870694205595654923255085531136⟩
def references : Fin 1 → Box := ![Part84.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.split 14 1 (.split 16 1 (.split 17 1 (.step 9 (.split 21 1 (.split 22 1 (.split 24 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 9 (.step 11 (.step 27 (.split 2 0 (.split 10 0 (.split 25 0 (.split 30 0 (.split 38 0 (.split 40 0 (.split 56 0 (.split 65 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.step 3 (.close 4))) (.step 3 (.step 4 (.step 9 (.close 11))))) (.step 3 (.step 4 (.close 11)))) (.step 11 (.step 3 (.close 4)))) (.step 9 (.close 11))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9)))) (.step 3 (.step 4 (.close 9)))) (.step 3 (.step 5 (.close 9))))))))))) (.run (.step 3 (.step 4 (.step 7 (.close 11)))))) (.run (.step 4 (.step 7 (.close 9)))))) (.run (.step 3 (.step 4 (.step 7 (.step 9 (.close 11))))))) (.run (.step 3 (.step 4 (.step 7 (.step 11 (.close 9))))))) (.run (.step 3 (.step 5 (.step 11 (.close 9)))))) (.run (.step 9 (.step 3 (.step 7 (.close 11)))))) (.run (.step 3 (.step 7 (.step 9 (.step 3 (.step 9 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part84.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part85

namespace Part86
def root : Box := ⟨2149580800, 11567172216946143397854115110619787389832519696295652639433675849248688344731867195748388336922178544854647860267379134962731524675915685369614386703281446977179206799352145085730630403359058123136277143970998472580905566208⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 6 0 (.split 10 0 (.split 12 0 (.step 5 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 5 (.split 49 0 (.step 5 (.step 3 (.step 11 (.step 23 (.close 5))))) (.step 3 (.step 12 (.step 5 (.close 21)))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 5 (.step 15 (.close 37))))) (.step 3 (.step 5 (.close 27)))) (.step 3 (.step 5 (.step 18 (.close 27))))) (.step 3 (.step 5 (.step 18 (.close 27))))) (.step 5 (.step 17 (.step 23 (.step 12 (.step 18 (.step 12 (.close 14))))))))) (.step 3 (.step 23 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.step 11 (.step 5 (.close 9))))) (.step 5 (.step 23 (.step 43 (.step 66 (.step 43 (.step 12 (.close 14)))))))) (.step 3 (.step 5 (.step 29 (.step 40 (.step 74 (.close 75))))))) (.step 3 (.close 5))) (.step 3 (.step 9 (.step 23 (.step 5 (.step 23 (.close 5))))))) (.step 5 (.step 23 (.step 27 (.step 43 (.step 12 (.close 42))))))) (.step 3 (.step 5 (.step 9 (.step 23 (.step 5 (.step 23 (.close 5)))))))) (.step 3 (.step 9 (.step 23 (.step 5 (.step 21 (.step 27 (.step 23 (.close 5))))))))) (.step 3 (.step 9 (.step 12 (.step 23 (.step 5 (.step 27 (.step 34 (.step 40 (.close 5)))))))))) (.step 3 (.step 5 (.step 31 (.step 37 (.step 39 (.step 37 (.close 41)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part86

namespace Part87
def root : Box := ⟨2149580800, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859317986157849565251358925870694205595654923255086579712⟩
def references : Fin 1 → Box := ![Part86.root]
def proof : Chunks.Proof 1 := (.step 3 (.split 6 1 (.split 12 1 (.step 43 (.step 58 (.split 14 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 24 1 (.split 25 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 5 (.split 39 1 (.reuse 0) (.run (.step 5 (.step 21 (.step 27 (.step 23 (.step 42 (.close 12))))))))) (.run (.step 5 (.close 3)))) (.run (.step 3 (.step 5 (.step 31 (.close 39)))))) (.run (.step 3 (.step 5 (.step 21 (.step 29 (.step 38 (.step 40 (.step 38 (.close 5)))))))))) (.run (.step 3 (.step 5 (.step 28 (.step 5 (.step 31 (.close 37)))))))) (.run (.step 5 (.step 3 (.close 28))))) (.run (.step 5 (.close 27)))) (.run (.step 3 (.step 5 (.close 18))))) (.run (.step 3 (.close 5)))) (.run (.step 3 (.step 4 (.step 5 (.close 18)))))) (.run (.step 3 (.step 4 (.step 5 (.close 18)))))) (.run (.step 5 (.step 17 (.step 23 (.close 17)))))))) (.run (.step 3 (.step 4 (.step 5 (.step 9 (.step 12 (.step 15 (.step 23 (.step 16 (.step 31 (.step 5 (.step 15 (.close 5)))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 9 (.step 5 (.close 9)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part86.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part87

namespace Part88
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467546697054282815846016033344701363436071082044798053224592554253089328375234614912161961161781419172337918621214184115266061859317986157849565251358925870694205595654923255086579712⟩
def references : Fin 6 → Box := ![Part71.root, Part75.root, Part80.root, Part81.root, Part85.root, Part87.root]
def proof : Chunks.Proof 6 := (.split 2 1 (.split 6 1 (.split 10 1 (.split 12 1 (.split 14 1 (.reuse 0) (.step 23 (.split 16 1 (.split 17 1 (.reuse 1) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 74 (.step 17 (.step 7 (.step 18 (.step 3 (.step 7 (.close 17))))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.step 67 (.step 17 (.step 5 (.step 7 (.step 17 (.close 18))))))))))))))) (.split 14 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 2) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.step 18 (.step 15 (.step 3 (.step 15 (.step 3 (.close 18)))))))))))) (.run (.step 3 (.step 4 (.step 7 (.step 18 (.close 22))))))) (.run (.step 3 (.step 4 (.step 7 (.step 18 (.close 21))))))) (.run (.step 3 (.step 5 (.step 12 (.step 15 (.step 17 (.step 23 (.step 5 (.step 3 (.step 9 (.close 15))))))))))))) (.reuse 3)) (.reuse 4)) (.reuse 5))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part71.excludes
  · exact Part75.excludes
  · exact Part80.excludes
  · exact Part81.excludes
  · exact Part85.excludes
  · exact Part87.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part88

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part88.excludes
end FiveColour.Packed.Chunked.Case7
