module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case263
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320739514560393474085715600998401⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨21147804418224193522998, 5653543574944809734216459823660801489576522078620855821178834661651632152003592601918852037219013942892917655553525559658949764092620606276399307326740011991056444881747577005808722435159187886012534539862748905366093825, 0⟩]
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
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447923491190280007596173915924144464963797397887748648802769449202326658827291721729⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 29 0 (.split 31 0 (.split 33 0 (.split 37 0 (.split 40 0 (.split 45 0 (.split 54 0 (.split 60 0 (.split 73 0 (.step 4 (.split 46 0 (.step 38 (.close 37)) (.step 37 (.step 38 (.close 39))))) (.step 31 (.step 45 (.close 38)))) (.step 31 (.step 63 (.split 46 0 (.step 38 (.close 37)) (.step 37 (.step 38 (.close 39))))))) (.step 31 (.step 39 (.close 38)))) (.step 31 (.step 48 (.split 46 0 (.step 38 (.close 37)) (.step 37 (.step 38 (.close 39))))))) (.step 31 (.close 4))) (.step 31 (.close 5))) (.step 31 (.step 39 (.step 51 (.step 4 (.close 31)))))) (.step 31 (.split 33 0 (.split 34 0 (.split 35 0 (.step 5 (.step 4 (.step 31 (.close 4)))) (.step 4 (.close 31))) (.step 31 (.close 4))) (.step 40 (.step 43 (.step 31 (.close 4))))))) (.split 31 0 (.split 33 0 (.split 34 0 (.split 35 0 (.step 31 (.step 50 (.close 31))) (.step 31 (.step 38 (.close 4)))) (.step 31 (.step 37 (.close 38)))) (.step 31 (.step 32 (.close 31)))) (.step 31 (.step 32 (.step 4 (.close 5)))))))
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
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524750123642650625, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672959198988366246553201244731071610414846809452427893640195535561008611329⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 35 0 (.step 47 (.split 37 0 (.split 40 0 (.step 5 (.split 45 0 (.split 54 0 (.split 60 0 (.step 39 (.close 12)) (.step 31 (.step 39 (.close 38)))) (.step 31 (.close 39))) (.step 31 (.step 39 (.close 38))))) (.step 5 (.close 21))) (.step 5 (.close 31)))) (.step 41 (.step 4 (.step 28 (.step 38 (.step 31 (.close 39))))))) (.split 37 0 (.split 40 0 (.step 47 (.step 37 (.split 28 0 (.split 45 0 (.step 5 (.split 54 0 (.step 38 (.close 39)) (.step 31 (.close 38)))) (.step 31 (.step 38 (.close 39)))) (.step 31 (.close 38))))) (.step 31 (.close 4))) (.step 5 (.step 31 (.step 4 (.close 8)))))) (.step 31 (.step 5 (.step 28 (.step 31 (.close 51)))))) (.step 31 (.split 33 0 (.step 5 (.step 28 (.step 31 (.close 49)))) (.step 31 (.close 24))))) (.step 31 (.split 31 0 (.step 41 (.step 47 (.step 50 (.close 31)))) (.step 31 (.step 5 (.close 32)))))) (.split 37 0 (.split 40 0 (.split 44 0 (.split 45 0 (.split 46 0 (.split 47 0 (.step 29 (.step 4 (.close 28))) (.step 28 (.close 6))) (.step 28 (.close 6))) (.step 6 (.close 28))) (.step 47 (.close 6))) (.step 6 (.step 4 (.close 5)))) (.step 6 (.step 4 (.close 5))))))
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
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672959198988366246553201244731071610414846809452427893640195535561008611329⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 25 0 (.split 26 0 (.reuse 0) (.run (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 38 0 (.step 47 (.split 37 0 (.split 40 0 (.step 4 (.split 45 0 (.split 54 0 (.split 60 0 (.step 39 (.close 12)) (.step 31 (.step 39 (.close 38)))) (.step 31 (.close 39))) (.step 31 (.step 39 (.close 38))))) (.step 4 (.close 21))) (.step 4 (.close 31)))) (.step 38 (.step 4 (.step 29 (.step 41 (.step 31 (.close 39))))))) (.split 37 0 (.split 40 0 (.step 47 (.step 37 (.split 28 0 (.split 45 0 (.step 5 (.split 54 0 (.step 38 (.close 39)) (.step 31 (.close 38)))) (.step 31 (.step 38 (.close 39)))) (.step 31 (.close 38))))) (.step 4 (.step 29 (.step 31 (.close 4))))) (.step 31 (.close 5)))) (.step 31 (.step 4 (.step 29 (.step 31 (.close 51)))))) (.step 31 (.split 33 0 (.step 4 (.step 29 (.step 31 (.close 66)))) (.step 31 (.close 23))))) (.step 31 (.split 31 0 (.step 38 (.step 47 (.step 67 (.close 31)))) (.step 31 (.step 4 (.close 32)))))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945763423537266707370630157278031587540262423187308073189377⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 19 0 (.split 23 0 (.reuse 0) (.run (.step 31 (.split 25 0 (.split 26 0 (.split 29 0 (.step 69 (.split 31 0 (.step 45 (.step 48 (.step 63 (.step 31 (.close 38))))) (.step 23 (.step 24 (.step 31 (.close 22)))))) (.step 31 (.step 32 (.step 23 (.step 26 (.close 4)))))) (.step 31 (.split 29 0 (.step 69 (.step 63 (.step 75 (.step 31 (.close 38))))) (.step 31 (.step 23 (.close 10)))))) (.step 31 (.split 26 0 (.split 29 0 (.step 69 (.step 48 (.split 31 0 (.step 45 (.step 48 (.step 31 (.step 28 (.close 38))))) (.step 31 (.close 24))))) (.step 31 (.step 24 (.close 9)))) (.step 6 (.step 28 (.close 29))))))))) (.run (.step 31 (.split 23 0 (.split 25 0 (.split 26 0 (.split 29 0 (.step 51 (.split 31 0 (.step 48 (.step 31 (.step 51 (.step 31 (.close 38))))) (.step 23 (.step 24 (.step 31 (.close 22)))))) (.step 31 (.step 32 (.step 23 (.step 22 (.close 4)))))) (.step 31 (.split 29 0 (.step 51 (.step 63 (.split 31 0 (.step 39 (.step 51 (.step 4 (.step 29 (.step 31 (.close 38)))))) (.step 31 (.close 22))))) (.step 31 (.step 22 (.close 23)))))) (.step 31 (.split 26 0 (.split 29 0 (.step 51 (.step 48 (.step 59 (.step 31 (.close 38))))) (.step 31 (.step 24 (.close 9)))) (.step 6 (.step 28 (.close 29)))))) (.step 31 (.split 25 0 (.split 33 0 (.step 69 (.split 41 0 (.step 51 (.close 63)) (.step 23 (.close 26)))) (.step 23 (.step 22 (.close 4)))) (.step 31 (.step 22 (.close 24)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573259488515625058737849446041926430256791553⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 18 0 (.reuse 0) (.run (.split 19 0 (.split 23 0 (.split 25 0 (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.step 48 (.step 63 (.step 31 (.step 38 (.close 39))))) (.step 31 (.step 37 (.close 38)))) (.step 23 (.step 24 (.step 31 (.close 22))))) (.step 31 (.step 23 (.step 24 (.step 31 (.close 22)))))) (.step 31 (.step 32 (.step 23 (.step 5 (.step 31 (.close 4))))))) (.step 31 (.split 29 0 (.split 31 0 (.step 38 (.step 63 (.step 31 (.step 29 (.close 39))))) (.step 31 (.close 23))) (.step 31 (.close 38))))) (.step 31 (.split 26 0 (.split 29 0 (.split 31 0 (.step 41 (.step 48 (.step 31 (.step 28 (.close 38))))) (.step 31 (.close 24))) (.step 31 (.close 41))) (.step 6 (.step 28 (.close 29)))))) (.step 31 (.split 25 0 (.split 41 0 (.split 44 0 (.split 26 0 (.step 69 (.step 21 (.close 4))) (.step 31 (.step 21 (.close 4)))) (.step 69 (.step 23 (.step 47 (.step 24 (.step 31 (.close 4))))))) (.step 23 (.close 26))) (.step 31 (.step 21 (.close 24)))))) (.split 25 0 (.split 26 0 (.split 35 0 (.split 28 0 (.split 29 0 (.step 31 (.step 51 (.step 21 (.close 31)))) (.step 32 (.step 22 (.step 23 (.step 24 (.close 26)))))) (.step 31 (.close 22))) (.step 31 (.step 21 (.close 4)))) (.step 31 (.step 23 (.step 29 (.close 63))))) (.split 26 0 (.step 31 (.step 24 (.step 28 (.close 48)))) (.step 6 (.close 21)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1361129467683753853853498429727072845825, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952944194148103420037181032339389913424790090332755919137406977⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 25 0 (.split 26 0 (.step 31 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.step 63 (.split 35 0 (.step 68 (.step 31 (.step 37 (.close 38)))) (.step 4 (.step 31 (.step 37 (.close 38)))))) (.step 31 (.close 37))) (.step 31 (.step 5 (.close 16)))) (.step 31 (.step 23 (.step 5 (.close 16))))) (.step 31 (.split 35 0 (.step 12 (.step 24 (.step 48 (.step 23 (.step 32 (.step 5 (.close 31))))))) (.step 23 (.close 31)))))) (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 36 0 (.step 63 (.step 4 (.step 29 (.step 31 (.close 37))))) (.step 31 (.step 5 (.step 29 (.step 37 (.step 38 (.close 39))))))) (.step 31 (.close 37))) (.step 31 (.close 4))) (.step 31 (.close 4))) (.step 31 (.step 4 (.close 10))))) (.step 31 (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 35 0 (.step 47 (.step 49 (.step 31 (.close 63)))) (.step 31 (.step 28 (.step 37 (.step 38 (.close 39)))))) (.step 31 (.close 37))) (.step 5 (.step 28 (.step 31 (.close 5))))) (.step 31 (.close 16))) (.step 31 (.step 24 (.close 9)))) (.step 31 (.step 28 (.close 4)))))) (.step 31 (.step 48 (.split 25 0 (.split 26 0 (.step 69 (.step 12 (.split 35 0 (.step 23 (.step 16 (.close 48))) (.step 4 (.step 5 (.close 31)))))) (.step 31 (.close 63))) (.step 31 (.step 16 (.close 24))))))))
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
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260849645092742491703299540356157329637377⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 13 0 (.reuse 0) (.split 18 0 (.split 19 0 (.reuse 1) (.run (.split 23 0 (.step 31 (.step 48 (.split 25 0 (.split 26 0 (.step 51 (.step 12 (.split 35 0 (.step 23 (.step 16 (.close 48))) (.step 4 (.step 5 (.close 31)))))) (.step 31 (.close 63))) (.step 31 (.step 16 (.close 22)))))) (.split 25 0 (.step 31 (.step 12 (.split 26 0 (.step 22 (.step 26 (.step 16 (.close 31)))) (.step 10 (.step 22 (.step 26 (.close 31))))))) (.step 16 (.step 31 (.step 22 (.close 5)))))))) (.run (.split 19 0 (.split 23 0 (.step 31 (.step 48 (.split 25 0 (.split 26 0 (.split 35 0 (.step 68 (.close 31)) (.step 5 (.step 23 (.close 38)))) (.step 31 (.close 63))) (.step 31 (.step 16 (.close 24)))))) (.split 25 0 (.step 31 (.step 12 (.split 29 0 (.step 48 (.split 26 0 (.step 21 (.step 23 (.step 5 (.close 16)))) (.step 10 (.step 21 (.step 5 (.close 16)))))) (.step 21 (.step 26 (.step 5 (.close 10))))))) (.step 16 (.step 31 (.step 21 (.close 24)))))) (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.split 23 0 (.step 31 (.step 21 (.step 22 (.close 4)))) (.step 21 (.step 22 (.step 26 (.close 4)))))) (.step 21 (.close 31))) (.step 10 (.step 15 (.step 31 (.step 21 (.step 22 (.step 5 (.close 21)))))))) (.step 16 (.step 31 (.step 41 (.step 6 (.step 21 (.step 22 (.close 4))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1329227995784915872903807060280344577, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952944194148103420037179672539150225455852109738133252344905729⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 25 0 (.step 31 (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.step 48 (.split 36 0 (.step 55 (.step 31 (.step 37 (.close 38)))) (.step 31 (.step 4 (.step 37 (.close 38)))))) (.step 31 (.close 37))) (.step 31 (.step 4 (.close 15)))) (.step 4 (.step 31 (.step 23 (.step 4 (.close 22)))))) (.step 31 (.split 35 0 (.step 12 (.step 23 (.step 24 (.step 32 (.step 4 (.close 31)))))) (.step 23 (.close 31))))) (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 36 0 (.step 47 (.step 63 (.step 31 (.step 4 (.step 37 (.close 38)))))) (.step 29 (.step 31 (.step 4 (.step 37 (.close 39)))))) (.step 31 (.close 37))) (.step 4 (.step 29 (.step 31 (.close 4))))) (.step 31 (.close 15))) (.step 31 (.step 23 (.close 10)))))) (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 35 0 (.split 41 0 (.step 47 (.step 31 (.step 4 (.step 37 (.close 39))))) (.step 4 (.close 5))) (.step 31 (.step 4 (.step 37 (.step 38 (.close 39)))))) (.step 31 (.close 37))) (.step 31 (.close 5))) (.step 31 (.close 5))) (.step 31 (.step 5 (.close 9)))) (.step 31 (.step 28 (.close 29))))) (.step 31 (.step 63 (.split 25 0 (.split 26 0 (.step 69 (.step 12 (.split 35 0 (.step 23 (.step 24 (.step 4 (.close 31)))) (.step 21 (.step 15 (.close 31)))))) (.step 31 (.step 15 (.close 23)))) (.step 31 (.close 48)))))))
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
def root : Box := ⟨1329227995784915872903807060280344577, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573259489844853054522765318945733490537136129⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 23 0 (.step 31 (.step 63 (.split 25 0 (.split 26 0 (.step 51 (.step 12 (.split 35 0 (.step 23 (.step 24 (.step 4 (.close 31)))) (.step 21 (.step 15 (.close 31)))))) (.step 31 (.step 15 (.close 22)))) (.step 31 (.close 48))))) (.split 25 0 (.step 31 (.step 12 (.split 26 0 (.step 22 (.step 26 (.step 4 (.close 31)))) (.step 15 (.step 22 (.step 26 (.close 31))))))) (.step 9 (.step 16 (.step 31 (.step 26 (.step 48 (.step 22 (.close 4))))))))))) (.run (.split 19 0 (.split 23 0 (.step 31 (.step 63 (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.step 24 (.step 21 (.step 23 (.step 15 (.close 48)))))) (.step 31 (.close 21))) (.step 31 (.step 15 (.close 23)))) (.step 31 (.close 48))))) (.split 25 0 (.step 31 (.step 12 (.split 29 0 (.step 63 (.split 26 0 (.step 21 (.step 23 (.step 4 (.close 15)))) (.step 15 (.step 21 (.step 4 (.close 22)))))) (.step 21 (.step 26 (.close 38)))))) (.step 9 (.step 16 (.step 31 (.step 26 (.step 41 (.step 6 (.step 4 (.close 26)))))))))) (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.split 23 0 (.step 31 (.step 21 (.step 22 (.close 4)))) (.step 21 (.step 22 (.step 26 (.close 4)))))) (.step 15 (.step 21 (.close 22)))) (.step 15 (.step 31 (.step 21 (.step 22 (.close 4)))))) (.step 9 (.step 16 (.step 31 (.split 26 0 (.step 21 (.step 22 (.step 4 (.close 26)))) (.step 6 (.close 21))))))))))
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
def root : Box := ⟨1237940039285380274899124225, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952944194148103420037179671209922230908876276119706466963685377⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 23 0 (.split 25 0 (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 35 0 (.step 31 (.step 49 (.close 31))) (.step 31 (.step 66 (.step 31 (.close 38))))) (.step 31 (.close 49))) (.step 31 (.step 51 (.close 71)))) (.step 31 (.split 33 0 (.split 35 0 (.step 12 (.close 49)) (.step 4 (.close 40))) (.step 12 (.step 23 (.step 14 (.close 15))))))) (.step 31 (.step 32 (.step 12 (.step 4 (.close 5)))))) (.step 31 (.split 29 0 (.split 31 0 (.split 33 0 (.step 66 (.step 47 (.step 31 (.close 38)))) (.step 4 (.step 17 (.step 11 (.step 4 (.close 31)))))) (.step 31 (.close 66))) (.step 31 (.step 12 (.step 4 (.close 32))))))) (.step 31 (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.step 49 (.step 47 (.step 31 (.close 38)))) (.step 5 (.step 14 (.step 8 (.step 5 (.close 31)))))) (.step 31 (.close 49))) (.step 31 (.step 12 (.step 5 (.close 32))))) (.step 6 (.step 28 (.close 29)))))) (.step 31 (.split 41 0 (.split 25 0 (.split 44 0 (.split 26 0 (.step 12 (.step 23 (.step 15 (.close 48)))) (.step 31 (.step 12 (.close 23)))) (.step 69 (.step 23 (.step 47 (.step 12 (.close 48)))))) (.step 31 (.step 12 (.step 16 (.step 5 (.close 21)))))) (.step 12 (.step 23 (.step 24 (.step 26 (.close 4)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1237940039285380274899124225, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260849645092743729643338825736432228761601⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.split 18 0 (.split 19 0 (.reuse 0) (.run (.split 29 0 (.step 31 (.split 33 0 (.split 25 0 (.split 44 0 (.split 26 0 (.step 12 (.step 23 (.step 15 (.close 48)))) (.step 31 (.step 12 (.close 23)))) (.step 51 (.step 23 (.step 47 (.step 12 (.close 48)))))) (.step 31 (.step 12 (.step 16 (.step 5 (.close 21)))))) (.step 12 (.step 23 (.step 22 (.close 24)))))) (.step 12 (.step 31 (.step 32 (.split 25 0 (.step 51 (.step 22 (.step 15 (.step 4 (.close 22))))) (.step 6 (.step 16 (.step 22 (.close 4))))))))))) (.run (.split 25 0 (.split 26 0 (.split 19 0 (.split 23 0 (.step 31 (.split 31 0 (.split 33 0 (.split 54 0 (.split 35 0 (.step 12 (.step 23 (.close 48))) (.step 23 (.close 31))) (.step 12 (.step 21 (.close 31)))) (.step 12 (.step 22 (.step 4 (.close 23))))) (.step 12 (.step 16 (.step 23 (.close 14)))))) (.step 12 (.step 31 (.step 21 (.step 26 (.step 5 (.close 21))))))) (.split 23 0 (.step 12 (.step 31 (.step 21 (.step 22 (.step 4 (.close 21)))))) (.step 21 (.step 12 (.step 22 (.step 26 (.close 4))))))) (.step 31 (.step 12 (.split 35 0 (.step 23 (.close 63)) (.step 21 (.close 23)))))) (.step 31 (.step 12 (.split 38 0 (.step 24 (.close 48)) (.step 21 (.close 22)))))))) (.run (.split 18 0 (.split 19 0 (.step 31 (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.close 48)) (.step 31 (.close 12))) (.step 31 (.close 12))) (.step 31 (.close 12)))) (.step 12 (.step 31 (.step 12 (.close 31))))) (.step 12 (.step 31 (.step 12 (.close 31)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1180591620717411303425, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945763423537266707370630157278031587541443014808025484492801⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 25 0 (.split 26 0 (.step 31 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.step 47 (.step 31 (.step 63 (.close 38)))) (.step 31 (.step 37 (.step 4 (.step 29 (.step 38 (.close 39))))))) (.step 31 (.step 5 (.close 10)))) (.step 31 (.step 23 (.step 5 (.close 16))))) (.step 31 (.split 35 0 (.step 47 (.step 23 (.step 32 (.step 5 (.close 31))))) (.step 23 (.close 31)))))) (.step 47 (.close 31))) (.step 47 (.close 6))) (.step 31 (.step 48 (.split 25 0 (.split 26 0 (.step 69 (.split 35 0 (.step 23 (.step 24 (.step 47 (.step 5 (.close 31))))) (.step 5 (.step 23 (.close 31))))) (.step 10 (.step 5 (.close 47)))) (.step 6 (.close 29)))))) (.split 23 0 (.step 31 (.step 48 (.split 25 0 (.split 26 0 (.step 51 (.split 35 0 (.step 23 (.step 24 (.step 47 (.step 5 (.close 31))))) (.step 5 (.step 23 (.close 31))))) (.step 10 (.step 5 (.close 47)))) (.step 6 (.close 29))))) (.split 25 0 (.step 31 (.split 26 0 (.step 48 (.split 35 0 (.step 22 (.step 26 (.step 10 (.close 31)))) (.step 21 (.step 5 (.step 22 (.close 63)))))) (.step 10 (.close 4)))) (.step 6 (.close 9))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1361129467683753855034090050444484149249, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260849645092742491704480131976874740940801⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 28 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 36 0 (.step 47 (.step 23 (.step 48 (.close 63)))) (.step 23 (.close 63))) (.step 31 (.close 37))) (.step 5 (.step 31 (.close 24)))) (.step 5 (.step 16 (.close 31)))) (.step 31 (.step 12 (.step 48 (.split 35 0 (.step 24 (.step 16 (.step 10 (.close 63)))) (.step 5 (.close 31))))))) (.step 31 (.close 4))) (.step 47 (.step 10 (.step 31 (.close 4))))) (.step 31 (.step 10 (.step 16 (.step 48 (.step 69 (.step 63 (.close 22)))))))) (.split 23 0 (.step 31 (.step 10 (.step 16 (.step 48 (.step 51 (.step 63 (.close 22))))))) (.step 10 (.step 22 (.step 26 (.close 31)))))) (.split 19 0 (.split 23 0 (.step 31 (.step 10 (.step 12 (.step 16 (.step 48 (.split 29 0 (.step 23 (.step 5 (.close 21))) (.step 21 (.close 5)))))))) (.step 10 (.step 16 (.step 21 (.step 26 (.close 31)))))) (.step 10 (.step 16 (.step 21 (.step 12 (.step 22 (.close 31)))))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.step 47 (.step 16 (.close 6))) (.step 6 (.close 29))) (.step 6 (.close 16))) (.step 9 (.step 6 (.close 8)))) (.step 9 (.step 6 (.close 8))))))
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
def root : Box := ⟨1329227995784917053495427777691648001, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320738276620353035783935021285377⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 48 (.step 63 (.step 4 (.close 6))))) (.split 25 0 (.step 31 (.step 12 (.step 63 (.step 26 (.step 4 (.close 10)))))) (.step 6 (.close 9)))) (.split 25 0 (.split 26 0 (.split 35 0 (.step 48 (.step 22 (.step 29 (.step 5 (.close 31))))) (.step 15 (.step 21 (.step 22 (.step 4 (.close 31)))))) (.step 10 (.close 29))) (.step 6 (.close 9)))) (.split 25 0 (.split 26 0 (.split 29 0 (.split 31 0 (.step 31 (.step 48 (.step 63 (.step 21 (.step 4 (.close 22)))))) (.step 15 (.close 58))) (.step 38 (.step 5 (.close 41)))) (.step 10 (.step 15 (.close 29)))) (.step 6 (.close 9)))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 25 0 (.step 31 (.step 12 (.close 63))) (.step 6 (.close 16))) (.step 9 (.step 10 (.step 12 (.close 4))))) (.step 12 (.close 16))) (.step 12 (.close 16)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1237941219877000992310427649, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320739514560392321164209920409601⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.step 31 (.split 23 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 33 0 (.step 47 (.step 24 (.step 16 (.step 5 (.close 31))))) (.step 12 (.step 22 (.step 5 (.close 10))))) (.step 5 (.step 23 (.close 63)))) (.step 31 (.close 29))) (.step 6 (.close 29))) (.step 6 (.step 12 (.step 16 (.step 26 (.step 48 (.step 63 (.close 22))))))))) (.step 6 (.split 26 0 (.split 33 0 (.step 31 (.step 12 (.step 16 (.step 22 (.step 48 (.step 23 (.step 5 (.close 31)))))))) (.step 12 (.step 16 (.close 22)))) (.step 31 (.close 29))))) (.step 6 (.split 26 0 (.split 19 0 (.split 35 0 (.step 12 (.step 16 (.step 31 (.step 21 (.step 48 (.step 23 (.step 47 (.step 5 (.close 22))))))))) (.step 15 (.step 12 (.step 21 (.close 10))))) (.step 16 (.step 21 (.step 12 (.step 22 (.step 31 (.close 4))))))) (.step 15 (.step 31 (.close 29)))))) (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 6 (.step 12 (.close 63)))) (.step 12 (.close 16))) (.step 15 (.close 16))) (.step 15 (.close 16)))) (.split 25 0 (.step 12 (.step 31 (.step 12 (.close 63)))) (.step 5 (.close 6)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320739514560392321164209920409601⟩
def references : Fin 7 → Box := ![Part6.root, Part8.root, Part10.root, Part11.root, Part12.root, Part13.root, Part14.root]
def proof : Chunks.Proof 7 := (.split 7 0 (.split 9 0 (.split 12 0 (.reuse 0) (.split 13 0 (.reuse 1) (.run (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 48 (.step 63 (.close 12)))) (.step 12 (.step 48 (.step 15 (.close 31))))) (.step 12 (.step 48 (.step 15 (.step 31 (.close 15)))))) (.step 12 (.step 48 (.step 15 (.step 12 (.step 38 (.step 16 (.close 31))))))))))) (.split 12 0 (.reuse 2) (.run (.split 13 0 (.split 18 0 (.split 19 0 (.step 31 (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.close 31)) (.step 31 (.close 12))) (.step 31 (.close 12))) (.step 31 (.close 12)))) (.step 12 (.step 31 (.step 12 (.close 31))))) (.step 12 (.step 31 (.step 12 (.close 31))))) (.step 12 (.step 31 (.step 12 (.close 31)))))))) (.split 9 0 (.split 12 0 (.split 13 0 (.split 18 0 (.reuse 3) (.run (.split 19 0 (.split 23 0 (.step 31 (.step 48 (.split 25 0 (.split 26 0 (.split 35 0 (.step 68 (.close 31)) (.step 5 (.step 23 (.close 38)))) (.step 10 (.step 5 (.close 47)))) (.step 6 (.close 29))))) (.split 25 0 (.step 31 (.split 26 0 (.step 48 (.split 35 0 (.step 21 (.step 26 (.step 21 (.close 5)))) (.step 21 (.close 10)))) (.step 10 (.close 4)))) (.step 6 (.close 9)))) (.split 25 0 (.split 26 0 (.split 35 0 (.split 37 0 (.split 38 0 (.split 23 0 (.step 31 (.step 22 (.step 5 (.close 31)))) (.step 22 (.step 26 (.close 31)))) (.step 10 (.step 21 (.close 22)))) (.step 21 (.step 22 (.step 4 (.close 23))))) (.step 21 (.close 31))) (.step 10 (.step 21 (.step 4 (.close 22))))) (.step 6 (.close 9)))))) (.reuse 4)) (.reuse 5)) (.reuse 6)))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part8.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1152921504606846977, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945763423537266707370630157278031587540263576108812680036353⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 25 0 (.step 31 (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.step 47 (.step 31 (.step 48 (.close 38)))) (.step 31 (.step 37 (.step 4 (.step 28 (.step 38 (.close 39))))))) (.step 31 (.step 4 (.close 9)))) (.step 4 (.step 31 (.step 23 (.step 4 (.close 22)))))) (.step 31 (.split 35 0 (.step 24 (.step 47 (.step 32 (.step 4 (.close 31))))) (.step 23 (.close 31))))) (.step 47 (.close 6)))) (.step 47 (.close 31))) (.step 31 (.split 25 0 (.split 26 0 (.step 69 (.split 35 0 (.step 24 (.step 47 (.step 4 (.close 31)))) (.step 31 (.close 23)))) (.step 6 (.close 28))) (.step 6 (.step 9 (.step 5 (.close 47))))))) (.step 31 (.split 23 0 (.step 31 (.split 25 0 (.split 26 0 (.step 51 (.split 35 0 (.step 24 (.step 47 (.step 4 (.close 31)))) (.step 31 (.close 23)))) (.step 6 (.close 28))) (.step 6 (.step 9 (.step 5 (.close 47)))))) (.split 25 0 (.step 6 (.step 31 (.step 63 (.split 35 0 (.step 22 (.step 26 (.close 48))) (.step 9 (.step 21 (.step 22 (.close 31)))))))) (.step 9 (.step 22 (.close 5))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1152921504606846977, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260849645092742491703300693277661936484353⟩
def references : Fin 1 → Box := ![Part16.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.split 18 0 (.reuse 0) (.run (.split 19 0 (.step 31 (.split 23 0 (.step 31 (.step 63 (.split 25 0 (.split 26 0 (.split 35 0 (.step 24 (.step 47 (.step 21 (.step 23 (.step 4 (.close 31)))))) (.step 31 (.close 21))) (.step 6 (.close 28))) (.step 6 (.step 9 (.step 5 (.close 47))))))) (.split 25 0 (.step 6 (.step 31 (.step 63 (.split 35 0 (.step 21 (.step 26 (.step 21 (.close 4)))) (.step 9 (.close 21)))))) (.step 9 (.step 21 (.step 5 (.close 16))))))) (.split 25 0 (.split 26 0 (.split 35 0 (.split 37 0 (.split 38 0 (.split 23 0 (.step 31 (.step 22 (.step 4 (.close 31)))) (.step 22 (.step 26 (.close 31)))) (.step 21 (.close 31))) (.step 21 (.step 22 (.step 23 (.close 26))))) (.step 21 (.close 31))) (.step 6 (.close 10))) (.step 9 (.step 21 (.step 5 (.close 22)))))))) (.run (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 48 (.step 63 (.step 5 (.close 6))))) (.split 25 0 (.step 31 (.step 6 (.step 12 (.step 26 (.step 4 (.step 5 (.step 47 (.step 4 (.close 31))))))))) (.step 9 (.close 28)))) (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.step 48 (.step 22 (.step 4 (.close 31))))) (.step 9 (.step 15 (.step 21 (.step 22 (.step 4 (.close 31))))))) (.step 6 (.close 10))) (.step 9 (.close 28)))) (.split 25 0 (.split 26 0 (.split 29 0 (.split 31 0 (.step 31 (.step 48 (.step 63 (.step 21 (.step 4 (.close 22)))))) (.step 16 (.close 71))) (.step 38 (.step 5 (.close 41)))) (.step 6 (.close 10))) (.step 9 (.step 16 (.close 28)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1329227995784915874056728564887191553, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573259489844853054522765320098654995143983105⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 0 (.split 26 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 28 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 36 0 (.step 47 (.step 24 (.step 48 (.close 4)))) (.step 24 (.close 48))) (.step 31 (.close 37))) (.step 4 (.step 31 (.close 23)))) (.step 4 (.step 15 (.close 31)))) (.step 31 (.step 12 (.step 63 (.split 35 0 (.step 24 (.step 47 (.step 15 (.close 48)))) (.step 9 (.step 15 (.step 21 (.close 31))))))))) (.step 31 (.close 4))) (.step 31 (.step 9 (.step 15 (.step 63 (.step 69 (.step 48 (.close 26)))))))) (.split 23 0 (.step 31 (.step 9 (.step 15 (.step 51 (.step 63 (.step 48 (.close 22))))))) (.step 15 (.step 22 (.step 26 (.close 31)))))) (.split 19 0 (.split 23 0 (.step 31 (.step 9 (.step 12 (.step 15 (.step 63 (.split 29 0 (.step 23 (.close 48)) (.step 21 (.close 4)))))))) (.step 9 (.step 15 (.step 21 (.step 26 (.close 31)))))) (.step 9 (.step 15 (.step 21 (.step 12 (.step 22 (.close 31)))))))) (.split 18 0 (.split 19 0 (.split 23 0 (.step 47 (.step 15 (.close 6))) (.step 6 (.close 11))) (.step 10 (.step 6 (.close 11)))) (.step 10 (.step 6 (.close 11))))) (.split 18 0 (.split 19 0 (.split 23 0 (.step 48 (.split 26 0 (.step 47 (.close 31)) (.step 6 (.close 28)))) (.step 9 (.step 4 (.close 26)))) (.step 9 (.step 4 (.close 22)))) (.step 9 (.step 4 (.close 28))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1237940040438301779505971201, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320739514559212882464997115953153⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.step 31 (.split 23 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 33 0 (.step 47 (.step 24 (.step 4 (.step 15 (.close 48))))) (.step 12 (.step 22 (.step 4 (.close 9))))) (.step 31 (.step 12 (.close 23)))) (.step 6 (.close 28))) (.step 31 (.close 28))) (.step 6 (.step 12 (.step 15 (.step 26 (.split 25 0 (.step 26 (.step 4 (.close 31))) (.step 4 (.close 9))))))))) (.step 6 (.split 25 0 (.split 33 0 (.step 31 (.step 12 (.step 15 (.step 22 (.step 51 (.step 4 (.close 31))))))) (.step 12 (.step 15 (.close 22)))) (.step 31 (.close 28))))) (.step 6 (.split 25 0 (.split 19 0 (.split 35 0 (.step 12 (.split 37 0 (.step 15 (.step 31 (.step 21 (.step 47 (.step 4 (.close 26)))))) (.step 21 (.step 4 (.step 15 (.step 23 (.close 26))))))) (.step 15 (.step 12 (.step 9 (.close 21))))) (.step 15 (.step 21 (.step 12 (.step 22 (.step 31 (.close 4))))))) (.step 16 (.step 31 (.close 28)))))) (.split 25 0 (.split 26 0 (.step 12 (.step 15 (.close 31))) (.step 4 (.close 6))) (.step 5 (.step 9 (.step 12 (.close 9)))))) (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 6 (.step 12 (.close 48)))) (.step 12 (.close 15))) (.step 12 (.close 15))) (.step 12 (.close 15))) (.step 4 (.step 6 (.close 12))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320739514560393474085714527256577⟩
def references : Fin 4 → Box := ![Part15.root, Part17.root, Part18.root, Part19.root]
def proof : Chunks.Proof 4 := (.split 6 0 (.reuse 0) (.split 7 0 (.split 9 0 (.split 12 0 (.reuse 1) (.split 13 0 (.reuse 2) (.run (.split 18 0 (.split 19 0 (.split 23 0 (.split 25 0 (.step 31 (.step 12 (.close 31))) (.step 9 (.close 28))) (.step 9 (.step 10 (.step 12 (.close 5))))) (.step 12 (.close 15))) (.step 12 (.close 15)))))) (.reuse 3)) (.run (.split 9 0 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 48 (.step 6 (.close 63)))) (.step 6 (.step 28 (.close 63)))) (.step 6 (.step 48 (.step 9 (.close 31))))) (.step 6 (.step 48 (.step 9 (.step 29 (.close 31)))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 25 0 (.step 31 (.step 6 (.close 63))) (.step 6 (.close 10))) (.step 6 (.close 10))) (.step 6 (.close 10))) (.step 6 (.close 10)))) (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 25 0 (.step 31 (.step 6 (.close 48))) (.step 6 (.close 28))) (.step 6 (.close 9))) (.step 6 (.close 9))) (.step 6 (.close 9))) (.step 6 (.step 9 (.close 4))))) (.step 6 (.step 31 (.step 6 (.close 31))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part17.excludes
  · exact Part18.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1073741825, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945763423537266707370630157278031587540262423187309146931201⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 23 0 (.split 25 0 (.split 26 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 34 0 (.split 35 0 (.step 31 (.step 28 (.step 31 (.close 38)))) (.step 29 (.step 31 (.close 38)))) (.step 31 (.step 37 (.close 38)))) (.step 31 (.step 51 (.close 71)))) (.step 31 (.split 33 0 (.split 35 0 (.step 58 (.close 10)) (.step 4 (.close 40))) (.step 40 (.step 8 (.close 58)))))) (.step 31 (.step 32 (.split 37 0 (.step 48 (.step 5 (.close 9))) (.step 4 (.close 36)))))) (.step 31 (.split 29 0 (.split 31 0 (.step 29 (.close 4)) (.step 6 (.close 29))) (.step 6 (.close 29))))) (.step 31 (.split 26 0 (.split 29 0 (.split 31 0 (.step 28 (.close 4)) (.step 6 (.close 28))) (.step 6 (.close 28))) (.step 6 (.close 28))))) (.step 31 (.split 25 0 (.split 41 0 (.split 44 0 (.split 26 0 (.step 69 (.step 23 (.close 48))) (.step 6 (.close 28))) (.step 9 (.step 10 (.step 23 (.step 24 (.step 29 (.close 5))))))) (.step 69 (.close 4))) (.step 6 (.close 28))))) (.split 29 0 (.step 31 (.split 33 0 (.split 25 0 (.split 44 0 (.split 26 0 (.step 51 (.step 23 (.close 48))) (.step 6 (.close 28))) (.step 9 (.step 10 (.step 23 (.step 24 (.step 9 (.close 28))))))) (.step 6 (.close 28))) (.step 51 (.close 4)))) (.step 6 (.step 32 (.step 31 (.step 51 (.step 10 (.close 31)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1361129467683753853853498429728146587649, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260849645092742491703299540356158403379201⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 18 0 (.split 19 0 (.step 31 (.split 23 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.step 24 (.split 37 0 (.step 48 (.split 38 0 (.split 46 0 (.step 5 (.close 31)) (.step 28 (.close 48))) (.step 24 (.close 31)))) (.step 10 (.step 5 (.close 16)))))) (.step 5 (.step 23 (.close 63)))) (.step 6 (.close 29))) (.step 6 (.close 28))) (.step 6 (.step 10 (.step 12 (.step 26 (.step 16 (.close 31)))))))) (.step 12 (.split 25 0 (.split 26 0 (.split 35 0 (.step 10 (.step 31 (.step 22 (.step 16 (.close 48))))) (.step 9 (.step 21 (.step 22 (.step 4 (.close 31)))))) (.step 6 (.close 16))) (.step 6 (.close 16))))) (.step 12 (.split 25 0 (.split 26 0 (.split 19 0 (.split 35 0 (.step 10 (.step 31 (.step 21 (.step 48 (.split 23 0 (.step 23 (.step 24 (.step 16 (.close 63)))) (.step 21 (.step 26 (.close 5)))))))) (.step 21 (.close 31))) (.step 10 (.step 21 (.step 22 (.step 31 (.step 4 (.close 16))))))) (.step 6 (.close 28))) (.step 6 (.close 28))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨1329227995784915872903807061354086401, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320738276619172444163218683723777⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 13 0 (.split 18 0 (.split 19 0 (.step 31 (.split 23 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 12 (.split 37 0 (.split 38 0 (.split 40 0 (.split 45 0 (.step 63 (.close 9)) (.step 4 (.close 31))) (.step 5 (.close 24))) (.step 5 (.step 9 (.step 4 (.close 31))))) (.step 4 (.close 23)))) (.step 31 (.step 9 (.close 23)))) (.step 6 (.close 28))) (.step 6 (.close 28))) (.step 6 (.step 9 (.step 12 (.step 26 (.step 15 (.close 31)))))))) (.step 12 (.split 25 0 (.split 26 0 (.split 35 0 (.split 37 0 (.step 9 (.step 31 (.step 22 (.step 4 (.close 31))))) (.step 22 (.step 4 (.step 9 (.close 31))))) (.step 9 (.step 15 (.step 21 (.step 22 (.close 31)))))) (.step 6 (.close 15))) (.step 6 (.close 15))))) (.step 12 (.split 25 0 (.split 26 0 (.split 19 0 (.split 37 0 (.step 9 (.step 31 (.step 21 (.step 55 (.close 63))))) (.step 21 (.step 4 (.step 23 (.close 31))))) (.step 9 (.step 21 (.step 22 (.step 31 (.step 4 (.close 15))))))) (.step 6 (.close 29))) (.step 6 (.close 29))))) (.step 12 (.step 31 (.step 6 (.step 9 (.close 12)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨1073741825, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320738276619172444163218683723777⟩
def references : Fin 3 → Box := ![Part21.root, Part22.root, Part23.root]
def proof : Chunks.Proof 3 := (.split 12 0 (.split 13 0 (.split 18 0 (.reuse 0) (.run (.split 25 0 (.split 26 0 (.split 19 0 (.split 23 0 (.step 31 (.split 31 0 (.split 33 0 (.split 54 0 (.split 35 0 (.step 24 (.step 31 (.close 10))) (.step 23 (.close 31))) (.step 9 (.step 21 (.close 31)))) (.step 23 (.step 8 (.close 24)))) (.split 35 0 (.step 23 (.step 24 (.step 48 (.close 4)))) (.step 9 (.step 15 (.step 21 (.close 23))))))) (.split 28 0 (.split 29 0 (.step 31 (.step 69 (.step 21 (.step 23 (.step 24 (.step 9 (.step 21 (.close 31)))))))) (.step 32 (.step 26 (.step 23 (.step 24 (.close 31)))))) (.step 31 (.close 22)))) (.split 23 0 (.split 28 0 (.split 29 0 (.step 31 (.step 51 (.step 21 (.step 22 (.step 23 (.step 9 (.step 21 (.close 23)))))))) (.step 32 (.step 22 (.step 23 (.step 24 (.close 31)))))) (.step 31 (.close 22))) (.step 21 (.step 22 (.step 26 (.close 31)))))) (.step 6 (.step 31 (.close 6)))) (.step 6 (.step 31 (.close 6)))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨1237940039285380275972866049, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945763423537266707370630157278032825480301708567584046055425⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 19 0 (.split 33 0 (.step 31 (.split 23 0 (.split 25 0 (.split 26 0 (.split 54 0 (.split 56 0 (.step 12 (.split 35 0 (.step 31 (.close 26)) (.step 31 (.close 4)))) (.step 31 (.step 5 (.close 32)))) (.step 12 (.step 51 (.step 9 (.close 63))))) (.step 6 (.close 28))) (.step 6 (.close 28))) (.step 6 (.step 12 (.step 69 (.split 35 0 (.step 24 (.step 10 (.step 15 (.close 31)))) (.step 9 (.step 15 (.close 63))))))))) (.step 6 (.step 12 (.step 31 (.split 35 0 (.split 38 0 (.step 51 (.step 40 (.split 40 0 (.step 23 (.close 8)) (.step 5 (.close 11))))) (.step 31 (.step 5 (.close 43)))) (.step 31 (.step 4 (.close 36)))))))) (.step 6 (.step 12 (.split 35 0 (.split 38 0 (.split 47 0 (.split 64 0 (.split 23 0 (.step 31 (.step 23 (.step 22 (.close 4)))) (.step 22 (.step 26 (.close 4)))) (.step 23 (.step 32 (.step 9 (.step 15 (.step 22 (.close 26))))))) (.step 24 (.step 32 (.step 10 (.step 16 (.step 22 (.close 26))))))) (.step 31 (.step 10 (.step 16 (.step 21 (.close 22)))))) (.step 31 (.step 9 (.step 15 (.step 21 (.step 4 (.close 22)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨1073741825, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320739514560392321164210994151425⟩
def references : Fin 2 → Box := ![Part24.root, Part25.root]
def proof : Chunks.Proof 2 := (.split 7 0 (.split 9 0 (.reuse 0) (.split 12 0 (.split 13 0 (.split 18 0 (.reuse 1) (.run (.step 6 (.step 12 (.split 35 0 (.split 38 0 (.split 47 0 (.split 64 0 (.split 23 0 (.split 33 0 (.step 31 (.split 41 0 (.split 37 0 (.step 9 (.close 48)) (.step 4 (.close 22))) (.step 23 (.close 24)))) (.step 22 (.step 23 (.step 24 (.close 31))))) (.step 26 (.step 31 (.step 5 (.close 22))))) (.step 32 (.step 9 (.step 15 (.step 21 (.close 23)))))) (.step 32 (.step 10 (.step 16 (.step 21 (.close 23)))))) (.step 32 (.step 10 (.step 16 (.step 21 (.close 23)))))) (.step 32 (.step 9 (.step 15 (.step 21 (.close 23)))))))))) (.run (.step 12 (.close 31)))) (.run (.step 12 (.close 31))))) (.run (.split 9 0 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.step 31 (.split 23 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 33 0 (.step 47 (.step 24 (.step 48 (.step 23 (.step 5 (.close 31)))))) (.step 6 (.close 5))) (.step 5 (.step 23 (.close 63)))) (.step 6 (.close 29))) (.step 6 (.close 28))) (.step 6 (.close 31)))) (.step 6 (.step 31 (.step 6 (.close 31))))) (.step 6 (.step 31 (.step 6 (.close 31))))) (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 6 (.close 63))) (.step 6 (.close 10))) (.step 9 (.close 10))) (.step 9 (.close 10)))) (.split 13 0 (.split 25 0 (.step 12 (.split 35 0 (.step 6 (.step 9 (.close 31))) (.step 9 (.close 31)))) (.step 5 (.close 6))) (.step 5 (.step 6 (.close 9))))) (.step 6 (.step 12 (.step 6 (.close 31)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part24.excludes
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨1, 5653548956058700166736201897690286646765642754749942220620061133762033130387882728367193192996232820298782873651456500297779028033736998447925345672960924424952945764956032807573260850974320739514560393474085715600998401⟩
def references : Fin 2 → Box := ![Part20.root, Part26.root]
def proof : Chunks.Proof 2 := (.split 3 0 (.reuse 0) (.split 6 0 (.reuse 1) (.run (.split 7 0 (.split 9 0 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.step 31 (.split 23 0 (.split 26 0 (.split 35 0 (.split 33 0 (.step 47 (.step 24 (.step 4 (.step 48 (.close 4))))) (.step 6 (.close 4))) (.step 31 (.close 6))) (.step 6 (.close 28))) (.step 6 (.close 31)))) (.step 6 (.step 31 (.step 9 (.close 21))))) (.step 6 (.step 31 (.step 6 (.close 31))))) (.split 26 0 (.step 12 (.split 35 0 (.step 10 (.step 6 (.close 31))) (.step 6 (.step 9 (.close 31))))) (.step 4 (.close 6)))) (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 31 (.step 6 (.close 48))) (.step 6 (.close 9))) (.step 6 (.close 9))) (.step 6 (.close 9))) (.step 4 (.step 6 (.close 9))))) (.step 6 (.step 12 (.step 6 (.close 31))))) (.step 6 (.step 31 (.step 6 (.close 31))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part27

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part27.excludes
end FiveColour.Packed.ProjectedChunks.Case263
