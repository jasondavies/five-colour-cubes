module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case28
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413524840649535549816918667904115097468928⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨10699377823114761907191, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646219954648068689896578978248292267480420713472, 0⟩]
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
def root : Box := ⟨2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493272680857600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838452961638544125920541832062422772495411535063196054615422259317568989439206207294730442917945280803817652224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 0 (.split 43 0 (.split 50 0 (.split 51 0 (.split 58 0 (.step 68 (.step 15 (.step 18 (.step 5 (.close 17))))) (.step 40 (.step 15 (.step 17 (.close 20))))) (.step 52 (.step 57 (.step 4 (.close 15))))) (.step 52 (.split 36 0 (.split 51 0 (.step 58 (.step 15 (.close 20))) (.step 53 (.step 18 (.step 15 (.close 20))))) (.step 15 (.step 39 (.close 4)))))) (.step 52 (.split 36 0 (.step 9 (.step 71 (.close 9))) (.step 15 (.step 9 (.step 54 (.step 9 (.close 4)))))))) (.split 43 0 (.split 50 0 (.split 51 0 (.step 40 (.step 15 (.step 17 (.step 19 (.step 20 (.close 39)))))) (.step 52 (.step 31 (.step 15 (.step 20 (.step 19 (.close 20))))))) (.step 52 (.step 38 (.step 4 (.close 5))))) (.step 52 (.split 42 0 (.step 9 (.step 68 (.step 5 (.close 15)))) (.step 15 (.step 9 (.step 5 (.step 20 (.step 5 (.close 31)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2037035976334486086268445688409378161051468393665936250636140449354381299763336707257139200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057597465300074312612718436228892894236261727635687604224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 51 0 (.split 54 0 (.step 53 (.step 68 (.close 4))) (.step 43 (.step 18 (.step 15 (.close 33))))) (.step 53 (.step 39 (.step 4 (.close 15))))) (.step 53 (.step 13 (.step 37 (.step 18 (.close 20)))))) (.step 53 (.split 36 0 (.split 54 0 (.split 58 0 (.step 29 (.step 4 (.close 13))) (.step 31 (.close 9))) (.step 9 (.close 5))) (.step 54 (.step 9 (.step 29 (.close 13))))))) (.split 43 0 (.split 49 0 (.split 51 0 (.split 54 0 (.split 34 0 (.step 42 (.step 4 (.step 18 (.close 24)))) (.step 31 (.step 24 (.close 19)))) (.step 38 (.step 4 (.close 5)))) (.step 53 (.step 31 (.step 24 (.close 33))))) (.step 53 (.step 52 (.step 38 (.close 13))))) (.step 53 (.split 36 0 (.split 34 0 (.step 27 (.step 9 (.close 11))) (.step 9 (.step 5 (.step 13 (.step 5 (.close 11)))))) (.step 33 (.step 9 (.close 5))))))) (.split 39 0 (.split 43 0 (.split 49 0 (.split 34 0 (.step 53 (.step 38 (.close 4))) (.split 50 0 (.step 38 (.step 4 (.close 15))) (.step 15 (.step 18 (.close 38))))) (.step 71 (.step 38 (.step 13 (.close 19))))) (.split 49 0 (.step 71 (.close 29)) (.step 9 (.step 53 (.step 13 (.close 9)))))) (.split 43 0 (.split 49 0 (.step 71 (.close 38)) (.step 42 (.step 4 (.step 13 (.step 17 (.step 20 (.close 33))))))) (.step 9 (.step 24 (.step 9 (.step 33 (.step 5 (.close 13))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057597465300074312612718436228892894236261727635687604224⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 30 0 (.split 35 0 (.split 34 0 (.run (.split 39 0 (.split 42 0 (.split 50 0 (.split 36 0 (.step 68 (.step 4 (.close 5))) (.step 54 (.step 18 (.step 4 (.close 9))))) (.step 53 (.split 61 0 (.step 57 (.step 4 (.close 11))) (.step 52 (.step 18 (.step 4 (.step 9 (.close 11)))))))) (.step 62 (.step 57 (.step 18 (.step 9 (.step 13 (.step 4 (.step 9 (.close 29))))))))) (.split 42 0 (.split 50 0 (.split 54 0 (.split 72 0 (.step 68 (.step 5 (.close 27))) (.step 62 (.step 5 (.step 9 (.close 13))))) (.split 61 0 (.step 61 (.step 5 (.step 9 (.close 19)))) (.step 52 (.step 4 (.close 5))))) (.step 53 (.split 61 0 (.split 63 0 (.step 38 (.step 4 (.step 5 (.close 11)))) (.step 27 (.step 38 (.close 36)))) (.step 52 (.step 65 (.step 4 (.close 5))))))) (.step 62 (.step 68 (.step 4 (.step 5 (.close 13)))))))) (.reuse 0)) (.run (.split 39 0 (.split 43 0 (.split 34 0 (.step 53 (.split 36 0 (.step 53 (.step 57 (.close 4))) (.step 57 (.step 18 (.step 4 (.close 13)))))) (.step 15 (.step 53 (.step 39 (.step 4 (.close 17)))))) (.step 53 (.step 9 (.close 29)))) (.split 43 0 (.split 49 0 (.split 51 0 (.split 59 0 (.step 38 (.close 4)) (.step 38 (.close 4))) (.step 53 (.step 4 (.step 24 (.step 33 (.step 15 (.step 20 (.close 38)))))))) (.step 53 (.step 40 (.close 38)))) (.step 9 (.step 53 (.step 9 (.step 5 (.step 9 (.close 11)))))))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512452466762755551445353331214420645047507704663244800⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 35 0 (.split 39 0 (.split 42 0 (.split 43 0 (.split 34 0 (.step 62 (.step 18 (.close 13))) (.step 52 (.step 24 (.step 40 (.step 15 (.close 20)))))) (.step 62 (.step 68 (.step 5 (.step 4 (.close 13)))))) (.step 68 (.step 48 (.step 13 (.step 33 (.close 39)))))) (.step 62 (.split 42 0 (.step 62 (.step 68 (.step 5 (.close 27)))) (.step 24 (.step 43 (.close 5)))))) (.split 34 0 (.split 36 0 (.step 42 (.step 53 (.step 43 (.step 62 (.close 4))))) (.step 43 (.step 53 (.step 24 (.step 4 (.close 9)))))) (.step 43 (.step 68 (.step 4 (.step 11 (.step 13 (.close 15)))))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 53 (.step 62 (.step 24 (.step 4 (.step 5 (.close 11)))))) (.step 24 (.step 62 (.step 33 (.step 31 (.step 11 (.step 19 (.step 20 (.close 13))))))))) (.split 36 0 (.step 42 (.close 4)) (.step 33 (.step 19 (.step 13 (.close 20)))))) (.split 35 0 (.split 36 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 43 (.close 37)))) (.step 33 (.step 15 (.step 17 (.close 19)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057598961877750939457306676802161595710073855310611611648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 50 0 (.step 54 (.step 63 (.step 9 (.close 13)))) (.step 53 (.step 54 (.step 27 (.step 4 (.close 13)))))) (.step 61 (.step 68 (.step 27 (.step 42 (.step 61 (.close 4))))))) (.step 68 (.step 13 (.close 33)))) (.split 36 0 (.step 42 (.step 53 (.step 43 (.step 54 (.step 4 (.close 9)))))) (.step 43 (.step 53 (.step 24 (.step 4 (.close 9))))))) (.split 35 0 (.split 36 0 (.step 68 (.step 13 (.step 15 (.close 16)))) (.step 43 (.step 48 (.step 39 (.step 13 (.step 15 (.close 33))))))) (.step 43 (.step 68 (.step 4 (.step 11 (.step 13 (.close 15)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 53 (.split 39 0 (.step 53 (.step 54 (.step 24 (.step 11 (.close 13))))) (.step 24 (.step 27 (.step 20 (.close 13)))))) (.step 43 (.step 33 (.step 24 (.step 4 (.close 13)))))) (.split 36 0 (.step 42 (.close 4)) (.step 33 (.step 19 (.step 13 (.close 20)))))) (.split 35 0 (.split 36 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 43 (.close 37)))) (.step 33 (.step 15 (.step 17 (.close 19))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057597466761575949943621354432577726952544747291620147200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 53 (.step 68 (.step 5 (.close 13)))) (.step 42 (.step 53 (.step 65 (.step 9 (.step 13 (.close 19))))))) (.step 68 (.step 13 (.close 33)))) (.step 53 (.step 5 (.close 19)))) (.split 35 0 (.split 36 0 (.step 68 (.step 13 (.step 15 (.close 16)))) (.step 43 (.step 48 (.step 39 (.step 13 (.step 15 (.close 33))))))) (.step 43 (.step 53 (.step 33 (.step 15 (.step 29 (.step 37 (.step 24 (.step 4 (.close 38))))))))))) (.split 34 0 (.split 35 0 (.step 53 (.step 18 (.close 19))) (.split 39 0 (.step 53 (.step 4 (.step 11 (.step 13 (.close 19))))) (.step 5 (.step 24 (.close 19))))) (.split 35 0 (.split 36 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 38 (.step 5 (.close 13))))) (.step 33 (.step 15 (.step 17 (.close 19))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057598963339252576788209595005846428426356874966544154624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 61 (.step 53 (.step 54 (.step 24 (.step 11 (.step 13 (.close 18)))))))) (.step 24 (.split 39 0 (.step 24 (.step 43 (.step 5 (.step 13 (.close 33))))) (.step 24 (.close 19))))) (.split 36 0 (.step 53 (.step 5 (.step 4 (.close 19)))) (.step 24 (.close 19)))) (.split 35 0 (.step 24 (.split 36 0 (.split 39 0 (.step 24 (.step 43 (.step 5 (.step 13 (.close 33))))) (.step 24 (.close 19))) (.step 24 (.step 20 (.step 4 (.step 11 (.close 14))))))) (.step 24 (.step 17 (.step 19 (.step 15 (.step 19 (.close 20)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 19 (.close 20)))) (.step 24 (.step 20 (.close 23)))) (.step 24 (.step 19 (.step 4 (.close 20))))) (.step 24 (.step 33 (.step 20 (.step 4 (.close 14))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019726936512108167954835142655035519795200⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 62 (.step 42 (.step 24 (.step 11 (.close 13)))))) (.step 24 (.step 70 (.step 42 (.step 24 (.close 13)))))) (.split 36 0 (.step 53 (.step 5 (.step 4 (.close 19)))) (.step 24 (.close 19)))) (.split 35 0 (.step 24 (.split 36 0 (.step 70 (.step 42 (.step 24 (.close 13)))) (.step 24 (.step 20 (.step 24 (.step 19 (.step 4 (.close 11)))))))) (.step 24 (.step 17 (.step 19 (.step 15 (.step 19 (.close 20)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.step 19 (.close 20)))) (.step 24 (.step 20 (.step 24 (.step 19 (.step 4 (.close 11))))))) (.step 24 (.step 19 (.step 4 (.close 20))))) (.step 24 (.step 33 (.step 25 (.step 24 (.close 14))))))))) (.split 22 0 (.reuse 1) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 42 (.step 24 (.step 20 (.step 11 (.close 13))))) (.step 24 (.close 19))) (.step 24 (.step 42 (.step 4 (.step 5 (.close 19)))))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.close 19))) (.step 24 (.step 19 (.step 20 (.close 4))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 42 (.step 13 (.step 19 (.close 20)))) (.step 19 (.step 20 (.step 23 (.step 9 (.step 13 (.close 24))))))) (.step 19 (.step 11 (.step 5 (.close 13))))) (.step 19 (.step 20 (.close 4)))) (.step 19 (.step 18 (.close 9)))) (.step 19 (.step 20 (.step 17 (.step 23 (.step 15 (.step 9 (.close 24))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019726936512108167954835142655035519795200⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part7.root]
def proof : Chunks.Proof 3 := (.split 16 0 (.split 17 0 (.reuse 0) (.split 22 0 (.reuse 1) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 62 (.step 54 (.step 11 (.step 4 (.step 13 (.close 18))))))) (.step 24 (.step 70 (.step 43 (.step 24 (.close 13)))))) (.split 36 0 (.step 62 (.split 39 0 (.step 24 (.step 4 (.close 13))) (.step 18 (.step 11 (.step 19 (.step 20 (.close 13))))))) (.step 24 (.step 19 (.close 20))))) (.split 35 0 (.step 24 (.split 36 0 (.step 70 (.step 43 (.step 24 (.close 13)))) (.step 24 (.step 20 (.step 4 (.step 11 (.close 14))))))) (.step 24 (.step 17 (.step 24 (.step 19 (.close 20))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 61 (.step 24 (.step 11 (.step 18 (.step 13 (.close 18)))))))) (.step 24 (.step 20 (.close 23)))) (.step 24 (.step 19 (.step 20 (.step 4 (.step 9 (.step 11 (.close 20)))))))) (.step 24 (.step 33 (.step 20 (.step 4 (.close 14)))))))))) (.reuse 2))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057597465300075706409293344392839240218653768158281728000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 39 0 (.split 43 0 (.split 50 0 (.split 51 0 (.split 36 0 (.step 52 (.step 68 (.close 15))) (.step 15 (.step 40 (.step 24 (.step 17 (.close 39)))))) (.step 52 (.step 4 (.step 20 (.step 19 (.close 42)))))) (.step 52 (.step 53 (.step 5 (.close 20))))) (.step 52 (.step 68 (.step 5 (.close 9))))) (.split 43 0 (.split 50 0 (.split 51 0 (.split 54 0 (.step 42 (.step 52 (.step 4 (.step 5 (.close 19))))) (.step 23 (.step 15 (.step 38 (.step 17 (.step 19 (.step 20 (.close 39)))))))) (.step 42 (.step 52 (.step 4 (.close 20))))) (.step 42 (.step 52 (.step 5 (.step 19 (.close 38)))))) (.step 52 (.step 27 (.close 4))))) (.split 35 0 (.step 52 (.step 43 (.close 5))) (.split 39 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 43 (.close 15)) (.step 4 (.step 15 (.step 24 (.close 17))))) (.step 15 (.step 38 (.close 4)))) (.step 15 (.step 40 (.step 17 (.close 37))))) (.step 15 (.step 4 (.step 29 (.close 9))))) (.step 40 (.step 17 (.step 29 (.close 38))))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 53 (.step 24 (.close 4)))) (.split 43 0 (.step 42 (.step 5 (.step 13 (.step 20 (.close 24))))) (.step 24 (.step 31 (.step 11 (.close 20)))))) (.split 36 0 (.step 42 (.close 4)) (.step 43 (.step 13 (.step 4 (.step 20 (.step 9 (.step 11 (.close 19))))))))) (.split 36 0 (.split 39 0 (.step 52 (.step 4 (.step 11 (.close 13)))) (.step 24 (.step 31 (.step 17 (.close 24))))) (.step 43 (.close 37))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513949044440776192608502068429468101251675902181376000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 61 (.step 52 (.step 24 (.step 61 (.step 4 (.step 5 (.step 9 (.close 11)))))))) (.split 36 0 (.step 42 (.step 15 (.step 23 (.step 24 (.step 9 (.close 17)))))) (.step 4 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.step 24 (.step 43 (.close 52))) (.step 4 (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))))) (.split 34 0 (.split 36 0 (.split 39 0 (.split 35 0 (.step 52 (.step 24 (.step 11 (.step 18 (.close 20))))) (.step 5 (.step 24 (.close 13)))) (.step 24 (.step 31 (.step 11 (.step 17 (.step 19 (.step 20 (.close 13)))))))) (.step 13 (.step 5 (.step 24 (.step 19 (.close 20)))))) (.step 13 (.step 24 (.step 33 (.step 5 (.step 11 (.close 17)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 61 (.step 24 (.step 13 (.step 11 (.step 17 (.close 18)))))) (.step 13 (.step 11 (.step 17 (.step 20 (.close 19)))))) (.step 24 (.step 19 (.step 11 (.step 13 (.step 4 (.close 20))))))) (.step 13 (.step 17 (.step 23 (.step 11 (.close 17)))))) (.step 13 (.split 34 0 (.split 35 0 (.split 36 0 (.step 11 (.step 17 (.step 20 (.step 24 (.close 18))))) (.step 20 (.step 4 (.step 5 (.close 9))))) (.step 5 (.step 11 (.step 17 (.step 19 (.step 20 (.close 24))))))) (.step 17 (.step 16 (.close 20))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513949044440776192608502068429468101251675902181376000⟩
def references : Fin 2 → Box := ![Part9.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 68 (.split 43 0 (.split 50 0 (.split 59 0 (.step 24 (.step 13 (.step 14 (.close 18)))) (.step 48 (.step 24 (.step 15 (.close 13))))) (.step 48 (.step 52 (.step 24 (.step 19 (.close 38)))))) (.step 27 (.step 4 (.close 11)))))) (.step 24 (.step 43 (.step 52 (.step 11 (.step 20 (.close 4))))))) (.split 36 0 (.step 42 (.step 15 (.step 23 (.step 24 (.step 9 (.close 17)))))) (.step 4 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.step 24 (.step 43 (.close 52))) (.step 4 (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))))) (.split 34 0 (.split 36 0 (.split 39 0 (.split 35 0 (.step 52 (.step 24 (.step 11 (.step 18 (.step 20 (.close 18)))))) (.step 5 (.step 24 (.close 13)))) (.step 24 (.step 31 (.step 11 (.step 17 (.step 19 (.step 24 (.step 13 (.close 15))))))))) (.step 13 (.step 5 (.step 24 (.step 19 (.close 20)))))) (.step 13 (.step 24 (.step 33 (.step 5 (.step 11 (.close 17)))))))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512453928265786678923179698845599343722567883189911552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 52 (.step 24 (.step 42 (.step 11 (.step 4 (.close 20))))))) (.step 24 (.step 43 (.step 42 (.step 13 (.step 5 (.step 9 (.step 11 (.close 17))))))))) (.split 36 0 (.step 42 (.step 15 (.step 23 (.step 24 (.step 9 (.close 17)))))) (.step 4 (.step 24 (.step 13 (.close 19)))))) (.split 35 0 (.step 24 (.step 43 (.step 42 (.step 13 (.step 5 (.step 9 (.step 11 (.close 17)))))))) (.step 4 (.step 17 (.step 15 (.step 17 (.step 9 (.step 19 (.close 20))))))))) (.split 34 0 (.split 36 0 (.step 42 (.step 5 (.step 13 (.step 24 (.close 19))))) (.step 13 (.step 5 (.step 24 (.close 19))))) (.step 13 (.step 24 (.step 33 (.step 5 (.step 11 (.close 17)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 13 (.step 11 (.step 17 (.close 18)))))) (.step 13 (.step 11 (.step 17 (.step 19 (.step 5 (.step 19 (.step 20 (.close 24))))))))) (.step 24 (.close 19))) (.step 13 (.step 17 (.step 23 (.step 11 (.close 17)))))) (.step 13 (.step 42 (.step 19 (.step 24 (.step 5 (.step 11 (.close 20))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413523511420272114300817534695558113918976⟩
def references : Fin 3 → Box := ![Part8.root, Part11.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.reuse 0) (.split 16 0 (.reuse 1) (.split 17 0 (.reuse 2) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 13 (.step 11 (.step 17 (.close 18)))))) (.step 13 (.step 11 (.step 17 (.step 19 (.step 5 (.step 19 (.close 20)))))))) (.step 24 (.close 19))) (.step 13 (.step 17 (.step 23 (.step 11 (.close 17)))))) (.step 13 (.step 42 (.step 19 (.step 20 (.close 9)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.split 30 0 (.step 11 (.step 17 (.step 42 (.step 20 (.step 4 (.close 13)))))) (.step 13 (.step 11 (.step 17 (.step 19 (.close 20)))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.step 20 (.close 24)))))))) (.step 11 (.step 17 (.step 19 (.close 5))))) (.step 19 (.step 13 (.close 20)))) (.step 11 (.step 17 (.step 19 (.close 4))))) (.step 17 (.step 13 (.step 19 (.close 20))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115992053442883318074582352331628185222896545996906408376363411523775323428809402197989784551424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 35 0 (.split 39 0 (.split 43 0 (.split 36 0 (.split 42 0 (.split 61 0 (.split 63 0 (.step 57 (.close 4)) (.step 15 (.step 4 (.step 17 (.close 22))))) (.step 15 (.step 5 (.step 22 (.close 26))))) (.step 15 (.step 62 (.step 4 (.close 13))))) (.step 15 (.step 57 (.step 4 (.close 13))))) (.step 9 (.split 61 0 (.step 9 (.close 5)) (.step 52 (.step 5 (.close 9)))))) (.split 43 0 (.split 50 0 (.split 51 0 (.split 58 0 (.step 40 (.step 15 (.step 13 (.step 17 (.close 19))))) (.split 59 0 (.step 40 (.step 15 (.step 13 (.step 17 (.close 19))))) (.step 57 (.step 40 (.step 15 (.close 17)))))) (.step 57 (.split 61 0 (.step 4 (.step 17 (.step 15 (.step 19 (.close 20))))) (.step 4 (.close 5))))) (.step 53 (.split 61 0 (.step 21 (.close 38)) (.step 15 (.step 4 (.close 5)))))) (.step 9 (.step 27 (.close 52))))) (.step 9 (.split 36 0 (.step 53 (.split 39 0 (.step 15 (.step 53 (.step 54 (.close 4)))) (.step 53 (.step 15 (.step 38 (.close 4)))))) (.step 57 (.step 15 (.step 33 (.step 13 (.step 5 (.close 17))))))))) (.step 15 (.split 35 0 (.step 15 (.step 9 (.step 52 (.step 24 (.step 15 (.close 4)))))) (.step 15 (.close 37))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057597465300074312614047664224677810109165534695967948800⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 30 0 (.reuse 0) (.run (.split 34 0 (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 51 0 (.split 58 0 (.step 43 (.step 18 (.step 15 (.close 33)))) (.step 4 (.step 15 (.close 24)))) (.step 53 (.step 18 (.step 15 (.close 20))))) (.step 53 (.step 13 (.step 4 (.close 15))))) (.step 53 (.step 9 (.close 5)))) (.step 43 (.step 42 (.step 53 (.step 4 (.step 9 (.close 13))))))) (.split 39 0 (.split 43 0 (.split 49 0 (.split 51 0 (.split 36 0 (.step 15 (.step 38 (.close 4))) (.step 38 (.close 4))) (.step 15 (.step 18 (.close 38)))) (.step 15 (.step 42 (.step 13 (.step 21 (.close 37)))))) (.step 9 (.step 18 (.step 9 (.close 11))))) (.step 4 (.step 9 (.close 38))))) (.split 35 0 (.split 36 0 (.step 15 (.step 9 (.step 18 (.step 17 (.step 19 (.close 20)))))) (.step 15 (.step 37 (.step 15 (.close 18))))) (.step 15 (.step 18 (.step 15 (.step 19 (.close 20)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1496577676626845917468569053617346715934736278093824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513949044439382397362821900268037991763442439867596800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 68 (.split 39 0 (.split 50 0 (.split 54 0 (.step 68 (.close 5)) (.step 4 (.step 9 (.step 15 (.step 13 (.step 17 (.close 20))))))) (.step 53 (.split 61 0 (.step 61 (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 4 (.close 5))))) (.step 27 (.step 61 (.split 61 0 (.step 42 (.step 4 (.step 17 (.step 15 (.close 19))))) (.step 4 (.close 5))))))) (.step 24 (.step 18 (.step 9 (.step 15 (.step 24 (.close 13))))))) (.split 36 0 (.step 53 (.step 9 (.step 15 (.step 4 (.step 17 (.step 20 (.close 24))))))) (.step 43 (.step 15 (.step 17 (.step 19 (.close 33))))))) (.step 43 (.step 68 (.close 15)))) (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 18 (.step 9 (.step 17 (.step 15 (.close 20))))))) (.step 4 (.step 38 (.step 9 (.close 13))))) (.step 24 (.step 13 (.step 33 (.step 15 (.step 4 (.close 37))))))))) (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 18 (.step 9 (.step 17 (.step 15 (.close 20)))))) (.step 4 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19))))))) (.step 24 (.step 13 (.close 15))))) (.step 24 (.close 11)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1461501637332232146199469748589186826717286629376, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019728265740103952870708046462095800139776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 53 (.step 68 (.split 39 0 (.split 54 0 (.step 68 (.close 5)) (.step 4 (.step 9 (.step 15 (.step 13 (.step 17 (.close 20))))))) (.step 27 (.step 42 (.step 4 (.step 13 (.close 15)))))))) (.step 24 (.step 18 (.step 9 (.step 15 (.step 24 (.close 13))))))) (.step 53 (.step 4 (.close 15)))) (.step 43 (.step 68 (.close 15)))) (.step 24 (.split 34 0 (.step 53 (.step 4 (.close 15))) (.step 24 (.step 13 (.step 33 (.step 15 (.step 4 (.close 37))))))))) (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 18 (.step 9 (.step 17 (.step 15 (.close 20)))))) (.step 4 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19))))))) (.step 24 (.step 13 (.close 15))))) (.step 24 (.close 11)))) (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 18 (.step 9 (.step 17 (.step 15 (.close 20)))))) (.step 4 (.step 17 (.step 24 (.step 9 (.step 15 (.close 19))))))) (.step 24 (.step 13 (.close 15))))) (.step 24 (.close 11))) (.step 24 (.step 20 (.step 11 (.step 5 (.close 19))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1393797904136159731261855295847583948210176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413524840648267899216690438502618394263552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 15 (.split 34 0 (.split 39 0 (.step 15 (.step 5 (.step 9 (.close 17)))) (.step 52 (.step 27 (.step 23 (.step 15 (.close 17)))))) (.step 15 (.step 43 (.close 4))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 15 (.step 24 (.step 17 (.close 13)))) (.step 13 (.close 15))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 15 (.step 13 (.close 17))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 27 (.step 48 (.step 15 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 5 (.step 15 (.step 13 (.close 17)))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 27 (.step 48 (.step 15 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 5 (.step 15 (.step 13 (.close 17))))) (.step 24 (.step 11 (.step 13 (.close 5)))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 24 (.step 27 (.step 42 (.step 15 (.step 17 (.step 4 (.close 5))))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 5 (.step 15 (.step 13 (.close 17))))) (.step 24 (.step 11 (.step 13 (.close 5))))) (.step 24 (.step 11 (.step 14 (.step 13 (.close 17))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620777316594601057597465300074312612718437496543494464491129132390809600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 39 0 (.split 43 0 (.split 50 0 (.split 51 0 (.split 36 0 (.step 52 (.step 68 (.close 4))) (.step 43 (.step 39 (.step 13 (.step 18 (.step 13 (.close 33))))))) (.step 52 (.step 39 (.step 4 (.close 19))))) (.step 52 (.step 53 (.step 18 (.close 20))))) (.step 52 (.split 36 0 (.split 54 0 (.step 68 (.step 4 (.close 9))) (.step 9 (.close 5))) (.step 9 (.step 54 (.step 9 (.step 4 (.close 29)))))))) (.split 43 0 (.split 50 0 (.split 51 0 (.split 54 0 (.step 71 (.step 24 (.step 19 (.close 38)))) (.step 43 (.step 52 (.step 4 (.close 19))))) (.step 52 (.step 31 (.step 24 (.close 33))))) (.step 52 (.step 53 (.step 24 (.step 4 (.close 33)))))) (.step 52 (.split 35 0 (.split 36 0 (.step 27 (.step 9 (.close 11))) (.step 9 (.step 5 (.step 20 (.step 5 (.close 31)))))) (.step 9 (.step 24 (.step 9 (.close 5)))))))) (.split 35 0 (.step 52 (.step 15 (.step 4 (.close 17)))) (.step 15 (.step 33 (.step 13 (.close 15)))))) (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 33 (.step 39 (.step 4 (.close 9))))) (.split 36 0 (.step 52 (.step 31 (.step 33 (.step 9 (.close 19))))) (.step 33 (.step 20 (.step 13 (.close 19)))))) (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 4 (.step 9 (.close 19))))) (.step 18 (.step 33 (.step 19 (.step 20 (.close 24)))))) (.step 33 (.step 24 (.close 13))))) (.split 35 0 (.split 36 0 (.step 52 (.close 13)) (.step 13 (.step 15 (.step 33 (.close 15))))) (.step 33 (.close 15))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1496577676626844588241840919301702041529172700954624, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513949044439382396033595172133722347089036876290457600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.split 39 0 (.step 52 (.step 54 (.step 24 (.step 11 (.close 18))))) (.step 24 (.step 27 (.step 20 (.step 13 (.close 31))))))) (.step 43 (.step 13 (.step 24 (.step 4 (.close 33)))))) (.split 36 0 (.step 68 (.step 43 (.step 24 (.step 13 (.close 4))))) (.step 33 (.step 4 (.step 24 (.step 9 (.step 13 (.close 38)))))))) (.split 35 0 (.split 36 0 (.step 43 (.step 13 (.step 15 (.step 5 (.close 11))))) (.step 13 (.step 43 (.close 16)))) (.step 33 (.step 15 (.step 13 (.step 4 (.close 15))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.step 33 (.step 20 (.step 4 (.close 9))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 33 (.step 24 (.step 4 (.close 9)))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 33 (.step 43 (.step 14 (.step 4 (.close 39)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 61 (.step 13 (.step 11 (.step 4 (.close 19))))))) (.step 13 (.step 24 (.close 20)))) (.step 24 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 17 (.step 23 (.close 15))))) (.step 13 (.step 33 (.step 24 (.split 42 0 (.step 17 (.close 20)) (.step 24 (.step 20 (.close 14))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512453928264392882348272802549853589559928857298993152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.split 39 0 (.step 52 (.step 53 (.step 63 (.step 9 (.step 19 (.close 20)))))) (.step 24 (.step 27 (.step 19 (.step 13 (.close 31))))))) (.step 43 (.step 13 (.step 24 (.step 4 (.close 33)))))) (.split 36 0 (.step 53 (.close 19)) (.step 33 (.step 4 (.step 24 (.step 9 (.step 13 (.close 38)))))))) (.split 35 0 (.split 36 0 (.step 43 (.step 13 (.step 15 (.step 5 (.close 11))))) (.step 13 (.step 43 (.close 16)))) (.step 33 (.step 15 (.step 13 (.step 4 (.close 15))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 53 (.close 13)) (.step 13 (.step 33 (.step 24 (.step 4 (.close 9)))))) (.step 33 (.close 19))) (.step 13 (.step 33 (.step 38 (.close 5)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 42 (.step 13 (.step 11 (.step 4 (.close 19))))))) (.step 13 (.step 24 (.step 19 (.step 5 (.step 9 (.step 11 (.close 20)))))))) (.step 24 (.step 19 (.step 4 (.close 13))))) (.step 13 (.step 17 (.step 23 (.close 15))))) (.step 13 (.step 33 (.step 24 (.step 53 (.step 14 (.close 17)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019726936513375818555063372056532223000576⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 52 (.split 42 0 (.step 42 (.step 24 (.step 11 (.step 13 (.close 18))))) (.step 13 (.step 23 (.close 24))))) (.step 24 (.step 33 (.step 42 (.step 4 (.step 5 (.close 13))))))) (.step 13 (.step 24 (.step 19 (.step 5 (.step 9 (.step 11 (.close 20)))))))) (.step 24 (.step 19 (.step 4 (.close 13))))) (.step 13 (.step 17 (.step 23 (.close 15))))) (.step 13 (.step 33 (.step 24 (.step 53 (.step 14 (.close 17))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 70 (.step 24 (.step 13 (.step 19 (.step 13 (.step 11 (.close 18))))))) (.step 13 (.step 19 (.step 20 (.close 9))))) (.step 19 (.step 11 (.step 5 (.close 13))))) (.step 19 (.step 13 (.close 20)))) (.step 19 (.step 13 (.close 4)))) (.step 17 (.step 13 (.close 14)))) (.step 19 (.step 13 (.step 20 (.step 15 (.step 9 (.close 24))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019726936513375818555063372056532223000576⟩
def references : Fin 3 → Box := ![Part19.root, Part20.root, Part22.root]
def proof : Chunks.Proof 3 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 62 (.step 24 (.step 4 (.step 5 (.close 11)))))) (.step 24 (.step 62 (.step 70 (.split 42 0 (.step 24 (.step 11 (.step 13 (.close 18)))) (.step 5 (.step 11 (.step 19 (.close 13))))))))) (.split 36 0 (.step 62 (.step 43 (.step 13 (.step 24 (.close 4))))) (.step 33 (.step 4 (.step 24 (.step 9 (.step 13 (.close 38)))))))) (.split 35 0 (.split 36 0 (.step 43 (.step 13 (.step 15 (.step 5 (.close 11))))) (.step 13 (.step 43 (.close 16)))) (.step 33 (.step 15 (.step 13 (.step 4 (.close 15))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 62 (.split 39 0 (.step 52 (.step 33 (.step 4 (.close 9)))) (.step 24 (.step 33 (.close 13)))))) (.step 13 (.step 33 (.step 24 (.step 4 (.close 9)))))) (.step 33 (.step 19 (.step 13 (.close 20))))) (.step 13 (.step 33 (.step 43 (.step 14 (.step 4 (.close 39)))))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512452466764149348020262762811366855668949723960573952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 43 0 (.step 15 (.split 50 0 (.step 66 (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 48 (.step 13 (.close 17)))))) (.split 50 0 (.split 51 0 (.step 15 (.close 11)) (.step 52 (.step 15 (.close 11)))) (.step 15 (.step 52 (.step 15 (.close 11)))))) (.step 15 (.split 43 0 (.split 50 0 (.split 35 0 (.split 51 0 (.step 17 (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 17 (.close 13)))) (.step 5 (.step 15 (.step 13 (.close 17))))) (.step 15 (.step 42 (.step 17 (.close 13))))) (.step 15 (.step 31 (.step 11 (.close 13))))))) (.step 15 (.split 35 0 (.step 13 (.close 17)) (.step 15 (.close 17))))) (.split 34 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 52 (.step 15 (.step 13 (.close 20)))) (.step 13 (.close 15))) (.step 31 (.step 15 (.step 17 (.step 13 (.step 9 (.close 15))))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.step 13 (.close 17)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 35 0 (.step 52 (.step 15 (.step 11 (.close 13)))) (.step 5 (.step 15 (.close 13)))) (.step 24 (.step 31 (.step 11 (.close 17))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.step 13 (.close 17))))) (.step 13 (.step 15 (.close 17))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨1329229263435516101133208558057291776, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513949044439382397362823167918638219992843936570802176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 39 0 (.split 43 0 (.step 15 (.step 52 (.close 4))) (.step 52 (.step 9 (.close 5)))) (.step 15 (.step 43 (.step 15 (.step 52 (.step 5 (.step 9 (.close 17)))))))) (.step 15 (.step 43 (.step 15 (.close 13))))) (.step 15 (.close 13))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 15 (.step 18 (.step 11 (.step 13 (.close 17)))))) (.step 13 (.step 15 (.close 17)))) (.step 18 (.step 15 (.close 17)))) (.step 52 (.close 15)))) (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 18 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 24 (.close 13)))) (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 13 (.close 15))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17))))) (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 18 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 24 (.close 13)))) (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 13 (.close 15))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17)))) (.step 24 (.step 13 (.close 4))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413524840649535549816918667904115097468928⟩
def references : Fin 3 → Box := ![Part23.root, Part24.root, Part25.root]
def proof : Chunks.Proof 3 := (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 35 0 (.step 52 (.step 15 (.step 11 (.close 13)))) (.step 5 (.step 15 (.close 13)))) (.step 24 (.step 31 (.step 11 (.close 17))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.step 13 (.close 17))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17))))) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 35 0 (.step 52 (.step 15 (.step 11 (.close 13)))) (.step 5 (.step 15 (.close 13)))) (.step 24 (.step 31 (.step 11 (.close 17))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.step 13 (.close 17))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17))) (.split 22 0 (.step 13 (.close 17)) (.step 17 (.close 13))))))) (.split 14 0 (.split 16 0 (.reuse 2) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 18 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 15 (.step 13 (.close 17))))) (.step 24 (.close 13)))) (.step 53 (.step 13 (.close 15)))) (.step 24 (.step 13 (.close 4)))) (.step 24 (.step 14 (.step 11 (.step 13 (.close 17)))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.step 15 (.close 13)) (.step 15 (.close 13))) (.step 24 (.close 13))) (.step 24 (.close 13))) (.step 24 (.step 13 (.close 17)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes
  · exact Part24.excludes
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413524840649535549816918667904115097468928⟩
def references : Fin 6 → Box := ![Part13.root, Part15.root, Part16.root, Part17.root, Part18.root, Part26.root]
def proof : Chunks.Proof 6 := (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.run (.split 30 0 (.split 34 0 (.split 39 0 (.split 42 0 (.step 68 (.split 35 0 (.step 62 (.step 68 (.step 4 (.close 5)))) (.step 53 (.step 4 (.step 9 (.step 15 (.step 13 (.step 17 (.close 20))))))))) (.step 43 (.step 62 (.step 24 (.step 43 (.step 9 (.step 15 (.step 13 (.step 4 (.close 19)))))))))) (.step 43 (.step 27 (.step 42 (.step 62 (.step 24 (.step 4 (.close 5)))))))) (.step 43 (.step 68 (.close 15)))) (.step 24 (.split 34 0 (.split 35 0 (.step 24 (.step 43 (.step 18 (.step 9 (.step 17 (.step 15 (.close 20))))))) (.step 4 (.step 38 (.step 9 (.close 13))))) (.step 24 (.step 13 (.step 33 (.step 15 (.step 4 (.close 37))))))))))) (.reuse 2)) (.reuse 3)) (.reuse 4))) (.reuse 5))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes
  · exact Part15.excludes
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part18.excludes
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part27

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part27.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case28

namespace FiveColour.Packed.EnumerationChunks.Projected.Case28
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 272 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 272 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 272 0).upper i := by decide +kernel
lemma budget_model : (⟨10699377823114761907191, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646219954648068689896578978248292267480420713472, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 272), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨10699377823114761907191, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646219954648068689896578978248292267480420713472, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 272) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 272 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 272 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 272) (Archive.root 272) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 272 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 272 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case28

namespace FiveColour.Packed.EnumerationChunks.Case28
def root : Box := Archive.root 272
def families : Fin 78 → List Cut := Enumeration.families 272
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case28.original_covered points
end FiveColour.Packed.EnumerationChunks.Case28
