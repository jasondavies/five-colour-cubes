module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case13
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435877942431820996935680⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨10699377823114745129911, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487662666603259713959062043145214737994425041920, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115992053442883318074582352331628185222896545996906408376362082295779538512936498390929504206848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 0 (.split 34 0 (.split 39 0 (.split 42 0 (.split 36 0 (.step 68 (.step 4 (.close 5))) (.step 54 (.step 9 (.step 4 (.step 13 (.close 18)))))) (.step 62 (.step 9 (.step 4 (.step 13 (.close 18)))))) (.split 42 0 (.split 61 0 (.split 63 0 (.split 62 0 (.step 27 (.step 5 (.step 19 (.close 38)))) (.step 42 (.close 4))) (.step 27 (.step 52 (.step 57 (.step 4 (.close 35)))))) (.step 52 (.step 71 (.step 4 (.close 5))))) (.step 62 (.step 57 (.step 4 (.step 5 (.close 9))))))) (.split 39 0 (.split 43 0 (.split 50 0 (.split 51 0 (.step 68 (.step 15 (.step 4 (.step 5 (.close 17))))) (.step 52 (.step 39 (.step 18 (.step 4 (.close 15)))))) (.step 52 (.step 58 (.step 15 (.close 20))))) (.step 9 (.step 52 (.step 71 (.close 9))))) (.step 52 (.split 42 0 (.split 54 0 (.step 31 (.step 9 (.step 15 (.close 19)))) (.step 9 (.step 15 (.step 5 (.close 19))))) (.step 15 (.step 31 (.step 9 (.step 19 (.step 20 (.step 19 (.close 38))))))))))) (.step 53 (.split 39 0 (.split 43 0 (.split 51 0 (.split 58 0 (.step 68 (.step 15 (.step 18 (.step 5 (.close 17))))) (.step 40 (.step 24 (.step 15 (.step 17 (.close 39)))))) (.step 53 (.step 54 (.step 39 (.close 4))))) (.step 9 (.close 29))) (.step 53 (.step 9 (.step 38 (.close 4))))))))
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387624381372985387180762800817231128545920125768513194383333836980224000⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 24 0 (.split 30 0 (.reuse 0) (.run (.split 35 0 (.step 53 (.split 39 0 (.split 42 0 (.step 53 (.step 68 (.step 4 (.close 9)))) (.step 62 (.step 33 (.step 9 (.step 4 (.close 13)))))) (.step 53 (.step 31 (.step 24 (.step 9 (.close 33))))))) (.split 39 0 (.step 53 (.step 68 (.step 9 (.step 18 (.close 33))))) (.split 43 0 (.step 42 (.close 4)) (.step 9 (.step 24 (.step 9 (.step 33 (.close 5)))))))))) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 42 0 (.split 61 0 (.split 63 0 (.split 62 0 (.step 27 (.close 4)) (.step 42 (.step 53 (.step 4 (.close 11))))) (.step 27 (.step 4 (.close 7)))) (.step 52 (.split 62 0 (.step 5 (.step 27 (.close 4))) (.step 42 (.step 46 (.step 4 (.close 27))))))) (.step 62 (.step 7 (.step 4 (.close 5))))) (.step 42 (.step 9 (.step 53 (.close 29))))) (.split 39 0 (.split 43 0 (.split 50 0 (.step 40 (.step 15 (.close 29))) (.step 52 (.step 40 (.step 15 (.close 29))))) (.step 7 (.close 9))) (.split 43 0 (.split 50 0 (.step 5 (.step 27 (.step 7 (.step 17 (.step 27 (.step 15 (.close 29))))))) (.step 42 (.step 5 (.step 27 (.close 7))))) (.step 5 (.step 7 (.close 9)))))) (.split 35 0 (.split 43 0 (.split 49 0 (.split 51 0 (.split 42 0 (.step 42 (.step 7 (.step 4 (.step 15 (.close 20))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 42 (.step 7 (.close 20))))) (.step 53 (.step 7 (.step 4 (.step 15 (.close 20)))))) (.step 7 (.step 9 (.close 27)))) (.split 43 0 (.step 42 (.close 4)) (.step 7 (.close 9)))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097246545182300911861077801358741076981241580879872000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 68 (.step 54 (.close 5))) (.step 61 (.step 68 (.step 5 (.close 13))))) (.step 68 (.step 38 (.step 24 (.close 13))))) (.split 34 0 (.split 35 0 (.step 53 (.step 42 (.step 54 (.step 4 (.step 9 (.close 11)))))) (.step 42 (.close 4))) (.split 35 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 13 (.step 15 (.close 17))))))) (.split 30 0 (.split 34 0 (.step 61 (.step 68 (.step 27 (.step 61 (.step 4 (.close 7)))))) (.step 7 (.step 17 (.step 15 (.close 19))))) (.step 7 (.step 24 (.close 19))))) (.split 24 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 61 (.step 4 (.step 9 (.close 11))))) (.step 24 (.step 11 (.step 19 (.close 20)))))) (.step 24 (.split 35 0 (.step 70 (.step 17 (.step 20 (.close 24)))) (.step 17 (.step 19 (.step 24 (.close 20))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 70 (.step 20 (.step 24 (.step 11 (.close 13)))))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.step 33 (.close 20)))))) (.step 7 (.step 24 (.step 7 (.step 18 (.close 19))))))))
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
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006683938242763996005043573793264261236812414976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 53 (.step 24 (.step 42 (.step 11 (.step 4 (.close 13))))))) (.step 53 (.step 5 (.close 19)))) (.step 24 (.split 35 0 (.split 36 0 (.step 24 (.close 13)) (.step 24 (.step 19 (.step 5 (.step 9 (.step 11 (.close 15))))))) (.step 17 (.step 19 (.step 4 (.step 19 (.close 4)))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 42 (.step 13 (.step 19 (.close 20))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.close 20)))))) (.step 7 (.step 24 (.step 7 (.step 18 (.close 19)))))) (.split 24 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 24 (.step 42 (.step 11 (.step 18 (.step 13 (.close 18)))))) (.step 20 (.step 4 (.step 5 (.close 13))))) (.step 24 (.close 19))) (.step 24 (.step 19 (.close 20))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.close 19))) (.step 19 (.close 20))) (.step 19 (.step 4 (.close 13)))) (.step 19 (.step 20 (.step 17 (.step 4 (.step 9 (.close 15)))))))) (.step 7 (.step 19 (.step 7 (.step 19 (.close 20))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006683938242763996005043573793264261236812414976⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 53 (.step 68 (.step 5 (.step 4 (.close 13))))) (.step 68 (.step 27 (.step 42 (.close 4))))) (.step 53 (.close 19))) (.split 35 0 (.step 53 (.close 19)) (.split 39 0 (.step 53 (.step 4 (.step 11 (.step 13 (.step 15 (.close 19)))))) (.step 5 (.step 19 (.step 24 (.close 19))))))) (.split 30 0 (.split 34 0 (.step 42 (.step 53 (.step 7 (.step 9 (.step 7 (.step 4 (.close 20))))))) (.step 7 (.step 17 (.step 15 (.close 19))))) (.step 7 (.step 24 (.close 19))))) (.split 24 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 42 (.step 53 (.step 4 (.step 9 (.close 11)))))) (.step 24 (.step 11 (.close 19))))) (.step 24 (.split 35 0 (.step 70 (.step 17 (.step 24 (.close 19)))) (.step 17 (.step 19 (.step 4 (.step 19 (.close 4)))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 42 (.step 13 (.step 19 (.close 20))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.step 24 (.close 14))))))) (.step 7 (.step 24 (.step 7 (.step 18 (.close 19)))))))) (.reuse 0))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006683938242763996005043573793264261236812414976⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part4.root]
def proof : Chunks.Proof 3 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 30 0 (.split 39 0 (.split 35 0 (.step 62 (.step 63 (.step 9 (.step 13 (.step 15 (.close 17)))))) (.step 53 (.step 40 (.step 24 (.close 9))))) (.step 62 (.split 42 0 (.step 42 (.step 62 (.step 27 (.step 24 (.step 13 (.close 18)))))) (.step 5 (.step 24 (.close 19)))))) (.split 34 0 (.step 62 (.split 39 0 (.step 53 (.step 33 (.step 24 (.step 4 (.step 5 (.close 11)))))) (.step 24 (.step 33 (.close 19))))) (.split 35 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 13 (.step 15 (.close 17))))))) (.split 30 0 (.split 39 0 (.step 62 (.split 42 0 (.step 62 (.step 7 (.close 5))) (.step 5 (.step 7 (.step 19 (.close 20)))))) (.split 42 0 (.step 27 (.step 4 (.close 7))) (.step 7 (.step 19 (.step 20 (.close 24)))))) (.step 7 (.step 24 (.close 19))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387624381372985387180762800818624925120828289714859176775374359574347776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 30 0 (.step 52 (.split 34 0 (.split 39 0 (.split 35 0 (.step 52 (.step 63 (.step 9 (.close 20)))) (.step 15 (.step 40 (.step 9 (.step 19 (.step 20 (.close 38))))))) (.step 42 (.step 52 (.step 27 (.step 42 (.step 5 (.step 19 (.close 20)))))))) (.step 52 (.step 37 (.close 4))))) (.split 34 0 (.split 35 0 (.step 52 (.step 42 (.step 53 (.step 4 (.step 9 (.close 20)))))) (.step 42 (.close 4))) (.split 36 0 (.step 43 (.step 52 (.close 13))) (.step 13 (.step 38 (.step 24 (.step 31 (.step 9 (.close 33))))))))) (.split 34 0 (.split 43 0 (.split 50 0 (.split 51 0 (.split 30 0 (.split 35 0 (.step 52 (.step 5 (.step 7 (.step 19 (.close 27))))) (.step 42 (.step 15 (.step 5 (.step 7 (.close 17)))))) (.step 42 (.step 24 (.step 27 (.close 4))))) (.step 52 (.step 57 (.step 61 (.step 4 (.close 7)))))) (.step 52 (.step 27 (.step 4 (.close 7))))) (.step 52 (.step 9 (.step 11 (.step 4 (.step 5 (.close 7))))))) (.step 52 (.close 17)))))
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
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097246545183694708435985965305087059373282103473995776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.step 61 (.step 52 (.step 24 (.step 61 (.step 4 (.close 9)))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 13 (.step 24 (.step 11 (.close 17))))) (.step 5 (.step 19 (.step 20 (.step 9 (.close 13)))))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.step 61 (.split 39 0 (.step 52 (.step 11 (.step 17 (.step 24 (.step 15 (.close 7)))))) (.step 11 (.step 27 (.close 7))))) (.step 7 (.step 17 (.step 24 (.close 19)))))) (.split 24 0 (.split 30 0 (.step 24 (.split 34 0 (.step 61 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 20 (.step 11 (.step 17 (.step 4 (.close 19)))))))) (.step 7 (.step 17 (.step 24 (.step 27 (.step 4 (.close 5)))))))))
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
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084095751429008705194750663595721218301844174084482531328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.step 42 (.step 52 (.step 24 (.step 42 (.step 4 (.step 9 (.close 19))))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.step 42 (.step 4 (.close 5))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.split 35 0 (.split 39 0 (.step 52 (.step 11 (.step 42 (.step 7 (.step 4 (.close 15)))))) (.step 11 (.step 27 (.step 5 (.close 7))))) (.step 42 (.step 17 (.step 11 (.step 15 (.step 4 (.step 7 (.close 19)))))))) (.step 7 (.step 17 (.step 24 (.close 19)))))) (.split 24 0 (.split 30 0 (.step 24 (.split 34 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 19 (.step 24 (.step 25 (.step 11 (.step 5 (.close 17))))))))) (.step 7 (.step 17 (.step 24 (.step 19 (.step 4 (.step 15 (.close 19))))))))))
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
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332039338904168989919775656301759406538752⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.step 24 (.split 34 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 19 (.step 20 (.step 5 (.step 9 (.step 11 (.close 17))))))))) (.step 7 (.step 17 (.step 24 (.step 19 (.step 4 (.step 15 (.close 19)))))))) (.split 24 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 20 (.step 4 (.close 13)))))) (.step 13 (.step 11 (.step 17 (.step 19 (.close 20))))))) (.step 13 (.step 19 (.step 5 (.step 11 (.step 17 (.close 20))))))) (.step 11 (.step 17 (.close 19)))) (.step 13 (.step 17 (.step 16 (.step 19 (.close 20)))))) (.step 11 (.step 17 (.step 19 (.step 7 (.close 15)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387624381372985387180762800817231129875148121553429067287140897260568576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 42 0 (.split 61 0 (.split 63 0 (.split 62 0 (.step 9 (.step 57 (.close 4))) (.step 53 (.step 9 (.step 4 (.step 5 (.close 13)))))) (.step 9 (.step 15 (.step 4 (.close 17))))) (.step 15 (.step 5 (.step 9 (.close 22))))) (.step 9 (.step 15 (.step 62 (.step 4 (.close 13)))))) (.step 9 (.step 15 (.step 4 (.close 13))))) (.step 9 (.step 15 (.step 53 (.step 38 (.step 20 (.step 4 (.close 13)))))))) (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 51 0 (.step 43 (.step 15 (.close 18))) (.step 18 (.step 15 (.step 20 (.step 24 (.close 33)))))) (.step 52 (.step 53 (.close 13)))) (.step 53 (.close 9))) (.step 43 (.step 42 (.step 24 (.step 4 (.close 52)))))) (.split 39 0 (.step 15 (.step 9 (.step 42 (.step 13 (.step 18 (.close 33)))))) (.step 4 (.step 9 (.close 38)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 42 0 (.split 61 0 (.step 9 (.split 63 0 (.split 62 0 (.step 29 (.close 4)) (.step 42 (.step 4 (.step 5 (.close 17))))) (.step 15 (.step 27 (.close 4))))) (.step 52 (.split 36 0 (.split 43 0 (.step 5 (.close 15)) (.step 4 (.close 5))) (.step 4 (.close 5))))) (.step 9 (.step 43 (.step 62 (.step 5 (.step 7 (.close 15))))))) (.step 9 (.step 53 (.step 15 (.close 29))))) (.step 9 (.step 15 (.step 43 (.step 15 (.step 5 (.step 15 (.step 7 (.close 17))))))))) (.step 53 (.step 9 (.step 43 (.step 42 (.step 4 (.step 7 (.close 15))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097246545182300913190305797143656949885048641160216576⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 30 0 (.split 39 0 (.split 42 0 (.step 68 (.step 62 (.step 4 (.step 9 (.close 13))))) (.step 15 (.step 9 (.step 18 (.step 24 (.close 13)))))) (.step 43 (.step 27 (.step 42 (.step 62 (.close 4)))))) (.step 24 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 4 (.close 9))))) (.step 4 (.step 15 (.step 9 (.step 13 (.step 19 (.step 20 (.close 33)))))))))) (.step 43 (.step 27 (.step 24 (.step 4 (.step 15 (.step 7 (.close 17)))))))))) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 68 (.split 61 0 (.split 63 0 (.step 61 (.step 68 (.step 4 (.close 5)))) (.step 4 (.step 9 (.step 15 (.step 13 (.step 17 (.close 19))))))) (.step 4 (.close 5)))) (.step 9 (.step 53 (.step 15 (.step 4 (.step 17 (.close 20))))))) (.step 15 (.step 24 (.step 15 (.step 4 (.step 9 (.close 13))))))) (.step 24 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 4 (.close 9))))) (.step 4 (.step 15 (.step 9 (.step 13 (.step 19 (.step 20 (.close 33)))))))))) (.step 43 (.step 27 (.step 24 (.step 4 (.step 15 (.step 7 (.close 17)))))))) (.step 24 (.split 24 0 (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.step 20 (.close 19)))))) (.step 13 (.close 24)))) (.step 7 (.step 17 (.step 15 (.close 19)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1393797904136159731261855295847583948210176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668132164774835648560108819686883328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 24 0 (.split 22 0 (.step 15 (.step 52 (.split 30 0 (.step 15 (.step 4 (.step 5 (.close 9)))) (.step 42 (.close 13))))) (.step 24 (.step 15 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17))))))))))) (.step 52 (.split 22 0 (.step 15 (.step 9 (.step 23 (.step 17 (.step 7 (.close 15)))))) (.step 17 (.step 7 (.step 4 (.step 9 (.close 15)))))))) (.split 22 0 (.step 24 (.split 24 0 (.step 15 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17))))))))) (.step 17 (.step 7 (.step 4 (.step 9 (.close 15))))))) (.step 13 (.close 17)))) (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.step 15 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17))))))))) (.step 17 (.step 7 (.step 4 (.step 9 (.close 15))))))) (.step 13 (.close 17))) (.step 17 (.close 13)))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668132164774835648560108819686883328⟩
def references : Fin 2 → Box := ![Part11.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 68 (.step 53 (.step 68 (.step 4 (.close 5))))) (.step 43 (.step 27 (.step 42 (.step 4 (.close 13)))))) (.step 53 (.step 4 (.close 15)))) (.step 24 (.step 53 (.step 4 (.close 15))))) (.step 43 (.step 27 (.step 24 (.step 4 (.step 15 (.step 7 (.close 17)))))))) (.step 24 (.split 24 0 (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.close 19))))) (.step 13 (.close 24)))) (.step 7 (.step 17 (.step 15 (.close 19))))))) (.split 22 0 (.step 24 (.split 24 0 (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.close 19))))) (.step 13 (.close 24)))) (.step 7 (.step 17 (.step 15 (.close 19)))))) (.step 24 (.step 7 (.step 11 (.step 5 (.close 19))))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084095749967505674067272838495740639831398515402659069952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.step 52 (.split 34 0 (.split 39 0 (.split 42 0 (.step 52 (.step 68 (.step 4 (.close 9)))) (.step 62 (.step 13 (.step 9 (.step 4 (.close 18)))))) (.step 52 (.split 35 0 (.step 31 (.step 9 (.step 19 (.close 20)))) (.step 24 (.step 4 (.step 9 (.close 33))))))) (.step 15 (.step 52 (.step 15 (.close 17)))))) (.split 34 0 (.split 35 0 (.step 52 (.step 33 (.step 9 (.step 4 (.close 20))))) (.split 39 0 (.step 52 (.close 33)) (.step 18 (.step 33 (.step 19 (.close 20)))))) (.split 35 0 (.step 52 (.close 13)) (.step 15 (.step 13 (.step 15 (.close 17))))))) (.split 34 0 (.split 43 0 (.split 50 0 (.split 51 0 (.split 54 0 (.split 59 0 (.step 7 (.step 4 (.close 19))) (.step 52 (.close 7))) (.step 43 (.step 52 (.step 4 (.step 7 (.close 19)))))) (.step 7 (.step 52 (.step 7 (.close 19))))) (.step 52 (.step 53 (.step 7 (.step 4 (.close 19)))))) (.step 7 (.step 9 (.close 27)))) (.step 7 (.step 15 (.close 17))))) (.split 24 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 52 (.step 43 (.close 11))) (.step 24 (.step 70 (.step 42 (.step 13 (.step 4 (.close 9)))))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.step 70 (.step 62 (.step 33 (.step 13 (.step 4 (.step 11 (.step 19 (.close 20)))))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.step 7 (.step 24 (.close 19))))))
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
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006683938242763997272694174021493662733515620352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 52 (.step 53 (.step 63 (.step 9 (.step 19 (.close 20)))))) (.step 43 (.step 13 (.step 24 (.close 4))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.step 53 (.close 13)) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 42 (.step 13 (.step 4 (.close 9)))))) (.step 13 (.step 20 (.close 24)))) (.step 24 (.step 13 (.step 19 (.close 4))))) (.step 13 (.step 17 (.step 14 (.close 4))))))) (.step 7 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 30 0 (.step 24 (.step 13 (.step 11 (.step 19 (.close 13))))) (.step 13 (.step 24 (.step 11 (.close 19))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 23)))))) (.step 24 (.step 13 (.step 19 (.close 4))))) (.step 13 (.step 17 (.step 14 (.close 4))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 19 (.step 13 (.step 19 (.step 4 (.close 9))))))) (.step 13 (.step 19 (.close 20)))) (.step 19 (.step 4 (.close 13)))) (.step 13 (.step 14 (.close 17)))) (.step 13 (.step 19 (.step 20 (.step 9 (.close 15))))))))))
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
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097246545183694708435987232955687287602683600177201152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 34 0 (.split 39 0 (.split 43 0 (.step 15 (.split 50 0 (.step 66 (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 13 (.close 17))))) (.split 50 0 (.split 51 0 (.step 15 (.close 11)) (.step 13 (.step 15 (.close 11)))) (.step 15 (.step 13 (.close 11))))) (.step 15 (.split 43 0 (.split 30 0 (.step 42 (.step 15 (.step 13 (.close 17)))) (.step 31 (.step 17 (.close 13)))) (.step 15 (.step 31 (.step 11 (.close 13))))))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.split 34 0 (.split 39 0 (.split 43 0 (.split 30 0 (.split 50 0 (.step 17 (.step 7 (.step 4 (.close 15)))) (.step 15 (.step 7 (.close 17)))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 9 (.close 11)))) (.split 30 0 (.split 35 0 (.step 27 (.step 4 (.close 5))) (.step 5 (.step 11 (.step 15 (.step 7 (.close 17)))))) (.step 7 (.close 17)))) (.step 7 (.step 15 (.close 17)))))) (.split 24 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 62 (.step 13 (.step 4 (.step 9 (.close 15))))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 7 (.step 15 (.close 17))))) (.split 22 0 (.split 24 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.close 13)) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 13 (.step 15 (.close 17)))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332039338905436640520003885703256109744128⟩
def references : Fin 3 → Box := ![Part14.root, Part15.root, Part16.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 54 (.step 24 (.close 11)))) (.step 24 (.split 36 0 (.step 24 (.step 27 (.step 13 (.close 18)))) (.step 5 (.step 20 (.step 9 (.close 13))))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 33 (.step 4 (.step 9 (.close 20))))) (.step 13 (.step 24 (.step 4 (.step 9 (.close 33)))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 61 (.step 13 (.step 11 (.step 4 (.close 19))))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 23)))))) (.step 24 (.step 13 (.step 19 (.close 20))))) (.step 13 (.step 17 (.step 14 (.close 4))))))))) (.reuse 1)) (.split 16 0 (.reuse 2) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 39 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 17 (.step 13 (.close 11)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 17 (.close 13))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435876789510316390088704⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 34 0 (.split 30 0 (.step 15 (.step 52 (.split 39 0 (.step 15 (.step 18 (.close 9))) (.step 43 (.step 15 (.step 5 (.step 9 (.close 17)))))))) (.split 35 0 (.step 52 (.step 15 (.step 13 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 9 (.step 15 (.close 17)))))))) (.step 15 (.close 13))) (.step 15 (.step 43 (.step 9 (.step 52 (.step 15 (.step 5 (.close 7)))))))) (.step 24 (.split 24 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 5 (.step 7 (.step 15 (.close 17))))))) (.split 22 0 (.step 24 (.split 24 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 5 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 13 (.step 15 (.close 17)))))) (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 5 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.step 13 (.close 17))))) (.split 16 0 (.split 17 0 (.split 24 0 (.split 36 0 (.step 15 (.step 4 (.close 5))) (.step 13 (.close 15))) (.step 5 (.step 15 (.close 7)))) (.step 13 (.close 15))) (.step 13 (.close 17))))))
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435876789510316390088704⟩
def references : Fin 6 → Box := ![Part5.root, Part6.root, Part7.root, Part9.root, Part13.root, Part18.root]
def proof : Chunks.Proof 6 := (.split 10 0 (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.run (.split 24 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 52 (.step 11 (.step 4 (.close 19))))) (.step 42 (.step 11 (.step 17 (.step 13 (.step 4 (.step 19 (.close 20))))))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 62 (.step 70 (.step 42 (.step 13 (.step 24 (.step 11 (.close 17))))))) (.step 5 (.step 19 (.step 24 (.close 13))))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.step 4 (.close 7))) (.step 42 (.step 11 (.step 15 (.step 17 (.step 4 (.step 7 (.close 19)))))))) (.step 7 (.close 17))) (.step 7 (.step 17 (.step 24 (.close 19)))))))) (.reuse 2)) (.reuse 3))) (.reuse 4)) (.reuse 5))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part9.excludes
  · exact Part13.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1152921505680588800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084095749967505674067272837228090039604322035410562711552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 42 0 (.split 61 0 (.split 63 0 (.split 62 0 (.step 9 (.close 4)) (.step 53 (.step 9 (.close 4)))) (.step 9 (.step 4 (.close 11)))) (.step 52 (.split 62 0 (.step 9 (.close 4)) (.step 46 (.step 4 (.step 7 (.close 9))))))) (.step 9 (.step 62 (.close 7)))) (.step 9 (.step 15 (.step 52 (.step 7 (.close 9)))))) (.step 9 (.step 53 (.split 36 0 (.step 53 (.step 9 (.close 4))) (.step 9 (.step 7 (.close 15))))))) (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.step 7 (.step 4 (.close 9))) (.step 52 (.step 53 (.close 7)))) (.step 7 (.step 9 (.step 7 (.close 27))))) (.step 43 (.step 27 (.step 42 (.step 4 (.step 7 (.close 9))))))) (.split 39 0 (.split 43 0 (.split 49 0 (.split 36 0 (.step 9 (.step 7 (.step 4 (.close 9)))) (.step 7 (.close 9))) (.step 9 (.step 42 (.close 7)))) (.step 7 (.close 9))) (.step 4 (.step 9 (.close 7)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 42 0 (.split 61 0 (.step 9 (.step 11 (.step 4 (.close 5)))) (.step 46 (.step 9 (.close 11)))) (.step 9 (.close 4))) (.step 9 (.step 5 (.close 11)))) (.step 9 (.close 29))) (.step 53 (.step 9 (.step 43 (.step 5 (.step 9 (.close 7)))))))) (.split 24 0 (.split 30 0 (.split 39 0 (.split 42 0 (.step 68 (.step 62 (.step 4 (.close 7)))) (.step 7 (.close 9))) (.step 43 (.step 27 (.step 42 (.step 11 (.close 4)))))) (.step 7 (.step 9 (.close 11)))) (.step 43 (.step 27 (.close 4))))))
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
def root : Box := ⟨1393796574908163946345983544962028274712576, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332039338904168989919776809223264013385728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 15 (.split 30 0 (.split 34 0 (.split 39 0 (.split 43 0 (.split 50 0 (.step 9 (.step 40 (.step 7 (.close 9)))) (.step 52 (.step 9 (.close 4)))) (.step 9 (.close 5))) (.step 27 (.step 42 (.step 11 (.step 4 (.close 7)))))) (.step 9 (.step 40 (.step 43 (.close 9))))) (.split 34 0 (.step 42 (.step 27 (.step 43 (.step 24 (.step 4 (.close 9)))))) (.step 4 (.step 7 (.close 9)))))) (.step 52 (.step 15 (.step 9 (.step 23 (.step 11 (.close 7))))))) (.step 24 (.split 24 0 (.split 34 0 (.step 24 (.step 27 (.step 48 (.close 11)))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 11 (.step 5 (.close 7)))))) (.split 22 0 (.step 24 (.split 24 0 (.split 34 0 (.step 24 (.step 27 (.step 48 (.close 11)))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 11 (.step 5 (.close 7))))) (.step 7 (.close 11)))) (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.split 34 0 (.step 24 (.step 27 (.step 42 (.step 15 (.step 4 (.close 9)))))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 11 (.step 5 (.close 7))))) (.step 7 (.close 11))) (.step 11 (.close 7)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨1329227995784915874056728565960933376, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668132164774835649713030324293730304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 30 0 (.step 15 (.step 9 (.split 61 0 (.step 9 (.close 4)) (.step 4 (.step 9 (.close 4)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.step 15 (.step 7 (.step 4 (.step 7 (.close 9)))))) (.step 7 (.close 9))) (.step 9 (.step 4 (.close 7)))) (.step 7 (.step 9 (.close 7))))) (.step 9 (.step 7 (.step 9 (.close 4))))) (.split 22 0 (.split 24 0 (.split 30 0 (.step 15 (.step 9 (.step 4 (.close 9)))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.close 9))) (.step 4 (.step 17 (.step 7 (.step 9 (.close 11))))))) (.split 24 0 (.split 30 0 (.split 17 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.step 4 (.close 9))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 9 (.step 4 (.close 7)))) (.step 7 (.step 9 (.close 7)))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 7 (.close 9))) (.split 34 0 (.step 53 (.step 24 (.step 4 (.close 9)))) (.step 4 (.step 9 (.close 7)))))) (.split 24 0 (.split 30 0 (.split 36 0 (.split 39 0 (.step 15 (.close 4)) (.step 52 (.split 16 0 (.step 15 (.close 4)) (.step 4 (.close 11))))) (.step 15 (.step 4 (.close 7)))) (.step 4 (.step 15 (.close 7)))) (.split 16 0 (.split 17 0 (.step 15 (.close 4)) (.step 11 (.step 4 (.step 7 (.close 9))))) (.step 11 (.step 4 (.step 7 (.close 9))))))))
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
def root : Box := ⟨1267650600229382323002383794176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435877942431820996935680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 24 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.split 30 0 (.step 15 (.split 39 0 (.step 7 (.step 4 (.step 7 (.close 9)))) (.step 43 (.step 27 (.step 52 (.step 4 (.step 7 (.close 9)))))))) (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.split 16 0 (.split 17 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 52 (.split 50 0 (.step 7 (.step 4 (.close 9))) (.step 15 (.step 43 (.step 9 (.close 4)))))) (.step 7 (.close 9))) (.step 4 (.step 9 (.step 15 (.step 24 (.step 9 (.step 7 (.close 9)))))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.split 16 0 (.step 52 (.split 17 0 (.step 24 (.step 15 (.step 9 (.step 43 (.step 27 (.step 4 (.close 7))))))) (.step 5 (.step 7 (.step 9 (.close 11)))))) (.step 7 (.step 9 (.close 11))))) (.split 16 0 (.split 24 0 (.split 17 0 (.split 36 0 (.step 15 (.step 4 (.close 5))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.step 11 (.close 7)))) (.step 7 (.close 11)))) (.split 14 0 (.split 24 0 (.split 16 0 (.split 30 0 (.split 36 0 (.step 15 (.close 4)) (.step 7 (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 4 (.step 29 (.close 9)))) (.step 4 (.step 15 (.close 7))))))
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435877942431820996935680⟩
def references : Fin 5 → Box := ![Part19.root, Part20.root, Part21.root, Part22.root, Part23.root]
def proof : Chunks.Proof 5 := (.split 6 0 (.reuse 0) (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 68 (.step 27 (.split 61 0 (.step 11 (.close 4)) (.step 4 (.close 5))))) (.step 9 (.step 40 (.step 9 (.close 7))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 43 (.step 27 (.close 4)))) (.step 7 (.step 11 (.close 4)))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 68 (.step 27 (.step 53 (.step 4 (.step 7 (.close 9)))))) (.step 43 (.step 27 (.step 42 (.step 4 (.close 7)))))) (.step 53 (.step 4 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 43 (.step 27 (.close 4)))) (.step 7 (.step 11 (.close 4)))) (.step 7 (.step 11 (.close 4)))))) (.reuse 2)) (.reuse 3)) (.reuse 4)))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part24

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part24.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case13

namespace FiveColour.Packed.EnumerationChunks.Projected.Case13
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 257 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 257 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 257 0).upper i := by decide +kernel
lemma budget_model : (⟨10699377823114745129911, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487662666603259713959062043145214737994425041920, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 257), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨10699377823114745129911, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487662666603259713959062043145214737994425041920, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 257) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 257 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 257 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 257) (Archive.root 257) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 257 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 257 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case13

namespace FiveColour.Packed.EnumerationChunks.Case13
def root : Box := Archive.root 257
def families : Fin 78 → List Cut := Enumeration.families 257
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case13.original_covered points
end FiveColour.Packed.EnumerationChunks.Case13
