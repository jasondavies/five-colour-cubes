module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784575657165831645354346414080⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨10699377823114694798071, 5789234131009374248507341982684158351525473076195097263463908735304727765271163198607014520417109729396981796214162666810521916439567451338240667233911583614265164498419429981634595467193379621284503232172723970020313400320, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048574375721378193357604306599964932473086477917525557605854245761843200⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 26 0 (.split 30 0 (.reuse 0) (.run (.split 35 0 (.step 53 (.split 39 0 (.split 42 0 (.step 53 (.step 68 (.step 4 (.close 9)))) (.step 62 (.step 33 (.step 9 (.step 4 (.close 13)))))) (.step 53 (.step 31 (.step 24 (.step 9 (.close 33))))))) (.split 39 0 (.step 53 (.step 68 (.step 9 (.step 18 (.close 33))))) (.split 43 0 (.step 42 (.close 4)) (.step 9 (.step 24 (.step 9 (.step 33 (.close 5)))))))))) (.run (.split 34 0 (.split 30 0 (.split 35 0 (.split 39 0 (.split 42 0 (.split 50 0 (.step 68 (.step 4 (.close 7))) (.step 53 (.step 9 (.step 29 (.close 4))))) (.step 62 (.step 7 (.close 4)))) (.split 42 0 (.step 27 (.step 9 (.step 38 (.step 4 (.close 7))))) (.step 9 (.step 43 (.step 27 (.step 7 (.step 21 (.step 7 (.close 24))))))))) (.step 53 (.split 39 0 (.step 29 (.close 4)) (.step 53 (.step 9 (.step 27 (.step 7 (.close 4)))))))) (.split 35 0 (.step 53 (.step 71 (.step 29 (.close 7)))) (.split 39 0 (.step 53 (.step 7 (.step 4 (.step 9 (.close 20))))) (.step 4 (.step 27 (.step 9 (.close 29))))))) (.split 35 0 (.split 30 0 (.step 15 (.step 52 (.split 36 0 (.step 7 (.step 5 (.step 7 (.step 9 (.step 19 (.close 27)))))) (.step 7 (.close 27))))) (.step 7 (.step 15 (.step 17 (.close 19))))) (.split 39 0 (.split 43 0 (.split 59 0 (.step 38 (.step 15 (.step 7 (.close 17)))) (.step 15 (.step 38 (.close 29)))) (.step 7 (.close 9))) (.step 38 (.close 4)))))))
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
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050965034715788244153507753440203761989661491200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 68 (.step 54 (.close 5))) (.step 61 (.step 68 (.step 5 (.close 13))))) (.step 68 (.step 38 (.step 24 (.close 13))))) (.split 34 0 (.split 35 0 (.step 53 (.step 42 (.step 54 (.step 4 (.step 9 (.close 11)))))) (.step 42 (.close 4))) (.split 35 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 13 (.step 15 (.close 17))))))) (.split 30 0 (.split 34 0 (.step 68 (.close 27)) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 24 (.close 27))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 61 (.step 4 (.step 9 (.close 11))))) (.step 24 (.step 11 (.step 19 (.close 20)))))) (.step 24 (.split 35 0 (.step 70 (.step 17 (.step 20 (.close 24)))) (.step 17 (.step 19 (.step 24 (.close 20))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 70 (.step 20 (.step 24 (.step 11 (.close 13)))))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.step 33 (.close 20)))))) (.step 7 (.step 24 (.step 4 (.close 27)))))))
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
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672046691162357192586156486781645594034176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 53 (.step 24 (.step 42 (.step 11 (.step 4 (.close 13))))))) (.step 53 (.step 5 (.close 19)))) (.step 24 (.split 35 0 (.split 36 0 (.step 24 (.close 13)) (.step 24 (.step 19 (.step 5 (.step 9 (.step 11 (.close 15))))))) (.step 17 (.step 19 (.step 4 (.step 19 (.close 4)))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 42 (.step 13 (.step 19 (.close 20))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.close 20)))))) (.step 7 (.step 24 (.step 4 (.close 27))))) (.split 26 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 24 (.step 42 (.step 11 (.step 18 (.step 13 (.close 18)))))) (.step 20 (.step 4 (.step 5 (.close 13))))) (.step 24 (.close 19))) (.step 24 (.step 19 (.close 20))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.close 19))) (.step 19 (.close 20))) (.step 19 (.step 4 (.close 13)))) (.step 19 (.step 20 (.step 17 (.step 4 (.step 9 (.close 15)))))))) (.step 7 (.step 19 (.step 23 (.step 19 (.step 20 (.close 24)))))))))
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672046691162357192586156486781645594034176⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 53 (.step 68 (.step 5 (.step 4 (.close 13))))) (.step 68 (.step 27 (.step 42 (.close 4))))) (.step 53 (.close 19))) (.split 35 0 (.step 53 (.close 19)) (.split 39 0 (.step 53 (.step 4 (.step 11 (.step 13 (.step 15 (.close 19)))))) (.step 5 (.step 19 (.step 24 (.close 19))))))) (.split 30 0 (.split 34 0 (.step 68 (.close 27)) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 24 (.close 27))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 42 (.step 53 (.step 4 (.step 9 (.close 11)))))) (.step 24 (.step 11 (.close 19))))) (.step 24 (.split 35 0 (.step 70 (.step 17 (.step 24 (.close 19)))) (.step 17 (.step 19 (.step 4 (.step 19 (.close 4)))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 42 (.step 13 (.step 19 (.close 20))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.step 24 (.close 14))))))) (.step 7 (.step 24 (.step 4 (.close 27))))))) (.reuse 0))
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
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048574375721378193357604306601358729047994641863871539997894768355966976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.step 52 (.split 34 0 (.split 39 0 (.split 35 0 (.step 52 (.step 63 (.step 9 (.close 20)))) (.step 15 (.step 40 (.step 9 (.step 19 (.step 20 (.close 38))))))) (.step 42 (.step 52 (.step 27 (.step 42 (.step 5 (.step 19 (.close 20)))))))) (.step 52 (.step 37 (.close 4))))) (.split 34 0 (.split 35 0 (.step 52 (.step 42 (.step 53 (.step 4 (.step 9 (.close 20)))))) (.step 42 (.close 4))) (.split 36 0 (.step 43 (.step 52 (.close 13))) (.step 13 (.step 38 (.step 24 (.step 31 (.step 9 (.close 33))))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 15 (.step 27 (.step 29 (.close 4)))) (.step 57 (.split 35 0 (.step 15 (.step 27 (.close 7))) (.step 29 (.step 4 (.close 7)))))) (.split 39 0 (.split 43 0 (.split 49 0 (.split 50 0 (.step 43 (.close 29)) (.step 15 (.step 27 (.step 7 (.close 27))))) (.step 15 (.step 27 (.step 29 (.close 4))))) (.step 4 (.step 7 (.close 9)))) (.step 38 (.step 5 (.step 11 (.step 17 (.close 7))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 15 (.step 27 (.step 7 (.step 4 (.step 9 (.close 17)))))) (.step 4 (.step 7 (.step 15 (.step 17 (.step 19 (.close 20))))))) (.step 4 (.step 38 (.close 7)))) (.step 7 (.step 17 (.close 15)))))))
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
def root : Box := ⟨1496577678020641163148737215047456204168198591873024, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050966428512363152317454099422595802512255614976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 61 (.step 52 (.step 24 (.step 61 (.step 4 (.close 9)))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 13 (.step 24 (.step 11 (.close 17))))) (.step 5 (.step 19 (.step 20 (.step 9 (.close 13)))))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.step 4 (.close 7))) (.step 4 (.step 11 (.step 38 (.step 24 (.step 27 (.close 7))))))) (.step 4 (.step 7 (.close 17)))) (.step 5 (.step 7 (.step 17 (.step 24 (.close 19))))))) (.split 26 0 (.split 30 0 (.step 24 (.split 34 0 (.step 61 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 20 (.step 11 (.step 17 (.step 4 (.close 19)))))))) (.step 7 (.step 17 (.step 24 (.close 19)))))))
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
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050966428512363152317454099422595802512255614976⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 52 (.step 11 (.step 4 (.close 19))))) (.step 42 (.step 11 (.step 17 (.step 13 (.step 4 (.step 19 (.close 20))))))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 62 (.step 70 (.step 42 (.step 13 (.step 24 (.step 11 (.close 17))))))) (.step 5 (.step 19 (.step 24 (.close 13))))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.step 4 (.close 7))) (.step 4 (.step 11 (.step 38 (.step 24 (.step 27 (.close 7))))))) (.step 4 (.step 7 (.close 17)))) (.step 5 (.step 7 (.step 17 (.step 24 (.close 19))))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890272592934791438998677829947870230665066694493264150528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 42 (.step 52 (.step 24 (.step 42 (.step 4 (.step 9 (.close 19))))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.step 42 (.step 4 (.close 5))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 27 (.step 4 (.close 7))) (.step 4 (.step 11 (.close 38)))) (.step 4 (.step 7 (.close 17)))) (.step 5 (.step 7 (.step 17 (.step 24 (.close 19))))))) (.split 26 0 (.split 30 0 (.step 24 (.split 34 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 19 (.step 24 (.step 25 (.step 11 (.step 5 (.close 17))))))))) (.step 7 (.step 17 (.step 24 (.close 19)))))))
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065843266070521138932138878822168188157952⟩
def references : Fin 5 → Box := ![Part1.root, Part2.root, Part4.root, Part7.root, Part8.root]
def proof : Chunks.Proof 5 := (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.split 39 0 (.split 35 0 (.step 62 (.step 63 (.step 9 (.step 13 (.step 15 (.close 17)))))) (.step 53 (.step 40 (.step 24 (.close 9))))) (.step 62 (.split 42 0 (.step 42 (.step 62 (.step 27 (.step 24 (.step 13 (.close 18)))))) (.step 5 (.step 24 (.close 19)))))) (.split 34 0 (.step 62 (.split 39 0 (.step 53 (.step 33 (.step 24 (.step 4 (.step 5 (.close 11)))))) (.step 24 (.step 33 (.close 19))))) (.split 35 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 13 (.step 15 (.close 17))))))) (.split 30 0 (.split 34 0 (.step 68 (.close 27)) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 24 (.close 27))))))) (.reuse 1)) (.reuse 2)) (.split 16 0 (.reuse 3) (.split 17 0 (.reuse 4) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.step 24 (.split 34 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 19 (.step 20 (.step 5 (.step 9 (.step 11 (.close 17))))))))) (.step 7 (.step 17 (.step 24 (.close 19))))) (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 20 (.step 4 (.close 13)))))) (.step 13 (.step 11 (.step 17 (.step 19 (.close 20))))))) (.step 13 (.step 19 (.step 5 (.step 11 (.step 17 (.close 20))))))) (.step 11 (.step 17 (.close 19)))) (.step 13 (.step 17 (.step 16 (.step 19 (.close 20)))))) (.step 11 (.step 17 (.step 19 (.step 7 (.close 15)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part4.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048574375721378193357604306599964933802314473702441430509661306042187776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 42 0 (.split 61 0 (.split 63 0 (.split 62 0 (.step 9 (.step 57 (.close 4))) (.step 53 (.step 9 (.step 4 (.step 5 (.close 13)))))) (.step 9 (.step 15 (.step 4 (.close 17))))) (.step 15 (.step 5 (.step 9 (.close 22))))) (.step 9 (.step 15 (.step 62 (.step 4 (.close 13)))))) (.step 9 (.step 15 (.step 4 (.close 13))))) (.step 9 (.step 15 (.step 53 (.step 38 (.step 20 (.step 4 (.close 13)))))))) (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 51 0 (.step 43 (.step 15 (.close 18))) (.step 18 (.step 15 (.step 20 (.step 24 (.close 33)))))) (.step 52 (.step 53 (.close 13)))) (.step 53 (.close 9))) (.step 43 (.step 42 (.step 24 (.step 4 (.close 52)))))) (.split 39 0 (.step 15 (.step 9 (.step 42 (.step 13 (.step 18 (.close 33)))))) (.step 4 (.step 9 (.close 38)))))) (.split 34 0 (.split 35 0 (.step 9 (.split 36 0 (.step 15 (.split 30 0 (.split 62 0 (.step 29 (.close 4)) (.step 40 (.step 53 (.step 29 (.close 4))))) (.step 53 (.step 7 (.step 4 (.close 17)))))) (.step 57 (.step 7 (.step 5 (.close 15)))))) (.split 39 0 (.split 43 0 (.split 49 0 (.split 59 0 (.step 29 (.close 4)) (.step 15 (.step 29 (.close 4)))) (.step 15 (.step 53 (.close 29)))) (.step 9 (.close 7))) (.step 9 (.step 38 (.close 4))))) (.step 15 (.step 7 (.close 27))))))
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
def root : Box := ⟨1496577676626845917468569053617346715934736278093824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050965034717117472149292669313107569049941835776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 68 (.split 61 0 (.split 63 0 (.step 61 (.step 68 (.step 4 (.close 5)))) (.step 4 (.step 9 (.step 15 (.step 13 (.step 17 (.close 19))))))) (.step 4 (.close 5)))) (.step 9 (.step 53 (.step 15 (.step 4 (.step 17 (.close 20))))))) (.step 15 (.step 24 (.step 15 (.step 4 (.step 9 (.close 13))))))) (.step 24 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 4 (.close 9))))) (.step 4 (.step 15 (.step 9 (.step 13 (.step 19 (.step 20 (.close 33)))))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 9 (.step 27 (.step 15 (.step 7 (.close 17))))) (.step 7 (.step 17 (.step 24 (.close 15))))) (.step 7 (.step 15 (.close 7)))) (.step 4 (.step 7 (.step 17 (.step 24 (.close 15))))))) (.step 24 (.split 26 0 (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.step 20 (.close 19)))))) (.step 13 (.close 24)))) (.step 4 (.step 7 (.step 15 (.step 17 (.close 19)))))))))
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
def root : Box := ⟨1461501637332232146199469748589186826717286629376, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672048020390352977502029390588705874378752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 68 (.step 53 (.step 68 (.step 4 (.close 5))))) (.step 43 (.step 27 (.step 42 (.step 4 (.close 13)))))) (.step 53 (.step 4 (.close 15)))) (.step 24 (.step 53 (.step 4 (.close 15))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 9 (.step 27 (.step 15 (.step 7 (.close 17))))) (.step 7 (.step 17 (.step 24 (.close 15))))) (.step 7 (.step 15 (.close 7)))) (.step 4 (.step 7 (.step 17 (.step 24 (.close 15))))))) (.step 24 (.split 26 0 (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.close 19))))) (.step 13 (.close 24)))) (.step 4 (.step 7 (.step 15 (.step 17 (.close 19)))))))) (.split 22 0 (.step 24 (.split 26 0 (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.close 19))))) (.step 13 (.close 24)))) (.step 4 (.step 7 (.step 15 (.step 17 (.close 19))))))) (.step 24 (.close 11)))))
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
def root : Box := ⟨1393797904136159731261855295847583948210176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595298516923848011782629228468502528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 26 0 (.split 22 0 (.step 15 (.step 52 (.split 30 0 (.step 15 (.step 4 (.step 5 (.close 9)))) (.step 42 (.close 13))))) (.step 24 (.step 15 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17))))))))))) (.step 15 (.step 24 (.step 15 (.close 17))))) (.split 22 0 (.step 24 (.step 15 (.split 26 0 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17)))))))) (.step 4 (.step 11 (.step 15 (.step 7 (.close 17)))))))) (.step 17 (.step 5 (.step 7 (.step 9 (.close 13))))))) (.split 17 0 (.split 22 0 (.step 24 (.step 15 (.split 26 0 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17)))))))) (.step 4 (.step 11 (.step 15 (.step 7 (.close 17)))))))) (.step 17 (.step 5 (.step 7 (.step 9 (.close 13)))))) (.step 17 (.step 7 (.close 13))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048574375721378193357604306599964932473087745568125785835255742465048576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.step 52 (.split 34 0 (.split 39 0 (.split 42 0 (.step 52 (.step 68 (.step 4 (.close 9)))) (.step 62 (.step 13 (.step 9 (.step 4 (.close 18)))))) (.step 52 (.split 35 0 (.step 31 (.step 9 (.step 19 (.close 20)))) (.step 24 (.step 4 (.step 9 (.close 33))))))) (.step 15 (.step 52 (.step 15 (.close 17)))))) (.split 34 0 (.split 35 0 (.step 52 (.step 33 (.step 9 (.step 4 (.close 20))))) (.split 39 0 (.step 52 (.close 33)) (.step 18 (.step 33 (.step 19 (.close 20)))))) (.split 35 0 (.step 52 (.close 13)) (.step 15 (.step 13 (.step 15 (.close 17))))))) (.split 35 0 (.split 43 0 (.split 34 0 (.split 39 0 (.step 52 (.step 7 (.step 4 (.close 20)))) (.split 30 0 (.step 43 (.step 27 (.step 4 (.step 7 (.close 24))))) (.step 7 (.step 19 (.step 20 (.step 19 (.close 24))))))) (.step 7 (.close 15))) (.step 7 (.step 9 (.step 46 (.close 9))))) (.split 34 0 (.split 30 0 (.split 36 0 (.step 52 (.step 53 (.step 7 (.step 4 (.step 9 (.close 20)))))) (.step 7 (.step 24 (.close 29)))) (.step 7 (.step 24 (.close 29)))) (.step 7 (.close 15))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050965034715788245421158353668433163486364696576⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 52 (.step 43 (.close 11))) (.step 24 (.step 70 (.step 42 (.step 13 (.step 4 (.close 9)))))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.step 70 (.step 62 (.step 33 (.step 13 (.step 4 (.step 11 (.step 19 (.close 20)))))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.step 7 (.step 24 (.close 27)))))) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 54 (.step 24 (.close 11)))) (.step 24 (.split 36 0 (.step 24 (.step 27 (.step 13 (.close 18)))) (.step 5 (.step 20 (.step 9 (.close 13))))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 33 (.step 4 (.step 9 (.close 20))))) (.step 13 (.step 24 (.step 4 (.step 9 (.close 33)))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 61 (.step 13 (.step 11 (.step 4 (.close 19))))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 23)))))) (.step 24 (.step 13 (.step 19 (.close 20))))) (.step 13 (.step 17 (.step 14 (.close 4)))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672046691163624843186384716183142297239552⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 52 (.step 53 (.step 63 (.step 9 (.step 19 (.close 20)))))) (.step 43 (.step 13 (.step 24 (.close 4))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.step 53 (.close 13)) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 42 (.step 13 (.step 4 (.close 9)))))) (.step 13 (.step 20 (.close 24)))) (.step 24 (.step 13 (.step 19 (.close 4))))) (.step 13 (.step 17 (.step 14 (.close 4))))))) (.step 7 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 30 0 (.step 24 (.step 13 (.step 11 (.step 19 (.close 13))))) (.step 13 (.step 24 (.step 11 (.close 19))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 23)))))) (.step 24 (.step 13 (.step 19 (.close 4))))) (.step 13 (.step 17 (.step 14 (.close 4))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 19 (.step 13 (.step 19 (.step 4 (.close 9))))))) (.step 13 (.step 19 (.close 20)))) (.step 19 (.step 4 (.close 13)))) (.step 13 (.step 14 (.close 17)))) (.step 13 (.step 19 (.step 20 (.step 9 (.close 15)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050966428512363153585104699650825204008958820352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 39 0 (.split 43 0 (.step 15 (.split 50 0 (.step 66 (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 13 (.close 17))))) (.split 50 0 (.split 51 0 (.step 15 (.close 11)) (.step 13 (.step 15 (.close 11)))) (.step 15 (.step 13 (.close 11))))) (.step 15 (.split 43 0 (.split 30 0 (.step 42 (.step 15 (.step 13 (.close 17)))) (.step 31 (.step 17 (.close 13)))) (.step 15 (.step 31 (.step 11 (.close 13))))))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 7 (.step 4 (.step 7 (.step 11 (.step 15 (.close 17)))))))) (.split 26 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 62 (.step 13 (.step 4 (.step 9 (.close 15))))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 5 (.step 7 (.step 15 (.close 17)))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.close 13)) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 5 (.step 7 (.step 15 (.close 17))))) (.step 7 (.step 13 (.step 15 (.close 17)))))))
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
def root : Box := ⟨1329229263435516101133208558057291776, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784574448240012030725171707904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 30 0 (.step 15 (.step 52 (.split 39 0 (.step 15 (.step 18 (.close 9))) (.step 43 (.step 15 (.step 5 (.step 9 (.close 17)))))))) (.split 35 0 (.step 52 (.step 15 (.step 13 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 9 (.step 15 (.close 17)))))))) (.step 15 (.close 13))) (.step 15 (.step 7 (.step 4 (.step 9 (.step 15 (.close 17))))))) (.step 24 (.split 26 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 7 (.close 15)))))) (.split 22 0 (.step 24 (.split 26 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 7 (.close 15))))) (.step 7 (.step 13 (.step 15 (.close 17)))))) (.split 17 0 (.split 22 0 (.step 24 (.split 26 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 4 (.step 7 (.close 15))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 7 (.step 13 (.close 17))))) (.split 16 0 (.split 17 0 (.split 36 0 (.step 15 (.step 4 (.close 5))) (.step 15 (.step 4 (.close 13)))) (.step 17 (.step 5 (.step 7 (.step 9 (.close 13)))))) (.step 17 (.step 5 (.step 7 (.step 9 (.close 13))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1208925819614630248448000, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048574375721378193357604306599964932473086477918734483425468874936549376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 35 0 (.split 39 0 (.split 42 0 (.split 34 0 (.split 50 0 (.step 63 (.close 9)) (.step 53 (.step 63 (.close 9)))) (.step 9 (.step 7 (.step 5 (.step 7 (.close 9)))))) (.step 62 (.step 7 (.close 4)))) (.split 42 0 (.split 34 0 (.step 27 (.step 42 (.step 68 (.step 9 (.close 5))))) (.step 9 (.step 5 (.close 7)))) (.step 9 (.step 5 (.close 7))))) (.step 9 (.split 34 0 (.step 42 (.step 53 (.step 7 (.step 4 (.close 9))))) (.step 9 (.step 7 (.step 15 (.close 11))))))) (.split 35 0 (.split 39 0 (.step 53 (.close 7)) (.split 43 0 (.step 42 (.step 5 (.close 7))) (.step 7 (.step 11 (.step 5 (.close 13)))))) (.split 34 0 (.step 9 (.step 42 (.close 4))) (.step 7 (.close 9))))) (.split 30 0 (.split 34 0 (.step 9 (.split 36 0 (.split 35 0 (.step 27 (.close 46)) (.step 9 (.step 4 (.close 7)))) (.step 9 (.step 7 (.step 5 (.step 9 (.close 11))))))) (.split 35 0 (.step 9 (.step 7 (.close 11))) (.step 29 (.close 4)))) (.split 34 0 (.split 35 0 (.step 9 (.step 46 (.step 9 (.close 7)))) (.step 4 (.step 29 (.close 7)))) (.step 7 (.step 9 (.close 11)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨1208925819614630248448000, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672046691162357193795082306396274768740352⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 62 (.step 7 (.close 5)))) (.step 42 (.step 7 (.step 9 (.close 5)))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 9 (.step 27 (.step 4 (.close 7)))) (.step 4 (.step 11 (.close 7)))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 7 (.step 9 (.close 11)))))))) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 61 (.step 68 (.step 61 (.step 7 (.step 4 (.close 9)))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 9 (.step 27 (.step 4 (.close 7)))) (.step 4 (.step 11 (.close 7)))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 7 (.step 9 (.close 11)))))) (.step 7 (.step 11 (.close 4)))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 42 (.step 53 (.step 7 (.step 9 (.close 5))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 9 (.step 27 (.step 4 (.close 7)))) (.step 4 (.step 11 (.close 7)))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 5 (.step 7 (.step 9 (.close 11)))))) (.step 7 (.step 11 (.close 4)))) (.step 7 (.step 11 (.close 4))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨1393796574908163947554908211655152842571776, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890272591473289801667774911744186606874603289466506313728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.step 52 (.split 26 0 (.step 68 (.step 9 (.close 5))) (.step 9 (.step 11 (.close 4))))) (.step 27 (.step 42 (.step 52 (.step 5 (.step 7 (.close 9))))))) (.split 26 0 (.split 39 0 (.step 15 (.step 5 (.step 9 (.close 7)))) (.step 9 (.step 11 (.step 5 (.close 7))))) (.step 5 (.step 11 (.close 7))))) (.split 36 0 (.split 26 0 (.step 52 (.close 11)) (.step 5 (.step 11 (.close 7)))) (.step 7 (.step 11 (.step 9 (.step 11 (.close 15))))))) (.split 34 0 (.split 36 0 (.split 35 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 39 0 (.step 24 (.step 11 (.close 4))) (.step 11 (.close 4))) (.step 27 (.step 42 (.step 24 (.step 48 (.step 9 (.close 7))))))) (.step 17 (.step 4 (.step 5 (.close 7))))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.step 42 (.close 11)))) (.step 5 (.step 7 (.close 11)))) (.step 7 (.close 11)))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 68 (.step 11 (.step 4 (.close 5))))) (.step 7 (.close 9))) (.split 36 0 (.step 11 (.step 4 (.step 5 (.close 7)))) (.step 4 (.step 7 (.step 9 (.close 11)))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 5 (.close 7))))))
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
def root : Box := ⟨1329227995786124798723421690528792576, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595298516925056937602243857643208704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 26 0 (.split 22 0 (.split 34 0 (.step 9 (.split 39 0 (.split 50 0 (.step 63 (.step 7 (.close 9))) (.step 9 (.step 5 (.close 10)))) (.step 9 (.step 5 (.close 7))))) (.step 15 (.split 35 0 (.step 43 (.close 9)) (.step 9 (.step 4 (.close 7)))))) (.step 24 (.split 34 0 (.step 9 (.step 24 (.step 9 (.step 5 (.close 7))))) (.step 4 (.step 7 (.step 9 (.close 7))))))) (.step 9 (.step 7 (.step 9 (.close 15))))) (.split 22 0 (.step 24 (.split 26 0 (.split 34 0 (.step 9 (.step 24 (.step 9 (.step 5 (.close 7))))) (.step 4 (.step 7 (.step 9 (.close 7))))) (.step 4 (.step 9 (.close 7))))) (.step 7 (.close 9)))) (.split 17 0 (.split 22 0 (.step 24 (.split 26 0 (.split 34 0 (.step 9 (.step 24 (.step 9 (.step 5 (.close 7))))) (.step 4 (.step 7 (.step 9 (.close 7))))) (.step 4 (.step 9 (.close 7))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 26 0 (.split 30 0 (.step 52 (.step 15 (.step 9 (.step 5 (.close 7))))) (.step 5 (.step 15 (.step 17 (.close 7))))) (.step 9 (.step 15 (.step 7 (.close 11)))))) (.step 17 (.step 5 (.close 7)))) (.step 17 (.step 5 (.close 7)))) (.step 17 (.step 5 (.close 7))))))
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
def root : Box := ⟨1267651809154049016126951653376, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672046691163624844395310535797771471945728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 35 0 (.split 43 0 (.split 51 0 (.split 61 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 52 (.step 9 (.step 7 (.step 4 (.close 9))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 5 (.step 7 (.close 11))))) (.step 7 (.step 52 (.step 7 (.close 9))))) (.step 7 (.step 27 (.step 7 (.step 9 (.step 5 (.close 10))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 9 (.split 36 0 (.step 42 (.step 7 (.step 4 (.close 9)))) (.step 4 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 5 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 9 (.step 46 (.step 9 (.close 7)))) (.step 4 (.step 29 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))))
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
def root : Box := ⟨1208925819614630248448000, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784575657165831645354346414080⟩
def references : Fin 4 → Box := ![Part20.root, Part21.root, Part22.root, Part23.root]
def proof : Chunks.Proof 4 := (.split 10 0 (.split 12 0 (.split 14 0 (.reuse 0) (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 26 0 (.split 30 0 (.split 22 0 (.split 34 0 (.step 61 (.split 35 0 (.step 52 (.step 7 (.step 4 (.close 9)))) (.step 11 (.step 4 (.close 7))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 11))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 5 (.close 7)))))) (.run (.split 17 0 (.split 26 0 (.split 30 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 42 (.step 24 (.step 11 (.step 4 (.close 5))))) (.split 36 0 (.step 11 (.step 4 (.step 5 (.close 7)))) (.step 4 (.step 7 (.step 9 (.close 11)))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 11))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 5 (.close 7)))) (.step 11 (.close 7)))))) (.reuse 2)) (.split 12 0 (.split 14 0 (.reuse 3) (.run (.split 16 0 (.split 26 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 15 (.split 34 0 (.split 39 0 (.split 43 0 (.step 17 (.step 7 (.step 4 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 17 (.close 7))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.step 11 (.close 7)))) (.step 7 (.close 11))))) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 15 (.step 9 (.step 43 (.step 24 (.step 9 (.step 5 (.step 7 (.step 5 (.close 10))))))))) (.step 7 (.close 9))) (.step 4 (.step 9 (.close 7)))) (.step 5 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 5 (.close 17))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784575657165831645354346414080⟩
def references : Fin 9 → Box := ![Part9.root, Part10.root, Part11.root, Part12.root, Part13.root, Part16.root, Part17.root, Part18.root, Part24.root]
def proof : Chunks.Proof 9 := (.split 8 0 (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.run (.split 26 0 (.split 30 0 (.split 39 0 (.split 42 0 (.step 68 (.step 62 (.step 4 (.step 9 (.close 13))))) (.step 15 (.step 9 (.step 18 (.step 24 (.close 13)))))) (.step 43 (.step 27 (.step 42 (.step 62 (.close 4)))))) (.step 24 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 4 (.close 9))))) (.step 4 (.step 15 (.step 9 (.step 13 (.step 19 (.step 20 (.close 33)))))))))) (.split 30 0 (.split 34 0 (.split 39 0 (.step 68 (.step 27 (.close 7))) (.step 4 (.step 9 (.step 17 (.step 27 (.close 7)))))) (.step 7 (.step 15 (.close 7)))) (.step 4 (.step 7 (.step 17 (.step 24 (.close 15))))))))) (.reuse 2)) (.reuse 3)) (.reuse 4))) (.split 12 0 (.split 14 0 (.reuse 5) (.split 16 0 (.reuse 6) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 39 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 17 (.step 13 (.close 11)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 5 (.step 7 (.step 15 (.close 17))))) (.step 7 (.step 13 (.step 15 (.close 17))))) (.step 13 (.step 7 (.close 17))))))) (.reuse 7))) (.reuse 8))
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
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part18.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part25

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part25.excludes
end FiveColour.Packed.EnumerationChunks.Case12
