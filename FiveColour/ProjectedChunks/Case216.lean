module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case216
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413524840649535549816918667904115097468928⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨10699377823114761907191, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646219954648068689896578978248292267480420713472, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115992053442883318074582352331628185222896545996906408376362082295779538512936498390929504206848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 0 (.split 34 0 (.split 39 0 (.split 42 0 (.split 36 0 (.step 68 (.step 4 (.close 5))) (.step 54 (.step 9 (.step 4 (.step 13 (.close 18)))))) (.step 62 (.step 9 (.step 4 (.step 13 (.close 18)))))) (.split 42 0 (.split 61 0 (.split 63 0 (.split 62 0 (.step 27 (.step 5 (.step 19 (.close 38)))) (.step 42 (.close 4))) (.step 27 (.step 52 (.step 57 (.step 4 (.close 35)))))) (.step 52 (.step 71 (.step 4 (.close 5))))) (.step 62 (.step 57 (.step 4 (.step 5 (.close 9))))))) (.split 39 0 (.split 43 0 (.split 50 0 (.split 51 0 (.step 68 (.step 15 (.step 4 (.step 5 (.close 17))))) (.step 52 (.step 39 (.step 18 (.step 4 (.close 15)))))) (.step 52 (.step 58 (.step 15 (.close 20))))) (.step 9 (.step 52 (.step 71 (.close 9))))) (.step 52 (.split 42 0 (.split 54 0 (.step 31 (.step 9 (.step 15 (.close 19)))) (.step 9 (.step 15 (.step 5 (.close 19))))) (.step 15 (.step 31 (.step 9 (.step 19 (.step 20 (.step 19 (.close 38))))))))))) (.step 53 (.split 39 0 (.split 43 0 (.split 51 0 (.split 58 0 (.step 68 (.step 15 (.step 18 (.step 5 (.close 17))))) (.step 40 (.step 24 (.step 15 (.step 17 (.close 39)))))) (.step 53 (.step 54 (.step 39 (.close 4))))) (.step 9 (.close 29))) (.step 53 (.step 9 (.step 38 (.close 4))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512452466762755551445353331214420645047507704663244800⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 22 0 (.split 30 0 (.reuse 0) (.run (.split 35 0 (.step 53 (.split 39 0 (.split 42 0 (.step 53 (.step 68 (.step 4 (.close 9)))) (.step 62 (.step 33 (.step 9 (.step 4 (.close 13)))))) (.step 53 (.step 31 (.step 24 (.step 9 (.close 33))))))) (.split 39 0 (.step 53 (.step 68 (.step 9 (.step 18 (.close 33))))) (.split 43 0 (.step 42 (.close 4)) (.step 9 (.step 24 (.step 9 (.step 33 (.close 5)))))))))) (.run (.split 30 0 (.split 39 0 (.split 35 0 (.step 62 (.step 63 (.step 9 (.step 13 (.step 15 (.close 17)))))) (.step 53 (.step 40 (.step 24 (.close 9))))) (.step 62 (.split 42 0 (.step 42 (.step 62 (.step 27 (.step 24 (.step 13 (.close 18)))))) (.step 5 (.step 24 (.close 19)))))) (.split 34 0 (.step 62 (.split 39 0 (.step 53 (.step 33 (.step 24 (.step 4 (.step 5 (.close 11)))))) (.step 24 (.step 33 (.close 19))))) (.split 35 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 13 (.step 15 (.close 17)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513949044439382396033593904483122118859635379587252224⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 68 (.step 54 (.close 5))) (.step 61 (.step 68 (.step 5 (.close 13))))) (.step 68 (.step 38 (.step 24 (.close 13))))) (.split 34 0 (.split 35 0 (.step 53 (.step 42 (.step 54 (.step 4 (.step 9 (.close 11)))))) (.step 42 (.close 4))) (.split 35 0 (.step 43 (.step 33 (.step 24 (.step 4 (.close 13))))) (.step 33 (.step 13 (.step 15 (.close 17))))))) (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 61 (.step 4 (.step 9 (.close 11))))) (.step 24 (.step 11 (.step 19 (.close 20)))))) (.step 24 (.split 35 0 (.step 70 (.step 17 (.step 20 (.close 24)))) (.step 17 (.step 19 (.step 24 (.close 20))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 70 (.step 20 (.step 24 (.step 11 (.close 13)))))) (.step 24 (.step 19 (.close 20)))) (.step 24 (.step 33 (.close 20)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019726936512108167954835142655035519795200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 42 (.step 53 (.step 24 (.step 42 (.step 11 (.step 4 (.close 13))))))) (.step 53 (.step 5 (.close 19)))) (.step 24 (.split 35 0 (.split 36 0 (.step 24 (.close 13)) (.step 24 (.step 19 (.step 5 (.step 9 (.step 11 (.close 15))))))) (.step 17 (.step 19 (.step 4 (.step 19 (.close 4)))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 42 (.step 13 (.step 19 (.close 20))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.close 20)))))) (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 36 0 (.step 24 (.step 42 (.step 11 (.step 18 (.step 13 (.close 18)))))) (.step 20 (.step 4 (.step 5 (.close 13))))) (.step 24 (.close 19))) (.step 24 (.step 19 (.close 20))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.step 13 (.close 19))) (.step 19 (.close 20))) (.step 19 (.step 4 (.close 13)))) (.step 19 (.step 20 (.step 17 (.step 4 (.step 9 (.close 15))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512452466764149348020261495160766627439548227257368576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.step 52 (.split 34 0 (.split 39 0 (.split 35 0 (.step 52 (.step 63 (.step 9 (.close 20)))) (.step 15 (.step 40 (.step 9 (.step 19 (.step 20 (.close 38))))))) (.step 42 (.step 52 (.step 27 (.step 42 (.step 5 (.step 19 (.close 20)))))))) (.step 52 (.step 37 (.close 4))))) (.split 34 0 (.split 35 0 (.step 52 (.step 42 (.step 53 (.step 4 (.step 9 (.close 20)))))) (.step 42 (.close 4))) (.split 36 0 (.step 43 (.step 52 (.close 13))) (.step 13 (.step 38 (.step 24 (.step 31 (.step 9 (.close 33))))))))) (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 52 (.step 11 (.step 4 (.close 19))))) (.step 42 (.step 11 (.step 17 (.step 13 (.step 4 (.step 19 (.close 20))))))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 62 (.step 70 (.step 42 (.step 13 (.step 24 (.step 11 (.close 17))))))) (.step 5 (.step 19 (.step 24 (.close 13))))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413523511420272114300817534695558113918976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 42 (.step 52 (.step 24 (.step 42 (.step 4 (.step 9 (.close 19))))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.step 42 (.step 4 (.close 5))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.step 24 (.split 34 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 19 (.step 24 (.step 25 (.step 11 (.step 5 (.close 17)))))))))) (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 19 (.step 20 (.step 5 (.step 9 (.step 11 (.close 17))))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 42 (.split 30 0 (.step 11 (.step 17 (.step 19 (.step 20 (.step 4 (.close 13)))))) (.step 13 (.step 11 (.step 17 (.step 19 (.close 20))))))) (.step 13 (.step 19 (.step 5 (.step 11 (.step 17 (.close 20))))))) (.step 11 (.step 17 (.close 19)))) (.step 13 (.step 17 (.step 16 (.step 19 (.close 20)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413523511420272114300817534695558113918976⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 4 := (.split 14 0 (.split 16 0 (.reuse 0) (.split 17 0 (.run (.split 22 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 53 (.step 68 (.step 5 (.step 4 (.close 13))))) (.step 68 (.step 27 (.step 42 (.close 4))))) (.step 53 (.close 19))) (.split 35 0 (.step 53 (.close 19)) (.split 39 0 (.step 53 (.step 4 (.step 11 (.step 13 (.step 15 (.close 19)))))) (.step 5 (.step 19 (.step 24 (.close 19))))))) (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 24 (.step 42 (.step 53 (.step 4 (.step 9 (.close 11)))))) (.step 24 (.step 11 (.close 19))))) (.step 24 (.split 35 0 (.step 70 (.step 17 (.step 24 (.close 19)))) (.step 17 (.step 19 (.step 4 (.step 19 (.close 4)))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 33 (.step 42 (.step 13 (.step 19 (.close 20))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.step 24 (.close 14))))))))) (.reuse 1))) (.split 16 0 (.split 17 0 (.reuse 2) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.step 61 (.step 52 (.step 24 (.step 61 (.step 4 (.close 9)))))) (.step 24 (.step 43 (.step 24 (.step 15 (.step 11 (.close 17))))))) (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.step 13 (.step 24 (.step 11 (.close 17))))) (.step 5 (.step 19 (.step 20 (.step 9 (.close 13)))))) (.step 13 (.step 5 (.step 17 (.step 9 (.close 19)))))))) (.split 30 0 (.step 24 (.split 34 0 (.step 61 (.step 11 (.step 17 (.step 13 (.step 5 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 24 (.step 20 (.step 11 (.step 17 (.step 4 (.close 19))))))))))) (.reuse 3)))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512452466762755552774581326999336517951314764943589376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 42 0 (.split 61 0 (.split 63 0 (.split 62 0 (.step 9 (.step 57 (.close 4))) (.step 53 (.step 9 (.step 4 (.step 5 (.close 13)))))) (.step 9 (.step 15 (.step 4 (.close 17))))) (.step 15 (.step 5 (.step 9 (.close 22))))) (.step 9 (.step 15 (.step 62 (.step 4 (.close 13)))))) (.step 9 (.step 15 (.step 4 (.close 13))))) (.step 9 (.step 15 (.step 53 (.step 38 (.step 20 (.step 4 (.close 13)))))))) (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 51 0 (.step 43 (.step 15 (.close 18))) (.step 18 (.step 15 (.step 20 (.step 24 (.close 33)))))) (.step 52 (.step 53 (.close 13)))) (.step 53 (.close 9))) (.step 43 (.step 42 (.step 24 (.step 4 (.close 52)))))) (.split 39 0 (.step 15 (.step 9 (.step 42 (.step 13 (.step 18 (.close 33)))))) (.step 4 (.step 9 (.close 38)))))) (.split 30 0 (.split 39 0 (.split 42 0 (.step 68 (.step 62 (.step 4 (.step 9 (.close 13))))) (.step 15 (.step 9 (.step 18 (.step 24 (.close 13)))))) (.step 43 (.step 27 (.step 42 (.step 62 (.close 4)))))) (.step 24 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 4 (.close 9))))) (.step 4 (.step 15 (.step 9 (.step 13 (.step 19 (.step 20 (.close 33))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019728265740103952870708046462095800139776⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 68 (.split 61 0 (.split 63 0 (.step 61 (.step 68 (.step 4 (.close 5)))) (.step 4 (.step 9 (.step 15 (.step 13 (.step 17 (.close 19))))))) (.step 4 (.close 5)))) (.step 9 (.step 53 (.step 15 (.step 4 (.step 17 (.close 20))))))) (.step 15 (.step 24 (.step 15 (.step 4 (.step 9 (.close 13))))))) (.step 24 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 4 (.close 9))))) (.step 4 (.step 15 (.step 9 (.step 13 (.step 19 (.step 20 (.close 33)))))))))) (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.step 20 (.close 19)))))) (.step 13 (.close 24))))))) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 68 (.step 53 (.step 68 (.step 4 (.close 5))))) (.step 43 (.step 27 (.step 42 (.step 4 (.close 13)))))) (.step 53 (.step 4 (.close 15)))) (.step 24 (.step 53 (.step 4 (.close 15))))) (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.close 19))))) (.step 13 (.close 24))))) (.step 24 (.split 22 0 (.step 24 (.split 34 0 (.step 18 (.step 9 (.step 15 (.step 13 (.close 19))))) (.step 13 (.close 24)))) (.step 23 (.step 17 (.close 24))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754512452466762755551445354598865020873276909201366450176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.step 52 (.split 34 0 (.split 39 0 (.split 42 0 (.step 52 (.step 68 (.step 4 (.close 9)))) (.step 62 (.step 13 (.step 9 (.step 4 (.close 18)))))) (.step 52 (.split 35 0 (.step 31 (.step 9 (.step 19 (.close 20)))) (.step 24 (.step 4 (.step 9 (.close 33))))))) (.step 15 (.step 52 (.step 15 (.close 17)))))) (.split 34 0 (.split 35 0 (.step 52 (.step 33 (.step 9 (.step 4 (.close 20))))) (.split 39 0 (.step 52 (.close 33)) (.step 18 (.step 33 (.step 19 (.close 20)))))) (.split 35 0 (.step 52 (.close 13)) (.step 15 (.step 13 (.step 15 (.close 17))))))) (.split 30 0 (.split 34 0 (.step 62 (.split 39 0 (.step 52 (.step 43 (.close 11))) (.step 24 (.step 70 (.step 42 (.step 13 (.step 4 (.close 9)))))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.step 70 (.step 62 (.step 33 (.step 13 (.step 4 (.step 11 (.step 19 (.close 20)))))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505941019726936513375818555063372056532223000576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 52 (.step 53 (.step 63 (.step 9 (.step 19 (.close 20)))))) (.step 43 (.step 13 (.step 24 (.close 4))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.step 53 (.close 13)) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 42 (.step 13 (.step 4 (.close 9)))))) (.step 13 (.step 20 (.close 24)))) (.step 24 (.step 13 (.step 19 (.close 4))))) (.step 13 (.step 17 (.step 14 (.close 4)))))) (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 30 0 (.step 24 (.step 13 (.step 11 (.step 19 (.close 13))))) (.step 13 (.step 24 (.step 11 (.close 19))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 23)))))) (.step 24 (.step 13 (.step 19 (.close 4))))) (.step 13 (.step 17 (.step 14 (.close 4))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 19 (.step 13 (.step 19 (.step 4 (.close 9))))))) (.step 13 (.step 19 (.close 20)))) (.step 19 (.step 4 (.close 13)))) (.step 13 (.step 14 (.close 17)))) (.step 13 (.step 19 (.step 20 (.step 9 (.close 15)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413523511421539764901045764097054817124352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 39 0 (.split 43 0 (.step 15 (.split 50 0 (.step 66 (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 13 (.close 17))))) (.split 50 0 (.split 51 0 (.step 15 (.close 11)) (.step 13 (.step 15 (.close 11)))) (.step 15 (.step 13 (.close 11))))) (.step 15 (.split 43 0 (.split 30 0 (.step 42 (.step 15 (.step 13 (.close 17)))) (.step 31 (.step 17 (.close 13)))) (.step 15 (.step 31 (.step 11 (.close 13))))))) (.step 15 (.step 13 (.close 17)))) (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 62 (.step 13 (.step 4 (.step 9 (.close 15))))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17))))) (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.step 61 (.close 13)) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17))))) (.split 17 0 (.split 22 0 (.split 30 0 (.step 24 (.split 34 0 (.split 35 0 (.split 39 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 17 (.step 13 (.close 11)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17)))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413523511421539764901045764097054817124352⟩
def references : Fin 3 → Box := ![Part9.root, Part10.root, Part11.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 39 0 (.step 52 (.step 54 (.step 24 (.close 11)))) (.step 24 (.split 36 0 (.step 24 (.step 27 (.step 13 (.close 18)))) (.step 5 (.step 20 (.step 9 (.close 13))))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 52 (.step 33 (.step 4 (.step 9 (.close 20))))) (.step 13 (.step 24 (.step 4 (.step 9 (.close 33)))))) (.step 33 (.step 13 (.close 19)))) (.step 13 (.step 33 (.step 15 (.close 4)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 70 (.step 24 (.step 61 (.step 13 (.step 11 (.step 4 (.close 19))))))) (.step 13 (.step 20 (.step 4 (.step 9 (.close 23)))))) (.step 24 (.step 13 (.step 19 (.close 20))))) (.step 13 (.step 17 (.step 14 (.close 4)))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560668620779001591267754513950505942413524840649535549816918667904115097468928⟩
def references : Fin 3 → Box := ![Part6.root, Part8.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.step 52 (.split 30 0 (.step 15 (.step 4 (.step 5 (.close 9)))) (.step 42 (.close 13))))) (.step 24 (.step 15 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17))))))))))) (.split 22 0 (.step 24 (.step 15 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17)))))))))) (.step 13 (.step 15 (.close 17))))) (.split 17 0 (.split 22 0 (.step 24 (.step 15 (.step 24 (.step 15 (.step 24 (.step 15 (.step 13 (.step 4 (.step 9 (.close 17)))))))))) (.step 13 (.step 15 (.close 17)))) (.step 13 (.close 17))))))) (.split 12 0 (.reuse 2) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.step 15 (.step 52 (.split 39 0 (.step 15 (.step 18 (.close 9))) (.step 43 (.step 15 (.step 5 (.step 9 (.close 17)))))))) (.split 35 0 (.step 52 (.step 15 (.step 13 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 9 (.step 15 (.close 17)))))))) (.step 15 (.close 13))) (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15))))))) (.step 24 (.split 22 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 13 (.close 15))))) (.split 17 0 (.step 24 (.split 22 0 (.step 24 (.step 13 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 13 (.close 15)))) (.step 13 (.close 17)))) (.split 16 0 (.split 17 0 (.split 36 0 (.step 15 (.step 4 (.close 5))) (.step 13 (.close 15))) (.step 13 (.close 15))) (.step 13 (.close 15)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part8.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case216
