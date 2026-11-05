module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case201
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435877942431820996935680⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨10699377823114745129911, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487662666603259713959062043145214737994425041920, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387624381372985387182259378493857973134160699037214668195461511904231424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 24 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 39 0 (.step 68 (.step 39 (.step 5 (.close 4)))) (.split 42 0 (.split 61 0 (.step 27 (.step 61 (.step 57 (.step 4 (.close 13))))) (.step 52 (.step 5 (.step 11 (.step 18 (.close 35)))))) (.step 62 (.step 5 (.step 9 (.close 13)))))) (.step 52 (.step 68 (.split 36 0 (.step 68 (.close 4)) (.step 15 (.step 31 (.step 9 (.step 19 (.close 20))))))))) (.step 53 (.step 68 (.step 29 (.step 38 (.step 39 (.close 4))))))) (.split 35 0 (.step 53 (.step 68 (.step 43 (.close 13)))) (.split 39 0 (.step 53 (.step 33 (.step 29 (.close 38)))) (.step 42 (.close 4))))) (.split 30 0 (.split 39 0 (.split 35 0 (.split 34 0 (.split 42 0 (.split 61 0 (.step 27 (.close 4)) (.step 52 (.step 5 (.step 7 (.step 11 (.close 27)))))) (.step 7 (.step 5 (.step 7 (.step 9 (.step 20 (.close 27))))))) (.step 9 (.step 24 (.step 40 (.step 15 (.step 7 (.close 17))))))) (.step 53 (.step 7 (.step 9 (.close 29))))) (.step 42 (.split 42 0 (.step 27 (.step 7 (.step 4 (.close 27)))) (.step 62 (.step 5 (.close 7)))))) (.split 35 0 (.split 43 0 (.step 42 (.step 7 (.step 4 (.step 15 (.close 20))))) (.step 7 (.step 9 (.step 7 (.close 27))))) (.step 42 (.close 4))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006683938242763996005043573793264261236812414976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 53 (.step 68 (.step 5 (.step 4 (.close 13))))) (.step 42 (.step 24 (.step 18 (.close 9))))) (.step 53 (.close 19))) (.split 35 0 (.step 53 (.close 19)) (.split 22 0 (.step 42 (.close 4)) (.step 24 (.close 19))))) (.split 30 0 (.step 42 (.split 35 0 (.step 7 (.step 9 (.step 7 (.step 4 (.step 15 (.close 20)))))) (.step 42 (.step 7 (.step 4 (.step 9 (.step 15 (.close 19)))))))) (.step 7 (.step 19 (.close 20))))) (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.step 24 (.step 42 (.step 18 (.step 9 (.step 13 (.close 19)))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.step 20 (.close 4))))) (.step 7 (.step 19 (.close 20)))) (.step 24 (.split 24 0 (.split 30 0 (.split 34 0 (.step 62 (.step 19 (.step 11 (.step 4 (.close 13))))) (.step 19 (.step 20 (.step 4 (.step 5 (.close 9)))))) (.step 19 (.step 20 (.step 19 (.step 4 (.close 9)))))) (.step 7 (.step 19 (.close 4))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097246545183694708435985965305087059373282103473995776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.step 52 (.split 30 0 (.split 34 0 (.step 52 (.step 63 (.step 9 (.step 19 (.step 20 (.close 38)))))) (.step 15 (.step 40 (.step 9 (.step 17 (.close 19)))))) (.step 52 (.step 42 (.step 13 (.step 43 (.close 11))))))) (.split 34 0 (.split 30 0 (.step 52 (.step 27 (.close 4))) (.step 42 (.step 24 (.step 27 (.step 4 (.close 5)))))) (.step 52 (.step 7 (.close 17))))) (.split 24 0 (.split 30 0 (.step 52 (.step 62 (.step 24 (.step 13 (.step 24 (.close 11)))))) (.step 24 (.split 34 0 (.step 42 (.step 13 (.step 24 (.step 11 (.step 17 (.close 18)))))) (.step 5 (.step 13 (.step 17 (.close 9))))))) (.split 30 0 (.split 35 0 (.step 27 (.step 4 (.close 7))) (.step 17 (.step 11 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 15 (.close 19))))))) (.split 22 0 (.split 24 0 (.split 30 0 (.step 52 (.step 61 (.step 24 (.step 11 (.close 13))))) (.step 24 (.split 34 0 (.step 42 (.step 13 (.step 20 (.close 4)))) (.step 5 (.step 13 (.step 17 (.close 9))))))) (.step 61 (.step 7 (.step 4 (.step 9 (.close 15)))))) (.step 24 (.split 24 0 (.split 34 0 (.step 11 (.step 17 (.step 20 (.step 13 (.step 4 (.close 19)))))) (.step 13 (.step 11 (.close 17)))) (.step 7 (.step 17 (.step 18 (.step 15 (.close 19))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332039338904168989919775656301759406538752⟩
def references : Fin 3 → Box := ![Part0.root, Part1.root, Part2.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 35 0 (.split 39 0 (.step 70 (.step 62 (.step 43 (.step 11 (.close 13))))) (.step 62 (.step 33 (.step 24 (.step 11 (.step 13 (.close 18))))))) (.split 17 0 (.step 62 (.step 68 (.close 19))) (.split 30 0 (.step 62 (.step 24 (.step 4 (.step 19 (.step 11 (.close 20)))))) (.step 24 (.step 19 (.close 20)))))) (.split 35 0 (.split 39 0 (.step 7 (.step 9 (.step 7 (.step 4 (.step 15 (.close 20)))))) (.split 17 0 (.step 27 (.step 4 (.close 5))) (.step 7 (.close 19)))) (.step 43 (.step 24 (.step 27 (.close 4)))))))) (.reuse 1)) (.split 16 0 (.reuse 2) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.step 42 (.step 24 (.step 42 (.step 27 (.step 17 (.step 4 (.close 13))))))) (.step 24 (.step 42 (.step 4 (.close 5))))) (.step 42 (.step 52 (.step 7 (.step 4 (.step 9 (.close 15))))))) (.step 24 (.step 42 (.split 24 0 (.step 25 (.step 11 (.step 13 (.step 17 (.close 19))))) (.step 7 (.step 15 (.close 17))))))) (.split 22 0 (.step 24 (.step 42 (.split 24 0 (.split 30 0 (.step 11 (.step 17 (.step 13 (.step 19 (.close 4))))) (.step 13 (.step 11 (.step 17 (.step 19 (.step 4 (.close 20))))))) (.step 7 (.step 15 (.close 17)))))) (.split 24 0 (.split 30 0 (.step 24 (.step 19 (.step 13 (.step 11 (.step 17 (.step 19 (.step 4 (.close 20)))))))) (.step 13 (.step 19 (.step 11 (.step 17 (.step 5 (.close 20))))))) (.step 7 (.step 17 (.step 19 (.close 4))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097246545182300913190305797143656949885048641160216576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 61 0 (.step 9 (.split 63 0 (.step 57 (.step 67 (.close 4))) (.step 15 (.close 4)))) (.step 15 (.step 4 (.step 5 (.close 9))))) (.step 9 (.step 15 (.step 38 (.step 53 (.step 4 (.close 13))))))) (.step 9 (.step 15 (.close 4)))) (.step 53 (.split 35 0 (.split 39 0 (.step 9 (.step 13 (.step 15 (.step 18 (.step 15 (.close 20)))))) (.step 24 (.step 4 (.step 9 (.close 13))))) (.step 9 (.step 15 (.step 33 (.step 4 (.step 13 (.close 17))))))))) (.step 9 (.split 30 0 (.split 35 0 (.split 42 0 (.split 34 0 (.split 61 0 (.step 29 (.close 4)) (.step 15 (.step 4 (.close 5)))) (.step 15 (.step 4 (.close 7)))) (.step 15 (.step 29 (.close 4)))) (.step 15 (.step 29 (.close 4)))) (.step 43 (.step 42 (.step 53 (.step 4 (.close 7)))))))) (.split 24 0 (.split 30 0 (.split 35 0 (.step 62 (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 9 (.step 15 (.step 40 (.step 17 (.step 19 (.close 20))))))) (.step 24 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 24 (.step 43 (.step 27 (.close 4)))))) (.split 24 0 (.split 30 0 (.split 22 0 (.split 35 0 (.step 68 (.split 61 0 (.step 27 (.step 4 (.step 17 (.step 15 (.close 19))))) (.step 4 (.close 5)))) (.step 9 (.step 15 (.step 40 (.step 17 (.step 19 (.close 20))))))) (.step 24 (.close 4))) (.step 24 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 24 (.step 43 (.step 27 (.close 4)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097246545182300911861079069009341305210643077583077376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.step 52 (.split 30 0 (.split 34 0 (.step 52 (.step 68 (.step 4 (.close 9)))) (.step 15 (.step 4 (.step 5 (.close 9))))) (.step 33 (.step 52 (.split 34 0 (.step 52 (.step 33 (.step 4 (.close 9)))) (.step 15 (.step 33 (.step 13 (.step 4 (.close 9)))))))))) (.split 34 0 (.split 43 0 (.split 30 0 (.step 52 (.step 7 (.step 4 (.close 19)))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 9 (.step 7 (.close 27))))) (.step 7 (.close 15)))) (.split 24 0 (.split 34 0 (.step 62 (.step 70 (.split 42 0 (.step 52 (.step 24 (.close 11))) (.step 43 (.close 5))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.step 7 (.step 19 (.close 20))))) (.split 22 0 (.split 24 0 (.split 34 0 (.split 35 0 (.step 52 (.step 54 (.step 11 (.step 4 (.step 18 (.close 19)))))) (.step 43 (.step 13 (.step 24 (.close 4))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 24 (.split 35 0 (.step 13 (.step 17 (.step 20 (.step 24 (.close 11))))) (.step 17 (.step 19 (.step 13 (.step 19 (.close 20)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332039338905436640520003885703256109744128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 24 0 (.split 34 0 (.split 39 0 (.step 15 (.step 13 (.step 11 (.close 17)))) (.split 43 0 (.step 17 (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 11 (.close 13))))) (.step 15 (.close 13))) (.split 34 0 (.split 43 0 (.split 50 0 (.step 17 (.step 7 (.step 4 (.close 15)))) (.step 15 (.step 7 (.close 17)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.close 15))))) (.step 24 (.split 24 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15))) (.step 7 (.step 15 (.close 17)))))) (.split 22 0 (.step 24 (.split 24 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15))) (.step 7 (.step 15 (.close 17))))) (.step 7 (.step 13 (.close 15))))) (.split 17 0 (.split 22 0 (.step 24 (.split 24 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15))) (.step 7 (.step 15 (.close 17))))) (.step 7 (.step 13 (.close 15)))) (.step 7 (.step 13 (.step 15 (.close 17)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435876789510316390088704⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 12 0 (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 34 0 (.step 53 (.split 30 0 (.step 52 (.step 24 (.step 4 (.step 5 (.close 11))))) (.step 33 (.step 13 (.step 24 (.close 11)))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 24 (.split 35 0 (.step 13 (.step 17 (.step 24 (.step 11 (.step 18 (.close 19)))))) (.step 17 (.step 19 (.step 13 (.step 4 (.close 9))))))))) (.step 7 (.split 22 0 (.step 24 (.split 35 0 (.step 13 (.step 17 (.step 20 (.step 19 (.close 4))))) (.step 17 (.step 19 (.step 13 (.step 4 (.close 9))))))) (.split 30 0 (.step 24 (.step 19 (.step 13 (.step 17 (.step 19 (.step 5 (.step 9 (.close 20)))))))) (.step 13 (.step 19 (.step 17 (.close 20)))))))))) (.reuse 1)) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 34 0 (.split 22 0 (.step 15 (.step 52 (.step 15 (.step 4 (.step 5 (.close 9)))))) (.step 24 (.close 13))) (.step 15 (.close 13))) (.step 15 (.step 24 (.step 9 (.step 43 (.step 15 (.step 5 (.step 7 (.close 17))))))))) (.step 24 (.close 13))) (.split 17 0 (.step 24 (.close 13)) (.step 7 (.step 13 (.step 15 (.close 17)))))) (.split 16 0 (.split 24 0 (.split 36 0 (.step 15 (.step 4 (.close 5))) (.step 13 (.close 15))) (.step 5 (.step 15 (.close 7)))) (.step 13 (.close 15))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1152921505680588800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006683938242763996005043573794417182741419261952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 61 0 (.step 9 (.step 7 (.close 4))) (.step 52 (.step 9 (.step 5 (.close 7))))) (.step 9 (.step 38 (.step 7 (.step 4 (.close 9)))))) (.step 9 (.step 15 (.step 43 (.close 7))))) (.step 53 (.split 35 0 (.step 7 (.step 4 (.step 7 (.close 9)))) (.step 9 (.step 7 (.step 4 (.close 9))))))) (.step 9 (.split 34 0 (.split 30 0 (.step 9 (.step 4 (.step 5 (.close 11)))) (.step 42 (.step 7 (.step 4 (.close 9))))) (.step 9 (.step 7 (.close 11)))))) (.split 24 0 (.split 30 0 (.split 35 0 (.step 62 (.step 4 (.close 7))) (.step 9 (.step 40 (.step 9 (.close 7))))) (.step 7 (.close 9))) (.step 24 (.step 43 (.close 27))))) (.split 24 0 (.split 30 0 (.split 22 0 (.split 35 0 (.step 68 (.step 27 (.step 11 (.close 4)))) (.step 9 (.step 40 (.step 9 (.close 7))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 24 (.step 43 (.close 27))))) (.split 24 0 (.split 30 0 (.split 17 0 (.split 22 0 (.step 53 (.step 7 (.step 4 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 7 (.step 11 (.close 4)))) (.step 7 (.close 9))) (.step 24 (.step 43 (.close 27))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1152921505680588800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668132164774835649713030324293730304⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 24 0 (.step 15 (.split 22 0 (.step 52 (.step 27 (.split 30 0 (.step 9 (.close 4)) (.step 4 (.close 9))))) (.step 23 (.step 11 (.close 7))))) (.step 52 (.step 9 (.step 11 (.close 4))))) (.step 24 (.step 27 (.step 15 (.step 11 (.close 4)))))) (.step 24 (.step 42 (.step 24 (.step 15 (.step 9 (.step 4 (.close 7)))))))))) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 30 0 (.step 15 (.step 9 (.step 11 (.step 4 (.close 9))))) (.split 34 0 (.split 35 0 (.split 22 0 (.step 9 (.step 7 (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 7 (.close 9)))) (.step 9 (.step 4 (.close 7)))) (.step 7 (.close 9)))) (.step 9 (.step 5 (.close 7)))) (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 22 0 (.step 9 (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 9)))) (.step 9 (.step 4 (.close 7)))) (.step 7 (.close 9))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 9 (.step 7 (.close 11)))))) (.split 24 0 (.split 30 0 (.step 15 (.close 4)) (.step 4 (.step 9 (.close 15)))) (.step 52 (.split 34 0 (.step 52 (.step 27 (.step 7 (.close 9)))) (.step 5 (.step 9 (.close 7)))))))))
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
def root : Box := ⟨1152921505680588800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435877942431820996935680⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.split 14 0 (.split 24 0 (.split 35 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 52 (.step 7 (.step 4 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 16 0 (.split 36 0 (.step 15 (.close 4)) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.split 12 0 (.split 16 0 (.split 36 0 (.split 39 0 (.split 42 0 (.step 52 (.step 7 (.step 4 (.close 9)))) (.step 7 (.close 9))) (.step 4 (.step 9 (.step 15 (.step 11 (.close 7)))))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 15 (.close 4)))) (.step 52 (.split 12 0 (.step 52 (.step 24 (.step 9 (.step 7 (.step 4 (.close 9)))))) (.step 4 (.step 9 (.close 7)))))) (.split 12 0 (.split 16 0 (.split 24 0 (.split 36 0 (.step 15 (.step 4 (.close 5))) (.step 7 (.close 9))) (.step 5 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 4 (.step 15 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859652560670387626066369652084097248006685332040668133432425435877942431820996935680⟩
def references : Fin 4 → Box := ![Part3.root, Part4.root, Part7.root, Part10.root]
def proof : Chunks.Proof 4 := (.split 6 0 (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.split 16 0 (.reuse 1) (.run (.split 24 0 (.split 30 0 (.split 17 0 (.split 22 0 (.step 53 (.step 43 (.step 27 (.step 4 (.step 13 (.close 15)))))) (.step 24 (.close 4))) (.step 24 (.close 4))) (.step 24 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 24 (.step 43 (.step 27 (.close 4))))))) (.run (.split 16 0 (.split 17 0 (.step 15 (.step 52 (.split 22 0 (.step 15 (.step 52 (.split 30 0 (.step 9 (.step 15 (.close 4))) (.step 42 (.step 7 (.step 4 (.step 9 (.close 13)))))))) (.step 23 (.step 15 (.step 17 (.step 9 (.close 13)))))))) (.step 24 (.step 15 (.step 17 (.close 5))))) (.step 24 (.step 42 (.step 15 (.step 17 (.close 4))))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part7.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part11.excludes
end FiveColour.Packed.ProjectedChunks.Case201
