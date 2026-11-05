module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case200
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784575657165831645354346414080⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨10699377823114694798071, 5789234131009374248507341982684158351525473076195097263463908735304727765271163198607014520417109729396981796214162666810521916439567451338240667233911583614265164498419429981634595467193379621284503232172723970020313400320, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890272591473288407871200003580239051966391634314737483776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 39 0 (.split 43 0 (.split 42 0 (.step 68 (.close 4)) (.step 62 (.step 4 (.step 7 (.close 13))))) (.step 9 (.step 68 (.step 4 (.close 7))))) (.split 42 0 (.split 61 0 (.split 63 0 (.step 68 (.close 4)) (.step 27 (.step 52 (.step 4 (.close 19))))) (.step 52 (.step 40 (.step 11 (.close 35))))) (.step 62 (.step 4 (.step 7 (.close 9)))))) (.split 39 0 (.split 43 0 (.split 51 0 (.split 26 0 (.step 31 (.step 13 (.step 15 (.close 17)))) (.step 15 (.step 7 (.close 17)))) (.step 52 (.step 7 (.step 39 (.step 18 (.close 15)))))) (.step 9 (.step 7 (.step 52 (.step 29 (.close 5)))))) (.step 52 (.step 38 (.step 31 (.step 9 (.step 15 (.step 7 (.close 19))))))))) (.step 53 (.split 39 0 (.step 29 (.step 53 (.step 39 (.close 4)))) (.step 40 (.step 29 (.close 38)))))) (.split 35 0 (.step 53 (.split 39 0 (.step 7 (.step 53 (.step 43 (.step 9 (.step 13 (.close 15)))))) (.step 53 (.step 7 (.step 31 (.step 9 (.step 20 (.close 13)))))))) (.split 39 0 (.step 53 (.step 7 (.step 29 (.close 38)))) (.step 71 (.step 29 (.close 38)))))) (.split 30 0 (.split 39 0 (.step 68 (.step 52 (.step 43 (.step 53 (.step 4 (.close 7)))))) (.step 62 (.step 68 (.step 11 (.step 19 (.step 24 (.step 19 (.close 27)))))))) (.split 26 0 (.step 62 (.step 33 (.step 42 (.step 33 (.step 24 (.close 4)))))) (.step 7 (.step 19 (.close 20)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672046691162357192586156486781645594034176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 39 0 (.step 53 (.step 7 (.step 63 (.step 9 (.step 20 (.close 13)))))) (.step 68 (.step 27 (.step 42 (.close 4))))) (.step 53 (.close 7))) (.split 35 0 (.step 53 (.close 7)) (.split 39 0 (.step 53 (.step 4 (.close 7))) (.step 5 (.step 19 (.step 24 (.close 7))))))) (.split 26 0 (.split 30 0 (.step 62 (.split 34 0 (.step 24 (.step 42 (.step 11 (.step 4 (.close 13))))) (.step 17 (.step 24 (.close 19))))) (.step 24 (.step 33 (.step 24 (.step 11 (.close 13)))))) (.step 7 (.step 19 (.close 20))))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 24 (.step 42 (.step 18 (.step 9 (.step 13 (.close 19)))))) (.step 24 (.close 19))) (.step 24 (.step 33 (.step 20 (.close 4))))) (.step 7 (.step 19 (.close 20)))) (.step 24 (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.step 19 (.step 11 (.step 4 (.close 13))))) (.step 19 (.step 20 (.step 4 (.step 5 (.close 9)))))) (.step 19 (.step 20 (.step 19 (.step 4 (.close 9)))))) (.step 7 (.step 19 (.close 4))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050966428512363152317454099422595802512255614976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.step 52 (.split 30 0 (.split 34 0 (.step 52 (.step 63 (.step 9 (.step 19 (.step 20 (.close 38)))))) (.step 15 (.step 40 (.step 9 (.step 17 (.close 19)))))) (.step 52 (.step 42 (.step 13 (.step 43 (.close 11))))))) (.split 30 0 (.step 52 (.split 34 0 (.step 15 (.step 27 (.step 7 (.step 4 (.close 9))))) (.step 52 (.close 29)))) (.split 34 0 (.step 68 (.close 27)) (.step 4 (.step 7 (.step 15 (.close 17))))))) (.split 26 0 (.split 30 0 (.step 52 (.step 62 (.step 24 (.step 13 (.step 24 (.close 11)))))) (.step 24 (.split 34 0 (.step 42 (.step 13 (.step 24 (.step 11 (.step 17 (.close 18)))))) (.step 5 (.step 13 (.step 17 (.close 9))))))) (.split 30 0 (.split 34 0 (.step 27 (.step 4 (.close 7))) (.step 4 (.step 7 (.step 15 (.close 17))))) (.step 5 (.step 7 (.step 15 (.step 17 (.close 19)))))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 52 (.step 61 (.step 24 (.step 11 (.close 13))))) (.step 24 (.split 34 0 (.step 42 (.step 13 (.step 20 (.close 4)))) (.step 5 (.step 13 (.step 17 (.close 9))))))) (.split 30 0 (.split 34 0 (.step 27 (.step 4 (.close 7))) (.step 4 (.step 7 (.step 15 (.close 17))))) (.step 5 (.step 7 (.step 15 (.step 17 (.close 19))))))) (.step 24 (.split 26 0 (.split 34 0 (.step 11 (.step 17 (.step 20 (.step 13 (.step 4 (.close 19)))))) (.step 13 (.step 11 (.close 17)))) (.step 7 (.step 17 (.close 24))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065843266070521138932138878822168188157952⟩
def references : Fin 3 → Box := ![Part0.root, Part1.root, Part2.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 68 (.step 54 (.close 5))) (.step 42 (.step 43 (.step 42 (.step 4 (.step 9 (.close 13))))))) (.split 35 0 (.step 53 (.step 33 (.step 43 (.close 11)))) (.step 42 (.close 4)))) (.split 30 0 (.step 68 (.close 27)) (.step 7 (.step 19 (.close 20))))) (.split 26 0 (.split 30 0 (.step 62 (.split 34 0 (.step 24 (.step 61 (.step 4 (.step 9 (.close 11))))) (.step 17 (.step 24 (.close 19))))) (.step 24 (.step 33 (.step 20 (.close 4))))) (.step 7 (.step 19 (.close 20))))))) (.reuse 1)) (.split 16 0 (.reuse 2) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 42 (.step 24 (.step 42 (.step 27 (.step 17 (.step 4 (.close 13))))))) (.step 24 (.step 42 (.step 4 (.close 5))))) (.split 30 0 (.split 34 0 (.step 27 (.step 4 (.close 7))) (.step 4 (.step 7 (.step 15 (.close 17))))) (.step 5 (.step 7 (.step 15 (.step 17 (.close 19))))))) (.step 24 (.split 26 0 (.step 42 (.step 25 (.step 11 (.step 13 (.step 17 (.close 19)))))) (.step 7 (.step 17 (.close 19)))))) (.split 26 0 (.split 34 0 (.split 35 0 (.step 42 (.split 36 0 (.step 42 (.step 11 (.step 17 (.step 13 (.step 4 (.step 19 (.close 20))))))) (.step 13 (.step 11 (.step 17 (.step 5 (.step 19 (.close 20)))))))) (.step 11 (.step 17 (.close 19)))) (.step 13 (.step 17 (.close 16)))) (.step 7 (.step 17 (.step 19 (.step 24 (.close 19))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890272591473288407872529231576023967839295441375017828352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 61 0 (.step 9 (.split 63 0 (.step 57 (.step 67 (.close 4))) (.step 15 (.close 4)))) (.step 15 (.step 4 (.step 5 (.close 9))))) (.step 9 (.step 15 (.step 38 (.step 53 (.step 4 (.close 13))))))) (.step 9 (.step 15 (.close 4)))) (.step 53 (.split 35 0 (.split 39 0 (.step 9 (.step 13 (.step 15 (.step 18 (.step 15 (.close 20)))))) (.step 24 (.step 4 (.step 9 (.close 13))))) (.step 9 (.step 15 (.step 33 (.step 4 (.step 13 (.close 17))))))))) (.split 30 0 (.split 35 0 (.step 62 (.step 4 (.step 9 (.step 13 (.close 15))))) (.step 9 (.step 15 (.step 40 (.step 17 (.step 19 (.close 20))))))) (.step 24 (.step 4 (.step 9 (.step 13 (.close 15))))))) (.split 34 0 (.split 35 0 (.step 9 (.split 22 0 (.step 15 (.split 30 0 (.step 29 (.close 4)) (.step 38 (.step 7 (.step 4 (.close 17)))))) (.step 27 (.close 7)))) (.split 39 0 (.split 43 0 (.split 22 0 (.step 15 (.step 29 (.close 4))) (.step 27 (.step 15 (.step 7 (.step 4 (.close 17)))))) (.step 9 (.close 7))) (.step 9 (.step 27 (.step 15 (.step 27 (.step 4 (.close 7)))))))) (.step 15 (.close 7)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274088050965034715788245421158353668433163486364696576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 52 (.split 34 0 (.split 39 0 (.step 68 (.step 7 (.step 4 (.step 9 (.close 13))))) (.step 52 (.step 43 (.close 11)))) (.step 15 (.step 52 (.close 7))))) (.split 26 0 (.step 52 (.step 33 (.split 34 0 (.step 52 (.step 33 (.step 4 (.close 9)))) (.step 15 (.step 33 (.step 13 (.step 4 (.close 9)))))))) (.step 7 (.step 19 (.close 20))))) (.split 26 0 (.split 34 0 (.step 62 (.step 70 (.split 42 0 (.step 52 (.step 24 (.close 11))) (.step 43 (.close 5))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.step 7 (.step 19 (.close 20))))) (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 52 (.step 54 (.step 11 (.step 4 (.step 18 (.close 19)))))) (.step 43 (.step 13 (.step 24 (.close 4))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 24 (.split 35 0 (.step 13 (.step 17 (.step 20 (.step 24 (.close 11))))) (.step 17 (.step 19 (.step 13 (.step 19 (.close 20)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065843266071788789532367108223664891363328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 26 0 (.split 34 0 (.split 39 0 (.step 15 (.step 13 (.step 11 (.close 17)))) (.split 43 0 (.step 17 (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 11 (.close 13))))) (.step 15 (.close 13))) (.step 15 (.close 7)))) (.step 24 (.split 26 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15))) (.step 5 (.step 7 (.close 15)))))) (.split 22 0 (.step 24 (.split 26 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15))) (.step 5 (.step 7 (.close 15))))) (.step 7 (.step 13 (.close 15))))) (.split 17 0 (.split 22 0 (.step 24 (.split 26 0 (.split 34 0 (.split 35 0 (.step 13 (.step 4 (.step 9 (.close 15)))) (.step 5 (.step 15 (.close 13)))) (.step 13 (.close 15))) (.step 5 (.step 7 (.close 15))))) (.step 7 (.step 13 (.close 15)))) (.step 7 (.step 13 (.step 15 (.close 17)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784574448240012030725171707904⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 12 0 (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.step 53 (.split 30 0 (.step 52 (.step 24 (.step 4 (.step 5 (.close 11))))) (.step 33 (.step 13 (.step 24 (.close 11)))))) (.split 35 0 (.step 43 (.step 13 (.step 15 (.close 5)))) (.step 15 (.step 13 (.step 4 (.step 11 (.step 15 (.close 17)))))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.step 24 (.split 35 0 (.step 13 (.step 17 (.step 24 (.step 11 (.step 18 (.close 19)))))) (.step 17 (.step 19 (.step 13 (.step 4 (.close 9))))))))) (.step 7 (.split 22 0 (.step 24 (.split 35 0 (.step 13 (.step 17 (.step 20 (.step 19 (.close 4))))) (.step 17 (.step 19 (.step 13 (.step 4 (.close 9))))))) (.split 30 0 (.step 24 (.step 19 (.step 13 (.step 17 (.step 19 (.step 5 (.step 9 (.close 20)))))))) (.step 13 (.step 19 (.step 17 (.close 20)))))))))) (.reuse 1)) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 26 0 (.split 34 0 (.split 22 0 (.step 15 (.step 52 (.step 15 (.step 4 (.step 5 (.close 9)))))) (.step 24 (.close 13))) (.step 15 (.close 13))) (.step 15 (.close 7))) (.step 24 (.step 13 (.step 4 (.step 7 (.close 15)))))) (.step 24 (.split 17 0 (.step 24 (.step 13 (.step 4 (.step 7 (.close 15))))) (.step 7 (.step 13 (.close 15)))))) (.split 16 0 (.split 36 0 (.step 15 (.step 4 (.close 5))) (.step 13 (.close 15))) (.step 13 (.close 15))))))
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
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784574448240012030725171707904⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part7.root]
def proof : Chunks.Proof 3 := (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 68 (.split 61 0 (.step 27 (.step 4 (.step 17 (.step 15 (.close 19))))) (.step 4 (.close 5)))) (.step 9 (.step 15 (.step 40 (.step 17 (.step 19 (.close 20))))))) (.step 24 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.step 68 (.close 29))) (.step 24 (.step 4 (.step 15 (.step 7 (.step 9 (.step 13 (.step 19 (.close 20))))))))))) (.run (.split 26 0 (.split 30 0 (.split 17 0 (.split 22 0 (.step 53 (.step 43 (.step 27 (.step 4 (.step 13 (.close 15)))))) (.step 24 (.close 4))) (.step 24 (.close 4))) (.step 24 (.step 4 (.step 9 (.step 13 (.close 15)))))) (.split 17 0 (.step 68 (.close 29)) (.step 4 (.step 7 (.step 17 (.step 19 (.close 15))))))))) (.run (.split 16 0 (.split 17 0 (.step 15 (.split 26 0 (.step 52 (.step 24 (.step 15 (.step 4 (.step 5 (.close 9)))))) (.step 15 (.step 7 (.close 17))))) (.step 24 (.step 15 (.step 17 (.step 4 (.step 7 (.step 9 (.close 13)))))))) (.split 17 0 (.step 24 (.step 15 (.step 17 (.step 4 (.step 7 (.step 9 (.close 13))))))) (.step 13 (.step 15 (.close 17)))))))) (.reuse 2))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1208925819614630248448000, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512466672046691162357193795082306396274768740352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 39 0 (.step 63 (.close 9)) (.step 27 (.step 42 (.step 9 (.step 5 (.close 11)))))) (.step 9 (.step 52 (.step 7 (.close 9))))) (.step 9 (.step 42 (.step 9 (.close 4))))) (.split 35 0 (.step 53 (.close 7)) (.step 9 (.step 42 (.close 4))))) (.split 30 0 (.step 9 (.split 34 0 (.split 35 0 (.step 27 (.step 7 (.step 4 (.close 9)))) (.step 9 (.step 4 (.close 7)))) (.step 9 (.step 7 (.close 11))))) (.split 34 0 (.step 9 (.step 46 (.step 9 (.close 7)))) (.step 4 (.step 7 (.close 9)))))) (.split 26 0 (.split 30 0 (.step 62 (.split 39 0 (.step 7 (.step 4 (.close 9))) (.step 42 (.close 7)))) (.step 7 (.close 9))) (.split 30 0 (.split 34 0 (.step 9 (.step 11 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 9)))) (.step 5 (.step 7 (.close 9)))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 61 (.step 24 (.step 61 (.close 7)))) (.step 7 (.close 9))) (.split 30 0 (.split 34 0 (.step 9 (.step 11 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 9)))) (.step 5 (.step 7 (.close 9))))) (.step 7 (.close 9)))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 42 (.step 24 (.step 42 (.step 7 (.step 4 (.close 9)))))) (.step 7 (.close 9))) (.split 30 0 (.split 34 0 (.step 9 (.step 11 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 9)))) (.step 5 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 7 (.step 11 (.close 4))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1208925819614630248448000, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065843266070521140141064698436797362864128⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.split 35 0 (.step 11 (.close 4)) (.step 9 (.step 5 (.close 9))))) (.step 5 (.step 9 (.close 11))))) (.split 35 0 (.step 52 (.split 43 0 (.step 67 (.step 7 (.step 4 (.close 9)))) (.step 7 (.close 9)))) (.step 5 (.step 24 (.step 11 (.close 7)))))) (.split 34 0 (.split 30 0 (.step 9 (.step 11 (.step 5 (.step 7 (.close 9))))) (.step 5 (.step 11 (.close 7)))) (.step 5 (.step 11 (.close 7))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.step 11 (.close 4))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 4 (.close 5))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 61 (.step 11 (.step 5 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 4 (.close 5)))) (.step 7 (.close 11)))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 42 (.step 11 (.step 4 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 4 (.close 5)))) (.step 7 (.close 11))) (.step 7 (.close 11))))))
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
def root : Box := ⟨1267651809154049016126951653376, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784575657165831645354346414080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 26 0 (.split 35 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.step 7 (.step 4 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 16 0 (.split 17 0 (.step 24 (.step 15 (.step 9 (.step 24 (.step 4 (.close 7)))))) (.step 5 (.step 7 (.close 9)))) (.step 7 (.close 9)))) (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 9 (.step 52 (.step 7 (.step 4 (.close 9))))) (.step 7 (.close 9))) (.step 5 (.step 7 (.close 9)))) (.step 5 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 4 (.step 9 (.close 7))))) (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 9 (.step 46 (.step 9 (.close 7)))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 5 (.step 7 (.close 9)))) (.step 5 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 4 (.step 9 (.close 7))))) (.split 26 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.split 30 0 (.step 17 (.step 15 (.close 7))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 5 (.close 17))) (.step 5 (.step 11 (.close 7))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1073741824, 5783586108473076835780973348126786343074119910683107574151513744559940130933447660914570214420479527377891314500838455255137160115994090478859654413342048576060718044890274089512468065844595299784575657165831645354346414080⟩
def references : Fin 3 → Box := ![Part8.root, Part10.root, Part11.root]
def proof : Chunks.Proof 3 := (.split 8 0 (.reuse 0) (.split 10 0 (.split 12 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 26 0 (.split 34 0 (.step 9 (.step 24 (.step 9 (.step 5 (.close 9))))) (.step 15 (.step 24 (.step 9 (.close 4))))) (.step 9 (.step 7 (.close 4)))) (.step 24 (.step 9 (.step 23 (.step 9 (.close 7)))))) (.split 17 0 (.step 24 (.step 9 (.step 23 (.step 9 (.close 7))))) (.step 7 (.close 9)))) (.split 16 0 (.split 17 0 (.step 15 (.step 23 (.step 15 (.step 17 (.close 7))))) (.step 17 (.step 5 (.close 7)))) (.step 17 (.step 5 (.close 7))))))) (.reuse 2)))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case200
