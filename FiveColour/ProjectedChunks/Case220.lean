module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case220
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169782973925946370456118814450513510137856⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11592891989185051536311, 5789234131009374243490890256636772759901847847044975927221819681141912234360735955635684560038361693663553977767563026573470034338538450591010444121878566042502720243029128217487664061762293317802547158855163062708886045696, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505348989002138654166870315303761317853260273393074176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 63 0 (.step 9 (.step 20 (.step 19 (.close 38)))) (.step 52 (.step 9 (.step 20 (.step 19 (.close 38)))))) (.step 52 (.step 9 (.step 15 (.step 20 (.step 19 (.close 38))))))) (.step 29 (.step 38 (.step 53 (.step 20 (.step 13 (.close 15))))))) (.split 35 0 (.step 53 (.step 38 (.step 9 (.step 20 (.close 13))))) (.step 38 (.step 9 (.close 13))))) (.split 30 0 (.split 42 0 (.split 35 0 (.step 27 (.close 7)) (.step 29 (.step 7 (.close 9)))) (.step 62 (.step 29 (.close 7)))) (.step 42 (.step 43 (.step 11 (.step 24 (.step 20 (.close 27)))))))) (.split 24 0 (.split 30 0 (.step 43 (.step 11 (.step 62 (.close 13)))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 17 (.step 24 (.step 19 (.close 20))))))) (.split 30 0 (.split 42 0 (.step 27 (.close 7)) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 24 (.close 19)))))) (.split 22 0 (.split 24 0 (.split 30 0 (.step 43 (.step 11 (.step 61 (.close 13)))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 17 (.step 24 (.step 19 (.close 20))))))) (.split 30 0 (.split 39 0 (.step 43 (.step 11 (.close 27))) (.step 11 (.step 27 (.close 7)))) (.step 7 (.step 24 (.close 19))))) (.step 24 (.split 24 0 (.split 34 0 (.step 61 (.step 24 (.step 11 (.close 13)))) (.step 17 (.step 24 (.close 20)))) (.step 7 (.step 19 (.close 20))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505348989003532450741778479250107300245300795987197952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.step 9 (.step 57 (.close 19)))) (.step 43 (.step 9 (.step 15 (.close 17)))))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.step 24 (.step 15 (.close 13)))))) (.step 43 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.split 30 0 (.split 35 0 (.step 27 (.close 7)) (.step 42 (.step 15 (.step 9 (.step 27 (.close 7)))))) (.step 42 (.step 52 (.step 43 (.step 11 (.step 24 (.step 15 (.close 7))))))))) (.split 24 0 (.split 30 0 (.split 34 0 (.step 62 (.step 43 (.step 11 (.step 17 (.step 15 (.close 19)))))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.split 34 0 (.step 42 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 13 (.step 17 (.step 9 (.close 19))))))) (.step 11 (.step 17 (.split 42 0 (.split 30 0 (.step 27 (.close 7)) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 24 (.step 15 (.close 19))))))))) (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.step 61 (.step 24 (.close 11))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.split 34 0 (.step 42 (.step 20 (.step 9 (.close 13)))) (.step 13 (.step 17 (.step 9 (.close 19))))))) (.step 11 (.step 17 (.step 61 (.step 7 (.close 15)))))) (.step 11 (.step 17 (.split 42 0 (.step 61 (.step 24 (.step 61 (.step 25 (.step 7 (.close 13)))))) (.step 7 (.step 13 (.step 20 (.step 19 (.close 24)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644696682934940016528320451919740928⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.step 43 (.step 11 (.step 42 (.step 13 (.close 19))))) (.step 42 (.step 38 (.close 11)))) (.step 42 (.step 24 (.step 11 (.step 17 (.step 24 (.close 27))))))) (.step 24 (.step 42 (.split 24 0 (.split 34 0 (.step 25 (.step 11 (.step 19 (.close 13)))) (.step 17 (.step 24 (.close 19)))) (.step 7 (.step 19 (.close 20))))))) (.split 22 0 (.step 24 (.step 42 (.split 24 0 (.split 34 0 (.step 42 (.step 19 (.step 9 (.step 13 (.close 20))))) (.step 17 (.step 24 (.close 19)))) (.step 7 (.step 19 (.close 20)))))) (.split 24 0 (.step 19 (.step 20 (.step 9 (.step 13 (.step 15 (.close 17)))))) (.step 7 (.step 19 (.close 20)))))))) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 34 0 (.step 42 (.step 24 (.step 11 (.close 15)))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.step 42 (.close 13)))) (.step 11 (.step 17 (.step 42 (.step 15 (.step 7 (.close 19))))))) (.step 11 (.step 17 (.split 42 0 (.step 42 (.step 24 (.step 19 (.step 25 (.step 7 (.close 13)))))) (.step 7 (.step 13 (.step 19 (.step 20 (.close 24))))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.split 67 0 (.step 67 (.step 19 (.step 20 (.close 7)))) (.step 19 (.step 7 (.step 13 (.close 20))))) (.step 24 (.step 19 (.step 7 (.close 13))))) (.step 19 (.step 7 (.step 13 (.close 20)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450503775986399016514773509907040086989605961728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.step 9 (.split 35 0 (.split 36 0 (.step 66 (.step 77 (.step 13 (.close 15)))) (.step 15 (.step 43 (.step 17 (.close 13))))) (.step 15 (.step 38 (.step 20 (.step 13 (.close 17))))))) (.split 35 0 (.step 9 (.step 38 (.step 37 (.step 53 (.step 13 (.step 15 (.close 20))))))) (.step 38 (.close 9)))) (.step 9 (.step 29 (.close 7)))) (.split 24 0 (.split 39 0 (.step 75 (.step 68 (.step 9 (.step 15 (.step 17 (.close 24)))))) (.step 17 (.step 9 (.step 24 (.step 38 (.step 15 (.close 19))))))) (.step 9 (.step 17 (.step 24 (.close 29)))))) (.split 24 0 (.split 22 0 (.split 30 0 (.split 39 0 (.step 29 (.step 66 (.step 20 (.close 19)))) (.step 9 (.step 17 (.step 24 (.step 38 (.step 15 (.close 19))))))) (.step 24 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33))))))) (.step 17 (.close 24))) (.split 30 0 (.split 34 0 (.split 22 0 (.step 9 (.step 17 (.step 27 (.close 7)))) (.step 7 (.step 17 (.close 24)))) (.step 7 (.step 15 (.step 7 (.step 15 (.close 17)))))) (.step 7 (.step 17 (.close 24)))))) (.split 17 0 (.split 24 0 (.split 22 0 (.split 30 0 (.split 35 0 (.step 9 (.step 38 (.step 17 (.step 15 (.step 19 (.close 20)))))) (.step 38 (.close 9))) (.step 24 (.step 29 (.step 15 (.step 13 (.step 24 (.close 33))))))) (.step 17 (.close 24))) (.step 53 (.step 17 (.step 24 (.close 15))))) (.step 17 (.step 24 (.close 7))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604503852411326905606153539173632006054662574617766395904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 22 0 (.split 24 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.step 9 (.step 24 (.step 33 (.close 19))))) (.step 15 (.step 43 (.step 13 (.step 9 (.close 15))))))) (.split 34 0 (.split 35 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.step 42 (.step 13 (.step 9 (.close 33))))) (.step 15 (.split 35 0 (.step 33 (.step 13 (.step 15 (.close 9)))) (.step 15 (.step 13 (.close 17))))))) (.split 30 0 (.split 34 0 (.split 42 0 (.step 52 (.step 27 (.close 7))) (.step 7 (.step 24 (.close 19)))) (.step 7 (.step 15 (.close 17)))) (.step 7 (.step 24 (.close 19))))) (.split 24 0 (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 13 (.close 20)))))) (.step 42 (.step 43 (.step 19 (.step 13 (.close 24)))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.step 7 (.step 24 (.close 19))))) (.split 22 0 (.step 15 (.split 24 0 (.split 30 0 (.step 66 (.step 15 (.close 11))) (.split 34 0 (.step 42 (.step 13 (.step 9 (.close 15)))) (.step 13 (.close 15)))) (.step 17 (.close 7)))) (.step 17 (.step 15 (.step 7 (.close 11)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644697950585540244757721948622946304⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 24 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 24 (.step 42 (.step 13 (.step 11 (.step 19 (.close 20))))))) (.step 42 (.step 43 (.step 19 (.step 13 (.step 20 (.close 9))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.step 15 (.step 17 (.close 13)))) (.step 7 (.step 17 (.step 24 (.close 19))))) (.step 7 (.step 17 (.step 24 (.split 35 0 (.step 25 (.step 11 (.step 13 (.close 19)))) (.step 19 (.step 13 (.step 20 (.close 9))))))))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 24 (.step 42 (.step 9 (.close 13))))) (.step 42 (.step 38 (.step 11 (.step 13 (.close 19)))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.step 15 (.step 17 (.close 13)))) (.step 7 (.step 17 (.step 24 (.close 19))))) (.step 7 (.step 17 (.step 24 (.step 42 (.split 35 0 (.step 13 (.step 24 (.step 11 (.close 19)))) (.step 19 (.step 9 (.close 13))))))))) (.step 17 (.step 7 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 42 (.step 13 (.step 11 (.step 19 (.close 20))))))) (.step 13 (.step 20 (.close 9)))) (.step 19 (.step 9 (.step 13 (.close 20))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169781644696682934940017681241956526587904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 34 0 (.split 22 0 (.split 30 0 (.step 9 (.split 35 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 9 (.close 7)))) (.split 35 0 (.step 53 (.step 7 (.close 9))) (.step 38 (.close 7)))) (.split 17 0 (.step 62 (.split 39 0 (.step 29 (.step 24 (.close 9))) (.step 9 (.step 11 (.close 7))))) (.step 7 (.step 9 (.close 11))))) (.step 15 (.split 17 0 (.split 22 0 (.step 9 (.step 52 (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.split 30 0 (.split 34 0 (.split 22 0 (.step 9 (.step 27 (.step 7 (.close 9)))) (.step 11 (.step 7 (.close 9)))) (.step 43 (.step 27 (.close 9)))) (.step 53 (.step 9 (.step 24 (.step 27 (.close 7))))))) (.split 17 0 (.split 24 0 (.split 22 0 (.split 30 0 (.split 35 0 (.step 9 (.step 11 (.close 7))) (.step 38 (.close 7))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 7 (.close 9)))) (.step 7 (.close 11)))) (.split 24 0 (.split 43 0 (.split 16 0 (.step 15 (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.step 9 (.step 7 (.close 11))) (.step 42 (.step 9 (.close 7)))) (.step 52 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.step 11 (.close 7))) (.step 52 (.step 24 (.step 9 (.close 7))))) (.step 11 (.close 9)))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169782973925946370456118814450513510137856⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 24 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 49 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 9 (.close 11))) (.step 9 (.close 7))) (.step 9 (.close 11))) (.step 9 (.close 11))) (.split 34 0 (.step 9 (.split 35 0 (.split 16 0 (.step 15 (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 9 (.close 7)))) (.step 7 (.step 9 (.close 7))))) (.split 30 0 (.split 16 0 (.step 9 (.step 7 (.close 11))) (.step 29 (.close 9))) (.step 9 (.close 7)))) (.split 24 0 (.step 15 (.step 7 (.close 11))) (.step 29 (.close 9)))))) (.run (.split 12 0 (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.step 15 (.split 22 0 (.split 30 0 (.step 9 (.step 52 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.split 16 0 (.step 52 (.split 17 0 (.step 24 (.step 9 (.step 15 (.step 29 (.close 7))))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11))))) (.split 16 0 (.split 30 0 (.step 15 (.close 7)) (.step 7 (.close 11))) (.step 7 (.close 11)))) (.split 14 0 (.split 24 0 (.split 30 0 (.step 15 (.close 7)) (.step 7 (.close 9))) (.step 29 (.close 9))) (.step 15 (.close 7))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427843953328119214467807118604505350450505169782973925946370456118814450513510137856⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part5.root, Part7.root]
def proof : Chunks.Proof 4 := (.split 6 0 (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.step 15 (.split 24 0 (.split 34 0 (.split 22 0 (.step 52 (.step 9 (.step 15 (.close 17)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.step 13 (.close 17)))) (.step 9 (.step 17 (.step 7 (.close 15)))))) (.step 17 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.step 17 (.step 15 (.step 17 (.step 9 (.close 13))))))))) (.split 12 0 (.reuse 2) (.run (.split 14 0 (.split 16 0 (.split 24 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 13 (.close 9)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.close 13))) (.step 15 (.step 13 (.close 17)))) (.step 52 (.split 17 0 (.step 24 (.step 9 (.step 15 (.step 17 (.close 7))))) (.step 7 (.step 15 (.close 17)))))) (.step 17 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.step 17 (.close 15)))))) (.reuse 3))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case220
