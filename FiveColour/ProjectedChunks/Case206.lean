module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case206
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296365978192852270710784⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11592891989184984427175, 5789234131004114107589337099063798706207994136494267968630320216040438736791686334725463514473658914523947363325998255082438296860036168560471394733557376541140673600293513512804911129709412585432587090062323471997042951168, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265487995527790973921520564328392639197386883467313152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 63 0 (.step 9 (.step 20 (.step 7 (.close 27)))) (.step 52 (.step 9 (.step 20 (.step 7 (.close 27)))))) (.step 9 (.step 29 (.step 15 (.step 17 (.step 19 (.close 20))))))) (.step 29 (.step 38 (.step 20 (.step 13 (.close 15)))))) (.split 35 0 (.step 53 (.step 7 (.step 9 (.step 20 (.close 13))))) (.step 38 (.step 7 (.close 9))))) (.step 29 (.close 7))) (.split 24 0 (.split 26 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.step 75 (.close 7))) (.split 26 0 (.split 42 0 (.step 27 (.close 7)) (.step 7 (.step 19 (.close 20)))) (.step 11 (.step 27 (.close 7)))))) (.split 22 0 (.split 24 0 (.split 26 0 (.step 43 (.step 11 (.step 24 (.step 19 (.close 38))))) (.split 30 0 (.step 27 (.step 7 (.step 9 (.step 15 (.close 19))))) (.step 7 (.step 19 (.close 20))))) (.split 26 0 (.step 61 (.close 7)) (.step 11 (.step 27 (.close 7))))) (.step 24 (.split 24 0 (.split 26 0 (.step 25 (.step 11 (.step 19 (.close 13)))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 20))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822101399346931959571337872447061993979904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.step 52 (.split 30 0 (.step 15 (.step 9 (.step 43 (.close 38)))) (.step 42 (.step 13 (.step 9 (.step 20 (.close 17))))))) (.split 34 0 (.step 27 (.step 15 (.close 29))) (.step 43 (.step 17 (.close 27))))) (.split 26 0 (.split 30 0 (.step 27 (.close 7)) (.step 42 (.step 24 (.step 11 (.step 17 (.step 7 (.close 15))))))) (.step 11 (.step 27 (.close 7))))) (.split 24 0 (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 17 (.step 15 (.close 19))))) (.step 24 (.step 42 (.step 13 (.step 17 (.step 9 (.close 20))))))) (.step 11 (.step 24 (.step 17 (.step 27 (.close 7)))))) (.step 11 (.step 17 (.step 43 (.close 27)))))) (.split 22 0 (.split 24 0 (.step 74 (.split 26 0 (.step 52 (.step 24 (.step 11 (.close 13)))) (.step 11 (.step 24 (.step 17 (.step 24 (.step 15 (.close 7)))))))) (.step 11 (.step 17 (.step 43 (.close 27))))) (.step 11 (.step 17 (.step 24 (.step 74 (.step 25 (.close 7)))))))) (.split 17 0 (.split 22 0 (.split 24 0 (.step 67 (.split 26 0 (.step 42 (.step 15 (.close 24))) (.step 11 (.step 24 (.step 17 (.step 24 (.step 15 (.close 7)))))))) (.step 11 (.step 17 (.step 42 (.step 15 (.step 7 (.close 19))))))) (.step 11 (.step 17 (.step 24 (.step 42 (.step 19 (.step 25 (.close 7)))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 67 (.step 19 (.step 20 (.close 7)))) (.step 24 (.step 19 (.close 7)))) (.step 7 (.step 13 (.step 19 (.close 20))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927744487210776254122274324480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 29 (.split 35 0 (.split 36 0 (.step 66 (.step 24 (.step 13 (.step 15 (.close 17))))) (.step 15 (.step 24 (.step 13 (.close 17))))) (.step 15 (.step 38 (.step 13 (.close 19)))))) (.step 75 (.split 26 0 (.step 9 (.step 24 (.step 15 (.step 13 (.close 17))))) (.step 27 (.step 7 (.step 9 (.close 15))))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 9 (.step 43 (.step 17 (.step 15 (.close 19))))) (.step 24 (.step 9 (.step 13 (.close 15))))) (.step 29 (.close 7))) (.step 17 (.close 24)))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 22 0 (.step 9 (.step 17 (.step 24 (.step 15 (.step 19 (.step 20 (.close 27))))))) (.step 17 (.close 24))) (.step 24 (.step 9 (.step 15 (.step 24 (.close 7)))))) (.step 15 (.step 24 (.step 9 (.close 15))))) (.step 24 (.step 15 (.step 7 (.step 9 (.step 13 (.step 19 (.close 20))))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 22 0 (.step 9 (.step 29 (.close 7))) (.step 17 (.step 24 (.step 9 (.step 24 (.step 15 (.close 27))))))) (.step 29 (.close 7))) (.step 24 (.step 9 (.close 29)))) (.step 29 (.close 7)))) (.split 24 0 (.step 15 (.split 26 0 (.split 30 0 (.split 34 0 (.step 17 (.close 9)) (.step 15 (.close 13))) (.step 24 (.step 9 (.step 15 (.close 17))))) (.step 15 (.step 7 (.close 17))))) (.step 17 (.step 9 (.step 15 (.step 7 (.close 17))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740263991417852557925908188155006037147777300830649057280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 22 0 (.split 24 0 (.split 34 0 (.split 35 0 (.split 30 0 (.split 36 0 (.step 68 (.step 9 (.step 19 (.close 27)))) (.step 9 (.step 24 (.step 7 (.step 13 (.close 19)))))) (.step 53 (.close 7))) (.step 29 (.step 38 (.step 43 (.close 7))))) (.step 29 (.step 43 (.step 7 (.close 13))))) (.split 43 0 (.step 29 (.close 7)) (.step 7 (.close 9)))) (.split 24 0 (.split 26 0 (.split 34 0 (.step 62 (.step 43 (.close 7))) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 19 (.close 20)))) (.step 7 (.close 24)))) (.split 22 0 (.split 24 0 (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 52 (.close 19)))) (.split 34 0 (.step 42 (.step 27 (.step 24 (.close 7)))) (.step 7 (.step 13 (.close 17))))) (.step 27 (.close 7))) (.step 11 (.step 27 (.close 7)))) (.step 11 (.step 24 (.split 24 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 17 (.step 7 (.close 13))) (.step 19 (.step 7 (.close 13)))) (.step 7 (.step 13 (.close 17)))) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 17 (.step 19 (.close 15))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1100585369600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927744487210776255221785952256⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.split 12 0 (.reuse 0) (.run (.split 24 0 (.step 9 (.split 14 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 30 0 (.step 29 (.step 24 (.close 15))) (.step 38 (.step 29 (.step 24 (.close 7))))) (.step 29 (.step 15 (.step 37 (.step 7 (.close 19)))))) (.step 29 (.step 38 (.step 15 (.step 7 (.close 13)))))) (.step 15 (.step 29 (.step 37 (.close 7))))) (.step 24 (.step 7 (.step 13 (.close 15))))) (.step 15 (.step 24 (.step 43 (.step 15 (.step 7 (.close 13)))))))) (.step 29 (.close 7))))) (.run (.split 22 0 (.split 24 0 (.split 12 0 (.split 14 0 (.split 26 0 (.split 34 0 (.step 68 (.step 7 (.step 19 (.close 13)))) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 19 (.close 20)))) (.step 11 (.step 24 (.step 74 (.step 7 (.step 13 (.close 15))))))) (.step 9 (.step 24 (.step 7 (.step 13 (.close 15)))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 24 (.close 13)))))) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 12 0 (.split 14 0 (.split 26 0 (.split 34 0 (.step 53 (.step 43 (.close 7))) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 19 (.close 20)))) (.step 11 (.step 24 (.step 67 (.step 7 (.step 13 (.close 15))))))) (.step 9 (.step 24 (.step 7 (.step 13 (.close 15)))))) (.step 7 (.step 24 (.close 27)))) (.step 7 (.step 19 (.close 13)))) (.step 7 (.step 19 (.close 13))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547009841937229043349004251164114988510500316120026840124729318656966656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 4 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.step 52 (.split 39 0 (.step 29 (.step 15 (.step 24 (.step 13 (.close 33))))) (.step 38 (.step 33 (.step 9 (.step 15 (.step 13 (.close 19)))))))) (.split 34 0 (.split 30 0 (.step 29 (.close 7)) (.step 7 (.step 19 (.close 20)))) (.step 7 (.close 15)))) (.split 26 0 (.split 30 0 (.step 43 (.step 27 (.close 7))) (.step 7 (.step 19 (.close 20)))) (.split 30 0 (.step 27 (.step 7 (.step 9 (.step 15 (.close 19))))) (.step 7 (.close 24))))) (.step 15 (.split 24 0 (.step 66 (.step 15 (.step 11 (.step 15 (.close 7))))) (.step 17 (.close 7))))) (.step 15 (.step 52 (.step 9 (.step 29 (.step 13 (.close 15))))))) (.split 24 0 (.split 26 0 (.split 12 0 (.split 14 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.step 7 (.step 9 (.close 19)))) (.step 7 (.close 15)))) (.step 7 (.step 19 (.close 13)))) (.step 15 (.split 34 0 (.split 39 0 (.step 13 (.step 9 (.close 15))) (.step 11 (.step 17 (.close 7)))) (.step 7 (.step 13 (.close 15)))))) (.step 9 (.step 15 (.step 43 (.close 7))))) (.step 7 (.step 15 (.step 19 (.close 20))))) (.step 7 (.step 24 (.close 27))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265487995529184771825657991710254722722637062556614656⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 24 0 (.split 26 0 (.split 12 0 (.split 14 0 (.split 34 0 (.split 35 0 (.step 62 (.step 13 (.step 7 (.step 9 (.step 20 (.close 19)))))) (.step 42 (.step 43 (.close 7)))) (.step 7 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.step 15 (.step 17 (.step 7 (.step 9 (.close 13)))))) (.step 15 (.step 17 (.step 7 (.step 9 (.close 13)))))) (.step 7 (.step 15 (.step 19 (.close 20))))) (.step 7 (.step 17 (.close 24)))))) (.run (.split 22 0 (.split 24 0 (.split 26 0 (.split 12 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 13 (.step 7 (.step 9 (.close 20)))) (.step 24 (.step 13 (.step 7 (.step 11 (.step 19 (.close 20))))))) (.step 42 (.step 43 (.close 7)))) (.step 7 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.step 15 (.step 17 (.step 7 (.step 9 (.close 13)))))) (.step 15 (.step 17 (.step 7 (.step 9 (.close 13)))))) (.step 7 (.step 15 (.step 19 (.close 20))))) (.step 7 (.step 17 (.close 24)))) (.step 7 (.step 17 (.step 24 (.step 25 (.step 11 (.step 13 (.close 19))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195395087439005656718489157632⟩
def references : Fin 5 → Box := ![Part0.root, Part1.root, Part2.root, Part4.root, Part6.root]
def proof : Chunks.Proof 5 := (.split 10 0 (.split 4 0 (.split 12 0 (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.step 43 (.step 11 (.step 19 (.step 20 (.close 38))))) (.step 38 (.step 7 (.step 9 (.step 15 (.close 19)))))) (.step 42 (.step 24 (.step 9 (.step 17 (.step 19 (.close 27))))))) (.step 24 (.step 42 (.step 67 (.step 24 (.step 7 (.close 19))))))) (.step 24 (.split 24 0 (.split 26 0 (.step 42 (.split 34 0 (.step 19 (.step 11 (.close 20))) (.step 17 (.step 19 (.step 11 (.step 15 (.close 20))))))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 20)))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 16 0 (.reuse 4) (.run (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.split 12 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 13 (.step 7 (.step 9 (.step 19 (.close 20))))) (.step 24 (.step 13 (.step 7 (.step 11 (.close 19)))))) (.step 42 (.step 38 (.step 7 (.step 9 (.close 13)))))) (.step 7 (.step 15 (.step 17 (.step 9 (.close 13)))))) (.step 15 (.step 17 (.step 7 (.step 9 (.close 13)))))) (.step 15 (.step 17 (.step 7 (.step 9 (.close 13)))))) (.step 7 (.step 15 (.step 19 (.close 20))))) (.step 7 (.step 17 (.close 24)))) (.step 7 (.step 17 (.step 24 (.step 25 (.step 11 (.step 13 (.close 19)))))))) (.step 7 (.step 17 (.step 24 (.step 42 (.split 30 0 (.step 19 (.step 11 (.step 13 (.close 20)))) (.step 13 (.step 19 (.step 11 (.close 20)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part4.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927745696136595868751449030656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 24 0 (.split 12 0 (.split 14 0 (.split 22 0 (.split 34 0 (.step 9 (.split 35 0 (.step 11 (.step 7 (.close 9))) (.step 9 (.step 7 (.close 9))))) (.step 29 (.step 9 (.close 7)))) (.split 26 0 (.split 30 0 (.step 9 (.step 11 (.close 7))) (.step 7 (.close 9))) (.step 11 (.close 7)))) (.split 26 0 (.split 43 0 (.split 22 0 (.split 39 0 (.split 36 0 (.step 9 (.close 7)) (.step 57 (.step 17 (.step 7 (.close 9))))) (.step 9 (.step 11 (.close 7)))) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.step 9 (.split 26 0 (.split 34 0 (.split 35 0 (.step 9 (.close 7)) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 9 (.step 7 (.close 11)))))) (.step 9 (.split 14 0 (.split 26 0 (.split 22 0 (.split 34 0 (.step 27 (.close 7)) (.step 9 (.step 7 (.close 11)))) (.step 11 (.close 7))) (.step 9 (.close 11))) (.step 11 (.close 7))))) (.split 22 0 (.split 26 0 (.split 43 0 (.split 12 0 (.split 14 0 (.step 61 (.step 74 (.step 7 (.close 9)))) (.step 11 (.close 7))) (.step 9 (.step 17 (.step 9 (.close 7))))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 24 (.close 9)))) (.step 7 (.close 11)))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 43 0 (.split 12 0 (.split 14 0 (.step 42 (.step 67 (.close 9))) (.step 11 (.close 7))) (.step 9 (.step 17 (.step 9 (.close 7))))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 24 (.close 9)))) (.step 7 (.close 11))) (.step 11 (.close 7)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728574927744487211929175626881171456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.step 24 (.close 9))) (.step 62 (.step 29 (.step 24 (.close 9))))) (.step 24 (.split 30 0 (.step 9 (.step 11 (.close 7))) (.step 7 (.close 9))))) (.step 24 (.step 38 (.step 9 (.step 7 (.close 9)))))) (.split 34 0 (.step 27 (.step 29 (.close 7))) (.step 15 (.step 27 (.step 29 (.close 7)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 27 (.step 9 (.close 11))) (.step 29 (.close 7))) (.step 24 (.step 9 (.step 27 (.close 7))))) (.step 11 (.close 9)))) (.split 26 0 (.split 43 0 (.split 16 0 (.step 15 (.split 24 0 (.split 30 0 (.split 22 0 (.step 9 (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 24 (.step 9 (.step 24 (.close 9))))) (.step 9 (.step 11 (.close 7))))) (.step 11 (.close 7))) (.step 24 (.step 9 (.close 7)))) (.step 11 (.close 7)))) (.split 24 0 (.step 15 (.step 9 (.split 26 0 (.split 35 0 (.step 9 (.close 7)) (.step 9 (.close 7))) (.step 9 (.close 7))))) (.split 30 0 (.split 14 0 (.step 9 (.step 7 (.close 11))) (.step 11 (.close 9))) (.step 9 (.close 7))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1152921505680588800, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296365978192852270710784⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 4 0 (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 12 0 (.split 24 0 (.split 14 0 (.split 30 0 (.step 15 (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.close 11)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 15 (.close 7))) (.step 52 (.split 14 0 (.split 16 0 (.step 24 (.step 9 (.step 15 (.step 27 (.close 7))))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 7))))) (.split 14 0 (.split 30 0 (.step 9 (.step 15 (.close 7))) (.step 7 (.close 9))) (.step 15 (.close 7)))))) (.run (.split 10 0 (.split 24 0 (.split 26 0 (.split 43 0 (.split 12 0 (.split 14 0 (.step 9 (.split 34 0 (.step 11 (.close 7)) (.step 9 (.close 7)))) (.step 11 (.close 7))) (.step 9 (.close 11))) (.step 9 (.step 11 (.close 7)))) (.step 9 (.close 11))) (.step 11 (.close 9))) (.split 24 0 (.split 26 0 (.split 12 0 (.split 14 0 (.split 16 0 (.step 9 (.step 24 (.step 9 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 9 (.close 7)))))) (.run (.split 8 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 10 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 49 0 (.step 11 (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 11 (.step 9 (.close 7)))) (.step 11 (.close 7))) (.step 9 (.close 7)))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845806001547011526933895740265489457030822102728576195396296365978192852270710784⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part10.root]
def proof : Chunks.Proof 3 := (.split 6 0 (.split 8 0 (.reuse 0) (.split 4 0 (.split 10 0 (.reuse 1) (.run (.split 12 0 (.split 16 0 (.split 24 0 (.split 26 0 (.split 17 0 (.split 14 0 (.split 22 0 (.split 30 0 (.step 9 (.step 43 (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 15 (.step 17 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 66 (.split 17 0 (.split 22 0 (.split 30 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 17 (.split 26 0 (.split 17 0 (.step 9 (.split 22 0 (.split 49 0 (.step 68 (.step 9 (.close 7))) (.step 9 (.step 7 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 11)))) (.step 9 (.step 7 (.close 11)))))) (.step 7 (.close 11))) (.step 17 (.step 9 (.close 7)))))) (.run (.split 12 0 (.split 24 0 (.split 26 0 (.split 10 0 (.split 14 0 (.split 16 0 (.step 9 (.split 17 0 (.split 22 0 (.split 34 0 (.step 27 (.step 43 (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 11 (.close 7))) (.step 7 (.step 9 (.close 11)))) (.step 9 (.step 7 (.step 9 (.close 11))))) (.step 11 (.step 7 (.close 9)))) (.step 9 (.close 7)))))) (.reuse 2))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part11.excludes
end FiveColour.Packed.ProjectedChunks.Case206
