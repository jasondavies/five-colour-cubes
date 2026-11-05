module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case219
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298520677406703664046859616256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11592891989185001204471, 5789234131009374248507341982684158351525473076195097263463908735304727765271163198607014520417109729396981796214162666810521916439567451338240667233911583614265164498419429981634596862352413225127988347882672294734774404096, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682190494784872458094036667452773681075780682174693376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 63 0 (.step 9 (.step 20 (.step 19 (.close 38)))) (.step 52 (.step 9 (.step 20 (.step 19 (.close 38)))))) (.step 52 (.step 9 (.step 15 (.step 20 (.step 19 (.close 38))))))) (.step 29 (.step 38 (.step 53 (.step 20 (.step 13 (.close 15))))))) (.split 35 0 (.step 53 (.step 38 (.step 9 (.step 20 (.close 13))))) (.step 38 (.step 9 (.close 13))))) (.split 34 0 (.split 36 0 (.split 30 0 (.step 9 (.step 27 (.step 7 (.close 29)))) (.step 38 (.step 9 (.step 27 (.close 7))))) (.step 29 (.close 7))) (.split 36 0 (.step 29 (.close 7)) (.step 7 (.close 29))))) (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 62 (.close 13)))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 17 (.step 24 (.step 19 (.close 20))))))) (.step 75 (.split 30 0 (.step 27 (.step 7 (.step 9 (.step 15 (.close 19))))) (.step 7 (.step 19 (.close 20))))))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 61 (.close 13)))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.close 13)))) (.step 43 (.step 17 (.step 24 (.step 19 (.close 20))))))) (.split 30 0 (.split 34 0 (.step 27 (.close 29)) (.step 7 (.step 15 (.step 17 (.close 19))))) (.step 7 (.step 24 (.close 27))))) (.split 26 0 (.step 24 (.split 34 0 (.step 61 (.step 24 (.step 11 (.close 13)))) (.step 17 (.step 24 (.close 20))))) (.step 7 (.step 24 (.close 27)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682190494786266254668944831399119663467821204768817152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.step 9 (.step 57 (.close 19)))) (.step 43 (.step 9 (.step 15 (.close 17)))))) (.split 34 0 (.step 42 (.step 43 (.step 11 (.step 24 (.step 15 (.close 13)))))) (.step 43 (.step 17 (.step 9 (.step 19 (.close 20))))))) (.split 30 0 (.split 34 0 (.step 27 (.step 15 (.close 29))) (.split 36 0 (.step 27 (.step 15 (.close 29))) (.step 7 (.step 27 (.step 15 (.close 17)))))) (.step 67 (.step 38 (.step 7 (.step 9 (.close 15))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 62 (.step 43 (.step 11 (.step 17 (.step 15 (.close 19)))))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.split 34 0 (.step 42 (.step 24 (.step 11 (.step 13 (.close 17))))) (.step 13 (.step 17 (.step 9 (.close 19))))))) (.step 11 (.step 75 (.step 24 (.step 17 (.step 27 (.close 7)))))))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 61 (.step 24 (.close 11))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.split 34 0 (.step 42 (.step 20 (.step 9 (.close 13)))) (.step 13 (.step 17 (.step 9 (.close 19))))))) (.step 11 (.step 74 (.step 24 (.step 17 (.step 7 (.close 15))))))) (.step 11 (.step 17 (.step 24 (.step 74 (.step 25 (.step 7 (.close 13))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903585571863035083952379750840860701360128⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 43 (.step 11 (.step 42 (.step 13 (.close 19))))) (.step 42 (.step 38 (.close 11)))) (.step 38 (.split 30 0 (.step 27 (.step 7 (.step 9 (.step 15 (.close 24))))) (.step 7 (.close 24))))) (.split 26 0 (.step 24 (.step 42 (.split 34 0 (.step 25 (.step 11 (.step 19 (.close 13)))) (.step 17 (.step 24 (.close 19)))))) (.step 7 (.step 24 (.close 27))))) (.split 22 0 (.split 26 0 (.step 24 (.step 42 (.split 34 0 (.step 42 (.step 19 (.step 9 (.step 13 (.close 20))))) (.step 17 (.step 24 (.close 19)))))) (.step 7 (.step 24 (.close 27)))) (.step 24 (.step 19 (.step 7 (.step 20 (.step 9 (.close 13)))))))))) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 42 (.step 24 (.step 11 (.close 15)))) (.step 17 (.step 9 (.close 19)))) (.step 24 (.step 42 (.close 13)))) (.step 11 (.step 38 (.step 24 (.step 17 (.step 27 (.close 7))))))) (.step 11 (.step 17 (.step 24 (.step 67 (.step 19 (.step 7 (.step 13 (.close 20))))))))) (.step 11 (.step 17 (.split 42 0 (.split 59 0 (.step 67 (.step 19 (.step 20 (.step 7 (.close 13))))) (.step 24 (.step 19 (.close 13)))) (.step 13 (.step 7 (.step 19 (.close 20)))))))))))
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
def root : Box := ⟨1329227995784915872903807061354086400, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956286509790326182866922522270262607398387580928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 16 0 (.split 22 0 (.split 39 0 (.step 29 (.split 35 0 (.step 66 (.step 43 (.step 15 (.step 20 (.step 13 (.close 17)))))) (.step 15 (.step 38 (.step 20 (.step 13 (.close 17))))))) (.step 9 (.step 38 (.step 66 (.step 24 (.step 15 (.step 17 (.step 19 (.close 20))))))))) (.split 17 0 (.step 62 (.step 29 (.step 66 (.close 24)))) (.step 17 (.close 24)))) (.split 34 0 (.split 36 0 (.split 22 0 (.step 53 (.step 9 (.step 17 (.close 24)))) (.step 17 (.close 24))) (.step 24 (.step 9 (.step 15 (.step 24 (.close 13)))))) (.step 38 (.step 24 (.step 9 (.close 13)))))) (.split 34 0 (.split 36 0 (.split 16 0 (.split 22 0 (.step 53 (.step 9 (.step 24 (.step 15 (.step 13 (.close 17)))))) (.step 24 (.step 9 (.step 15 (.step 13 (.step 19 (.close 20))))))) (.step 24 (.step 9 (.step 15 (.step 13 (.step 19 (.close 20))))))) (.step 38 (.step 43 (.step 15 (.step 9 (.step 13 (.step 24 (.close 33)))))))) (.step 38 (.step 15 (.step 13 (.step 33 (.step 9 (.close 15)))))))) (.split 43 0 (.split 54 0 (.split 16 0 (.split 22 0 (.split 30 0 (.step 29 (.close 7)) (.step 38 (.step 29 (.close 7)))) (.step 66 (.step 24 (.step 27 (.close 7))))) (.step 38 (.step 17 (.close 24)))) (.step 29 (.step 7 (.close 17)))) (.step 9 (.step 29 (.close 7))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410680693917109639410080705525781018417885095026548015104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 52 (.split 34 0 (.step 52 (.step 9 (.step 24 (.step 33 (.close 19))))) (.step 15 (.step 43 (.step 13 (.step 9 (.close 15))))))) (.split 34 0 (.split 35 0 (.step 52 (.step 33 (.step 9 (.close 20)))) (.step 42 (.step 13 (.step 9 (.close 33))))) (.step 15 (.split 35 0 (.step 33 (.step 13 (.step 15 (.close 9)))) (.step 15 (.step 13 (.close 17))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 52 (.step 9 (.step 24 (.step 27 (.close 7))))) (.step 7 (.step 24 (.close 29)))) (.step 7 (.close 15))) (.step 7 (.step 24 (.close 29))))) (.split 26 0 (.split 34 0 (.split 35 0 (.step 62 (.step 68 (.step 11 (.step 19 (.step 13 (.close 20)))))) (.step 42 (.step 43 (.step 19 (.step 13 (.close 24)))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.step 7 (.step 24 (.close 27))))) (.step 15 (.split 22 0 (.split 26 0 (.split 30 0 (.step 66 (.step 15 (.close 11))) (.split 34 0 (.step 42 (.step 13 (.step 9 (.close 15)))) (.step 13 (.close 15)))) (.step 15 (.step 7 (.close 17)))) (.step 17 (.step 7 (.close 13)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903585571864302734552607980242357404565504⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 24 (.step 42 (.step 13 (.step 11 (.step 19 (.close 20))))))) (.step 42 (.step 43 (.step 19 (.step 13 (.step 20 (.close 9))))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.step 15 (.step 17 (.close 13)))) (.step 7 (.step 17 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 24 (.split 35 0 (.step 25 (.step 11 (.step 13 (.close 19)))) (.step 19 (.step 13 (.step 20 (.close 9))))))))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 14 0 (.split 34 0 (.split 35 0 (.split 39 0 (.step 52 (.step 24 (.step 9 (.close 11)))) (.step 24 (.step 42 (.step 9 (.close 13))))) (.step 42 (.step 38 (.step 11 (.step 13 (.close 19)))))) (.step 15 (.step 17 (.step 13 (.step 9 (.close 15)))))) (.step 15 (.step 17 (.close 13)))) (.step 7 (.step 17 (.step 24 (.close 27))))) (.step 7 (.step 17 (.step 24 (.step 42 (.split 35 0 (.step 13 (.step 24 (.step 11 (.close 19)))) (.step 19 (.step 9 (.close 13))))))))) (.step 17 (.step 7 (.split 35 0 (.split 36 0 (.step 42 (.step 24 (.step 42 (.step 13 (.step 11 (.step 19 (.close 20))))))) (.step 13 (.step 20 (.close 9)))) (.step 19 (.step 9 (.step 13 (.close 20))))))))))
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
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410680693917109639411409932253916542988379115219299860480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 12 0 (.split 14 0 (.split 22 0 (.split 30 0 (.step 9 (.split 34 0 (.split 35 0 (.step 9 (.close 11)) (.step 9 (.close 7))) (.step 29 (.step 9 (.step 7 (.step 9 (.close 11))))))) (.split 34 0 (.step 42 (.step 9 (.step 7 (.close 9)))) (.step 7 (.close 9)))) (.split 43 0 (.split 30 0 (.split 39 0 (.step 75 (.step 9 (.close 7))) (.step 9 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11))))) (.split 43 0 (.split 22 0 (.split 30 0 (.split 39 0 (.split 36 0 (.step 9 (.step 7 (.step 9 (.close 11)))) (.step 57 (.step 17 (.step 9 (.close 7))))) (.step 9 (.step 11 (.close 7)))) (.split 34 0 (.split 39 0 (.step 67 (.step 9 (.close 7))) (.step 11 (.close 7))) (.step 7 (.step 9 (.close 11))))) (.step 11 (.close 7))) (.step 11 (.close 7)))) (.step 9 (.split 34 0 (.split 35 0 (.split 36 0 (.step 9 (.close 11)) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 9 (.step 7 (.close 11)))))) (.split 12 0 (.split 43 0 (.split 34 0 (.split 35 0 (.split 14 0 (.split 22 0 (.step 9 (.close 7)) (.step 11 (.close 7))) (.step 11 (.close 7))) (.step 29 (.step 7 (.close 9)))) (.step 29 (.close 7))) (.step 9 (.step 11 (.close 7)))) (.step 9 (.step 11 (.step 7 (.close 15)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298520677406703664046859616256⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 14 0 (.split 12 0 (.step 74 (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 29 (.close 7)))) (.step 7 (.close 11))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 43 0 (.split 14 0 (.split 12 0 (.step 67 (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 11 (.close 7))) (.step 7 (.step 11 (.close 7)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.step 29 (.close 7)))) (.step 7 (.close 11))) (.step 11 (.close 7))))) (.run (.split 12 0 (.split 16 0 (.split 26 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 52 (.step 7 (.close 9))) (.step 9 (.step 42 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 17 (.close 7))) (.split 14 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 43 0 (.step 43 (.step 29 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 7 (.step 9 (.close 11)))) (.step 11 (.close 7)))) (.step 7 (.close 11))) (.step 17 (.step 9 (.close 7))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605869459967413393176756323975220540839692494164013442047248757105290059378163443449117929573212623427845805999780164462155511410682191956287903586901092298520677406703664046859616256⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part5.root, Part7.root]
def proof : Chunks.Proof 4 := (.split 8 0 (.split 10 0 (.split 12 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 16 0 (.step 15 (.split 26 0 (.split 17 0 (.split 34 0 (.split 22 0 (.step 52 (.step 9 (.step 15 (.close 17)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.step 13 (.close 17)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.close 17)))) (.step 17 (.step 15 (.close 7))))))) (.split 12 0 (.reuse 2) (.run (.split 14 0 (.split 16 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 52 (.step 13 (.close 9)))) (.step 17 (.step 9 (.close 13)))) (.step 15 (.close 13))) (.step 15 (.step 13 (.close 17)))) (.step 15 (.step 7 (.close 17)))) (.step 17 (.step 15 (.step 13 (.step 7 (.close 15)))))) (.step 17 (.close 15)))))) (.reuse 3))
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
end FiveColour.Packed.ProjectedChunks.Case219
