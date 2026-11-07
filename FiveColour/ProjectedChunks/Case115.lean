module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case115
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097865426944760507643113028527127628352305330343209552155942485835022954693662867456⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩]
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427455488602457974186977122378194942615406702098425214968038230594232515862196786164418624280820860798242385821696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 7 (.step 3 (.close 69))) (.split 10 0 (.split 34 0 (.step 77 (.close 3)) (.step 3 (.close 77))) (.step 3 (.close 77)))) (.step 69 (.split 10 0 (.step 29 (.step 69 (.split 14 0 (.step 75 (.close 3)) (.step 3 (.close 75))))) (.step 3 (.close 75))))) (.split 72 1 (.split 74 1 (.split 14 0 (.split 22 0 (.step 31 (.close 74)) (.step 18 (.close 31))) (.step 74 (.close 3))) (.step 74 (.close 3))) (.step 74 (.close 3)))) (.step 69 (.step 3 (.close 7)))) (.step 3 (.step 74 (.split 72 1 (.step 18 (.step 31 (.step 3 (.close 34)))) (.step 3 (.close 75)))))) (.step 69 (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 14 0 (.split 17 0 (.step 31 (.close 67)) (.step 18 (.close 31))) (.step 67 (.close 3))) (.step 67 (.close 3))) (.step 67 (.close 31))) (.step 67 (.close 3)))))) (.step 69 (.step 66 (.split 72 1 (.split 74 1 (.split 17 0 (.step 66 (.close 3)) (.step 18 (.close 66))) (.step 66 (.close 18))) (.step 66 (.close 3)))))) (.split 67 1 (.step 51 (.step 3 (.close 7))) (.step 3 (.close 7)))) (.split 51 1 (.split 67 1 (.step 47 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 46)))) (.step 7 (.step 75 (.split 63 1 (.split 64 1 (.split 71 1 (.step 31 (.close 7)) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66)))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097865426944760504273119695133294657940569128521623581534198472216018215855403827200⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 75 (.split 42 1 (.split 63 1 (.split 64 1 (.split 74 1 (.step 31 (.close 7)) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.step 7 (.close 39)))))))) (.run (.step 9 (.step 75 (.split 36 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 14 0 (.split 16 0 (.split 34 0 (.step 3 (.close 38)) (.step 31 (.close 3))) (.step 18 (.close 31))) (.step 40 (.step 38 (.close 18)))) (.step 29 (.close 38))) (.step 3 (.close 21))) (.step 3 (.close 21))) (.step 69 (.step 23 (.split 10 0 (.split 34 0 (.step 77 (.close 38)) (.step 17 (.step 31 (.close 38)))) (.step 3 (.close 77)))))) (.step 29 (.step 38 (.step 69 (.step 74 (.close 3)))))) (.step 3 (.step 38 (.close 74)))) (.step 21 (.step 67 (.close 31)))) (.step 29 (.step 38 (.step 51 (.step 66 (.close 3)))))) (.step 31 (.step 3 (.close 38)))) (.step 31 (.step 3 (.close 39)))))))) (.run (.step 7 (.step 75 (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 31 (.close 7)) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.step 7 (.close 37)))) (.step 7 (.step 31 (.close 37)))) (.step 29 (.step 31 (.step 37 (.close 3))))))))) (.run (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))) (.step 3 (.close 31)))))
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
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097865426944760507643113028527127628352305330343209549620641285378564151700256456704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 31 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 34 1 (.step 27 (.split 30 1 (.split 36 1 (.split 42 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 10 0 (.step 11 (.split 14 2 (.split 16 0 (.step 3 (.step 17 (.close 31))) (.step 17 (.step 3 (.close 17)))) (.step 17 (.step 3 (.close 31))))) (.step 3 (.close 17))) (.step 11 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.step 17 (.close 31)))) (.step 31 (.close 17))) (.step 3 (.close 17)))) (.step 31 (.close 17))) (.step 31 (.step 69 (.step 23 (.split 10 0 (.split 16 0 (.step 75 (.close 17)) (.step 3 (.step 17 (.close 38)))) (.step 3 (.close 75))))))) (.step 17 (.step 36 (.step 69 (.step 74 (.close 3)))))) (.step 3 (.step 17 (.close 74)))) (.step 11 (.step 17 (.step 67 (.close 3))))) (.step 34 (.step 66 (.close 17)))) (.step 31 (.step 66 (.step 67 (.step 74 (.step 75 (.step 77 (.split 16 0 (.step 40 (.split 17 0 (.split 22 0 (.step 38 (.close 17)) (.step 3 (.step 17 (.close 38)))) (.step 3 (.step 17 (.close 38))))) (.step 3 (.step 17 (.close 38))))))))))) (.step 11 (.step 17 (.step 3 (.close 18))))) (.step 17 (.step 18 (.step 3 (.close 20))))) (.step 17 (.step 18 (.step 3 (.close 19))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097865426944760507643113028527127628352305330343209552155942485835022954693662867456⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 77 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.close 7)) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 66 (.step 67 (.step 38 (.close 74)))))))))) (.run (.step 7 (.step 77 (.split 22 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 72 1 (.step 18 (.close 7)) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 67 (.step 38 (.close 74))))) (.step 18 (.step 7 (.close 20)))))))) (.run (.step 7 (.step 77 (.split 17 1 (.split 22 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.close 7)) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 38 (.step 66 (.close 67))))) (.step 18 (.step 7 (.close 19)))) (.step 7 (.step 18 (.close 19)))))))) (.reuse 1)) (.run (.split 14 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))) (.step 3 (.close 31))) (.step 3 (.close 17)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case115
