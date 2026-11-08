module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case26
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813225706412971961174874276258381824⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37630511536740859966407, 5789234131004108975754332037409142809267054969284561340134967070491198656929520178649377157723386516549331769084384324871873123416508784820466354286493168996104550163977995004790153775060025742547153916698520434934706865153, 0⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813224438762371732944346879648333824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.step 28 (.step 48 (.close 16))) (.step 7 (.step 10 (.step 7 (.step 4 (.step 7 (.close 16))))))) (.step 7 (.step 55 (.step 4 (.step 8 (.close 16)))))) (.step 7 (.split 22 0 (.step 55 (.step 4 (.step 8 (.close 16)))) (.split 38 0 (.step 20 (.step 23 (.step 20 (.step 4 (.close 8))))) (.step 19 (.step 20 (.step 5 (.step 8 (.close 16))))))))) (.step 7 (.split 17 0 (.split 22 0 (.step 55 (.step 4 (.step 8 (.close 16)))) (.split 38 0 (.step 23 (.step 25 (.close 4))) (.step 19 (.step 5 (.close 17))))) (.split 38 0 (.step 20 (.step 55 (.step 19 (.step 20 (.close 4))))) (.step 19 (.step 5 (.close 17))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 4 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 7 (.step 4 (.close 8)))) (.step 7 (.close 4))) (.step 7 (.step 13 (.step 4 (.step 8 (.step 14 (.close 19))))))) (.step 7 (.step 13 (.step 20 (.step 23 (.step 4 (.close 8))))))) (.step 13 (.step 7 (.split 38 0 (.split 36 0 (.step 19 (.step 4 (.step 8 (.close 14)))) (.step 20 (.step 4 (.close 8)))) (.step 4 (.step 8 (.step 14 (.close 19))))))))))
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
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813225706412971961174874276258381824⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.split 10 0 (.reuse 0) (.run (.step 7 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 28 (.step 16 (.step 4 (.close 13)))) (.step 13 (.step 16 (.step 28 (.step 4 (.close 33)))))) (.step 13 (.step 40 (.step 5 (.close 15))))) (.step 13 (.step 39 (.step 23 (.step 5 (.step 14 (.step 5 (.close 8)))))))) (.step 13 (.split 38 0 (.split 47 0 (.split 43 0 (.step 23 (.step 14 (.step 15 (.close 19)))) (.split 50 0 (.step 23 (.step 14 (.step 17 (.close 20)))) (.step 24 (.step 25 (.close 15))))) (.step 33 (.step 14 (.step 19 (.close 4))))) (.step 33 (.step 14 (.step 5 (.step 8 (.close 19)))))))) (.step 13 (.close 4)))))) (.run (.step 7 (.split 11 0 (.step 7 (.step 28 (.step 4 (.step 5 (.close 7))))) (.split 25 0 (.step 7 (.close 8)) (.split 16 0 (.step 7 (.step 4 (.step 7 (.close 8)))) (.step 7 (.close 8))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Case26
