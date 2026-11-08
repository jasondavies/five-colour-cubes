module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case37
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423277128847227091184193542275961310808171872256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨18740915245514456087283, 5789228615357111146520043253955950924962759905236944250816662429627930946143177890630323431728858874565283113377443026906005086448749057136295994626906708871240422740574967198931403751522663329691581331687037538719964857344, 0⟩]
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
def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423277128847227089916541733121912294682293960704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.split 34 0 (.step 43 (.step 33 (.close 5))) (.step 52 (.step 43 (.close 28)))) (.step 52 (.step 24 (.close 5)))) (.split 38 0 (.step 62 (.step 24 (.close 33))) (.step 5 (.step 24 (.step 33 (.close 5)))))) (.split 22 0 (.split 38 0 (.step 54 (.step 24 (.close 11))) (.step 5 (.step 24 (.step 33 (.close 5))))) (.split 38 0 (.step 70 (.step 20 (.step 24 (.close 11)))) (.step 19 (.step 33 (.step 5 (.step 20 (.close 5)))))))) (.split 17 0 (.split 22 0 (.split 38 0 (.step 53 (.close 24)) (.step 5 (.step 24 (.step 33 (.close 5))))) (.split 38 0 (.step 70 (.step 42 (.close 24))) (.step 19 (.step 23 (.close 11))))) (.split 22 0 (.split 38 0 (.split 39 0 (.step 53 (.close 20)) (.step 19 (.close 20))) (.step 19 (.step 23 (.close 11)))) (.step 19 (.step 20 (.step 11 (.close 17))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709304279539078337391387595286117423277128847227091184193542275961310808171872256⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.step 52 (.step 43 (.close 33))) (.step 13 (.step 15 (.step 13 (.close 11))))) (.step 13 (.step 70 (.step 43 (.close 11))))) (.step 13 (.split 38 0 (.split 39 0 (.step 54 (.step 17 (.step 5 (.close 11)))) (.step 33 (.step 17 (.step 11 (.step 5 (.close 20)))))) (.step 33 (.step 5 (.step 14 (.step 5 (.close 11)))))))) (.split 14 0 (.step 13 (.split 38 0 (.split 39 0 (.split 50 0 (.split 34 0 (.step 20 (.step 5 (.close 11))) (.split 36 0 (.step 14 (.close 17)) (.step 20 (.step 15 (.step 14 (.step 17 (.close 38))))))) (.step 33 (.step 24 (.step 25 (.close 15))))) (.step 33 (.step 17 (.step 19 (.close 5))))) (.step 33 (.split 34 0 (.step 24 (.step 5 (.close 19))) (.step 14 (.close 5)))))) (.step 13 (.close 17)))))) (.run (.step 7 (.split 14 0 (.step 7 (.split 34 0 (.step 7 (.close 5)) (.step 7 (.close 5)))) (.split 16 0 (.step 7 (.step 52 (.step 7 (.close 5)))) (.step 7 (.close 11)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Case37
