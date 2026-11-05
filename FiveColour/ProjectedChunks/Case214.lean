module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case214
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813225706412971961174874276258381824⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨37630511536740859966407, 5789234131004108975754332037409142809267054969284561340134967070491198656929520178649377157723386516549331769084384324871873123416508784820466354286493168996104550163977995004790153775060025742547153916698520434934706865153, 0⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813225706412971961174874276258381824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 5 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.step 28 (.step 23 (.step 16 (.close 33)))) (.step 7 (.close 4))) (.step 7 (.step 23 (.step 5 (.step 4 (.close 8)))))) (.step 7 (.split 11 0 (.step 23 (.step 5 (.step 17 (.step 5 (.close 8))))) (.step 13 (.step 4 (.step 8 (.step 14 (.close 19)))))))) (.step 7 (.split 11 0 (.split 38 0 (.step 23 (.step 55 (.close 17))) (.step 23 (.step 5 (.step 8 (.close 19))))) (.step 13 (.step 19 (.step 4 (.step 8 (.close 14)))))))) (.step 7 (.step 13 (.split 16 0 (.split 17 0 (.step 55 (.step 13 (.close 16))) (.step 13 (.step 23 (.step 5 (.close 14))))) (.step 13 (.split 38 0 (.step 23 (.step 25 (.close 4))) (.step 19 (.step 4 (.close 5))))))))) (.step 7 (.close 4))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case214
