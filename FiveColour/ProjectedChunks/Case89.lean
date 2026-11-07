module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case89
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561985620297241790275433032890604203515029986169684971481199898063562242270237783113339390051486948237207924443023257437211928521454620016749357237875261433814481934417351357339009024⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨18741817655939024337635, 5789228615351851010618494880448709935079879776571393911013839255768432665236912487960502774861810452465697322629129481734798338504805576798767767746958544377551056015095924842852531572048546471937896452059573376945140794368, 0⟩]
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561985620297241790275433032890604203515029986169684971481199898063562242270237783113339390051486948237207924443023257437211928521454620016749357237875261433814481934417351357339009024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 1 (.split 8 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 7 (.step 5 (.step 3 (.close 5)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.close 31))) (.step 3 (.step 5 (.step 45 (.step 59 (.step 18 (.close 31))))))) (.step 7 (.step 31 (.close 39)))) (.step 7 (.step 31 (.step 37 (.step 7 (.close 41)))))) (.step 3 (.step 5 (.step 28 (.step 3 (.close 5)))))) (.step 18 (.close 7))) (.step 18 (.step 7 (.close 20)))) (.step 7 (.step 18 (.step 19 (.close 7))))) (.step 3 (.split 16 1 (.split 17 1 (.split 22 1 (.step 31 (.step 5 (.close 8))) (.step 5 (.step 11 (.step 17 (.step 3 (.close 18)))))) (.step 5 (.step 11 (.step 18 (.step 3 (.close 17)))))) (.step 18 (.step 17 (.step 3 (.close 19))))))) (.step 3 (.step 31 (.step 47 (.split 38 1 (.step 5 (.step 11 (.step 3 (.close 5)))) (.step 5 (.step 11 (.step 5 (.close 28))))))))) (.step 3 (.step 18 (.step 31 (.split 8 1 (.split 14 1 (.step 5 (.close 28)) (.step 5 (.close 8))) (.step 5 (.close 11))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case89
