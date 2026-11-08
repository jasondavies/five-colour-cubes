module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case170
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907325874679733835659797051151405482294297367215441433258863453815725693537334639298688838240867053521537857950810644588998014541240092122493056521533945616254991223914972053504⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨37630777495684390910951, 5789234131004114112605798393242650429804653116085229495907826956687667789266125362145452370754004878501022282187955398943580153440264784719876785736443695986532384820264588047565369261804881218339326414038357380245696283649, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907325874679733835659797051151405482294297367215441433258863453815725693537334639298688838240867053521537857950810644588998014541240092122493056521533945616254991223914972053504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.step 7 (.step 53 (.step 7 (.step 9 (.step 27 (.step 52 (.close 54))))))) (.split 50 1 (.step 7 (.close 52)) (.step 52 (.close 7)))) (.step 46 (.step 7 (.step 9 (.step 27 (.close 46)))))) (.step 7 (.close 52))) (.step 7 (.close 52))) (.step 7 (.step 37 (.step 45 (.step 52 (.close 37)))))) (.step 7 (.close 52))) (.step 7 (.step 52 (.close 53)))) (.step 7 (.step 19 (.step 25 (.step 52 (.step 53 (.close 19)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Case170
