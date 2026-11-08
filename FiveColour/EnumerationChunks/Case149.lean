module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case149
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021456981675107747125572707315812807960466904529286623087051983662682463608067571667840869786210641596556675732393964432097957696238546964614693828958307321528625225541877760⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908917104513533148135, 5789234131004114112605798393242650429804653116085229495907826956687667789262925569881378478716838741340481764996164168058096198318839850164380465265623768996171257991797277202683691464458712915539133314228167607251470648321, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021456981675107747125572707315812807960466904529286623087051983662682463608067571667840869786210641596556675732393964432097957696238546964614693828958307321528625225541877760⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 16 1 (.split 17 1 (.step 7 (.split 25 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.step 7 (.split 17 0 (.split 38 1 (.step 7 (.step 28 (.close 3))) (.step 28 (.step 7 (.step 22 (.close 38))))) (.step 7 (.step 28 (.close 38))))) (.step 7 (.close 10))) (.step 7 (.close 45))) (.step 7 (.close 39))) (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 7 (.split 56 1 (.step 7 (.step 29 (.step 3 (.close 7)))) (.step 28 (.step 3 (.step 22 (.close 38)))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 29 (.step 7 (.step 26 (.close 38)))))) (.step 3 (.step 28 (.close 38)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7))))))) (.step 7 (.step 37 (.step 7 (.step 22 (.close 28)))))) (.step 28 (.step 29 (.step 7 (.step 22 (.close 28)))))) (.step 28 (.step 7 (.step 22 (.close 28)))))) (.step 7 (.split 25 1 (.step 5 (.step 4 (.close 29))) (.step 3 (.step 5 (.close 28)))))) (.step 7 (.split 25 1 (.split 26 1 (.step 7 (.close 19)) (.step 3 (.step 4 (.step 19 (.close 29))))) (.step 3 (.step 5 (.step 19 (.close 28)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Case149
