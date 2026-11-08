module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case165
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581034647693109995948679302381139345918350729549015981121540317608631936850967134208⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908989162382482537447, 5789234131004114112605798393242650429804653116085229495907826956687667789266122240396902054761773496903789967293253081098767902610547516371633635263202584673723359761206532767663752339810506252854686049505762319230327325697, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581034647693109995948679302381139345918350729549015981121540317608631936850967134208⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 34 1 (.step 7 (.split 36 1 (.split 42 1 (.step 7 (.close 9)) (.step 7 (.close 29))) (.step 7 (.step 29 (.step 7 (.close 38)))))) (.step 7 (.step 37 (.step 7 (.close 29))))) (.step 29 (.step 7 (.close 9)))) (.step 7 (.close 29))) (.step 7 (.close 29))) (.step 7 (.step 19 (.step 25 (.step 29 (.close 19))))))))
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
end FiveColour.Packed.EnumerationChunks.Case165
