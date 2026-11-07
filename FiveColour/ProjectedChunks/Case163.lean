module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case163
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 14696649931972027310843567413250109754945439536968884389595063388703520555541387431211646263345286992573790608268317171496806457101030448337679594870959463296296912876252378552531360509156444941452312576⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37630777495684390910967, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969540306823801303036701114543271236497706403072882097210736755628673497432065025, 0⟩]
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
def root : Box := ⟨4294967296, 14696649931972027310843567413250109754945439536968884389595063388703520555541387431211646263345286992573790608268317171496806457101030448337679594870959463296296912876252378552531360509156444941452312576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 31 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 49 2 (.split 50 2 (.split 59 2 (.step 3 (.step 18 (.close 31))) (.step 62 (.step 3 (.step 18 (.close 31))))) (.step 62 (.step 3 (.split 36 1 (.step 52 (.step 18 (.close 31))) (.step 31 (.close 52)))))) (.step 52 (.step 62 (.step 3 (.step 31 (.split 36 1 (.step 52 (.close 3)) (.step 31 (.close 52)))))))) (.step 31 (.step 52 (.close 53)))) (.step 18 (.step 52 (.close 53)))) (.step 18 (.step 52 (.close 53)))) (.step 18 (.step 52 (.close 53))))))
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
end FiveColour.Packed.ProjectedChunks.Case163
