module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case79
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453662937339866917829898525575702741147148683607720716629431726907862846768667319649344419120433526760768928975405322294499007270620046061246528260766972808127495610857974398976⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 9⟩]
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 4898883310657342436947854453662937339866917829898525575702741147148683607720716629431726907862846768667319649344419120433526760768928975405322294499007270620046061246528260766972808127495610857974398976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 52 (.close 53)) (.step 54 (.step 43 (.step 13 (.step 52 (.close 53)))))) (.split 10 0 (.step 53 (.step 33 (.step 37 (.step 38 (.close 39))))) (.step 13 (.step 33 (.step 45 (.step 53 (.step 39 (.step 54 (.close 70))))))))) (.split 30 0 (.step 70 (.step 24 (.step 13 (.step 52 (.close 53))))) (.step 33 (.split 49 0 (.split 42 0 (.split 43 0 (.step 17 (.close 20)) (.split 51 0 (.step 17 (.step 24 (.close 45))) (.step 53 (.step 20 (.close 70))))) (.step 25 (.step 70 (.step 17 (.step 20 (.close 45)))))) (.step 13 (.step 24 (.close 42))))))) (.split 22 0 (.split 30 0 (.step 54 (.step 24 (.step 13 (.step 52 (.close 53))))) (.step 33 (.split 49 0 (.split 36 0 (.split 43 0 (.step 17 (.step 24 (.close 25))) (.split 59 0 (.step 25 (.step 39 (.close 54))) (.step 24 (.close 25)))) (.step 54 (.step 17 (.step 20 (.step 25 (.close 39)))))) (.step 13 (.step 24 (.close 42)))))) (.split 30 0 (.split 34 0 (.step 54 (.step 24 (.step 13 (.step 25 (.close 53))))) (.split 49 0 (.split 36 0 (.step 24 (.step 20 (.close 25))) (.step 25 (.step 20 (.step 17 (.step 19 (.close 24)))))) (.step 13 (.step 17 (.step 20 (.close 24)))))) (.step 33 (.split 49 0 (.step 25 (.close 20)) (.step 13 (.split 34 0 (.step 24 (.step 25 (.step 42 (.close 53)))) (.step 17 (.step 20 (.close 24)))))))))))
theorem accepted : Fast.check 9 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 9 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 9 families root :=
  Fast.check_sound 9 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 4898883310657342436947854453662937339866917829898525575702741147148683607720716629431726907862846768667319649344419120433526760768928975405322294499007270620046061246528260766972808127495610857974398976⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 36 0 (.step 52 (.step 33 (.close 53))) (.step 54 (.step 45 (.step 13 (.step 33 (.close 52)))))) (.step 70 (.step 52 (.close 33)))) (.split 22 0 (.step 54 (.step 52 (.close 33))) (.split 30 0 (.step 54 (.step 24 (.step 13 (.step 52 (.close 62))))) (.step 33 (.split 49 0 (.split 42 0 (.step 54 (.close 17)) (.step 25 (.step 39 (.step 17 (.close 24))))) (.step 13 (.step 24 (.close 54))))))))) (.reuse 0))
theorem accepted : Fast.check 9 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 9 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 9 families root :=
  Fast.check_sound 9 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 9 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Case79
