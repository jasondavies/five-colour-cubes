module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case261
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453662937339866917829898525575702741147148683607720716629431726907862846768667319649344419120433526760768928975405322294499007270620046061246528260766972808127495610857974398976⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨37630777495684390910967, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969540306823801303036701114543271236497706403072882097210736755628673497432065025, 0⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947854453662937339866917829898525575702741147148683607720716629431726907862846768667319649344419120433526760768928975405322294499007270620046061246528260766972808127495610857974398976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 0 (.split 50 0 (.split 17 0 (.step 45 (.step 17 (.step 20 (.close 24)))) (.split 36 0 (.step 25 (.step 17 (.close 39))) (.step 54 (.step 17 (.close 20))))) (.step 33 (.split 17 0 (.step 43 (.step 45 (.close 24))) (.step 54 (.step 15 (.step 17 (.close 19))))))) (.step 13 (.split 50 0 (.split 17 0 (.step 43 (.step 45 (.step 17 (.close 24)))) (.step 54 (.step 17 (.close 24)))) (.step 33 (.split 17 0 (.step 43 (.step 52 (.step 53 (.close 54)))) (.step 54 (.step 17 (.close 24)))))))))
theorem accepted : Chunks.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 10 families root :=
  Chunks.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 10 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case261
