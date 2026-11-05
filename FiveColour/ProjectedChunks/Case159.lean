module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case159
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 20547420562073265984704848899732305810752788293392480828525960026937070328324469270501914355744029186454239325959353951828593224040886470104094731929728789327053521017561907029208496751279545668370171399503872⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨37033564156298044177399, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969540306823801303036701114543271236497705040614186417671967029225310810172032001, 0⟩]
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
def root : Box := ⟨4294967296, 20547420562073265984704848899732305810752788293392480828525960026937070328324469270501914355744029186454239325959353951828593224040886470104094731929728789327053521017561907029208496751279545668370171399503872⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 31 (.split 49 2 (.split 50 2 (.split 59 2 (.split 61 2 (.split 62 2 (.step 3 (.split 69 2 (.step 18 (.step 3 (.step 31 (.close 3)))) (.step 3 (.step 72 (.step 18 (.close 31)))))) (.step 3 (.step 65 (.step 3 (.step 72 (.step 18 (.close 31))))))) (.step 3 (.step 64 (.step 3 (.step 72 (.step 18 (.close 31))))))) (.step 3 (.step 62 (.step 18 (.close 31))))) (.step 3 (.step 53 (.step 3 (.step 62 (.step 18 (.close 31))))))) (.step 3 (.step 52 (.step 3 (.step 62 (.step 18 (.close 31)))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case159
