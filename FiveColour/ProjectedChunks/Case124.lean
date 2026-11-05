module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case124
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563360988812019600753489695576727108223441446050823162149888295180723588540306001958948033257361300580282306786926215966883497021811860138183739584782300918424382486832573923196928⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563360988812019600753489695576727108223441446050823162149888295180723588540301522469463677648940185695721169898366602682555633889771648426567583564885646745211966511188237638172672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 7 (.step 70 (.step 7 (.step 26 (.step 44 (.split 17 0 (.step 26 (.step 44 (.close 62))) (.step 7 (.step 27 (.close 44))))))))) (.step 54 (.step 7 (.step 54 (.close 7))))) (.step 53 (.split 51 1 (.split 67 1 (.step 7 (.split 34 0 (.step 53 (.close 7)) (.step 9 (.step 7 (.step 18 (.step 26 (.step 18 (.close 31)))))))) (.step 53 (.close 7))) (.step 53 (.step 7 (.close 54)))))) (.step 52 (.split 51 1 (.split 67 1 (.split 16 0 (.split 17 0 (.step 52 (.close 7)) (.step 27 (.step 7 (.step 34 (.step 44 (.step 18 (.close 52))))))) (.step 27 (.step 7 (.step 21 (.step 44 (.step 18 (.close 52))))))) (.step 52 (.close 7))) (.step 52 (.step 7 (.close 54)))))) (.step 46 (.step 52 (.step 53 (.step 62 (.split 16 0 (.split 17 0 (.split 49 1 (.split 50 1 (.step 7 (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.close 52))))) (.step 7 (.close 27))) (.step 7 (.close 27)))))))) (.step 7 (.split 49 1 (.split 50 1 (.step 7 (.close 31)) (.step 9 (.step 18 (.step 31 (.close 53))))) (.step 9 (.step 18 (.step 31 (.close 52))))))) (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.step 7 (.close 31)) (.step 9 (.step 18 (.step 31 (.close 53))))) (.step 9 (.step 18 (.step 31 (.close 52))))) (.step 7 (.close 31))))) (.step 7 (.split 49 1 (.step 7 (.step 18 (.close 53))) (.step 18 (.close 52))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 14696649931972027310843563360988812019600753489695576727108223441446050823162149888295180723588540306001958948033257361300580282306786926215966883497021811860138183739584782300918424382486832573923196928⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.step 7 (.step 18 (.close 52))) (.step 18 (.close 52)))))) (.run (.step 7 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 7 (.close 31)) (.step 9 (.step 15 (.step 18 (.step 31 (.close 52)))))) (.step 9 (.step 15 (.step 18 (.step 31 (.close 52)))))) (.step 7 (.close 31))) (.step 31 (.step 7 (.close 37))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 53))) (.step 18 (.close 52)))))) (.run (.step 7 (.split 22 1 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 7 (.close 18)))))) (.run (.step 7 (.split 17 1 (.split 22 1 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 7 (.close 18))) (.step 18 (.step 7 (.close 19)))))))
theorem accepted : Chunks.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Chunks.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case124
