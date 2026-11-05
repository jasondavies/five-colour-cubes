module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case131
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 11031304526203974597457456414861827591216226218170224712992800863701511987345293261276955675041785747872245836758516316945197974873823230471798269789540728614993933247412426327056486183294402372092120028165295002615811⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨33056547325848823263166, 5653548961323972924649819221030976445153133834664318320894055915633373970312978309199083541659665574237124035234633543590903009947958734622527102053675334481630444417570509838843814981610451647649597243903117796856300545, 0⟩]
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
def root : Box := ⟨3, 11031304526203974597457456414861827591216226218170224712992800863701511987345293261276955675041785747872245836758516316945197974873823230471798269789540728614993933247412426327056486183294402372092120028165295002615811⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 37 1 (.split 45 1 (.step 29 (.step 38 (.step 18 (.step 37 (.step 15 (.step 39 (.step 7 (.step 9 (.close 15))))))))) (.step 4 (.step 9 (.step 15 (.step 29 (.step 37 (.step 38 (.step 39 (.step 45 (.step 7 (.step 39 (.step 7 (.close 15))))))))))))) (.step 4 (.step 29 (.step 38 (.step 18 (.step 40 (.step 18 (.step 6 (.step 7 (.step 18 (.close 37))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case131
