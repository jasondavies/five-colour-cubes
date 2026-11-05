module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case130
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 11031315046490827063734810252807897147906663155714922655383763785300200921729236658022183685968499181543439394300642599402135782228403439166093230211284779432853165244509969100239648375129033318395720584235066429803523⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨31580798797232318965660, 5521043902401079285245703114100180852279210293007498667362342662451989309891209519920916348400808705186586945553271027835730159787749946386451025171467237958107529184775918001688523606593683223613208425061032107443201, 0⟩]
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
def root : Box := ⟨3, 11031315046490827063734810252807897147906663155714922655383763785300200921729236658022183685968499181543439394300642599402135782228403439166093230211284776141844050602097884790301283260428023352923989317075339732583427⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 37 1 (.split 45 1 (.split 68 1 (.split 5 1 (.split 6 1 (.split 11 1 (.split 12 1 (.step 4 (.split 26 1 (.step 4 (.step 6 (.close 4))) (.step 4 (.step 6 (.close 4))))) (.step 4 (.step 15 (.close 4)))) (.step 4 (.step 14 (.close 4)))) (.step 4 (.step 9 (.step 4 (.step 6 (.close 4)))))) (.step 4 (.step 8 (.step 4 (.step 6 (.close 4)))))) (.step 4 (.split 5 1 (.split 6 1 (.split 11 1 (.split 12 1 (.split 26 1 (.step 71 (.step 4 (.step 6 (.step 7 (.close 18))))) (.step 4 (.step 6 (.step 18 (.close 29))))) (.step 4 (.step 15 (.step 6 (.step 18 (.close 29)))))) (.step 4 (.step 14 (.step 7 (.step 18 (.close 30)))))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 7 (.close 8)))))) (.step 4 (.step 18 (.split 5 1 (.split 6 1 (.split 11 1 (.split 12 1 (.split 26 1 (.step 48 (.step 18 (.step 4 (.step 6 (.close 30))))) (.step 4 (.step 6 (.step 7 (.step 18 (.close 29)))))) (.step 4 (.close 15))) (.step 4 (.close 14))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 6 (.close 8))))))) (.step 4 (.split 5 1 (.split 6 1 (.split 11 1 (.split 12 1 (.split 26 1 (.step 40 (.step 4 (.step 6 (.step 7 (.close 18))))) (.step 4 (.step 6 (.step 18 (.close 29))))) (.step 4 (.step 15 (.step 6 (.step 18 (.close 29)))))) (.step 4 (.step 14 (.step 7 (.step 18 (.close 30)))))) (.step 4 (.step 6 (.close 9)))) (.step 4 (.step 7 (.close 8)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3, 11031315046490827063734810252807897147906663155714922655383763785300200921729236658022183685968499181543439394300642599402135782228403439166093230211284779432853165244509969100239648375129033318395720584235066429803523⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 4 (.split 21 1 (.reuse 0) (.run (.step 4 (.step 18 (.split 5 1 (.split 6 1 (.split 11 1 (.split 12 1 (.split 26 1 (.step 24 (.step 18 (.step 4 (.step 6 (.close 24))))) (.step 4 (.step 6 (.step 7 (.step 18 (.close 24)))))) (.step 4 (.close 15))) (.step 4 (.close 14))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 6 (.close 8)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case130
