module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case160
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 14696649931972027310843567413250124865537179545093439263006959923764509578370492614225090042016592934024712630968082005368590957896147791281707544963611392948807153088719483585775190013509790116536647680⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨37630669409018456112119, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639180033369853557824749914671530180203279448118754128379673028050877429417560652570824680124548036304556207899649, 0⟩]
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
def root : Box := ⟨4294967296, 4898883310657342436947866610446845652807205799353216953383423347438573399034675120513392538808005849186577660408545386999798013290190580171047226034961991995441277337455663086295794152653226819824123904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 2 (.split 56 2 (.split 59 2 (.step 18 (.step 31 (.step 58 (.step 3 (.step 31 (.step 58 (.step 3 (.close 18)))))))) (.step 58 (.split 16 1 (.split 17 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 22 1 (.split 56 1 (.step 62 (.step 3 (.step 31 (.close 18)))) (.step 3 (.step 22 (.step 31 (.step 52 (.step 21 (.step 53 (.step 21 (.close 58))))))))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 31 (.close 52)))) (.step 3 (.step 21 (.step 31 (.step 52 (.close 58)))))) (.step 3 (.step 22 (.step 31 (.close 52))))) (.step 3 (.step 31 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))))) (.step 18 (.step 31 (.step 58 (.step 31 (.step 3 (.step 5 (.close 58)))))))) (.step 21 (.step 53 (.step 58 (.step 53 (.split 16 1 (.split 17 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 22 1 (.split 56 1 (.step 62 (.split 34 0 (.step 53 (.step 3 (.step 31 (.close 18)))) (.step 3 (.step 21 (.step 31 (.close 52)))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 52 (.close 53))))))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 21 (.step 31 (.close 52))))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 52)))))) (.step 3 (.step 21 (.step 31 (.close 52))))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 14696649931972027310843567413250124865537179545093439263006959923764509578370492614225090042016592934024712630968082005368590957896147791281707544963611392948807153088719483585775190013509790116536647680⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 18 (.step 31 (.step 58 (.split 38 2 (.step 3 (.split 49 2 (.reuse 0) (.run (.step 52 (.step 58 (.split 50 1 (.split 59 1 (.step 3 (.step 18 (.step 31 (.step 48 (.step 21 (.step 52 (.step 21 (.close 58)))))))) (.step 52 (.step 62 (.split 36 1 (.split 38 1 (.step 52 (.step 18 (.close 22))) (.step 3 (.step 21 (.step 31 (.step 52 (.close 58)))))) (.step 3 (.step 22 (.step 31 (.close 52)))))))) (.step 21 (.step 52 (.step 18 (.step 21 (.close 22))))))))))) (.run (.step 10 (.step 21 (.step 31 (.step 41 (.step 3 (.step 18 (.step 58 (.split 56 1 (.step 3 (.step 31 (.step 5 (.step 21 (.step 41 (.close 58)))))) (.step 28 (.step 41 (.step 31 (.step 3 (.step 58 (.step 41 (.close 3)))))))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case160
