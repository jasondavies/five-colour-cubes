module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case152
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 14696649931972027310843567413250124865537179545093439263006959923764509578370492614225090042016592934024712630968082005368590965133153368613969758936797955991801393918093525188310442479608790611107250176⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37630669409018422557687, 5789234131009374248507346766749891419687533244750779835710650130547166070165997423784225875531183789473991668342093468871764627366270137944873799542728008123750934930136012272409766640092332188979741397452445100402566759425, 0⟩]
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
def root : Box := ⟨4294967296, 9797766621314684873895717011848485257329437581978434872992665578376939364242957648396898568074353886845607295772639831765932245483657736487013858834154738001484729840884909566447168609568549643250302976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 2 (.step 3 (.split 49 2 (.split 50 2 (.step 18 (.step 31 (.step 58 (.split 56 2 (.split 59 2 (.step 3 (.step 31 (.close 58))) (.split 25 1 (.split 38 1 (.split 56 1 (.step 62 (.step 3 (.step 29 (.step 16 (.close 21))))) (.step 3 (.step 22 (.step 31 (.step 52 (.step 21 (.step 28 (.step 21 (.step 53 (.close 58)))))))))) (.step 3 (.step 21 (.step 31 (.step 28 (.step 52 (.close 58))))))) (.step 3 (.step 31 (.close 58))))) (.step 58 (.split 25 1 (.step 31 (.step 3 (.step 5 (.close 58)))) (.step 28 (.close 58)))))))) (.step 21 (.step 53 (.step 58 (.split 59 1 (.step 3 (.step 18 (.step 31 (.step 48 (.step 21 (.step 28 (.step 52 (.step 28 (.close 53))))))))) (.step 52 (.step 18 (.step 31 (.step 53 (.step 3 (.step 31 (.step 53 (.step 3 (.step 21 (.close 53))))))))))))))) (.step 52 (.step 58 (.split 50 1 (.step 18 (.step 31 (.split 59 1 (.step 3 (.step 31 (.step 48 (.step 52 (.step 21 (.close 28)))))) (.step 52 (.step 3 (.step 31 (.step 58 (.step 52 (.close 3))))))))) (.step 21 (.step 52 (.step 3 (.step 18 (.step 31 (.step 53 (.step 3 (.step 21 (.close 52)))))))))))))) (.step 10 (.step 21 (.step 31 (.step 41 (.step 58 (.step 28 (.step 3 (.step 18 (.split 56 1 (.step 3 (.step 31 (.step 5 (.step 21 (.step 28 (.close 41)))))) (.step 28 (.step 31 (.step 3 (.step 5 (.step 21 (.close 41)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 14696649931972027310843567413250124865537179545093439263006959923764509578370492614225090042016592934024712630968082005368590965133153368613969758936797955991801393918093525188310442479608790611107250176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 18 (.step 31 (.step 58 (.split 25 2 (.reuse 0) (.run (.step 10 (.step 28 (.step 3 (.step 18 (.step 31 (.step 58 (.split 38 1 (.step 31 (.step 3 (.step 5 (.step 28 (.step 21 (.step 52 (.close 58))))))) (.step 21 (.close 28)))))))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case152
