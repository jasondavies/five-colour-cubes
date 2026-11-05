module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case252
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055221114677693970840402853060144478704032022528⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055219720881119062676456507077752438181437898752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 0 (.split 63 0 (.split 64 0 (.split 16 0 (.split 17 0 (.step 24 (.step 15 (.step 20 (.close 39)))) (.step 20 (.step 15 (.step 17 (.close 39))))) (.split 17 0 (.split 22 0 (.step 24 (.step 20 (.close 38))) (.step 25 (.step 11 (.close 17)))) (.split 22 0 (.step 20 (.step 11 (.close 17))) (.step 20 (.step 11 (.step 15 (.close 17))))))) (.step 33 (.split 10 0 (.step 24 (.close 19)) (.split 16 0 (.step 24 (.step 15 (.close 17))) (.step 17 (.step 19 (.close 11))))))) (.step 13 (.split 64 0 (.split 16 0 (.step 24 (.step 15 (.close 20))) (.split 17 0 (.step 24 (.close 25)) (.step 20 (.step 11 (.close 15))))) (.step 33 (.split 16 0 (.step 24 (.step 15 (.close 25))) (.step 11 (.step 19 (.step 15 (.close 25))))))))) (.step 33 (.split 63 0 (.split 17 0 (.step 24 (.step 15 (.close 17))) (.step 39 (.step 19 (.step 11 (.close 15))))) (.step 13 (.step 29 (.step 24 (.step 19 (.close 25)))))))))
theorem accepted : Chunks.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Chunks.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055221114677693970840402853060144478704032022528⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 10 0 (.split 22 0 (.split 34 0 (.split 30 0 (.step 11 (.step 13 (.step 19 (.close 20)))) (.step 13 (.step 24 (.close 19)))) (.step 37 (.close 11))) (.split 30 0 (.split 34 0 (.step 11 (.step 13 (.step 20 (.close 19)))) (.step 17 (.step 24 (.close 33)))) (.step 13 (.step 25 (.step 33 (.step 11 (.step 17 (.close 20)))))))) (.step 13 (.step 11 (.step 13 (.step 15 (.step 17 (.close 33))))))) (.split 17 0 (.split 22 0 (.split 34 0 (.step 13 (.step 24 (.close 19))) (.step 38 (.step 13 (.step 11 (.close 17))))) (.step 13 (.step 19 (.step 25 (.close 11))))) (.split 10 0 (.split 22 0 (.step 13 (.step 19 (.step 20 (.close 11)))) (.step 19 (.step 13 (.step 20 (.step 11 (.close 17)))))) (.step 13 (.close 17)))))))
theorem accepted : Chunks.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Chunks.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case252
