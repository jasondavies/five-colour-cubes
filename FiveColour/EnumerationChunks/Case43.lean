module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case43
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385586726332153578340564076825196806239628009025805056200994399355957672947436486656⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908284911715872467959, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691003773395856797335276228224145743890145446228163347693427359436041631246125966867020082117046907873927859536897, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385586726332153578340564076825196806239628009025805054933343799127728271450733281280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 12 0 (.split 22 0 (.split 59 0 (.split 49 0 (.step 7 (.step 18 (.step 9 (.close 28)))) (.step 37 (.step 7 (.step 9 (.close 18))))) (.step 45 (.step 9 (.step 18 (.step 7 (.close 16)))))) (.step 7 (.step 43 (.step 4 (.close 5))))) (.split 35 0 (.step 37 (.step 7 (.step 18 (.step 9 (.close 33))))) (.step 29 (.step 37 (.step 18 (.step 33 (.close 38))))))) (.split 22 0 (.split 12 0 (.step 7 (.step 39 (.step 4 (.step 9 (.close 5))))) (.step 37 (.step 7 (.step 18 (.step 9 (.step 33 (.close 38))))))) (.step 7 (.split 12 0 (.step 39 (.step 23 (.step 9 (.close 17)))) (.step 13 (.step 24 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20))))))))))) (.split 17 0 (.split 22 0 (.step 38 (.step 7 (.close 43))) (.step 7 (.split 12 0 (.step 45 (.step 23 (.step 9 (.step 17 (.close 19))))) (.step 13 (.step 24 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20)))))))))) (.split 22 0 (.step 7 (.split 12 0 (.step 39 (.step 23 (.step 9 (.close 17)))) (.step 13 (.step 24 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20))))))))) (.split 26 0 (.step 24 (.step 20 (.close 4))) (.step 7 (.close 17)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385586726332153578340564076825196806239628009025805056200994399355957672947436486656⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 12 0 (.step 7 (.step 52 (.step 58 (.step 9 (.close 33))))) (.step 15 (.step 7 (.close 13)))) (.step 7 (.split 12 0 (.step 45 (.step 13 (.step 15 (.step 4 (.close 9))))) (.step 13 (.close 4))))) (.step 7 (.split 12 0 (.split 22 0 (.step 39 (.step 13 (.step 4 (.step 9 (.close 5))))) (.step 13 (.step 24 (.step 39 (.step 4 (.close 5)))))) (.step 13 (.close 4))))) (.step 7 (.split 12 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 43 (.step 4 (.close 5))) (.step 13 (.step 33 (.close 38)))) (.step 13 (.step 24 (.step 45 (.step 4 (.close 5)))))) (.step 13 (.split 35 0 (.split 38 0 (.step 24 (.step 14 (.close 20))) (.step 23 (.step 14 (.close 19)))) (.step 24 (.step 4 (.close 5)))))) (.step 13 (.close 4)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Case43
