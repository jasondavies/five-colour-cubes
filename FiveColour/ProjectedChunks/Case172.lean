module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case172
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨5368709120, 27578261315509951190293573009181879821612031056833052072607586401445832050266569092377515365822805540488394102204848583232804504576830940383220631898272054235967322736802367535222721038223488666866799965663704440111104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908392998381874375671, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859361899508584915508177230179531154389992449, 0⟩]
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
def root : Box := ⟨5368709120, 22062609052407958992681534144408529078141359762215129152622999453185061167676019190179426423400008604072021912864674731572065039896307473190642687065293773522630237495544505959164359769698066491073402440527939949821952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 49 1 (.split 72 2 (.split 50 1 (.split 59 1 (.step 31 (.split 35 1 (.step 3 (.split 12 1 (.split 16 0 (.split 17 0 (.split 72 1 (.step 3 (.step 18 (.close 31))) (.step 26 (.step 3 (.close 12)))) (.step 18 (.close 57))) (.step 18 (.close 57))) (.step 9 (.step 12 (.step 15 (.close 18)))))) (.step 9 (.step 32 (.split 51 1 (.step 75 (.split 12 1 (.split 54 1 (.step 3 (.close 38)) (.step 21 (.step 31 (.close 57)))) (.step 15 (.close 3)))) (.step 3 (.close 15))))))) (.step 3 (.split 12 1 (.split 16 0 (.split 17 0 (.step 26 (.split 35 1 (.step 3 (.step 18 (.close 31))) (.step 21 (.step 3 (.step 18 (.close 31)))))) (.step 3 (.close 62))) (.step 3 (.step 18 (.close 21)))) (.step 15 (.close 3))))) (.step 3 (.step 32 (.step 62 (.split 12 1 (.split 16 0 (.split 17 0 (.step 9 (.step 21 (.step 31 (.step 57 (.step 3 (.close 12)))))) (.step 3 (.step 18 (.close 40)))) (.step 18 (.close 21))) (.step 15 (.close 3))))))) (.step 29 (.step 31 (.split 12 1 (.split 50 1 (.split 51 1 (.step 75 (.step 3 (.close 18))) (.step 3 (.close 57))) (.step 3 (.step 40 (.step 57 (.close 75))))) (.step 15 (.close 75)))))) (.step 3 (.step 12 (.step 62 (.split 72 2 (.step 53 (.split 16 0 (.split 17 0 (.step 9 (.step 57 (.step 31 (.step 21 (.step 3 (.step 18 (.close 26))))))) (.step 3 (.close 40))) (.step 3 (.step 18 (.close 21))))) (.step 26 (.step 38 (.step 40 (.step 57 (.step 52 (.close 75))))))))))) (.step 31 (.step 15 (.close 62)))) (.step 31 (.step 15 (.close 57)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨5368709120, 27578261315509946291410262351839442873761629655193447550375803776218089072530134204825465650986546303163484810266262530737019867248219869865532718405795939152715170372461517800752685048161719234542915063488746071523328⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 54 2 (.step 18 (.step 75 (.split 21 2 (.split 59 2 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 34 1 (.reuse 0) (.run (.step 31 (.step 15 (.close 52))))) (.run (.step 18 (.close 26)))) (.run (.step 3 (.step 18 (.step 31 (.step 15 (.step 57 (.step 75 (.split 49 1 (.split 72 1 (.step 3 (.step 18 (.close 15))) (.step 18 (.close 31))) (.step 3 (.step 12 (.close 18)))))))))))) (.run (.step 18 (.close 22)))) (.run (.step 18 (.close 21)))) (.run (.step 3 (.step 26 (.step 62 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 12 1 (.split 16 0 (.step 62 (.step 18 (.close 31))) (.step 3 (.close 62))) (.step 15 (.close 62))) (.step 31 (.close 62))) (.step 15 (.step 31 (.close 52)))) (.step 18 (.close 26))) (.step 18 (.close 22)))))))) (.run (.step 31 (.split 59 2 (.split 72 2 (.split 35 1 (.split 49 1 (.step 24 (.step 9 (.step 15 (.step 18 (.step 3 (.step 12 (.close 53))))))) (.step 3 (.step 12 (.step 18 (.close 52))))) (.step 18 (.step 24 (.step 15 (.close 38))))) (.step 18 (.step 38 (.step 24 (.step 57 (.close 75)))))) (.step 15 (.step 18 (.step 57 (.close 62)))))))))) (.run (.step 12 (.step 21 (.step 22 (.step 24 (.step 26 (.step 32 (.step 57 (.close 3))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨5368709120, 27578261315509946291410262351839442873761629655193447550375803776227918834365369201163640024343719025227025996097885991896845180682688240396728396390430759010041493891249580841467770222334905820361858016261192577712128⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 49 2 (.split 50 2 (.reuse 0) (.run (.step 3 (.step 18 (.step 21 (.step 57 (.step 62 (.step 75 (.split 21 2 (.split 16 1 (.split 17 1 (.step 52 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 72 2 (.split 12 1 (.split 17 0 (.step 53 (.step 18 (.close 31))) (.step 3 (.close 53))) (.step 15 (.close 53))) (.step 15 (.step 26 (.step 40 (.step 57 (.split 34 0 (.step 53 (.close 57)) (.step 15 (.step 31 (.close 53))))))))) (.step 31 (.close 53))) (.step 31 (.close 53))) (.step 31 (.close 53))) (.step 18 (.close 26)))) (.step 18 (.close 53))) (.step 18 (.close 53))) (.step 15 (.step 18 (.step 53 (.close 24))))))))))))) (.run (.step 3 (.step 12 (.step 18 (.step 57 (.step 75 (.split 16 1 (.split 17 1 (.step 52 (.split 21 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 72 2 (.split 16 0 (.split 17 0 (.split 21 0 (.step 52 (.step 26 (.step 52 (.close 38)))) (.step 3 (.step 40 (.close 52)))) (.step 3 (.close 52))) (.step 3 (.step 21 (.close 52)))) (.step 26 (.step 38 (.step 40 (.step 57 (.step 52 (.close 75))))))) (.step 31 (.close 52))) (.step 31 (.close 52))) (.step 31 (.close 52))) (.step 18 (.close 26))) (.step 18 (.close 52)))) (.step 18 (.close 52))) (.step 18 (.close 52))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨5368709120, 27578261315509951190293573009181879821612031056833052072607586401445832050266569092377515365822805540488394102204848583232804504576830940383220631898272054235967322736802367535222721038223488666866799965663704440111104⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 24 (.step 31 (.split 12 2 (.split 35 2 (.reuse 0) (.run (.step 18 (.step 21 (.step 57 (.step 62 (.step 75 (.split 21 2 (.split 49 2 (.split 59 2 (.split 12 1 (.split 16 1 (.step 29 (.step 38 (.split 49 1 (.split 54 1 (.step 3 (.step 18 (.step 38 (.step 3 (.close 18))))) (.step 38 (.close 57))) (.step 3 (.step 12 (.step 40 (.step 38 (.step 26 (.step 38 (.close 52)))))))))) (.step 18 (.close 21))) (.step 15 (.close 38))) (.step 38 (.step 40 (.step 52 (.step 57 (.split 34 0 (.step 62 (.close 38)) (.step 31 (.close 38)))))))) (.step 12 (.step 38 (.step 40 (.step 52 (.step 57 (.split 36 0 (.step 52 (.close 26)) (.step 31 (.close 38))))))))) (.step 15 (.step 18 (.step 38 (.close 24)))))))))))) (.run (.step 21 (.step 22 (.step 24 (.step 26 (.step 15 (.close 3)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case172
