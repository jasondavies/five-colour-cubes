module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case145
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 22062609072975435583028631289050242477408899362913360780759701718906196071722981281654683816466216116414183168122039526655296860369470163090524725501036342791423138815180716573868412475674325410892547717959917638778880⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32016031753816174816247, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859360537049889235969407502623246962523112449, 0⟩]
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
def root : Box := ⟨4294967296, 11031304536482698885562547197198468165968213701681847363918554756099838410387059583165296092749740891049045499281556738791848684124845934918408373508225578558508485151450313374642706429857324448808373295006347719344128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.split 59 1 (.split 61 1 (.split 62 1 (.step 31 (.split 69 1 (.step 3 (.close 18)) (.step 3 (.close 4)))) (.step 3 (.close 71))) (.step 3 (.step 31 (.step 21 (.close 64))))) (.step 3 (.close 62)))) (.split 59 1 (.step 3 (.split 61 1 (.split 62 1 (.step 57 (.close 4)) (.step 3 (.close 57))) (.step 3 (.close 57)))) (.step 26 (.step 3 (.close 57))))) (.step 53 (.split 16 0 (.split 17 0 (.split 21 0 (.split 34 0 (.step 3 (.step 21 (.step 3 (.close 12)))) (.step 3 (.step 21 (.close 26)))) (.step 3 (.close 40))) (.step 3 (.close 40))) (.step 3 (.close 21))))) (.step 52 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 3 (.step 12 (.step 3 (.close 21)))) (.step 3 (.step 12 (.close 26)))) (.step 3 (.close 26))) (.step 3 (.close 40))) (.step 3 (.step 12 (.close 18)))))) (.step 31 (.close 12))) (.step 31 (.close 12))) (.step 18 (.close 26))) (.step 18 (.close 22))) (.step 18 (.close 21))) (.step 12 (.step 21 (.step 22 (.step 26 (.split 36 1 (.split 42 1 (.split 54 1 (.split 59 1 (.split 50 1 (.step 3 (.step 12 (.split 62 1 (.step 15 (.close 18)) (.step 3 (.close 15))))) (.step 12 (.step 3 (.close 15)))) (.step 12 (.step 15 (.close 3)))) (.step 15 (.close 3))) (.step 15 (.close 31))) (.step 15 (.close 31)))))))))
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
def root : Box := ⟨4294967296, 11031304536492736697466084091851774311440685661231513416841146962806357661335921698489387726424160473529995932493776973723521511759639585487847166617619896947194503746494222103760745906136140645771491956455363657596928⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 3 (.split 68 1 (.split 21 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.step 18 (.step 21 (.step 31 (.split 61 1 (.split 12 1 (.split 49 1 (.split 54 1 (.split 69 1 (.split 17 0 (.split 59 1 (.step 3 (.step 21 (.close 38))) (.step 21 (.step 3 (.close 26)))) (.step 3 (.close 38))) (.step 3 (.close 38))) (.step 21 (.step 38 (.step 3 (.close 57))))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 40 (.step 38 (.step 26 (.close 52))))))))) (.step 15 (.close 3))) (.step 3 (.step 15 (.close 71))))))))) (.run (.step 31 (.close 12)))) (.run (.step 18 (.split 12 1 (.split 35 1 (.step 3 (.split 49 1 (.split 50 1 (.step 31 (.split 54 1 (.split 59 1 (.split 61 1 (.step 18 (.close 4)) (.step 4 (.step 21 (.close 64)))) (.step 4 (.close 18))) (.step 4 (.close 18)))) (.step 4 (.close 18))) (.step 4 (.step 12 (.close 18))))) (.step 18 (.close 31))) (.step 4 (.step 15 (.close 3))))))) (.run (.step 18 (.step 31 (.split 21 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 71 (.split 12 1 (.step 3 (.step 71 (.close 15))) (.step 4 (.step 3 (.step 12 (.close 15)))))) (.step 3 (.step 4 (.close 62)))) (.step 3 (.step 18 (.step 15 (.close 53))))) (.step 3 (.step 12 (.step 18 (.close 52))))) (.step 32 (.step 38 (.close 71)))) (.step 4 (.close 63))))))))
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
def root : Box := ⟨4294967296, 22062609072970414227635207513043660267657163179304745550024697199571335324990470827608193711002532602864730663399149946404038721612718128740653631539693543399369255763917378182420333295153857078060236949090055674134528⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 69 2 (.split 72 2 (.reuse 0) (.run (.step 26 (.step 31 (.step 71 (.split 12 1 (.split 21 1 (.split 35 1 (.step 3 (.step 18 (.split 49 1 (.split 50 1 (.split 54 1 (.split 61 1 (.split 62 1 (.split 69 1 (.step 75 (.split 16 0 (.split 12 0 (.step 3 (.close 75)) (.step 26 (.step 3 (.step 12 (.close 75))))) (.step 3 (.close 75)))) (.step 3 (.close 75))) (.step 31 (.close 71))) (.step 31 (.close 71))) (.step 26 (.step 57 (.close 18)))) (.step 21 (.step 26 (.step 40 (.step 57 (.step 3 (.close 12))))))) (.step 12 (.step 26 (.step 40 (.step 52 (.step 57 (.step 3 (.close 21)))))))))) (.step 21 (.step 29 (.step 38 (.step 3 (.step 18 (.step 38 (.step 3 (.step 21 (.close 38)))))))))) (.step 4 (.step 18 (.close 75)))) (.step 15 (.close 75)))))))) (.run (.step 31 (.step 71 (.split 16 1 (.split 12 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 35 1 (.step 72 (.step 3 (.step 22 (.step 31 (.close 71))))) (.step 3 (.step 31 (.close 71)))) (.step 3 (.close 18))) (.step 36 (.step 64 (.step 31 (.step 5 (.close 72)))))) (.step 3 (.close 18))) (.step 3 (.step 64 (.step 4 (.step 15 (.close 65)))))) (.step 3 (.close 18)))))))
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
def root : Box := ⟨4294967296, 22062609072970414227635207513052370930747462682318725493182514302937426663741126947493584078630838628751567309413571963843565538802043318352912308419858295594252082705721290130853547568926994248641853057976206756937728⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 54 2 (.split 59 2 (.split 61 2 (.split 62 2 (.reuse 0) (.run (.step 21 (.step 71 (.step 65 (.step 31 (.split 17 1 (.split 12 1 (.split 21 1 (.split 54 1 (.split 72 1 (.step 65 (.step 3 (.step 18 (.step 21 (.close 31))))) (.step 3 (.step 31 (.close 65)))) (.step 3 (.step 57 (.step 64 (.close 65))))) (.step 4 (.step 18 (.step 21 (.step 63 (.step 64 (.step 31 (.step 3 (.close 65))))))))) (.step 3 (.step 64 (.step 4 (.step 15 (.close 65)))))) (.step 3 (.close 18))))))))) (.run (.step 71 (.step 64 (.step 31 (.split 16 1 (.split 17 1 (.split 12 1 (.split 21 1 (.split 22 1 (.split 35 1 (.split 54 1 (.split 72 1 (.step 64 (.step 3 (.step 31 (.close 64)))) (.step 3 (.close 64))) (.step 3 (.step 57 (.close 64)))) (.step 3 (.step 31 (.close 71)))) (.step 3 (.close 18))) (.step 4 (.step 34 (.step 64 (.step 3 (.step 18 (.close 4))))))) (.step 3 (.step 15 (.close 64)))) (.step 3 (.close 18))) (.step 3 (.close 18)))))))) (.run (.step 3 (.step 62 (.split 68 1 (.split 12 1 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.step 62 (.step 18 (.step 62 (.close 3)))) (.step 31 (.close 12))) (.step 26 (.step 55 (.step 57 (.close 62))))) (.step 15 (.close 31))) (.step 3 (.step 18 (.close 12)))) (.step 15 (.close 62))) (.step 18 (.close 62))))))) (.run (.step 21 (.step 22 (.step 26 (.step 57 (.step 31 (.split 62 2 (.split 61 2 (.split 62 1 (.step 57 (.step 3 (.step 4 (.close 57)))) (.step 3 (.step 57 (.close 64)))) (.step 4 (.step 57 (.close 64)))) (.step 4 (.step 64 (.step 57 (.close 65))))))))))))
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

namespace Part4
def root : Box := ⟨6880495847970214534832462685906260822389694967504843371212766518160768628265454424210055659330381354631168, 22062609072970414227635207513052370930747462682318725493182514302943979838297950278385700327535620443460594766639241268515429224114910540497646934291207972144139527299055176503437450103886088255327852132711422467506176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 21 (.step 31 (.step 57 (.step 71 (.split 49 2 (.split 59 1 (.split 72 1 (.split 12 1 (.step 3 (.step 18 (.split 21 1 (.split 49 1 (.split 54 1 (.split 61 1 (.split 69 1 (.step 29 (.step 38 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.step 3 (.close 38)) (.step 21 (.step 32 (.step 15 (.close 38))))) (.step 3 (.close 38))) (.step 21 (.step 18 (.close 31)))) (.step 3 (.close 38))))) (.step 3 (.close 38))) (.step 3 (.step 21 (.close 38)))) (.step 32 (.step 38 (.close 57)))) (.step 3 (.step 9 (.step 12 (.step 32 (.step 38 (.close 52))))))) (.step 4 (.step 18 (.close 31)))))) (.step 15 (.close 38))) (.step 29 (.step 38 (.split 17 1 (.step 75 (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 18 (.close 22)))))) (.step 15 (.step 26 (.step 40 (.step 57 (.split 34 0 (.step 62 (.close 3)) (.step 3 (.close 38)))))))) (.step 12 (.step 38 (.step 40 (.step 57 (.step 52 (.close 26))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4294967296, 22062609072970414227635207513052370930747462682318725493182514302943979838297950278385700327535620443460594766639241268515429224114910540497646934291207972144139527299055176503437450103886088255327852132711422467506176⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 35 2 (.split 49 2 (.split 50 2 (.reuse 0) (.run (.step 3 (.step 57 (.step 62 (.split 72 2 (.split 12 1 (.split 16 1 (.step 52 (.split 21 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 54 1 (.step 18 (.step 53 (.close 3))) (.step 53 (.close 31))) (.step 31 (.close 12))) (.step 31 (.close 12))) (.step 15 (.close 31))) (.step 3 (.close 53)))) (.step 18 (.close 21))) (.step 15 (.close 53))) (.step 26 (.step 31 (.step 40 (.step 53 (.close 75))))))))))) (.run (.step 3 (.step 12 (.step 52 (.step 57 (.split 72 2 (.split 68 1 (.split 16 1 (.step 52 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 54 1 (.step 18 (.step 52 (.close 18))) (.step 12 (.step 52 (.close 3)))) (.step 31 (.close 12))) (.step 31 (.close 12))) (.step 12 (.step 31 (.step 52 (.step 18 (.close 26)))))) (.step 15 (.close 31)))) (.step 18 (.close 21))) (.step 18 (.close 52))) (.step 26 (.step 31 (.step 38 (.step 40 (.step 52 (.close 75))))))))))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4294967296, 22062609072975435583028631289050242477408899362913360780759701718906196071722981281654683816466216116414183168122039526655296860369470163090524725501036342791423138815180716573868412475674325410892547717959917638778880⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.split 12 2 (.step 18 (.step 71 (.split 21 2 (.reuse 0) (.run (.step 3 (.step 31 (.step 57 (.split 35 2 (.split 49 2 (.split 50 2 (.split 59 2 (.step 24 (.split 72 2 (.step 24 (.split 61 2 (.split 62 2 (.step 57 (.step 71 (.split 69 2 (.split 12 1 (.split 54 1 (.split 61 1 (.step 4 (.step 3 (.step 4 (.step 18 (.close 12))))) (.step 4 (.close 64))) (.step 4 (.close 57))) (.step 4 (.close 15))) (.step 24 (.step 43 (.step 64 (.step 3 (.close 65)))))))) (.step 24 (.close 65))) (.step 24 (.close 64)))) (.step 4 (.step 15 (.step 18 (.close 75)))))) (.step 3 (.step 15 (.step 18 (.step 52 (.step 53 (.step 24 (.close 62)))))))) (.step 4 (.step 15 (.step 18 (.step 53 (.close 24)))))) (.step 4 (.step 12 (.step 18 (.close 52))))) (.step 15 (.step 18 (.step 31 (.step 38 (.close 24))))))))))))) (.run (.step 15 (.step 18 (.step 9 (.step 21 (.step 15 (.step 3 (.step 22 (.step 24 (.step 26 (.step 31 (.step 71 (.split 62 2 (.split 61 2 (.split 62 1 (.step 15 (.step 3 (.step 4 (.step 15 (.close 71))))) (.step 4 (.step 15 (.close 65)))) (.step 15 (.close 64))) (.step 4 (.step 21 (.step 64 (.step 15 (.step 57 (.close 65))))))))))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part6.excludes
end FiveColour.Packed.ProjectedChunks.Case145
