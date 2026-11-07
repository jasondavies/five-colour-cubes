module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case56
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644320647064274132271104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660749386805549175884476045519682621152070220555079396390043072223356798867117014992814086484636469259678209525254359177288413835952018510578314660701798400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 16 0 (.step 7 (.split 10 0 (.split 12 0 (.step 7 (.close 21)) (.step 9 (.step 18 (.step 15 (.close 75))))) (.step 7 (.close 15)))) (.split 17 0 (.step 7 (.step 18 (.close 7))) (.step 7 (.close 18)))) (.split 72 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 70))) (.step 7 (.step 9 (.close 75))))) (.split 67 1 (.split 72 1 (.split 16 0 (.split 12 0 (.step 7 (.close 21)) (.step 9 (.step 18 (.close 62)))) (.step 18 (.step 7 (.close 9)))) (.step 26 (.close 7))) (.step 62 (.close 7)))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 34 0 (.split 12 0 (.step 7 (.step 9 (.close 18))) (.step 9 (.close 57))) (.step 15 (.step 7 (.close 21)))) (.step 9 (.step 26 (.step 18 (.close 21))))) (.step 57 (.split 12 0 (.step 70 (.close 7)) (.step 9 (.step 26 (.close 57)))))) (.step 9 (.step 26 (.step 18 (.close 57)))))) (.split 67 1 (.split 72 1 (.split 59 1 (.split 54 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 54))) (.step 57 (.close 7))) (.step 62 (.close 7))) (.step 7 (.step 26 (.step 54 (.close 57))))) (.step 54 (.step 7 (.step 54 (.close 57)))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106416804706180239593862104121686846717430938697033110655389288545372543552506476761919575670309819382995538502452966143971844685824⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 10 0 (.step 9 (.step 18 (.close 53))) (.step 7 (.close 15))) (.step 18 (.step 7 (.close 9)))) (.step 18 (.step 7 (.close 9)))) (.step 9 (.step 38 (.step 18 (.close 75))))) (.step 53 (.close 7))) (.step 53 (.close 7))) (.step 53 (.step 57 (.close 7)))) (.step 53 (.close 7))))) (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 16 0 (.split 12 0 (.step 7 (.close 21)) (.step 9 (.step 18 (.close 52)))) (.step 18 (.step 7 (.close 9)))) (.step 9 (.step 40 (.step 26 (.close 52))))) (.step 52 (.close 7))) (.step 52 (.close 7))) (.step 52 (.step 57 (.close 7)))) (.step 52 (.close 7))) (.step 52 (.close 7))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 59 1 (.split 54 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 70 (.close 9))) (.step 54 (.close 9))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46))))))
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

namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125759709371322780837965323211321688290854149386895838498087984163607854340895065245737935055805408350490853376⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.split 34 0 (.split 36 0 (.step 7 (.close 26)) (.split 49 0 (.step 7 (.close 39)) (.step 7 (.step 21 (.close 26))))) (.split 54 1 (.split 49 0 (.step 7 (.close 45)) (.step 7 (.close 37))) (.step 15 (.step 26 (.step 7 (.close 45)))))) (.step 26 (.step 29 (.step 40 (.step 45 (.step 18 (.step 26 (.step 37 (.close 57))))))))) (.step 26 (.step 55 (.step 9 (.step 53 (.step 38 (.step 45 (.step 18 (.step 26 (.close 57)))))))))) (.step 26 (.step 55 (.step 52 (.step 18 (.step 26 (.step 37 (.close 52))))))))))) (.run (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 34 0 (.split 42 0 (.step 7 (.close 57)) (.split 49 0 (.step 7 (.close 39)) (.step 7 (.step 21 (.close 26))))) (.split 54 1 (.split 49 0 (.step 7 (.close 39)) (.step 7 (.close 37))) (.step 15 (.step 39 (.close 7))))) (.step 57 (.step 7 (.close 62)))) (.step 57 (.step 7 (.step 38 (.close 62))))) (.step 57 (.split 72 1 (.step 55 (.close 52)) (.step 7 (.close 75))))) (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 45 (.close 57)))) (.step 7 (.step 57 (.step 45 (.close 62))))) (.step 7 (.step 26 (.step 57 (.step 45 (.step 38 (.close 52)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513087281144589659270946239224073530504013861256652436342227563024910706950455236011747784523776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 21 0 (.split 36 0 (.split 49 0 (.step 7 (.step 15 (.step 7 (.close 21)))) (.step 7 (.step 15 (.close 26)))) (.split 54 1 (.split 49 0 (.step 7 (.step 29 (.close 37))) (.step 7 (.close 37))) (.step 29 (.step 37 (.close 57))))) (.step 7 (.close 37))) (.step 15 (.step 7 (.step 26 (.close 57))))) (.step 15 (.step 57 (.step 7 (.step 38 (.close 62)))))) (.step 15 (.step 52 (.step 7 (.step 26 (.step 52 (.close 37))))))) (.split 49 1 (.split 50 1 (.split 54 1 (.step 37 (.step 7 (.close 37))) (.step 29 (.step 37 (.step 7 (.close 57))))) (.step 7 (.step 37 (.close 62)))) (.step 52 (.step 37 (.close 52))))) (.split 49 1 (.step 45 (.split 50 1 (.step 39 (.step 7 (.step 15 (.step 39 (.close 52))))) (.step 7 (.step 15 (.step 37 (.step 52 (.step 45 (.step 26 (.close 53))))))))) (.step 37 (.step 52 (.step 37 (.close 52)))))) (.step 38 (.step 7 (.close 37))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429148918254945690599483432967365594029418708386292170752⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 21 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 18 (.split 10 0 (.step 29 (.step 38 (.close 7))) (.step 7 (.close 15)))) (.step 29 (.close 38))) (.step 7 (.step 9 (.close 75)))) (.step 9 (.step 26 (.step 40 (.step 26 (.close 38)))))) (.step 57 (.close 7))) (.step 57 (.step 7 (.step 9 (.step 26 (.close 38)))))) (.step 21 (.step 38 (.step 18 (.close 53))))) (.step 9 (.step 53 (.step 57 (.step 75 (.step 52 (.step 40 (.step 38 (.close 26))))))))) (.step 9 (.close 7))) (.step 29 (.step 38 (.step 7 (.close 37))))) (.step 29 (.step 38 (.step 7 (.close 38))))))) (.reuse 1)) (.run (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.close 53)))) (.step 18 (.step 53 (.step 7 (.step 18 (.close 52)))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 26 (.step 18 (.close 7)))) (.step 18 (.step 26 (.step 55 (.step 27 (.close 52))))))))) (.run (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 34 1 (.split 36 1 (.split 42 1 (.step 7 (.step 9 (.close 54))) (.step 7 (.close 15))) (.step 7 (.close 39))) (.step 7 (.close 37))) (.step 18 (.step 26 (.close 37)))) (.step 9 (.step 18 (.close 62)))) (.step 57 (.close 7))) (.step 9 (.step 18 (.close 53)))) (.step 9 (.step 18 (.close 52)))) (.step 18 (.step 38 (.close 37)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303819740104044092417662777429065728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 18 (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 35 0 (.step 7 (.close 15)) (.step 15 (.close 7))) (.step 15 (.close 7))) (.step 15 (.close 7))) (.step 15 (.split 21 0 (.split 35 0 (.step 70 (.close 7)) (.step 7 (.close 15))) (.step 7 (.close 15))))) (.step 15 (.close 62)))) (.step 15 (.close 18))) (.step 7 (.step 15 (.step 57 (.step 62 (.step 70 (.split 21 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 15))) (.step 7 (.close 15))))))))) (.step 21 (.step 22 (.step 15 (.close 53))))) (.step 21 (.step 22 (.step 15 (.close 52))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.split 21 1 (.split 16 0 (.step 15 (.close 7)) (.step 7 (.close 15))) (.step 7 (.close 15))))) (.step 7 (.step 15 (.step 29 (.step 57 (.step 37 (.step 7 (.step 15 (.close 39))))))))) (.step 15 (.step 18 (.step 15 (.close 38))))) (.step 7 (.step 15 (.close 7)))) (.step 18 (.step 15 (.close 52)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644320647064274132271104⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.split 22 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 22 (.step 18 (.close 7)))) (.step 18 (.step 22 (.step 55 (.step 27 (.close 52)))))) (.step 7 (.step 18 (.close 53))))))) (.run (.split 17 1 (.split 22 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 21 (.step 18 (.close 7)))) (.step 21 (.step 53 (.step 18 (.close 7))))) (.step 7 (.step 18 (.close 53)))) (.step 7 (.split 35 1 (.step 18 (.step 19 (.step 25 (.close 53)))) (.step 18 (.close 19))))))) (.reuse 1)) (.run (.step 7 (.split 12 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.step 15 (.close 18))))) (.step 18 (.step 52 (.close 7)))) (.step 15 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part6.excludes
end FiveColour.Packed.ProjectedChunks.Case56
