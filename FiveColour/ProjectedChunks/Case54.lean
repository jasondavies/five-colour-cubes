module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case54
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473034770628323890015303129108578304⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334835886793856427426709802302643992082965358552532360516319954545687682355986065970569142177816300267095233487778479729227855822848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 65 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 74 1 (.step 7 (.step 3 (.close 37))) (.split 10 0 (.step 11 (.step 69 (.step 3 (.close 17)))) (.step 3 (.close 7)))) (.step 7 (.close 19))) (.step 7 (.split 10 0 (.step 11 (.step 67 (.step 7 (.close 19)))) (.step 7 (.close 17))))) (.split 74 1 (.split 10 0 (.step 29 (.split 14 0 (.step 7 (.close 75)) (.step 3 (.close 75)))) (.step 3 (.step 7 (.close 37)))) (.step 23 (.close 69)))) (.split 34 0 (.split 16 0 (.step 3 (.step 74 (.close 3))) (.step 3 (.step 19 (.close 20)))) (.step 3 (.step 15 (.close 39))))) (.split 72 1 (.split 74 1 (.split 10 0 (.step 74 (.close 3)) (.step 3 (.close 66))) (.step 11 (.step 69 (.close 74)))) (.step 29 (.step 69 (.close 74))))) (.step 3 (.step 7 (.close 3)))) (.step 67 (.split 65 1 (.split 72 1 (.split 74 1 (.split 14 0 (.step 3 (.close 67)) (.step 67 (.close 3))) (.step 67 (.close 3))) (.step 67 (.close 3))) (.step 3 (.close 67))))) (.step 66 (.split 65 1 (.split 72 1 (.split 74 1 (.split 14 0 (.step 3 (.close 66)) (.step 66 (.close 3))) (.step 66 (.close 3))) (.step 66 (.close 3))) (.step 3 (.close 66))))) (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.close 51)))) (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 9 (.step 3 (.close 11)))) (.step 3 (.close 47)))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710571549221520149702034641977677192813174361847375949345432920381318993606501990400⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.reuse 0) (.run (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 72 1 (.split 14 0 (.step 7 (.close 37)) (.step 7 (.close 37))) (.step 75 (.close 7))) (.step 7 (.step 37 (.close 69)))) (.step 29 (.step 69 (.split 10 0 (.step 69 (.close 74)) (.step 3 (.close 45)))))) (.step 3 (.step 45 (.step 39 (.step 15 (.close 69)))))) (.step 29 (.step 67 (.step 69 (.split 65 1 (.split 10 0 (.step 67 (.close 3)) (.step 3 (.close 45))) (.step 3 (.close 67)))))))) (.step 3 (.step 29 (.step 66 (.step 3 (.close 45)))))))) (.run (.split 42 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 72 1 (.split 14 0 (.step 7 (.close 37)) (.step 7 (.close 37))) (.step 75 (.close 7))) (.step 7 (.step 37 (.close 69)))) (.step 74 (.close 3))) (.step 3 (.close 39))) (.step 29 (.step 74 (.step 75 (.split 65 1 (.split 10 0 (.step 51 (.close 67)) (.step 3 (.close 37))) (.step 3 (.close 39)))))))) (.step 3 (.step 29 (.step 66 (.step 3 (.close 39)))))) (.step 7 (.split 65 1 (.split 74 1 (.split 71 1 (.split 63 1 (.step 39 (.split 14 0 (.step 39 (.close 3)) (.step 3 (.step 37 (.close 39))))) (.step 37 (.step 39 (.step 51 (.step 45 (.close 66)))))) (.step 39 (.close 74))) (.step 45 (.step 66 (.step 37 (.close 74))))) (.step 3 (.step 39 (.close 66))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878621701000088909131876905224388669307493450465302002849734043909010401935780749597003795660800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 72 1 (.split 14 0 (.step 7 (.close 37)) (.step 7 (.close 37))) (.step 37 (.close 7))) (.step 7 (.step 37 (.close 69)))) (.step 29 (.step 66 (.step 74 (.close 3))))) (.step 3 (.step 37 (.close 74)))) (.step 29 (.step 66 (.step 67 (.step 37 (.close 3))))))) (.step 3 (.step 29 (.close 66)))) (.step 7 (.split 65 1 (.split 74 1 (.split 63 1 (.split 14 0 (.step 45 (.step 66 (.step 45 (.close 3)))) (.step 37 (.close 67))) (.step 37 (.close 66))) (.step 45 (.step 17 (.step 66 (.close 67))))) (.step 3 (.step 37 (.close 67)))))) (.step 7 (.split 63 1 (.split 64 1 (.step 39 (.step 7 (.step 37 (.close 74)))) (.step 66 (.step 39 (.step 3 (.close 67))))) (.step 37 (.close 66))))) (.step 29 (.step 37 (.step 38 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351416920862357228923406966562077843489298713778954698752⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.step 29 (.split 14 0 (.step 7 (.step 38 (.close 3))) (.step 3 (.step 38 (.close 19))))) (.step 3 (.step 7 (.close 37)))) (.step 23 (.step 69 (.step 38 (.close 19))))) (.step 29 (.close 38))) (.step 74 (.close 3))) (.step 3 (.step 40 (.step 9 (.step 7 (.close 38)))))) (.step 3 (.close 38))) (.step 38 (.step 67 (.close 3)))) (.step 66 (.close 3))) (.step 51 (.step 3 (.close 7)))) (.step 3 (.step 9 (.close 7)))) (.step 29 (.step 38 (.close 7)))) (.step 29 (.step 38 (.close 7)))))) (.reuse 1)) (.run (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67))) (.step 3 (.close 66))) (.step 38 (.step 3 (.close 7)))))) (.run (.split 35 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 35 0 (.step 7 (.close 19)) (.step 7 (.close 19))) (.step 77 (.close 7))) (.step 7 (.step 19 (.close 69)))) (.step 11 (.step 69 (.split 10 0 (.step 69 (.close 74)) (.step 3 (.close 25)))))) (.step 3 (.step 25 (.step 20 (.step 19 (.close 69)))))) (.step 11 (.step 67 (.step 3 (.close 25)))))) (.step 3 (.step 11 (.step 66 (.step 69 (.split 10 0 (.step 69 (.step 66 (.close 3))) (.step 3 (.close 25)))))))) (.step 66 (.step 67 (.step 69 (.step 40 (.step 38 (.step 74 (.step 7 (.step 19 (.close 20))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418417440033855767995207135346544963110841453878706176⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.reuse 0) (.run (.split 22 1 (.split 35 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 35 0 (.step 7 (.close 19)) (.step 7 (.close 19))) (.step 77 (.close 7))) (.step 7 (.step 19 (.close 69)))) (.step 74 (.close 3))) (.step 3 (.close 20))) (.step 11 (.step 67 (.step 3 (.close 20)))))) (.step 3 (.step 11 (.step 66 (.step 74 (.step 77 (.split 65 1 (.split 10 0 (.step 51 (.step 66 (.close 3))) (.step 3 (.close 17))) (.step 3 (.close 20))))))))) (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 19 (.close 69)))))))) (.step 7 (.split 35 1 (.split 65 1 (.split 72 1 (.split 71 1 (.split 64 1 (.step 20 (.step 11 (.split 10 0 (.split 30 0 (.step 74 (.step 25 (.close 3))) (.step 7 (.close 20))) (.step 7 (.close 20))))) (.step 19 (.step 20 (.step 51 (.step 25 (.close 66)))))) (.step 20 (.close 74))) (.step 25 (.step 66 (.step 19 (.close 74))))) (.step 3 (.step 20 (.close 66)))) (.step 19 (.step 66 (.step 20 (.step 25 (.close 75))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473033502977723661785901632405372928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.step 11 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.close 37)) (.step 3 (.close 7))) (.step 7 (.close 17))) (.step 17 (.step 7 (.close 17))))) (.step 7 (.close 17))) (.step 11 (.close 17))) (.step 17 (.step 23 (.step 69 (.step 17 (.close 37)))))) (.step 74 (.close 3))) (.step 3 (.step 23 (.step 11 (.step 7 (.close 17)))))) (.step 67 (.close 3))) (.step 17 (.step 66 (.close 3)))) (.step 51 (.step 3 (.close 7)))) (.step 3 (.step 11 (.close 7)))) (.step 66 (.step 67 (.step 69 (.step 23 (.step 17 (.step 74 (.step 7 (.step 37 (.close 39)))))))))) (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 37 (.close 77)))))))) (.step 66 (.step 67 (.step 74 (.step 77 (.step 38 (.step 23 (.split 17 0 (.step 38 (.close 17)) (.step 3 (.close 17)))))))))) (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 38 (.step 37 (.step 69 (.step 37 (.close 17))))))))))) (.step 3 (.step 67 (.split 63 1 (.step 7 (.step 3 (.close 17))) (.step 3 (.close 17)))))) (.step 11 (.step 17 (.step 7 (.close 17))))) (.step 11 (.step 17 (.step 7 (.close 17))))) (.step 11 (.step 17 (.step 7 (.close 19))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473034770628323890015303129108578304⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.run (.split 17 1 (.split 22 1 (.split 35 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 35 0 (.step 7 (.close 19)) (.step 7 (.close 19))) (.step 19 (.close 7))) (.step 7 (.step 19 (.close 69)))) (.step 11 (.step 67 (.step 74 (.close 3))))) (.step 3 (.step 19 (.close 74)))) (.step 11 (.close 67)))) (.step 3 (.step 11 (.step 67 (.step 66 (.step 19 (.close 3))))))) (.step 38 (.step 23 (.step 66 (.step 67 (.step 7 (.step 19 (.step 38 (.step 19 (.close 74)))))))))) (.step 7 (.split 35 1 (.split 72 1 (.split 64 1 (.split 34 0 (.step 19 (.step 11 (.step 20 (.step 66 (.step 19 (.close 3)))))) (.step 7 (.close 19))) (.step 19 (.close 67))) (.step 25 (.step 38 (.step 66 (.close 67))))) (.step 19 (.step 38 (.close 66)))))) (.step 7 (.split 35 1 (.split 63 1 (.split 64 1 (.step 20 (.step 7 (.step 19 (.close 74)))) (.step 19 (.close 67))) (.step 66 (.step 19 (.close 3)))) (.step 19 (.step 38 (.close 66)))))))) (.reuse 1)) (.run (.split 14 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.step 66 (.split 64 1 (.step 7 (.step 3 (.close 38))) (.step 3 (.close 38)))))) (.step 17 (.step 3 (.close 7))))))
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
end FiveColour.Packed.ProjectedChunks.Case54
