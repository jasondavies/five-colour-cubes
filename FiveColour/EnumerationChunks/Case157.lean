module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case157
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582725106862932750327987969825813665638203742725676240020156477489167991036149025554405274496498519322323517839564621150199447250527139290174589548986630144000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 65 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 74 1 (.step 7 (.step 3 (.close 37))) (.step 3 (.split 10 0 (.step 11 (.step 69 (.step 3 (.step 7 (.close 17))))) (.step 3 (.close 7))))) (.step 7 (.step 3 (.close 19)))) (.step 7 (.split 10 0 (.step 11 (.step 67 (.step 3 (.step 7 (.close 19))))) (.step 3 (.step 7 (.close 17)))))) (.split 74 1 (.split 10 0 (.step 29 (.split 14 0 (.step 7 (.step 38 (.step 3 (.step 15 (.close 37))))) (.step 3 (.step 69 (.step 3 (.close 19)))))) (.step 3 (.step 7 (.close 37)))) (.step 11 (.step 23 (.close 69))))) (.step 3 (.split 34 0 (.split 16 0 (.step 3 (.step 74 (.close 3))) (.step 3 (.step 19 (.close 20)))) (.step 3 (.step 15 (.close 39)))))) (.split 65 1 (.split 72 1 (.split 74 1 (.split 10 0 (.step 74 (.close 3)) (.step 3 (.close 66))) (.step 11 (.step 69 (.close 74)))) (.step 29 (.step 69 (.close 74)))) (.step 3 (.close 74)))) (.step 3 (.step 7 (.close 3)))) (.step 67 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 14 0 (.step 3 (.step 29 (.step 66 (.step 3 (.close 19))))) (.step 67 (.close 3))) (.step 11 (.step 67 (.close 3)))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.close 67)))))) (.step 66 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.step 3 (.step 29 (.close 66))) (.step 66 (.close 3))) (.step 3 (.close 66))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.close 66)))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284971109347745694313144495698113782212194144467153126322106969901841642152822261340901969221382934224903470055424⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.reuse 0) (.run (.step 3 (.step 55 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.close 51))))))) (.run (.step 3 (.step 55 (.split 51 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 9 (.step 11 (.close 9))))) (.step 3 (.step 7 (.close 3)))))))) (.run (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 72 1 (.split 14 0 (.step 7 (.step 15 (.close 37))) (.step 3 (.step 7 (.close 37)))) (.step 29 (.step 75 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 37 (.close 69))))) (.step 29 (.step 69 (.step 74 (.split 10 0 (.step 69 (.close 74)) (.step 3 (.step 37 (.close 39)))))))) (.step 3 (.step 45 (.step 39 (.step 15 (.close 69)))))) (.step 29 (.step 67 (.step 69 (.split 65 1 (.split 10 0 (.step 67 (.close 3)) (.step 3 (.step 37 (.close 39)))) (.step 3 (.step 45 (.step 15 (.step 39 (.close 67))))))))))) (.step 3 (.step 29 (.step 66 (.step 3 (.close 45)))))) (.step 3 (.close 7))) (.step 3 (.close 7)))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710571549221520149702034641977677192813174361847375949345432920381318993606501990400⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.reuse 0) (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 72 1 (.split 14 0 (.step 7 (.step 15 (.close 37))) (.step 3 (.step 7 (.close 37)))) (.step 29 (.step 75 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 37 (.close 69))))) (.step 29 (.step 74 (.close 3)))) (.step 3 (.close 39))) (.step 29 (.step 67 (.step 74 (.step 75 (.split 65 1 (.split 10 0 (.step 51 (.close 67)) (.step 3 (.close 37))) (.step 3 (.step 15 (.close 39)))))))))) (.step 3 (.step 29 (.step 66 (.step 3 (.close 39)))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.step 39 (.split 65 1 (.split 74 1 (.split 71 1 (.split 63 1 (.step 39 (.step 29 (.split 10 0 (.split 14 0 (.step 39 (.close 3)) (.step 3 (.step 37 (.close 39)))) (.step 3 (.step 7 (.close 39)))))) (.step 29 (.step 37 (.step 39 (.step 51 (.step 45 (.step 39 (.close 66)))))))) (.step 29 (.step 39 (.step 37 (.step 66 (.step 37 (.close 67))))))) (.step 3 (.step 7 (.step 45 (.step 66 (.step 37 (.step 67 (.step 37 (.close 74))))))))) (.step 3 (.step 39 (.close 66)))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878621701000088909131876905224388669307493450465302002849734043909010401935780749597003795660800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 72 1 (.split 14 0 (.step 7 (.step 15 (.close 37))) (.step 3 (.step 7 (.close 37)))) (.step 29 (.step 37 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 37 (.step 17 (.step 39 (.step 45 (.close 66)))))))) (.step 29 (.step 66 (.step 74 (.close 3))))) (.step 3 (.step 15 (.step 37 (.close 74))))) (.step 29 (.step 66 (.step 67 (.step 3 (.step 37 (.close 3)))))))) (.step 3 (.step 29 (.close 66)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.step 37 (.split 65 1 (.split 74 1 (.split 63 1 (.split 14 0 (.step 45 (.step 29 (.step 39 (.step 66 (.step 45 (.close 3)))))) (.step 3 (.step 7 (.step 37 (.close 67))))) (.step 15 (.step 37 (.close 66)))) (.step 3 (.step 7 (.step 45 (.step 17 (.step 66 (.close 67))))))) (.step 3 (.step 15 (.step 37 (.close 67)))))))) (.step 7 (.step 37 (.split 63 1 (.split 64 1 (.step 39 (.step 3 (.step 7 (.step 37 (.step 17 (.step 39 (.close 66))))))) (.step 29 (.step 66 (.step 39 (.step 3 (.step 37 (.step 39 (.step 17 (.close 67))))))))) (.step 15 (.step 37 (.close 66))))))) (.step 7 (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173670077078685654501933695668785984680049459756317080512933709979058176⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.step 29 (.split 14 0 (.step 7 (.step 38 (.close 3))) (.step 3 (.step 38 (.step 3 (.close 19)))))) (.step 3 (.step 7 (.close 37)))) (.step 11 (.step 23 (.step 69 (.step 3 (.step 38 (.step 3 (.close 19)))))))) (.step 29 (.close 38))) (.step 29 (.step 38 (.step 74 (.close 3))))) (.step 3 (.step 40 (.step 9 (.step 7 (.step 3 (.close 38))))))) (.step 3 (.close 38))) (.step 29 (.step 38 (.step 67 (.close 3))))) (.step 29 (.step 38 (.step 66 (.close 3))))) (.step 3 (.step 40 (.step 9 (.step 38 (.step 51 (.step 3 (.close 7)))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))) (.reuse 1)) (.run (.step 3 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67)))) (.step 3 (.close 66))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.close 7))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351416920862357228923406966562077843489298713778954698752⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.reuse 0) (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 35 0 (.step 7 (.step 11 (.step 17 (.close 19)))) (.step 3 (.step 7 (.close 19)))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.close 69))))) (.step 11 (.step 69 (.step 74 (.split 10 0 (.step 69 (.close 74)) (.step 3 (.step 17 (.close 19)))))))) (.step 3 (.step 25 (.step 20 (.step 19 (.close 69)))))) (.step 11 (.step 67 (.step 3 (.close 25)))))) (.step 3 (.step 11 (.step 66 (.step 69 (.split 65 1 (.split 10 0 (.step 69 (.step 66 (.close 3))) (.step 3 (.step 17 (.close 19)))) (.step 3 (.step 25 (.step 19 (.step 20 (.close 66))))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 69 (.step 40 (.step 38 (.step 74 (.step 7 (.step 19 (.close 20)))))))))))) (.step 3 (.close 7))) (.step 3 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173670077078685654503430273345412829268290033025018554325061384903065600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 35 0 (.step 7 (.step 11 (.step 17 (.close 19)))) (.step 3 (.step 7 (.close 19)))) (.step 11 (.step 77 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.close 69))))) (.step 11 (.step 74 (.close 3)))) (.step 3 (.close 20))) (.step 11 (.step 67 (.step 3 (.close 20)))))) (.step 3 (.step 11 (.step 66 (.step 74 (.step 77 (.split 65 1 (.split 10 0 (.step 51 (.step 66 (.close 3))) (.step 3 (.close 17))) (.step 3 (.step 19 (.close 20)))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 19 (.step 25 (.close 38)))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351416922323858866254309884765762676205581733434887241728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 35 0 (.step 7 (.step 11 (.step 17 (.close 19)))) (.step 3 (.step 7 (.close 19)))) (.step 11 (.step 19 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.step 20 (.step 25 (.step 38 (.close 67)))))))) (.step 11 (.step 67 (.step 74 (.close 3))))) (.step 3 (.step 19 (.close 74)))) (.step 11 (.close 67)))) (.step 3 (.step 11 (.step 66 (.step 67 (.step 66 (.step 3 (.step 19 (.close 3))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 38 (.step 11 (.step 23 (.step 66 (.step 67 (.step 7 (.step 19 (.step 38 (.step 19 (.close 74))))))))))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.step 19 (.split 35 1 (.split 65 1 (.split 72 1 (.split 64 1 (.split 34 0 (.step 19 (.step 11 (.step 20 (.step 66 (.step 19 (.close 3)))))) (.step 7 (.step 17 (.close 19)))) (.step 11 (.step 19 (.step 66 (.close 67))))) (.step 3 (.step 7 (.step 25 (.step 38 (.step 66 (.close 67))))))) (.step 3 (.step 19 (.close 66)))) (.step 3 (.step 7 (.step 19 (.step 38 (.close 66))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901535493098898125339031377679393861109811249152⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 3 := (.split 16 1 (.split 17 1 (.reuse 0) (.split 22 1 (.reuse 1) (.run (.step 7 (.step 25 (.split 35 1 (.split 65 1 (.split 72 1 (.split 71 1 (.split 64 1 (.step 20 (.step 11 (.split 10 0 (.split 14 0 (.split 30 0 (.step 74 (.step 25 (.close 3))) (.step 3 (.step 7 (.step 19 (.close 20))))) (.step 17 (.step 20 (.close 19)))) (.step 3 (.step 7 (.step 17 (.step 19 (.close 20)))))))) (.step 11 (.step 19 (.step 20 (.step 51 (.step 25 (.step 20 (.close 66)))))))) (.step 11 (.step 20 (.step 19 (.step 66 (.step 19 (.close 67))))))) (.step 3 (.step 7 (.step 25 (.step 66 (.step 19 (.step 67 (.step 19 (.close 74))))))))) (.step 3 (.step 20 (.close 66)))) (.step 3 (.step 7 (.step 19 (.step 66 (.step 20 (.step 25 (.step 38 (.close 74)))))))))))))) (.split 17 1 (.reuse 2) (.run (.step 7 (.step 19 (.split 35 1 (.split 63 1 (.split 64 1 (.step 20 (.step 3 (.step 7 (.step 19 (.step 20 (.step 38 (.close 67))))))) (.step 11 (.step 19 (.close 67)))) (.step 11 (.step 66 (.step 19 (.close 3))))) (.step 3 (.step 7 (.step 19 (.step 38 (.close 66)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460183827084136443896789531466851308460946267023810258800930402015142566826945994187336382264144254782668800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.step 11 (.split 16 0 (.step 3 (.split 17 0 (.split 22 0 (.step 3 (.step 17 (.close 37))) (.step 3 (.close 7))) (.step 7 (.step 3 (.close 17))))) (.step 17 (.step 3 (.step 7 (.close 17)))))) (.step 3 (.step 7 (.close 17)))) (.step 11 (.close 17))) (.step 11 (.step 17 (.step 23 (.step 69 (.step 3 (.step 17 (.step 3 (.close 37))))))))) (.step 11 (.step 17 (.step 74 (.close 3))))) (.step 3 (.step 23 (.step 11 (.step 7 (.step 3 (.close 17))))))) (.step 3 (.close 17))) (.step 11 (.step 17 (.step 67 (.close 3))))) (.step 11 (.step 17 (.step 66 (.close 3))))) (.step 3 (.step 23 (.step 11 (.step 17 (.step 51 (.step 3 (.close 7)))))))) (.step 3 (.step 11 (.close 7)))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 69 (.step 23 (.step 17 (.step 74 (.step 7 (.step 37 (.close 39)))))))))))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 37 (.step 17 (.step 39 (.close 45))))))))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 75 (.step 77 (.step 29 (.step 38 (.step 23 (.split 10 0 (.split 34 0 (.split 16 0 (.split 30 0 (.split 17 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.step 17 (.close 37)))) (.step 3 (.close 17))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473034770628323890015303129108578304⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 1) (.run (.step 3 (.step 7 (.step 66 (.step 67 (.step 74 (.step 7 (.step 38 (.step 37 (.step 69 (.step 17 (.step 37 (.close 17)))))))))))))) (.run (.step 3 (.step 7 (.step 67 (.split 63 1 (.step 7 (.step 3 (.close 17))) (.step 3 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 7 (.step 17 (.close 19))))))))) (.run (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.step 7 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66)))) (.step 3 (.close 66))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 66 (.split 64 1 (.step 7 (.step 3 (.close 38))) (.step 3 (.close 38))))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 17 (.step 3 (.close 7)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part10.excludes
end FiveColour.Packed.EnumerationChunks.Case157
