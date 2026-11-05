module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case203
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891007115968910814577287456568148754432⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11519759214886988329712, 5265277774370127436459349584068739266192120946542279668661627859253734152924371453712738166804696987248258691298635655720769798495402573058864266597235872468271864526934913852805176730168410353023445446577619968, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890875659729952015703925111304360980212832583822965135058339895762223104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 35 0 (.split 36 0 (.split 53 0 (.split 56 0 (.split 74 0 (.split 30 0 (.step 28 (.step 3 (.close 15))) (.step 3 (.step 28 (.close 37)))) (.step 3 (.step 28 (.close 37)))) (.step 28 (.step 48 (.step 45 (.close 3))))) (.step 51 (.step 3 (.close 28)))) (.step 51 (.split 44 0 (.step 39 (.step 3 (.step 16 (.step 3 (.close 37))))) (.step 51 (.step 28 (.close 3)))))) (.split 38 0 (.split 42 0 (.step 29 (.split 53 0 (.split 30 0 (.step 38 (.step 3 (.step 15 (.close 37)))) (.step 3 (.step 37 (.close 38)))) (.step 3 (.step 37 (.close 38))))) (.step 69 (.step 45 (.step 29 (.step 3 (.step 15 (.close 37))))))) (.split 34 0 (.split 36 0 (.split 53 0 (.step 29 (.close 38)) (.step 3 (.step 28 (.close 38)))) (.step 39 (.step 28 (.close 38)))) (.split 30 0 (.split 36 0 (.step 28 (.close 38)) (.step 37 (.step 28 (.close 38)))) (.step 3 (.step 28 (.step 37 (.close 38)))))))) (.split 30 0 (.split 38 0 (.step 29 (.close 3)) (.step 28 (.close 29))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 28 (.step 3 (.step 4 (.step 10 (.close 28))))) (.step 3 (.close 28))) (.step 29 (.close 3))) (.step 3 (.step 38 (.step 29 (.close 3))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620408855669430763527990259413193017656247639661871104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 35 0 (.step 51 (.split 30 0 (.split 34 0 (.step 3 (.step 5 (.step 28 (.close 38)))) (.step 3 (.step 39 (.step 3 (.step 28 (.close 37)))))) (.step 3 (.step 33 (.step 3 (.close 20)))))) (.split 30 0 (.step 51 (.split 38 0 (.step 29 (.step 3 (.step 37 (.close 38)))) (.step 3 (.step 28 (.close 38))))) (.step 3 (.step 4 (.step 3 (.step 11 (.close 15))))))) (.split 30 0 (.split 34 0 (.step 51 (.close 29)) (.step 3 (.split 36 0 (.step 29 (.close 3)) (.step 7 (.step 28 (.close 29)))))) (.step 3 (.step 4 (.step 3 (.close 7)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.step 69 (.split 35 0 (.step 3 (.step 5 (.step 3 (.close 8)))) (.step 3 (.step 4 (.step 3 (.close 11))))))) (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.close 39)))) (.step 3 (.step 11 (.close 15))))) (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 20 (.close 3))))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 33 (.step 3 (.close 20)))))) (.step 4 (.step 24 (.step 11 (.step 69 (.step 4 (.step 3 (.close 7))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712618913739494441249842667889829324260127139620670406656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 53 0 (.split 56 0 (.step 67 (.close 3)) (.step 5 (.step 28 (.step 3 (.close 38))))) (.step 51 (.step 3 (.close 4)))) (.step 3 (.step 50 (.step 3 (.step 28 (.close 39)))))) (.split 35 0 (.split 36 0 (.step 3 (.step 49 (.step 3 (.step 28 (.close 37))))) (.step 3 (.step 51 (.step 39 (.step 3 (.step 28 (.close 37))))))) (.step 3 (.step 38 (.close 3))))) (.split 34 0 (.split 35 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 11))))) (.step 3 (.step 38 (.step 8 (.close 16)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 47 (.step 3 (.step 4 (.close 28)))) (.step 3 (.close 28))) (.step 29 (.step 3 (.close 4)))) (.step 3 (.step 38 (.step 7 (.close 28))))) (.step 3 (.step 4 (.step 3 (.close 7)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.split 35 0 (.step 69 (.step 3 (.step 5 (.step 3 (.close 8))))) (.step 3 (.step 24 (.step 3 (.step 4 (.close 8))))))) (.split 35 0 (.split 36 0 (.step 3 (.step 23 (.step 3 (.step 8 (.close 14))))) (.step 3 (.step 39 (.close 3)))) (.step 3 (.step 11 (.close 15))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 3 (.step 50 (.close 3))) (.step 3 (.step 19 (.step 3 (.step 19 (.close 3)))))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 33 (.step 3 (.close 20)))))) (.step 4 (.step 24 (.step 11 (.step 67 (.step 3 (.close 4)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317171068094430908463098025733939267295594414080⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.split 35 0 (.split 36 0 (.step 51 (.step 3 (.close 5))) (.step 3 (.step 8 (.close 3)))) (.step 3 (.step 24 (.step 3 (.step 4 (.close 8))))))) (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.close 39)))) (.step 3 (.step 11 (.close 15))))) (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 19 (.step 3 (.step 19 (.close 3))))))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 33 (.step 3 (.close 20)))))) (.step 4 (.step 24 (.step 11 (.step 67 (.step 3 (.close 4))))))) (.split 30 0 (.split 36 0 (.split 26 0 (.split 34 0 (.step 69 (.split 35 0 (.step 51 (.step 19 (.step 3 (.close 8)))) (.step 3 (.close 19)))) (.split 35 0 (.split 38 0 (.step 69 (.split 42 0 (.step 3 (.step 8 (.close 14))) (.step 3 (.step 19 (.close 3))))) (.step 3 (.step 8 (.close 16)))) (.step 3 (.step 11 (.close 15))))) (.step 24 (.step 3 (.step 11 (.step 4 (.close 19)))))) (.step 20 (.close 3))) (.step 19 (.step 20 (.close 3)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890875659729952015703925111305754776787740747769311117450380418356346880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 53 0 (.split 56 0 (.split 34 0 (.step 77 (.step 3 (.close 28))) (.step 29 (.step 3 (.step 5 (.close 37))))) (.step 5 (.step 28 (.step 3 (.close 37))))) (.step 51 (.close 3))) (.step 51 (.step 3 (.step 5 (.step 28 (.close 37)))))) (.split 38 0 (.split 42 0 (.split 36 0 (.split 34 0 (.split 43 0 (.split 53 0 (.step 5 (.step 4 (.step 11 (.close 28)))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 5 (.step 28 (.close 37))))) (.step 3 (.step 5 (.step 28 (.close 37))))) (.step 3 (.step 29 (.step 3 (.step 5 (.close 37)))))) (.step 3 (.step 5 (.step 28 (.step 37 (.close 38))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 53 0 (.step 67 (.close 3)) (.step 3 (.close 8))) (.step 3 (.close 5))) (.step 3 (.step 11 (.step 3 (.close 4))))) (.step 3 (.step 24 (.step 3 (.close 5)))))) (.split 30 0 (.split 34 0 (.split 38 0 (.split 42 0 (.step 47 (.step 4 (.step 28 (.step 5 (.step 15 (.step 5 (.close 29))))))) (.step 3 (.close 29))) (.step 3 (.step 5 (.close 28)))) (.step 3 (.step 29 (.close 3)))) (.step 3 (.step 11 (.step 4 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1461503031127477826367631178698675060179600408576, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891005816627044371716331307818188537856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 53 0 (.step 67 (.close 3)) (.step 8 (.step 14 (.step 3 (.close 5))))) (.step 3 (.step 8 (.close 14)))) (.step 3 (.step 11 (.step 3 (.step 4 (.close 14)))))) (.step 3 (.step 11 (.step 3 (.step 13 (.close 14)))))) (.step 3 (.step 67 (.close 3)))) (.step 3 (.step 11 (.step 24 (.step 67 (.step 3 (.close 4))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.split 35 0 (.split 38 0 (.split 42 0 (.step 11 (.step 3 (.close 14))) (.step 3 (.step 11 (.step 3 (.close 14))))) (.step 3 (.step 5 (.step 8 (.close 14))))) (.step 3 (.step 11 (.step 17 (.step 3 (.step 4 (.step 3 (.close 13))))))))) (.step 3 (.step 17 (.close 3)))) (.step 19 (.step 3 (.step 25 (.close 3))))) (.step 3 (.step 11 (.step 17 (.step 24 (.step 67 (.step 3 (.close 4))))))))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 11 (.step 3 (.close 5))) (.step 3 (.step 11 (.close 3))))) (.step 3 (.step 11 (.step 17 (.close 19))))) (.step 3 (.step 17 (.close 3)))) (.step 19 (.step 3 (.step 20 (.close 3))))) (.step 3 (.step 11 (.step 17 (.step 24 (.step 67 (.step 3 (.close 4)))))))) (.step 19 (.step 20 (.step 3 (.step 4 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891005816627044371716331307818188537856⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 30 0 (.step 69 (.split 38 0 (.split 42 0 (.step 11 (.step 3 (.close 4))) (.step 3 (.step 11 (.step 3 (.close 13))))) (.step 3 (.step 5 (.close 8))))) (.step 3 (.split 34 0 (.step 11 (.step 3 (.step 13 (.close 14)))) (.step 3 (.step 11 (.step 13 (.close 17))))))) (.step 3 (.step 11 (.step 24 (.step 69 (.step 4 (.step 3 (.close 7)))))))))) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 36 0 (.split 35 0 (.step 51 (.step 3 (.close 5))) (.step 3 (.step 11 (.step 3 (.step 4 (.close 14)))))) (.step 3 (.step 11 (.step 3 (.step 13 (.close 14)))))) (.step 3 (.split 34 0 (.step 11 (.step 3 (.step 13 (.close 14)))) (.step 3 (.step 11 (.step 13 (.close 17))))))) (.step 3 (.step 11 (.step 24 (.step 74 (.step 3 (.close 4))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.split 35 0 (.step 51 (.step 3 (.step 5 (.step 3 (.close 11))))) (.step 3 (.step 11 (.step 17 (.step 3 (.step 4 (.step 3 (.close 13))))))))) (.step 3 (.step 17 (.close 3)))) (.step 20 (.step 3 (.step 11 (.close 3))))) (.step 3 (.step 11 (.step 17 (.step 24 (.step 69 (.step 4 (.step 3 (.close 7)))))))))))) (.reuse 1))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1298074214633706907132625156046848, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712618912277992803918941047760359125250751252588820168704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 53 0 (.split 34 0 (.split 38 0 (.step 3 (.close 28)) (.step 5 (.step 28 (.step 3 (.close 37))))) (.step 3 (.step 28 (.close 37)))) (.step 8 (.step 4 (.step 17 (.step 4 (.close 3)))))) (.step 51 (.step 3 (.step 28 (.step 3 (.step 4 (.close 37))))))) (.split 36 0 (.split 53 0 (.step 4 (.step 28 (.step 3 (.close 37)))) (.step 4 (.close 8))) (.step 3 (.step 28 (.step 4 (.step 37 (.close 38))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 53 0 (.step 3 (.close 5)) (.step 8 (.step 3 (.close 4)))) (.step 3 (.step 4 (.step 3 (.close 8))))) (.step 3 (.close 4))) (.step 3 (.step 23 (.step 3 (.close 4)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 47 (.step 4 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 28))) (.step 3 (.close 4)))) (.split 26 0 (.split 30 0 (.split 35 0 (.step 60 (.step 69 (.step 3 (.close 8)))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 3 (.split 34 0 (.step 8 (.step 3 (.step 13 (.close 14)))) (.step 3 (.step 8 (.step 13 (.close 14))))))) (.step 3 (.step 24 (.step 3 (.step 4 (.step 8 (.close 14)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1461501637330904216277899466423190152281088589824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317171068094432206537312659440846399919676719104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 8 (.step 50 (.step 3 (.close 5)))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 3 (.step 8 (.step 3 (.step 13 (.close 14)))))) (.step 3 (.step 50 (.close 3)))) (.step 3 (.step 24 (.step 3 (.step 4 (.step 8 (.close 14))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 60 (.step 69 (.step 3 (.step 5 (.step 3 (.close 8)))))) (.step 3 (.step 4 (.step 8 (.step 14 (.close 17)))))) (.step 3 (.step 14 (.close 3)))) (.step 19 (.step 3 (.step 25 (.close 3))))) (.step 3 (.step 4 (.step 3 (.step 8 (.step 14 (.close 17)))))))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.split 35 0 (.split 36 0 (.step 8 (.step 14 (.step 3 (.close 5)))) (.step 3 (.step 8 (.step 3 (.step 13 (.close 14)))))) (.step 3 (.step 4 (.step 8 (.close 14)))))) (.step 3 (.step 14 (.close 3)))) (.step 19 (.step 3 (.step 20 (.close 3))))) (.step 3 (.step 4 (.step 3 (.step 8 (.step 14 (.close 17))))))) (.step 19 (.step 20 (.step 3 (.close 4)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1393796576206238160979689299173147750170624, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891007114701259005423238440442270842880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 30 0 (.split 36 0 (.split 53 0 (.split 43 0 (.step 8 (.step 3 (.close 5))) (.step 3 (.close 8))) (.step 8 (.step 14 (.close 3)))) (.step 3 (.step 8 (.close 14)))) (.step 3 (.step 8 (.close 14)))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 69 (.step 17 (.step 3 (.step 4 (.close 5)))))) (.step 51 (.split 26 0 (.split 30 0 (.step 51 (.step 14 (.step 17 (.close 3)))) (.step 3 (.step 4 (.step 3 (.step 8 (.close 14)))))) (.step 3 (.step 4 (.step 8 (.close 14))))))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 53 0 (.split 56 0 (.step 17 (.close 3)) (.step 3 (.step 8 (.close 14)))) (.step 8 (.close 14))) (.step 3 (.step 5 (.step 8 (.close 14))))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 17 (.close 3))) (.step 17 (.step 3 (.step 4 (.step 3 (.close 5))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891007114701259005423238440442270842880⟩
def references : Fin 7 → Box := ![Part0.root, Part1.root, Part3.root, Part6.root, Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 7 := (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 26 0 (.split 35 0 (.split 38 0 (.step 69 (.split 30 0 (.step 3 (.step 28 (.close 37))) (.step 3 (.close 20)))) (.split 30 0 (.step 60 (.step 3 (.step 5 (.step 28 (.step 37 (.close 38)))))) (.step 3 (.step 5 (.step 3 (.step 8 (.close 16))))))) (.step 69 (.step 4 (.step 45 (.step 3 (.step 28 (.step 37 (.close 38)))))))) (.split 30 0 (.step 69 (.step 75 (.step 3 (.close 28)))) (.step 3 (.step 4 (.step 3 (.close 7)))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 4) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.step 51 (.split 35 0 (.split 36 0 (.step 8 (.step 3 (.close 5))) (.step 3 (.step 8 (.step 3 (.close 13))))) (.step 3 (.step 4 (.close 8))))) (.step 3 (.split 34 0 (.step 8 (.step 3 (.step 13 (.close 14)))) (.step 3 (.step 8 (.step 13 (.close 14))))))) (.step 3 (.step 24 (.step 3 (.step 4 (.step 8 (.close 14))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.split 35 0 (.step 60 (.step 69 (.step 3 (.close 8)))) (.step 3 (.step 4 (.step 8 (.close 14)))))) (.step 3 (.step 14 (.close 3)))) (.step 20 (.step 3 (.step 8 (.close 3))))) (.step 3 (.step 4 (.step 3 (.step 8 (.step 14 (.close 17)))))))))) (.reuse 5)) (.reuse 6)))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part3.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712618912277992803918939750953795091772073521461441069056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 53 0 (.split 56 0 (.step 66 (.close 3)) (.step 28 (.step 3 (.close 38)))) (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 28 (.step 38 (.close 39))))) (.split 35 0 (.step 3 (.step 49 (.close 3))) (.step 3 (.step 66 (.close 3))))) (.split 34 0 (.split 35 0 (.step 3 (.step 19 (.step 3 (.close 28)))) (.step 3 (.step 19 (.step 3 (.close 28))))) (.step 3 (.split 35 0 (.step 33 (.step 3 (.step 13 (.close 3)))) (.step 3 (.step 11 (.close 13))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 28 (.step 3 (.step 4 (.step 10 (.close 28))))) (.step 3 (.close 28))) (.step 29 (.close 3))) (.step 3 (.step 66 (.close 3)))) (.step 3 (.split 34 0 (.step 3 (.step 29 (.close 3))) (.step 3 (.close 7)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.step 3 (.step 13 (.close 3)))) (.step 3 (.step 14 (.step 17 (.step 3 (.step 13 (.close 3))))))) (.step 3 (.step 13 (.step 33 (.close 3))))) (.step 4 (.step 24 (.step 3 (.step 4 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317171068094430909730748625962168668792297619456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 11))))) (.step 3 (.step 14 (.step 17 (.step 3 (.step 13 (.close 3))))))) (.step 3 (.step 13 (.step 33 (.close 3))))) (.step 4 (.step 24 (.step 3 (.step 4 (.step 3 (.close 7))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 3 (.step 69 (.step 3 (.close 8)))) (.step 3 (.step 13 (.step 3 (.close 8))))) (.step 3 (.step 11 (.close 13)))) (.step 3 (.step 13 (.step 14 (.step 11 (.close 15)))))) (.step 25 (.step 3 (.step 13 (.step 19 (.step 3 (.step 4 (.close 11)))))))) (.step 7 (.close 3)))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 13 (.step 3 (.close 8)))))) (.step 3 (.step 11 (.close 13)))) (.step 3 (.step 13 (.step 14 (.step 11 (.close 15)))))) (.step 20 (.step 3 (.step 13 (.step 19 (.step 3 (.step 4 (.close 8)))))))) (.step 7 (.close 3))) (.step 19 (.step 20 (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891005817894694971944560709314891743232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 53 0 (.split 56 0 (.step 3 (.step 5 (.close 8))) (.step 3 (.close 5))) (.step 3 (.close 8))) (.step 3 (.close 5))) (.step 3 (.step 11 (.step 3 (.close 4))))) (.step 3 (.step 17 (.step 3 (.close 11))))) (.step 3 (.step 66 (.step 3 (.close 11))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.split 26 0 (.split 30 0 (.step 3 (.step 17 (.step 3 (.step 11 (.close 3))))) (.step 3 (.step 5 (.step 11 (.close 13))))) (.step 3 (.close 7)))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 3 (.step 17 (.step 3 (.step 11 (.close 3))))) (.step 3 (.step 5 (.step 11 (.close 13))))) (.step 3 (.close 7))) (.step 17 (.close 3)))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 3 (.step 17 (.step 3 (.step 11 (.close 3))))) (.step 3 (.step 5 (.step 11 (.close 13))))) (.step 3 (.close 7))) (.step 17 (.close 3))) (.step 17 (.step 3 (.close 5))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1299341865233935136534121859252224, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891007115968909605651467841938974048256⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 53 0 (.step 3 (.close 5)) (.step 8 (.step 3 (.close 4)))) (.step 3 (.step 4 (.step 3 (.close 8))))) (.step 3 (.close 4))) (.step 3 (.step 14 (.step 3 (.close 8))))) (.step 3 (.step 49 (.step 3 (.close 8))))) (.step 3 (.step 24 (.step 3 (.close 4))))) (.split 26 0 (.split 30 0 (.step 3 (.step 14 (.step 3 (.step 8 (.close 3))))) (.step 3 (.step 4 (.step 8 (.close 13))))) (.step 3 (.close 4)))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 3 (.step 14 (.step 3 (.step 8 (.close 3))))) (.step 3 (.step 4 (.step 8 (.close 13))))) (.step 3 (.close 4))) (.step 17 (.step 8 (.step 3 (.close 13)))))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 3 (.step 14 (.step 3 (.step 8 (.close 3))))) (.step 3 (.step 4 (.step 8 (.close 13))))) (.step 3 (.close 4))) (.step 17 (.step 8 (.step 3 (.close 13))))) (.step 17 (.step 8 (.close 13))))) (.step 3 (.step 14 (.close 3)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712618912277992803918939749686145700469663734593912569856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 36 0 (.step 47 (.step 58 (.step 5 (.step 37 (.close 38))))) (.step 51 (.step 3 (.step 5 (.step 28 (.close 37)))))) (.split 38 0 (.split 42 0 (.step 47 (.step 4 (.step 40 (.step 5 (.step 37 (.close 38)))))) (.step 3 (.step 29 (.step 3 (.step 5 (.step 38 (.step 37 (.close 39)))))))) (.step 3 (.step 5 (.step 28 (.close 38)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 8 (.step 47 (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.step 11 (.close 3)))) (.step 3 (.step 24 (.step 3 (.close 5)))))) (.split 30 0 (.step 47 (.step 3 (.step 7 (.step 5 (.close 28))))) (.step 3 (.step 11 (.step 3 (.step 4 (.step 3 (.close 7)))))))) (.split 26 0 (.split 30 0 (.step 69 (.split 38 0 (.split 42 0 (.step 11 (.close 3)) (.step 3 (.step 7 (.step 3 (.close 8))))) (.step 3 (.step 5 (.close 8))))) (.step 3 (.split 34 0 (.step 11 (.close 3)) (.step 3 (.close 7))))) (.step 3 (.step 11 (.step 4 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317171068094430908463099234659758881924769120256⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 36 0 (.split 35 0 (.step 51 (.step 3 (.close 5))) (.step 3 (.step 11 (.close 3)))) (.step 3 (.step 11 (.close 3)))) (.step 3 (.split 34 0 (.step 11 (.close 3)) (.step 3 (.close 7))))) (.step 3 (.step 11 (.step 4 (.step 3 (.close 7)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.split 35 0 (.step 51 (.step 3 (.step 5 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 4 (.close 8)))))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 8))) (.step 3 (.step 7 (.step 8 (.close 11)))))))) (.run (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 8 (.step 11 (.step 3 (.close 5)))) (.step 3 (.close 8))) (.step 3 (.step 11 (.close 3)))) (.step 3 (.step 11 (.close 3)))) (.step 3 (.step 67 (.close 3)))) (.step 3 (.step 11 (.step 4 (.step 3 (.close 7)))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.split 35 0 (.split 38 0 (.step 11 (.close 3)) (.step 3 (.step 5 (.close 8)))) (.step 3 (.step 7 (.step 4 (.close 8)))))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 8))) (.step 3 (.step 7 (.step 8 (.close 11)))))) (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.step 11 (.close 3))) (.step 3 (.step 7 (.step 4 (.close 8))))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 8))) (.step 3 (.step 7 (.step 8 (.close 11))))) (.step 19 (.step 20 (.step 3 (.step 4 (.step 3 (.close 7))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1267651809154049016126951653376, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891007115968910814577287456568148754432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 8 (.step 47 (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.step 11 (.close 3)))) (.step 3 (.step 17 (.step 3 (.close 7))))) (.step 3 (.step 66 (.step 3 (.close 7))))) (.step 3 (.step 29 (.close 3)))) (.split 26 0 (.split 30 0 (.step 3 (.step 17 (.step 11 (.close 3)))) (.step 3 (.step 5 (.close 7)))) (.step 3 (.close 7)))) (.split 22 0 (.split 26 0 (.split 30 0 (.step 3 (.step 17 (.step 11 (.close 3)))) (.step 3 (.step 5 (.close 7)))) (.step 3 (.close 7))) (.step 7 (.close 8)))) (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.step 3 (.step 17 (.step 11 (.close 3)))) (.step 3 (.step 5 (.close 7)))) (.step 3 (.close 7))) (.step 7 (.close 8))) (.step 7 (.close 8)))) (.split 16 0 (.step 66 (.split 17 0 (.split 22 0 (.step 3 (.split 26 0 (.step 7 (.step 4 (.close 5))) (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8))))) (.step 7 (.close 11)))) (.step 3 (.step 17 (.close 3)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891007115968910814577287456568148754432⟩
def references : Fin 2 → Box := ![Part16.root, Part17.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 11 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 11 (.step 5 (.step 11 (.close 5)))) (.step 66 (.split 35 0 (.step 47 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 3 (.step 7 (.close 11)))))))) (.step 67 (.step 3 (.step 7 (.step 4 (.close 5)))))) (.step 11 (.step 5 (.step 11 (.step 5 (.close 29)))))) (.step 11 (.close 3))) (.step 11 (.close 3))) (.step 11 (.step 3 (.step 5 (.step 3 (.step 4 (.step 3 (.close 7)))))))))) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 30 0 (.step 8 (.split 36 0 (.step 11 (.step 3 (.close 5))) (.step 3 (.close 8)))) (.step 3 (.close 8))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 4 (.close 8)))) (.step 69 (.step 8 (.close 3)))) (.step 51 (.split 26 0 (.step 8 (.close 3)) (.step 3 (.step 4 (.close 8)))))) (.split 17 0 (.split 22 0 (.split 26 0 (.step 8 (.close 3)) (.step 3 (.step 4 (.close 8)))) (.step 8 (.close 3))) (.step 8 (.step 3 (.close 5))))) (.split 16 0 (.step 66 (.step 11 (.close 3))) (.step 8 (.close 11)))))) (.reuse 1))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509979005890877344726618712620410317172461891007115968910814577287456568148754432⟩
def references : Fin 6 → Box := ![Part10.root, Part11.root, Part12.root, Part13.root, Part14.root, Part18.root]
def proof : Chunks.Proof 6 := (.split 8 0 (.split 10 0 (.reuse 0) (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.step 3 (.step 13 (.close 3)))) (.step 3 (.step 14 (.step 17 (.step 3 (.step 13 (.close 3))))))) (.step 3 (.step 13 (.step 33 (.close 3))))) (.step 4 (.step 24 (.step 3 (.step 4 (.step 3 (.close 7))))))) (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 13 (.step 3 (.close 8)))))) (.step 3 (.step 11 (.close 13)))) (.step 3 (.step 13 (.step 14 (.step 11 (.close 15)))))) (.step 20 (.step 3 (.step 13 (.step 25 (.close 3)))))) (.step 7 (.close 3)))))) (.reuse 2)) (.reuse 3)) (.reuse 4))) (.reuse 5))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part19

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part19.excludes
end FiveColour.Packed.ProjectedChunks.Case203
