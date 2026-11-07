module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case217
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310646809571252465719884974330123715328899809280⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11519759214887055438832, 5265277774374911502192413395042321151349739735218570910636844525234622908848336196301850770133722977586047213474194916510032396784268157516925953188630634353931345538559401307494245342244156428591742906684933120, 0⟩]
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
def root : Box := ⟨2037035976334486086268445688409378161051468393665936250636140449354381299763336707257139200, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463078600603174879943786104778708660458182334798333813714213285687984128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 0 (.split 35 0 (.split 36 0 (.split 56 0 (.split 38 0 (.step 3 (.close 49)) (.split 42 0 (.step 3 (.close 28)) (.step 3 (.close 38)))) (.step 51 (.step 28 (.close 69)))) (.step 51 (.step 3 (.split 42 0 (.step 3 (.close 50)) (.step 39 (.step 3 (.close 45))))))) (.split 36 0 (.split 53 0 (.step 29 (.step 38 (.close 3))) (.step 3 (.close 50))) (.step 3 (.split 38 0 (.step 29 (.step 3 (.close 38))) (.step 3 (.close 38)))))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.split 53 0 (.step 29 (.step 3 (.close 37))) (.step 3 (.close 8))) (.step 3 (.close 28))) (.step 3 (.step 28 (.close 37)))) (.step 3 (.step 28 (.step 3 (.close 38))))) (.split 38 0 (.split 42 0 (.step 3 (.step 28 (.close 37))) (.step 37 (.step 3 (.close 39)))) (.step 3 (.step 37 (.step 28 (.step 3 (.close 38))))))) (.step 3 (.split 36 0 (.split 38 0 (.step 29 (.step 3 (.close 38))) (.step 3 (.close 38))) (.step 37 (.step 38 (.close 3))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463078600603174879943786104778708660458182334798333813714213285687984128⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 30 0 (.run (.split 35 0 (.split 36 0 (.split 53 0 (.split 56 0 (.split 34 0 (.split 38 0 (.step 3 (.close 49)) (.step 29 (.close 69))) (.split 38 0 (.step 29 (.close 69)) (.split 42 0 (.step 29 (.close 69)) (.step 28 (.close 45))))) (.step 51 (.step 28 (.close 69)))) (.step 51 (.step 3 (.close 45)))) (.step 51 (.split 44 0 (.step 39 (.step 28 (.step 39 (.close 69)))) (.step 51 (.step 28 (.close 3)))))) (.split 38 0 (.split 42 0 (.split 36 0 (.split 34 0 (.split 53 0 (.step 29 (.close 69)) (.step 51 (.close 4))) (.split 43 0 (.step 29 (.step 48 (.step 49 (.close 50)))) (.step 3 (.close 28)))) (.step 51 (.step 29 (.close 69)))) (.step 69 (.split 44 0 (.step 45 (.step 38 (.close 51))) (.step 29 (.close 3))))) (.split 42 0 (.split 53 0 (.split 56 0 (.step 29 (.step 38 (.close 3))) (.step 28 (.close 38))) (.step 3 (.step 28 (.close 38)))) (.step 69 (.step 28 (.close 38))))))) (.reuse 0))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1496577676626844588240573268701473812127675997749248, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860269849143778443773340010388561696312121029587632128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 35 0 (.step 51 (.split 36 0 (.split 44 0 (.split 34 0 (.step 3 (.close 49)) (.step 3 (.step 28 (.step 3 (.close 37))))) (.step 51 (.step 11 (.close 28)))) (.step 51 (.close 39)))) (.split 36 0 (.split 38 0 (.split 42 0 (.step 51 (.step 29 (.close 69))) (.step 3 (.step 29 (.step 3 (.step 38 (.close 45)))))) (.step 3 (.step 28 (.close 38)))) (.step 51 (.close 20)))) (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.close 50)) (.step 3 (.step 33 (.close 39))))) (.step 24 (.step 3 (.close 50)))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 25))) (.step 3 (.close 23))) (.step 3 (.close 39))) (.step 3 (.close 33))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 69 (.step 3 (.close 19))) (.step 51 (.step 39 (.close 3))))) (.step 24 (.step 3 (.step 4 (.step 8 (.close 19)))))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 69 (.split 42 0 (.step 3 (.close 20)) (.step 3 (.close 20)))) (.step 3 (.close 20))) (.step 3 (.step 39 (.close 3)))) (.step 3 (.step 4 (.close 20))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.step 8 (.close 20))) (.step 3 (.close 20))) (.step 3 (.close 20))) (.step 20 (.close 3))) (.step 3 (.close 33))) (.split 35 0 (.split 38 0 (.step 3 (.step 33 (.step 20 (.close 3)))) (.step 5 (.close 33))) (.step 19 (.step 24 (.close 3))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463078600603174879943787566280345991361100538483166529997232941620527104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 53 0 (.split 56 0 (.split 38 0 (.step 3 (.close 49)) (.step 67 (.close 3))) (.step 51 (.step 5 (.close 41)))) (.step 51 (.step 3 (.close 8)))) (.step 51 (.split 44 0 (.step 3 (.step 28 (.step 3 (.close 41)))) (.step 3 (.step 8 (.close 28)))))) (.split 38 0 (.split 42 0 (.split 36 0 (.split 43 0 (.step 50 (.close 3)) (.step 3 (.close 29))) (.step 3 (.close 38))) (.step 3 (.step 29 (.close 38)))) (.step 3 (.close 50)))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.step 3 (.close 49)) (.step 3 (.close 59))) (.step 3 (.close 56))) (.step 3 (.step 28 (.close 45)))) (.step 3 (.step 28 (.close 41)))) (.split 38 0 (.split 43 0 (.step 3 (.step 28 (.step 37 (.close 38)))) (.step 3 (.close 20))) (.step 41 (.close 3)))) (.step 3 (.split 36 0 (.split 38 0 (.step 29 (.close 38)) (.step 3 (.close 38))) (.step 38 (.close 50)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 50 (.close 3)) (.step 3 (.close 8))) (.step 3 (.close 8))) (.step 3 (.close 50))) (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 20))) (.step 3 (.close 19)))) (.step 24 (.close 67))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 25))) (.step 3 (.close 19))) (.step 3 (.step 38 (.close 23)))) (.step 3 (.close 33))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310645415774676258214073394412595140685520175104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.split 44 0 (.split 38 0 (.step 3 (.close 19)) (.step 3 (.step 19 (.close 3)))) (.step 51 (.step 8 (.close 3)))) (.step 51 (.step 39 (.close 3))))) (.step 24 (.step 3 (.close 50)))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.step 8 (.close 20))) (.step 3 (.close 20))) (.step 3 (.close 19))) (.step 3 (.step 39 (.close 3)))) (.step 3 (.close 38)))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 50)) (.step 3 (.close 20))) (.step 3 (.close 19))) (.step 20 (.close 3))) (.step 3 (.close 33))) (.step 38 (.step 41 (.step 3 (.step 20 (.step 3 (.close 20)))))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 69 (.split 43 0 (.step 51 (.step 3 (.close 8))) (.step 19 (.step 3 (.close 8))))) (.step 19 (.close 5))) (.step 20 (.close 51))) (.step 19 (.step 3 (.close 4)))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 3 (.step 14 (.step 17 (.close 19)))) (.step 19 (.close 3))) (.step 25 (.close 3))) (.step 3 (.close 19))) (.step 20 (.close 3))) (.step 19 (.close 3)))) (.step 19 (.step 20 (.close 3))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310645415774676258214073394412595140685520175104⟩
def references : Fin 4 → Box := ![Part1.root, Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 4 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 35 0 (.split 38 0 (.split 42 0 (.step 69 (.step 3 (.close 39))) (.step 69 (.close 20))) (.split 42 0 (.split 36 0 (.step 69 (.step 28 (.close 51))) (.step 3 (.step 28 (.step 3 (.step 38 (.close 39)))))) (.step 69 (.close 23)))) (.step 69 (.split 34 0 (.split 38 0 (.step 75 (.step 3 (.step 50 (.close 3)))) (.step 3 (.close 38))) (.step 75 (.step 3 (.step 28 (.close 37))))))) (.split 34 0 (.split 35 0 (.split 36 0 (.step 69 (.step 3 (.close 50))) (.split 38 0 (.step 69 (.step 3 (.close 20))) (.step 3 (.close 20)))) (.step 24 (.step 3 (.close 50)))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 69 (.step 3 (.close 25))) (.step 3 (.close 23))) (.step 3 (.step 39 (.step 3 (.close 8))))) (.step 3 (.close 33))))))) (.reuse 1)) (.split 17 0 (.split 22 0 (.reuse 2) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 38 0 (.split 42 0 (.step 69 (.step 3 (.close 8))) (.step 69 (.close 20))) (.step 23 (.step 3 (.close 67)))) (.step 24 (.step 3 (.close 50)))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 69 (.split 42 0 (.step 3 (.close 56)) (.step 3 (.close 25)))) (.step 3 (.close 19))) (.step 3 (.split 46 0 (.step 39 (.close 3)) (.step 3 (.close 16))))) (.step 3 (.close 38)))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 50)) (.step 3 (.close 25))) (.step 3 (.close 19))) (.step 3 (.step 20 (.step 3 (.close 25))))) (.step 3 (.close 33))) (.step 38 (.step 41 (.step 3 (.step 25 (.step 3 (.close 20)))))))))) (.reuse 3)))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463078600603174879943786104780102457033090498744679796106253808282107904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 35 0 (.split 38 0 (.split 42 0 (.split 36 0 (.split 34 0 (.split 43 0 (.split 53 0 (.step 69 (.close 8)) (.step 11 (.step 3 (.close 14)))) (.step 11 (.close 49))) (.split 43 0 (.step 49 (.close 3)) (.step 3 (.close 11)))) (.step 51 (.step 5 (.close 74)))) (.step 69 (.split 44 0 (.step 3 (.step 37 (.close 3))) (.step 29 (.step 28 (.close 11)))))) (.split 42 0 (.split 36 0 (.split 53 0 (.split 56 0 (.step 63 (.close 49)) (.step 5 (.step 43 (.close 49)))) (.step 5 (.close 49))) (.step 3 (.step 28 (.step 5 (.close 37))))) (.step 3 (.step 28 (.step 37 (.step 5 (.step 37 (.close 38)))))))) (.split 36 0 (.split 38 0 (.split 42 0 (.split 72 0 (.split 34 0 (.split 53 0 (.step 5 (.step 11 (.close 28))) (.step 3 (.close 49))) (.step 3 (.close 49))) (.step 29 (.step 4 (.step 37 (.close 75))))) (.step 29 (.step 3 (.step 5 (.close 37))))) (.step 5 (.step 28 (.close 38)))) (.step 3 (.step 29 (.step 37 (.step 3 (.step 5 (.step 37 (.close 38))))))))) (.split 34 0 (.split 35 0 (.split 53 0 (.split 56 0 (.step 67 (.close 3)) (.step 3 (.step 5 (.close 8)))) (.step 3 (.close 49))) (.step 29 (.step 24 (.step 3 (.close 49))))) (.step 3 (.step 67 (.step 3 (.close 24)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860269849145172240348248174334907678704161552181755904⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.step 69 (.split 38 0 (.split 42 0 (.step 11 (.step 69 (.close 4))) (.step 3 (.step 11 (.step 3 (.close 77))))) (.step 3 (.step 5 (.close 19))))) (.step 3 (.split 35 0 (.step 69 (.step 17 (.step 3 (.close 11)))) (.step 3 (.close 17))))) (.split 34 0 (.step 3 (.split 35 0 (.step 69 (.split 36 0 (.step 11 (.step 3 (.close 14))) (.step 3 (.close 24)))) (.step 3 (.close 24)))) (.step 5 (.step 11 (.close 17))))))) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 35 0 (.step 51 (.step 11 (.close 5))) (.step 11 (.step 3 (.step 4 (.close 19))))) (.step 3 (.step 11 (.step 24 (.close 51))))) (.step 3 (.split 35 0 (.split 36 0 (.step 11 (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))))) (.split 34 0 (.step 3 (.split 35 0 (.split 36 0 (.step 11 (.step 3 (.close 20))) (.step 3 (.close 20))) (.step 3 (.close 20)))) (.step 5 (.step 11 (.close 17))))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 69 (.split 36 0 (.split 38 0 (.step 74 (.step 25 (.step 8 (.close 20)))) (.step 3 (.step 5 (.step 8 (.close 19))))) (.step 20 (.close 3)))) (.step 11 (.step 17 (.step 19 (.step 4 (.close 20)))))) (.split 36 0 (.step 3 (.step 17 (.close 3))) (.step 5 (.step 11 (.close 17))))) (.step 20 (.step 3 (.step 20 (.step 25 (.close 3)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310646809571251166378019740394987181208114298880⟩
def references : Fin 2 → Box := ![Part5.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.reuse 0) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 38 0 (.split 42 0 (.split 36 0 (.split 43 0 (.step 11 (.step 49 (.close 3))) (.step 3 (.close 8))) (.step 3 (.step 8 (.close 49)))) (.step 3 (.step 11 (.step 3 (.close 49))))) (.step 3 (.close 67))) (.step 3 (.step 11 (.step 24 (.step 3 (.close 50)))))) (.step 3 (.split 35 0 (.split 36 0 (.step 11 (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))))) (.split 34 0 (.step 67 (.close 3)) (.step 5 (.close 38)))) (.split 30 0 (.split 34 0 (.split 35 0 (.step 69 (.split 36 0 (.split 38 0 (.split 42 0 (.step 11 (.step 14 (.step 3 (.close 17)))) (.step 3 (.step 11 (.close 25)))) (.step 3 (.close 19))) (.step 3 (.step 20 (.step 11 (.close 25)))))) (.step 11 (.step 19 (.close 3)))) (.split 36 0 (.step 3 (.step 17 (.close 3))) (.step 5 (.step 11 (.close 17))))) (.step 19 (.step 25 (.close 3))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 74 (.step 51 (.step 3 (.close 8)))) (.step 3 (.close 67))) (.step 20 (.close 51))) (.step 11 (.step 19 (.close 3)))) (.split 36 0 (.step 3 (.step 17 (.close 3))) (.step 5 (.step 11 (.close 17))))) (.step 19 (.step 20 (.close 3)))) (.step 19 (.step 20 (.step 3 (.step 11 (.close 3))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1298074214633706907132625156046848, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576858773271467151599186397511334493929407125978745929728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 44 0 (.split 51 0 (.split 53 0 (.step 66 (.step 3 (.close 37))) (.step 51 (.step 3 (.close 4)))) (.step 48 (.step 8 (.step 51 (.close 3))))) (.split 53 0 (.split 56 0 (.step 47 (.step 8 (.step 28 (.close 8)))) (.step 8 (.close 28))) (.step 8 (.close 3)))) (.split 38 0 (.step 51 (.split 44 0 (.step 3 (.step 37 (.close 3))) (.step 28 (.step 29 (.close 8))))) (.step 3 (.step 28 (.step 37 (.step 3 (.step 4 (.step 37 (.close 38))))))))) (.split 34 0 (.split 36 0 (.split 53 0 (.split 56 0 (.split 38 0 (.step 66 (.close 3)) (.step 3 (.step 28 (.close 37)))) (.step 3 (.step 28 (.step 37 (.close 38))))) (.step 4 (.step 24 (.close 50)))) (.step 3 (.step 28 (.step 4 (.step 37 (.close 38)))))) (.step 3 (.close 66)))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 44 0 (.split 51 0 (.step 50 (.close 3)) (.step 3 (.close 50))) (.step 8 (.close 3))) (.step 3 (.step 23 (.step 3 (.close 50))))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 50 (.step 3 (.close 23)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 69 (.step 8 (.step 3 (.close 5)))) (.step 3 (.step 8 (.step 23 (.step 3 (.close 25)))))) (.step 3 (.step 4 (.step 8 (.close 19))))) (.step 3 (.split 36 0 (.step 8 (.step 14 (.close 3))) (.step 3 (.close 14))))) (.split 34 0 (.step 3 (.split 36 0 (.step 8 (.step 50 (.close 3))) (.step 3 (.close 23)))) (.step 4 (.step 8 (.close 14)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1461501637330904216277899466423190152281088589824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310645415774677556288288028119502273309602480128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 44 0 (.step 8 (.step 50 (.split 53 0 (.step 3 (.close 5)) (.step 14 (.step 3 (.close 5)))))) (.step 8 (.close 3))) (.step 3 (.step 8 (.step 23 (.step 3 (.close 56)))))) (.step 3 (.close 50))) (.step 3 (.split 36 0 (.step 8 (.step 14 (.close 3))) (.step 3 (.close 14))))) (.split 34 0 (.step 50 (.close 3)) (.step 4 (.close 41)))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 60 (.step 69 (.step 8 (.step 3 (.close 5))))) (.step 3 (.step 20 (.step 8 (.step 20 (.step 3 (.close 19))))))) (.step 3 (.close 50))) (.split 35 0 (.step 14 (.close 3)) (.step 3 (.close 4)))) (.step 19 (.step 25 (.close 3))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 51 (.split 42 0 (.step 8 (.step 14 (.step 3 (.close 17)))) (.step 3 (.step 8 (.step 3 (.close 19)))))) (.step 3 (.step 8 (.step 14 (.close 19))))) (.step 20 (.close 51))) (.step 3 (.close 50))) (.split 35 0 (.step 14 (.close 3)) (.step 3 (.close 4)))) (.step 19 (.step 20 (.close 3)))) (.step 19 (.step 20 (.step 3 (.close 25)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1393796576206238160979689299173147750170624, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310646809571252464452234374101894313832196603904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 38 0 (.split 53 0 (.split 42 0 (.split 44 0 (.step 3 (.close 14)) (.step 8 (.close 3))) (.step 3 (.close 49))) (.step 49 (.step 3 (.close 8)))) (.step 3 (.step 5 (.step 8 (.close 14))))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.split 30 0 (.step 69 (.step 49 (.split 35 0 (.step 8 (.close 5)) (.step 4 (.close 8))))) (.step 4 (.step 8 (.close 14))))) (.step 51 (.split 22 0 (.split 30 0 (.step 51 (.step 66 (.split 35 0 (.step 8 (.close 5)) (.step 4 (.close 8))))) (.step 4 (.step 8 (.close 14)))) (.step 14 (.close 13))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 38 0 (.split 53 0 (.split 56 0 (.step 66 (.split 72 0 (.split 34 0 (.step 8 (.close 17)) (.step 3 (.close 14))) (.step 3 (.close 17)))) (.step 3 (.step 8 (.close 14)))) (.step 8 (.close 14))) (.step 5 (.close 19))) (.step 4 (.close 19))) (.step 4 (.step 8 (.close 14)))) (.step 19 (.step 14 (.close 13)))) (.step 19 (.step 14 (.close 13))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463078600603174879943786104778708660458183602448934041943614782391189504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 56 0 (.split 38 0 (.step 3 (.close 49)) (.split 42 0 (.step 3 (.close 28)) (.step 3 (.close 45)))) (.step 51 (.step 28 (.close 69)))) (.step 51 (.step 3 (.split 42 0 (.step 3 (.close 49)) (.step 39 (.step 3 (.close 45))))))) (.split 36 0 (.split 42 0 (.split 53 0 (.step 29 (.step 4 (.step 48 (.close 38)))) (.step 3 (.close 49))) (.step 3 (.step 28 (.step 38 (.close 39))))) (.step 3 (.split 38 0 (.step 29 (.step 3 (.step 38 (.close 39)))) (.step 3 (.close 38)))))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 49 (.close 3)) (.step 3 (.close 28))) (.step 3 (.close 49))) (.step 3 (.step 28 (.close 49)))) (.split 38 0 (.split 42 0 (.step 3 (.close 49)) (.step 37 (.step 3 (.close 39)))) (.step 3 (.step 37 (.close 49))))) (.step 3 (.step 66 (.close 49))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 3 (.close 49)) (.step 3 (.step 49 (.close 3)))) (.split 38 0 (.split 42 0 (.step 3 (.close 28)) (.step 3 (.close 39))) (.step 3 (.close 33)))) (.step 3 (.step 66 (.step 3 (.close 11))))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 28)) (.step 3 (.close 45))) (.step 3 (.close 16))) (.step 3 (.step 37 (.step 33 (.close 3))))) (.step 3 (.close 33))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1496577676626844588241840919301702041529172700954624, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860269849143778443773341278039161924541522526290837504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.close 49)) (.step 3 (.step 39 (.close 3))))) (.step 24 (.step 3 (.close 49)))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 25))) (.step 3 (.close 14))) (.step 3 (.close 39))) (.step 3 (.close 66)))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 25))) (.step 3 (.close 23))) (.step 3 (.step 20 (.close 3)))) (.step 3 (.close 33))) (.step 39 (.step 13 (.step 3 (.close 11)))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.step 8 (.close 20))) (.step 3 (.close 20))) (.step 3 (.close 20))) (.step 3 (.step 13 (.close 20)))) (.step 3 (.step 4 (.close 20)))) (.split 35 0 (.step 14 (.step 3 (.close 15))) (.step 4 (.close 17)))) (.split 34 0 (.step 20 (.step 25 (.close 3))) (.step 14 (.step 17 (.close 20)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576858774732968788930088018908455293167012414507299373056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 53 0 (.step 3 (.close 8)) (.step 3 (.close 49))) (.step 3 (.step 8 (.step 3 (.close 5))))) (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 20))) (.step 3 (.close 19)))) (.step 24 (.step 3 (.close 38)))) (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 25))) (.step 3 (.close 14))) (.step 3 (.step 14 (.step 17 (.step 37 (.step 3 (.close 8))))))) (.step 3 (.close 38)))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.close 8)) (.step 3 (.close 25))) (.step 3 (.close 19))) (.step 3 (.step 13 (.step 20 (.close 3))))) (.step 3 (.close 33))) (.step 38 (.step 14 (.close 3))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.step 8 (.close 19))) (.step 3 (.close 25))) (.step 3 (.close 19))) (.step 3 (.step 13 (.step 19 (.close 3))))) (.step 3 (.close 38))) (.split 35 0 (.step 14 (.step 3 (.close 15))) (.step 4 (.close 17)))) (.split 35 0 (.step 25 (.split 43 0 (.step 3 (.step 13 (.step 3 (.close 20)))) (.step 13 (.step 24 (.step 19 (.close 3)))))) (.step 17 (.step 19 (.close 23)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1393796574909431596946210621442020371070976, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310646809571251167645670340623216582704817504256⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 56 0 (.split 38 0 (.step 11 (.step 3 (.close 14))) (.step 3 (.close 49))) (.step 3 (.step 5 (.close 8)))) (.step 3 (.close 49))) (.step 3 (.step 24 (.step 3 (.close 49))))) (.step 29 (.step 24 (.step 3 (.close 49))))) (.step 3 (.close 66))) (.split 34 0 (.step 3 (.step 66 (.step 3 (.close 13)))) (.step 3 (.close 37)))) (.split 30 0 (.split 34 0 (.step 3 (.split 35 0 (.step 69 (.step 17 (.step 3 (.close 66)))) (.step 3 (.close 13)))) (.step 3 (.close 17))) (.split 35 0 (.step 14 (.close 13)) (.step 3 (.close 13))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.split 35 0 (.split 36 0 (.step 11 (.step 3 (.close 14))) (.step 3 (.close 13))) (.step 3 (.close 13)))) (.step 3 (.close 17))) (.split 35 0 (.step 14 (.close 13)) (.step 3 (.close 13)))) (.step 20 (.step 14 (.close 13))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.split 35 0 (.split 36 0 (.step 11 (.step 3 (.close 14))) (.step 3 (.close 13))) (.step 3 (.close 13)))) (.step 3 (.close 17))) (.step 38 (.close 3))) (.step 19 (.step 14 (.close 13)))) (.step 19 (.step 14 (.close 13))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1299341865233935136534121859252224, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310646809571252465719884974330123715328899809280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 44 0 (.split 51 0 (.step 49 (.close 3)) (.step 3 (.close 14))) (.step 8 (.close 3))) (.step 3 (.step 23 (.step 3 (.close 49))))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.close 49))) (.split 34 0 (.step 3 (.step 49 (.step 3 (.close 13)))) (.step 3 (.close 37)))) (.split 30 0 (.split 34 0 (.step 3 (.split 36 0 (.step 8 (.step 14 (.step 3 (.close 14)))) (.step 3 (.close 13)))) (.step 3 (.close 14))) (.split 35 0 (.step 14 (.close 3)) (.step 3 (.close 4))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.split 36 0 (.step 8 (.step 14 (.step 3 (.close 14)))) (.step 3 (.close 13)))) (.step 3 (.close 14))) (.split 35 0 (.step 14 (.close 3)) (.step 3 (.close 4)))) (.step 20 (.step 14 (.close 3))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.split 36 0 (.step 8 (.step 14 (.step 3 (.close 14)))) (.step 3 (.close 13)))) (.step 3 (.close 14))) (.step 41 (.close 3))) (.step 19 (.step 14 (.close 3)))) (.step 19 (.step 14 (.step 3 (.close 13)))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 3 (.close 14)) (.step 3 (.close 4))) (.step 14 (.close 3))) (.step 14 (.close 3))) (.step 14 (.close 3))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310646809571252465719884974330123715328899809280⟩
def references : Fin 5 → Box := ![Part12.root, Part13.root, Part14.root, Part15.root, Part16.root]
def proof : Chunks.Proof 5 := (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.run (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 69 (.step 3 (.close 49))) (.split 38 0 (.step 69 (.step 3 (.close 20))) (.step 3 (.close 20)))) (.step 24 (.step 3 (.close 49)))) (.split 35 0 (.split 36 0 (.split 38 0 (.step 69 (.step 3 (.close 25))) (.step 3 (.close 14))) (.step 3 (.step 14 (.step 17 (.step 37 (.step 3 (.close 8))))))) (.step 3 (.close 66)))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.step 69 (.step 3 (.close 25))) (.step 3 (.close 23))) (.step 3 (.step 13 (.step 20 (.close 3))))) (.step 3 (.close 33))) (.step 45 (.step 13 (.step 3 (.close 8)))))))) (.reuse 1)) (.split 17 0 (.reuse 2) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.step 8 (.close 19))) (.step 3 (.close 20))) (.step 3 (.close 19))) (.step 3 (.step 13 (.close 20)))) (.step 3 (.close 38))) (.split 35 0 (.step 14 (.step 3 (.close 15))) (.step 4 (.close 17)))) (.split 35 0 (.step 20 (.split 38 0 (.step 3 (.step 13 (.step 20 (.close 3)))) (.step 14 (.close 19)))) (.step 17 (.step 19 (.close 23))))) (.step 19 (.step 20 (.step 13 (.close 3)))))))) (.reuse 3)) (.reuse 4))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074508126332463080285599841576860271310646809571252465719884974330123715328899809280⟩
def references : Fin 5 → Box := ![Part8.root, Part9.root, Part10.root, Part11.root, Part17.root]
def proof : Chunks.Proof 5 := (.split 10 0 (.split 11 0 (.reuse 0) (.split 14 0 (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 30 0 (.split 34 0 (.step 51 (.split 35 0 (.split 36 0 (.step 8 (.step 51 (.close 5))) (.step 3 (.step 8 (.step 3 (.close 56))))) (.step 3 (.step 4 (.close 19))))) (.step 3 (.split 36 0 (.step 8 (.step 14 (.close 3))) (.step 3 (.close 14))))) (.split 34 0 (.step 3 (.split 36 0 (.step 8 (.step 50 (.close 3))) (.step 3 (.close 20)))) (.step 4 (.step 8 (.close 14))))) (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 60 (.step 51 (.step 69 (.step 3 (.close 19))))) (.step 20 (.close 51))) (.step 3 (.step 8 (.step 14 (.close 25))))) (.split 35 0 (.step 14 (.close 3)) (.step 3 (.close 4)))) (.step 20 (.step 3 (.step 8 (.step 14 (.step 3 (.close 25)))))))))) (.reuse 2)) (.reuse 3))) (.reuse 4))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part18.excludes
end FiveColour.Packed.ProjectedChunks.Case217
