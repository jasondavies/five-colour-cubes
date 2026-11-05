module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case194
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350626369544627693813333691209875456⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11519759214886954775232, 5021355398095715194672006110474991829640005411303441180663043928424359283843673970689742072656462809873798003367987238269049531288523336371066778577353908327990027355414615209580706801631257362793884550144, 0⟩]
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077919628301774418863731838850464017419237064704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 50 (.step 3 (.step 28 (.close 37))))) (.step 3 (.close 20))) (.step 38 (.step 3 (.close 28)))) (.split 26 0 (.step 41 (.step 3 (.close 28))) (.step 3 (.step 4 (.close 28))))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 69 (.split 34 0 (.step 3 (.step 4 (.close 5))) (.step 3 (.step 19 (.close 3))))) (.split 34 0 (.step 69 (.step 3 (.step 19 (.close 3)))) (.step 3 (.step 33 (.close 3))))) (.step 4 (.step 24 (.step 3 (.step 4 (.close 8)))))) (.step 4 (.step 23 (.step 3 (.step 5 (.close 8))))))) (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 51 (.split 34 0 (.step 3 (.step 4 (.close 5))) (.step 3 (.step 19 (.close 3))))) (.split 34 0 (.step 51 (.step 3 (.step 19 (.close 3)))) (.step 3 (.step 33 (.close 3))))) (.step 4 (.step 24 (.step 3 (.step 4 (.close 8)))))) (.step 4 (.step 23 (.step 3 (.step 5 (.close 8)))))) (.split 30 0 (.split 25 0 (.split 26 0 (.split 34 0 (.step 51 (.step 69 (.split 35 0 (.step 3 (.step 5 (.step 3 (.close 8)))) (.step 3 (.step 4 (.step 3 (.close 11))))))) (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 19 (.step 3 (.step 19 (.close 3))))))) (.step 3 (.step 11 (.close 15))))) (.step 4 (.step 24 (.step 3 (.step 4 (.step 8 (.close 19))))))) (.step 23 (.step 3 (.step 5 (.step 8 (.close 19)))))) (.step 19 (.step 3 (.step 7 (.step 3 (.close 20)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077919628301774418863731838850464017419237064704⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 53 0 (.split 74 0 (.split 30 0 (.split 34 0 (.step 28 (.step 38 (.close 3))) (.step 37 (.step 28 (.step 3 (.close 38))))) (.step 3 (.step 28 (.step 38 (.close 37))))) (.step 3 (.step 28 (.step 38 (.close 37))))) (.step 3 (.step 28 (.step 38 (.close 37))))) (.split 30 0 (.step 29 (.close 3)) (.step 38 (.step 3 (.close 28))))) (.split 26 0 (.split 30 0 (.step 28 (.close 3)) (.step 41 (.step 3 (.close 28)))) (.step 28 (.step 3 (.step 9 (.close 28)))))) (.split 25 0 (.step 69 (.split 26 0 (.split 30 0 (.step 3 (.step 28 (.step 37 (.close 38)))) (.step 3 (.close 20))) (.step 4 (.step 7 (.close 28))))) (.split 26 0 (.split 30 0 (.step 60 (.step 3 (.step 5 (.close 28)))) (.step 3 (.step 5 (.step 3 (.close 7))))) (.step 3 (.step 4 (.close 28)))))) (.split 22 0 (.split 25 0 (.split 26 0 (.step 51 (.split 30 0 (.step 3 (.step 28 (.step 37 (.close 38)))) (.step 3 (.close 20)))) (.split 30 0 (.step 51 (.step 7 (.close 28))) (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 51 (.step 5 (.step 7 (.close 28))))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 51 (.step 69 (.step 3 (.close 20)))) (.split 34 0 (.step 51 (.step 3 (.close 20))) (.step 3 (.step 33 (.close 3))))) (.step 4 (.step 24 (.step 3 (.step 4 (.close 8)))))) (.step 4 (.step 23 (.step 3 (.step 5 (.close 8))))))))) (.reuse 0))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917049616419384767446408823993352116573038285898645504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 53 0 (.split 34 0 (.split 42 0 (.step 3 (.close 5)) (.step 3 (.step 5 (.close 28)))) (.step 3 (.step 5 (.step 28 (.close 37))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.step 28 (.close 37))))) (.step 29 (.step 3 (.step 5 (.close 37))))) (.step 29 (.step 3 (.step 5 (.close 28))))) (.step 29 (.step 28 (.step 3 (.close 5))))) (.split 25 0 (.split 26 0 (.step 69 (.step 5 (.step 11 (.step 3 (.close 13))))) (.step 3 (.step 11 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.step 5 (.close 8))))) (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 51 (.step 3 (.close 11))) (.step 3 (.step 11 (.step 3 (.close 13))))) (.step 3 (.step 11 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.step 5 (.close 8)))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 69 (.split 34 0 (.step 51 (.step 3 (.close 11))) (.step 3 (.step 11 (.step 3 (.close 13)))))) (.step 3 (.step 20 (.close 3)))) (.step 3 (.step 11 (.step 17 (.step 4 (.step 3 (.close 7))))))) (.step 3 (.step 5 (.step 3 (.step 8 (.close 14)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098349327027678184832856057941831188480⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 14 0 (.reuse 0) (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 11 (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 11 (.close 3)))) (.step 3 (.step 11 (.step 3 (.close 13))))) (.step 3 (.step 11 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.step 5 (.close 8)))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 69 (.split 34 0 (.split 38 0 (.step 11 (.step 3 (.close 4))) (.step 3 (.step 5 (.close 8)))) (.step 3 (.step 11 (.step 3 (.close 13)))))) (.step 3 (.step 19 (.step 3 (.close 11))))) (.step 3 (.step 11 (.step 17 (.step 4 (.step 3 (.close 7))))))) (.step 3 (.step 5 (.step 3 (.step 8 (.close 14))))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 11 (.step 3 (.close 5))) (.step 3 (.step 11 (.close 3))))) (.step 3 (.step 11 (.step 17 (.close 19))))) (.step 3 (.step 17 (.close 3)))) (.step 19 (.step 3 (.step 20 (.close 3))))) (.step 3 (.step 11 (.step 17 (.step 19 (.step 20 (.close 3))))))) (.step 3 (.step 5 (.step 3 (.step 8 (.step 14 (.close 17)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1461501637330904216277899466423190152281088589824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077919628301775716937946472557371150043319369728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 8 (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 8 (.close 3)))) (.step 3 (.step 8 (.step 3 (.close 13))))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 8 (.step 5 (.step 3 (.close 7)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 60 (.step 69 (.close 3))) (.step 3 (.step 8 (.step 3 (.step 13 (.close 14)))))) (.step 3 (.step 19 (.step 3 (.close 8))))) (.step 3 (.step 4 (.step 3 (.step 8 (.close 14)))))) (.step 3 (.step 8 (.step 14 (.step 5 (.step 3 (.close 7)))))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.split 35 0 (.split 36 0 (.step 8 (.step 14 (.step 3 (.close 5)))) (.step 3 (.step 8 (.step 3 (.step 13 (.close 14)))))) (.step 3 (.step 4 (.step 8 (.close 14)))))) (.step 3 (.step 14 (.close 3)))) (.step 19 (.step 3 (.step 20 (.close 3))))) (.step 3 (.step 4 (.step 3 (.step 8 (.step 14 (.close 17))))))) (.step 3 (.step 8 (.step 14 (.step 19 (.step 20 (.close 3)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1298074214633706907132625156046848, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077919628301775716937946472557371150043319369728⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 53 0 (.step 3 (.step 28 (.close 37))) (.step 4 (.step 8 (.step 3 (.close 4))))) (.step 3 (.step 28 (.step 3 (.step 4 (.close 37)))))) (.step 4 (.step 3 (.step 28 (.close 37))))) (.step 28 (.step 29 (.step 3 (.close 4))))) (.step 28 (.step 3 (.step 4 (.close 28))))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 60 (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 8 (.step 3 (.close 13))))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 8 (.step 5 (.step 3 (.close 7))))))) (.split 22 0 (.split 25 0 (.step 51 (.step 4 (.step 8 (.step 3 (.close 13))))) (.step 3 (.step 8 (.step 5 (.step 3 (.close 7)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 51 (.split 34 0 (.step 60 (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 8 (.step 3 (.close 13)))))) (.step 3 (.step 20 (.close 3)))) (.step 3 (.step 4 (.step 3 (.step 8 (.close 14)))))) (.step 3 (.step 8 (.step 14 (.step 5 (.step 3 (.close 7)))))))))) (.reuse 0))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917049616417990970871501927697606362410399260007727104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 28 (.step 38 (.close 37)))) (.step 3 (.step 13 (.close 3)))) (.split 30 0 (.split 34 0 (.step 29 (.close 3)) (.step 3 (.step 7 (.close 28)))) (.step 3 (.step 7 (.close 28))))) (.split 26 0 (.split 30 0 (.split 34 0 (.step 28 (.close 3)) (.step 3 (.step 7 (.close 28)))) (.step 3 (.step 7 (.close 28)))) (.step 3 (.step 7 (.close 28))))) (.split 25 0 (.split 26 0 (.step 3 (.step 45 (.step 3 (.step 13 (.close 3))))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7))))))) (.split 22 0 (.split 25 0 (.split 26 0 (.step 3 (.step 39 (.step 3 (.step 13 (.close 3))))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.step 3 (.step 13 (.close 3)))) (.step 3 (.step 13 (.step 3 (.step 14 (.close 11)))))) (.step 3 (.step 13 (.step 20 (.close 3))))) (.step 4 (.step 7 (.close 3)))) (.step 7 (.close 3))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077919628301774420131382439078693418915940270080⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.step 3 (.split 35 0 (.step 13 (.step 3 (.close 8))) (.step 3 (.step 11 (.close 13))))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.step 3 (.step 13 (.close 3)))) (.step 3 (.step 13 (.step 3 (.step 14 (.close 11)))))) (.step 3 (.step 13 (.step 19 (.step 3 (.step 14 (.close 11))))))) (.step 4 (.step 7 (.close 3)))) (.step 7 (.close 3)))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 13 (.step 3 (.close 8)))))) (.step 3 (.step 11 (.close 13)))) (.step 3 (.step 13 (.step 14 (.step 11 (.close 15)))))) (.step 19 (.step 13 (.step 20 (.close 3))))) (.step 7 (.close 3))) (.step 7 (.close 3))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨1299341865233935136534121859252224, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350626369543418767992592062616698880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.split 26 0 (.step 49 (.step 3 (.close 8))) (.step 3 (.close 4))) (.step 3 (.step 5 (.step 3 (.close 7)))))) (.split 25 0 (.split 26 0 (.step 3 (.step 14 (.step 3 (.close 8)))) (.step 3 (.close 4))) (.step 3 (.close 7)))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 14 (.step 3 (.step 8 (.close 3))))) (.step 3 (.step 4 (.step 8 (.close 13))))) (.step 3 (.close 4))) (.step 3 (.close 7)))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 3 (.step 14 (.split 36 0 (.step 8 (.step 3 (.close 14))) (.step 3 (.step 8 (.close 13)))))) (.step 3 (.step 4 (.step 8 (.close 13))))) (.step 13 (.close 3))) (.step 3 (.close 4))) (.step 3 (.close 7)))) (.step 3 (.step 13 (.step 8 (.close 14))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350626369543418767992592062616698880⟩
def references : Fin 4 → Box := ![Part3.root, Part5.root, Part7.root, Part8.root]
def proof : Chunks.Proof 4 := (.split 10 0 (.split 11 0 (.reuse 0) (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.split 36 0 (.split 53 0 (.step 3 (.step 4 (.close 5))) (.step 8 (.step 3 (.step 4 (.close 5))))) (.step 3 (.close 8))) (.step 3 (.close 8))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 5 (.close 8)))) (.step 69 (.step 3 (.step 4 (.close 5))))) (.step 51 (.step 14 (.step 3 (.step 4 (.close 5)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 14 (.split 38 0 (.step 17 (.close 3)) (.step 3 (.step 5 (.step 8 (.close 14)))))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 3 (.step 4 (.step 3 (.step 8 (.close 14)))))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 3 (.step 5 (.step 8 (.close 14))))))))) (.split 11 0 (.split 14 0 (.reuse 2) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.step 66 (.step 3 (.step 66 (.step 3 (.close 7))))) (.step 3 (.close 5)))) (.split 25 0 (.step 3 (.step 17 (.step 3 (.step 7 (.close 11))))) (.step 3 (.close 5)))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 17 (.step 3 (.step 11 (.close 3))))) (.step 3 (.step 5 (.step 11 (.close 13))))) (.step 3 (.close 7))) (.step 3 (.close 5)))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 3 (.step 17 (.split 35 0 (.step 14 (.step 3 (.step 11 (.close 3)))) (.step 3 (.step 11 (.close 13)))))) (.step 3 (.step 5 (.step 11 (.close 13))))) (.step 13 (.close 3))) (.step 3 (.close 7))) (.step 3 (.close 5)))))) (.reuse 3)))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917049616417990970871500660048215060000612392479227904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 36 0 (.step 47 (.step 3 (.step 5 (.close 37)))) (.step 3 (.step 5 (.step 28 (.step 37 (.close 38)))))) (.step 29 (.step 3 (.step 5 (.step 38 (.close 37)))))) (.step 29 (.step 3 (.step 5 (.close 28))))) (.step 29 (.step 28 (.step 3 (.close 5))))) (.split 25 0 (.split 26 0 (.step 69 (.step 5 (.step 7 (.step 3 (.close 4))))) (.step 3 (.step 7 (.step 4 (.close 8))))) (.step 3 (.step 5 (.close 8))))) (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 51 (.step 3 (.close 7))) (.step 3 (.step 7 (.step 3 (.close 8))))) (.step 3 (.step 7 (.step 4 (.close 8))))) (.step 3 (.step 5 (.close 8)))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 69 (.split 34 0 (.step 51 (.step 3 (.close 7))) (.step 3 (.step 7 (.close 8))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 7 (.step 4 (.close 8))))) (.step 3 (.step 5 (.step 3 (.close 8))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨1208925819614630248448000, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098349327027679393758675672571005894656⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 11 (.close 3)) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 7 (.step 3 (.close 8))))) (.step 3 (.step 7 (.step 4 (.close 8))))) (.step 3 (.step 5 (.close 8)))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 69 (.split 34 0 (.split 38 0 (.step 11 (.close 3)) (.step 3 (.step 5 (.close 8)))) (.step 3 (.step 7 (.close 8))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 7 (.step 4 (.close 8))))) (.step 3 (.step 5 (.step 3 (.close 8)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.step 11 (.close 3))) (.step 3 (.step 7 (.step 4 (.close 8))))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 8))) (.step 3 (.step 7 (.step 8 (.close 11))))) (.step 3 (.step 5 (.step 3 (.close 8)))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 11 (.step 3 (.close 5))) (.step 67 (.step 3 (.close 7)))) (.step 5 (.step 11 (.close 5)))) (.step 5 (.step 8 (.step 5 (.close 28))))) (.step 11 (.close 3))) (.step 11 (.close 3))) (.step 11 (.step 3 (.close 5))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨1125900980584448, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917049616417990970871500660047006134182123663211364352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 36 0 (.step 47 (.step 3 (.step 4 (.close 37)))) (.step 3 (.step 28 (.step 3 (.step 4 (.step 37 (.close 38))))))) (.step 4 (.step 3 (.step 28 (.step 38 (.close 37)))))) (.step 28 (.step 29 (.step 3 (.close 4))))) (.step 28 (.step 3 (.step 4 (.close 28))))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 60 (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 7 (.step 3 (.close 8))))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 7 (.step 5 (.close 8)))))) (.split 22 0 (.split 25 0 (.step 51 (.step 4 (.step 7 (.step 3 (.close 5))))) (.step 3 (.step 7 (.step 5 (.close 8))))) (.split 25 0 (.split 26 0 (.split 30 0 (.step 51 (.split 34 0 (.step 60 (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 7 (.close 8))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 4 (.step 3 (.close 8))))) (.step 3 (.step 7 (.step 5 (.close 8))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨1125900980584448, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350625101892818539764316465820336128⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 11 0 (.split 14 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 8 (.close 3)) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 7 (.step 3 (.close 8))))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 7 (.step 5 (.close 8))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 60 (.step 69 (.close 3))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 4 (.step 3 (.close 8))))) (.step 3 (.step 7 (.step 5 (.close 8)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.split 35 0 (.split 36 0 (.step 8 (.close 3)) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 4 (.close 8))))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 8))) (.step 3 (.step 4 (.step 3 (.close 8))))) (.step 3 (.step 7 (.close 8))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 11 (.step 3 (.step 4 (.close 5)))) (.step 3 (.close 8))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 5 (.close 8)))) (.step 11 (.close 3))) (.step 11 (.close 3))) (.step 11 (.step 3 (.close 5)))))) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 8 (.step 3 (.close 4))) (.step 50 (.step 3 (.close 7)))) (.step 4 (.step 8 (.step 3 (.close 28))))) (.step 4 (.step 8 (.close 4)))) (.step 8 (.close 3))) (.step 8 (.close 3))) (.step 8 (.step 3 (.close 4)))) (.step 49 (.step 8 (.close 3))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨1125900980584448, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350626369544627693813332591698247680⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 10 0 (.reuse 0) (.run (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.split 26 0 (.step 49 (.step 3 (.close 7))) (.step 3 (.close 4))) (.step 3 (.step 5 (.step 3 (.close 7)))))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 3 (.step 11 (.step 3 (.close 4))))) (.split 14 0 (.step 49 (.step 7 (.step 4 (.close 8)))) (.step 3 (.step 4 (.step 3 (.close 8)))))))) (.run (.split 10 0 (.split 11 0 (.split 14 0 (.split 16 0 (.step 47 (.split 17 0 (.split 22 0 (.step 3 (.step 4 (.close 5))) (.step 8 (.close 3))) (.step 8 (.close 3)))) (.step 8 (.step 3 (.close 4)))) (.step 11 (.close 3))) (.step 8 (.step 3 (.close 4)))) (.step 3 (.step 7 (.close 8))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨1100585369600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077919628301774418863731838850464018518748692480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 28 (.step 38 (.close 37)))) (.step 3 (.close 7))) (.step 28 (.step 29 (.close 3)))) (.step 28 (.step 3 (.close 28)))) (.split 25 0 (.split 26 0 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7))))))) (.split 22 0 (.split 25 0 (.split 26 0 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 51 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 4 (.step 7 (.close 3)))) (.step 7 (.close 3))))) (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 69 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 4 (.step 7 (.close 3)))) (.step 7 (.close 3)))) (.split 25 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 51 (.split 36 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.close 7)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨1298074214633706907133724667674624, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350625101892818539763191665425121280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 4 (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.close 7))) (.step 3 (.close 4))) (.step 3 (.step 5 (.step 3 (.close 7)))))) (.step 8 (.step 3 (.close 7)))) (.step 8 (.split 25 0 (.split 26 0 (.step 3 (.step 20 (.split 30 0 (.step 3 (.step 13 (.close 14))) (.step 3 (.close 7))))) (.step 3 (.close 4))) (.step 3 (.close 7))))) (.step 8 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.split 34 0 (.step 19 (.split 36 0 (.step 3 (.step 14 (.close 17))) (.step 3 (.close 7)))) (.step 3 (.close 7)))) (.step 3 (.step 4 (.close 7)))) (.step 3 (.close 4))) (.step 3 (.close 7))))) (.step 3 (.step 8 (.step 4 (.step 3 (.close 14)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨1100585369600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350626369543418767992593162128326656⟩
def references : Fin 2 → Box := ![Part15.root, Part16.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 11 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 5 (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.close 7))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.close 5)))) (.step 11 (.step 3 (.close 7)))) (.step 11 (.split 25 0 (.step 3 (.split 26 0 (.split 30 0 (.step 74 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 3 (.close 5))))) (.step 11 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.split 34 0 (.step 19 (.split 36 0 (.step 3 (.step 14 (.close 17))) (.step 3 (.close 7)))) (.step 3 (.close 7)))) (.step 3 (.step 5 (.close 7)))) (.step 3 (.close 7))) (.step 3 (.close 5))))))) (.reuse 1)) (.run (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 7 (.step 3 (.close 28))))) (.step 3 (.step 7 (.step 3 (.close 28))))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.step 7 (.close 3))) (.split 16 0 (.split 25 0 (.split 26 0 (.step 13 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 5))) (.step 7 (.close 3)))) (.split 14 0 (.split 16 0 (.split 25 0 (.split 26 0 (.step 13 (.close 3)) (.step 3 (.close 4))) (.step 3 (.close 7))) (.step 7 (.close 3))) (.step 3 (.step 4 (.step 5 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨1100585369600, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350626369544627693813333691209875456⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.split 8 0 (.reuse 0) (.run (.split 10 0 (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 5 (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.close 7))) (.step 3 (.step 4 (.step 3 (.close 7))))) (.step 3 (.close 5)))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 11 (.close 3))) (.step 3 (.step 8 (.close 3)))) (.step 7 (.step 3 (.close 8)))))) (.run (.split 8 0 (.split 10 0 (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.split 26 0 (.split 30 0 (.step 3 (.step 4 (.step 3 (.step 4 (.step 3 (.close 7)))))) (.step 3 (.close 7))) (.step 3 (.close 4))) (.step 3 (.step 5 (.step 3 (.close 7)))))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 3 (.step 8 (.close 3)))) (.step 8 (.close 3))) (.step 7 (.step 3 (.close 8)))) (.step 3 (.step 7 (.close 8))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨1073741824, 5783586108473071698929511776359016237500579447288910316334420535437335904231230827929368359976964628776581131343519670068452955178330620522074509980815142271677792172205917051077921022098350626369544627693813333691209875456⟩
def references : Fin 4 → Box := ![Part9.root, Part11.root, Part14.root, Part18.root]
def proof : Chunks.Proof 4 := (.split 4 0 (.split 5 0 (.split 8 0 (.reuse 0) (.split 10 0 (.split 11 0 (.reuse 1) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 8 (.step 3 (.step 4 (.close 5)))) (.step 3 (.close 8))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 5 (.close 8)))) (.step 8 (.close 3))) (.step 8 (.close 3))) (.step 8 (.step 3 (.close 4)))) (.step 66 (.step 8 (.step 3 (.close 4))))))) (.run (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.split 25 0 (.step 66 (.step 3 (.step 7 (.step 3 (.close 4))))) (.step 3 (.close 5)))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 7 (.step 3 (.close 8)))) (.step 66 (.step 7 (.step 5 (.step 8 (.close 3)))))) (.step 3 (.step 8 (.step 3 (.close 5)))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part11.excludes
  · exact Part14.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part19.excludes
end FiveColour.Packed.ProjectedChunks.Case194
