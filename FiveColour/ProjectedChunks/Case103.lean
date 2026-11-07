module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case103
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934408045371882287302473502903020006576514178411409702912⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593776385211095628535, 5789234131009374248507341982684158355876555513350053335929015326897327162342062193097593244396629436776638632267636611235444786831573185258760290656459859266733554791122816590519108237010294841316599838966919287400980022272, 0⟩]
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460185687623521853432901339388523142134881260582158384915405315182105932566770031554577519064794076887698636800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 72 1 (.split 74 1 (.split 71 1 (.split 8 0 (.step 7 (.step 3 (.close 29))) (.step 3 (.step 11 (.close 29)))) (.step 74 (.close 3))) (.step 11 (.step 69 (.split 71 1 (.split 16 0 (.step 3 (.close 77)) (.step 18 (.close 3))) (.step 69 (.close 74)))))) (.step 69 (.step 29 (.step 69 (.split 71 1 (.split 8 0 (.step 3 (.close 75)) (.step 3 (.close 75))) (.step 69 (.close 74))))))) (.step 69 (.step 3 (.close 7)))) (.step 3 (.step 74 (.split 72 1 (.step 18 (.split 74 1 (.step 3 (.close 31)) (.step 3 (.close 11)))) (.step 3 (.close 75)))))) (.step 69 (.step 67 (.split 65 1 (.step 77 (.split 17 0 (.step 75 (.step 3 (.close 31))) (.step 3 (.close 67)))) (.step 3 (.close 67)))))) (.step 69 (.step 66 (.split 65 1 (.step 75 (.step 77 (.split 16 0 (.step 3 (.close 66)) (.step 3 (.close 66))))) (.step 3 (.close 66)))))) (.split 67 1 (.step 51 (.step 3 (.close 7))) (.step 3 (.close 7)))) (.split 51 1 (.split 67 1 (.step 47 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 7 (.step 75 (.split 63 1 (.split 64 1 (.split 71 1 (.step 31 (.close 7)) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66)))))) (.step 7 (.step 75 (.split 42 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 74 1 (.step 31 (.close 7)) (.step 31 (.close 11))))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.close 39)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097867279618188301332246472269054796947094780841378231783224312463181957094652772352⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 42 1 (.split 65 1 (.split 74 1 (.split 51 1 (.step 75 (.split 67 1 (.step 29 (.split 8 0 (.split 10 0 (.split 17 0 (.split 36 0 (.step 66 (.step 67 (.split 51 0 (.step 38 (.close 3)) (.step 3 (.close 21))))) (.step 38 (.step 3 (.close 66)))) (.step 66 (.step 67 (.step 18 (.close 38))))) (.step 38 (.step 3 (.close 66)))) (.step 9 (.step 66 (.step 67 (.step 38 (.step 74 (.close 38)))))))) (.step 3 (.close 38)))) (.step 3 (.close 38))) (.step 66 (.step 67 (.step 69 (.step 11 (.step 23 (.step 38 (.step 74 (.close 38))))))))) (.step 3 (.step 21 (.close 38)))) (.step 31 (.step 3 (.close 38)))) (.step 31 (.step 38 (.close 3))))))))))) (.run (.step 7 (.step 75 (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 31 (.close 7)) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.close 45))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 29 (.step 31 (.close 37))))))))) (.run (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))) (.step 3 (.close 31)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934408045371879499709323684039823696303632065114465632256⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 29 (.step 74 (.split 74 1 (.split 30 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.step 3 (.close 18))) (.step 3 (.close 21))) (.step 29 (.close 67))) (.step 29 (.close 66))) (.step 3 (.close 29))) (.step 3 (.close 29))) (.step 27 (.step 47 (.step 66 (.step 29 (.step 67 (.step 18 (.close 74)))))))))))))) (.run (.step 7 (.step 77 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.close 7)) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 66 (.step 38 (.close 67))))) (.step 18 (.step 29 (.step 66 (.close 67))))))))) (.run (.step 7 (.step 77 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 72 1 (.step 18 (.close 7)) (.step 18 (.close 29))))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 66 (.step 38 (.close 67))))) (.step 18 (.step 29 (.close 74)))) (.step 18 (.close 20))))))) (.run (.step 7 (.step 77 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.close 7)) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 38 (.close 67)))) (.step 18 (.step 29 (.close 67)))) (.step 18 (.close 25))) (.step 7 (.step 18 (.close 19))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934408045371882287302473502903017588724874949153060290560⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 14 1 (.reuse 0) (.run (.step 3 (.step 31 (.step 27 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 51 1 (.step 77 (.split 67 1 (.step 11 (.split 10 0 (.step 67 (.split 16 0 (.step 74 (.split 30 0 (.step 66 (.split 26 0 (.step 3 (.close 17)) (.step 23 (.step 17 (.close 29))))) (.step 3 (.close 17)))) (.step 17 (.step 18 (.close 29))))) (.step 17 (.step 3 (.close 66))))) (.step 3 (.close 17)))) (.step 3 (.close 17))) (.step 31 (.step 17 (.close 66)))) (.step 31 (.step 17 (.close 66)))) (.step 31 (.close 17))) (.step 3 (.close 17))) (.step 31 (.step 66 (.step 67 (.step 69 (.step 23 (.step 29 (.step 17 (.step 74 (.close 17)))))))))) (.step 3 (.step 17 (.close 34)))) (.step 31 (.step 66 (.step 67 (.step 74 (.step 75 (.step 77 (.split 16 0 (.step 29 (.step 11 (.step 23 (.split 17 0 (.step 38 (.close 17)) (.step 3 (.close 17)))))) (.step 3 (.step 17 (.close 29))))))))))) (.step 29 (.step 47 (.step 66 (.step 67 (.step 74 (.step 77 (.step 29 (.step 3 (.close 17)))))))))) (.step 17 (.step 3 (.close 18)))) (.step 17 (.step 3 (.close 18)))) (.step 17 (.step 18 (.close 19)))))))))))) (.run (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))) (.step 3 (.close 31))) (.step 3 (.close 29))) (.step 3 (.close 17)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934408045371882287302473502903020006576514178411409702912⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 8 1 (.reuse 0) (.run (.step 3 (.step 31 (.step 11 (.step 27 (.step 74 (.split 35 1 (.split 72 1 (.split 10 1 (.split 26 1 (.split 30 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 67 1 (.step 11 (.step 3 (.close 31))) (.step 3 (.close 11))) (.step 3 (.step 11 (.close 31)))) (.step 3 (.step 29 (.step 11 (.close 31))))) (.step 31 (.close 11))) (.step 11 (.close 67))) (.step 11 (.close 66))) (.step 3 (.close 11))) (.step 3 (.close 11))) (.step 9 (.close 47))) (.step 3 (.close 11))) (.step 9 (.step 31 (.step 47 (.step 11 (.step 66 (.step 67 (.close 75)))))))) (.step 31 (.step 47 (.step 66 (.step 67 (.step 74 (.step 75 (.step 11 (.step 3 (.close 31)))))))))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part4.excludes
end FiveColour.Packed.ProjectedChunks.Case103
