module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case64
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046469715305779158844648997153197260800⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨37630511536740893520887, 5789234131009374248507346766749886964179117598075761631441503938856419104125729984377942245333425284026394393415169773689373755704242316349912225571028696891635007459092358541327061333498215709696615525420286517587399934977, 0⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264584551890877153870977257186960390719417315701555200000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 34 0 (.split 30 0 (.step 55 (.step 45 (.step 4 (.close 28)))) (.split 36 0 (.step 55 (.close 33)) (.step 33 (.step 55 (.close 33))))) (.split 36 0 (.split 30 0 (.step 55 (.step 16 (.step 28 (.step 4 (.close 33))))) (.step 33 (.step 55 (.close 33)))) (.split 38 0 (.split 42 0 (.step 55 (.close 33)) (.step 45 (.split 30 0 (.step 16 (.step 4 (.close 28))) (.step 37 (.step 28 (.step 4 (.close 33))))))) (.split 43 0 (.split 30 0 (.step 16 (.step 33 (.close 4))) (.step 33 (.close 16))) (.step 33 (.step 16 (.step 4 (.step 5 (.step 20 (.close 28)))))))))) (.split 30 0 (.split 38 0 (.step 55 (.step 40 (.step 37 (.step 39 (.close 43))))) (.step 33 (.step 23 (.step 43 (.step 8 (.step 16 (.close 20))))))) (.step 33 (.step 55 (.step 37 (.step 20 (.step 4 (.step 20 (.close 39))))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1498039178264175491158776953534190095147331930292224, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046468415963913924909512463032411750400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 55 (.split 42 0 (.step 35 (.step 24 (.close 25))) (.step 23 (.step 19 (.step 20 (.close 24)))))) (.step 33 (.step 23 (.close 24)))) (.split 38 0 (.split 42 0 (.step 54 (.step 4 (.step 8 (.close 19)))) (.step 20 (.step 19 (.step 23 (.step 20 (.close 24)))))) (.step 33 (.step 20 (.step 4 (.close 5)))))) (.split 36 0 (.split 38 0 (.split 42 0 (.step 55 (.step 23 (.step 17 (.close 19)))) (.step 25 (.step 39 (.step 4 (.step 8 (.close 17)))))) (.step 33 (.close 23))) (.step 39 (.close 17)))) (.split 34 0 (.split 36 0 (.split 38 0 (.step 25 (.split 30 0 (.step 8 (.step 4 (.close 19))) (.step 19 (.step 8 (.step 4 (.close 20)))))) (.step 19 (.step 8 (.step 20 (.step 23 (.close 24)))))) (.step 25 (.step 19 (.close 20)))) (.split 30 0 (.split 36 0 (.step 25 (.step 19 (.step 20 (.close 4)))) (.step 20 (.step 19 (.step 17 (.step 8 (.close 20)))))) (.step 19 (.step 20 (.step 23 (.step 17 (.close 24)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046468415963913924909512463032411750400⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 16 0 (.split 17 0 (.reuse 0) (.run (.split 22 0 (.split 30 0 (.split 38 0 (.step 55 (.step 39 (.step 17 (.step 37 (.close 43))))) (.step 33 (.step 23 (.step 43 (.step 8 (.step 16 (.close 20))))))) (.step 33 (.step 39 (.step 23 (.step 25 (.close 37)))))) (.split 34 0 (.split 36 0 (.split 38 0 (.step 55 (.step 25 (.step 55 (.step 4 (.step 8 (.close 20)))))) (.step 33 (.step 23 (.close 24)))) (.split 38 0 (.split 42 0 (.step 54 (.step 4 (.step 8 (.close 20)))) (.step 20 (.step 23 (.step 20 (.close 24))))) (.step 33 (.step 20 (.step 4 (.close 5)))))) (.split 36 0 (.split 38 0 (.split 42 0 (.step 55 (.step 23 (.step 17 (.close 20)))) (.step 25 (.step 23 (.close 17)))) (.step 33 (.close 23))) (.step 39 (.close 17))))))) (.split 17 0 (.run (.split 22 0 (.split 30 0 (.split 38 0 (.step 55 (.step 40 (.step 37 (.close 38)))) (.step 33 (.step 23 (.step 41 (.step 4 (.step 5 (.close 37))))))) (.step 33 (.step 41 (.step 25 (.step 37 (.close 38)))))) (.split 34 0 (.split 36 0 (.split 38 0 (.step 55 (.step 25 (.step 35 (.step 19 (.close 23))))) (.step 33 (.step 23 (.close 24)))) (.split 38 0 (.split 42 0 (.step 55 (.step 23 (.step 19 (.step 20 (.close 24))))) (.step 25 (.step 20 (.step 4 (.close 19))))) (.step 33 (.close 23)))) (.split 36 0 (.split 38 0 (.split 42 0 (.step 55 (.step 23 (.step 17 (.close 19)))) (.step 25 (.step 23 (.close 17)))) (.step 33 (.close 23))) (.step 45 (.step 20 (.step 19 (.step 4 (.step 8 (.close 17)))))))))) (.reuse 1)))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1267650600228229401497776947200, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264584551890877153870977258454610990947646717198258405376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 0 (.split 34 0 (.split 30 0 (.split 38 0 (.step 55 (.close 13)) (.step 33 (.step 28 (.step 13 (.close 4))))) (.step 33 (.step 13 (.step 4 (.step 20 (.close 28)))))) (.split 36 0 (.split 30 0 (.split 42 0 (.step 55 (.close 13)) (.step 16 (.close 13))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 16)))))) (.split 38 0 (.split 30 0 (.split 43 0 (.step 16 (.close 13)) (.step 13 (.step 16 (.close 15)))) (.step 13 (.step 33 (.step 16 (.close 39))))) (.step 33 (.step 16 (.close 13)))))) (.split 34 0 (.split 30 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 13 (.step 40 (.step 5 (.step 33 (.close 39)))))) (.step 13 (.step 33 (.step 23 (.step 20 (.close 39)))))) (.split 38 0 (.step 13 (.split 47 0 (.split 50 0 (.step 40 (.step 39 (.close 43))) (.step 33 (.step 24 (.step 15 (.close 39))))) (.step 33 (.step 23 (.step 15 (.close 17)))))) (.step 33 (.step 13 (.step 14 (.step 5 (.step 16 (.close 39))))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046468417231564525137741864529114955776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 30 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 13 (.step 40 (.step 5 (.step 33 (.close 38)))))) (.step 13 (.step 33 (.step 23 (.step 20 (.close 38)))))) (.split 38 0 (.step 13 (.split 47 0 (.split 50 0 (.step 40 (.step 38 (.close 39))) (.step 33 (.step 24 (.step 15 (.close 39))))) (.step 33 (.step 23 (.step 15 (.close 17)))))) (.step 33 (.step 13 (.step 14 (.step 5 (.step 16 (.close 39)))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 25 (.step 55 (.step 4 (.step 8 (.close 13))))) (.step 13 (.step 19 (.close 5)))) (.step 13 (.step 20 (.step 19 (.close 4))))) (.step 13 (.split 38 0 (.split 43 0 (.step 14 (.close 15)) (.step 23 (.step 17 (.close 14)))) (.step 14 (.step 5 (.step 14 (.close 15))))))) (.step 13 (.step 33 (.split 42 0 (.step 25 (.step 8 (.close 14))) (.step 25 (.step 14 (.step 17 (.close 20))))))))) (.split 34 0 (.split 30 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 55 (.step 19 (.step 13 (.close 4)))) (.step 13 (.step 8 (.close 19)))) (.step 13 (.step 23 (.step 19 (.close 20))))) (.step 33 (.step 13 (.step 19 (.close 5))))) (.step 13 (.step 20 (.close 19)))) (.step 13 (.step 33 (.step 20 (.step 25 (.step 4 (.close 8))))))) (.step 13 (.split 38 0 (.split 47 0 (.split 50 0 (.step 14 (.step 17 (.close 20))) (.step 17 (.close 15))) (.step 14 (.close 17))) (.step 14 (.step 5 (.step 14 (.close 15)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1298074214633706907132625156046848, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586048468553780715566795834443725900136576000561512448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.split 51 0 (.step 5 (.step 4 (.close 13))) (.step 48 (.step 13 (.close 14)))) (.split 46 0 (.step 55 (.step 13 (.step 23 (.close 15)))) (.step 13 (.step 4 (.step 8 (.close 48)))))) (.split 43 0 (.split 51 0 (.split 34 0 (.step 5 (.step 4 (.close 13))) (.step 37 (.close 4))) (.step 16 (.step 5 (.step 14 (.close 19))))) (.step 28 (.step 4 (.step 5 (.close 13)))))) (.split 34 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 13 (.step 33 (.step 4 (.close 8))))) (.split 43 0 (.step 37 (.close 4)) (.step 13 (.step 33 (.step 23 (.step 20 (.close 28)))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 13 (.step 4 (.step 8 (.step 19 (.close 20)))))) (.split 43 0 (.step 37 (.close 4)) (.step 13 (.step 23 (.step 4 (.close 15)))))) (.step 13 (.step 33 (.step 23 (.step 4 (.close 20))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 13 (.step 4 (.step 8 (.step 19 (.close 20)))))) (.split 43 0 (.step 37 (.close 4)) (.step 13 (.step 23 (.step 4 (.close 15)))))) (.step 13 (.step 33 (.step 20 (.close 4))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 25 (.step 8 (.step 4 (.step 13 (.close 17))))) (.step 13 (.step 4 (.step 8 (.step 19 (.close 20)))))) (.step 13 (.close 20))) (.step 13 (.step 20 (.step 4 (.step 8 (.close 14)))))) (.step 13 (.step 20 (.step 25 (.close 4))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨1298074214633706907132625156046848, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046469715305779158844648997153197260800⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 13 (.step 4 (.step 8 (.close 19))))) (.split 43 0 (.step 37 (.close 4)) (.step 13 (.step 23 (.step 4 (.close 15)))))) (.step 13 (.step 33 (.step 23 (.step 4 (.close 20)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 25 (.step 8 (.step 4 (.step 13 (.close 17))))) (.step 13 (.step 4 (.step 8 (.close 19))))) (.step 13 (.step 19 (.step 4 (.step 8 (.close 20)))))) (.step 13 (.step 19 (.step 14 (.close 20))))) (.step 13 (.step 19 (.step 25 (.close 8)))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 55 (.step 35 (.step 8 (.step 4 (.close 13))))) (.step 13 (.step 4 (.step 8 (.close 19))))) (.step 13 (.step 19 (.step 4 (.step 8 (.close 20)))))) (.step 13 (.step 19 (.step 14 (.close 20))))) (.step 13 (.step 19 (.step 20 (.step 4 (.close 8)))))) (.step 25 (.step 13 (.step 19 (.step 8 (.close 14))))))))) (.run (.split 16 0 (.split 34 0 (.step 13 (.split 36 0 (.step 13 (.step 48 (.step 8 (.close 13)))) (.step 13 (.close 4)))) (.split 46 0 (.split 50 0 (.step 13 (.step 4 (.step 8 (.close 14)))) (.step 13 (.close 4))) (.step 13 (.close 33)))) (.step 13 (.step 14 (.close 4))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047605235886618534719015264586049930055418046469715305779158844648997153197260800⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part4.root, Part6.root]
def proof : Chunks.Proof 4 := (.split 11 0 (.split 10 0 (.reuse 0) (.split 16 0 (.split 17 0 (.reuse 1) (.run (.split 22 0 (.split 34 0 (.split 30 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 13)))) (.step 13 (.close 39))) (.step 13 (.step 33 (.step 20 (.step 4 (.close 39)))))) (.split 38 0 (.step 13 (.step 39 (.step 55 (.step 33 (.step 14 (.step 17 (.close 39))))))) (.step 33 (.step 13 (.step 14 (.step 5 (.step 16 (.close 39)))))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 25 (.step 55 (.step 4 (.step 8 (.close 13))))) (.step 13 (.step 19 (.step 5 (.step 8 (.close 20)))))) (.step 13 (.step 20 (.close 19)))) (.step 13 (.step 39 (.step 14 (.step 15 (.close 17)))))) (.step 13 (.step 33 (.split 42 0 (.step 20 (.step 4 (.close 14))) (.step 25 (.step 14 (.step 17 (.close 20))))))))))) (.reuse 2))) (.reuse 3))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part7.excludes
end FiveColour.Packed.EnumerationChunks.Case64
