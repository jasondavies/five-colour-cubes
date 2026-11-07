module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case102
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629412372176344319488361123675623736891375844577090015168031054793736884600176640⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩]
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925664188033770695627336559962463655613398901129254453295620147697437467558653698612971399368017294971434102674792746003509134806669205451613829622039600144095040472351768576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 3 (.close 31)) (.step 3 (.step 18 (.close 31)))) (.step 7 (.close 12))) (.step 3 (.step 18 (.close 31)))) (.split 2 0 (.split 16 0 (.step 3 (.step 18 (.close 31))) (.step 18 (.close 3))) (.step 23 (.step 31 (.close 18))))) (.step 29 (.step 69 (.step 75 (.step 31 (.close 3)))))) (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 31 (.close 74)) (.step 18 (.close 74))) (.step 31 (.close 74))) (.step 74 (.close 3))) (.step 74 (.close 3)))) (.step 69 (.step 3 (.close 7)))) (.step 3 (.step 74 (.step 3 (.step 63 (.step 74 (.split 72 1 (.step 18 (.step 23 (.close 31))) (.step 3 (.close 31))))))))) (.step 67 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 17 0 (.step 31 (.close 67)) (.step 18 (.close 31))) (.step 31 (.close 67))) (.step 67 (.close 3))) (.step 67 (.close 31))) (.step 63 (.step 3 (.close 67))))))) (.step 66 (.step 3 (.step 66 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 31 (.step 3 (.close 18))) (.step 18 (.close 66))) (.step 31 (.step 12 (.close 66)))) (.step 66 (.close 3))) (.step 66 (.close 31))) (.step 63 (.step 3 (.close 66))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978176018699776613985412130863684895550980965866709126920756807098103058901880470546827275494567965426176479604822245376⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 3 (.split 63 1 (.split 64 1 (.split 65 1 (.step 18 (.step 74 (.step 75 (.split 74 1 (.split 71 1 (.split 72 1 (.split 10 0 (.split 14 0 (.step 28 (.split 30 0 (.step 59 (.close 3)) (.step 3 (.close 31)))) (.step 5 (.close 31))) (.step 3 (.close 31))) (.step 31 (.step 3 (.close 38)))) (.step 31 (.close 74))) (.step 5 (.close 18)))))) (.step 3 (.step 10 (.step 18 (.close 63))))) (.step 31 (.close 67))) (.step 31 (.step 63 (.close 66))))))) (.run (.split 67 1 (.step 51 (.step 3 (.close 7))) (.step 3 (.close 7))))) (.run (.step 9 (.step 10 (.step 27 (.step 47 (.step 3 (.step 7 (.step 3 (.close 10)))))))))) (.run (.step 7 (.step 75 (.split 56 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 31 (.step 7 (.close 38))) (.step 31 (.close 74))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 31 (.close 45)))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955248248460861332199476374696285274888869300199406940376193171560166325748382919164777224037401117839384903680⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 3 (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 3 (.step 75 (.split 74 1 (.split 72 1 (.split 2 0 (.split 14 0 (.split 34 0 (.split 35 0 (.step 18 (.close 31)) (.step 31 (.close 3))) (.step 31 (.close 3))) (.step 5 (.close 31))) (.step 5 (.close 31))) (.step 31 (.step 3 (.close 38)))) (.step 5 (.close 18))))) (.step 31 (.close 74))) (.step 3 (.step 10 (.step 18 (.close 63))))) (.step 31 (.close 67))) (.step 31 (.step 63 (.close 66)))) (.step 5 (.step 28 (.split 63 1 (.split 64 1 (.step 59 (.step 5 (.step 59 (.step 18 (.step 74 (.step 41 (.step 3 (.close 59)))))))) (.step 41 (.close 67))) (.step 31 (.step 63 (.step 66 (.close 5)))))))) (.step 31 (.step 41 (.close 45))))))) (.run (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.step 31 (.close 39)))) (.step 31 (.close 67))) (.step 31 (.close 66)))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629412372176340949495027729842653325155174022991119393424017435788998046339039232⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 74 1 (.split 51 1 (.step 75 (.split 67 1 (.step 29 (.split 2 0 (.split 10 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 38 (.step 21 (.close 38))) (.step 31 (.step 38 (.step 31 (.step 38 (.close 66)))))) (.step 40 (.step 38 (.close 74)))) (.step 40 (.step 66 (.step 67 (.step 38 (.close 18)))))) (.step 38 (.step 3 (.step 31 (.close 66))))) (.step 31 (.step 32 (.close 38))))) (.step 3 (.close 21)))) (.step 3 (.close 38))) (.step 40 (.step 66 (.step 67 (.step 69 (.step 74 (.split 2 0 (.step 38 (.close 74)) (.step 3 (.step 5 (.close 12)))))))))) (.step 3 (.step 21 (.close 38)))) (.step 29 (.step 31 (.step 38 (.close 3))))) (.step 38 (.close 45))) (.step 31 (.step 38 (.close 3)))) (.step 38 (.close 39)))))))))) (.run (.step 7 (.step 75 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 31 (.step 7 (.close 37))) (.step 31 (.close 17))) (.step 31 (.close 67))) (.step 31 (.close 66))) (.step 28 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 37)))) (.step 28 (.step 31 (.step 37 (.close 3))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 31 (.close 37)))))))) (.run (.step 18 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))) (.step 3 (.close 31))))))
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
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629412372176344319488361123675623736891375844577087479866830598334933891191668736⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 31 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 34 1 (.split 36 1 (.step 27 (.step 77 (.step 3 (.step 31 (.split 74 1 (.split 2 0 (.split 16 0 (.step 3 (.step 18 (.close 31))) (.step 18 (.close 3))) (.step 23 (.step 17 (.close 5)))) (.step 17 (.close 3))))))) (.step 5 (.step 17 (.close 31)))) (.step 17 (.close 31))) (.step 69 (.step 40 (.split 2 0 (.split 16 0 (.step 75 (.close 3)) (.step 3 (.close 17))) (.step 3 (.step 5 (.close 12))))))) (.step 17 (.step 69 (.step 74 (.close 3))))) (.step 3 (.step 18 (.step 17 (.close 34))))) (.step 17 (.step 51 (.step 67 (.close 3))))) (.step 12 (.step 17 (.step 18 (.step 34 (.close 66)))))) (.step 31 (.step 5 (.step 12 (.step 17 (.close 67)))))) (.step 18 (.step 31 (.step 5 (.step 12 (.step 17 (.close 67))))))) (.step 17 (.step 31 (.step 66 (.step 67 (.step 74 (.step 75 (.split 2 0 (.split 16 0 (.step 40 (.split 17 0 (.step 38 (.step 69 (.step 38 (.close 17)))) (.step 3 (.close 17)))) (.step 3 (.close 17))) (.step 5 (.close 17)))))))))) (.step 5 (.step 17 (.step 18 (.close 3))))) (.step 18 (.step 3 (.close 20)))) (.step 18 (.step 17 (.step 3 (.close 19))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629412372176344319488361123675623736891375844577090015168031054793736884600176640⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.close 7)) (.step 18 (.close 74))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 66 (.step 38 (.close 67))))))) (.run (.step 7 (.split 22 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.step 18 (.close 7)))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 66 (.step 38 (.close 67))))) (.step 18 (.close 20)))))) (.run (.split 17 1 (.split 22 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.close 7)) (.step 18 (.close 38))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.step 38 (.close 67)))) (.step 18 (.step 7 (.close 19)))) (.step 18 (.step 7 (.close 19)))))) (.reuse 1)) (.run (.step 18 (.split 14 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 31 (.close 66))) (.step 3 (.close 31))) (.step 3 (.close 17)))))) (.run (.step 3 (.step 18 (.step 31 (.split 14 1 (.split 35 1 (.split 38 1 (.split 56 1 (.step 67 (.step 77 (.split 63 1 (.split 65 1 (.step 75 (.split 71 1 (.step 5 (.step 3 (.step 23 (.step 31 (.step 5 (.close 18)))))) (.step 23 (.step 74 (.close 5))))) (.step 3 (.close 63))) (.step 63 (.step 66 (.close 5)))))) (.step 5 (.step 18 (.step 5 (.close 74))))) (.step 5 (.step 24 (.step 18 (.step 31 (.step 5 (.close 67))))))) (.step 3 (.step 32 (.step 38 (.step 5 (.close 66)))))) (.step 5 (.close 17))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case102
