module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case52
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346508060100310038720657802945775553919410948789671030933787587844363013977094851835157240217394550776266752⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37630669409018422557687, 5789234131009374248507346766749891419687533244750779835710650130547166070165997423784225875531183789473991668342093468871764627366270137944873799542728008123750934930136012272409766640092332188979741397452445100402566759425, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370173242433610688582630967190983671696516852578875204481347508805974601998431130877209673839655727310329166435526377472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 49 1 (.split 51 1 (.split 67 1 (.step 58 (.split 25 0 (.step 7 (.step 9 (.step 21 (.step 7 (.close 16))))) (.split 34 0 (.split 36 0 (.split 42 0 (.step 55 (.step 9 (.step 7 (.step 21 (.step 7 (.close 26)))))) (.step 7 (.close 21))) (.step 7 (.step 21 (.close 22)))) (.step 7 (.step 16 (.step 21 (.close 22))))))) (.step 7 (.step 53 (.step 9 (.step 21 (.close 26)))))) (.step 54 (.step 7 (.step 53 (.step 9 (.step 21 (.step 26 (.step 21 (.close 28))))))))) (.split 50 1 (.split 51 1 (.split 67 1 (.step 58 (.step 7 (.step 9 (.step 16 (.step 7 (.close 21)))))) (.step 7 (.close 52))) (.step 52 (.step 7 (.step 9 (.step 21 (.step 26 (.step 21 (.step 28 (.close 52))))))))) (.step 52 (.step 58 (.step 7 (.step 9 (.step 16 (.step 7 (.close 21))))))))) (.step 54 (.split 55 1 (.split 56 1 (.step 46 (.split 25 0 (.split 38 0 (.step 7 (.step 9 (.step 7 (.step 27 (.close 46))))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 46 (.close 52))))))) (.step 7 (.step 29 (.step 45 (.step 16 (.step 21 (.step 22 (.step 45 (.close 52))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346508060100310036683621826611287658399569242318072679669193227563159441779366854921301996818978824414822400⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.split 42 1 (.step 58 (.split 43 1 (.split 49 1 (.split 51 1 (.split 67 1 (.step 58 (.step 7 (.step 10 (.step 22 (.step 7 (.step 16 (.step 7 (.close 21)))))))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 7 (.step 9 (.step 54 (.close 21))))) (.step 48 (.step 16 (.step 58 (.step 9 (.close 26)))))) (.step 7 (.step 9 (.close 10))))) (.step 7 (.step 29 (.step 21 (.step 38 (.close 41)))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 45 (.step 7 (.step 28 (.step 22 (.step 16 (.close 21)))))) (.step 7 (.step 22 (.step 29 (.step 21 (.step 38 (.step 16 (.step 22 (.step 16 (.step 39 (.close 45))))))))))) (.step 7 (.step 22 (.step 29 (.step 52 (.step 16 (.step 22 (.step 21 (.step 38 (.close 39))))))))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.step 45 (.split 55 1 (.split 59 1 (.step 37 (.step 7 (.step 16 (.step 22 (.step 16 (.close 21)))))) (.step 7 (.step 16 (.step 22 (.step 21 (.step 22 (.close 28))))))) (.step 5 (.step 7 (.step 28 (.step 37 (.close 21))))))) (.step 7 (.step 29 (.step 37 (.close 21))))) (.step 7 (.step 16 (.step 37 (.close 52))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346508060100310038720657802945775553919410948789671030933787587844363013977094851835157240217394550776266752⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.step 7 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.reuse 0) (.run (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.step 28 (.step 7 (.step 10 (.step 7 (.step 16 (.step 7 (.close 21))))))) (.step 5 (.step 9 (.step 26 (.step 28 (.close 7)))))) (.step 7 (.step 28 (.step 9 (.step 26 (.close 28)))))) (.step 5 (.step 9 (.step 58 (.split 38 1 (.step 21 (.step 58 (.close 26))) (.step 21 (.close 22))))))) (.step 58 (.step 9 (.step 16 (.step 58 (.close 26)))))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 28 (.step 7 (.step 28 (.step 16 (.step 21 (.close 29)))))))) (.step 7 (.step 28 (.step 7 (.step 22 (.step 28 (.step 16 (.step 21 (.close 29))))))))) (.step 7 (.step 16 (.step 28 (.step 4 (.close 7)))))))) (.run (.step 7 (.step 5 (.step 4 (.close 18)))))) (.run (.step 7 (.step 18 (.split 25 1 (.step 7 (.close 52)) (.step 4 (.step 5 (.close 28)))))))) (.run (.step 7 (.step 18 (.split 25 1 (.split 38 1 (.step 7 (.step 19 (.close 52))) (.step 4 (.step 5 (.close 19)))) (.step 4 (.step 7 (.step 19 (.close 28))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case52
