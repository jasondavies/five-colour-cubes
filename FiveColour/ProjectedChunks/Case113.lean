module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case113
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418663330879116423184506546400681381766544520965642277752735860326091826164400128⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555258632336548123135211779362607014491560817380790703488300182096482310202940080247430800253393876000549635595664621568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.step 58 (.split 49 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 55 1 (.split 50 1 (.step 7 (.step 9 (.step 3 (.step 16 (.close 21))))) (.step 62 (.step 31 (.close 3)))) (.step 3 (.step 31 (.step 48 (.step 21 (.close 53)))))) (.step 3 (.step 7 (.step 26 (.step 44 (.step 53 (.close 52))))))) (.step 3 (.step 22 (.step 31 (.step 21 (.step 28 (.step 21 (.step 28 (.close 53))))))))) (.step 3 (.step 53 (.close 54)))) (.step 58 (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.step 31 (.step 3 (.close 21))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 52)))))) (.step 52 (.split 56 1 (.step 62 (.close 3)) (.step 3 (.step 16 (.step 22 (.step 31 (.step 21 (.close 52))))))))) (.step 3 (.step 52 (.close 7)))) (.step 52 (.split 56 1 (.split 30 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.step 9 (.step 7 (.step 16 (.step 21 (.step 22 (.close 29)))))))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 16 (.step 21 (.step 22 (.step 29 (.step 31 (.close 52))))))))))))) (.step 3 (.step 46 (.step 52 (.step 53 (.step 7 (.step 9 (.step 27 (.close 46))))))))) (.step 7 (.step 31 (.split 49 1 (.step 31 (.step 7 (.step 22 (.close 28)))) (.step 9 (.step 18 (.step 31 (.close 52)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418659712376324387060066165974429448536009877842467182633787973055933785808306176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 3 (.step 21 (.step 58 (.split 42 1 (.split 49 1 (.step 58 (.split 56 1 (.step 3 (.step 28 (.step 16 (.step 21 (.step 16 (.close 22)))))) (.step 28 (.step 3 (.step 41 (.close 3)))))) (.step 3 (.step 16 (.step 21 (.step 31 (.step 41 (.step 52 (.close 58)))))))) (.step 31 (.step 3 (.step 28 (.step 3 (.close 41))))))))))) (.run (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 22 (.close 28)))) (.step 9 (.step 18 (.step 22 (.step 31 (.close 52)))))) (.step 31 (.step 7 (.step 28 (.step 3 (.step 22 (.close 39))))))) (.step 21 (.step 31 (.step 28 (.close 39))))))))) (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 22 (.close 28)))) (.step 9 (.step 15 (.step 16 (.step 18 (.step 31 (.close 52))))))) (.step 31 (.step 7 (.step 28 (.step 3 (.close 37)))))) (.step 16 (.step 21 (.step 28 (.step 31 (.step 37 (.close 3))))))) (.step 31 (.close 37))))))) (.run (.step 3 (.step 7 (.step 18 (.close 52))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418663330879116423184506546400681381766544520965642277752735860326091826164400128⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.reuse 0) (.run (.step 3 (.step 10 (.step 58 (.split 34 1 (.split 36 1 (.split 38 1 (.step 3 (.split 42 1 (.split 49 1 (.split 50 1 (.step 28 (.step 3 (.step 28 (.step 3 (.close 28))))) (.step 3 (.step 21 (.step 28 (.step 29 (.step 53 (.step 28 (.close 58)))))))) (.step 3 (.step 31 (.step 52 (.close 58))))) (.step 28 (.step 29 (.step 3 (.step 22 (.close 28))))))) (.step 21 (.step 28 (.step 3 (.step 58 (.step 28 (.close 3))))))) (.step 3 (.step 28 (.step 29 (.step 3 (.step 22 (.close 28))))))) (.step 3 (.step 16 (.step 28 (.step 29 (.step 3 (.step 22 (.close 28))))))))))))) (.run (.step 7 (.step 18 (.split 25 1 (.step 18 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 28)))))))) (.run (.step 7 (.step 18 (.split 22 1 (.split 25 1 (.step 18 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 28)))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 25 1 (.step 18 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 28)))) (.step 7 (.close 18))) (.step 7 (.close 18))))))) (.run (.step 3 (.step 7 (.split 25 1 (.step 3 (.step 7 (.step 18 (.close 52)))) (.step 3 (.close 28)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case113
