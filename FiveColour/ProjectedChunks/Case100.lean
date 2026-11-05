module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case100
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418663330879116423184506546400681381766544520965642277752735860326095124699283456⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37630669409018422557671, 5789234131004114112605798393242650429804653116085229495907826956687667789262928691629928794709070122937714079890866485902908449148557118512623615738864880308980283049286057048738638195494140525221857074735173807150830978049, 0⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418659712376324387060066165974429448536009877842467182633787973055934885319933952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 1 (.split 36 1 (.split 38 1 (.split 30 1 (.split 42 1 (.split 43 1 (.step 58 (.split 49 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 50 1 (.step 7 (.step 3 (.step 16 (.close 21)))) (.step 31 (.step 3 (.close 53)))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 53)))))) (.step 3 (.step 22 (.step 31 (.step 21 (.step 28 (.close 53))))))) (.step 3 (.step 53 (.step 7 (.step 53 (.step 7 (.step 26 (.step 44 (.close 54))))))))) (.step 58 (.step 62 (.split 50 1 (.step 54 (.step 70 (.split 51 1 (.step 31 (.step 3 (.close 21))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 52)))))))) (.step 52 (.step 31 (.step 3 (.close 21))))))))) (.step 3 (.step 46 (.step 52 (.step 7 (.step 9 (.step 27 (.close 46)))))))) (.step 7 (.step 31 (.step 3 (.close 7))))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 21 (.step 58 (.split 42 1 (.step 3 (.step 41 (.step 3 (.step 16 (.step 21 (.step 28 (.step 31 (.step 41 (.step 52 (.close 58)))))))))) (.step 31 (.step 3 (.step 28 (.step 3 (.step 22 (.step 39 (.close 41)))))))))))) (.step 7 (.step 31 (.close 39)))) (.step 7 (.step 31 (.step 37 (.step 7 (.step 28 (.step 3 (.step 22 (.close 37))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418663330879116423184506546400681381766544520965642277752735860326095124699283456⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.split 10 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.reuse 0) (.run (.step 3 (.step 58 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.step 3 (.step 58 (.step 28 (.step 3 (.step 16 (.step 21 (.step 22 (.close 28)))))))) (.step 28 (.step 3 (.step 28 (.step 16 (.step 21 (.close 29))))))) (.step 21 (.step 28 (.step 3 (.step 16 (.step 21 (.close 28))))))) (.step 28 (.step 3 (.step 22 (.step 28 (.step 16 (.step 21 (.close 29)))))))) (.step 16 (.step 28 (.step 3 (.step 16 (.step 21 (.close 28))))))))))) (.run (.step 7 (.step 18 (.close 7))))) (.run (.step 7 (.step 18 (.close 7))))) (.run (.step 7 (.step 18 (.close 7))))) (.run (.step 3 (.step 7 (.close 18))))) (.run (.step 3 (.step 7 (.close 18)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part1.excludes
end FiveColour.Packed.ProjectedChunks.Case100
