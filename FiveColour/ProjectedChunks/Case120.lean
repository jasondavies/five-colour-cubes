module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case120
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 15410569095717432481535464385687030409294294611718197590307904932128702664653758458985750653254047969415741066085507295890927596006104333592161011654483935797504528678670512667404759083363659870776496383590400⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37033564156298044177399, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969540306823801303036701114543271236497705040614186417671967029225310810172032001, 0⟩]
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
def root : Box := ⟨3221225472, 15410569095717432481535455887479145341020715578306892744099410519110697151463852969117075830388944144123030108574788741461933122777179159741630822403940157454646493282628842469649814122281935574763039142969344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 62 1 (.step 70 (.step 7 (.split 17 0 (.split 36 0 (.split 22 0 (.step 72 (.split 42 0 (.split 10 0 (.split 16 0 (.step 53 (.step 7 (.close 9))) (.step 7 (.step 27 (.close 36)))) (.step 7 (.close 52))) (.step 7 (.step 9 (.close 22))))) (.step 7 (.step 27 (.step 36 (.close 44))))) (.step 7 (.step 9 (.step 22 (.close 26))))) (.step 7 (.step 27 (.step 36 (.close 44))))))) (.step 65 (.step 70 (.split 67 1 (.split 69 1 (.split 17 0 (.step 65 (.close 7)) (.step 7 (.step 27 (.step 36 (.close 44))))) (.step 65 (.close 7))) (.step 65 (.close 7)))))) (.step 70 (.split 62 1 (.split 69 1 (.split 17 0 (.split 22 0 (.step 62 (.close 7)) (.step 7 (.step 27 (.step 36 (.close 44))))) (.step 7 (.step 27 (.step 36 (.close 44))))) (.split 17 0 (.split 36 0 (.step 62 (.step 72 (.step 4 (.close 7)))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 26 (.step 52 (.close 53)))))))) (.step 4 (.step 7 (.step 27 (.step 36 (.step 44 (.step 52 (.close 53))))))))) (.step 65 (.step 53 (.split 17 0 (.split 10 0 (.split 22 0 (.split 43 0 (.split 51 0 (.step 65 (.step 4 (.close 7))) (.step 54 (.step 62 (.step 4 (.step 22 (.close 36)))))) (.step 9 (.step 27 (.step 62 (.close 65))))) (.step 4 (.step 7 (.step 27 (.step 44 (.step 36 (.close 52))))))) (.step 7 (.step 52 (.step 62 (.close 65))))) (.step 4 (.step 7 (.step 27 (.step 44 (.step 36 (.close 52)))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 15410569095717432481535464385687030409294294611718197590307898538787671617501663038719865298890018112147196753615572289727578107636033777196350757217313082057280026296446648303942821142647324700378025208840192⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 61 1 (.split 50 1 (.reuse 0) (.run (.step 53 (.step 65 (.step 70 (.split 69 1 (.split 59 1 (.step 70 (.split 17 0 (.step 53 (.close 7)) (.step 7 (.step 27 (.step 36 (.close 53)))))) (.step 53 (.close 7))) (.step 53 (.step 65 (.step 70 (.split 10 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.step 53 (.step 4 (.close 7))) (.step 22 (.step 36 (.step 52 (.close 53))))) (.step 9 (.step 27 (.close 53)))) (.step 4 (.step 7 (.step 27 (.step 36 (.step 44 (.close 52))))))) (.step 4 (.step 7 (.step 27 (.step 36 (.step 44 (.close 52))))))) (.step 7 (.step 52 (.close 53))))))))))))) (.run (.step 64 (.split 67 1 (.split 62 1 (.split 69 1 (.split 50 1 (.split 59 1 (.split 17 0 (.step 64 (.step 4 (.close 7))) (.step 7 (.step 27 (.step 36 (.close 44))))) (.step 52 (.split 17 0 (.step 64 (.step 7 (.step 9 (.step 27 (.close 53))))) (.step 4 (.step 7 (.step 27 (.step 44 (.step 36 (.close 53))))))))) (.step 52 (.step 53 (.step 65 (.split 17 0 (.step 64 (.step 7 (.step 9 (.close 27)))) (.step 4 (.step 7 (.step 27 (.step 36 (.close 44)))))))))) (.step 64 (.step 7 (.close 53)))) (.step 64 (.step 7 (.close 53)))) (.step 53 (.step 62 (.step 64 (.close 70)))))))) (.run (.step 53 (.step 54 (.step 62 (.step 54 (.step 64 (.step 54 (.step 22 (.step 36 (.step 54 (.step 64 (.step 54 (.close 65))))))))))))))
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
def root : Box := ⟨3221225472, 15410569095717432481535464385687030409294294611718197590307904932128702664653758458985750653254047964718651421048356480429473334873896969415344923734760009147945586570763805146010319273990647598921341667901440⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 67 1 (.split 50 1 (.step 64 (.split 62 1 (.split 69 1 (.split 59 1 (.split 17 0 (.step 52 (.step 4 (.close 7))) (.step 7 (.step 27 (.step 36 (.close 52))))) (.step 52 (.close 7))) (.step 52 (.step 64 (.split 30 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.step 52 (.step 4 (.close 7))) (.step 22 (.step 36 (.close 52)))) (.step 9 (.step 27 (.close 52)))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 26 (.close 52))))))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 26 (.close 52))))))) (.step 7 (.step 52 (.close 53))))))) (.step 64 (.step 53 (.step 65 (.step 52 (.split 36 0 (.step 65 (.step 7 (.step 9 (.close 27)))) (.step 4 (.step 7 (.step 9 (.step 22 (.close 26)))))))))))) (.step 52 (.step 7 (.step 52 (.close 53))))) (.step 52 (.step 65 (.close 70)))) (.step 52 (.close 54)))))) (.run (.step 46 (.step 52 (.step 53 (.step 62 (.step 64 (.step 65 (.step 72 (.split 49 1 (.split 50 1 (.step 46 (.split 61 1 (.split 17 0 (.step 46 (.close 7)) (.step 7 (.step 27 (.close 30)))) (.step 10 (.step 30 (.close 46))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46))))))))))))) (.run (.step 7 (.split 49 1 (.step 31 (.split 61 1 (.step 7 (.step 10 (.step 18 (.close 31)))) (.step 10 (.step 18 (.step 31 (.close 64)))))) (.step 7 (.step 9 (.step 18 (.step 31 (.close 52)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 15410569095717432481535464385687030409294294611718197590307904932128702664653758458985750653254047969415741066085507295890927596006104333592161011654483935797504528678670512667404759083363659870776496383590400⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 10 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 42 1 (.split 49 1 (.step 31 (.split 61 1 (.step 7 (.step 10 (.step 18 (.close 31)))) (.step 10 (.step 18 (.step 31 (.close 64)))))) (.step 7 (.step 9 (.step 18 (.step 31 (.close 52)))))) (.step 7 (.close 31)))))) (.run (.step 7 (.split 36 1 (.split 42 1 (.split 49 1 (.step 31 (.split 61 1 (.step 7 (.step 10 (.step 16 (.step 18 (.close 31))))) (.step 10 (.step 16 (.step 18 (.step 31 (.close 64))))))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 31 (.close 52))))))) (.step 7 (.close 31))) (.step 31 (.step 7 (.close 37))))))) (.run (.step 7 (.split 49 1 (.step 18 (.step 7 (.step 18 (.close 64)))) (.step 7 (.step 18 (.close 52))))))) (.run (.step 7 (.split 49 1 (.step 18 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64)))) (.step 7 (.step 18 (.close 52))))))) (.run (.step 7 (.split 22 1 (.split 49 1 (.step 18 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64)))) (.step 7 (.step 18 (.close 52)))) (.step 7 (.close 18)))))) (.run (.step 7 (.split 49 1 (.step 18 (.step 7 (.step 18 (.close 64)))) (.step 7 (.step 18 (.close 52))))))) (.run (.step 7 (.split 17 1 (.split 22 1 (.split 49 1 (.step 18 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64)))) (.step 7 (.step 18 (.close 52)))) (.step 7 (.close 18))) (.step 18 (.step 7 (.close 19)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case120
