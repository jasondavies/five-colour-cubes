module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case121
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418657903124933423987846066510759099520863898935111075851296510751841455236448256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37630669409018456112119, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639180033369853557824749914671530180203279448118754128379673028050877429417560652570824680124548036304556207899649, 0⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555258632336548123135211779362607014491560815571539309155234628603185669442191520040087289852760062884024885472021970944⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 58 (.split 56 1 (.split 67 1 (.step 7 (.step 31 (.step 3 (.step 7 (.step 3 (.close 18)))))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 62)))))) (.step 3 (.step 22 (.step 16 (.step 31 (.step 21 (.close 58)))))))) (.step 3 (.close 54))) (.step 58 (.split 51 1 (.split 59 1 (.split 67 1 (.step 31 (.step 53 (.close 3))) (.step 3 (.step 53 (.close 7)))) (.step 53 (.split 56 1 (.step 62 (.step 3 (.close 7))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 53)))))))) (.step 3 (.step 53 (.step 7 (.step 9 (.step 27 (.close 54))))))))) (.step 58 (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.step 31 (.step 52 (.step 3 (.close 21)))) (.step 3 (.step 52 (.close 7)))) (.step 52 (.split 56 1 (.step 62 (.step 3 (.close 7))) (.step 3 (.step 22 (.step 31 (.step 21 (.close 52)))))))) (.step 3 (.step 52 (.step 7 (.step 9 (.step 27 (.close 54))))))) (.step 52 (.split 56 1 (.split 30 0 (.split 36 0 (.step 52 (.close 3)) (.step 9 (.step 18 (.step 21 (.step 31 (.close 26)))))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 52)))))))))) (.step 3 (.step 46 (.step 52 (.step 53 (.step 62 (.split 49 1 (.step 7 (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46)))))))))) (.step 7 (.step 31 (.split 49 1 (.step 31 (.step 7 (.step 22 (.step 39 (.step 41 (.close 45)))))) (.step 9 (.step 18 (.step 31 (.close 52)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418657903124933423987846066510756176517589237129274668481631078185802143371362304⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 34 1 (.split 10 1 (.split 30 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 3 (.step 21 (.step 58 (.split 42 1 (.split 49 1 (.split 59 1 (.split 56 1 (.step 3 (.step 16 (.close 31))) (.step 28 (.step 41 (.split 10 0 (.split 17 0 (.step 41 (.close 3)) (.step 3 (.step 18 (.close 39)))) (.step 3 (.close 41)))))) (.step 3 (.step 21 (.step 31 (.step 41 (.close 58)))))) (.step 3 (.step 21 (.step 16 (.step 31 (.step 41 (.step 52 (.close 58)))))))) (.step 31 (.step 3 (.step 28 (.close 41)))))))))) (.run (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 22 (.close 39)))) (.step 9 (.step 18 (.step 22 (.step 31 (.close 52)))))) (.step 31 (.step 7 (.step 28 (.close 39))))) (.step 21 (.step 31 (.step 28 (.step 39 (.close 3)))))))))) (.run (.step 3 (.step 7 (.step 18 (.close 52)))))) (.run (.step 3 (.step 7 (.step 18 (.close 52)))))) (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.step 31 (.step 7 (.step 22 (.close 37)))) (.step 9 (.step 15 (.step 16 (.step 18 (.step 31 (.close 52))))))) (.step 31 (.step 7 (.step 28 (.close 37))))) (.step 16 (.step 21 (.step 31 (.step 28 (.step 37 (.close 3))))))) (.step 31 (.close 37))))))) (.run (.step 7 (.step 18 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 52))))))) (.run (.step 7 (.step 18 (.split 22 1 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 52))) (.step 7 (.close 18)))))))
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
def root : Box := ⟨3221225472, 14696649931972027310843563360988823352544558495788992882167145842741792590283978775555263557592019762090150465058080986704418657903124933423987846066510759099520863898935111075851296510751841455236448256⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 52))) (.step 7 (.close 18))) (.step 18 (.step 7 (.close 19))))))))
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
end FiveColour.Packed.ProjectedChunks.Case121
