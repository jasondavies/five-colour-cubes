module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case91
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300298891045423258397181086105194016944922857351016204877651967375440348636285763584⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32016031753816107707383, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699533605928482613073959526943958677216822273, 0⟩]
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723970045351180113510613693152386674714095504997968065450791043968172285861894438559294994463033013331830513038323870676032841985262360422215089066203351995102605082624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 71 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 72 1 (.step 71 (.split 21 0 (.split 26 0 (.step 3 (.close 7)) (.step 3 (.close 29))) (.step 3 (.step 18 (.close 4))))) (.step 3 (.step 29 (.step 26 (.step 31 (.step 18 (.close 71))))))) (.step 71 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 72 (.close 7)) (.step 3 (.close 72))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.close 31))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.close 75))))) (.step 3 (.close 70))) (.split 67 1 (.split 72 1 (.step 65 (.split 10 0 (.split 12 0 (.split 16 0 (.step 72 (.split 22 0 (.split 26 0 (.step 65 (.close 3)) (.step 3 (.close 28))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.close 65))) (.step 3 (.close 71))) (.step 3 (.step 7 (.close 52))))) (.step 3 (.step 21 (.close 71)))) (.step 3 (.close 70)))) (.split 62 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 16 0 (.step 72 (.split 17 0 (.split 21 0 (.step 64 (.close 71)) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 7 (.close 64)))) (.step 3 (.close 64))) (.step 3 (.step 15 (.close 71)))) (.step 3 (.close 70))) (.step 71 (.split 72 1 (.step 64 (.close 3)) (.step 3 (.close 64)))))) (.step 26 (.split 61 1 (.split 68 1 (.split 62 1 (.step 62 (.step 3 (.step 7 (.close 70)))) (.step 3 (.step 65 (.step 7 (.close 62))))) (.step 3 (.close 62))) (.step 3 (.step 64 (.step 7 (.close 62)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663450964914574338333518811909397372374160509255057738462230134292727774933790460175968641888206299246162790580224⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.step 3 (.split 59 1 (.step 71 (.split 61 1 (.split 62 1 (.step 9 (.step 57 (.step 3 (.step 71 (.step 57 (.close 3)))))) (.step 3 (.close 57))) (.step 3 (.step 57 (.close 64))))) (.step 57 (.step 3 (.close 4))))))) (.run (.step 3 (.step 54 (.close 64))))) (.run (.step 53 (.step 57 (.step 71 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 72 1 (.split 68 1 (.split 54 1 (.step 53 (.step 3 (.close 7))) (.step 21 (.step 3 (.close 57)))) (.step 3 (.close 53))) (.step 21 (.step 26 (.step 55 (.step 3 (.step 29 (.step 3 (.close 53)))))))) (.step 53 (.close 70))) (.step 53 (.close 7))) (.step 3 (.step 64 (.step 7 (.close 53))))) (.step 53 (.close 54)))))))) (.run (.step 52 (.step 57 (.step 71 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 72 1 (.split 68 1 (.split 69 1 (.split 16 0 (.split 54 1 (.step 52 (.step 3 (.close 4))) (.step 57 (.close 3))) (.step 18 (.close 52))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.close 52))) (.step 26 (.step 55 (.step 57 (.step 52 (.close 3)))))) (.step 52 (.close 70))) (.step 3 (.step 65 (.step 7 (.close 52))))) (.step 3 (.close 64))) (.step 52 (.close 54)))))))) (.run (.step 3 (.step 52 (.step 53 (.step 62 (.step 46 (.step 10 (.step 30 (.step 46 (.close 64))))))))))) (.run (.split 49 1 (.split 50 1 (.step 31 (.close 7)) (.step 31 (.close 53))) (.step 31 (.close 52)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300295185698567660905643189325198356435828200115297593084216079601456663775808585728⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 31 (.step 75 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.close 7)) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.step 7 (.close 29)))))))) (.run (.step 3 (.step 9 (.step 21 (.step 57 (.step 71 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 61 1 (.split 69 1 (.step 75 (.split 54 1 (.split 68 1 (.split 72 1 (.step 3 (.step 29 (.step 18 (.close 38)))) (.step 29 (.step 3 (.close 38)))) (.step 4 (.step 3 (.close 38)))) (.step 21 (.step 29 (.step 38 (.step 18 (.close 57))))))) (.step 3 (.step 31 (.close 38)))) (.step 3 (.step 38 (.close 71)))) (.step 3 (.step 21 (.step 26 (.step 29 (.step 3 (.close 38))))))) (.step 3 (.step 21 (.step 38 (.step 57 (.step 62 (.step 29 (.step 40 (.step 71 (.step 52 (.step 26 (.step 3 (.close 15))))))))))))) (.step 31 (.step 3 (.close 38)))) (.step 31 (.step 29 (.close 39))))))))))) (.run (.step 7 (.step 31 (.step 38 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.close 7)) (.step 15 (.step 31 (.close 52)))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.close 37))))))))) (.run (.step 31 (.split 35 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.close 31))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300298891045423258397181086105194014021919582686551909943411269740607892210453577728⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 21 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 57 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 29 (.step 3 (.step 71 (.step 29 (.split 54 1 (.step 3 (.step 29 (.close 3))) (.step 29 (.close 3))))))) (.step 3 (.step 28 (.step 29 (.close 65))))) (.step 3 (.step 31 (.step 29 (.close 71))))) (.step 3 (.step 27 (.step 29 (.step 57 (.step 62 (.close 3))))))) (.step 27 (.step 29 (.step 57 (.split 34 0 (.step 53 (.close 3)) (.step 3 (.close 29))))))) (.step 3 (.step 27 (.step 29 (.step 52 (.step 57 (.split 26 2 (.step 52 (.close 3)) (.step 29 (.close 3))))))))) (.step 21 (.step 29 (.step 3 (.step 29 (.step 3 (.step 21 (.close 29))))))))))) (.run (.step 7 (.step 26 (.step 18 (.close 7)))))) (.run (.step 3 (.step 18 (.step 31 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 72 1 (.split 68 1 (.split 54 1 (.split 61 1 (.step 31 (.split 62 1 (.step 18 (.step 3 (.close 4))) (.step 10 (.step 21 (.step 4 (.step 22 (.step 4 (.close 24)))))))) (.step 30 (.step 64 (.step 31 (.step 5 (.close 64)))))) (.step 4 (.step 3 (.close 57)))) (.step 4 (.close 63))) (.step 4 (.step 18 (.close 75)))) (.step 3 (.step 18 (.close 34)))) (.step 3 (.step 18 (.close 53)))) (.step 4 (.step 18 (.close 52)))) (.step 4 (.step 18 (.close 38)))) (.step 4 (.step 18 (.close 29))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.step 22 (.step 18 (.close 7))) (.step 7 (.close 18)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300298891045423258397181086105194016944922857351016204877651967375440348636285763584⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.step 18 (.close 7))) (.step 7 (.close 18))) (.step 7 (.close 18))))))) (.run (.step 18 (.step 15 (.step 21 (.step 22 (.step 26 (.split 21 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.step 71 (.split 61 1 (.step 57 (.step 3 (.split 62 1 (.step 9 (.split 69 1 (.step 15 (.step 3 (.step 15 (.step 18 (.step 15 (.close 18)))))) (.step 3 (.close 15)))) (.step 3 (.close 15))))) (.step 3 (.step 15 (.close 64)))))) (.step 15 (.step 3 (.close 4)))) (.step 15 (.close 53))) (.step 15 (.step 3 (.close 52)))) (.step 21 (.step 15 (.close 38)))) (.step 15 (.step 29 (.close 3)))) (.step 4 (.step 15 (.close 3))))))))))) (.run (.step 31 (.split 26 1 (.split 35 1 (.split 49 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 15))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 29))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part4.excludes
end FiveColour.Packed.ProjectedChunks.Case91
