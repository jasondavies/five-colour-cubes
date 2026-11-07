module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case92
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900391752254130578073414866733319883587584⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32016031753816174816183, 5789234131009374243490890256636772759901851996560544808214778193549775928795277575978058672488451386148482820637016487820419584261128081612316866307095117301248629629600134054099986200052311922515709018284938770805055030273, 0⟩]
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723970045351180113510613693152386674714095504997968065450791043968172285861894438559294992610359585534771386261188110537026316332942605771966064434883160789997137690624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 71 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 72 1 (.split 68 1 (.split 21 0 (.split 34 0 (.split 6 0 (.step 3 (.close 7)) (.step 3 (.close 4))) (.step 7 (.step 3 (.close 15)))) (.step 3 (.step 9 (.step 3 (.close 40))))) (.step 3 (.close 71))) (.step 3 (.step 75 (.step 26 (.step 9 (.step 18 (.close 71))))))) (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 72 (.close 7)) (.step 3 (.step 7 (.close 27)))) (.step 3 (.close 31))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.close 9))) (.step 3 (.step 4 (.close 75))))) (.step 3 (.close 70))) (.step 72 (.split 67 1 (.split 72 1 (.split 6 0 (.split 10 0 (.step 65 (.split 12 0 (.split 17 0 (.step 65 (.close 3)) (.step 3 (.step 7 (.close 27)))) (.step 3 (.close 31)))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.close 9))) (.step 3 (.step 9 (.close 71)))) (.step 3 (.close 70))))) (.step 72 (.split 62 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 10 0 (.step 72 (.split 16 0 (.split 17 0 (.step 64 (.close 3)) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.close 64))) (.step 3 (.close 9))) (.step 3 (.step 9 (.close 64)))) (.step 3 (.close 70))) (.step 64 (.step 3 (.step 9 (.close 64))))))) (.step 26 (.split 61 1 (.split 62 1 (.step 62 (.step 3 (.step 7 (.close 70)))) (.step 3 (.step 65 (.step 7 (.close 62))))) (.step 3 (.step 64 (.step 7 (.close 62)))))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419363043606477426946928350824370933873160537618234527129738701615067723752852566291176249331458783378106145789677199049706094723072⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.step 3 (.split 59 1 (.step 71 (.split 61 1 (.split 62 1 (.step 9 (.step 57 (.step 3 (.step 57 (.step 71 (.close 3)))))) (.step 3 (.close 57))) (.step 3 (.step 57 (.close 64))))) (.step 9 (.step 26 (.step 3 (.step 18 (.close 57))))))))) (.run (.step 3 (.step 54 (.close 64))))) (.run (.step 53 (.step 57 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 54 1 (.step 53 (.step 3 (.close 4))) (.step 9 (.step 3 (.close 57)))) (.step 9 (.step 21 (.step 26 (.step 3 (.close 75)))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 4 (.step 9 (.close 53))))) (.step 53 (.close 70))) (.step 3 (.close 65))) (.step 3 (.step 64 (.step 7 (.close 53))))) (.step 53 (.close 54))))))) (.run (.step 52 (.step 57 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 54 1 (.step 52 (.step 3 (.close 4))) (.step 9 (.step 3 (.close 57)))) (.step 18 (.close 52))) (.step 9 (.step 26 (.step 55 (.step 52 (.close 3)))))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.step 4 (.step 9 (.close 71))))) (.step 52 (.close 70))) (.step 3 (.step 65 (.step 7 (.close 52))))) (.step 3 (.close 64))) (.step 52 (.close 54))))))) (.run (.step 3 (.step 52 (.step 53 (.step 62 (.step 46 (.step 10 (.step 30 (.step 46 (.close 64)))))))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867216509745583268191762679433672996777039834501098837018808292474880⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 7)) (.step 9 (.close 31))) (.step 31 (.close 53))) (.step 31 (.close 52))))) (.run (.step 31 (.step 57 (.step 75 (.split 49 1 (.split 50 1 (.step 31 (.close 7)) (.step 31 (.close 53))) (.step 31 (.close 52)))))))) (.run (.step 3 (.step 9 (.step 21 (.step 57 (.step 71 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 61 1 (.split 69 1 (.step 75 (.step 3 (.split 54 1 (.split 68 1 (.split 72 1 (.step 3 (.step 21 (.step 9 (.close 38)))) (.step 38 (.close 3))) (.step 4 (.step 3 (.close 38)))) (.step 9 (.step 21 (.step 38 (.step 18 (.close 57)))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 31 (.step 57 (.close 71))))) (.step 9 (.step 21 (.step 26 (.step 3 (.close 38)))))) (.step 3 (.step 9 (.step 21 (.step 38 (.step 52 (.step 40 (.step 57 (.step 71 (.step 52 (.step 26 (.step 3 (.close 15))))))))))))) (.step 31 (.close 45))) (.step 31 (.close 39)))))))))) (.run (.step 7 (.step 31 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 7)) (.step 15 (.close 31))) (.step 9 (.step 15 (.step 31 (.close 52))))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.close 37)))))))) (.run (.step 31 (.split 35 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.close 31)))))) (.run (.step 7 (.step 26 (.step 18 (.close 7))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900391752251595276872956102087317263482880⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 72 1 (.split 68 1 (.split 54 1 (.split 61 1 (.step 31 (.split 62 1 (.step 3 (.step 18 (.step 4 (.close 5)))) (.step 10 (.step 21 (.step 3 (.step 22 (.step 4 (.close 24)))))))) (.step 10 (.step 64 (.step 31 (.step 5 (.close 64)))))) (.step 4 (.step 3 (.close 57)))) (.step 4 (.close 63))) (.step 4 (.step 9 (.step 18 (.close 31))))) (.step 3 (.step 9 (.step 18 (.close 34))))) (.step 3 (.step 18 (.close 53)))) (.step 4 (.step 18 (.step 34 (.close 52))))) (.step 18 (.step 31 (.close 38))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.step 22 (.step 18 (.close 7))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.step 18 (.close 7))) (.step 7 (.close 18))) (.step 7 (.close 18))))))) (.run (.step 18 (.step 15 (.step 21 (.step 22 (.step 26 (.split 21 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.split 61 1 (.step 57 (.step 3 (.step 71 (.split 62 1 (.step 9 (.split 69 1 (.step 15 (.step 3 (.step 15 (.step 3 (.step 15 (.close 3)))))) (.step 3 (.close 15)))) (.step 3 (.close 15)))))) (.step 3 (.step 15 (.close 64))))) (.step 15 (.step 3 (.close 4)))) (.step 15 (.close 53))) (.step 15 (.step 3 (.close 52)))) (.step 21 (.step 15 (.close 38)))) (.step 4 (.step 15 (.close 3)))))))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900391752254130578073414866733319883587584⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.step 15 (.step 31 (.split 35 1 (.split 49 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 9))) (.step 3 (.close 18))) (.step 3 (.close 31)))))))) (.run (.step 9 (.step 18 (.step 9 (.step 10 (.step 18 (.step 9 (.step 3 (.close 31))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case92
