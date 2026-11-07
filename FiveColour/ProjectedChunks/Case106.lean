module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case106
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900391752254130578073411407968806063046656⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32016031753816174816247, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859360537049889235969407502623246962523112449, 0⟩]
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
def root : Box := ⟨3221225472, 16546956804726563904923843341139074970125335771864222515327851842760435797046250090572257438483184792151178439388961173410546439713335097602099406563871990785697950776998590819524241315394866968719372952682566489473024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 72 1 (.split 68 1 (.split 21 0 (.split 34 0 (.split 12 0 (.step 3 (.close 7)) (.step 3 (.close 4))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 3 (.step 18 (.close 4)))) (.step 3 (.close 71))) (.step 3 (.split 68 1 (.step 26 (.step 31 (.step 40 (.close 3)))) (.step 4 (.close 75))))) (.split 72 1 (.split 68 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 72 (.close 7)) (.step 7 (.close 72))) (.step 7 (.close 72))) (.step 3 (.close 31))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.close 71))) (.step 31 (.close 71)))) (.step 3 (.close 70))) (.split 67 1 (.split 69 1 (.split 72 1 (.split 68 1 (.split 10 0 (.split 12 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 65 (.close 3)) (.step 3 (.close 21))) (.step 7 (.close 65))) (.step 7 (.close 65))) (.step 3 (.close 31))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.close 71))) (.step 3 (.step 21 (.close 71)))) (.step 71 (.step 72 (.step 7 (.close 21))))) (.step 3 (.step 65 (.close 7))))) (.split 62 1 (.split 67 1 (.split 69 1 (.split 72 1 (.split 68 1 (.split 16 0 (.split 17 0 (.split 21 0 (.step 64 (.step 3 (.close 7))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 64)))) (.step 3 (.step 7 (.close 64)))) (.step 3 (.close 71))) (.step 3 (.step 15 (.close 71)))) (.step 71 (.step 72 (.step 7 (.close 15))))) (.step 3 (.step 64 (.close 7)))) (.step 64 (.step 71 (.split 30 0 (.step 64 (.step 21 (.close 64))) (.step 3 (.close 64))))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093075572377104832499323948193091619392633598393459906905549328110014170132658294862463832094238167283488160974964313863458221485913562056576236257280000⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 54 1 (.step 71 (.split 59 1 (.reuse 0) (.run (.step 26 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 16 0 (.step 62 (.step 3 (.close 7))) (.step 18 (.close 62))) (.step 3 (.step 62 (.step 7 (.close 72))))) (.step 62 (.close 70))) (.step 3 (.step 65 (.step 7 (.close 70))))) (.step 3 (.step 64 (.step 7 (.close 70))))))))) (.run (.split 59 1 (.step 71 (.split 61 1 (.split 62 1 (.split 72 1 (.step 3 (.split 69 1 (.step 57 (.close 71)) (.step 3 (.close 57)))) (.step 26 (.step 57 (.close 3)))) (.step 3 (.step 57 (.close 65)))) (.step 3 (.step 57 (.step 21 (.close 64)))))) (.step 57 (.step 3 (.close 4)))))) (.run (.step 3 (.step 54 (.step 22 (.step 36 (.step 54 (.close 64)))))))) (.run (.step 57 (.split 51 1 (.split 61 1 (.step 53 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 54 1 (.step 53 (.step 3 (.close 7))) (.step 21 (.step 3 (.close 57)))) (.step 21 (.step 26 (.step 55 (.step 3 (.step 57 (.close 3))))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 18 (.step 53 (.close 57))))) (.step 53 (.close 70))) (.step 3 (.close 65)))) (.step 3 (.step 53 (.step 64 (.step 53 (.close 7)))))) (.step 53 (.close 54))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455661999739885999974590870590949195541832823096428324835788735664313699520934742606544654881724656958780211200⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 57 (.split 51 1 (.split 61 1 (.split 62 1 (.step 52 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 17 0 (.split 54 1 (.step 52 (.step 3 (.close 4))) (.step 57 (.close 3))) (.step 18 (.close 52))) (.step 26 (.step 55 (.step 57 (.step 52 (.close 3)))))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.step 12 (.close 71)))) (.step 52 (.close 70)))) (.step 3 (.step 52 (.step 65 (.step 52 (.close 7)))))) (.step 3 (.step 52 (.close 64)))) (.step 52 (.close 54)))))) (.run (.step 3 (.step 52 (.step 53 (.step 62 (.step 64 (.step 65 (.step 72 (.split 17 0 (.step 46 (.close 7)) (.step 7 (.close 46)))))))))))) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.split 61 1 (.step 7 (.close 31)) (.step 31 (.close 64)))) (.step 31 (.close 57))) (.step 31 (.close 53))) (.step 31 (.close 52))))) (.run (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.split 61 1 (.step 7 (.close 31)) (.step 31 (.close 64)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.step 7 (.close 39)))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867216509745583268191762679433672996777039834501097684097303685627904⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.step 21 (.step 57 (.step 71 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 61 1 (.split 69 1 (.split 72 1 (.split 54 1 (.step 3 (.split 68 1 (.split 12 0 (.step 18 (.close 38)) (.step 21 (.step 18 (.close 38)))) (.step 4 (.close 38)))) (.step 38 (.step 57 (.close 3)))) (.step 29 (.step 38 (.step 3 (.step 38 (.close 3)))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 31 (.step 57 (.close 71))))) (.step 21 (.step 26 (.step 57 (.step 3 (.close 38)))))) (.step 3 (.step 9 (.step 21 (.step 57 (.step 62 (.step 71 (.step 75 (.step 55 (.split 34 0 (.split 36 0 (.step 3 (.close 26)) (.step 3 (.close 38))) (.step 3 (.close 38)))))))))))) (.step 31 (.step 3 (.close 38)))) (.step 3 (.step 31 (.close 39))))))))) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.split 61 1 (.step 7 (.close 31)) (.step 31 (.close 64)))) (.step 15 (.close 31))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.close 37))) (.step 31 (.step 37 (.close 3))))))) (.run (.split 35 1 (.step 3 (.split 49 1 (.step 7 (.close 64)) (.step 18 (.close 52)))) (.step 3 (.close 31))))) (.run (.step 7 (.step 26 (.split 49 1 (.split 50 1 (.step 18 (.step 31 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64))))) (.step 18 (.close 26))) (.step 18 (.close 52)))))))
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
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900389093795603707041209141551692095946752⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 68 1 (.split 72 1 (.split 61 1 (.split 62 1 (.step 3 (.step 31 (.step 18 (.step 22 (.step 4 (.close 5)))))) (.step 10 (.step 21 (.step 65 (.step 31 (.step 3 (.step 22 (.step 4 (.close 24))))))))) (.step 34 (.step 64 (.step 68 (.step 65 (.step 3 (.close 18))))))) (.step 18 (.close 31))) (.step 4 (.close 63))) (.step 3 (.close 18))) (.step 4 (.step 9 (.step 18 (.close 57))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52)))) (.step 18 (.step 31 (.close 38)))))))) (.run (.step 7 (.step 18 (.split 22 1 (.step 22 (.split 49 1 (.split 50 1 (.step 18 (.step 31 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64))))) (.step 18 (.close 22))) (.step 18 (.close 52)))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.split 49 1 (.split 50 1 (.step 18 (.step 31 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64))))) (.step 18 (.close 21))) (.step 18 (.close 52)))) (.step 7 (.close 18))) (.step 7 (.close 18)))))))
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

namespace Part5
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900391752254130578073411407968806063046656⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 21 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.step 21 (.step 22 (.step 26 (.split 59 1 (.step 31 (.step 71 (.split 61 1 (.split 62 1 (.split 72 1 (.step 3 (.split 69 1 (.step 15 (.close 71)) (.step 3 (.close 15)))) (.step 15 (.step 26 (.step 3 (.close 15))))) (.step 3 (.step 15 (.close 65)))) (.step 3 (.step 15 (.close 64)))))) (.step 15 (.step 3 (.close 4)))))))) (.step 21 (.step 15 (.step 3 (.step 4 (.close 15)))))) (.step 21 (.step 15 (.close 53)))) (.step 12 (.step 21 (.step 15 (.step 26 (.close 52)))))) (.step 21 (.step 15 (.step 18 (.close 38))))) (.step 4 (.step 15 (.step 3 (.step 18 (.close 15)))))))))) (.run (.split 35 1 (.split 49 1 (.split 54 1 (.step 3 (.step 7 (.close 64))) (.step 3 (.close 15))) (.step 18 (.close 52))) (.step 3 (.close 31)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case106
