module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
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
def root : Box := ⟨3221225472, 16546956804726563904923843341130364307043140791445713268740391357272230469915526767031786554616698173769460462608038908373396679428365312598524963947220306884560446378272274691872469282822988135877672503890446148173824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 69 1 (.split 72 1 (.split 68 1 (.split 10 0 (.split 21 0 (.split 34 0 (.split 12 0 (.step 3 (.close 7)) (.step 3 (.close 4))) (.step 7 (.step 9 (.step 3 (.step 7 (.close 15)))))) (.step 3 (.step 18 (.close 4)))) (.step 3 (.close 7))) (.step 3 (.step 4 (.step 18 (.step 3 (.close 15)))))) (.step 3 (.split 68 1 (.step 26 (.step 31 (.step 26 (.step 40 (.close 3))))) (.step 4 (.step 26 (.step 3 (.step 15 (.close 21)))))))) (.split 72 1 (.split 68 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 72 (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 4 (.step 15 (.close 21))))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 22 (.step 3 (.step 4 (.step 31 (.close 15))))))) (.step 3 (.step 4 (.step 26 (.step 31 (.step 15 (.step 57 (.step 15 (.close 21)))))))))) (.step 3 (.close 70))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291507728875520, 16546956804726563904923843341139074970125335771864222515327851842760435797046250090572257438483184792151178439388961173410546439713335097602099406563871990785697950776998590819524241315394866968719372952682566489473024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 62 1 (.split 67 1 (.split 69 1 (.split 72 1 (.split 68 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 64 (.step 3 (.step 4 (.close 7)))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 31 (.step 21 (.step 3 (.close 4)))))) (.step 3 (.step 4 (.step 15 (.step 26 (.step 21 (.step 31 (.step 21 (.close 57))))))))) (.step 64 (.step 71 (.step 72 (.step 7 (.step 3 (.close 4))))))) (.step 3 (.step 64 (.close 7)))) (.step 64 (.step 71 (.split 21 0 (.split 30 0 (.step 64 (.step 3 (.step 21 (.step 3 (.step 15 (.step 26 (.step 31 (.close 57)))))))) (.step 3 (.step 7 (.step 53 (.close 64))))) (.step 3 (.step 4 (.step 21 (.step 31 (.close 5))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723970045351180113510613693152386674714095504997968065450791043968172285861894438559294992610359585534771386261188110537026316332942605771966064434882007868492530843648⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.step 71 (.split 59 1 (.split 61 1 (.split 62 1 (.reuse 0) (.run (.split 67 1 (.split 69 1 (.split 72 1 (.split 68 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 35 0 (.step 65 (.close 3)) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 7 (.step 52 (.close 53))))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 4 (.step 15 (.close 21))))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 21 (.step 3 (.step 4 (.step 15 (.close 26))))))) (.step 3 (.step 4 (.step 21 (.step 26 (.step 15 (.step 31 (.step 15 (.close 57))))))))) (.step 65 (.step 71 (.step 72 (.step 7 (.step 3 (.close 4))))))) (.step 3 (.step 65 (.close 7)))))) (.reuse 1)) (.run (.step 26 (.split 61 1 (.split 62 1 (.split 68 1 (.split 67 1 (.split 69 1 (.split 16 0 (.step 62 (.step 3 (.close 7))) (.step 18 (.step 3 (.step 27 (.close 36))))) (.step 3 (.step 62 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53)))))))) (.step 3 (.step 26 (.step 44 (.step 62 (.step 7 (.close 70))))))) (.step 3 (.step 4 (.close 12)))) (.step 3 (.step 53 (.step 65 (.step 7 (.step 26 (.step 44 (.step 52 (.close 62))))))))) (.step 3 (.step 64 (.step 7 (.step 26 (.step 44 (.step 53 (.close 62))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093075572377104832499323948193091619392633598393459906905549328110014170132658294862463832094238167283488160974964313863458221485913562056576236257280000⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.step 3 (.split 59 1 (.step 71 (.split 61 1 (.split 62 1 (.split 72 1 (.step 3 (.split 69 1 (.step 57 (.step 3 (.close 4))) (.step 3 (.step 4 (.step 31 (.step 15 (.close 57))))))) (.step 9 (.step 26 (.step 57 (.close 3))))) (.step 3 (.step 4 (.step 21 (.step 57 (.close 65)))))) (.step 3 (.step 57 (.step 21 (.close 64)))))) (.step 3 (.step 9 (.step 26 (.step 57 (.step 3 (.close 4)))))))))) (.run (.step 3 (.step 54 (.step 22 (.step 36 (.step 54 (.close 64)))))))) (.run (.step 53 (.step 57 (.split 51 1 (.split 61 1 (.step 53 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 54 1 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.step 21 (.step 3 (.step 18 (.step 15 (.close 26))))))) (.step 18 (.step 27 (.step 3 (.step 34 (.step 3 (.close 36))))))) (.step 18 (.step 21 (.step 27 (.close 36))))) (.step 9 (.step 21 (.step 26 (.step 55 (.step 3 (.step 57 (.close 3)))))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 4 (.step 18 (.step 21 (.step 12 (.step 26 (.step 12 (.step 53 (.close 57)))))))))) (.step 3 (.step 53 (.step 7 (.close 70))))) (.step 3 (.step 53 (.close 7))))) (.step 3 (.step 53 (.step 64 (.step 7 (.step 53 (.step 4 (.close 7)))))))) (.step 3 (.step 53 (.close 54))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663450964914574338333518811909397370521487081457998611685094374153721249281470705525719617256884955119552716341248⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.step 57 (.split 51 1 (.split 61 1 (.step 53 (.split 62 1 (.step 52 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 54 1 (.step 52 (.step 3 (.close 4))) (.step 9 (.step 57 (.close 3)))) (.step 18 (.step 27 (.step 3 (.step 34 (.step 3 (.close 36))))))) (.step 18 (.step 27 (.step 3 (.step 21 (.close 36)))))) (.step 9 (.step 26 (.step 55 (.step 57 (.step 52 (.close 3))))))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.step 4 (.step 12 (.step 18 (.step 21 (.step 26 (.step 21 (.step 52 (.close 57)))))))))) (.step 3 (.step 52 (.step 7 (.close 70)))))) (.step 3 (.step 52 (.step 53 (.step 64 (.step 65 (.step 7 (.step 52 (.step 4 (.close 7))))))))))) (.step 3 (.step 52 (.close 64)))) (.step 3 (.step 52 (.close 54)))))))) (.run (.step 3 (.step 46 (.step 52 (.step 53 (.step 62 (.step 64 (.step 65 (.step 72 (.split 17 0 (.step 46 (.close 7)) (.step 7 (.step 27 (.close 30)))))))))))))) (.run (.step 7 (.step 31 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.split 61 1 (.step 7 (.step 26 (.step 15 (.step 21 (.close 31))))) (.step 10 (.step 18 (.step 26 (.step 31 (.close 64))))))) (.step 9 (.step 26 (.step 31 (.close 57))))) (.step 7 (.step 9 (.step 18 (.step 21 (.step 26 (.step 31 (.close 53)))))))) (.step 7 (.step 9 (.step 18 (.step 26 (.step 31 (.close 52)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666586737117980117614092232739799715714416226406661398036210841992473366686919576160794918830877210153320448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 21 (.step 57 (.step 71 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 61 1 (.split 69 1 (.split 72 1 (.step 3 (.split 54 1 (.step 3 (.split 68 1 (.split 16 0 (.split 12 0 (.step 18 (.step 21 (.step 3 (.step 4 (.close 15))))) (.step 21 (.step 18 (.step 15 (.step 3 (.close 4)))))) (.step 3 (.close 18))) (.step 4 (.step 21 (.step 3 (.step 15 (.close 26))))))) (.step 9 (.step 21 (.step 38 (.step 57 (.close 3))))))) (.step 29 (.step 38 (.step 3 (.step 38 (.close 3)))))) (.step 3 (.step 4 (.step 21 (.step 31 (.close 38)))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 31 (.step 38 (.step 57 (.step 64 (.close 71)))))))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 40 (.step 57 (.step 3 (.step 31 (.step 3 (.close 12))))))))))) (.step 3 (.step 9 (.step 21 (.step 38 (.step 52 (.step 57 (.step 62 (.step 71 (.step 75 (.step 55 (.split 34 0 (.split 36 0 (.step 3 (.step 12 (.step 15 (.close 26)))) (.step 3 (.step 26 (.close 31)))) (.step 3 (.step 15 (.step 26 (.close 31)))))))))))))))) (.step 3 (.step 31 (.step 3 (.step 26 (.close 38)))))) (.step 3 (.step 31 (.step 29 (.step 38 (.close 3))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867216509745583268191762679433672996777039834501097684097303685627904⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.split 61 1 (.step 7 (.close 31)) (.step 10 (.step 18 (.step 31 (.close 64)))))) (.step 7 (.step 9 (.step 18 (.step 21 (.step 31 (.close 53))))))) (.step 7 (.step 9 (.step 18 (.step 31 (.close 52)))))) (.step 31 (.step 7 (.step 26 (.close 39)))))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.split 61 1 (.step 7 (.close 31)) (.step 10 (.step 15 (.step 16 (.step 18 (.step 31 (.close 64)))))))) (.step 9 (.step 15 (.close 31)))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 21 (.step 31 (.step 52 (.close 53))))))))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 31 (.close 52))))))) (.step 31 (.step 7 (.step 26 (.close 37))))) (.step 31 (.close 37))) (.step 15 (.step 21 (.step 29 (.step 31 (.step 37 (.close 3))))))))))) (.run (.step 3 (.step 7 (.split 35 1 (.step 3 (.split 49 1 (.step 7 (.step 18 (.close 64))) (.step 7 (.step 18 (.close 52))))) (.step 3 (.close 31))))))) (.run (.step 7 (.step 18 (.step 26 (.step 18 (.split 49 1 (.split 50 1 (.step 18 (.step 31 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64))))) (.step 7 (.step 18 (.close 26)))) (.step 7 (.step 18 (.step 26 (.close 52)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900389093795603707041209141551692095946752⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 68 1 (.split 72 1 (.split 61 1 (.split 62 1 (.step 3 (.step 31 (.step 18 (.step 3 (.step 4 (.step 22 (.step 4 (.step 3 (.close 5))))))))) (.step 10 (.step 21 (.step 32 (.step 65 (.step 31 (.step 3 (.step 5 (.step 22 (.step 4 (.step 3 (.close 5)))))))))))) (.step 10 (.step 12 (.step 34 (.step 64 (.step 68 (.step 65 (.step 3 (.close 18))))))))) (.step 4 (.step 3 (.step 18 (.step 15 (.close 24)))))) (.step 4 (.step 5 (.step 43 (.close 63))))) (.step 3 (.step 4 (.close 18)))) (.step 4 (.step 9 (.step 18 (.close 57))))) (.step 3 (.step 4 (.step 18 (.step 34 (.close 53)))))) (.step 3 (.step 4 (.step 18 (.step 34 (.close 52)))))) (.step 4 (.step 9 (.step 18 (.step 31 (.close 38))))))))))) (.run (.step 7 (.step 18 (.step 22 (.split 22 1 (.step 22 (.step 18 (.split 49 1 (.split 50 1 (.step 18 (.step 31 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64))))) (.step 7 (.step 18 (.close 22)))) (.step 7 (.step 18 (.step 22 (.close 52))))))) (.step 7 (.close 18)))))))) (.run (.step 7 (.step 18 (.step 21 (.split 17 1 (.split 22 1 (.step 21 (.step 18 (.split 49 1 (.split 50 1 (.step 18 (.step 31 (.split 61 1 (.step 7 (.close 18)) (.step 18 (.close 64))))) (.step 7 (.step 18 (.close 21)))) (.step 7 (.step 18 (.step 21 (.close 52))))))) (.step 7 (.close 18))) (.step 7 (.close 18))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300293333025139867219800754697913599925345900391752254130578073411407968806063046656⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 9 (.step 31 (.split 21 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.step 21 (.step 22 (.step 26 (.split 59 1 (.step 31 (.step 71 (.split 61 1 (.split 62 1 (.split 72 1 (.step 3 (.split 69 1 (.step 15 (.step 3 (.close 4))) (.step 3 (.step 4 (.close 15))))) (.step 9 (.step 15 (.step 3 (.step 26 (.step 3 (.close 15))))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 31 (.step 57 (.step 64 (.close 65))))))))) (.step 3 (.step 15 (.step 21 (.step 34 (.close 64)))))))) (.step 3 (.step 9 (.step 15 (.step 3 (.close 4)))))))))) (.step 9 (.step 15 (.step 3 (.step 21 (.step 15 (.step 3 (.step 4 (.close 15))))))))) (.step 3 (.step 9 (.step 15 (.step 21 (.step 15 (.step 3 (.step 4 (.step 18 (.step 22 (.step 26 (.step 12 (.step 4 (.close 53)))))))))))))) (.step 3 (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 22 (.step 26 (.step 34 (.step 3 (.step 26 (.close 52))))))))))))) (.step 9 (.step 15 (.step 21 (.step 15 (.step 3 (.step 18 (.step 15 (.step 31 (.step 26 (.step 3 (.step 4 (.step 32 (.close 38)))))))))))))) (.step 3 (.step 4 (.step 9 (.step 15 (.step 3 (.step 18 (.close 15)))))))))))))) (.run (.step 3 (.step 7 (.step 15 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.step 7 (.step 18 (.close 64)))) (.step 3 (.close 15))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 18 (.close 52))))) (.step 3 (.step 15 (.close 31)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case106
