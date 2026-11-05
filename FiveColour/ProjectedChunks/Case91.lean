module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
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
def root : Box := ⟨3221225472, 16546956804726563904923843341139066471917450703590643481916547003262398523556366458061486247376973585694220665753077346810510196044764395374680300047652804367205684093821766792856900804647484892050360930517672056061952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 62 1 (.split 67 1 (.split 69 1 (.split 72 1 (.step 71 (.split 21 0 (.split 26 0 (.step 3 (.close 7)) (.step 3 (.step 12 (.step 3 (.close 15))))) (.step 3 (.step 18 (.close 4))))) (.step 3 (.step 29 (.step 26 (.step 31 (.step 18 (.step 4 (.close 3)))))))) (.step 71 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 72 (.step 3 (.close 4))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 4 (.step 15 (.close 21))))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 4 (.step 26 (.step 29 (.step 15 (.close 21))))))))) (.step 3 (.step 7 (.close 70)))) (.split 67 1 (.split 72 1 (.step 65 (.split 68 1 (.split 10 0 (.split 12 0 (.split 16 0 (.step 72 (.split 17 0 (.split 21 0 (.split 22 0 (.split 26 0 (.step 65 (.close 3)) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 4 (.step 15 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 21 (.step 3 (.step 4 (.step 15 (.step 29 (.step 15 (.close 26)))))))))) (.step 3 (.step 4 (.step 21 (.step 26 (.step 31 (.step 15 (.step 57 (.step 15 (.close 65)))))))))) (.step 3 (.step 65 (.close 7))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613251382624826190013998972285069696513357348517404005177088464802023512939887504928130779557201952911780884309465039118488049213094591479827641379364773298176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 54 1 (.step 71 (.split 59 1 (.split 61 1 (.reuse 0) (.run (.split 62 1 (.split 67 1 (.split 72 1 (.step 64 (.split 68 1 (.split 10 0 (.split 12 0 (.split 16 0 (.step 72 (.split 17 0 (.split 21 0 (.step 64 (.step 3 (.step 4 (.close 7)))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 7 (.step 27 (.close 36))))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 31 (.step 22 (.step 3 (.step 4 (.step 15 (.close 21))))))))) (.step 3 (.step 4 (.step 15 (.step 26 (.step 31 (.step 21 (.step 57 (.step 21 (.close 64)))))))))) (.step 3 (.step 64 (.close 7)))) (.step 64 (.step 71 (.split 21 0 (.split 72 1 (.step 64 (.close 3)) (.step 3 (.step 15 (.step 21 (.step 26 (.step 28 (.step 31 (.close 57)))))))) (.step 3 (.step 4 (.step 18 (.close 4)))))))))) (.run (.step 26 (.split 61 1 (.split 68 1 (.split 62 1 (.step 62 (.step 3 (.step 7 (.step 26 (.step 44 (.close 70)))))) (.step 3 (.step 53 (.step 65 (.step 7 (.step 9 (.step 27 (.close 52)))))))) (.step 3 (.step 4 (.close 12)))) (.step 3 (.step 64 (.step 7 (.step 9 (.step 27 (.close 53))))))))))) (.run (.step 3 (.split 59 1 (.step 71 (.split 61 1 (.split 62 1 (.step 9 (.step 57 (.step 3 (.step 57 (.step 71 (.step 57 (.close 3))))))) (.step 3 (.step 4 (.step 21 (.close 57))))) (.step 3 (.step 57 (.step 21 (.step 36 (.close 64))))))) (.step 3 (.step 9 (.step 26 (.step 57 (.step 3 (.close 4))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651413817704218235797227771522456084766466287663467482895832071170250897607914377075184102826171570258872160387999074583111153613799424⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 3 (.step 54 (.step 22 (.step 36 (.step 54 (.close 64)))))))) (.run (.step 53 (.step 57 (.step 71 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 72 1 (.split 68 1 (.split 69 1 (.split 16 0 (.split 54 1 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.step 21 (.step 3 (.step 18 (.step 15 (.close 26))))))) (.step 18 (.step 3 (.step 21 (.close 27))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 4 (.step 12 (.close 21))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 55 (.step 3 (.step 29 (.step 3 (.step 12 (.close 15))))))))))) (.step 3 (.step 53 (.step 7 (.step 9 (.step 27 (.close 52))))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 64 (.step 7 (.step 9 (.step 27 (.close 53))))))) (.step 3 (.step 53 (.close 54))))))))) (.run (.step 52 (.step 57 (.step 71 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 72 1 (.split 68 1 (.split 69 1 (.split 16 0 (.split 54 1 (.step 52 (.step 3 (.close 4))) (.step 9 (.step 57 (.close 3)))) (.step 18 (.step 3 (.step 21 (.close 27))))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.step 4 (.step 12 (.close 21))))) (.step 3 (.step 9 (.step 26 (.step 55 (.step 57 (.step 52 (.close 3)))))))) (.step 3 (.step 52 (.step 7 (.step 9 (.step 27 (.close 53))))))) (.step 3 (.step 53 (.step 64 (.step 65 (.step 4 (.step 7 (.step 9 (.close 27))))))))) (.step 3 (.step 52 (.close 64)))) (.step 3 (.step 52 (.close 54)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666586737117980117614092232741652389142213285533438533796349848518125686441569825185426240175003820227559424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 21 (.step 57 (.step 71 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 61 1 (.split 69 1 (.step 75 (.step 3 (.split 54 1 (.split 68 1 (.split 72 1 (.step 3 (.step 29 (.step 18 (.step 21 (.step 3 (.step 4 (.close 15))))))) (.step 29 (.step 3 (.step 26 (.step 31 (.step 21 (.step 3 (.close 4)))))))) (.step 4 (.step 3 (.step 29 (.step 21 (.step 3 (.step 15 (.close 26)))))))) (.step 9 (.step 21 (.step 29 (.step 38 (.step 3 (.step 18 (.step 31 (.close 3))))))))))) (.step 3 (.step 4 (.step 21 (.step 29 (.step 31 (.step 15 (.close 38)))))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 29 (.step 31 (.step 38 (.step 57 (.step 64 (.close 71))))))))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 29 (.step 3 (.step 18 (.step 31 (.step 3 (.close 12))))))))))) (.step 3 (.step 9 (.step 21 (.step 38 (.step 52 (.step 57 (.step 62 (.step 29 (.step 40 (.step 71 (.step 52 (.step 26 (.step 3 (.close 15))))))))))))))) (.step 3 (.step 31 (.step 3 (.step 26 (.step 29 (.step 3 (.close 38)))))))) (.step 3 (.step 31 (.step 29 (.step 3 (.step 26 (.close 38)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300295185698567660905643189325198356435828200115297593084216079601456663775808585728⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 3 (.step 46 (.step 52 (.step 53 (.step 62 (.step 46 (.step 10 (.step 30 (.step 46 (.close 64)))))))))))) (.run (.step 7 (.step 31 (.step 75 (.split 49 1 (.split 50 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 29 (.step 31 (.close 53)))))))) (.step 9 (.step 18 (.step 26 (.step 31 (.close 52))))))))))) (.run (.step 7 (.step 31 (.step 57 (.step 75 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 18 (.step 21 (.step 29 (.step 31 (.close 53))))))) (.step 9 (.step 18 (.step 31 (.close 52))))) (.step 31 (.step 7 (.step 26 (.close 29))))))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.step 38 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 29 (.step 31 (.close 52)))))))) (.step 9 (.step 15 (.step 18 (.step 31 (.close 52)))))) (.step 31 (.step 7 (.step 26 (.step 29 (.step 3 (.close 37))))))) (.step 31 (.close 37))))))))) (.run (.step 3 (.step 7 (.step 31 (.split 35 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.step 29 (.close 31)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300298891045423258393890076990548608782256390632260727786908395061716477133908344832⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 57 (.step 71 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 29 (.step 3 (.step 71 (.step 29 (.split 54 1 (.step 3 (.step 29 (.close 3))) (.step 9 (.step 29 (.close 3)))))))) (.step 3 (.step 4 (.step 21 (.step 28 (.step 29 (.step 15 (.step 57 (.close 65))))))))) (.step 3 (.step 31 (.step 29 (.step 21 (.step 57 (.step 64 (.step 15 (.close 29))))))))) (.step 3 (.step 9 (.step 26 (.step 27 (.step 29 (.step 57 (.step 62 (.close 3))))))))) (.step 3 (.step 9 (.step 21 (.step 27 (.step 29 (.step 53 (.step 57 (.split 34 0 (.step 53 (.close 3)) (.step 3 (.step 15 (.step 26 (.close 29))))))))))))) (.step 3 (.step 9 (.step 27 (.step 29 (.step 52 (.step 57 (.split 10 0 (.split 26 2 (.step 52 (.close 3)) (.step 29 (.close 3))) (.step 3 (.step 15 (.close 21))))))))))) (.step 3 (.step 28 (.close 29)))) (.step 3 (.step 28 (.close 29)))) (.step 21 (.step 29 (.step 3 (.step 29 (.step 3 (.step 4 (.step 15 (.step 21 (.step 28 (.close 29))))))))))) (.step 3 (.step 15 (.step 28 (.close 29))))))))))) (.run (.step 7 (.step 18 (.step 26 (.step 18 (.close 7)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300298891045423258397181086105194016944922857348357746350780935173173931522318663680⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 71 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 72 1 (.split 68 1 (.split 54 1 (.split 61 1 (.step 31 (.split 62 1 (.step 3 (.step 18 (.step 3 (.close 4)))) (.step 5 (.step 10 (.step 21 (.step 4 (.step 22 (.step 4 (.step 3 (.close 5)))))))))) (.step 10 (.step 12 (.step 30 (.step 34 (.step 64 (.step 31 (.step 5 (.step 18 (.step 21 (.step 22 (.step 3 (.step 4 (.close 5)))))))))))))) (.step 4 (.step 3 (.step 18 (.step 15 (.close 24)))))) (.step 4 (.step 5 (.step 43 (.close 63))))) (.step 4 (.step 9 (.step 18 (.step 15 (.step 26 (.step 15 (.step 29 (.step 15 (.close 24)))))))))) (.step 3 (.step 4 (.step 18 (.close 34))))) (.step 3 (.step 4 (.step 18 (.step 34 (.close 53)))))) (.step 3 (.step 4 (.step 18 (.step 34 (.close 52)))))) (.step 4 (.step 9 (.step 18 (.step 29 (.step 31 (.close 38))))))) (.step 4 (.step 9 (.step 18 (.close 29))))))))))) (.run (.step 7 (.step 18 (.step 22 (.split 22 1 (.step 22 (.step 18 (.close 7))) (.step 7 (.close 18)))))))) (.run (.step 7 (.step 18 (.step 21 (.split 17 1 (.step 21 (.split 22 1 (.step 21 (.step 18 (.close 7))) (.step 7 (.close 18)))) (.step 7 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 16546956804731580361433956459794509568944475573414723977243613258093081965718135879651419368458976973756663455666591216607464477296585300298891045423258397181086105194016944922857351016204877651967375440348636285763584⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 9 (.step 15 (.step 21 (.step 22 (.step 26 (.step 31 (.split 21 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.step 71 (.split 61 1 (.step 57 (.step 3 (.split 62 1 (.step 9 (.split 69 1 (.step 15 (.step 3 (.step 15 (.step 18 (.step 15 (.step 3 (.close 4))))))) (.step 3 (.step 4 (.close 15))))) (.step 3 (.step 4 (.close 15)))))) (.step 3 (.step 15 (.step 21 (.step 34 (.close 64)))))))) (.step 3 (.step 9 (.step 15 (.step 3 (.close 4)))))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 4 (.step 12 (.close 17)))))))) (.step 3 (.step 9 (.step 12 (.step 15 (.step 3 (.step 21 (.step 3 (.step 26 (.step 3 (.step 34 (.close 52)))))))))))) (.step 9 (.step 15 (.step 3 (.step 21 (.step 15 (.step 29 (.step 31 (.step 4 (.step 26 (.step 3 (.step 32 (.close 38))))))))))))) (.step 9 (.step 15 (.step 29 (.close 3))))) (.step 3 (.step 4 (.step 9 (.step 15 (.close 3)))))))))))))))) (.run (.step 3 (.step 7 (.step 15 (.step 31 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 15))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 15 (.close 29)))) (.step 3 (.step 15 (.close 29))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case91
