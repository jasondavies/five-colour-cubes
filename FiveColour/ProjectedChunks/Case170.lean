module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case170
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨5368709120, 28917930542365358494637737218204797145799773145658739488147741112891570711210856287543374730586413528024730957976221450300976096218340626469688507872958563272837969214628406808886067553018961257895851065723386260841880879104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩]
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
def root : Box := ⟨5368709120, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284971109347745694313146532734090116698280412912841535700268021370235308089072897482618974202910926963109577883648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 65 1 (.split 67 1 (.split 74 1 (.split 10 1 (.split 14 0 (.step 31 (.split 72 1 (.split 63 1 (.step 3 (.step 32 (.step 3 (.step 12 (.step 66 (.step 3 (.step 11 (.close 18)))))))) (.step 12 (.step 66 (.step 3 (.step 21 (.step 18 (.close 31))))))) (.split 16 0 (.step 29 (.step 69 (.split 63 1 (.step 31 (.step 3 (.step 21 (.close 32)))) (.step 12 (.step 66 (.close 3)))))) (.step 31 (.step 18 (.step 32 (.step 18 (.close 66)))))))) (.step 12 (.step 3 (.split 72 1 (.split 34 0 (.split 36 0 (.split 42 0 (.step 12 (.step 3 (.step 11 (.step 18 (.close 3))))) (.step 3 (.step 12 (.step 3 (.close 18))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 31)))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 31)))))) (.step 12 (.step 29 (.step 40 (.step 67 (.step 3 (.step 18 (.close 31))))))))))) (.step 3 (.close 12))) (.step 12 (.step 18 (.step 69 (.split 63 1 (.split 34 0 (.step 11 (.step 69 (.split 64 1 (.step 3 (.step 18 (.step 3 (.close 12)))) (.step 32 (.step 18 (.step 3 (.close 12))))))) (.step 18 (.step 17 (.step 31 (.close 32))))) (.step 11 (.step 12 (.step 66 (.close 3))))))))) (.step 3 (.step 12 (.step 32 (.step 3 (.close 66)))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 18 (.step 3 (.step 15 (.close 21))))))))) (.step 3 (.step 12 (.step 22 (.close 36))))) (.step 3 (.step 9 (.step 11 (.close 9))))) (.step 3 (.step 31 (.step 12 (.close 66))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨5368709120, 11567183248250669601833611451386859594097058754810835277167420025121520891212690084408903120654842482096280259854760562857928462172752120373529882784186175573895303597648650773261381479942931301229837148834808726807119921152⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 72 2 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 3 (.step 31 (.step 12 (.close 66)))))) (.run (.step 3 (.step 31 (.step 12 (.close 66)))))) (.run (.step 9 (.step 12 (.step 31 (.step 32 (.split 51 1 (.step 75 (.step 3 (.step 29 (.step 66 (.split 65 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 51 0 (.step 31 (.step 40 (.step 31 (.close 12)))) (.step 3 (.step 12 (.step 3 (.close 15))))) (.step 3 (.step 12 (.step 3 (.close 31))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 31)))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 31)))))) (.step 3 (.step 15 (.close 26)))))))) (.step 3 (.close 22))))))))) (.run (.step 3 (.step 18 (.step 32 (.step 38 (.step 32 (.close 66)))))))) (.run (.step 3 (.step 18 (.step 32 (.step 38 (.step 32 (.close 66)))))))) (.run (.step 3 (.step 18 (.step 32 (.step 38 (.close 66))))))) (.run (.step 9 (.step 12 (.step 31 (.step 69 (.step 75 (.split 16 1 (.step 29 (.split 17 1 (.split 22 1 (.split 51 1 (.step 75 (.step 66 (.step 67 (.step 3 (.step 12 (.close 18)))))) (.step 3 (.step 22 (.step 21 (.close 51))))) (.step 3 (.step 18 (.step 66 (.step 32 (.step 67 (.step 32 (.close 74)))))))) (.step 3 (.step 18 (.step 66 (.step 32 (.step 67 (.step 32 (.close 74))))))))) (.step 3 (.step 18 (.step 38 (.step 66 (.close 67)))))))))))))
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
def root : Box := ⟨5368709120, 23134344423119528469337161269057015322384204377754896818270634333935114820372159140023362701051304549689077916935731812841921486135390009695008244234628706825835844388361856003126883842669619858950293639242507003707764244480⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 74 2 (.split 14 1 (.reuse 0) (.run (.step 12 (.step 18 (.step 75 (.split 34 1 (.step 27 (.split 36 1 (.split 42 1 (.split 51 1 (.step 77 (.step 3 (.split 65 1 (.split 72 1 (.step 11 (.step 67 (.split 34 0 (.split 35 1 (.step 3 (.step 18 (.step 3 (.close 31)))) (.step 23 (.step 17 (.step 32 (.step 17 (.step 3 (.close 31))))))) (.step 3 (.step 17 (.close 31)))))) (.step 29 (.step 38 (.step 40 (.step 67 (.step 69 (.step 17 (.step 74 (.step 3 (.close 17)))))))))) (.step 3 (.close 17))))) (.step 3 (.close 17))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 31 (.close 17))))) (.step 3 (.step 31 (.close 17))))))))) (.run (.step 11 (.step 12 (.step 18 (.step 69 (.step 77 (.split 34 1 (.step 11 (.split 36 1 (.split 42 1 (.split 51 1 (.step 77 (.step 66 (.step 67 (.step 3 (.step 69 (.step 31 (.step 23 (.step 31 (.step 12 (.close 32)))))))))) (.step 3 (.step 36 (.step 12 (.close 51))))) (.step 3 (.step 31 (.step 66 (.step 12 (.step 67 (.step 12 (.close 74)))))))) (.step 3 (.step 31 (.step 66 (.step 12 (.step 67 (.step 12 (.close 74))))))))) (.step 3 (.step 31 (.step 17 (.step 66 (.close 67)))))))))))))
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
def root : Box := ⟨5368709120, 28917930542365358494637737213532857953354645241770179763910642796200904719788330918630281592257553049117797149335903069041567714069209498761153161080996228918945149371490081693980443953730843950378036088725097212783544500224⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 63 2 (.split 64 2 (.split 71 2 (.step 3 (.step 75 (.step 77 (.split 65 2 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.split 72 2 (.split 74 2 (.step 68 (.step 74 (.split 14 1 (.step 68 (.step 66 (.step 67 (.step 3 (.step 31 (.close 21)))))) (.step 3 (.step 12 (.close 17)))))) (.step 3 (.step 17 (.step 18 (.step 66 (.step 67 (.step 68 (.step 12 (.step 74 (.step 12 (.close 77))))))))))) (.step 3 (.step 26 (.step 31 (.step 38 (.step 66 (.step 67 (.step 68 (.step 21 (.step 74 (.step 21 (.close 75)))))))))))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 68 (.step 69 (.step 66 (.step 67 (.step 74 (.close 3)))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 67 (.step 68 (.step 69 (.step 66 (.step 67 (.step 3 (.step 29 (.close 31)))))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 66 (.step 68 (.step 69 (.step 66 (.step 3 (.step 11 (.close 18)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4181389724724491839037947176121573151080448, 28917930542365358494637737213532857953354645241770179763910642796200904719788330918630281592257553049117797149335903075922063562039424033593615846987257051308640116876333452906746966295889196940324299336727932664728386535424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 11 (.step 12 (.step 17 (.step 18 (.step 38 (.step 67 (.step 74 (.step 75 (.step 77 (.split 65 2 (.split 34 1 (.step 11 (.step 17 (.split 35 2 (.split 36 1 (.split 42 1 (.split 51 1 (.split 65 1 (.split 67 1 (.split 72 2 (.split 34 0 (.split 64 1 (.split 71 1 (.split 30 0 (.split 35 1 (.step 17 (.step 3 (.close 31))) (.step 23 (.step 17 (.step 32 (.step 17 (.step 3 (.close 31))))))) (.step 3 (.close 17))) (.step 17 (.step 23 (.step 31 (.step 32 (.step 31 (.close 38))))))) (.step 17 (.step 23 (.step 32 (.step 31 (.close 67)))))) (.step 17 (.close 31))) (.step 23 (.step 38 (.step 67 (.step 69 (.step 74 (.split 16 0 (.step 75 (.close 17)) (.step 3 (.close 17))))))))) (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 23 (.step 31 (.step 32 (.step 38 (.step 74 (.split 16 0 (.split 17 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17)))))))))))) (.step 3 (.step 17 (.close 31)))) (.step 3 (.step 17 (.step 67 (.close 68))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨5368709120, 28917930542365358494637737218204797145799773145658739488147741112891570711210856287543374730586413528024730957976221450300976096218340626469688507872958563272837969214628406808886067553018961257895851065723386260841880879104⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.step 18 (.step 31 (.step 68 (.split 14 2 (.split 35 2 (.reuse 0) (.run (.step 3 (.step 9 (.step 12 (.step 31 (.step 32 (.step 38 (.step 66 (.step 74 (.step 75 (.step 77 (.split 65 2 (.split 16 1 (.step 29 (.step 38 (.split 17 1 (.split 22 1 (.split 51 1 (.split 65 1 (.split 67 1 (.split 74 2 (.split 14 1 (.step 38 (.step 66 (.step 3 (.step 23 (.step 12 (.step 3 (.close 18))))))) (.step 12 (.step 40 (.step 38 (.step 69 (.step 38 (.close 17))))))) (.step 17 (.step 23 (.step 66 (.step 69 (.step 74 (.split 16 0 (.split 17 0 (.step 38 (.close 12)) (.step 3 (.step 74 (.step 12 (.step 38 (.close 77)))))) (.step 3 (.step 18 (.close 38)))))))))) (.step 3 (.close 38))) (.step 3 (.step 31 (.close 38)))) (.step 3 (.close 22))) (.step 3 (.step 17 (.step 18 (.close 38))))) (.step 3 (.step 17 (.step 18 (.close 38))))))) (.step 3 (.step 18 (.close 38)))) (.step 3 (.step 31 (.step 38 (.step 66 (.close 68)))))))))))))))))) (.reuse 1)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case170
