module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
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
def root : Box := ⟨5368709120, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418417440033855767995208402997145191340242953803137024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 1 (.split 22 1 (.split 35 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 65 1 (.split 67 1 (.split 74 1 (.split 14 0 (.step 31 (.split 72 1 (.split 63 1 (.step 3 (.step 32 (.step 3 (.close 67)))) (.step 66 (.step 3 (.close 32)))) (.split 16 0 (.step 29 (.step 69 (.split 63 1 (.step 31 (.step 3 (.close 32))) (.step 66 (.close 3))))) (.step 31 (.step 18 (.close 67)))))) (.step 12 (.step 3 (.split 72 1 (.split 34 0 (.split 36 0 (.split 42 0 (.step 12 (.step 18 (.close 3))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.close 74))) (.step 3 (.step 12 (.step 18 (.close 31))))) (.step 12 (.step 67 (.step 3 (.close 75)))))))) (.step 18 (.step 69 (.split 63 1 (.split 34 0 (.step 11 (.step 69 (.split 64 1 (.step 18 (.step 3 (.close 12))) (.step 32 (.step 18 (.close 67)))))) (.step 18 (.step 17 (.step 31 (.close 32))))) (.step 66 (.close 3)))))) (.step 3 (.close 69))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 18 (.step 3 (.close 31)))))))) (.step 3 (.close 51))) (.step 3 (.close 47))) (.step 31 (.step 12 (.close 66)))) (.step 31 (.close 74))) (.step 31 (.close 66))) (.step 9 (.step 31 (.step 32 (.split 51 1 (.step 75 (.step 3 (.step 29 (.step 66 (.split 65 1 (.split 16 0 (.split 17 0 (.split 51 0 (.step 31 (.step 40 (.step 31 (.close 12)))) (.step 3 (.close 38))) (.step 18 (.close 74))) (.step 18 (.close 38))) (.step 3 (.close 31))))))) (.step 3 (.close 22))))))) (.step 18 (.step 32 (.close 66)))) (.step 18 (.step 32 (.close 66)))))
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
def root : Box := ⟨5368709120, 28917930526206221005081133799274836344768776455518557762013313250775265201909047731072490110442591841138702963335062871239996708693955086968726403501670347796023831681829366086470985381846917257618668366578714774953999204352⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 75 (.step 77 (.split 65 2 (.split 74 2 (.split 14 1 (.split 72 2 (.split 16 1 (.reuse 0) (.run (.step 18 (.step 38 (.close 66))))) (.run (.step 31 (.split 16 1 (.step 29 (.split 17 1 (.split 51 1 (.step 75 (.step 66 (.step 67 (.step 3 (.close 18))))) (.step 3 (.close 51))) (.step 18 (.step 66 (.step 32 (.close 74)))))) (.step 18 (.step 38 (.step 66 (.close 67)))))))) (.run (.step 12 (.step 18 (.step 75 (.split 34 1 (.step 27 (.split 36 1 (.split 42 1 (.split 51 1 (.step 77 (.step 3 (.split 72 1 (.step 11 (.step 67 (.split 35 1 (.step 18 (.step 3 (.close 31))) (.step 23 (.step 32 (.step 17 (.close 31))))))) (.step 38 (.step 40 (.step 67 (.step 69 (.step 17 (.step 74 (.close 17)))))))))) (.step 3 (.close 17))) (.step 31 (.close 17))) (.step 31 (.close 17)))) (.step 31 (.close 17)))))))) (.run (.step 18 (.step 77 (.split 34 1 (.step 11 (.split 36 1 (.split 51 1 (.step 77 (.step 66 (.step 67 (.step 3 (.step 69 (.step 31 (.step 23 (.step 31 (.close 32))))))))) (.step 3 (.close 51))) (.step 31 (.step 66 (.step 12 (.close 74)))))) (.step 31 (.step 17 (.step 66 (.close 67))))))))) (.run (.step 18 (.step 31 (.split 72 2 (.split 74 2 (.step 68 (.step 74 (.split 14 1 (.step 68 (.step 66 (.step 67 (.step 3 (.step 31 (.close 21)))))) (.step 3 (.step 12 (.close 17)))))) (.step 3 (.step 17 (.step 66 (.step 67 (.step 68 (.step 74 (.close 77)))))))) (.step 3 (.step 38 (.step 66 (.step 67 (.step 68 (.step 74 (.close 75)))))))))))))))
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
def root : Box := ⟨5368709120, 28917930542365358494637737213532857953354645241770179763910642796200904719788330918630281592257553049117797149335903075922063562039424033593615846987257051308640116876333452906746962114499472215832460298780756543160604164096⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 35 2 (.split 63 2 (.split 64 2 (.split 71 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 68 (.step 69 (.step 74 (.close 3)))))))))) (.run (.step 47 (.step 51 (.step 68 (.step 69 (.step 67 (.close 31)))))))) (.run (.step 47 (.step 51 (.step 68 (.step 69 (.step 66 (.close 18)))))))) (.run (.step 3 (.step 31 (.step 32 (.step 66 (.step 74 (.step 77 (.split 65 2 (.split 16 1 (.step 29 (.step 38 (.split 17 1 (.split 22 1 (.split 51 1 (.split 67 1 (.split 74 2 (.split 14 1 (.step 38 (.step 66 (.step 3 (.step 23 (.step 12 (.close 18)))))) (.step 12 (.step 40 (.step 38 (.step 69 (.step 38 (.close 17))))))) (.step 17 (.step 23 (.step 66 (.step 69 (.step 74 (.split 17 0 (.step 38 (.close 12)) (.step 3 (.close 77))))))))) (.step 3 (.close 38))) (.step 3 (.close 22))) (.step 18 (.close 38))) (.step 18 (.close 38))))) (.step 18 (.close 38))) (.step 3 (.step 38 (.step 66 (.close 68)))))))))))))
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
def root : Box := ⟨5368709120, 28917930542365358494637737218204797145799773145658739488147741112891570711210856287543374730586413528024730957976221450300976096218340626469688507872958563272837969214628406808886067553018961257895851065723386260841880879104⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.step 18 (.step 31 (.step 68 (.split 14 2 (.reuse 0) (.run (.step 3 (.step 12 (.step 67 (.step 74 (.step 75 (.split 65 2 (.split 34 1 (.step 11 (.step 17 (.split 35 2 (.split 36 1 (.split 42 1 (.split 67 1 (.split 72 2 (.split 64 1 (.split 71 1 (.split 30 0 (.split 35 1 (.step 17 (.step 3 (.close 31))) (.step 23 (.step 32 (.step 17 (.close 31))))) (.step 3 (.close 17))) (.step 17 (.close 74))) (.step 17 (.close 67))) (.step 23 (.step 38 (.step 74 (.split 16 0 (.step 75 (.close 17)) (.step 3 (.close 17))))))) (.step 3 (.close 17))) (.step 31 (.close 17))) (.step 31 (.close 17))) (.step 23 (.step 32 (.step 38 (.step 74 (.split 17 0 (.step 38 (.close 17)) (.step 3 (.close 17)))))))))) (.step 17 (.close 31))) (.step 3 (.step 17 (.step 67 (.close 68)))))))))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case170
