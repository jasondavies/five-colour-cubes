module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case138
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342787806629724160⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11593776385211095628519, 5789234131004114112605793609176917365993675384684502996126192153037828881438993460943296163574515770240361043816409628266588608613860165826510106852596731451962902910272861366847979792412103177558715516249647994149244240896, 0⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993925877836143429696690957731067867747567084912312220080475601571065221129460089588115160067528359303968881752396194990036479624244398066193259855148636854547106156691263255685525430101826315747328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 8 0 (.split 16 0 (.split 17 0 (.split 74 1 (.step 7 (.step 3 (.close 29))) (.step 3 (.split 4 0 (.step 11 (.step 69 (.step 3 (.step 7 (.close 17))))) (.step 3 (.close 7))))) (.step 7 (.step 3 (.close 19)))) (.step 7 (.step 3 (.split 17 0 (.step 7 (.step 3 (.close 19))) (.step 7 (.close 19)))))) (.split 16 0 (.split 74 1 (.step 3 (.split 17 0 (.split 34 0 (.split 4 0 (.step 3 (.step 7 (.close 11))) (.step 3 (.close 7))) (.split 36 0 (.step 7 (.step 3 (.close 11))) (.step 7 (.step 11 (.close 29))))) (.step 7 (.step 3 (.close 11))))) (.step 11 (.close 7))) (.step 11 (.step 3 (.split 17 0 (.step 7 (.step 3 (.close 11))) (.step 7 (.close 11))))))) (.split 74 1 (.split 4 0 (.step 29 (.step 3 (.step 75 (.close 3)))) (.step 3 (.split 8 0 (.step 3 (.step 7 (.close 29))) (.step 3 (.close 11))))) (.step 11 (.step 23 (.step 29 (.step 3 (.close 69))))))) (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 3 (.close 29)) (.step 3 (.close 74))) (.step 74 (.close 3))) (.step 11 (.step 69 (.step 3 (.close 74))))) (.step 29 (.step 69 (.step 3 (.close 74)))))) (.step 3 (.step 7 (.close 3)))) (.step 3 (.step 74 (.split 34 0 (.split 16 0 (.step 3 (.step 74 (.close 3))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 15 (.close 29))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334835886793856427426709802302643992082965358552532362368993382342746809133121826109575667830136054917344259328025643471566616395776⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 67 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 3 (.close 29)) (.step 3 (.close 67))) (.step 67 (.close 3))) (.step 11 (.step 67 (.close 3)))) (.step 29 (.step 67 (.close 3)))) (.step 3 (.close 67))))))) (.run (.step 66 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 3 (.close 29)) (.step 3 (.close 66))) (.step 66 (.close 3))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.close 3)))) (.step 3 (.close 66))))))) (.run (.step 3 (.step 55 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.close 51))))))) (.run (.step 3 (.step 55 (.split 51 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 7 (.close 3))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710573401894947946761161419113437331819700014167130599594458760628482735945262563328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 42 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 7 (.step 29 (.step 7 (.step 15 (.close 37))))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 37 (.step 11 (.close 39)))))))) (.step 3 (.step 23 (.step 11 (.step 7 (.step 29 (.step 17 (.step 37 (.close 39))))))))) (.step 29 (.step 74 (.step 75 (.step 3 (.close 7)))))) (.step 3 (.step 29 (.step 15 (.close 39))))) (.step 29 (.step 67 (.step 74 (.step 75 (.step 3 (.step 37 (.step 3 (.close 15))))))))) (.step 29 (.step 66 (.close 3)))) (.step 39 (.split 65 1 (.split 74 1 (.split 71 1 (.split 63 1 (.step 39 (.step 29 (.split 4 0 (.split 10 0 (.step 74 (.step 45 (.close 3))) (.step 3 (.step 7 (.step 37 (.close 39))))) (.step 3 (.step 7 (.step 37 (.close 39))))))) (.step 29 (.step 37 (.step 39 (.step 51 (.step 45 (.step 3 (.step 39 (.close 66))))))))) (.step 29 (.step 39 (.step 11 (.step 37 (.step 66 (.close 67))))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 45 (.step 37 (.step 66 (.step 37 (.close 67)))))))))) (.step 3 (.step 29 (.close 39))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460183827084136443896789531468703981888743326150587394561069408539401090006688079266830647035846070949117952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 4 0 (.step 29 (.step 3 (.split 8 0 (.step 7 (.step 19 (.close 37))) (.step 3 (.step 11 (.step 3 (.close 37))))))) (.step 3 (.split 8 0 (.step 3 (.step 7 (.close 29))) (.step 3 (.close 11))))) (.step 11 (.step 23 (.step 29 (.step 3 (.step 38 (.step 3 (.close 19)))))))) (.step 29 (.close 38))) (.step 29 (.step 38 (.step 74 (.close 3))))) (.step 3 (.step 40 (.step 9 (.step 7 (.step 3 (.close 29))))))) (.step 3 (.step 29 (.step 15 (.close 38))))) (.step 29 (.step 38 (.step 3 (.step 67 (.close 3)))))) (.step 29 (.step 38 (.step 66 (.close 3))))) (.step 3 (.step 40 (.step 9 (.step 29 (.step 38 (.step 3 (.close 7)))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878621701000088910984550333021447796084629210604308528502053798559259427776027913339342556233728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 7 (.step 29 (.step 7 (.step 15 (.close 37))))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 29 (.step 11 (.close 37)))))) (.step 3 (.step 23 (.step 11 (.step 7 (.step 17 (.step 29 (.close 37)))))))) (.step 29 (.step 75 (.step 3 (.close 7))))) (.step 3 (.step 15 (.step 29 (.close 37))))) (.step 29 (.step 66 (.step 67 (.step 3 (.close 37)))))) (.step 29 (.close 66))) (.step 37 (.split 65 1 (.split 74 1 (.split 63 1 (.split 14 0 (.step 45 (.step 29 (.step 39 (.step 66 (.step 45 (.close 3)))))) (.step 3 (.step 7 (.step 29 (.step 37 (.close 11)))))) (.step 15 (.step 29 (.step 37 (.close 66))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.step 39 (.step 45 (.close 66)))))))))) (.step 3 (.step 15 (.step 29 (.close 37))))))) (.step 37 (.split 65 1 (.split 74 1 (.split 63 1 (.step 39 (.step 29 (.step 74 (.step 37 (.close 3))))) (.step 15 (.step 29 (.step 37 (.close 66))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.step 39 (.close 66))))))))) (.step 3 (.step 15 (.step 29 (.close 37))))))) (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065245470636601467136205462790262072702194438304434699708782157327676676048739631104⟩
def references : Fin 4 → Box := ![Part1.root, Part2.root, Part3.root, Part4.root]
def proof : Chunks.Proof 4 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 7 (.step 29 (.step 7 (.step 15 (.close 37))))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 37 (.step 11 (.close 39)))))))) (.step 3 (.step 23 (.step 11 (.step 7 (.step 29 (.step 17 (.step 37 (.close 39))))))))) (.step 29 (.step 69 (.step 75 (.step 3 (.close 7)))))) (.step 3 (.step 29 (.step 15 (.step 39 (.step 15 (.step 45 (.close 69)))))))) (.step 29 (.step 67 (.step 69 (.split 65 1 (.split 8 0 (.split 4 0 (.step 67 (.close 3)) (.step 3 (.close 37))) (.step 3 (.step 37 (.step 11 (.close 39))))) (.step 3 (.step 15 (.close 39)))))))) (.step 29 (.step 66 (.close 3))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.run (.step 3 (.step 7 (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67))) (.step 3 (.close 66))) (.step 3 (.step 38 (.step 3 (.close 7)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622937198875408533562916267060128315057806582727789510656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 8 0 (.split 16 0 (.split 17 0 (.step 7 (.step 19 (.step 29 (.close 69)))) (.split 26 0 (.step 7 (.step 11 (.close 20))) (.step 3 (.step 7 (.step 19 (.step 20 (.close 19))))))) (.split 71 1 (.split 26 0 (.step 7 (.step 11 (.step 19 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.close 20))))) (.step 11 (.step 67 (.step 20 (.step 3 (.step 19 (.close 25)))))))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 7 (.step 19 (.close 69)))))))) (.step 3 (.step 11 (.step 19 (.step 20 (.step 19 (.step 25 (.close 69)))))))) (.step 11 (.step 67 (.close 3)))) (.step 11 (.step 66 (.step 69 (.split 65 1 (.split 26 0 (.split 4 0 (.step 66 (.close 3)) (.step 3 (.close 19))) (.step 3 (.step 19 (.close 20)))) (.step 3 (.step 19 (.close 20)))))))) (.step 3 (.step 66 (.step 67 (.step 69 (.step 40 (.step 29 (.step 11 (.step 38 (.step 7 (.step 19 (.close 20)))))))))))) (.step 3 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 67 (.step 20 (.step 19 (.close 69)))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397854115110619787389832519688183215467338191998800103240901699334777371649459497115392589330916867360103971340889514378725827946737335343812596719323497870574308376092473135003162641278949117260739827990528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 8 0 (.split 16 0 (.split 22 0 (.step 7 (.step 19 (.step 29 (.close 69)))) (.split 26 0 (.step 7 (.step 11 (.close 20))) (.step 3 (.step 7 (.step 19 (.step 20 (.close 19))))))) (.split 71 1 (.split 26 0 (.step 7 (.step 11 (.step 19 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.close 20))))) (.step 11 (.step 20 (.step 61 (.step 51 (.step 67 (.step 3 (.step 19 (.close 20)))))))))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 7 (.step 19 (.close 69)))))))) (.step 3 (.step 11 (.step 19 (.close 20))))) (.step 11 (.step 67 (.close 3)))) (.step 11 (.step 66 (.step 74 (.step 77 (.step 3 (.step 19 (.step 3 (.close 19))))))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 7 (.step 11 (.step 19 (.step 25 (.close 29)))))))))) (.step 3 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 20 (.step 67 (.step 20 (.close 74))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938695453085160407504507633397016531618710402713518080⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.step 7 (.split 22 1 (.reuse 0) (.run (.step 25 (.split 26 1 (.split 35 1 (.split 65 1 (.split 72 1 (.split 71 1 (.split 64 1 (.step 20 (.step 11 (.split 4 0 (.split 10 0 (.step 74 (.step 25 (.close 3))) (.step 3 (.step 7 (.step 17 (.close 19))))) (.step 3 (.step 7 (.step 19 (.close 20))))))) (.step 11 (.step 19 (.step 20 (.step 51 (.step 25 (.step 3 (.step 20 (.close 66))))))))) (.step 11 (.step 20 (.step 19 (.step 29 (.step 19 (.step 66 (.close 67)))))))) (.step 3 (.step 7 (.step 11 (.step 25 (.step 29 (.step 19 (.step 66 (.step 19 (.close 67)))))))))) (.step 3 (.step 11 (.close 20)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 20 (.step 25 (.step 38 (.close 66)))))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 20 (.step 19 (.step 66 (.step 20 (.close 67))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519688183215467338191998800103240901699334777371649459497115392589330916867360103971340889514378725827946737335343814281715990194784066358889545898176597895378936600373932789812166656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 8 0 (.split 17 0 (.split 22 0 (.step 7 (.step 19 (.step 29 (.close 67)))) (.split 26 0 (.step 7 (.step 11 (.step 19 (.close 3)))) (.step 3 (.step 7 (.step 19 (.close 25)))))) (.split 71 1 (.step 19 (.step 7 (.close 19))) (.step 11 (.step 20 (.step 61 (.step 51 (.step 19 (.close 3)))))))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 11 (.step 23 (.step 29 (.step 7 (.step 19 (.step 20 (.step 25 (.step 38 (.close 67))))))))))) (.step 3 (.step 11 (.close 19)))) (.step 11 (.close 67))) (.step 11 (.step 66 (.step 67 (.step 66 (.step 3 (.close 19))))))) (.step 3 (.step 38 (.step 11 (.step 23 (.step 29 (.step 38 (.step 3 (.step 19 (.close 66)))))))))) (.step 3 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 19 (.step 67 (.step 19 (.step 20 (.close 69)))))))))))))) (.step 19 (.split 26 1 (.split 35 1 (.split 65 1 (.split 72 1 (.split 64 1 (.split 34 0 (.step 19 (.step 11 (.step 20 (.step 66 (.step 19 (.close 3)))))) (.step 7 (.step 11 (.step 17 (.close 19))))) (.step 11 (.step 19 (.step 66 (.close 67))))) (.step 3 (.step 7 (.step 11 (.step 25 (.step 29 (.step 19 (.step 38 (.step 66 (.close 67)))))))))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 19 (.step 20 (.step 66 (.step 19 (.close 67)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914586797738407425837081849247901730058646061056⟩
def references : Fin 4 → Box := ![Part5.root, Part6.root, Part8.root, Part9.root]
def proof : Chunks.Proof 4 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 4 0 (.step 29 (.step 3 (.close 11))) (.step 3 (.split 8 0 (.step 3 (.step 7 (.close 29))) (.step 3 (.close 11))))) (.step 11 (.step 23 (.step 29 (.step 3 (.close 19)))))) (.step 29 (.step 11 (.step 3 (.step 19 (.step 20 (.step 67 (.close 69)))))))) (.step 3 (.close 7))) (.step 3 (.step 15 (.close 29)))) (.step 29 (.step 3 (.step 11 (.step 23 (.step 19 (.close 67))))))) (.step 29 (.step 3 (.step 23 (.step 11 (.close 66)))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 9 (.close 7)))) (.step 3 (.step 7 (.step 29 (.step 3 (.close 7))))))))) (.reuse 1)) (.reuse 2)) (.step 7 (.split 17 1 (.reuse 3) (.run (.step 19 (.split 26 1 (.split 35 1 (.split 65 1 (.split 72 1 (.split 64 1 (.step 20 (.step 11 (.step 74 (.step 19 (.close 3))))) (.step 11 (.step 19 (.step 66 (.close 67))))) (.step 3 (.step 7 (.step 11 (.step 25 (.step 29 (.step 19 (.step 20 (.step 38 (.step 66 (.close 67))))))))))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 19 (.step 20 (.step 66 (.close 67))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457892568212888550189389268015682463392224882806916348086866719690508927497378938566051991752269739463802880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 34 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.split 42 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 4 0 (.step 11 (.step 3 (.split 10 0 (.split 16 0 (.split 34 0 (.step 3 (.step 17 (.close 29))) (.step 17 (.step 3 (.close 29)))) (.step 17 (.close 3))) (.step 3 (.close 7))))) (.step 3 (.split 16 0 (.split 10 0 (.step 11 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 11)))))) (.step 11 (.close 17))) (.step 11 (.step 17 (.step 23 (.step 29 (.step 3 (.step 17 (.step 3 (.close 37))))))))) (.step 11 (.step 17 (.step 74 (.close 3))))) (.step 3 (.step 23 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 7 (.step 69 (.step 23 (.step 11 (.step 17 (.step 7 (.step 29 (.step 17 (.step 37 (.close 39)))))))))))) (.step 3 (.step 7 (.step 74 (.step 7 (.step 29 (.step 17 (.step 37 (.step 11 (.step 17 (.close 39))))))))))) (.step 11 (.step 17 (.step 3 (.step 67 (.close 3)))))) (.step 11 (.step 17 (.step 66 (.close 3))))) (.step 3 (.step 7 (.step 23 (.step 11 (.step 17 (.step 3 (.close 7)))))))) (.step 3 (.step 7 (.step 17 (.step 29 (.step 40 (.step 66 (.step 67 (.step 7 (.step 37 (.step 11 (.step 17 (.close 37))))))))))))) (.step 3 (.step 7 (.step 11 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2417851639229260496896000, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342786707118096384⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 11 (.split 10 1 (.split 26 1 (.split 30 1 (.split 35 1 (.split 43 1 (.split 34 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 42 1 (.split 4 0 (.step 11 (.step 3 (.close 29))) (.step 3 (.split 26 0 (.step 3 (.step 7 (.close 11))) (.step 3 (.close 11))))) (.step 3 (.step 7 (.step 11 (.step 29 (.close 37)))))) (.step 9 (.step 29 (.step 11 (.step 3 (.step 37 (.close 39))))))) (.step 11 (.step 9 (.step 29 (.step 37 (.step 66 (.close 69))))))) (.step 3 (.close 7))) (.step 3 (.close 11))) (.step 3 (.step 7 (.step 29 (.step 40 (.step 74 (.step 7 (.step 11 (.step 45 (.step 11 (.close 37))))))))))) (.step 11 (.step 3 (.step 9 (.step 29 (.close 67)))))) (.step 11 (.step 3 (.step 9 (.step 29 (.close 66)))))) (.step 3 (.step 7 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 29 (.step 40 (.step 66 (.step 67 (.step 7 (.step 37 (.step 11 (.step 37 (.step 39 (.close 69))))))))))))) (.step 3 (.step 7 (.step 11 (.close 7))))) (.step 3 (.step 9 (.step 29 (.step 38 (.step 11 (.step 38 (.step 11 (.step 38 (.close 66)))))))))) (.step 3 (.step 7 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 9 (.step 29 (.close 11))))) (.step 3 (.step 7 (.step 11 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342786707118096384⟩
def references : Fin 3 → Box := ![Part10.root, Part11.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 8 1 (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 35 1 (.reuse 1) (.run (.step 3 (.step 66 (.step 67 (.step 74 (.step 75 (.split 34 1 (.step 77 (.step 29 (.step 38 (.step 11 (.step 3 (.step 17 (.step 3 (.close 37)))))))) (.step 3 (.step 17 (.step 29 (.step 37 (.close 11))))))))))))) (.run (.step 3 (.step 7 (.step 67 (.split 63 1 (.step 7 (.step 3 (.close 11))) (.step 3 (.step 11 (.close 17))))))))) (.run (.step 3 (.step 29 (.step 11 (.step 17 (.step 23 (.step 29 (.step 17 (.step 29 (.step 17 (.close 66)))))))))))) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17))))))))) (.run (.step 3 (.step 7 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.step 66 (.split 64 1 (.step 7 (.step 3 (.close 29))) (.step 3 (.step 29 (.close 38))))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 17 (.step 3 (.close 7))))))))) (.reuse 2))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342787806629724160⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.reuse 0) (.run (.step 3 (.step 7 (.split 8 1 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67))) (.step 3 (.close 66))) (.step 3 (.split 63 1 (.split 64 1 (.step 7 (.step 3 (.close 29))) (.step 3 (.step 29 (.close 38)))) (.step 3 (.step 29 (.close 38)))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.split 63 1 (.split 64 1 (.step 7 (.step 3 (.close 11))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 11 (.close 17)))))) (.step 3 (.step 11 (.step 3 (.close 7)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part14

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part14.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case138

namespace FiveColour.Packed.EnumerationChunks.Projected.Case138
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 25 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 25 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 25 0).upper i := by decide +kernel
lemma budget_model : (⟨11593776385211095628519, 5789234131004114112605793609176917365993675384684502996126192153037828881438993460943296163574515770240361043816409628266588608613860165826510106852596731451962902910272861366847979792412103177558715516249647994149244240896, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 25), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11593776385211095628519, 5789234131004114112605793609176917365993675384684502996126192153037828881438993460943296163574515770240361043816409628266588608613860165826510106852596731451962902910272861366847979792412103177558715516249647994149244240896, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 25) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 25 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 25 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 25) (Archive.root 25) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 25 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 25 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case138

namespace FiveColour.Packed.EnumerationChunks.Case138
def root : Box := Archive.root 25
def families : Fin 78 → List Cut := Enumeration.families 25
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case138.original_covered points
end FiveColour.Packed.EnumerationChunks.Case138
