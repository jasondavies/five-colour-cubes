module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case45
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168169420385382274271979204042031104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
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
def root : Box := ⟨2147483648, 11031304536487720240955970973191984381084500630769492679916833617023780404672701586152017245777266494690284288273142738280548349377904898994297227759108898615751692076783260840166542302437209294479013662178102818635776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 21 0 (.split 35 0 (.split 68 0 (.step 7 (.close 9)) (.step 7 (.close 57))) (.step 7 (.step 9 (.close 21)))) (.step 7 (.close 4))) (.step 7 (.close 21))) (.split 16 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 17 0 (.split 30 0 (.step 9 (.step 71 (.close 26))) (.step 7 (.close 53))) (.step 4 (.close 7))) (.step 7 (.step 15 (.step 16 (.close 21))))) (.step 7 (.step 9 (.close 15)))) (.step 18 (.step 15 (.step 5 (.close 7))))) (.step 7 (.step 4 (.close 18))))) (.step 7 (.close 52))) (.step 7 (.split 12 0 (.split 16 0 (.step 9 (.step 26 (.step 40 (.close 71)))) (.step 7 (.close 18))) (.step 9 (.step 18 (.step 15 (.step 26 (.step 7 (.close 53))))))))) (.step 71 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 72 (.close 7)) (.step 7 (.close 36))) (.step 7 (.close 36))) (.split 16 0 (.split 17 0 (.step 4 (.step 10 (.step 57 (.close 71)))) (.step 4 (.close 7))) (.step 4 (.close 7)))) (.step 7 (.close 72))))) (.step 71 (.close 18))) (.step 70 (.step 71 (.split 69 1 (.split 72 1 (.split 10 0 (.split 21 0 (.step 70 (.close 71)) (.step 7 (.close 4))) (.step 7 (.close 15))) (.step 7 (.close 70))) (.step 70 (.close 7)))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482647896611133072268967799598839945926942495661812992169304799749288910841693435377197545194017316078588993256377040868500715816536594928338128563009571929047275929600⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.split 61 1 (.split 62 1 (.reuse 0) (.run (.split 68 1 (.split 72 1 (.split 12 0 (.split 16 0 (.split 67 1 (.split 10 0 (.step 72 (.split 17 0 (.split 36 0 (.step 65 (.close 7)) (.step 7 (.step 10 (.step 4 (.step 7 (.close 57)))))) (.step 7 (.close 54)))) (.step 7 (.close 65))) (.step 65 (.close 70))) (.step 7 (.close 65))) (.step 72 (.split 16 0 (.split 17 0 (.step 64 (.split 67 1 (.step 4 (.step 10 (.step 7 (.close 53)))) (.step 10 (.step 4 (.close 70))))) (.step 4 (.close 7))) (.step 4 (.close 7))))) (.step 4 (.step 70 (.close 71)))) (.step 65 (.close 71))))) (.run (.split 68 1 (.split 72 1 (.split 12 0 (.split 16 0 (.split 17 0 (.step 64 (.split 67 1 (.split 10 0 (.split 21 0 (.step 64 (.step 7 (.close 9))) (.step 4 (.step 7 (.close 9)))) (.step 7 (.close 52))) (.step 64 (.close 70)))) (.step 7 (.step 64 (.close 4)))) (.step 7 (.step 30 (.step 65 (.step 7 (.close 36)))))) (.step 64 (.split 10 0 (.step 4 (.split 16 0 (.step 64 (.close 4)) (.step 4 (.close 7)))) (.step 7 (.close 52))))) (.step 63 (.step 64 (.close 71)))) (.step 63 (.close 64))))) (.run (.split 68 1 (.split 72 1 (.split 16 0 (.split 61 1 (.split 62 1 (.step 62 (.step 70 (.split 69 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 57))) (.step 72 (.close 7))))) (.step 53 (.step 65 (.step 62 (.step 65 (.step 7 (.close 9))))))) (.step 64 (.step 62 (.step 64 (.close 7))))) (.step 18 (.step 7 (.step 27 (.step 44 (.close 62)))))) (.step 18 (.close 26))) (.step 18 (.step 62 (.step 64 (.step 62 (.close 71))))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635115217984954543119347244866627344068045132222223771465839302349596282919139147776⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 34 0 (.split 35 0 (.split 68 0 (.split 17 0 (.split 43 0 (.step 57 (.close 4)) (.step 9 (.close 4))) (.step 7 (.close 4))) (.step 7 (.step 4 (.close 57)))) (.step 9 (.step 21 (.close 57)))) (.step 7 (.close 57))) (.step 18 (.close 57))) (.step 26 (.step 57 (.close 4)))) (.step 4 (.close 57))) (.step 57 (.close 71))) (.step 57 (.step 70 (.step 26 (.step 54 (.step 57 (.step 7 (.step 4 (.close 57))))))))) (.step 4 (.step 21 (.step 57 (.step 10 (.step 57 (.step 65 (.close 7)))))))) (.step 72 (.step 4 (.step 15 (.step 57 (.step 10 (.step 64 (.step 57 (.close 64))))))))) (.step 57 (.close 62))))) (.run (.step 54 (.split 68 1 (.split 72 1 (.split 21 0 (.split 35 0 (.split 59 1 (.step 54 (.step 7 (.close 15))) (.step 54 (.close 4))) (.step 7 (.step 53 (.step 54 (.close 21))))) (.step 7 (.close 54))) (.step 7 (.step 22 (.step 26 (.step 54 (.close 15)))))) (.step 7 (.step 65 (.step 54 (.close 71)))))))) (.run (.step 53 (.split 51 1 (.split 61 1 (.split 62 1 (.split 54 1 (.split 68 1 (.split 72 1 (.step 53 (.step 70 (.split 69 1 (.step 7 (.close 53)) (.step 72 (.close 7))))) (.step 18 (.step 26 (.step 7 (.close 53))))) (.step 18 (.step 53 (.close 15)))) (.step 57 (.close 53))) (.step 53 (.close 4))) (.step 52 (.step 65 (.step 70 (.step 71 (.step 72 (.step 53 (.step 4 (.step 64 (.close 7)))))))))) (.step 53 (.close 54))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279576264966067672917373453177388234847326484906667312453706874118737162002209268745575682315794683731408169240406591058901754445824⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 54 1 (.step 52 (.step 7 (.close 52))) (.step 9 (.step 57 (.close 7)))) (.step 18 (.step 7 (.close 52)))) (.step 55 (.step 26 (.step 52 (.close 57))))) (.step 52 (.step 57 (.step 71 (.step 64 (.step 7 (.close 52))))))) (.step 52 (.close 71))) (.step 52 (.close 7))) (.step 53 (.step 64 (.step 70 (.step 71 (.step 65 (.step 52 (.step 7 (.step 9 (.step 7 (.close 22))))))))))) (.step 52 (.close 7))) (.step 52 (.close 54)))))) (.run (.step 54 (.step 70 (.split 49 1 (.split 50 1 (.split 54 1 (.split 68 1 (.split 72 1 (.split 21 0 (.split 35 0 (.split 59 1 (.split 10 0 (.split 12 0 (.split 16 0 (.step 46 (.step 7 (.close 9))) (.step 7 (.close 30))) (.step 10 (.step 46 (.split 34 0 (.split 36 0 (.step 9 (.close 4)) (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 7 (.close 46))) (.step 9 (.close 46))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 9 (.step 46 (.close 64))))) (.step 9 (.close 46))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900805023143666418788695380519316503456482003705408553886748635502143176743027983433406087168000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 12 0 (.step 7 (.split 16 0 (.split 72 1 (.step 9 (.step 18 (.step 21 (.step 7 (.close 38))))) (.step 29 (.close 75))) (.step 7 (.close 18)))) (.step 9 (.step 38 (.step 18 (.step 15 (.step 21 (.step 7 (.close 16)))))))) (.step 57 (.close 71))) (.step 38 (.close 71))) (.step 7 (.step 9 (.step 21 (.step 26 (.close 71)))))) (.step 21 (.step 7 (.step 10 (.close 21))))) (.step 63 (.step 15 (.step 71 (.close 53))))) (.step 53 (.step 18 (.step 26 (.step 7 (.close 71)))))) (.step 21 (.step 57 (.close 7)))) (.step 7 (.step 22 (.step 53 (.step 54 (.step 26 (.step 54 (.close 75)))))))) (.step 21 (.step 18 (.close 53)))) (.step 52 (.step 53 (.step 57 (.step 18 (.step 71 (.step 52 (.step 26 (.step 7 (.close 52)))))))))) (.step 7 (.step 9 (.close 10)))) (.split 49 1 (.split 50 1 (.step 41 (.split 61 1 (.step 38 (.step 7 (.step 21 (.close 38)))) (.step 7 (.step 21 (.step 31 (.close 38)))))) (.step 7 (.close 21))) (.step 7 (.close 38)))) (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.step 41 (.step 38 (.step 7 (.step 21 (.close 38))))) (.step 7 (.close 21))) (.step 7 (.close 38))) (.step 38 (.close 39))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900805023143666418788695380519316503456482003705408553886748635502143176743027983433406087168000⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 26 (.split 59 1 (.split 61 1 (.step 26 (.step 7 (.close 71))) (.step 31 (.close 64))) (.step 7 (.close 37))))) (.step 26 (.step 7 (.close 57)))) (.step 7 (.step 18 (.step 29 (.step 38 (.step 40 (.step 45 (.step 26 (.close 53))))))))) (.step 55 (.step 52 (.step 7 (.step 26 (.close 37)))))))) (.run (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 57 (.step 71 (.split 59 1 (.split 61 1 (.step 57 (.step 31 (.step 26 (.close 31)))) (.step 31 (.close 71))) (.step 7 (.close 26)))))) (.step 31 (.step 29 (.step 39 (.close 57))))) (.step 18 (.step 29 (.step 38 (.step 40 (.step 53 (.close 57))))))) (.step 55 (.step 52 (.step 7 (.step 37 (.close 26)))))) (.split 49 1 (.split 50 1 (.step 39 (.split 54 1 (.step 7 (.step 40 (.step 57 (.split 59 1 (.split 61 1 (.step 39 (.step 7 (.close 39))) (.step 31 (.step 39 (.close 64)))) (.step 7 (.close 37)))))) (.step 39 (.close 37)))) (.step 7 (.step 26 (.step 38 (.step 37 (.close 57)))))) (.step 7 (.step 26 (.step 52 (.close 57))))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244811554998574619695868897366901790430875013596117410043452853321728⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 15 (.step 71 (.split 59 1 (.split 61 1 (.step 15 (.step 31 (.step 26 (.close 71)))) (.step 15 (.close 31))) (.step 7 (.close 26)))))) (.step 15 (.step 7 (.close 57)))) (.step 15 (.step 7 (.step 21 (.close 62))))) (.step 15 (.step 52 (.step 7 (.step 26 (.close 21)))))) (.step 37 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 40 (.split 59 1 (.split 61 1 (.step 15 (.step 26 (.step 7 (.close 37)))) (.step 15 (.close 64))) (.step 7 (.close 37))))) (.step 15 (.step 31 (.step 7 (.close 37))))) (.step 7 (.step 37 (.close 53)))) (.step 7 (.step 37 (.close 52)))))) (.step 37 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 40 (.step 15 (.step 57 (.split 59 1 (.step 7 (.step 37 (.close 64))) (.step 7 (.close 21))))))) (.step 15 (.close 39))) (.step 7 (.step 15 (.step 39 (.close 52))))) (.step 7 (.step 37 (.close 52)))))) (.step 15 (.step 37 (.split 49 1 (.split 50 1 (.step 41 (.step 38 (.step 7 (.step 15 (.close 38))))) (.step 7 (.close 21))) (.step 7 (.close 38)))))))) (.run (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 15))) (.step 18 (.close 7))) (.step 18 (.step 7 (.close 52)))))) (.run (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 4))) (.step 18 (.close 7))) (.step 26 (.step 18 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168168152734782046042577707338825728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 43 1 (.split 51 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 34 0 (.split 35 0 (.split 72 0 (.split 17 0 (.split 16 0 (.step 15 (.split 22 0 (.step 9 (.step 7 (.close 15))) (.step 4 (.close 7)))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 15))) (.step 15 (.close 7))) (.step 4 (.step 15 (.step 10 (.step 15 (.close 53)))))) (.step 4 (.step 15 (.close 71)))) (.step 15 (.step 70 (.step 26 (.step 71 (.split 69 1 (.step 15 (.close 7)) (.step 4 (.step 15 (.close 7))))))))) (.step 4 (.step 15 (.step 16 (.step 10 (.step 21 (.step 64 (.step 65 (.close 7))))))))) (.step 15 (.step 57 (.step 54 (.step 15 (.step 7 (.step 4 (.close 54)))))))) (.step 9 (.close 46))) (.step 16 (.step 64 (.step 4 (.close 15))))) (.step 15 (.close 62))) (.step 15 (.close 4))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 15 (.step 7 (.close 15)))) (.step 7 (.step 15 (.step 29 (.step 31 (.step 37 (.step 7 (.close 39)))))))) (.step 21 (.step 15 (.close 38)))) (.step 15 (.step 7 (.close 15)))) (.step 18 (.close 15))) (.step 5 (.step 18 (.close 15)))) (.step 4 (.step 15 (.close 7)))) (.step 5 (.step 18 (.close 15)))) (.step 5 (.step 18 (.close 15)))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168169420385382274271979204042031104⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.step 18 (.step 40 (.step 68 (.step 4 (.step 9 (.close 10)))))) (.step 31 (.step 5 (.step 34 (.step 18 (.close 64)))))) (.step 4 (.step 9 (.step 18 (.close 26))))) (.step 4 (.step 18 (.close 57)))) (.step 7 (.step 22 (.close 54)))) (.step 4 (.step 18 (.close 53)))) (.step 4 (.step 18 (.close 52)))) (.step 7 (.step 24 (.close 26)))) (.step 7 (.step 24 (.close 39)))) (.step 4 (.step 18 (.close 38)))) (.step 7 (.step 31 (.close 37)))))) (.run (.split 22 1 (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 4))) (.step 18 (.close 7))) (.step 22 (.step 18 (.close 7)))) (.step 7 (.step 18 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))))))) (.run (.step 18 (.split 17 1 (.split 22 1 (.split 49 1 (.split 50 1 (.step 7 (.step 18 (.close 4))) (.step 18 (.close 7))) (.step 21 (.step 18 (.close 7)))) (.step 7 (.step 18 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))))) (.step 7 (.step 18 (.step 19 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52)))))))))) (.reuse 1)) (.run (.step 7 (.split 12 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 15 (.close 18))) (.step 18 (.close 7))) (.step 18 (.step 7 (.close 52)))) (.step 7 (.close 18))) (.step 15 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case45
