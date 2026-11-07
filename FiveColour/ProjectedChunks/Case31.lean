module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case31
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168169420385382276577822213255725056⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨2147483648, 11031304536487720240955970973191984381084500630769492679916833617023780404672701586152017245777266494690284288273142738280548349377904898994297227759108898615751692076783260840166542302437209294479014815099607425482752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 6 0 (.split 21 0 (.split 35 0 (.split 68 0 (.step 7 (.close 9)) (.step 7 (.close 57))) (.step 7 (.step 9 (.close 21)))) (.step 7 (.step 9 (.step 7 (.close 40))))) (.split 10 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 17 0 (.step 46 (.split 68 0 (.step 7 (.close 9)) (.step 7 (.close 9)))) (.step 4 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 4)))) (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 26 (.step 40 (.close 71)))))) (.step 71 (.split 6 0 (.split 10 0 (.split 12 0 (.split 17 0 (.step 72 (.close 7)) (.step 7 (.close 4))) (.step 4 (.step 72 (.close 7)))) (.step 7 (.close 52))) (.step 10 (.split 10 0 (.step 4 (.step 9 (.close 22))) (.step 7 (.close 9))))))) (.step 71 (.close 4))) (.step 70 (.step 71 (.split 69 1 (.split 72 1 (.split 21 0 (.step 70 (.close 9)) (.step 7 (.close 4))) (.step 7 (.close 70))) (.step 70 (.close 7)))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482647896611133072268967799598839945926942495661812992169304799749288910841693435377197545194017316078588993256377040868500715816536594928338128563010724850551882776576⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.split 61 1 (.split 62 1 (.reuse 0) (.run (.split 68 1 (.split 72 1 (.split 6 0 (.split 10 0 (.step 65 (.split 67 1 (.split 12 0 (.split 16 0 (.split 30 0 (.split 43 0 (.step 7 (.step 4 (.close 71))) (.step 10 (.step 9 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.close 4))) (.split 16 0 (.step 4 (.step 10 (.step 21 (.step 64 (.close 7))))) (.step 4 (.close 7)))) (.step 65 (.close 70)))) (.step 7 (.close 65))) (.step 10 (.step 72 (.split 10 0 (.split 67 1 (.step 4 (.step 9 (.close 22))) (.step 10 (.close 65))) (.step 7 (.close 65)))))) (.step 4 (.close 71))) (.step 63 (.close 71))))) (.run (.split 68 1 (.split 72 1 (.split 6 0 (.split 12 0 (.split 16 0 (.step 64 (.split 67 1 (.split 34 0 (.split 43 0 (.step 7 (.close 53)) (.step 10 (.step 30 (.close 64)))) (.step 7 (.close 15))) (.step 64 (.close 7)))) (.step 7 (.close 64))) (.step 64 (.step 4 (.split 10 0 (.step 64 (.close 4)) (.step 7 (.close 52)))))) (.step 10 (.step 72 (.split 10 0 (.step 4 (.step 64 (.split 16 0 (.step 4 (.step 10 (.close 53))) (.step 4 (.close 7))))) (.step 10 (.step 7 (.close 52))))))) (.step 4 (.step 10 (.close 71)))) (.step 63 (.close 64))))) (.run (.step 62 (.split 61 1 (.step 62 (.split 67 1 (.step 71 (.split 62 1 (.split 69 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 72 (.close 7))) (.step 65 (.close 7)))) (.step 26 (.close 70)))) (.step 64 (.step 62 (.step 64 (.step 7 (.close 9)))))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635115217984954543119347244866627344068045132222223771465839302350749204423745994752⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 72 1 (.split 12 0 (.split 67 1 (.split 21 0 (.split 34 0 (.split 69 1 (.split 35 0 (.step 54 (.step 9 (.close 7))) (.step 9 (.close 57))) (.step 4 (.close 57))) (.step 9 (.step 7 (.close 15)))) (.step 4 (.step 9 (.step 7 (.close 40))))) (.step 26 (.step 54 (.step 57 (.close 70))))) (.step 15 (.close 57))) (.step 26 (.close 57))) (.step 4 (.step 9 (.close 71)))) (.step 4 (.step 21 (.step 10 (.step 57 (.close 65)))))) (.step 4 (.step 15 (.step 10 (.step 57 (.close 64)))))) (.step 57 (.close 62))))) (.run (.split 54 1 (.split 68 1 (.split 72 1 (.step 54 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.step 7 (.close 53)) (.step 22 (.close 7))) (.step 54 (.close 65))) (.step 54 (.close 64))) (.step 54 (.close 7)))) (.step 7 (.step 22 (.step 9 (.close 54))))) (.step 7 (.step 54 (.close 71)))) (.step 54 (.close 57))))) (.run (.split 51 1 (.split 54 1 (.split 68 1 (.split 61 1 (.step 53 (.split 67 1 (.split 69 1 (.split 72 1 (.step 53 (.step 7 (.close 9))) (.step 9 (.step 18 (.step 21 (.step 7 (.close 53)))))) (.step 53 (.step 72 (.close 7)))) (.step 53 (.close 7)))) (.step 52 (.step 53 (.step 64 (.step 53 (.step 4 (.step 64 (.step 7 (.close 9))))))))) (.step 18 (.step 53 (.close 64)))) (.step 57 (.close 53))) (.step 53 (.close 54)))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775634760222489937077505622052248734149581064040202605968330172676848182290800644805214904974012198476081975525376⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 54 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.step 52 (.step 7 (.close 52))) (.step 9 (.step 18 (.step 26 (.close 52))))) (.step 52 (.step 64 (.step 7 (.close 52))))) (.step 52 (.close 71))) (.step 52 (.close 7))) (.step 52 (.step 53 (.step 64 (.step 65 (.step 70 (.step 7 (.close 52)))))))) (.step 57 (.close 52))) (.step 52 (.close 54)))))) (.run (.step 54 (.step 70 (.split 49 1 (.split 50 1 (.split 54 1 (.split 68 1 (.split 72 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 10 0 (.split 16 0 (.step 46 (.step 7 (.close 9))) (.step 7 (.close 4))) (.step 7 (.close 9))) (.step 10 (.close 46))) (.step 10 (.close 46))) (.step 10 (.step 30 (.close 46)))) (.step 9 (.close 46))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 9 (.close 46)))) (.step 9 (.close 46))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46)))))))) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 26 (.step 71 (.step 7 (.close 9))))) (.step 26 (.step 9 (.step 31 (.close 57))))) (.step 7 (.step 18 (.step 38 (.step 9 (.step 7 (.close 62))))))) (.step 7 (.step 18 (.step 26 (.step 29 (.step 40 (.step 9 (.close 52))))))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900807060179642753274781648965004912834643055173802219822999271642592531124328899691616877412352⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.split 42 1 (.step 57 (.split 49 1 (.step 7 (.step 57 (.step 9 (.step 71 (.step 7 (.step 26 (.close 7))))))) (.step 7 (.step 18 (.step 29 (.step 40 (.step 9 (.close 52)))))))) (.split 49 1 (.split 50 1 (.split 59 1 (.step 39 (.step 7 (.step 39 (.step 31 (.close 39))))) (.step 7 (.step 9 (.close 39)))) (.step 7 (.step 9 (.step 21 (.close 62))))) (.step 7 (.step 9 (.step 26 (.step 37 (.close 52))))))))) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 72 1 (.step 71 (.step 7 (.step 9 (.step 21 (.step 7 (.close 15)))))) (.step 29 (.step 38 (.close 71)))) (.step 7 (.step 9 (.step 21 (.close 70))))) (.step 4 (.step 21 (.close 7)))) (.step 4 (.step 15 (.step 10 (.close 71))))) (.step 9 (.step 18 (.step 21 (.step 26 (.close 71)))))) (.step 21 (.step 38 (.step 57 (.close 4))))) (.step 7 (.step 22 (.step 9 (.step 21 (.step 54 (.close 26))))))) (.step 9 (.step 21 (.step 7 (.close 21))))) (.step 9 (.step 52 (.step 53 (.step 18 (.step 57 (.step 38 (.step 16 (.close 71))))))))) (.step 7 (.step 9 (.close 10)))) (.split 49 1 (.step 41 (.step 38 (.step 7 (.step 21 (.close 38))))) (.step 7 (.close 38)))) (.step 57 (.step 38 (.step 39 (.step 7 (.step 21 (.close 38))))))))) (.run (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 9 (.close 18))) (.step 18 (.close 7))) (.step 18 (.step 7 (.close 52)))) (.step 7 (.close 18)))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244811554998574619695868897366901790430875013596118562964957460168704⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 34 1 (.reuse 0) (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 15 (.step 9 (.step 31 (.step 26 (.close 71)))))) (.step 15 (.step 7 (.close 57)))) (.step 15 (.step 7 (.step 9 (.close 53))))) (.step 7 (.step 15 (.step 9 (.step 7 (.close 52)))))) (.step 37 (.split 49 1 (.split 50 1 (.split 59 1 (.split 62 1 (.split 69 1 (.split 54 1 (.step 7 (.close 37)) (.step 15 (.step 7 (.close 37)))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 7 (.step 9 (.close 37)))) (.step 15 (.step 37 (.close 52)))))) (.split 49 1 (.split 50 1 (.split 59 1 (.step 39 (.step 7 (.step 37 (.close 31)))) (.step 7 (.close 37))) (.step 7 (.step 9 (.close 37)))) (.step 15 (.step 37 (.close 52))))) (.step 15 (.step 37 (.step 38 (.step 7 (.step 9 (.step 21 (.close 37)))))))))) (.run (.step 7 (.step 26 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 7)))))))
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

namespace Part6
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168168152734782047195499211945672704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 15 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 43 1 (.split 51 1 (.split 62 1 (.split 68 1 (.split 72 1 (.split 34 0 (.split 67 1 (.split 69 1 (.split 35 0 (.split 72 0 (.split 17 0 (.step 15 (.step 7 (.close 9))) (.step 4 (.close 7))) (.step 9 (.close 15))) (.step 7 (.close 15))) (.step 4 (.step 9 (.step 15 (.close 7))))) (.step 26 (.step 70 (.step 15 (.close 7))))) (.step 7 (.close 15))) (.step 15 (.close 4))) (.step 4 (.step 9 (.close 71)))) (.step 4 (.step 15 (.step 10 (.step 16 (.step 15 (.close 65))))))) (.step 15 (.step 54 (.step 22 (.step 54 (.step 15 (.close 7))))))) (.step 9 (.close 46))) (.step 4 (.step 15 (.close 64)))) (.step 15 (.close 62))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 15 (.step 7 (.close 15)))) (.step 15 (.step 7 (.close 15)))) (.step 15 (.close 38))) (.step 15 (.close 7))) (.step 18 (.close 9)))) (.step 7 (.close 26))) (.step 4 (.step 15 (.close 7)))) (.step 5 (.step 15 (.step 18 (.close 9))))) (.step 5 (.step 4 (.step 7 (.step 15 (.step 18 (.close 9))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168169420385382275424900708648878080⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 61 1 (.step 18 (.step 4 (.step 40 (.step 68 (.step 4 (.close 9)))))) (.step 31 (.step 5 (.step 10 (.step 18 (.close 4)))))) (.step 4 (.step 9 (.step 18 (.close 26))))) (.step 7 (.step 22 (.close 54)))) (.step 4 (.step 18 (.close 53)))) (.step 4 (.step 18 (.close 52)))) (.step 7 (.step 9 (.close 10)))) (.step 7 (.step 24 (.close 26)))) (.step 7 (.step 24 (.close 39)))) (.step 4 (.step 18 (.close 38)))) (.step 7 (.step 24 (.step 4 (.close 37))))))) (.run (.step 7 (.split 22 1 (.step 22 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 7)))) (.step 7 (.close 18)))))) (.run (.step 7 (.split 17 1 (.split 22 1 (.step 21 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 7)))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 19))))))) (.reuse 1)) (.run (.step 7 (.split 12 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 7 (.step 9 (.close 18))) (.step 18 (.close 7))) (.step 18 (.close 52))) (.step 7 (.close 18))) (.step 15 (.close 7))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168169420385382276577822213255725056⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.reuse 0) (.run (.split 10 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 61 1 (.split 67 1 (.split 62 1 (.step 9 (.split 69 1 (.split 16 0 (.split 34 0 (.split 36 0 (.step 9 (.close 4)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 4 (.close 10)))) (.step 4 (.step 9 (.close 10)))) (.step 9 (.step 10 (.step 26 (.step 70 (.split 34 0 (.step 9 (.close 4)) (.step 7 (.close 9)))))))) (.step 4 (.step 9 (.close 10)))) (.step 9 (.step 10 (.step 54 (.step 22 (.step 54 (.step 7 (.close 9)))))))) (.step 9 (.close 46))) (.step 9 (.step 7 (.step 9 (.close 10))))) (.step 7 (.step 9 (.step 29 (.step 31 (.step 39 (.step 7 (.close 9)))))))) (.step 7 (.step 9 (.step 29 (.step 31 (.step 37 (.step 7 (.close 9)))))))) (.step 9 (.step 7 (.close 9)))) (.step 5 (.step 9 (.close 18)))) (.step 5 (.step 4 (.step 7 (.step 9 (.close 18)))))) (.step 5 (.step 4 (.step 7 (.step 11 (.close 9)))))) (.step 7 (.step 9 (.step 7 (.close 9)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case31
