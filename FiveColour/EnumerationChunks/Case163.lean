module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case163
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644322952907283345965056⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908392998381874375607, 5789234131009374243490890256636772759901851996560544808214778193549775928795277575978058672488451386148482820637016487820419584261128081612316866307095117301248629629600134054099986201414770618195247788012495054996921910273, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904443229329621762877716815095803433753783035401925558845793450693587522711797889167563343395699730505224374806674248884844609171051730579925497825057099935621973016576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.split 16 0 (.step 7 (.step 9 (.step 7 (.step 15 (.step 7 (.close 17)))))) (.step 7 (.step 17 (.close 18))))) (.split 16 0 (.split 17 0 (.step 9 (.close 7)) (.step 18 (.step 7 (.close 9)))) (.step 18 (.step 7 (.close 9))))) (.split 6 0 (.step 18 (.split 10 0 (.step 29 (.step 75 (.close 7))) (.step 7 (.step 9 (.close 15))))) (.step 9 (.close 7)))) (.split 72 1 (.split 6 0 (.split 21 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.step 9 (.close 21)))) (.step 7 (.close 9))) (.split 21 0 (.split 35 0 (.step 70 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 21 (.close 26)))))) (.split 67 1 (.split 72 1 (.split 10 0 (.split 6 0 (.split 12 0 (.step 7 (.step 18 (.step 7 (.step 9 (.step 7 (.step 18 (.close 21))))))) (.step 9 (.step 18 (.step 15 (.step 7 (.close 21)))))) (.step 9 (.close 7))) (.step 18 (.split 6 0 (.step 7 (.step 9 (.step 7 (.close 15)))) (.step 9 (.close 7))))) (.step 9 (.step 26 (.close 7)))) (.step 26 (.step 62 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660749386805549175884476045519682621152070220555079396390043072223356798867117014992814086484636469259678209525254359177288413835952018511731236165308645376⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.split 21 0 (.split 34 0 (.split 35 0 (.step 7 (.close 9)) (.step 9 (.step 7 (.close 18)))) (.step 15 (.step 18 (.step 9 (.step 7 (.close 21)))))) (.step 9 (.step 7 (.close 18)))) (.step 9 (.step 15 (.step 18 (.close 21))))) (.step 9 (.step 26 (.step 18 (.step 15 (.step 18 (.close 21))))))) (.step 57 (.split 21 0 (.split 10 0 (.split 12 0 (.split 34 0 (.split 16 0 (.step 9 (.step 7 (.close 21))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.step 15 (.step 26 (.step 7 (.close 21)))))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 26)))))) (.step 9 (.step 26 (.step 18 (.step 15 (.close 21)))))))) (.run (.split 54 1 (.split 67 1 (.split 72 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.step 9 (.close 21)))) (.step 7 (.close 9))) (.split 21 0 (.split 35 0 (.split 72 0 (.step 46 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 62 (.close 7))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 54 (.step 7 (.step 9 (.step 26 (.step 21 (.close 54))))))) (.step 57 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922103644135012059424734283689937543763013994501621657294080218808964757922244700851138879601264205679804898147291492715493647477374976⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 6 0 (.split 12 0 (.step 7 (.step 18 (.step 7 (.step 9 (.step 7 (.step 18 (.close 21))))))) (.step 9 (.step 18 (.step 15 (.step 7 (.close 21)))))) (.step 9 (.close 7))) (.step 18 (.split 6 0 (.step 7 (.step 9 (.step 7 (.close 15)))) (.step 9 (.close 7))))) (.step 9 (.step 38 (.step 18 (.step 26 (.close 7)))))) (.step 53 (.close 7))) (.step 53 (.close 7))) (.step 9 (.step 21 (.step 53 (.step 57 (.close 7)))))) (.step 53 (.close 7))))) (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 6 0 (.step 7 (.step 18 (.step 7 (.step 9 (.step 7 (.step 18 (.close 21))))))) (.step 9 (.close 7))) (.step 9 (.step 18 (.step 15 (.step 7 (.close 21)))))) (.step 18 (.split 6 0 (.step 7 (.step 9 (.step 7 (.close 15)))) (.step 9 (.close 7))))) (.step 9 (.step 40 (.step 26 (.step 7 (.step 15 (.step 18 (.close 21)))))))) (.step 52 (.close 7))) (.step 52 (.close 7))) (.step 9 (.step 52 (.step 57 (.close 7))))) (.step 52 (.close 7))) (.step 52 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452123411166788548947610075842614532351263478466837987518627380693192075645315780456802274236058573561152065765376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 34 0 (.step 7 (.step 21 (.close 26))) (.split 49 0 (.step 7 (.step 29 (.step 37 (.step 7 (.close 21))))) (.step 7 (.step 15 (.step 21 (.close 26)))))) (.step 7 (.close 15))) (.step 29 (.step 75 (.split 21 0 (.split 34 0 (.step 7 (.close 9)) (.step 45 (.step 7 (.close 9)))) (.step 7 (.close 9)))))) (.step 18 (.step 26 (.step 29 (.step 40 (.step 9 (.step 7 (.step 26 (.step 15 (.close 21)))))))))) (.step 26 (.step 29 (.step 57 (.split 21 0 (.split 10 0 (.split 6 0 (.split 49 0 (.step 45 (.close 7)) (.step 7 (.step 26 (.step 15 (.close 21))))) (.step 9 (.close 7))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 7 (.step 9 (.step 7 (.close 15))))))))) (.step 26 (.step 55 (.step 9 (.step 53 (.step 38 (.step 45 (.step 18 (.step 26 (.step 15 (.step 52 (.close 53)))))))))))) (.step 26 (.step 55 (.step 9 (.step 52 (.step 18 (.step 26 (.step 37 (.step 21 (.step 15 (.close 52)))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125759709371322780837965323211321688290854149386895838498087984163607854340895065245737935056958329855097700352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 34 0 (.step 7 (.step 21 (.close 26))) (.split 49 0 (.step 7 (.step 29 (.step 37 (.step 7 (.close 21))))) (.step 7 (.step 15 (.step 21 (.close 26)))))) (.step 7 (.close 15))) (.step 29 (.step 75 (.split 21 0 (.split 34 0 (.step 7 (.close 9)) (.split 49 0 (.step 39 (.close 7)) (.step 7 (.close 9)))) (.step 7 (.close 9)))))) (.step 18 (.step 29 (.step 40 (.step 9 (.step 7 (.step 26 (.step 15 (.close 21))))))))) (.step 29 (.step 57 (.close 7)))) (.step 57 (.step 75 (.step 55 (.step 9 (.step 7 (.step 15 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52)))))))))))) (.step 57 (.split 50 1 (.step 75 (.step 55 (.step 9 (.step 7 (.step 15 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52)))))))))) (.step 9 (.step 52 (.step 7 (.close 21))))))) (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.split 59 1 (.split 21 0 (.split 43 0 (.step 39 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.step 39 (.step 37 (.step 21 (.close 26))))))) (.step 29 (.step 39 (.step 9 (.step 37 (.close 57)))))) (.step 7 (.step 9 (.step 38 (.step 57 (.step 15 (.step 37 (.step 45 (.step 52 (.close 53))))))))))) (.step 7 (.step 9 (.step 26 (.step 57 (.step 45 (.step 38 (.step 37 (.close 52))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762002869938770909476934032216990377794945951885006779211721752447241263771153730546005075511439980784254976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 67 1 (.split 6 0 (.step 18 (.split 10 0 (.step 29 (.step 38 (.close 7))) (.step 7 (.step 9 (.close 15))))) (.step 9 (.close 7))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 29 (.step 38 (.close 7)))) (.step 9 (.step 26 (.step 38 (.step 40 (.step 26 (.step 18 (.step 15 (.close 21))))))))) (.step 9 (.step 21 (.step 38 (.step 57 (.close 7)))))) (.step 57 (.step 7 (.step 9 (.step 26 (.step 21 (.close 38))))))) (.step 9 (.step 21 (.step 38 (.step 18 (.step 21 (.close 26))))))) (.step 9 (.step 53 (.step 57 (.step 62 (.step 75 (.step 52 (.step 40 (.step 38 (.step 7 (.step 21 (.close 26)))))))))))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 38 (.step 7 (.close 37)))))) (.step 7 (.step 29 (.step 38 (.step 7 (.step 37 (.close 38))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732142405299924596678035534750176926387658708231080740990161307942280966676857026506265388615646661845413515621185427260821189319651731342529433434493715729549215479186199674880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 36 0 (.step 7 (.step 15 (.close 21))) (.split 49 0 (.step 7 (.step 29 (.close 37))) (.step 7 (.step 15 (.step 21 (.close 26)))))) (.step 7 (.close 15))) (.step 29 (.step 75 (.split 21 0 (.split 36 0 (.step 7 (.close 9)) (.step 37 (.step 7 (.close 9)))) (.step 7 (.close 9)))))) (.step 15 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 15 (.step 29 (.step 57 (.step 75 (.split 6 0 (.step 7 (.step 21 (.close 26))) (.step 9 (.close 7)))))))) (.step 15 (.step 57 (.step 75 (.step 55 (.step 9 (.step 7 (.step 21 (.step 37 (.step 38 (.step 26 (.close 52)))))))))))) (.step 15 (.step 52 (.step 18 (.step 29 (.step 40 (.step 9 (.step 7 (.step 26 (.step 52 (.step 26 (.close 37)))))))))))) (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.split 59 1 (.split 6 0 (.step 37 (.close 7)) (.step 29 (.step 37 (.close 7)))) (.step 7 (.step 9 (.step 15 (.close 37))))) (.step 15 (.step 29 (.step 39 (.step 26 (.step 7 (.step 9 (.step 21 (.step 37 (.close 52)))))))))) (.step 7 (.step 9 (.step 15 (.step 37 (.step 38 (.step 52 (.step 45 (.close 53)))))))))) (.step 7 (.step 9 (.step 15 (.step 26 (.step 52 (.step 37 (.close 52))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513087281144589659270946239224073530504013861256652436342227563024910706950456388933252391370752⟩
def references : Fin 5 → Box := ![Part2.root, Part3.root, Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 5 := (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 67 1 (.split 72 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.split 21 0 (.split 35 0 (.split 10 0 (.split 34 0 (.step 46 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 46 (.step 70 (.step 7 (.close 9))))) (.step 9 (.close 7))) (.step 46 (.step 54 (.step 7 (.close 9))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.step 7 (.split 35 1 (.split 36 1 (.reuse 4) (.run (.split 49 1 (.step 45 (.split 50 1 (.step 37 (.split 54 1 (.split 59 1 (.split 6 0 (.step 37 (.close 7)) (.step 29 (.step 37 (.close 7)))) (.step 7 (.step 9 (.step 15 (.close 37))))) (.step 15 (.step 29 (.step 39 (.step 9 (.close 52))))))) (.step 7 (.step 9 (.step 15 (.step 37 (.step 26 (.step 38 (.step 52 (.step 39 (.step 45 (.step 26 (.close 53))))))))))))) (.step 7 (.step 9 (.step 15 (.step 37 (.step 52 (.step 37 (.close 52)))))))))) (.run (.step 29 (.step 38 (.step 7 (.close 37))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671446936548871827712212790721416926082462382858164938050027550408704⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.step 7 (.step 18 (.close 7))) (.step 7 (.step 9 (.close 18)))) (.step 18 (.close 9))) (.step 18 (.step 53 (.step 7 (.close 9))))) (.step 18 (.step 53 (.split 54 1 (.step 7 (.step 53 (.step 7 (.close 9)))) (.step 9 (.step 7 (.step 18 (.close 52)))))))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18)))))))))) (.run (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.split 6 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 7 (.step 9 (.close 18)))) (.step 18 (.close 9))) (.step 18 (.step 26 (.step 55 (.step 27 (.close 53)))))) (.step 18 (.step 26 (.step 55 (.step 27 (.step 52 (.close 7))))))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150414832622317444071673540634295504383757565823025152⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 35 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 12 0 (.split 34 1 (.split 36 1 (.split 42 1 (.step 7 (.step 9 (.close 26))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 26)))) (.step 7 (.step 9 (.step 26 (.close 37))))) (.step 9 (.split 34 1 (.split 36 1 (.split 42 1 (.step 7 (.step 26 (.close 54))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.close 15))))) (.step 7 (.step 9 (.step 18 (.step 26 (.step 15 (.close 37))))))) (.step 7 (.step 9 (.step 7 (.step 18 (.step 26 (.close 54))))))) (.step 9 (.step 57 (.close 7)))) (.step 7 (.step 9 (.step 18 (.close 53))))) (.step 7 (.step 9 (.step 18 (.close 52))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 18 (.step 38 (.close 37)))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.split 6 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 7 (.step 9 (.close 18)))) (.step 18 (.close 9))) (.step 18 (.step 22 (.step 55 (.step 27 (.close 53)))))) (.step 18 (.step 22 (.step 55 (.step 27 (.step 52 (.close 7))))))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 7 (.step 11 (.step 18 (.step 52 (.close 53))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922103644135012059424734283689937543763013994501621657294080218808966444564415955088830127622940503784459278190003830133807970938519552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.step 18 (.split 21 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 21 0 (.split 35 0 (.split 49 0 (.step 7 (.close 9)) (.step 9 (.step 7 (.close 15)))) (.step 9 (.step 15 (.close 7)))) (.step 9 (.step 15 (.close 7)))) (.step 15 (.close 7))) (.step 9 (.step 15 (.close 7)))) (.step 15 (.split 21 0 (.split 10 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 22 0 (.step 9 (.step 7 (.close 15))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))))) (.step 9 (.step 7 (.step 15 (.close 7)))))) (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 7 (.step 17 (.step 7 (.step 21 (.step 22 (.close 26)))))))))))) (.step 15 (.step 7 (.step 11 (.step 17 (.close 18)))))) (.step 7 (.step 15 (.step 57 (.step 62 (.split 21 1 (.split 67 1 (.split 10 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 16 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 70 (.close 7))) (.step 7 (.step 9 (.close 15))))))))) (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 22 (.step 26 (.close 53)))))))))))) (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 26 (.close 52)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303819740104044093570584282035912704⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 7 (.step 9 (.close 7))))) (.run (.step 7 (.step 15 (.step 26 (.step 29 (.split 21 1 (.split 21 0 (.split 10 0 (.split 6 0 (.split 49 0 (.step 45 (.close 7)) (.step 7 (.close 15))) (.step 9 (.close 7))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 7 (.step 9 (.close 15)))))))))) (.run (.step 7 (.step 15 (.step 29 (.step 57 (.step 75 (.split 21 1 (.split 42 1 (.split 6 0 (.step 7 (.close 15)) (.step 9 (.close 7))) (.step 37 (.step 39 (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 15))))))))))) (.run (.step 9 (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 7 (.step 18 (.step 21 (.step 22 (.close 26))))))))))))) (.run (.step 7 (.step 15 (.close 7))))) (.run (.step 7 (.step 15 (.step 18 (.step 9 (.step 15 (.close 52))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644321799985778739118080⟩
def references : Fin 2 → Box := ![Part9.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.split 6 0 (.step 7 (.close 18)) (.step 18 (.close 7))) (.step 7 (.step 9 (.close 18)))) (.step 18 (.close 9))) (.step 18 (.step 21 (.step 42 (.step 53 (.step 18 (.close 7))))))) (.step 18 (.step 21 (.step 42 (.step 53 (.step 55 (.step 27 (.close 52)))))))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 7 (.step 11 (.step 18 (.step 52 (.close 53)))))) (.step 7 (.step 11 (.step 18 (.split 35 1 (.step 18 (.step 19 (.step 25 (.step 52 (.close 53))))) (.step 18 (.close 19))))))))))) (.reuse 1)) (.run (.step 7 (.split 12 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.step 7 (.step 18 (.close 7))) (.step 7 (.step 9 (.step 15 (.close 18))))) (.step 15 (.close 18))) (.step 18 (.split 54 1 (.step 7 (.step 52 (.step 7 (.close 9)))) (.step 9 (.step 7 (.step 15 (.step 7 (.close 18)))))))) (.step 18 (.step 52 (.step 7 (.close 9))))) (.step 18 (.step 7 (.step 9 (.step 7 (.close 15)))))) (.step 15 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2305843011361177600, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762002869938770909476934032216990377794947638527178033449413000468917560546580114803801541178868748571901952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.step 18 (.step 9 (.split 67 1 (.split 34 0 (.split 36 0 (.step 9 (.close 7)) (.step 18 (.close 9))) (.step 15 (.step 18 (.close 9)))) (.split 21 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 7 (.close 9)) (.step 57 (.step 7 (.close 9)))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 9 (.step 21 (.step 9 (.step 11 (.close 9)))))) (.step 9 (.step 21 (.step 9 (.step 11 (.close 9)))))) (.step 7 (.step 9 (.step 57 (.split 67 1 (.split 21 0 (.split 35 0 (.split 10 0 (.split 16 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 46 (.step 70 (.close 7)))))))) (.step 9 (.step 21 (.step 9 (.step 11 (.close 9)))))) (.step 9 (.step 21 (.step 9 (.step 11 (.close 9)))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 9 (.step 29 (.split 21 0 (.split 34 0 (.split 35 0 (.step 18 (.close 9)) (.step 9 (.close 7))) (.step 15 (.step 45 (.step 7 (.close 9))))) (.step 7 (.close 9))))))) (.step 7 (.step 9 (.step 29 (.step 57 (.split 42 1 (.split 21 0 (.split 34 0 (.step 7 (.close 9)) (.step 15 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 45 (.step 7 (.close 9))))))))) (.step 9 (.step 18 (.close 9)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644322952907283345965056⟩
def references : Fin 2 → Box := ![Part12.root, Part13.root]
def proof : Chunks.Proof 2 := (.split 6 1 (.reuse 0) (.split 10 1 (.split 12 1 (.split 30 1 (.split 34 1 (.reuse 1) (.run (.step 7 (.step 9 (.step 15 (.step 29 (.split 36 1 (.split 42 1 (.split 21 0 (.split 36 0 (.step 7 (.close 9)) (.step 57 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 45 (.step 7 (.close 9)))) (.step 37 (.step 39 (.step 7 (.close 9))))))))))) (.run (.step 7 (.step 18 (.close 9))))) (.run (.step 9 (.step 21 (.step 15 (.step 7 (.step 11 (.close 9)))))))) (.run (.step 11 (.step 15 (.step 7 (.step 15 (.step 18 (.close 9)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part14.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case163

namespace FiveColour.Packed.EnumerationChunks.Projected.Case163
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 50 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 50 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 50 0).upper i := by decide +kernel
lemma budget_model : (⟨32908392998381874375607, 5789234131009374243490890256636772759901851996560544808214778193549775928795277575978058672488451386148482820637016487820419584261128081612316866307095117301248629629600134054099986201414770618195247788012495054996921910273, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 50), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908392998381874375607, 5789234131009374243490890256636772759901851996560544808214778193549775928795277575978058672488451386148482820637016487820419584261128081612316866307095117301248629629600134054099986201414770618195247788012495054996921910273, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 50) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 50 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 50 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 50) (Archive.root 50) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 50 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 50 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case163

namespace FiveColour.Packed.EnumerationChunks.Case163
def root : Box := Archive.root 50
def families : Fin 78 → List Cut := Enumeration.families 50
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case163.original_covered points
end FiveColour.Packed.EnumerationChunks.Case163
