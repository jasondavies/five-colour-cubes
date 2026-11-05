module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case141
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832589376755928668997108682832894707710076462020591537455646557167570371154622406493550142303538630521549672475708231706497879131967835682908788838197502738898984022354952192⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩]
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
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339634696057390253540763535145171875499029040707506839823264090299807717954378324660656491554518161958756784936418765180253998353323743738540738728103414588572327198683427961022971904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 74 1 (.step 31 (.split 72 1 (.split 2 0 (.split 14 0 (.split 16 0 (.step 31 (.step 3 (.step 32 (.step 3 (.step 5 (.close 18)))))) (.step 18 (.close 31))) (.split 34 0 (.step 67 (.step 18 (.step 3 (.step 5 (.close 12))))) (.step 3 (.step 12 (.step 3 (.step 5 (.close 31))))))) (.split 14 0 (.step 31 (.step 66 (.step 3 (.step 5 (.step 18 (.close 5)))))) (.step 12 (.step 23 (.step 12 (.step 3 (.step 5 (.step 18 (.step 5 (.close 31)))))))))) (.step 29 (.split 2 0 (.split 63 1 (.split 16 0 (.split 17 0 (.step 75 (.close 31)) (.step 3 (.step 18 (.step 31 (.close 12))))) (.step 3 (.step 18 (.step 31 (.close 12))))) (.step 12 (.step 66 (.close 3)))) (.step 31 (.step 3 (.step 12 (.step 3 (.step 21 (.close 32)))))))))) (.step 18 (.step 69 (.split 2 0 (.step 69 (.split 34 0 (.split 63 1 (.step 18 (.step 11 (.step 31 (.step 3 (.close 5))))) (.step 11 (.step 12 (.step 18 (.step 31 (.step 3 (.close 5))))))) (.step 18 (.step 17 (.step 5 (.close 31)))))) (.step 11 (.step 23 (.step 66 (.step 31 (.step 67 (.step 18 (.step 31 (.close 18)))))))))))) (.step 3 (.step 12 (.step 3 (.close 21))))) (.step 18 (.step 31 (.step 18 (.step 5 (.close 12)))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 21)))))) (.step 3 (.step 9 (.step 3 (.step 11 (.close 10)))))) (.step 3 (.step 31 (.close 12)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2787593149816327892691964784081049483214848, 11567172216946143397859013989258505539824339634696057390253540763535145171875499029040707506839823264090299810180582116437636741824471729722909746522102883928191210397205058557762380255126342180131867378484999318398024286208⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 18 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.step 27 (.split 51 1 (.split 56 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 34 0 (.split 35 1 (.split 36 0 (.step 11 (.step 67 (.split 38 0 (.split 42 0 (.step 12 (.step 3 (.step 17 (.close 3)))) (.step 3 (.step 12 (.step 3 (.close 5))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 5)))))))) (.step 3 (.step 12 (.step 18 (.step 5 (.step 31 (.close 32))))))) (.step 12 (.step 29 (.step 32 (.step 3 (.step 18 (.step 5 (.close 31)))))))) (.step 3 (.step 12 (.step 18 (.step 5 (.step 17 (.step 31 (.close 32)))))))) (.step 11 (.step 12 (.step 23 (.step 31 (.step 17 (.step 5 (.close 32)))))))) (.step 11 (.step 17 (.step 3 (.close 5))))) (.step 3 (.close 12))) (.step 3 (.step 5 (.step 12 (.close 17))))) (.step 3 (.close 12)))) (.step 3 (.step 5 (.step 12 (.close 31))))) (.step 3 (.step 5 (.step 12 (.step 18 (.close 5)))))) (.step 3 (.step 5 (.step 12 (.close 31))))) (.step 3 (.step 5 (.step 31 (.close 12))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339634696057390253540763535145171875499029040707506839823264090299810180582116437636741824471729722909746522102883928191210397205058557762380255126342180131867378484999318398025334784⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 43 1 (.step 51 (.step 18 (.step 31 (.step 63 (.step 66 (.step 5 (.step 12 (.close 18)))))))) (.step 3 (.close 10))))))) (.run (.step 3 (.step 31 (.close 12))))) (.run (.step 3 (.step 31 (.close 12))))) (.run (.step 9 (.step 31 (.step 32 (.split 51 1 (.step 75 (.step 3 (.step 29 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.step 66 (.step 31 (.close 3)))) (.step 3 (.step 31 (.step 12 (.close 32))))) (.step 3 (.step 18 (.step 31 (.step 12 (.close 32)))))) (.step 3 (.step 18 (.step 31 (.step 12 (.close 32)))))) (.step 3 (.step 31 (.step 12 (.close 32)))))))) (.step 3 (.close 21)))))))) (.run (.step 3 (.step 18 (.close 32))))) (.run (.step 3 (.step 18 (.close 32))))) (.run (.step 3 (.step 18 (.close 32))))) (.reuse 1)) (.run (.step 3 (.step 18 (.step 31 (.step 5 (.split 14 1 (.split 74 1 (.split 35 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 5 (.step 3 (.close 31))) (.step 3 (.step 5 (.step 12 (.step 31 (.close 32)))))) (.step 3 (.step 5 (.close 31)))) (.step 3 (.step 5 (.close 12)))) (.step 3 (.step 5 (.step 12 (.close 18))))) (.step 3 (.step 5 (.step 12 (.step 18 (.close 12)))))) (.step 3 (.step 31 (.step 5 (.step 12 (.step 32 (.close 66))))))) (.step 3 (.step 31 (.step 32 (.step 5 (.step 12 (.close 38))))))) (.step 5 (.step 18 (.step 12 (.step 18 (.close 66)))))) (.step 5 (.step 12 (.close 17))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨17350741762303288301255324726505233592430718434416092311654821463220390893739203583421689370594693101389196485621456874975989535943956833982217542175663796877910811186069807844798251453395170474334765216637959354571370266624, 23134333391815002265362563816272539653001741065417238379830951705730071083880018822481353363894000874126468754825662803999606392533769069051109454144835882449508648208339714170418975881596540922778200140680031900497120067584⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 18 (.step 27 (.step 69 (.split 65 1 (.split 2 1 (.split 14 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 51 1 (.step 11 (.split 35 1 (.split 56 1 (.split 67 1 (.split 2 0 (.split 34 0 (.step 77 (.step 66 (.step 18 (.step 31 (.step 3 (.close 5)))))) (.step 17 (.step 18 (.step 66 (.step 5 (.step 31 (.close 32))))))) (.step 23 (.close 77))) (.step 3 (.step 12 (.step 66 (.step 12 (.close 67)))))) (.step 3 (.step 5 (.step 18 (.step 12 (.step 66 (.step 12 (.close 67)))))))) (.step 3 (.step 5 (.step 23 (.step 32 (.step 66 (.step 69 (.step 31 (.step 74 (.step 3 (.step 5 (.close 12))))))))))))) (.step 3 (.step 12 (.close 36)))) (.step 3 (.step 5 (.step 31 (.step 12 (.step 66 (.step 12 (.close 67)))))))) (.step 3 (.step 5 (.step 18 (.step 12 (.step 66 (.step 12 (.close 67)))))))) (.step 3 (.step 5 (.step 31 (.step 12 (.step 66 (.step 12 (.close 67)))))))) (.step 3 (.step 5 (.step 17 (.step 31 (.close 66)))))) (.step 11 (.step 12 (.step 17 (.step 3 (.close 5)))))) (.step 3 (.step 5 (.step 17 (.step 69 (.step 67 (.step 74 (.step 12 (.step 18 (.close 66)))))))))) (.step 3 (.step 5 (.step 17 (.step 18 (.step 23 (.step 66 (.step 12 (.step 67 (.step 12 (.close 74)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4294967296, 23134344423119528469342060157039611857266280132044858189660179732051488734191009572112884835089343533144911518905292351163639293011419942826099406097477291475416082208677787433219155272190712990890074763497452939931977515008⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.step 3 (.split 72 2 (.split 74 2 (.split 65 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.split 14 1 (.split 35 1 (.split 38 1 (.split 56 1 (.step 63 (.split 63 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 31 (.split 16 0 (.step 63 (.step 3 (.close 18))) (.step 3 (.close 18)))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.step 12 (.close 23))))) (.step 3 (.step 26 (.step 31 (.close 21))))) (.step 12 (.step 63 (.step 3 (.close 66)))))) (.step 10 (.step 18 (.step 22 (.close 31))))) (.step 10 (.step 18 (.step 21 (.step 31 (.step 5 (.step 3 (.step 18 (.close 22))))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 5 (.step 12 (.step 17 (.step 18 (.close 17)))))))))))) (.reuse 1)) (.run (.step 9 (.step 29 (.step 31 (.step 38 (.step 69 (.split 65 1 (.split 2 1 (.split 14 1 (.split 16 1 (.split 17 1 (.step 75 (.step 51 (.step 66 (.step 3 (.step 12 (.close 18)))))) (.step 3 (.step 18 (.step 32 (.step 66 (.step 32 (.close 67))))))) (.step 3 (.step 18 (.step 32 (.step 38 (.step 66 (.close 67))))))) (.step 3 (.step 12 (.step 18 (.step 40 (.step 67 (.step 69 (.step 74 (.step 3 (.step 31 (.close 17))))))))))) (.step 3 (.step 5 (.step 31 (.step 66 (.step 67 (.step 5 (.step 69 (.step 12 (.close 32)))))))))) (.step 3 (.step 26 (.step 31 (.step 66 (.step 21 (.step 67 (.step 21 (.close 74)))))))))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129099878292929656859322879272865139657611978331117260307525794616938133160112630521832991598416855934954712553921526637361505678747306967044063312620971099963579962916051185855081127099985783798366208⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 56 2 (.split 63 2 (.split 64 2 (.split 71 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 66 (.step 3 (.step 67 (.step 69 (.step 74 (.step 3 (.step 18 (.close 31)))))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 66 (.step 67 (.step 3 (.step 18 (.step 31 (.step 67 (.step 3 (.step 31 (.step 3 (.step 5 (.close 18))))))))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 66 (.step 3 (.step 18 (.step 31 (.step 69 (.split 56 1 (.step 66 (.step 3 (.step 5 (.step 3 (.close 22))))) (.step 5 (.step 31 (.step 63 (.step 18 (.step 5 (.step 41 (.close 66))))))))))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 18 (.step 31 (.step 74 (.split 63 2 (.split 64 2 (.split 65 1 (.step 31 (.step 5 (.split 71 1 (.split 51 1 (.split 63 1 (.step 28 (.step 41 (.step 18 (.close 5)))) (.step 12 (.step 18 (.step 28 (.step 31 (.step 41 (.step 5 (.step 41 (.step 5 (.close 18)))))))))) (.step 3 (.close 18))) (.step 18 (.step 22 (.step 59 (.step 66 (.step 5 (.step 67 (.close 5)))))))))) (.step 3 (.step 10 (.step 16 (.step 18 (.step 22 (.step 41 (.step 43 (.step 18 (.step 31 (.step 21 (.close 63)))))))))))) (.step 5 (.step 18 (.step 31 (.step 41 (.step 63 (.step 66 (.close 67)))))))) (.step 5 (.step 12 (.step 18 (.step 31 (.step 63 (.close 66)))))))))))))))
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
def root : Box := ⟨6880495847970214534832462685906260822389694967504843371212766518160768628265454424210055659330381354631168, 23134344433892286795713129104550232122101987226767832589376755928668997108682832894707710076462017883852207481698903914781230401600906682269591550830965271342966304403622269168388411119730037201483664390663524479724192530432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 29 (.step 31 (.step 32 (.step 38 (.step 66 (.step 68 (.step 74 (.split 74 2 (.split 65 1 (.split 2 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 51 1 (.step 38 (.step 3 (.step 32 (.step 3 (.step 12 (.step 3 (.close 18))))))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 18 (.step 32 (.close 38))))) (.step 3 (.step 18 (.step 32 (.close 38))))) (.step 3 (.step 18 (.step 32 (.close 38))))) (.step 3 (.step 12 (.step 18 (.step 32 (.step 38 (.step 3 (.close 17)))))))) (.step 3 (.step 5 (.step 31 (.step 32 (.step 5 (.step 12 (.close 38)))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 5 (.step 17 (.step 18 (.step 23 (.step 32 (.step 66 (.step 69 (.step 38 (.step 12 (.close 74))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4181389724724491839037947176121572077338624, 11567183259023427928204680403569405684852646813397314788313655963357454358996646446151399881628294820992545434758396066223068477774043758793265037227867952595445954853342379240382946070602788920748249540867324949503364038656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 27 (.step 67 (.step 68 (.step 74 (.step 75 (.split 35 2 (.split 65 1 (.split 72 1 (.split 2 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 51 1 (.step 11 (.step 77 (.split 56 1 (.split 67 1 (.split 2 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 17 (.step 3 (.step 5 (.close 3)))) (.step 18 (.step 12 (.step 5 (.step 17 (.close 5)))))) (.step 12 (.step 17 (.step 3 (.step 5 (.close 31)))))) (.step 17 (.close 3))) (.step 12 (.step 17 (.close 3)))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 5 (.step 12 (.close 17))))))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 5 (.step 17 (.step 12 (.close 31)))))) (.step 3 (.step 5 (.step 12 (.close 17))))) (.step 3 (.step 5 (.step 17 (.step 12 (.close 31)))))) (.step 3 (.step 5 (.step 11 (.step 12 (.step 17 (.step 23 (.step 31 (.step 32 (.step 17 (.close 5))))))))))) (.step 3 (.step 5 (.step 17 (.close 31))))) (.step 3 (.step 5 (.step 12 (.close 17))))) (.step 3 (.step 5 (.step 11 (.step 12 (.step 17 (.step 23 (.step 31 (.step 67 (.step 69 (.step 38 (.step 74 (.split 2 0 (.split 34 0 (.split 36 0 (.step 17 (.close 5)) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 17)))))))))))))))) (.step 3 (.step 5 (.step 12 (.step 17 (.step 5 (.close 18))))))) (.step 3 (.step 5 (.step 11 (.step 12 (.step 17 (.step 23 (.step 31 (.step 32 (.step 38 (.step 74 (.step 38 (.step 3 (.close 17))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832589376755928668997108682832894707710076462020591537455646557167570371154622406493550142303538630521549672475708231706497879131967835682908788838197502738898984022354952192⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 3 := (.step 18 (.step 31 (.split 2 2 (.split 14 2 (.split 35 2 (.step 68 (.split 38 2 (.reuse 0) (.run (.step 3 (.step 5 (.step 10 (.step 18 (.step 31 (.step 41 (.step 67 (.split 63 2 (.split 71 2 (.split 64 1 (.split 65 1 (.step 31 (.step 5 (.step 59 (.split 51 1 (.step 69 (.step 31 (.step 5 (.step 12 (.step 41 (.close 5)))))) (.step 3 (.close 18)))))) (.step 3 (.step 10 (.step 16 (.step 18 (.step 21 (.step 32 (.step 41 (.step 31 (.step 24 (.step 18 (.step 22 (.close 63))))))))))))) (.step 5 (.step 18 (.step 21 (.step 31 (.step 41 (.step 66 (.step 5 (.close 67))))))))) (.step 5 (.step 18 (.step 31 (.step 59 (.step 63 (.step 66 (.step 67 (.step 5 (.step 12 (.step 41 (.close 59)))))))))))) (.step 5 (.step 12 (.step 18 (.step 31 (.step 63 (.close 66))))))))))))))))) (.reuse 1)) (.step 3 (.step 5 (.step 12 (.step 17 (.step 18 (.reuse 2))))))) (.run (.step 3 (.step 5 (.step 31 (.step 38 (.step 68 (.step 75 (.split 35 1 (.split 65 1 (.step 75 (.split 63 2 (.split 64 2 (.step 5 (.step 11 (.step 23 (.step 66 (.step 5 (.step 67 (.step 5 (.step 32 (.close 74))))))))) (.step 11 (.step 23 (.step 32 (.step 66 (.step 5 (.close 67))))))) (.step 11 (.step 12 (.step 23 (.close 66)))))) (.step 3 (.step 5 (.close 23)))) (.step 3 (.step 5 (.step 32 (.step 38 (.close 66))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case141
