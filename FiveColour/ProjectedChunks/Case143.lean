module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case143
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 23134322349737717735021796285272283483885134813317202352766244487352153458927202491314932076713772185564659526219838426654130820177421794578697792322685594472097454233382586607716314808008272834562903889688012443037042999296⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨18740915245514456087539, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475066830037980738387460577625234839625950792211697196357563187971868412046230991680761629786926547894765880320, 0⟩]
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
def root : Box := ⟨4294967296, 11567161174868858867508448700980813070724093481457900356577175617604274330753607623500358629022304844966269595465589117915469458866855971814769142062760224324035345236387619860252481314366270288820615852500921459653559189504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 59 1 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 39 1 (.step 31 (.step 27 (.step 5 (.step 31 (.close 3))))) (.step 27 (.step 32 (.step 31 (.step 5 (.step 31 (.step 17 (.step 5 (.close 3))))))))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 18 (.close 17)))) (.step 18 (.step 3 (.step 18 (.close 17))))) (.step 18 (.step 3 (.step 18 (.close 17))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 42 (.split 58 1 (.step 5 (.step 3 (.close 5))) (.step 27 (.step 31 (.step 5 (.step 44 (.step 5 (.close 3)))))))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18))))) (.step 44 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 62 (.step 27 (.step 32 (.step 31 (.step 42 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 17 (.close 23))))))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.step 17 (.step 18 (.close 17))))) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 17 (.close 23))))))))) (.step 61 (.step 31 (.step 5 (.step 3 (.step 5 (.step 3 (.close 17)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 11567161174868858867508448700980813070724093481457900356577175617604274334030194901912024075080432005042425114837579035501724881038806253783140740823860409123774074977949696720879328194400622753689546859086360212811342151680⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 32 (.split 56 1 (.split 2 0 (.split 16 0 (.split 74 1 (.split 17 0 (.step 62 (.split 22 0 (.split 34 0 (.split 36 0 (.step 32 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 21 (.step 5 (.close 17)))))) (.step 3 (.step 21 (.step 5 (.close 17))))) (.step 3 (.close 17)))) (.step 3 (.step 17 (.step 18 (.close 17))))) (.step 27 (.step 32 (.step 44 (.step 3 (.step 5 (.close 17))))))) (.step 3 (.step 18 (.step 17 (.close 32))))) (.step 3 (.step 21 (.step 5 (.step 22 (.step 23 (.close 5))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 22 (.step 5 (.step 17 (.close 23)))))))))))) (.run (.split 56 1 (.split 2 0 (.split 16 0 (.split 17 0 (.step 52 (.split 74 1 (.split 22 0 (.split 34 0 (.split 36 0 (.step 12 (.split 38 0 (.step 52 (.step 27 (.step 32 (.step 31 (.step 34 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 17 (.close 23)))))))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 31 (.close 17)))) (.step 3 (.step 17 (.close 18)))) (.step 12 (.step 27 (.step 23 (.step 34 (.step 31 (.step 23 (.step 32 (.step 3 (.close 18))))))))))) (.step 3 (.step 34 (.step 42 (.step 18 (.step 32 (.step 18 (.close 44)))))))) (.step 3 (.step 34 (.step 42 (.step 18 (.close 44)))))) (.step 3 (.step 23 (.step 34 (.step 42 (.step 5 (.step 21 (.step 5 (.step 22 (.step 23 (.close 31))))))))))) (.step 3 (.step 5 (.step 22 (.step 31 (.step 5 (.close 21))))))))) (.run (.step 3 (.step 31 (.close 21)))))
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
def root : Box := ⟨4294967296, 11567161174868858867513347584291470413161041331859301996181697849386899551943410803111915288955770776446274463688136124403029536737179494081102188324273832572513316698262847796165167464709830911069949759225862438013170089984⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.step 3 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 40 1 (.reuse 0) (.run (.step 31 (.step 43 (.split 49 1 (.split 50 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 5 (.step 31 (.step 5 (.step 3 (.step 17 (.close 21)))))) (.step 3 (.step 5 (.step 23 (.close 31))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.step 23 (.close 31))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 22 (.close 31))))))) (.step 3 (.step 5 (.step 23 (.step 31 (.close 21)))))))))) (.run (.step 21 (.step 31 (.step 43 (.split 49 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 58 (.split 34 0 (.step 42 (.step 5 (.step 31 (.step 3 (.close 5))))) (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 5 (.step 31 (.close 5)))))))) (.step 3 (.step 5 (.step 21 (.step 31 (.close 5))))))))))) (.run (.step 31 (.close 21)))) (.run (.step 31 (.close 21)))) (.run (.step 3 (.step 18 (.step 3 (.close 32)))))) (.run (.step 3 (.step 18 (.step 3 (.close 32)))))) (.run (.step 3 (.step 18 (.step 3 (.close 32)))))))
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
def root : Box := ⟨4294967296, 11567161174868858867513347584291470413161041331859301996189068869747879124897007589402908001633342888204900323899808402333196771429351659807832904584386447352867747118244808430735033281611727679844367656480583962996016939008⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 14 1 (.reuse 0) (.run (.step 18 (.step 31 (.step 34 (.split 38 1 (.step 27 (.split 40 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 74 1 (.split 2 0 (.split 34 0 (.split 39 1 (.split 36 0 (.split 50 1 (.split 38 0 (.step 61 (.step 18 (.step 27 (.step 23 (.step 3 (.close 17)))))) (.step 12 (.step 18 (.step 5 (.close 23))))) (.step 12 (.step 27 (.step 32 (.step 34 (.step 18 (.step 23 (.step 3 (.close 18))))))))) (.step 3 (.step 18 (.step 23 (.close 5))))) (.step 11 (.step 12 (.step 32 (.step 34 (.step 18 (.step 31 (.step 5 (.step 23 (.step 3 (.close 18))))))))))) (.step 3 (.step 18 (.step 23 (.step 5 (.close 17)))))) (.step 11 (.step 12 (.step 31 (.step 34 (.step 23 (.step 5 (.step 18 (.close 5))))))))) (.step 11 (.step 17 (.step 3 (.close 5))))) (.step 3 (.close 17))) (.step 3 (.step 5 (.step 17 (.step 18 (.step 21 (.close 23))))))) (.step 3 (.close 17))) (.step 3 (.step 5 (.step 11 (.step 12 (.step 17 (.step 3 (.step 18 (.step 23 (.close 17))))))))))) (.step 3 (.step 5 (.step 17 (.step 18 (.step 21 (.step 17 (.close 23))))))))))))) (.run (.step 12 (.step 18 (.step 31 (.step 58 (.split 14 1 (.split 39 1 (.step 3 (.step 58 (.step 48 (.step 3 (.step 27 (.step 32 (.step 3 (.step 44 (.close 52))))))))) (.step 27 (.step 32 (.step 42 (.close 3))))) (.step 8 (.step 12 (.step 18 (.step 17 (.step 34 (.step 32 (.step 42 (.step 32 (.close 44))))))))))))))))
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
def root : Box := ⟨17350741762303288301255324726505233592430718434416092311654821463220390893739203583421689370594693101389196485621456874975989535943956833982217542175663796877910811186069807844798251453395170474334765216637959354571370266624, 23134322349737717735016897401961626141448186954803363537292283178561473054056476645017367582029804955797697980980779652317189795391989549129311266034828978604808287908958013660600534250541841329400877800905890199374069235712⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 5 (.step 18 (.step 27 (.step 44 (.step 58 (.split 2 1 (.split 14 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 40 1 (.split 42 1 (.split 51 1 (.step 11 (.split 55 1 (.split 56 1 (.split 67 1 (.split 2 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 1 (.split 49 1 (.step 77 (.step 3 (.step 18 (.step 5 (.close 21))))) (.step 12 (.step 17 (.step 23 (.step 44 (.step 52 (.step 18 (.step 55 (.step 61 (.close 3)))))))))) (.step 32 (.step 42 (.close 3)))) (.step 18 (.step 23 (.step 5 (.close 42))))) (.step 18 (.step 23 (.step 5 (.step 31 (.close 42)))))) (.step 17 (.step 18 (.step 23 (.step 5 (.close 31)))))) (.step 23 (.step 77 (.close 5)))) (.step 3 (.step 18 (.close 42)))) (.step 3 (.step 5 (.step 18 (.step 23 (.close 42)))))) (.step 5 (.step 18 (.step 42 (.step 44 (.step 48 (.step 58 (.step 17 (.close 32)))))))))) (.step 3 (.step 18 (.close 42)))) (.step 3 (.step 5 (.step 23 (.step 31 (.close 42)))))) (.step 3 (.step 5 (.step 11 (.step 18 (.step 23 (.step 31 (.close 42)))))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 23 (.close 42))))))) (.step 3 (.step 5 (.step 23 (.step 31 (.close 36)))))) (.step 3 (.step 5 (.step 17 (.step 23 (.close 31)))))) (.step 11 (.step 17 (.step 3 (.step 5 (.step 3 (.close 17))))))) (.step 3 (.step 5 (.step 17 (.step 23 (.step 18 (.step 42 (.step 18 (.step 44 (.close 61))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨12156783893206034058141819913157698684606776071022764355456027333078084408436254335155391744962218147328704745931545280807798294166245435472324828615568252989437056064657154899968, 23134322349737717735016897401961626141448186962907886132762972550656019662828275768088551629378314526101716203032835924608026018828917379104123364253965475892505141780823543104764157898758393739779713127197260909142642524160⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 44 (.step 58 (.split 2 1 (.split 14 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 17 1 (.step 62 (.split 22 1 (.split 40 1 (.split 42 1 (.split 55 1 (.split 56 1 (.split 39 1 (.split 58 1 (.split 2 0 (.split 16 0 (.split 17 0 (.step 62 (.close 3)) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 31 (.step 44 (.step 5 (.close 21)))))) (.step 27 (.step 44 (.step 61 (.step 3 (.close 5)))))) (.step 27 (.step 32 (.step 42 (.step 3 (.close 5)))))) (.step 3 (.step 5 (.step 22 (.step 31 (.step 5 (.step 21 (.close 42)))))))) (.step 48 (.step 58 (.close 62)))) (.step 3 (.step 31 (.step 21 (.close 42))))) (.step 3 (.step 5 (.step 31 (.step 21 (.close 42)))))) (.step 3 (.step 18 (.step 32 (.close 42)))))) (.step 3 (.step 18 (.step 32 (.step 42 (.step 52 (.step 32 (.close 53)))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 31 (.step 5 (.step 42 (.step 52 (.close 58)))))))))) (.step 3 (.step 22 (.step 31 (.close 21))))) (.step 3 (.step 31 (.step 21 (.close 34))))) (.step 3 (.step 18 (.step 32 (.step 42 (.step 52 (.close 53))))))) (.step 12 (.step 18 (.step 23 (.step 27 (.step 31 (.step 34 (.step 42 (.step 44 (.step 48 (.step 53 (.step 23 (.step 55 (.step 17 (.step 18 (.close 32)))))))))))))))) (.step 3 (.step 5 (.step 23 (.step 42 (.step 44 (.step 52 (.step 5 (.step 53 (.step 5 (.step 21 (.close 34))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨11321887274464624056724663742964806672750763661249321285128618900736872487176446556258380175532976302624405125092291534699311753889774377897684302754298088130952480948224, 23134322349737717735016897401961626141448186962915800713158036745389038447984013640146213614383395745811847077580221236302683363362665208110336592048950136461074408301210476585403143197326940481865842211435984413150191550464⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 5 (.step 18 (.step 31 (.step 43 (.step 58 (.split 14 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 74 1 (.split 2 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 1 (.step 5 (.step 58 (.split 34 0 (.step 43 (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 5 (.step 16 (.close 21))))))) (.step 28 (.step 41 (.step 43 (.step 59 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 3 (.close 31))))) (.step 3 (.step 5 (.step 18 (.step 5 (.step 3 (.close 31))))))) (.step 3 (.step 5 (.step 18 (.step 5 (.step 3 (.close 31))))))) (.step 5 (.step 18 (.step 5 (.step 16 (.close 31)))))) (.step 5 (.close 31))) (.step 5 (.close 31))) (.step 3 (.step 5 (.step 22 (.step 31 (.step 21 (.close 41))))))) (.step 3 (.step 5 (.step 21 (.step 22 (.step 16 (.step 31 (.close 53)))))))) (.step 3 (.step 5 (.step 16 (.step 22 (.step 31 (.step 21 (.step 52 (.step 21 (.step 41 (.close 58))))))))))) (.step 5 (.close 31))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨9820171823688425610039569090482797456649926138129194368449874104288401389214023664649810276977712471452660052382680213027651769637656179159989877735424, 11567161174868858867508448700980813070724093481457900356580861127784764127053774510849804171445597454579516077526391954440746929240317369212974104070377559967090935989314040546838483445123640006335966974288737839376959012864⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 1 (.split 14 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 17 1 (.step 62 (.split 22 1 (.split 40 1 (.split 42 1 (.split 55 1 (.split 56 1 (.step 52 (.split 58 1 (.split 74 1 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 53 (.step 3 (.close 5))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 21 (.step 5 (.step 17 (.close 23)))))) (.step 27 (.step 32 (.step 44 (.step 31 (.close 53)))))) (.step 27 (.step 32 (.step 53 (.step 3 (.step 18 (.close 5)))))))) (.step 3 (.step 5 (.step 21 (.step 22 (.step 31 (.step 5 (.close 52)))))))) (.step 32 (.step 48 (.step 52 (.step 53 (.close 5)))))) (.step 3 (.step 21 (.step 23 (.step 31 (.close 44)))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.step 5 (.close 52)))))))) (.step 3 (.step 18 (.step 32 (.close 52)))))) (.step 3 (.step 18 (.step 32 (.step 52 (.step 32 (.close 53))))))) (.step 3 (.step 21 (.step 22 (.step 23 (.close 31)))))) (.step 3 (.step 21 (.step 23 (.step 31 (.close 34)))))) (.step 3 (.step 18 (.step 32 (.step 42 (.step 52 (.close 53))))))) (.step 12 (.step 18 (.step 23 (.step 27 (.step 31 (.step 32 (.step 34 (.step 48 (.step 53 (.step 55 (.step 23 (.step 53 (.close 17)))))))))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 52 (.step 5 (.step 53 (.close 5))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨9590011546570728134804266689924606891259693494266791375439330179969141981654319985009580348611047335402988332404961145534816181286773612465218387968, 11567161174868858867508448700980813070724093481457900356580861127784764120513386636088567583509087572050936701878302947872119747816700601924278660502928344383234303674125967293551425891198357569859338555634981275110221021184⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 2 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 17 1 (.step 62 (.split 22 1 (.split 40 1 (.split 42 1 (.split 55 1 (.split 56 1 (.step 52 (.split 39 1 (.split 58 1 (.split 74 1 (.split 2 0 (.split 16 0 (.split 17 0 (.step 52 (.close 3)) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 18 (.close 17)))) (.step 3 (.step 31 (.step 34 (.step 5 (.close 21)))))) (.step 12 (.step 27 (.step 34 (.step 44 (.step 31 (.step 52 (.close 3)))))))) (.step 12 (.step 27 (.step 34 (.step 52 (.step 58 (.step 18 (.close 5)))))))) (.step 12 (.step 27 (.step 32 (.step 34 (.step 42 (.step 3 (.close 5))))))))) (.step 3 (.step 5 (.step 22 (.step 31 (.step 52 (.close 5))))))) (.step 12 (.step 48 (.step 52 (.close 5))))) (.step 3 (.step 23 (.step 31 (.step 21 (.step 42 (.step 21 (.close 44)))))))) (.step 3 (.step 5 (.step 23 (.step 31 (.step 42 (.step 5 (.step 21 (.step 5 (.close 52)))))))))) (.step 3 (.step 18 (.step 32 (.step 42 (.step 32 (.close 52)))))))) (.step 3 (.step 18 (.step 32 (.step 42 (.close 52)))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 31 (.step 5 (.step 42 (.close 52))))))))) (.step 3 (.step 22 (.step 23 (.step 31 (.close 21)))))) (.step 3 (.step 16 (.step 17 (.step 31 (.step 21 (.close 34))))))) (.step 3 (.step 18 (.step 32 (.step 42 (.close 52)))))) (.step 3 (.step 5 (.step 23 (.step 34 (.step 42 (.step 52 (.close 5)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4294967296, 23134322349737717735016897401961626141448186962915800713158036745389038454537188196969544506499644650593661786607678457384990803246207497755916946179402126217620979852092822444111837007383723263990232757397952928114529009664⟩
def references : Fin 6 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 6 := (.split 49 2 (.split 50 2 (.split 56 2 (.split 58 2 (.split 59 2 (.split 74 2 (.split 2 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 31 (.step 5 (.step 58 (.step 5 (.split 16 1 (.split 17 1 (.split 22 1 (.split 14 1 (.step 3 (.step 42 (.step 23 (.step 61 (.step 3 (.step 17 (.step 21 (.step 17 (.close 23))))))))) (.step 5 (.step 17 (.step 23 (.close 17))))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.step 17 (.close 18)))))))))))) (.reuse 1)) (.reuse 2)) (.run (.step 5 (.step 12 (.step 27 (.step 32 (.step 34 (.step 36 (.step 44 (.step 42 (.step 27 (.step 58 (.step 61 (.close 3)))))))))))))) (.reuse 3)) (.step 3 (.step 21 (.step 32 (.step 53 (.step 58 (.step 53 (.step 61 (.split 74 2 (.reuse 4) (.run (.step 5 (.step 11 (.step 17 (.step 18 (.step 23 (.step 32 (.step 44 (.step 48 (.step 52 (.step 53 (.step 18 (.step 55 (.close 61))))))))))))))))))))))) (.step 3 (.step 34 (.step 52 (.step 58 (.step 52 (.step 61 (.split 74 2 (.reuse 5) (.run (.step 5 (.step 11 (.step 12 (.step 17 (.step 18 (.step 23 (.step 42 (.step 44 (.step 48 (.step 52 (.step 18 (.step 42 (.step 55 (.close 61)))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4294967296, 23134322349737717735016897401961626141448186962915800713158036745389038454537188196969544506499647358284079494678909068647566034112931170723879061285157202702591793729956121897676292324596142550061494067455499278093036552192⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 39 2 (.step 31 (.split 40 2 (.reuse 0) (.run (.step 5 (.step 12 (.step 31 (.step 5 (.step 43 (.step 3 (.step 18 (.step 61 (.split 49 2 (.split 50 2 (.split 59 2 (.step 43 (.step 27 (.step 42 (.step 61 (.step 77 (.split 74 1 (.step 3 (.step 31 (.step 21 (.step 31 (.close 17))))) (.step 17 (.step 3 (.step 18 (.close 23)))))))))) (.step 3 (.step 5 (.step 23 (.step 31 (.step 42 (.step 52 (.step 53 (.step 21 (.step 43 (.step 21 (.close 61)))))))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.step 52 (.close 53)))))))) (.step 3 (.step 5 (.step 23 (.step 31 (.step 42 (.step 52 (.close 43))))))))))))))))))) (.run (.step 5 (.step 12 (.step 27 (.step 32 (.step 34 (.step 36 (.step 42 (.step 31 (.step 43 (.step 44 (.step 42 (.step 3 (.close 5)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4181389724724491839037947176121572077338624, 11567161174868858867513347584291470413161041339963824591656072731661935947188811648813072116595358977374758848567450465566373282530278167955600818744487672740226824334459395824523398873561100151987387750352608741967066562560⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 2 (.split 40 1 (.split 2 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 39 1 (.split 42 1 (.split 50 1 (.split 51 1 (.step 11 (.step 77 (.split 55 1 (.split 56 1 (.split 67 1 (.split 59 1 (.split 2 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 17 (.step 3 (.close 5))) (.step 12 (.step 18 (.step 17 (.close 5))))) (.step 17 (.step 3 (.close 17)))) (.step 17 (.close 3))) (.step 12 (.step 17 (.step 5 (.close 3))))) (.step 12 (.step 23 (.step 17 (.step 3 (.close 18)))))) (.step 3 (.close 17))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 5 (.step 12 (.step 18 (.step 34 (.step 48 (.step 17 (.step 5 (.step 17 (.close 21)))))))))))) (.step 3 (.close 17))) (.step 3 (.step 11 (.step 12 (.step 17 (.step 23 (.step 32 (.step 34 (.step 48 (.step 17 (.step 44 (.step 17 (.close 18))))))))))))) (.step 3 (.step 5 (.close 17)))) (.step 11 (.step 12 (.step 17 (.step 31 (.step 17 (.step 32 (.close 42)))))))) (.step 3 (.step 5 (.step 17 (.step 21 (.close 23)))))) (.step 3 (.step 5 (.step 17 (.close 23))))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.step 17 (.step 21 (.close 23)))))) (.step 3 (.step 5 (.step 11 (.step 12 (.step 17 (.step 18 (.step 23 (.step 17 (.close 31)))))))))) (.step 3 (.step 11 (.step 12 (.step 17 (.step 23 (.step 34 (.step 42 (.step 44 (.step 48 (.step 53 (.step 55 (.step 17 (.step 32 (.close 61))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨4294967296, 23134322349737717735021796285272283483885134813317202352766244487352153458927202491314932076713772185564659526219838426654130820177421794578697792322685594472097454233382586607716314808008272834562903889688012443037042999296⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.step 3 (.step 5 (.step 18 (.step 58 (.split 14 2 (.split 38 2 (.reuse 0) (.run (.step 5 (.step 10 (.step 21 (.step 31 (.step 41 (.step 43 (.step 3 (.step 18 (.step 58 (.split 14 1 (.split 49 1 (.split 59 1 (.split 74 1 (.split 56 1 (.step 5 (.step 58 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 43 (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 5 (.step 16 (.close 21))))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.step 28 (.step 41 (.step 43 (.split 14 0 (.split 16 0 (.step 59 (.step 3 (.close 5))) (.step 3 (.step 18 (.step 31 (.close 5))))) (.step 18 (.step 31 (.close 5)))))))) (.step 5 (.close 31))) (.step 3 (.step 5 (.step 21 (.step 31 (.close 41)))))) (.step 3 (.step 5 (.step 16 (.step 21 (.step 31 (.close 41))))))) (.step 5 (.close 31)))))))))))))) (.step 5 (.step 17 (.step 18 (.step 27 (.step 31 (.step 34 (.step 42 (.step 43 (.step 58 (.step 61 (.split 50 2 (.reuse 1) (.run (.step 3 (.step 11 (.step 12 (.step 17 (.step 21 (.step 23 (.step 32 (.step 34 (.step 48 (.step 53 (.step 55 (.step 61 (.step 17 (.close 3)))))))))))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case143
