module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case145
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 22062609072975435583028631289050242477408899362913360780759701718906196071722981281654683816466216116414183168122039526655296860369470163090524725501036342791423138815180716573868412475674325410892547717959917638778880⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨4294967296, 11031304536482698885562547197198468165968213701681847363918554756099838410387059583165296092749740891049045499281556738791848684124845934918408373508223893561841788234965107507935590882553449388831901510271887606808576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.split 59 1 (.split 61 1 (.split 62 1 (.step 31 (.split 69 1 (.step 3 (.step 4 (.step 12 (.close 18)))) (.step 3 (.close 4)))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 15 (.close 26))))))) (.step 3 (.step 31 (.step 21 (.step 3 (.step 4 (.close 15))))))) (.step 3 (.step 18 (.step 12 (.step 15 (.close 21))))))) (.split 59 1 (.step 3 (.split 61 1 (.split 62 1 (.step 57 (.step 3 (.close 4))) (.step 3 (.step 4 (.step 21 (.step 15 (.step 26 (.step 15 (.close 31)))))))) (.step 3 (.step 4 (.step 15 (.step 31 (.step 21 (.close 57)))))))) (.step 3 (.step 9 (.step 26 (.step 3 (.step 18 (.close 12)))))))) (.step 3 (.step 53 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.step 3 (.step 9 (.step 21 (.step 3 (.close 12))))) (.step 3 (.step 12 (.step 15 (.step 21 (.close 26)))))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 4 (.step 18 (.close 12))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 12))))))) (.step 3 (.step 52 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.step 3 (.step 9 (.step 12 (.step 3 (.close 21))))) (.step 3 (.step 12 (.step 21 (.close 26))))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 4 (.step 12 (.step 4 (.close 18)))))) (.step 3 (.step 12 (.step 4 (.close 18))))) (.step 3 (.step 12 (.close 18))))))) (.step 31 (.close 12))) (.step 31 (.close 12))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 11031304536482698885562547197198468165968213701681847363918554756099838410387059583165296092749740891049045499283850237407838755636456755813710460449022143547676766275187902214029629305945809256878391848116473405898752⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 3 (.close 12)))))) (.run (.step 3 (.step 18 (.step 3 (.close 12)))))) (.run (.step 3 (.step 18 (.step 3 (.close 12)))))) (.run (.step 12 (.step 21 (.step 22 (.step 26 (.split 36 1 (.split 42 1 (.split 54 1 (.split 59 1 (.split 50 1 (.step 3 (.step 12 (.split 61 1 (.split 62 1 (.step 15 (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 4 (.close 15)))) (.step 3 (.step 4 (.close 15)))))) (.step 3 (.step 9 (.step 12 (.step 3 (.close 15)))))) (.step 3 (.step 9 (.step 12 (.step 15 (.close 3)))))) (.step 9 (.step 12 (.step 15 (.close 3))))) (.step 9 (.step 15 (.step 3 (.step 4 (.close 15)))))) (.step 9 (.step 15 (.step 22 (.step 15 (.step 3 (.step 15 (.close 4)))))))))))))) (.run (.step 18 (.step 21 (.step 31 (.split 61 1 (.split 12 1 (.split 49 1 (.split 54 1 (.split 69 1 (.split 16 0 (.split 17 0 (.split 59 1 (.step 3 (.step 21 (.step 18 (.step 31 (.close 3))))) (.step 9 (.step 21 (.step 3 (.step 18 (.step 12 (.step 15 (.close 26)))))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 15 (.close 26))))))) (.step 9 (.step 21 (.step 32 (.step 38 (.step 3 (.close 57))))))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 32 (.step 40 (.step 38 (.step 26 (.step 3 (.close 31))))))))))) (.step 9 (.step 12 (.step 15 (.close 3))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 26 (.step 31 (.close 38)))))))))))))
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
def root : Box := ⟨16546956789305961896186184622292741386824339327255337058691808188648596662272647460385980005831425763501354680654007792449941192573506196958749334502853199842367945848531539768980266049761934732756390778196300371329024, 22062609062696711294923540506713601902656911879401738122635685755238755436184353338746707730311777649197565719596448835356815640141977050127013389619522030175439800978848581949747589939310763800942419141919561041838080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 9 (.step 26 (.step 31 (.step 71 (.split 12 1 (.split 16 1 (.split 21 1 (.split 35 1 (.step 3 (.step 18 (.split 49 1 (.split 50 1 (.split 54 1 (.split 61 1 (.split 62 1 (.split 69 1 (.step 29 (.step 75 (.split 16 0 (.split 12 0 (.step 3 (.step 26 (.step 31 (.step 26 (.step 3 (.close 4)))))) (.step 26 (.step 3 (.step 12 (.step 15 (.step 31 (.step 3 (.close 4)))))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 15)))))))) (.step 3 (.step 4 (.step 26 (.step 31 (.step 15 (.step 57 (.step 15 (.close 21))))))))) (.step 3 (.step 4 (.step 21 (.step 26 (.step 31 (.step 15 (.step 57 (.step 15 (.close 65)))))))))) (.step 3 (.step 4 (.step 15 (.step 26 (.step 31 (.step 64 (.step 21 (.step 57 (.close 71)))))))))) (.step 9 (.step 26 (.step 57 (.step 3 (.close 4)))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 32 (.step 40 (.step 3 (.step 57 (.step 3 (.close 12))))))))))) (.step 3 (.step 9 (.step 12 (.step 26 (.step 40 (.step 52 (.step 3 (.step 57 (.step 3 (.close 21))))))))))))) (.step 21 (.step 29 (.step 38 (.step 3 (.step 18 (.step 38 (.step 3 (.step 4 (.step 15 (.step 21 (.step 26 (.step 31 (.close 38)))))))))))))) (.step 3 (.step 4 (.step 9 (.step 18 (.step 26 (.step 15 (.step 31 (.close 38))))))))) (.step 3 (.step 4 (.step 18 (.close 21))))) (.step 9 (.step 12 (.step 15 (.step 18 (.step 21 (.step 26 (.step 3 (.step 4 (.step 32 (.close 38))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4294967296, 22062609062696711294923540506713601902656911879401738122635685755238755436184353338746707730311777649197565719596448835356815640141977050127013389619522030175439800978848581949747589939310763800942419141919561041838080⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 72 2 (.step 3 (.split 68 1 (.split 21 1 (.split 34 1 (.reuse 0) (.run (.step 3 (.step 31 (.close 12))))) (.run (.step 18 (.step 31 (.split 12 1 (.split 35 1 (.step 3 (.split 49 1 (.split 50 1 (.step 31 (.split 54 1 (.step 40 (.split 59 1 (.split 61 1 (.step 18 (.step 3 (.close 4))) (.step 3 (.step 4 (.step 21 (.step 4 (.step 3 (.close 5))))))) (.step 3 (.step 4 (.close 18))))) (.step 4 (.close 18)))) (.step 3 (.step 4 (.close 18)))) (.step 3 (.step 4 (.step 12 (.close 18)))))) (.step 4 (.step 3 (.step 18 (.step 15 (.close 26)))))) (.step 4 (.step 9 (.step 12 (.step 15 (.close 3)))))))))) (.run (.step 18 (.step 31 (.split 21 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 71 (.split 12 1 (.step 3 (.step 71 (.close 15))) (.step 4 (.step 3 (.step 12 (.close 15)))))) (.step 3 (.step 4 (.step 15 (.step 12 (.close 26)))))) (.step 3 (.step 4 (.step 18 (.step 15 (.step 21 (.step 12 (.close 26)))))))) (.step 3 (.step 4 (.step 12 (.step 18 (.step 26 (.step 21 (.step 26 (.close 52))))))))) (.step 4 (.step 21 (.step 29 (.step 32 (.step 38 (.step 3 (.step 21 (.step 38 (.close 3)))))))))) (.step 4 (.step 5 (.close 63))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4294967296, 22062609072970414227635207513052362432531473091449675763200852845561503378631310518637893403762808014789490866544188384841152238229117211514956294212328981755237357719327863757752445062328104809601604031590671507783680⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 62 2 (.split 69 2 (.reuse 0) (.run (.step 3 (.step 31 (.step 71 (.split 16 1 (.split 12 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 35 1 (.step 72 (.step 3 (.step 22 (.step 3 (.step 4 (.step 31 (.step 15 (.close 57)))))))) (.step 3 (.step 21 (.step 4 (.step 31 (.step 38 (.step 15 (.step 57 (.step 64 (.close 71)))))))))) (.step 3 (.close 18))) (.step 4 (.step 10 (.step 18 (.step 22 (.step 36 (.step 63 (.step 64 (.step 31 (.step 3 (.step 5 (.step 18 (.step 3 (.close 4)))))))))))))) (.step 3 (.close 18))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 64 (.step 4 (.step 15 (.step 31 (.step 57 (.close 65))))))))))) (.step 3 (.close 18)))))))) (.run (.step 3 (.step 21 (.step 65 (.step 71 (.step 65 (.step 31 (.split 16 1 (.split 17 1 (.split 12 1 (.split 21 1 (.split 54 1 (.split 72 1 (.step 65 (.step 3 (.step 18 (.step 21 (.step 3 (.step 4 (.step 15 (.close 26)))))))) (.step 3 (.step 21 (.step 26 (.step 31 (.step 64 (.step 57 (.step 15 (.close 65))))))))) (.step 3 (.step 21 (.step 57 (.step 64 (.step 4 (.step 31 (.step 57 (.close 65))))))))) (.step 4 (.step 10 (.step 18 (.step 21 (.step 32 (.step 63 (.step 64 (.step 31 (.step 3 (.step 5 (.step 22 (.step 4 (.step 3 (.close 5))))))))))))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 64 (.step 4 (.step 15 (.step 31 (.step 57 (.close 65))))))))))) (.step 3 (.close 18))) (.step 3 (.close 18)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4294967296, 22062609072970414227635207513052370930747462682318725485984252231668312451244265335196013104439323239468500696452363047664625409727662725842447210653632924154378625692087857933720321880136114746228228768591944588722176⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 59 2 (.split 61 2 (.reuse 0) (.run (.step 3 (.step 64 (.step 71 (.step 64 (.step 31 (.split 16 1 (.split 17 1 (.split 12 1 (.split 21 1 (.split 22 1 (.split 35 1 (.step 72 (.split 54 1 (.split 72 1 (.step 64 (.step 3 (.step 31 (.step 21 (.step 3 (.close 4)))))) (.step 3 (.step 4 (.step 15 (.step 26 (.step 31 (.step 21 (.step 57 (.step 21 (.step 57 (.close 64))))))))))) (.step 3 (.step 4 (.step 15 (.step 31 (.step 57 (.step 21 (.close 64))))))))) (.step 3 (.step 21 (.step 4 (.step 15 (.step 31 (.step 38 (.step 57 (.close 64))))))))) (.step 3 (.close 18))) (.step 4 (.step 10 (.step 12 (.step 18 (.step 34 (.step 63 (.step 64 (.step 3 (.step 18 (.close 4))))))))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 34 (.close 64))))))) (.step 3 (.close 18))) (.step 3 (.close 18)))))))))) (.run (.step 3 (.step 26 (.step 62 (.split 68 1 (.split 12 1 (.split 21 1 (.split 22 1 (.split 34 1 (.split 35 1 (.split 16 1 (.split 36 1 (.step 62 (.step 18 (.step 31 (.step 62 (.close 3))))) (.step 3 (.step 26 (.step 31 (.close 12))))) (.step 3 (.step 18 (.close 12)))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 31 (.step 32 (.step 55 (.step 57 (.step 3 (.step 12 (.step 15 (.close 31))))))))))))) (.step 3 (.step 15 (.step 26 (.close 31))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 4 (.step 18 (.close 12))))) (.step 9 (.step 12 (.step 15 (.step 3 (.step 4 (.close 18))))))) (.step 3 (.step 4 (.step 18 (.step 26 (.step 38 (.close 62))))))))))))
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
def root : Box := ⟨4294967296, 22062609072970414227635207513052370930747462682318725493182514302943973444956919231233610458024493827056000593505658093422532121538235585945721657529624835778903891020023063499108667710945428761733623844082863812116480⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 50 2 (.split 54 2 (.reuse 0) (.run (.step 9 (.step 12 (.step 21 (.step 15 (.step 22 (.step 26 (.step 32 (.step 57 (.step 3 (.step 31 (.split 62 2 (.split 61 2 (.split 62 1 (.step 57 (.step 3 (.step 4 (.close 57)))) (.step 3 (.step 4 (.step 21 (.step 57 (.close 64)))))) (.step 3 (.step 4 (.step 15 (.step 57 (.close 64)))))) (.step 3 (.step 4 (.step 21 (.step 64 (.step 57 (.close 65))))))))))))))))))) (.run (.step 3 (.step 21 (.step 53 (.step 57 (.step 62 (.split 72 2 (.split 68 1 (.split 12 1 (.split 16 1 (.step 52 (.split 21 1 (.split 34 1 (.split 36 1 (.split 17 1 (.split 42 1 (.split 54 1 (.step 18 (.step 53 (.close 3))) (.step 9 (.step 21 (.step 26 (.step 32 (.step 53 (.step 3 (.close 15)))))))) (.step 3 (.step 21 (.step 26 (.step 15 (.step 31 (.close 12))))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 21 (.step 31 (.close 12))))) (.step 3 (.step 15 (.step 21 (.close 31))))) (.step 3 (.step 4 (.step 18 (.close 12)))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 9 (.step 12 (.step 15 (.step 3 (.step 4 (.close 18))))))) (.step 3 (.step 4 (.step 18 (.step 52 (.step 21 (.close 53))))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 31 (.step 32 (.step 40 (.step 52 (.step 53 (.step 57 (.step 3 (.close 53)))))))))))))))))))))
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
def root : Box := ⟨6880495847970214534832462685906260822389694967504843371212766518160768628265454424210055659330381354631168, 16546956799589707539684699180622902425804660796586865242490981018584282013369526011201748024247267238688271973114792805919439583012524217366921471075323429921169127498069682510770671615269305117883878608915121982930944⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 72 1 (.split 12 1 (.step 3 (.step 18 (.split 21 1 (.split 49 1 (.split 54 1 (.split 61 1 (.split 69 1 (.step 29 (.step 38 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.step 3 (.step 21 (.step 31 (.close 3)))) (.step 21 (.step 32 (.step 15 (.step 3 (.step 12 (.step 3 (.close 26)))))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 15)))))) (.step 3 (.step 18 (.step 21 (.step 18 (.close 31)))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 15)))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 15)))))))) (.step 3 (.step 4 (.step 21 (.step 31 (.step 15 (.close 38))))))) (.step 3 (.step 4 (.step 15 (.step 21 (.step 31 (.close 38))))))) (.step 9 (.step 21 (.step 32 (.step 38 (.step 3 (.step 4 (.close 12)))))))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 32 (.step 38 (.step 3 (.close 18))))))))) (.step 4 (.step 9 (.step 18 (.step 15 (.close 31)))))))) (.step 9 (.step 12 (.step 15 (.step 3 (.step 18 (.close 26))))))) (.step 29 (.step 38 (.step 75 (.split 17 1 (.step 75 (.step 3 (.step 4 (.step 15 (.step 21 (.step 26 (.step 31 (.close 38)))))))) (.step 3 (.step 4 (.step 18 (.close 22))))))))) (.step 3 (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 32 (.step 38 (.step 40 (.step 52 (.step 57 (.split 34 0 (.step 62 (.close 3)) (.step 3 (.step 15 (.close 31)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨4936513671963618126464907547672051514948207596900739594340794368, 22062609072970414227635207513052370930747462682318725493182514302943979838297950278385700327535620443460594766639241268515429224114910540497646934291207975435148641941467260813375815218587098220799583399871149164724224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 31 (.step 57 (.split 35 2 (.split 49 2 (.split 50 2 (.split 59 2 (.step 24 (.split 72 2 (.step 24 (.split 61 2 (.split 62 2 (.step 57 (.step 71 (.split 69 2 (.split 12 1 (.split 35 1 (.split 54 1 (.split 61 1 (.step 4 (.step 3 (.step 4 (.step 18 (.close 12))))) (.step 3 (.step 4 (.step 3 (.step 4 (.close 43)))))) (.step 4 (.step 3 (.step 18 (.step 12 (.close 52)))))) (.step 4 (.step 9 (.close 18)))) (.step 4 (.step 9 (.step 12 (.close 15))))) (.step 3 (.step 4 (.step 8 (.step 22 (.step 24 (.step 43 (.step 3 (.step 12 (.step 32 (.step 64 (.step 3 (.close 65))))))))))))))) (.step 3 (.step 4 (.step 8 (.step 21 (.step 24 (.step 32 (.step 43 (.step 3 (.step 22 (.step 64 (.step 3 (.close 65))))))))))))) (.step 3 (.step 4 (.step 8 (.step 12 (.step 14 (.step 24 (.step 43 (.close 64)))))))))) (.step 4 (.step 9 (.step 15 (.step 18 (.step 26 (.step 31 (.step 38 (.close 57)))))))))) (.step 3 (.step 4 (.step 15 (.step 18 (.step 52 (.step 53 (.step 12 (.step 24 (.step 12 (.close 57))))))))))) (.step 3 (.step 4 (.step 15 (.step 18 (.step 52 (.step 53 (.close 24)))))))) (.step 3 (.step 4 (.step 12 (.step 18 (.close 52)))))) (.step 4 (.step 9 (.step 15 (.step 18 (.step 31 (.step 38 (.close 24)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4294967296, 22062609072975430684145320631707805529558497961273756258527919093688282855821781390440808474987129601152815062021957431167307751010159925789938750815584744178506710662046738553243414174629697756249399965274706464997376⟩
def references : Fin 3 → Box := ![Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 3 := (.step 18 (.step 71 (.split 21 2 (.split 35 2 (.split 49 2 (.reuse 0) (.run (.step 3 (.step 12 (.step 52 (.step 57 (.step 62 (.split 72 2 (.split 68 1 (.split 16 1 (.step 52 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 17 1 (.split 42 1 (.split 54 1 (.step 18 (.step 52 (.step 3 (.step 12 (.close 18))))) (.step 9 (.step 12 (.step 18 (.step 52 (.close 3)))))) (.step 3 (.step 26 (.step 31 (.close 12))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 31 (.close 12)))) (.step 9 (.step 12 (.step 18 (.step 21 (.step 31 (.step 32 (.step 52 (.step 3 (.step 18 (.close 26))))))))))) (.step 3 (.step 15 (.close 31)))) (.step 3 (.step 4 (.step 12 (.close 18)))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 4 (.step 12 (.step 18 (.step 38 (.close 52))))))) (.step 9 (.step 12 (.step 18 (.step 26 (.step 31 (.step 38 (.step 40 (.step 52 (.step 57 (.step 3 (.step 52 (.close 71)))))))))))))))))))) (.step 9 (.step 21 (.step 31 (.step 38 (.step 57 (.step 62 (.step 71 (.split 49 2 (.reuse 1) (.run (.step 3 (.step 9 (.step 12 (.step 18 (.step 21 (.step 32 (.step 38 (.step 40 (.step 52 (.step 57 (.step 52 (.step 3 (.close 26))))))))))))))))))))))) (.reuse 2))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4294967296, 22062609072975435583028631289050242477408899362913360780759701718906196071722981281654683816466216116414183168122039526655296860369470163090524725501036342791423138815180716573868412475674325410892547717959917638778880⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.split 12 2 (.reuse 0) (.run (.step 9 (.step 12 (.step 15 (.step 18 (.step 9 (.step 21 (.step 15 (.step 3 (.step 22 (.step 24 (.step 26 (.step 31 (.step 71 (.split 62 2 (.split 61 2 (.split 62 1 (.step 15 (.step 3 (.step 4 (.step 15 (.close 71))))) (.step 3 (.step 4 (.step 15 (.step 64 (.close 65)))))) (.step 3 (.step 4 (.step 15 (.close 64))))) (.step 3 (.step 4 (.step 21 (.step 64 (.step 15 (.step 57 (.close 65)))))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case145
