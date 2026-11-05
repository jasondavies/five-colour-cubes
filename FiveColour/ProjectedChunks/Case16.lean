module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case16
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721538116913463296⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37630511536740859966407, 5789234131004108975754332037409142809267054969284561340134967070491198656929520178649377157723386516549331769084384324871873123416508784820466354286493168996104550163977995004790153775060025742547153916698520434934706865153, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333611306390233521696777233527924167357481041907833778309934839822358960865713813468870352156521784329433324376784115671543847936941975259849651677941092067123273715832324096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 52 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 25 0 (.step 7 (.step 3 (.step 16 (.close 21)))) (.step 3 (.split 34 0 (.split 36 0 (.split 42 0 (.step 3 (.step 4 (.close 7))) (.step 7 (.close 21))) (.step 7 (.step 21 (.close 22)))) (.step 7 (.step 16 (.close 21)))))) (.step 7 (.step 3 (.close 18)))) (.step 3 (.step 7 (.step 3 (.close 17))))) (.split 11 0 (.step 3 (.step 7 (.step 3 (.close 8)))) (.split 16 0 (.split 25 0 (.step 3 (.split 4 0 (.split 10 0 (.step 8 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 3 (.close 4))) (.step 7 (.close 8))))) (.step 7 (.close 3))) (.step 55 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 48 (.step 7 (.step 58 (.step 5 (.step 7 (.close 16)))))) (.step 7 (.close 3))) (.step 3 (.step 27 (.close 48)))) (.step 7 (.close 3))) (.step 7 (.close 3))))) (.step 3 (.close 60))) (.split 57 1 (.split 59 1 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 28 (.step 3 (.split 16 0 (.step 55 (.step 3 (.step 4 (.close 7)))) (.step 3 (.close 4))))) (.step 3 (.close 7))) (.step 3 (.step 10 (.step 8 (.close 3))))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 5 (.step 10 (.step 26 (.step 22 (.step 28 (.step 26 (.step 48 (.close 7))))))))) (.step 3 (.step 28 (.step 3 (.step 51 (.close 60))))))) (.step 3 (.step 55 (.step 3 (.step 48 (.step 3 (.close 16))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 9797766621314684873895708907333611310075747216966320922571584929003810029806465188704760677128061677323842636205361652263093392555032085063365525799315256511304250891752885526058032269070162737647058944⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.step 58 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.step 55 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 48 (.step 7 (.step 50 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.step 27 (.close 48)))) (.step 7 (.close 3))) (.step 7 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 5 0 (.split 11 0 (.step 53 (.step 55 (.step 7 (.step 5 (.step 7 (.step 3 (.close 16))))))) (.step 27 (.step 3 (.step 48 (.close 7))))) (.step 9 (.step 27 (.close 48)))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7)))))) (.step 3 (.step 48 (.close 3)))) (.step 5 (.step 48 (.step 7 (.step 9 (.step 7 (.step 16 (.step 7 (.close 21))))))))) (.step 3 (.step 4 (.step 35 (.close 48))))) (.step 3 (.step 7 (.step 3 (.step 48 (.step 9 (.step 21 (.close 26)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320922571584929003810029806465188704760677128061677323842636205361652263093392555032085063365525799315256511304250891752885526058032269070162737647058944⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 50 1 (.split 51 1 (.split 53 1 (.split 55 1 (.reuse 0) (.run (.step 48 (.step 58 (.step 3 (.step 5 (.close 28))))))) (.run (.split 52 1 (.split 55 1 (.split 67 1 (.split 4 0 (.split 56 1 (.split 57 1 (.split 59 1 (.split 10 0 (.split 11 0 (.split 25 0 (.step 3 (.step 8 (.step 7 (.step 3 (.close 18))))) (.step 3 (.close 8))) (.step 8 (.step 56 (.close 3)))) (.step 3 (.close 7))) (.step 4 (.step 8 (.step 36 (.step 44 (.close 48)))))) (.step 8 (.step 3 (.step 51 (.close 60))))) (.step 3 (.step 24 (.step 43 (.step 8 (.step 3 (.step 28 (.step 3 (.step 14 (.step 3 (.close 19))))))))))) (.step 3 (.step 48 (.step 7 (.step 3 (.close 8)))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 5 (.step 18 (.step 3 (.step 8 (.step 3 (.step 34 (.close 48))))))))) (.step 3 (.step 8 (.step 18 (.close 48))))))) (.run (.step 3 (.step 7 (.step 3 (.step 48 (.close 54))))))) (.reuse 1))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 9797766621314684873895708907333611310075747213533918822312342690894565662010827315779093107500927427650751881800998691086849622370637376465739371943525728396542471781441264153881891572981299417203081216⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.step 55 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 48 (.step 7 (.step 49 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.step 27 (.close 48)))) (.step 7 (.close 3))) (.step 7 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 5 0 (.split 11 0 (.step 52 (.step 55 (.step 7 (.step 5 (.step 7 (.step 3 (.close 16))))))) (.step 27 (.step 3 (.step 48 (.close 7))))) (.step 9 (.step 27 (.close 48)))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7)))))) (.step 3 (.step 48 (.close 3)))) (.step 5 (.step 16 (.step 48 (.step 7 (.step 9 (.close 21))))))) (.step 3 (.step 4 (.step 48 (.close 8))))) (.step 3 (.step 7 (.step 3 (.step 48 (.step 9 (.step 21 (.close 26))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496087086157417190034294038011212863205740661804321282664727926293102459295356400268016838351643920678665443979118918195516332844467059949568⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 46 1 (.split 47 1 (.split 49 1 (.reuse 0) (.step 55 (.split 50 1 (.reuse 1) (.run (.step 55 (.split 55 1 (.split 56 1 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 1 (.split 5 0 (.split 11 0 (.step 52 (.close 3)) (.step 27 (.step 48 (.close 7)))) (.step 9 (.step 27 (.close 48)))) (.step 3 (.step 4 (.step 27 (.step 34 (.close 48)))))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 27 (.step 7 (.step 48 (.close 7))))) (.step 48 (.step 52 (.step 55 (.close 7))))) (.step 48 (.step 52 (.step 55 (.close 7))))) (.step 3 (.step 5 (.step 9 (.step 16 (.step 21 (.step 48 (.step 7 (.close 26))))))))) (.step 48 (.close 52)))))))) (.run (.step 3 (.split 52 1 (.split 55 1 (.split 4 0 (.step 50 (.split 10 0 (.step 49 (.step 50 (.step 3 (.step 50 (.close 16))))) (.step 3 (.step 48 (.step 3 (.close 49)))))) (.step 3 (.step 48 (.step 3 (.close 50))))) (.step 48 (.step 50 (.step 3 (.close 16))))) (.step 48 (.step 3 (.close 50))))))) (.run (.step 3 (.split 52 1 (.split 55 1 (.split 4 0 (.step 49 (.split 10 0 (.step 49 (.step 50 (.step 60 (.step 49 (.step 3 (.close 49)))))) (.step 3 (.step 48 (.step 3 (.close 49)))))) (.step 3 (.step 48 (.step 49 (.close 3))))) (.step 48 (.step 49 (.close 3)))) (.step 48 (.step 3 (.close 49)))))))
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
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225215024284136453122862303379606157926290524943851354588919133636672670159250114037787681109470204793925050378162798592⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 28)))))) (.step 3 (.step 7 (.step 4 (.step 10 (.step 8 (.close 28))))))) (.step 7 (.step 28 (.close 31)))) (.step 28 (.step 31 (.step 3 (.step 8 (.close 37)))))) (.step 5 (.step 7 (.step 28 (.step 31 (.close 16)))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.step 14 (.close 37))))))))) (.step 3 (.step 28 (.step 31 (.close 16))))) (.step 5 (.step 7 (.step 28 (.step 21 (.step 31 (.close 16))))))) (.step 5 (.step 7 (.step 16 (.step 28 (.step 31 (.step 21 (.close 22)))))))) (.step 28 (.step 31 (.step 50 (.step 3 (.close 21)))))) (.step 28 (.step 31 (.step 49 (.step 3 (.step 21 (.close 22))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 9797766621314684873895708907333611310075747216966320925768258493109954742702384210604010156728983907683097558386034148790805254742265175334339120841097573277955832704223904011292861007802666610503712768⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 47 1 (.split 49 1 (.split 51 1 (.split 52 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 16 0 (.split 50 1 (.step 59 (.split 55 1 (.split 57 1 (.split 53 1 (.split 5 0 (.step 28 (.step 3 (.step 58 (.step 55 (.step 3 (.step 4 (.close 7))))))) (.step 3 (.step 5 (.step 3 (.step 10 (.step 3 (.close 8))))))) (.step 3 (.step 8 (.step 24 (.step 3 (.step 14 (.step 3 (.close 5)))))))) (.step 28 (.step 3 (.close 60)))) (.step 5 (.step 28 (.step 48 (.step 41 (.step 3 (.step 21 (.step 16 (.close 22)))))))))) (.step 3 (.step 5 (.step 10 (.step 21 (.step 3 (.close 16))))))) (.step 3 (.step 5 (.step 41 (.step 43 (.step 50 (.step 3 (.step 8 (.close 19))))))))) (.step 3 (.step 58 (.split 53 1 (.split 57 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 16))))) (.step 3 (.step 28 (.step 3 (.close 16))))) (.step 3 (.step 8 (.close 14))))))) (.step 3 (.step 58 (.split 53 1 (.split 57 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 16))))) (.step 3 (.step 28 (.step 3 (.close 16))))) (.step 3 (.step 8 (.close 28))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 21 (.step 28 (.step 41 (.step 21 (.step 31 (.close 48)))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 5 (.step 48 (.step 5 (.step 16 (.step 48 (.step 9 (.close 58))))))))) (.step 3 (.step 21 (.step 28 (.step 41 (.step 50 (.close 3))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 4898883310657342436947858505931971705553515434341103012552357296195872284853796012395921219212488485396954387642254928756641114756097356211168106773234288487593865050520345977789387190340105437207068672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.step 22 (.step 16 (.close 21)))) (.step 28 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 28)))))) (.step 3 (.step 7 (.step 4 (.step 10 (.step 8 (.close 28))))))) (.step 7 (.step 22 (.step 28 (.close 31))))) (.step 28 (.step 31 (.step 3 (.step 8 (.close 37)))))) (.step 5 (.step 7 (.step 28 (.step 31 (.close 16)))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.step 14 (.close 37))))))))) (.step 3 (.step 28 (.step 31 (.close 16))))) (.step 5 (.step 7 (.step 22 (.step 21 (.step 28 (.close 31))))))) (.step 5 (.step 7 (.step 16 (.step 22 (.step 28 (.close 31))))))) (.step 28 (.step 31 (.step 50 (.step 3 (.close 21)))))) (.step 28 (.step 31 (.step 49 (.step 3 (.step 21 (.close 22))))))) (.step 39 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.step 45 (.step 3 (.close 31))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.step 14 (.close 37))))))))) (.step 3 (.step 28 (.step 31 (.close 16))))) (.step 5 (.step 7 (.step 22 (.step 21 (.step 29 (.close 31))))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22)))))))) (.step 28 (.step 31 (.step 39 (.step 3 (.close 8)))))) (.step 28 (.step 31 (.step 37 (.step 39 (.step 3 (.close 8))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872270360586904047501897498942679454931441228244200275717726488393041638565502944574834099537369495444127744⟩
def references : Fin 4 → Box := ![Part4.root, Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 4 := (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 45 1 (.reuse 0) (.run (.step 48 (.split 46 1 (.split 47 1 (.split 49 1 (.step 48 (.step 31 (.step 3 (.step 4 (.step 8 (.close 3)))))) (.step 48 (.close 52))) (.step 3 (.step 48 (.step 4 (.step 8 (.close 17)))))) (.step 3 (.step 48 (.close 49))))))) (.run (.step 3 (.split 45 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 5 0 (.step 54 (.split 11 0 (.split 25 0 (.step 70 (.step 7 (.step 3 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.step 8 (.step 27 (.close 46))))))))) (.reuse 1)) (.split 42 1 (.split 43 1 (.split 45 1 (.split 46 1 (.reuse 2) (.run (.step 28 (.step 3 (.step 41 (.step 49 (.step 3 (.close 21)))))))) (.run (.step 3 (.step 4 (.step 21 (.step 31 (.step 48 (.step 4 (.step 10 (.step 16 (.close 21))))))))))) (.run (.step 3 (.step 10 (.step 7 (.close 9)))))) (.run (.step 7 (.step 28 (.step 31 (.step 38 (.step 41 (.step 3 (.step 7 (.step 16 (.close 21)))))))))))) (.step 7 (.step 31 (.split 38 1 (.reuse 3) (.run (.step 28 (.step 38 (.step 39 (.step 41 (.step 3 (.step 7 (.step 16 (.close 21)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 4898883310657342436947858505931971705553515434341103012552357296195872284853796012395921219210139945053925296592169658717294058297165951783905284137176532416050756989197608714486633572832830005782249472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.step 16 (.step 21 (.close 22)))) (.step 28 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 28)))))) (.step 3 (.step 7 (.step 4 (.step 10 (.step 8 (.close 28))))))) (.step 7 (.step 16 (.step 28 (.step 21 (.step 22 (.step 21 (.close 31)))))))) (.step 28 (.step 31 (.step 3 (.step 8 (.close 37)))))) (.step 5 (.step 7 (.step 28 (.step 31 (.close 16)))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.close 37)))))))) (.step 3 (.step 28 (.step 31 (.close 16))))) (.step 5 (.step 7 (.step 28 (.step 21 (.step 31 (.close 16))))))) (.step 5 (.step 7 (.step 16 (.close 31))))) (.step 28 (.step 31 (.step 49 (.step 3 (.step 31 (.step 37 (.step 3 (.step 8 (.step 37 (.close 8))))))))))) (.step 28 (.step 31 (.close 49)))) (.step 37 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.step 37 (.step 7 (.close 31))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.close 37)))))))) (.step 3 (.step 16 (.step 28 (.close 31))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 28 (.close 31))))))) (.step 5 (.step 7 (.step 16 (.close 31))))) (.step 16 (.step 28 (.step 31 (.step 37 (.close 3)))))) (.step 16 (.step 28 (.step 31 (.step 37 (.close 8)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895559371364629164715370542796639060337024974723973896702949596877291520⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 51 1 (.step 28 (.split 52 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 50 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 5 0 (.step 28 (.close 3)) (.step 3 (.step 10 (.step 8 (.close 3))))) (.step 5 (.step 9 (.step 26 (.close 28))))) (.step 28 (.step 3 (.step 5 (.close 48))))) (.step 5 (.step 28 (.close 48)))) (.step 3 (.step 5 (.step 24 (.step 43 (.step 8 (.step 3 (.close 28)))))))) (.step 3 (.step 5 (.step 9 (.step 28 (.close 48)))))) (.step 3 (.step 28 (.step 3 (.close 7))))) (.step 3 (.step 28 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 28 (.close 48))))) (.step 3 (.step 7 (.step 9 (.step 26 (.step 21 (.step 26 (.close 28)))))))) (.step 3 (.step 5 (.step 48 (.step 5 (.step 9 (.step 16 (.step 48 (.close 58))))))))) (.step 3 (.step 28 (.step 47 (.step 49 (.close 50)))))) (.step 28 (.step 3 (.step 28 (.step 47 (.close 49)))))) (.step 3 (.step 4 (.step 28 (.step 31 (.step 48 (.step 4 (.step 10 (.step 16 (.close 21)))))))))) (.step 3 (.step 9 (.step 10 (.step 4 (.close 7)))))) (.step 7 (.step 28 (.close 4)))) (.step 10 (.step 28 (.step 4 (.close 21))))) (.step 7 (.step 28 (.close 4)))) (.step 7 (.step 16 (.close 28)))) (.step 3 (.step 7 (.step 18 (.step 28 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861630357709485081999063942077045500305488729665852932096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.step 8 (.step 18 (.close 3)))) (.step 8 (.step 3 (.step 18 (.step 3 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.close 19))))))) (.step 8 (.step 56 (.step 3 (.step 4 (.close 7)))))) (.step 3 (.step 8 (.step 18 (.close 19))))) (.step 4 (.step 7 (.step 8 (.step 18 (.close 17)))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.step 50 (.close 3))))) (.step 8 (.step 18 (.step 49 (.step 18 (.step 3 (.step 19 (.step 3 (.close 19))))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 17 (.step 19 (.step 17 (.close 25)))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 41 (.step 7 (.step 19 (.close 20))))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 19 (.step 25 (.close 49)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861630357709485081999063942077045500305488729665852932096⟩
def references : Fin 4 → Box := ![Part8.root, Part9.root, Part10.root, Part11.root]
def proof : Chunks.Proof 4 := (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.reuse 1) (.run (.step 16 (.step 28 (.step 37 (.step 38 (.step 41 (.step 3 (.step 7 (.close 16)))))))))) (.run (.step 37 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.step 37 (.step 7 (.close 31))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.close 37)))))))) (.step 3 (.step 16 (.step 28 (.step 22 (.close 31)))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 28 (.close 31)))))))) (.step 5 (.step 7 (.step 16 (.close 31))))) (.step 16 (.step 28 (.step 31 (.step 37 (.close 3)))))) (.step 16 (.step 28 (.step 31 (.step 37 (.close 8)))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 38 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 3 (.close 28))))))))))) (.reuse 2)) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 4898883310657342436947858505931971701868005253851316535753964150702423300962214875397026012969633225421226311031900970430060731887902717595536502745583415857520429356621747874322688560634665447765049344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.step 8 (.step 18 (.close 3)))) (.step 8 (.step 3 (.step 18 (.step 3 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.close 19))))))) (.step 8 (.step 36 (.step 51 (.step 7 (.step 18 (.step 3 (.close 19)))))))) (.step 3 (.step 8 (.step 18 (.close 19))))) (.step 4 (.step 7 (.step 8 (.step 18 (.close 17)))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.step 50 (.close 3))))) (.step 8 (.step 18 (.step 49 (.step 18 (.step 3 (.step 19 (.step 3 (.close 19))))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 17 (.step 19 (.step 17 (.close 20)))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 41 (.step 7 (.step 19 (.close 20))))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 19 (.step 20 (.step 19 (.step 25 (.close 49)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 4898883310657342436947858505931971701868005253851316535753964150702423300962214875397026012969633225421226311031900970430060731887902719280533169442496907908033882781663342607060346211891337497749225472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.step 8 (.step 18 (.close 3)))) (.step 8 (.step 3 (.step 18 (.step 3 (.close 19)))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.close 19))))))) (.step 8 (.step 56 (.step 3 (.step 4 (.close 7)))))) (.step 3 (.step 8 (.step 18 (.close 19))))) (.step 4 (.step 7 (.step 8 (.step 18 (.close 17)))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.close 50)))) (.step 8 (.step 18 (.step 49 (.step 18 (.step 3 (.close 19))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 17 (.close 19)))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 41 (.close 19))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 19 (.close 49))))))))) (.step 19 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.close 19)))) (.step 8 (.step 18 (.step 19 (.step 3 (.close 28)))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 17 (.close 19)))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 19 (.close 28)))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 7 (.step 8 (.step 19 (.step 20 (.step 25 (.close 28))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768255444530293429638403179575160269446178193550187660127887651160600013903194637219012567029635799181822082622317615531636457783302637921884962816⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 30 0 (.split 45 1 (.split 50 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 25 0 (.step 8 (.step 3 (.step 55 (.close 3)))) (.step 3 (.step 8 (.step 3 (.step 14 (.close 3)))))) (.step 4 (.step 8 (.step 34 (.step 3 (.close 14)))))) (.step 8 (.step 3 (.close 60)))) (.step 3 (.step 24 (.step 43 (.step 8 (.step 3 (.step 14 (.step 3 (.close 28))))))))) (.step 8 (.step 14 (.close 3)))) (.step 3 (.step 4 (.step 8 (.step 14 (.step 34 (.step 14 (.step 3 (.step 14 (.step 18 (.close 48))))))))))) (.step 4 (.step 8 (.step 14 (.step 34 (.close 48)))))) (.step 3 (.step 48 (.step 8 (.step 7 (.step 3 (.close 14))))))) (.step 3 (.step 48 (.step 14 (.step 7 (.step 3 (.close 8))))))) (.step 3 (.step 48 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 8))))) (.step 3 (.step 8 (.step 3 (.close 14))))) (.step 3 (.step 8 (.close 14))))))) (.step 3 (.step 7 (.step 8 (.step 14 (.close 34)))))) (.step 3 (.step 5 (.step 18 (.step 3 (.step 30 (.step 8 (.step 3 (.step 14 (.step 34 (.close 48))))))))))) (.step 3 (.step 8 (.step 14 (.step 18 (.step 34 (.close 48))))))) (.step 3 (.step 7 (.step 27 (.step 14 (.step 34 (.step 8 (.step 14 (.close 44))))))))) (.step 3 (.step 4 (.step 34 (.step 4 (.step 48 (.step 49 (.step 27 (.close 34))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556398928213668202491009620791787520⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.reuse 0) (.run (.step 3 (.step 8 (.step 14 (.step 49 (.step 50 (.close 3)))))))) (.run (.step 8 (.step 3 (.step 14 (.step 34 (.step 49 (.close 3)))))))) (.run (.step 3 (.step 8 (.step 3 (.step 7 (.close 27))))))) (.run (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 7 (.step 28 (.step 37 (.close 39))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 43 (.step 24 (.step 49 (.step 50 (.step 59 (.step 60 (.split 42 1 (.step 24 (.step 8 (.step 3 (.close 14)))) (.step 3 (.step 8 (.step 14 (.close 28)))))))))))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 28 (.step 14 (.step 24 (.step 8 (.step 7 (.step 37 (.step 39 (.close 41)))))))))))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 14 (.step 28 (.step 37 (.step 8 (.step 7 (.step 14 (.close 37))))))))))))))) (.run (.step 3 (.step 7 (.step 31 (.step 7 (.step 3 (.close 8)))))))) (.run (.step 3 (.step 4 (.step 5 (.step 28 (.step 24 (.step 43 (.step 24 (.step 8 (.step 14 (.step 28 (.close 14))))))))))))) (.run (.step 7 (.step 8 (.step 14 (.step 17 (.step 14 (.step 7 (.step 18 (.close 3)))))))))) (.run (.step 7 (.step 8 (.step 14 (.step 17 (.step 14 (.step 7 (.step 18 (.step 3 (.close 14))))))))))) (.run (.step 7 (.step 8 (.step 14 (.step 17 (.step 14 (.step 7 (.step 18 (.step 19 (.close 3)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556398928213668202491009620791787520⟩
def references : Fin 4 → Box := ![Part12.root, Part13.root, Part14.root, Part16.root]
def proof : Chunks.Proof 4 := (.split 11 1 (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.reuse 1) (.run (.step 20 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 20 (.step 7 (.step 18 (.close 3)))) (.step 4 (.step 7 (.step 11 (.step 18 (.close 17)))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.step 19 (.step 3 (.close 20)))))) (.step 8 (.step 18 (.step 20 (.step 19 (.step 20 (.step 3 (.close 28)))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 17 (.step 19 (.step 17 (.close 20)))))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 19 (.step 20 (.close 28))))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 7 (.step 8 (.step 28 (.step 19 (.step 20 (.step 19 (.close 25)))))))))))))))))) (.step 7 (.step 18 (.split 17 1 (.reuse 2) (.run (.step 19 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.close 19)))) (.step 8 (.step 18 (.step 19 (.step 3 (.close 28)))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 17 (.close 19)))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 19 (.close 28)))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 7 (.step 8 (.step 19 (.step 20 (.close 28)))))))))))))))) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2251801961168896, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070819612416902153342427555758679335880405010435516860832613450894501111135101153726692319035392⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 51 1 (.step 8 (.split 52 1 (.split 55 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 45 1 (.split 50 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 25 0 (.step 8 (.close 3)) (.step 3 (.step 8 (.close 3)))) (.step 4 (.close 8))) (.step 8 (.step 3 (.step 4 (.close 48))))) (.step 3 (.step 10 (.step 24 (.step 10 (.step 8 (.step 3 (.close 28)))))))) (.step 3 (.step 4 (.step 8 (.close 48))))) (.step 4 (.step 8 (.close 48)))) (.step 3 (.step 8 (.step 3 (.close 7))))) (.step 3 (.step 8 (.step 3 (.close 7))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 5 (.step 18 (.step 3 (.step 30 (.step 3 (.step 8 (.close 48))))))))) (.step 3 (.step 8 (.close 48))))) (.step 3 (.step 7 (.step 8 (.step 27 (.step 34 (.close 44))))))) (.step 3 (.step 4 (.step 48 (.step 8 (.step 3 (.step 7 (.step 27 (.step 34 (.close 44)))))))))) (.step 3 (.step 8 (.step 47 (.step 48 (.close 50)))))) (.step 8 (.step 3 (.step 8 (.step 47 (.close 49)))))) (.step 3 (.step 8 (.step 3 (.step 7 (.close 27)))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 3 (.step 28 (.step 37 (.step 45 (.close 49)))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 10 (.step 43 (.step 24 (.step 10 (.step 8 (.step 28 (.close 41)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721537017401835520⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 5 1 (.split 10 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 11 1 (.split 25 1 (.split 38 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 3 (.close 28))))) (.step 3 (.step 7 (.step 28 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 3 (.close 8))))))))))) (.split 10 1 (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 1) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 8 (.step 28 (.step 24 (.step 8 (.step 3 (.step 41 (.step 39 (.step 37 (.step 45 (.close 49)))))))))))))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 8 (.step 28 (.step 41 (.step 24 (.step 8 (.step 3 (.step 37 (.close 49)))))))))))))))) (.run (.step 3 (.step 7 (.step 8 (.step 3 (.close 7))))))) (.run (.step 3 (.step 4 (.step 5 (.step 8 (.step 10 (.step 28 (.step 24 (.step 10 (.step 8 (.close 28)))))))))))) (.run (.step 7 (.step 8 (.close 4))))) (.run (.step 7 (.step 8 (.close 4))))) (.run (.step 7 (.step 8 (.close 4))))) (.run (.step 8 (.step 4 (.step 7 (.close 34)))))) (.run (.step 3 (.step 7 (.step 8 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721538116913463296⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 5 1 (.split 11 1 (.split 25 1 (.split 38 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 3 (.close 28))))) (.step 3 (.step 7 (.step 28 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 3 (.close 8))))) (.step 3 (.step 7 (.step 8 (.step 3 (.close 7))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part20.excludes
end FiveColour.Packed.ProjectedChunks.Case16
