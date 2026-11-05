module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case38
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721535917890207744⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨37630511536740859966423, 5789234131009369111655880410916383799149935097950111679937790244350696937832588910803674238545500183085609357535611307840729301634221804252716538090356296810875202044827950228461282219658217406305038239415791728186442646529, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895704855068445259560105394537425254182849656152267523402121774861738202336471050681150142431567084857165574524454675443950646797756861005884478239125071018415710407993177101823901696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 52 1 (.split 67 1 (.split 5 0 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 48 (.step 3 (.step 7 (.step 10 (.step 3 (.step 16 (.close 21))))))) (.step 3 (.step 28 (.close 3)))) (.step 7 (.close 3))) (.step 7 (.step 3 (.close 18)))) (.step 7 (.step 3 (.close 18)))) (.split 16 0 (.split 17 0 (.split 43 0 (.split 51 0 (.step 3 (.step 4 (.step 3 (.close 17)))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 17)))) (.step 7 (.step 18 (.close 3))))) (.step 7 (.close 3))) (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 43 0 (.split 51 0 (.step 3 (.step 4 (.step 3 (.close 8)))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.step 8 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.step 3 (.step 8 (.close 3))) (.step 3 (.step 4 (.close 3)))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 8))) (.step 7 (.close 8)))) (.step 3 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.step 48 (.close 3)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 9797766621314684873895708907333611306390233521696777233527924167357481041907833778309934839822358960865713813468870352156521784329433324376784115671543847936941975259849651677941092067123272616320696320⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 56 1 (.split 57 1 (.split 59 1 (.reuse 0) (.run (.step 55 (.split 67 1 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.step 58 (.split 17 0 (.step 55 (.step 7 (.step 3 (.step 9 (.step 26 (.step 3 (.step 16 (.close 21)))))))) (.step 7 (.close 3)))) (.step 7 (.step 3 (.close 18)))) (.step 48 (.step 3 (.step 7 (.step 3 (.close 17)))))) (.step 7 (.close 3)))) (.step 48 (.step 3 (.step 7 (.close 8))))) (.step 7 (.step 3 (.step 9 (.step 3 (.close 8))))))))) (.run (.step 3 (.step 60 (.split 52 1 (.split 10 0 (.step 60 (.step 3 (.step 18 (.step 3 (.close 16))))) (.step 3 (.close 49))) (.step 48 (.step 3 (.step 49 (.step 3 (.close 8)))))))))) (.run (.split 52 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 57 1 (.split 59 1 (.split 5 0 (.step 28 (.split 11 0 (.step 3 (.split 17 0 (.split 22 0 (.step 48 (.step 55 (.close 7))) (.step 3 (.close 4))) (.step 3 (.close 4)))) (.step 3 (.close 4)))) (.step 3 (.step 10 (.step 28 (.step 3 (.close 8)))))) (.step 5 (.step 10 (.step 22 (.step 26 (.step 28 (.step 48 (.close 7)))))))) (.step 28 (.step 51 (.step 3 (.close 60))))) (.step 3 (.step 5 (.step 43 (.step 50 (.step 7 (.step 3 (.step 28 (.step 3 (.close 8)))))))))) (.step 3 (.step 58 (.split 57 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 16))))) (.step 3 (.step 28 (.step 3 (.close 16)))))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 28 (.step 48 (.close 16)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966317649180977032861940016616768361105608460486015634259053152913993556129296987880477201793273199895158105624620123331681876308801486383677108309607841792⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 53 1 (.split 55 1 (.reuse 0) (.run (.step 48 (.step 58 (.step 3 (.step 5 (.step 28 (.close 31)))))))) (.run (.split 52 1 (.split 55 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.close 4)) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 7 (.step 18 (.close 3)))) (.step 8 (.split 25 0 (.step 56 (.step 3 (.close 34))) (.step 3 (.step 14 (.step 24 (.step 3 (.step 5 (.close 19))))))))) (.step 8 (.close 3))) (.step 4 (.step 8 (.step 36 (.step 44 (.step 3 (.step 18 (.step 34 (.close 48))))))))) (.step 8 (.step 51 (.step 3 (.close 60))))) (.step 3 (.step 24 (.step 43 (.close 51))))) (.step 3 (.step 48 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 8))))) (.step 3 (.step 8 (.step 3 (.close 17))))) (.step 3 (.step 8 (.close 28))))))) (.step 3 (.step 48 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 8))))) (.step 3 (.step 8 (.step 3 (.close 14))))) (.step 3 (.step 8 (.close 14))))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 5 (.step 18 (.step 3 (.step 30 (.step 8 (.step 3 (.close 48))))))))) (.step 3 (.step 8 (.step 48 (.close 19))))))) (.run (.step 3 (.step 7 (.step 3 (.step 48 (.close 54)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320922571584929003810029806465188704760677128061677323842636205361652263093392555032085063365525799315256511304250891752885526058032269070161638135431168⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.reuse 0) (.run (.step 55 (.split 51 1 (.step 58 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.step 58 (.split 17 0 (.step 55 (.step 7 (.step 3 (.step 9 (.step 21 (.step 3 (.close 16))))))) (.step 7 (.close 3)))) (.step 7 (.step 3 (.close 18)))) (.step 48 (.step 3 (.step 7 (.step 3 (.close 17)))))) (.step 7 (.close 3)))) (.step 48 (.step 3 (.step 7 (.close 8))))) (.step 7 (.step 3 (.step 9 (.step 3 (.close 8)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 5 0 (.split 11 0 (.split 34 0 (.split 36 0 (.step 53 (.close 3)) (.step 7 (.step 9 (.step 55 (.close 7))))) (.step 7 (.step 9 (.step 55 (.step 7 (.close 16)))))) (.step 27 (.step 48 (.close 7)))) (.step 9 (.step 27 (.close 48)))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7)))))) (.step 3 (.step 48 (.step 3 (.close 8))))) (.step 5 (.step 48 (.step 7 (.step 9 (.step 7 (.step 21 (.step 7 (.step 16 (.step 7 (.close 26))))))))))) (.step 3 (.step 4 (.step 35 (.step 48 (.close 8))))))) (.step 3 (.step 54 (.step 7 (.step 3 (.step 48 (.step 9 (.step 21 (.step 26 (.close 28)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 9797766621314684873895708907333611310075747213533918822312342690894565662010827315779093107500927427650751881800998691086849622370637376465739371943525728396542471781441264153881891572981298317691453440⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.step 58 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.step 58 (.split 17 0 (.step 55 (.step 7 (.step 3 (.step 9 (.step 16 (.step 3 (.close 21))))))) (.step 7 (.close 3)))) (.step 7 (.step 3 (.close 18)))) (.step 48 (.step 3 (.step 7 (.step 3 (.close 17)))))) (.step 7 (.close 3)))) (.step 48 (.step 3 (.step 7 (.close 8))))) (.step 7 (.step 3 (.step 9 (.step 3 (.close 8)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 5 0 (.split 11 0 (.split 34 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.step 9 (.step 55 (.close 7))))) (.step 7 (.step 9 (.step 55 (.step 7 (.close 16)))))) (.step 27 (.step 48 (.close 7)))) (.step 9 (.step 27 (.close 48)))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7))))) (.step 7 (.step 27 (.step 48 (.close 7)))))) (.step 3 (.step 48 (.step 3 (.close 8))))) (.step 5 (.step 16 (.step 48 (.step 7 (.step 9 (.step 7 (.step 22 (.step 7 (.step 21 (.close 26))))))))))) (.step 3 (.step 4 (.step 48 (.step 8 (.close 17))))))) (.step 3 (.step 54 (.step 7 (.step 3 (.step 48 (.step 9 (.step 21 (.step 26 (.step 21 (.close 28))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258493109954742702384210604007694103596633028146790946027889814942437258560771243922374072759807920345114128560690619651930700575115096742690816⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 47 1 (.split 49 1 (.reuse 0) (.step 55 (.split 50 1 (.reuse 1) (.run (.step 55 (.split 53 1 (.split 55 1 (.split 56 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 25 0 (.step 52 (.step 55 (.step 7 (.step 9 (.step 5 (.step 7 (.close 16))))))) (.step 9 (.step 27 (.step 52 (.step 3 (.step 16 (.close 21))))))) (.step 27 (.step 52 (.step 48 (.close 7))))) (.step 27 (.step 52 (.step 48 (.close 7))))) (.step 27 (.step 55 (.step 7 (.step 17 (.step 7 (.step 34 (.close 44)))))))) (.step 9 (.step 27 (.step 48 (.step 3 (.step 7 (.close 44))))))) (.step 5 (.step 9 (.step 21 (.step 5 (.step 16 (.step 48 (.step 7 (.step 22 (.step 7 (.step 26 (.close 52)))))))))))) (.step 48 (.close 52))) (.step 3 (.step 4 (.step 27 (.step 34 (.step 4 (.step 35 (.step 48 (.close 44)))))))))))))) (.run (.step 3 (.split 52 1 (.split 55 1 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 49 (.step 50 (.step 3 (.step 50 (.close 8))))) (.step 3 (.step 8 (.step 28 (.step 48 (.step 3 (.step 47 (.step 3 (.step 18 (.step 3 (.close 48))))))))))) (.step 48 (.step 50 (.close 3)))) (.step 48 (.step 50 (.step 3 (.close 21))))) (.step 48 (.step 49 (.step 50 (.step 3 (.close 21)))))) (.step 3 (.step 48 (.close 50)))) (.step 3 (.step 48 (.step 49 (.step 3 (.close 50)))))) (.step 48 (.step 50 (.step 3 (.step 16 (.close 21)))))) (.step 48 (.step 3 (.close 50)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993512314372461856235306444415223878076369764031936969052253899181852508853859710143115846775732927687029205343260228066981774062780416⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 45 1 (.split 46 1 (.reuse 0) (.run (.split 47 1 (.step 3 (.split 52 1 (.split 55 1 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 49 (.step 50 (.step 49 (.step 3 (.step 49 (.step 8 (.close 17))))))) (.step 3 (.step 8 (.step 28 (.step 48 (.step 3 (.step 47 (.step 3 (.step 18 (.step 3 (.close 48))))))))))) (.step 48 (.step 49 (.close 3)))) (.step 48 (.step 49 (.step 3 (.close 21))))) (.step 48 (.close 49))) (.step 3 (.step 48 (.step 49 (.close 3))))) (.step 3 (.step 48 (.close 49)))) (.step 48 (.step 49 (.step 3 (.close 21))))) (.step 48 (.step 3 (.close 49))))) (.step 49 (.step 3 (.step 49 (.close 3))))))) (.run (.step 48 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 48 (.step 31 (.step 48 (.step 4 (.step 8 (.close 17)))))) (.step 48 (.close 53))) (.step 48 (.close 52))) (.step 3 (.step 48 (.close 50)))) (.step 3 (.step 48 (.close 49)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225215024284136453122862303379606157926290524943851354588919133636672670159250114037787681109470204793925049278651170816⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 28)))))) (.step 3 (.step 7 (.step 10 (.step 8 (.close 28)))))) (.step 7 (.step 28 (.close 31)))) (.step 28 (.step 31 (.step 3 (.step 8 (.close 37)))))) (.step 28 (.step 59 (.step 3 (.step 7 (.close 16)))))) (.step 5 (.step 7 (.step 28 (.step 31 (.step 16 (.close 21))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 28 (.step 14 (.step 37 (.close 39))))))))) (.step 3 (.step 28 (.step 31 (.step 16 (.close 45)))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.step 16 (.close 22))))))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.step 22 (.step 21 (.close 45)))))))))) (.step 28 (.step 31 (.step 50 (.step 31 (.step 50 (.close 3))))))) (.step 28 (.step 31 (.step 49 (.step 3 (.step 21 (.step 22 (.step 21 (.close 31))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 9797766621314684873895708907333611310075747216966320922571584929003810029806465188704763139753448951978793403645367911238956210038736489153782272567653021868914969467416098917698962576297712052384825344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 52 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 55 1 (.split 56 1 (.split 57 1 (.split 5 0 (.split 30 0 (.split 34 0 (.split 53 1 (.step 28 (.step 3 (.step 43 (.step 21 (.step 3 (.step 22 (.close 31))))))) (.step 3 (.step 24 (.step 3 (.step 19 (.close 28)))))) (.step 28 (.step 7 (.step 31 (.step 3 (.close 14)))))) (.step 3 (.step 7 (.step 28 (.step 3 (.close 7)))))) (.step 5 (.step 10 (.step 8 (.step 3 (.step 28 (.step 3 (.close 8)))))))) (.step 28 (.step 60 (.close 3)))) (.step 28 (.step 41 (.close 3)))) (.step 5 (.step 28 (.step 41 (.step 48 (.step 58 (.close 31))))))) (.step 3 (.step 5 (.step 43 (.step 59 (.step 7 (.step 3 (.step 28 (.step 3 (.close 8)))))))))) (.step 3 (.step 5 (.step 41 (.step 43 (.step 50 (.step 60 (.step 3 (.step 5 (.step 3 (.step 8 (.close 19)))))))))))) (.step 3 (.step 58 (.split 53 1 (.split 57 1 (.split 5 0 (.step 3 (.step 7 (.step 3 (.step 28 (.step 3 (.step 7 (.close 16))))))) (.step 3 (.close 8))) (.step 3 (.step 28 (.step 3 (.close 41))))) (.step 3 (.step 8 (.step 14 (.close 28)))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 28 (.step 41 (.step 48 (.close 16)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 28))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 48 (.step 7 (.step 9 (.close 21))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070819612416902153342427555758679335880405010435516860832613450894501111135101152599692900564992⟩
def references : Fin 3 → Box := ![Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 3 := (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 3 (.split 45 1 (.split 46 1 (.step 3 (.split 53 1 (.split 55 1 (.split 56 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 54 (.split 38 0 (.step 70 (.split 45 0 (.split 49 1 (.step 7 (.close 3)) (.step 52 (.step 7 (.close 3)))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 7 (.close 9))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 8 (.close 10)))) (.step 3 (.step 7 (.step 8 (.step 27 (.close 46))))))))) (.reuse 1)) (.split 42 1 (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.reuse 2) (.run (.step 3 (.step 5 (.step 48 (.step 5 (.step 16 (.step 48 (.step 9 (.step 58 (.close 26))))))))))) (.run (.step 21 (.step 28 (.step 3 (.step 41 (.step 50 (.step 3 (.close 16))))))))) (.run (.step 28 (.step 49 (.step 3 (.step 41 (.step 49 (.step 3 (.close 21))))))))) (.run (.step 3 (.step 4 (.step 21 (.step 31 (.step 48 (.step 4 (.step 10 (.step 16 (.step 21 (.close 28)))))))))))) (.run (.step 3 (.step 10 (.step 7 (.close 9)))))) (.run (.step 7 (.step 28 (.step 31 (.step 38 (.step 41 (.step 76 (.step 41 (.step 3 (.step 7 (.step 16 (.close 21))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 4898883310657342436947858505931971705553515434341103012552357296195872284851088327147756360951181440295252157463117783175219418881907434745724140652330357215093890044559272171053653585885608662081208320⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.step 22 (.close 31))) (.step 28 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 28)))))) (.step 3 (.step 7 (.step 10 (.step 8 (.close 28)))))) (.step 7 (.step 22 (.step 28 (.close 31))))) (.step 28 (.step 31 (.step 3 (.step 8 (.close 37)))))) (.step 22 (.step 28 (.step 51 (.step 59 (.step 3 (.step 4 (.close 7)))))))) (.step 5 (.step 7 (.step 28 (.step 31 (.step 16 (.close 21))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 28 (.step 14 (.step 37 (.close 39))))))))) (.step 3 (.step 28 (.step 31 (.step 16 (.close 39)))))) (.step 5 (.step 7 (.step 22 (.step 21 (.step 29 (.close 31))))))) (.step 5 (.step 7 (.step 22 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22))))))))) (.step 28 (.step 31 (.step 50 (.step 31 (.step 50 (.close 3))))))) (.step 28 (.step 31 (.step 49 (.step 3 (.step 21 (.close 22))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 4898883310657342436947858505931971705553515434341103012552357296195872284851088327147756360948832899952223066413032513135872362422976030318461318016272601143550781983236534907750899968378333230656389120⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.step 16 (.step 21 (.close 22)))) (.step 28 (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 7 (.step 4 (.step 16 (.close 28)))))) (.step 3 (.step 7 (.step 10 (.step 8 (.close 28)))))) (.step 7 (.step 28 (.close 31)))) (.step 28 (.step 31 (.step 3 (.step 8 (.close 37)))))) (.step 28 (.step 59 (.step 3 (.step 7 (.close 16)))))) (.step 5 (.step 7 (.step 28 (.step 31 (.step 16 (.close 21))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.close 37)))))))) (.step 3 (.step 28 (.step 31 (.step 16 (.close 37)))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22)))))))) (.step 5 (.step 7 (.step 16 (.step 31 (.close 16)))))) (.step 28 (.step 31 (.step 49 (.step 31 (.step 50 (.step 3 (.step 21 (.close 22))))))))) (.step 28 (.step 31 (.close 49)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646225306108056384960023375719349889697510367261388382142602357374124735779480414861667539615744⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 37 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.step 37 (.step 7 (.close 31))) (.step 5 (.step 7 (.step 28 (.step 31 (.step 16 (.close 21))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.close 37)))))))) (.step 3 (.step 16 (.step 28 (.step 31 (.close 37)))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22)))))))) (.step 5 (.step 7 (.step 16 (.close 31))))) (.step 16 (.step 28 (.step 31 (.step 45 (.step 3 (.step 37 (.close 8)))))))) (.step 16 (.step 28 (.step 31 (.step 37 (.step 8 (.close 49)))))))))) (.run (.step 16 (.step 28 (.step 37 (.step 38 (.step 41 (.step 3 (.step 7 (.step 16 (.close 21))))))))))) (.run (.step 37 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.step 37 (.step 7 (.close 31))) (.step 5 (.step 7 (.step 28 (.step 31 (.step 16 (.close 21))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 28 (.close 37)))))))) (.step 3 (.step 16 (.step 28 (.step 31 (.close 37)))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.close 22)))))))) (.step 5 (.step 7 (.step 16 (.close 31))))) (.step 16 (.step 28 (.step 31 (.step 39 (.step 45 (.step 49 (.step 3 (.step 37 (.step 3 (.step 37 (.close 8)))))))))))) (.step 16 (.step 28 (.step 31 (.step 37 (.step 8 (.close 49))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719446109644165038299075671418729782048078852993514574090160780178198373723013120⟩
def references : Fin 3 → Box := ![Part9.root, Part10.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.reuse 1) (.run (.step 45 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.step 45 (.step 7 (.step 31 (.close 3)))) (.step 5 (.step 7 (.step 28 (.step 31 (.step 16 (.close 21))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 28 (.step 14 (.step 37 (.close 39))))))))) (.step 3 (.step 31 (.step 16 (.step 28 (.step 16 (.close 39))))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.step 16 (.close 22))))))))) (.step 5 (.step 7 (.step 29 (.step 31 (.step 16 (.step 21 (.step 22 (.step 21 (.close 45)))))))))) (.step 28 (.step 31 (.step 39 (.step 45 (.step 8 (.close 37))))))) (.step 28 (.step 31 (.step 37 (.step 39 (.step 45 (.step 8 (.close 49))))))))))) (.run (.step 28 (.step 38 (.step 39 (.step 41 (.split 49 1 (.step 41 (.step 3 (.step 7 (.step 16 (.close 21))))) (.step 3 (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.close 31))))))))))))))))) (.reuse 2)) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 3 (.step 7 (.step 41 (.step 3 (.close 7))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 9797766621314684873895708907333611310075747216966320925768258496089993515087042155977050166022829408021160073200469012344868830878912827456540721009065379647498699239170117703368284305995303726679588864⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 28 (.split 52 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 55 1 (.split 57 1 (.split 5 0 (.split 30 0 (.split 46 0 (.split 53 1 (.step 28 (.close 3)) (.step 3 (.step 4 (.close 14)))) (.step 28 (.step 3 (.close 48)))) (.step 3 (.step 7 (.close 28)))) (.step 5 (.step 10 (.step 8 (.step 3 (.close 28)))))) (.step 28 (.step 47 (.step 3 (.close 48))))) (.step 5 (.step 28 (.close 48)))) (.step 3 (.step 5 (.step 43 (.step 59 (.step 7 (.step 3 (.step 28 (.step 3 (.close 8)))))))))) (.step 3 (.step 5 (.step 43 (.step 50 (.step 60 (.step 3 (.step 5 (.step 3 (.step 8 (.close 19))))))))))) (.step 3 (.step 28 (.step 58 (.split 53 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 16))))) (.step 3 (.close 8))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 28 (.close 48))))) (.step 3 (.step 7 (.step 9 (.step 26 (.step 28 (.close 26))))))) (.step 3 (.step 5 (.step 48 (.step 5 (.step 48 (.step 9 (.close 58)))))))) (.step 3 (.step 5 (.step 48 (.step 5 (.step 16 (.step 48 (.step 9 (.step 58 (.close 26)))))))))) (.step 28 (.step 3 (.step 49 (.step 28 (.step 47 (.close 50))))))) (.step 28 (.step 3 (.step 49 (.close 3))))) (.step 3 (.step 4 (.step 28 (.step 31 (.step 48 (.step 4 (.step 10 (.step 16 (.step 21 (.close 28))))))))))) (.step 3 (.step 9 (.step 10 (.step 4 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861630357709485081999063942077045500305488728566341304320⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 8 (.step 3 (.step 4 (.close 7))))) (.step 7 (.step 8 (.close 18)))) (.step 8 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 19 (.close 20)))))))) (.step 8 (.step 56 (.step 3 (.step 7 (.close 18)))))) (.step 3 (.step 8 (.step 18 (.step 19 (.close 25)))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 25)))))))) (.step 8 (.step 18 (.step 50 (.step 3 (.step 17 (.close 18))))))) (.step 8 (.step 18 (.step 49 (.step 18 (.step 49 (.close 3))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.close 25))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 41 (.step 49 (.step 7 (.step 19 (.close 20)))))))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 28 (.step 3 (.step 8 (.step 25 (.step 49 (.step 19 (.step 25 (.close 50))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 4898883310657342436947858505931971701868005253851316535753964150702423300962214875397026012969633225421226311031900970430060731887902717595536502745583415857520429356621747874322688560634664348253421568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 8 (.step 3 (.step 4 (.close 7))))) (.step 7 (.step 8 (.close 18)))) (.step 8 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 19 (.close 20)))))))) (.step 8 (.step 36 (.step 51 (.step 56 (.step 3 (.step 4 (.close 7)))))))) (.step 3 (.step 8 (.step 18 (.step 19 (.close 20)))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 25)))))))) (.step 8 (.step 18 (.step 50 (.step 3 (.step 17 (.close 18))))))) (.step 8 (.step 18 (.step 49 (.step 18 (.step 49 (.close 3))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 20 (.step 17 (.step 19 (.step 20 (.step 25 (.close 36)))))))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 41 (.step 49 (.step 7 (.step 19 (.close 20)))))))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 28 (.step 3 (.step 8 (.step 49 (.step 19 (.step 20 (.step 19 (.step 25 (.close 50)))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631854287161708843652182650314201779300856241265311744⟩
def references : Fin 4 → Box := ![Part13.root, Part14.root, Part15.root, Part16.root]
def proof : Chunks.Proof 4 := (.split 17 1 (.split 22 1 (.split 25 1 (.reuse 0) (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 1) (.run (.step 7 (.step 28 (.step 5 (.step 3 (.step 7 (.close 29)))))))) (.run (.step 10 (.step 28 (.step 21 (.step 3 (.step 4 (.step 21 (.close 26))))))))) (.run (.step 7 (.step 28 (.step 5 (.step 3 (.step 7 (.close 29)))))))) (.run (.step 7 (.step 16 (.step 28 (.close 4)))))) (.run (.step 3 (.step 7 (.step 18 (.step 28 (.step 3 (.close 7))))))))) (.reuse 2)) (.step 7 (.step 18 (.split 22 1 (.reuse 3) (.run (.split 25 1 (.step 25 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.step 25 (.step 7 (.step 18 (.close 3)))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 19 (.step 20 (.close 19))))))))) (.step 3 (.step 18 (.step 8 (.step 19 (.close 20)))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.step 19 (.close 25)))))))) (.step 8 (.step 18 (.step 19 (.step 20 (.step 3 (.close 28))))))) (.step 8 (.step 18 (.step 49 (.close 3))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.step 20 (.close 25)))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 7 (.step 8 (.step 19 (.step 20 (.step 25 (.step 28 (.close 41))))))))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 20 (.step 28 (.step 20 (.step 19 (.step 25 (.close 49)))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 4898883310657342436947858505931971701868005253851316535753964150702423300962214875397026012969633225421226311031900970430060731887902717595536502745581920741345439842936425504738819803105556329261957120⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 5 0 (.step 7 (.step 18 (.step 3 (.close 19)))) (.step 8 (.step 3 (.step 4 (.close 7))))) (.step 7 (.step 8 (.close 18)))) (.step 8 (.step 18 (.step 3 (.close 19))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.close 19))))))) (.step 8 (.step 56 (.step 3 (.step 7 (.close 18)))))) (.step 3 (.step 8 (.step 18 (.close 19))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.close 50)))) (.step 8 (.step 18 (.step 49 (.step 18 (.step 49 (.close 3))))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.close 19))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 41 (.close 19))))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 28 (.step 3 (.step 8 (.step 19 (.step 49 (.step 19 (.close 50)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 4898883310657342436947858505931971701868005253851316535753964150702423300962214875397026012969633225421226311031900970430060731887902719280533169442496907908033882781663342607060346211891336398237597696⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.reuse 0) (.run (.step 19 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.step 19 (.step 7 (.close 18))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.close 19))))))) (.step 3 (.step 18 (.step 8 (.close 19))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.step 19 (.close 28))))) (.step 8 (.step 18 (.step 49 (.close 3))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.close 19))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 7 (.step 8 (.step 19 (.step 28 (.close 41)))))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 28 (.step 19 (.close 49))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611306390237033040780390334793380602647126937646839188288158354627884271187752316957932298718405815412079863242578251911888882255915509990861693644100617380014552269193216⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 45 1 (.split 53 1 (.split 57 1 (.split 56 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 59 1 (.step 8 (.step 3 (.close 34))) (.step 3 (.step 4 (.step 8 (.step 3 (.close 34)))))) (.step 8 (.step 3 (.step 4 (.step 3 (.step 14 (.close 17))))))) (.step 8 (.step 7 (.step 18 (.close 3))))) (.step 8 (.step 7 (.step 18 (.step 3 (.close 14)))))) (.step 3 (.step 24 (.step 8 (.step 3 (.step 5 (.close 14))))))) (.step 8 (.step 60 (.close 3)))) (.step 8 (.step 14 (.close 3)))) (.step 4 (.step 8 (.step 14 (.step 48 (.close 14)))))) (.step 3 (.step 4 (.step 24 (.step 51 (.step 24 (.step 8 (.step 3 (.step 14 (.step 3 (.close 28))))))))))) (.step 3 (.step 4 (.step 14 (.step 24 (.step 49 (.step 60 (.step 3 (.step 4 (.step 3 (.step 8 (.close 14)))))))))))) (.step 3 (.step 48 (.split 56 1 (.split 57 1 (.split 16 0 (.split 17 0 (.step 3 (.step 7 (.step 8 (.step 3 (.step 4 (.close 7)))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 7 (.step 8 (.close 14))))) (.step 3 (.step 8 (.step 3 (.close 14))))) (.step 3 (.step 8 (.close 14))))))) (.step 3 (.step 48 (.step 14 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 8))))) (.step 3 (.step 8 (.step 3 (.close 14))))) (.step 3 (.step 8 (.close 14)))))))) (.step 3 (.step 7 (.step 8 (.step 14 (.close 34)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070819612416902153342427555758679335880405010435516860832613452192575325768808059732316982870016⟩
def references : Fin 1 → Box := ![Part20.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 55 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 18 (.step 30 (.step 8 (.step 3 (.step 34 (.step 3 (.step 14 (.close 48)))))))))))) (.run (.step 3 (.step 8 (.step 14 (.step 48 (.close 14))))))) (.run (.step 3 (.step 7 (.step 27 (.step 14 (.step 34 (.step 8 (.step 14 (.close 44)))))))))) (.run (.step 3 (.step 4 (.step 48 (.step 35 (.step 50 (.step 58 (.step 27 (.step 34 (.step 7 (.step 8 (.close 44))))))))))))) (.run (.step 3 (.step 4 (.step 34 (.step 4 (.step 48 (.step 49 (.step 58 (.step 27 (.step 34 (.close 44)))))))))))) (.run (.step 8 (.step 3 (.step 49 (.step 14 (.step 50 (.step 3 (.close 14))))))))) (.run (.step 8 (.step 34 (.step 14 (.step 3 (.step 49 (.step 3 (.close 14))))))))) (.run (.step 3 (.step 8 (.step 3 (.step 7 (.close 27))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 8 (.step 14 (.step 24 (.step 28 (.step 49 (.step 7 (.step 37 (.step 39 (.step 45 (.close 50)))))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 49 (.step 50 (.step 60 (.split 42 1 (.split 53 1 (.step 43 (.step 24 (.split 5 0 (.step 43 (.step 14 (.step 28 (.step 3 (.step 14 (.step 3 (.close 37))))))) (.step 8 (.close 3))))) (.step 8 (.step 14 (.close 3)))) (.step 3 (.step 4 (.step 28 (.step 8 (.step 14 (.step 37 (.close 39))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631854287161708843653480724528835486207988865347616768⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 28 (.step 41 (.step 14 (.step 24 (.step 8 (.step 49 (.step 7 (.step 37 (.step 39 (.step 45 (.close 50))))))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.step 43 (.step 4 (.step 14 (.step 28 (.step 41 (.step 49 (.step 7 (.step 37 (.step 8 (.step 14 (.close 37))))))))))))))))) (.run (.step 3 (.step 7 (.step 31 (.step 50 (.step 7 (.step 3 (.close 8))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 28 (.step 24 (.step 43 (.step 49 (.step 50 (.step 60 (.split 10 0 (.split 16 0 (.split 30 0 (.split 34 0 (.step 24 (.step 8 (.step 3 (.step 14 (.close 28))))) (.step 3 (.step 8 (.step 14 (.close 28))))) (.step 3 (.step 8 (.close 14)))) (.step 3 (.step 8 (.close 14)))) (.step 3 (.step 8 (.close 14))))))))))))))) (.run (.step 7 (.step 8 (.step 18 (.step 60 (.step 73 (.step 14 (.split 25 1 (.step 17 (.step 14 (.step 7 (.step 18 (.close 3))))) (.step 3 (.step 5 (.close 14)))))))))))) (.run (.step 7 (.step 8 (.step 18 (.split 22 1 (.split 25 1 (.step 17 (.step 14 (.split 38 1 (.split 50 1 (.step 14 (.step 3 (.step 7 (.step 14 (.close 17))))) (.step 3 (.step 4 (.step 7 (.step 14 (.step 17 (.step 14 (.close 18)))))))) (.step 3 (.step 5 (.close 14)))))) (.step 3 (.step 5 (.close 14)))) (.step 14 (.step 7 (.step 17 (.close 18))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2251801961168896, 9797766621314684873895708907333611310075747216966320925768258496089993512314372461856235306444415223878076369764031936969052253899181852508853859710143115846775732927687029205343260228068107673969623040⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 8 (.split 52 1 (.split 55 1 (.split 67 1 (.split 10 0 (.split 30 0 (.split 45 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 68 (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 4 (.close 8)))) (.step 3 (.step 7 (.close 8)))) (.step 7 (.close 8))) (.step 7 (.close 8))) (.step 8 (.close 3))) (.step 4 (.step 8 (.close 48)))) (.step 8 (.step 47 (.step 48 (.step 3 (.close 4)))))) (.step 3 (.step 10 (.step 24 (.step 43 (.step 51 (.step 10 (.step 8 (.close 28))))))))) (.step 4 (.step 8 (.close 48)))) (.step 3 (.step 8 (.step 48 (.split 56 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 8))))) (.step 3 (.close 8))))))) (.step 3 (.step 8 (.step 48 (.split 56 1 (.step 3 (.step 7 (.step 3 (.step 7 (.close 8))))) (.step 3 (.close 8))))))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 5 (.step 18 (.step 3 (.step 30 (.step 8 (.step 3 (.close 48))))))))) (.step 3 (.step 8 (.close 48))))) (.step 3 (.step 7 (.step 8 (.step 27 (.step 34 (.close 44))))))) (.step 3 (.step 4 (.step 48 (.step 8 (.step 3 (.step 7 (.step 27 (.step 34 (.close 44)))))))))) (.step 3 (.step 4 (.step 48 (.step 49 (.step 27 (.step 58 (.step 34 (.step 48 (.close 44)))))))))) (.step 8 (.step 3 (.step 49 (.step 8 (.step 47 (.close 50))))))) (.step 8 (.step 3 (.step 49 (.close 3))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2251801961168896, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556398928213668202492134421187002368⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 3 (.step 8 (.step 3 (.step 7 (.close 27))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 8 (.step 3 (.step 28 (.step 45 (.step 49 (.step 45 (.close 50))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 8 (.step 10 (.step 43 (.step 49 (.step 50 (.step 60 (.split 42 1 (.step 24 (.split 11 0 (.step 10 (.step 8 (.step 3 (.step 28 (.close 37))))) (.step 8 (.close 3)))) (.step 3 (.step 4 (.step 28 (.step 8 (.step 37 (.close 41)))))))))))))))))) (.run (.step 3 (.step 4 (.step 3 (.step 5 (.step 4 (.step 7 (.step 8 (.step 28 (.step 41 (.step 24 (.step 8 (.step 3 (.step 49 (.step 39 (.step 45 (.step 37 (.close 50))))))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 7 (.step 43 (.step 4 (.step 8 (.step 28 (.step 41 (.step 49 (.step 7 (.step 37 (.step 8 (.step 37 (.step 45 (.close 50)))))))))))))))))) (.run (.step 3 (.step 7 (.step 8 (.step 3 (.close 7))))))) (.run (.step 3 (.step 4 (.step 5 (.step 8 (.step 10 (.step 28 (.step 24 (.step 43 (.step 47 (.close 3)))))))))))) (.run (.step 7 (.step 8 (.step 4 (.step 3 (.step 7 (.close 11)))))))) (.run (.step 7 (.step 8 (.step 4 (.step 3 (.step 7 (.close 11)))))))) (.run (.step 7 (.step 8 (.step 4 (.step 3 (.step 7 (.close 11)))))))) (.run (.step 8 (.step 7 (.step 24 (.step 34 (.step 3 (.close 44))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721535917890207744⟩
def references : Fin 4 → Box := ![Part17.root, Part19.root, Part22.root, Part24.root]
def proof : Chunks.Proof 4 := (.split 5 1 (.split 10 1 (.split 11 1 (.split 16 1 (.reuse 0) (.step 7 (.step 18 (.split 17 1 (.reuse 1) (.run (.step 19 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.step 19 (.step 7 (.close 18))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.close 19))))))) (.step 3 (.step 18 (.step 8 (.close 19))))) (.step 4 (.step 7 (.step 11 (.step 18 (.step 17 (.close 19))))))) (.step 4 (.step 7 (.step 11 (.step 17 (.step 18 (.close 19))))))) (.step 8 (.step 18 (.step 19 (.close 28))))) (.step 8 (.step 18 (.step 49 (.close 3))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 18 (.close 19))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 7 (.step 8 (.step 19 (.step 28 (.close 41)))))))))) (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 28 (.step 19 (.close 49))))))))))))))) (.split 16 1 (.reuse 2) (.run (.step 7 (.step 8 (.step 18 (.step 19 (.step 35 (.step 14 (.split 25 1 (.step 17 (.step 14 (.step 7 (.step 18 (.close 3))))) (.step 3 (.step 5 (.close 14))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 11 1 (.split 25 1 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.close 49))) (.step 3 (.step 7 (.step 49 (.step 7 (.step 3 (.close 28))))))) (.step 3 (.step 7 (.step 28 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 14 (.step 3 (.close 7)))))))))))) (.split 10 1 (.reuse 3) (.run (.step 3 (.step 7 (.step 8 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part19.excludes
  · exact Part22.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part25

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part25.excludes
end FiveColour.Packed.ProjectedChunks.Case38
