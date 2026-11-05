module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case99
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447783622995019261834600293796402646082303876835311616⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000409413503253965452678337730340540649546387030196892732096284700566868009505471869653912252061528112354091956851768591570738554689425360617830527025743588818542320431398912⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 57 1 (.split 59 1 (.split 67 1 (.split 45 1 (.split 55 1 (.split 5 0 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 3 (.step 28 (.close 31))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 18 (.step 3 (.close 4))))) (.step 3 (.close 7))) (.step 3 (.step 18 (.step 47 (.step 3 (.step 4 (.close 8))))))) (.step 58 (.close 3))) (.step 48 (.close 3))) (.step 3 (.close 7))) (.split 67 1 (.step 48 (.step 58 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.step 3 (.step 31 (.step 3 (.close 21))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.close 7)))) (.step 3 (.step 18 (.close 48)))))) (.step 3 (.close 7)))) (.step 3 (.step 48 (.step 60 (.split 45 1 (.split 55 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 25 0 (.split 43 0 (.step 60 (.close 3)) (.step 3 (.step 31 (.step 3 (.close 48))))) (.step 31 (.step 3 (.close 48)))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 60 (.close 3))) (.step 47 (.step 60 (.close 3)))) (.step 58 (.step 5 (.step 28 (.close 31))))) (.step 48 (.step 4 (.step 8 (.close 12))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110638088186794583850658653746480219292209514700383857906579188412462163577883705309256930961212223066126870683402972257315223118807359737510530015599721040576512⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 53 1 (.split 56 1 (.reuse 0) (.run (.step 3 (.step 58 (.step 60 (.step 3 (.split 45 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.split 10 0 (.step 31 (.step 3 (.step 21 (.close 48)))) (.step 3 (.close 12)))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 28)))))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 28)))))) (.step 3 (.step 28 (.step 18 (.step 4 (.step 12 (.close 31))))))) (.step 10 (.step 28 (.step 3 (.step 18 (.step 8 (.close 31))))))) (.step 3 (.step 22 (.step 28 (.step 31 (.close 48)))))) (.step 28 (.step 51 (.step 60 (.close 3))))) (.step 5 (.step 28 (.step 3 (.step 31 (.close 48)))))) (.step 10 (.step 22 (.step 31 (.step 28 (.step 3 (.step 48 (.close 4)))))))))))))) (.run (.step 3 (.step 48 (.step 51 (.step 60 (.step 3 (.split 55 1 (.split 10 0 (.step 51 (.split 45 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 16 0 (.step 3 (.step 51 (.step 18 (.split 25 0 (.step 48 (.step 3 (.close 4))) (.step 3 (.step 4 (.close 14))))))) (.step 8 (.step 18 (.step 3 (.close 18))))) (.step 8 (.close 3))) (.step 3 (.step 8 (.step 18 (.close 48))))) (.step 8 (.step 51 (.step 60 (.close 3))))) (.step 4 (.step 8 (.step 3 (.step 18 (.close 48))))))) (.step 3 (.step 8 (.step 3 (.step 14 (.step 3 (.step 12 (.step 3 (.close 28))))))))) (.step 5 (.step 18 (.step 30 (.step 8 (.step 3 (.step 48 (.step 51 (.step 3 (.close 48)))))))))))))))))
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
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 14696649931972027310843563361000416961428110644959694905460647464469174318179182005046179800195600271401316668653718141385594891891031556573788785370139032066199671405809690735373219398348951493713854464⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.step 3 (.step 31 (.step 3 (.close 21))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.close 7)))) (.step 3 (.step 18 (.close 48)))))) (.step 3 (.close 7))) (.step 53 (.split 45 1 (.split 55 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 53 (.split 34 0 (.split 10 0 (.split 16 0 (.step 62 (.close 3)) (.step 3 (.step 18 (.step 3 (.close 48))))) (.step 3 (.step 18 (.step 3 (.step 12 (.close 48)))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 31 (.close 48)))))))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 18 (.step 12 (.close 48))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 48 (.step 3 (.step 21 (.step 29 (.step 16 (.close 22)))))))) (.step 3 (.step 48 (.close 3)))))) (.step 3 (.step 32 (.step 48 (.step 50 (.step 48 (.close 3))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.step 28 (.close 53)))))))) (.step 3 (.step 18 (.step 48 (.close 8))))) (.step 3 (.step 53 (.close 7))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 14696649931972027310843563361000416961428110638094890704942162988250685582587906259194844660941331772055135159844992219033107351522242139378536477658559975836676113185186447991020938006171224852825899008⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.step 3 (.step 31 (.step 3 (.close 21))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 12))) (.step 3 (.close 7)))) (.step 3 (.step 18 (.step 12 (.close 48))))))) (.step 3 (.close 7))) (.step 52 (.split 45 1 (.split 55 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 52 (.split 34 0 (.split 10 0 (.split 16 0 (.step 62 (.close 3)) (.step 3 (.step 18 (.step 3 (.close 48))))) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.step 9 (.step 18 (.step 31 (.close 48))))))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.step 12 (.close 48))))) (.step 3 (.step 48 (.step 3 (.step 16 (.step 31 (.close 21))))))) (.step 3 (.step 48 (.close 3)))))) (.step 3 (.step 12 (.step 48 (.step 49 (.step 48 (.close 3))))))) (.step 3 (.step 16 (.step 22 (.step 31 (.step 48 (.step 49 (.step 21 (.close 52))))))))) (.step 3 (.step 18 (.step 34 (.close 48))))) (.step 3 (.step 52 (.close 7)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959694911853988495516326408048693131662584394368729267579177585613271594698356212993911546580175684444170589001525226342450454425250673589531359800996134912⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.reuse 0) (.run (.step 3 (.step 48 (.step 55 (.step 60 (.split 53 1 (.split 56 1 (.split 5 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 48 (.step 3 (.step 48 (.step 3 (.close 21))))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 22 (.step 28 (.step 31 (.close 48)))))) (.step 3 (.step 8 (.step 18 (.close 48))))))))))) (.run (.step 3 (.step 51 (.step 3 (.step 7 (.step 26 (.step 44 (.close 54))))))))) (.reuse 1)) (.step 55 (.split 50 1 (.reuse 2) (.run (.step 48 (.step 52 (.step 55 (.step 58 (.split 45 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 52 (.split 34 0 (.split 36 0 (.split 10 0 (.step 53 (.close 3)) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 31 (.close 48))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 31 (.close 48)))))))) (.step 3 (.step 21 (.step 3 (.step 31 (.close 48)))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 9 (.step 18 (.step 34 (.close 48)))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.close 52))))))) (.step 3 (.step 48 (.step 3 (.step 21 (.step 31 (.close 52))))))) (.step 3 (.step 18 (.step 34 (.close 48))))) (.step 3 (.step 48 (.close 3))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959694911853994592681463743971020048844673834146670182809924978135050616489292981298088928934902481917028134884281397879425300922561016261358858410928373760⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 47 1 (.reuse 0) (.run (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.step 60 (.split 45 1 (.split 55 1 (.split 5 0 (.split 11 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 43 0 (.step 50 (.close 3)) (.step 3 (.step 31 (.step 3 (.close 48))))) (.step 31 (.step 3 (.step 21 (.close 48))))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 50 (.close 3))) (.step 47 (.step 50 (.close 3)))) (.step 32 (.step 50 (.close 3)))) (.step 32 (.step 48 (.step 4 (.step 8 (.close 12))))))))) (.step 48 (.step 50 (.close 3)))) (.step 28 (.step 48 (.step 50 (.step 3 (.step 50 (.step 3 (.step 16 (.step 21 (.step 16 (.close 22))))))))))) (.step 8 (.step 48 (.step 50 (.step 3 (.step 50 (.step 3 (.step 12 (.close 18))))))))) (.step 3 (.step 48 (.step 3 (.close 50))))) (.step 3 (.step 32 (.step 48 (.step 50 (.step 48 (.close 3))))))) (.step 3 (.step 12 (.step 48 (.step 49 (.step 53 (.step 49 (.step 32 (.step 48 (.close 3)))))))))))))
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272629209391341491588589722679742154323287266452673377934179875085718769687100721549899168604976375014507536808163580339247128772608⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.step 48 (.step 58 (.split 46 1 (.reuse 0) (.run (.split 47 1 (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.step 60 (.split 45 1 (.split 55 1 (.split 5 0 (.split 10 0 (.split 11 0 (.split 16 0 (.step 49 (.step 3 (.close 21))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 49 (.close 3))) (.step 3 (.step 12 (.step 3 (.close 28))))) (.step 47 (.step 49 (.close 3)))) (.step 12 (.step 49 (.close 3)))) (.step 12 (.step 48 (.step 3 (.step 4 (.close 8))))))))) (.step 48 (.step 49 (.close 3)))) (.step 28 (.step 48 (.step 49 (.step 3 (.step 49 (.step 3 (.step 21 (.close 22))))))))) (.step 8 (.step 48 (.step 49 (.step 3 (.step 49 (.step 3 (.step 12 (.close 18))))))))) (.step 3 (.step 48 (.step 3 (.close 49))))) (.step 3 (.step 32 (.step 48 (.step 50 (.step 48 (.close 3))))))) (.step 3 (.step 12 (.step 48 (.step 49 (.step 52 (.step 49 (.step 32 (.step 48 (.close 3))))))))))) (.step 48 (.step 49 (.step 3 (.step 50 (.close 3)))))))))) (.run (.step 3 (.step 10 (.step 30 (.step 47 (.step 3 (.step 46 (.step 9 (.step 27 (.step 46 (.close 52))))))))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 9797766621314684873895712959598777356905878862334473725247485502602642687644833161479305526709901526451883576388150225983693712030812358911014990202488316759610838898447980095790619693104359044011786240⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 52 1 (.split 53 1 (.step 21 (.split 56 1 (.split 57 1 (.step 3 (.step 58 (.split 45 1 (.split 55 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.split 10 0 (.step 31 (.step 3 (.close 21))) (.step 3 (.close 12)))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 28)))))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 28)))))) (.step 3 (.step 28 (.step 18 (.step 4 (.step 12 (.close 31))))))) (.step 10 (.step 28 (.step 3 (.step 18 (.step 8 (.close 31))))))) (.step 3 (.step 21 (.step 28 (.step 31 (.close 41)))))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 21 (.step 41 (.close 48)))))))) (.step 10 (.step 21 (.step 31 (.step 3 (.step 28 (.step 41 (.close 48)))))))))) (.step 26 (.step 28 (.step 3 (.step 48 (.step 60 (.step 3 (.close 16)))))))) (.step 28 (.step 41 (.step 3 (.step 58 (.step 41 (.close 3)))))))) (.step 3 (.step 4 (.step 5 (.step 41 (.step 51 (.step 24 (.step 43 (.step 60 (.split 5 0 (.step 43 (.step 28 (.step 3 (.step 18 (.step 14 (.close 31)))))) (.step 8 (.close 3)))))))))))) (.step 3 (.step 21 (.step 28 (.step 31 (.step 48 (.close 41))))))) (.step 3 (.step 21 (.step 31 (.step 48 (.step 28 (.step 48 (.step 49 (.step 41 (.step 52 (.close 58))))))))))) (.step 21 (.step 28 (.step 32 (.step 41 (.close 50)))))) (.step 21 (.step 41 (.step 48 (.step 28 (.step 41 (.step 49 (.step 3 (.step 49 (.step 3 (.step 21 (.close 22)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808404421007984981332222981525634950415101928307752620619525102454410189852805791217533983713968832919896064⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 58 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.step 60 (.split 53 1 (.step 31 (.step 3 (.close 7))) (.step 3 (.step 28 (.step 8 (.close 31)))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 29 (.step 31 (.close 53)))))))) (.step 3 (.step 9 (.step 18 (.step 31 (.close 52)))))) (.step 31 (.step 3 (.step 8 (.close 50)))))) (.step 3 (.step 31 (.close 49))))))))) (.step 3 (.step 10 (.step 21 (.step 48 (.step 58 (.split 42 1 (.reuse 1) (.run (.step 3 (.step 21 (.step 31 (.step 3 (.step 28 (.step 3 (.step 22 (.step 39 (.close 41))))))))))))))))) (.run (.step 7 (.step 31 (.step 58 (.split 38 1 (.split 42 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 53 1 (.split 57 1 (.step 31 (.step 3 (.close 7))) (.step 28 (.step 31 (.close 3)))) (.step 3 (.step 28 (.step 8 (.close 31))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 22 (.step 29 (.step 31 (.close 53))))))))) (.step 3 (.step 9 (.step 18 (.step 22 (.step 31 (.close 52))))))) (.step 31 (.step 3 (.step 8 (.close 50)))))) (.step 3 (.step 31 (.close 49)))) (.step 7 (.step 31 (.step 7 (.step 22 (.step 28 (.step 3 (.close 39)))))))) (.step 3 (.step 21 (.step 31 (.step 28 (.step 3 (.step 22 (.close 39)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500250506526720, 9797766621314684873895712959598777356905878862334476998638093398747420055737127787136984755110810767502529236293966303806257194146880797960096959400116496052355647375820307510814993790477903033029099520⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 1 (.split 36 1 (.split 38 1 (.step 48 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 28 (.split 52 1 (.split 53 1 (.split 57 1 (.step 3 (.step 58 (.step 28 (.split 45 1 (.split 55 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.close 3)) (.step 3 (.step 18 (.step 16 (.step 21 (.close 28)))))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 28)))))) (.step 3 (.step 28 (.close 3)))) (.step 10 (.step 28 (.close 5)))) (.step 3 (.step 28 (.close 48)))) (.step 3 (.step 5 (.step 28 (.close 48))))) (.step 10 (.step 31 (.step 3 (.step 28 (.step 3 (.close 48)))))))))) (.step 26 (.step 28 (.step 3 (.step 47 (.step 48 (.step 58 (.close 60)))))))) (.step 3 (.step 4 (.step 5 (.step 28 (.step 30 (.step 8 (.step 24 (.step 28 (.step 18 (.step 50 (.step 51 (.close 56))))))))))))) (.step 3 (.step 31 (.step 48 (.step 21 (.close 28))))))) (.step 3 (.step 21 (.step 31 (.step 48 (.step 50 (.step 28 (.close 53)))))))) (.step 3 (.step 31 (.step 48 (.step 49 (.step 58 (.close 21))))))) (.step 28 (.step 47 (.step 48 (.step 28 (.step 3 (.step 49 (.step 28 (.close 50))))))))) (.step 28 (.step 47 (.step 48 (.step 28 (.step 49 (.step 3 (.close 49)))))))) (.step 3 (.step 28 (.step 29 (.close 28)))))) (.step 21 (.step 28 (.step 58 (.step 28 (.step 3 (.close 21))))))) (.step 3 (.step 28 (.step 29 (.close 28))))) (.step 3 (.step 16 (.step 28 (.step 3 (.step 16 (.step 21 (.step 28 (.close 29))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343338214548610398614813211261605033395849851515813578045129035786223616⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 36 1 (.step 58 (.split 38 1 (.split 42 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 53 1 (.split 57 1 (.step 31 (.step 3 (.close 7))) (.step 28 (.step 31 (.close 3)))) (.step 3 (.step 28 (.step 8 (.step 14 (.close 31)))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 29 (.step 31 (.close 52)))))))) (.step 3 (.step 9 (.step 16 (.step 18 (.step 31 (.close 52))))))) (.step 31 (.step 3 (.step 8 (.step 14 (.close 49))))))) (.step 3 (.step 31 (.close 49)))) (.step 7 (.step 31 (.step 7 (.step 28 (.step 3 (.step 22 (.close 37)))))))) (.step 3 (.step 16 (.step 21 (.step 28 (.step 31 (.step 3 (.close 37))))))))) (.step 7 (.step 31 (.close 37)))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 18 (.step 50 (.split 53 1 (.step 3 (.step 7 (.step 3 (.step 28 (.close 31))))) (.step 3 (.step 8 (.close 18)))))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 28 (.close 31)))))))))) (.step 3 (.step 10 (.step 58 (.reuse 1)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447780699991744600026165202696269343240944523585519616⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 48 (.split 25 1 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 18 (.step 56 (.step 60 (.split 56 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 8 (.close 18))))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52)))) (.step 18 (.step 3 (.step 28 (.close 50)))))) (.step 3 (.step 18 (.close 49)))) (.step 3 (.step 8 (.step 18 (.step 28 (.step 41 (.step 49 (.step 41 (.close 50))))))))) (.step 3 (.step 18 (.step 28 (.close 49)))))))))) (.run (.step 7 (.step 18 (.step 48 (.split 22 1 (.split 25 1 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 18 (.step 56 (.split 56 1 (.split 57 1 (.step 18 (.step 3 (.close 7))) (.step 8 (.step 18 (.close 3)))) (.step 3 (.step 8 (.step 18 (.close 28))))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52)))) (.step 18 (.step 3 (.step 28 (.close 50)))))) (.step 3 (.step 18 (.close 49)))) (.step 3 (.step 8 (.step 18 (.step 28 (.step 41 (.step 49 (.step 41 (.close 50))))))))) (.step 3 (.step 18 (.step 28 (.close 49))))) (.step 7 (.step 18 (.step 7 (.step 8 (.step 3 (.step 14 (.close 20)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2596148429267413814265251385835520, 9797766621314684873895712959598777356905878855469672788529591272835895665089756673988525571854392555862242026866029002939218279279152929040165742273641137506341559316373040782897996679042376895287001088⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 34 1 (.split 36 1 (.split 42 1 (.step 34 (.split 45 1 (.split 55 1 (.split 59 1 (.split 5 0 (.split 16 0 (.step 3 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.step 48 (.step 3 (.close 4))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 14 (.step 3 (.close 12))))) (.step 3 (.step 14 (.step 3 (.close 12)))))) (.step 8 (.step 18 (.step 3 (.close 14))))) (.step 8 (.close 3))) (.step 3 (.step 8 (.step 18 (.step 12 (.close 14)))))) (.step 12 (.step 18 (.step 3 (.step 8 (.step 3 (.step 14 (.close 48)))))))) (.step 3 (.step 4 (.step 8 (.step 18 (.step 12 (.step 14 (.close 48))))))))) (.step 3 (.step 4 (.step 8 (.step 14 (.close 28)))))) (.step 3 (.step 4 (.step 8 (.step 14 (.step 28 (.step 14 (.close 31)))))))) (.step 3 (.step 4 (.step 28 (.step 8 (.step 14 (.close 31))))))))) (.step 8 (.step 3 (.step 12 (.step 48 (.step 60 (.step 3 (.close 12)))))))) (.step 3 (.step 4 (.step 5 (.step 31 (.step 51 (.step 24 (.step 43 (.step 60 (.split 5 0 (.step 43 (.step 14 (.step 3 (.close 28)))) (.step 8 (.close 3)))))))))))) (.step 8 (.step 14 (.step 34 (.step 14 (.step 3 (.step 48 (.step 51 (.split 34 1 (.split 36 1 (.split 42 1 (.step 14 (.close 3)) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2596148429267413814265251385835520, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447783622995019261834597758495202189621249083615215616⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.step 30 (.step 34 (.step 48 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 50 1 (.split 52 1 (.reuse 0) (.run (.step 3 (.step 12 (.step 18 (.step 34 (.step 8 (.step 48 (.close 14))))))))) (.run (.step 3 (.step 18 (.step 34 (.step 48 (.step 8 (.close 14)))))))) (.run (.step 12 (.step 14 (.step 18 (.step 48 (.step 8 (.step 14 (.step 50 (.step 3 (.step 50 (.step 3 (.step 12 (.close 14)))))))))))))) (.run (.step 12 (.step 8 (.step 14 (.step 18 (.step 34 (.close 49)))))))) (.run (.step 3 (.step 4 (.step 5 (.step 14 (.step 31 (.step 41 (.step 49 (.step 50 (.step 60 (.split 16 0 (.split 17 0 (.step 43 (.split 22 0 (.split 56 1 (.step 24 (.step 43 (.step 8 (.step 14 (.step 28 (.step 14 (.step 3 (.close 31)))))))) (.step 28 (.step 24 (.step 41 (.close 3))))) (.step 3 (.step 8 (.step 14 (.close 28)))))) (.step 3 (.step 5 (.step 8 (.step 14 (.close 28)))))) (.step 3 (.step 5 (.step 8 (.step 14 (.close 28))))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 14 (.step 28 (.step 30 (.step 8 (.step 14 (.step 24 (.step 28 (.step 14 (.step 49 (.step 14 (.close 50)))))))))))))))) (.run (.step 3 (.step 14 (.step 18 (.step 3 (.close 8))))))) (.run (.step 3 (.step 14 (.step 18 (.step 3 (.step 8 (.step 3 (.close 14))))))))) (.run (.step 3 (.step 14 (.step 18 (.step 8 (.step 14 (.step 3 (.close 19)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447783622995019261834600293796402646080052077021626368⟩
def references : Fin 2 → Box := ![Part11.root, Part13.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 11 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.step 48 (.split 22 1 (.split 25 1 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 18 (.step 56 (.split 56 1 (.split 57 1 (.step 18 (.step 3 (.close 7))) (.step 8 (.step 18 (.close 3)))) (.step 3 (.step 8 (.step 18 (.close 28))))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52)))) (.step 18 (.step 3 (.step 28 (.step 41 (.close 50))))))) (.step 3 (.step 18 (.close 49)))) (.step 3 (.step 8 (.step 18 (.step 28 (.step 41 (.close 49))))))) (.step 3 (.step 18 (.step 28 (.close 49))))) (.step 7 (.step 18 (.step 7 (.step 8 (.step 3 (.step 14 (.close 19))))))))) (.step 7 (.step 18 (.close 19)))))))) (.reuse 1)) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 11 1 (.split 25 1 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 18 (.split 47 1 (.split 53 1 (.step 3 (.step 7 (.step 3 (.close 28)))) (.step 3 (.close 8))) (.step 3 (.step 18 (.step 28 (.close 31)))))))) (.step 3 (.step 12 (.step 18 (.close 31))))) (.step 3 (.step 28 (.close 31)))) (.step 3 (.close 28))) (.step 3 (.step 8 (.close 14))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2251803034910720, 9797766621314684873895712959598777356905878862334476998638093398744512700837237674326617676364828610130992330386373676877752283103488156157746537450578803229509310760039768077764477592278809320636809216⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 8 (.split 52 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 25 1 (.split 34 1 (.split 36 1 (.split 42 1 (.step 8 (.split 45 1 (.split 55 1 (.split 59 1 (.split 5 2 (.split 16 0 (.step 3 (.step 47 (.step 18 (.split 34 0 (.step 8 (.close 3)) (.step 3 (.step 4 (.close 8))))))) (.step 8 (.close 3))) (.step 8 (.close 3))) (.step 3 (.step 8 (.close 48)))) (.step 18 (.step 3 (.step 30 (.step 8 (.step 3 (.close 48))))))) (.step 3 (.step 4 (.step 8 (.close 48)))))) (.step 3 (.step 4 (.step 8 (.close 28))))) (.step 3 (.step 4 (.step 8 (.step 28 (.close 31)))))) (.step 3 (.step 4 (.step 8 (.step 28 (.step 8 (.close 31))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 10 (.step 28 (.step 3 (.step 5 (.close 8)))))))))))) (.step 8 (.step 3 (.step 8 (.step 31 (.step 47 (.step 48 (.close 60)))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 10 (.step 28 (.step 31 (.step 8 (.step 3 (.step 8 (.step 31 (.step 43 (.step 31 (.step 49 (.step 51 (.close 59))))))))))))))))) (.step 3 (.step 18 (.step 48 (.close 8)))))) (.step 3 (.step 18 (.step 48 (.close 8))))) (.step 3 (.step 18 (.step 34 (.step 48 (.close 8)))))) (.step 8 (.step 47 (.step 48 (.step 8 (.step 3 (.step 49 (.step 8 (.close 50))))))))) (.step 8 (.step 47 (.step 48 (.step 8 (.step 49 (.step 3 (.step 48 (.close 49))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447783622995019261834600293796402646082303876835311616⟩
def references : Fin 2 → Box := ![Part14.root, Part15.root]
def proof : Chunks.Proof 2 := (.split 5 1 (.reuse 0) (.step 3 (.step 31 (.step 30 (.step 47 (.step 48 (.split 11 1 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.reuse 1) (.run (.step 3 (.step 4 (.step 5 (.step 8 (.step 10 (.step 28 (.step 31 (.step 41 (.step 8 (.step 43 (.step 8 (.step 41 (.step 49 (.step 41 (.close 50))))))))))))))))) (.run (.step 3 (.step 8 (.step 11 (.close 8)))))) (.run (.step 3 (.step 8 (.step 11 (.close 8)))))) (.run (.step 3 (.step 8 (.step 11 (.close 8))))))) (.run (.step 8 (.step 34 (.step 48 (.step 8 (.step 3 (.close 12))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part16.excludes
end FiveColour.Packed.ProjectedChunks.Case99
