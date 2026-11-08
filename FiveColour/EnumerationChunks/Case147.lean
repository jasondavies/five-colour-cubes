module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case147
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185308179080118173433856⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544048682091164331652901596069789229568681009490311697678919790461277178950253217472830376031289522707761235293447347690708508018485291312190866584442595549713022039386750976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 25 0 (.step 7 (.step 9 (.step 7 (.step 37 (.close 21))))) (.step 29 (.step 7 (.step 9 (.step 28 (.close 3)))))) (.step 7 (.step 5 (.step 9 (.step 7 (.step 3 (.close 15))))))) (.step 7 (.step 15 (.step 7 (.close 4))))) (.step 7 (.step 18 (.close 15)))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 25 0 (.split 34 0 (.step 7 (.close 9)) (.step 15 (.step 7 (.close 9)))) (.step 29 (.close 3))) (.step 7 (.step 9 (.close 3)))) (.step 7 (.step 9 (.close 3)))) (.step 7 (.step 18 (.step 3 (.step 7 (.close 9))))))) (.step 29 (.step 75 (.split 6 0 (.step 7 (.step 18 (.step 15 (.close 16)))) (.step 9 (.step 3 (.close 7))))))) (.split 72 1 (.split 6 0 (.step 7 (.step 9 (.step 3 (.close 7)))) (.step 3 (.step 70 (.close 7)))) (.step 3 (.step 7 (.step 9 (.close 21)))))) (.split 72 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 12 0 (.split 6 0 (.step 7 (.step 9 (.step 26 (.step 7 (.step 26 (.step 43 (.step 7 (.step 28 (.step 16 (.close 21)))))))))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.step 26 (.step 15 (.step 43 (.step 58 (.close 7))))))) (.step 18 (.step 7 (.step 18 (.step 5 (.close 9)))))) (.step 18 (.step 7 (.step 9 (.step 3 (.close 7)))))) (.step 62 (.close 7))) (.step 9 (.step 18 (.close 26))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459739099333684040314422763363333928265197587993432278272503716389658032955707765325523372830422836166939037588445533725074002132789644429451112622618573807918908440576⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.step 7 (.step 5 (.step 7 (.step 22 (.step 16 (.close 21))))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 21))))) (.step 48 (.split 16 0 (.step 28 (.step 22 (.step 3 (.step 15 (.step 16 (.close 21)))))) (.step 3 (.step 15 (.close 21)))))) (.step 3 (.step 7 (.step 28 (.step 3 (.step 7 (.close 15))))))) (.step 10 (.split 10 0 (.step 48 (.split 12 0 (.split 16 0 (.step 28 (.step 22 (.step 3 (.close 9)))) (.step 3 (.step 9 (.close 21)))) (.step 10 (.close 3)))) (.step 3 (.step 9 (.close 15)))))) (.step 29 (.step 75 (.split 6 0 (.step 59 (.close 3)) (.step 9 (.close 3)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 57 (.step 9 (.step 26 (.step 28 (.step 7 (.step 15 (.close 16)))))))))))) (.run (.step 58 (.step 18 (.step 9 (.step 48 (.step 58 (.close 3))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723026823511497443414970556934235212658789647265345092460553316133232956827146449715919748199299251030963049754647320915202263361566816073205108462244069376⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.split 21 0 (.split 25 0 (.split 34 0 (.step 7 (.step 9 (.step 7 (.step 18 (.step 21 (.close 22)))))) (.step 15 (.step 29 (.step 57 (.close 3))))) (.step 9 (.step 29 (.close 3)))) (.step 7 (.step 9 (.step 18 (.step 3 (.step 7 (.step 3 (.close 22)))))))) (.step 9 (.step 15 (.close 57)))) (.step 9 (.step 26 (.step 29 (.step 57 (.close 3)))))) (.step 3 (.step 57 (.split 12 0 (.step 70 (.close 7)) (.step 9 (.step 7 (.close 21))))))) (.step 9 (.step 26 (.step 57 (.close 3))))) (.step 3 (.step 22 (.step 48 (.step 9 (.close 57)))))) (.step 3 (.step 9 (.step 48 (.step 57 (.close 58)))))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.step 9 (.step 3 (.close 7)))) (.step 3 (.split 21 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.split 72 1 (.split 6 0 (.step 54 (.close 3)) (.step 3 (.step 46 (.close 54)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26))))))) (.step 54 (.step 62 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 57 (.close 7))))))
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
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11031304526203984395224077729546701486925133544052459742698464719678144919619690281947063874380578726072022452243037180911909063670611953424467646274162894849851078197692676784826962559834108120375316111553378520137728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 72 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 12 0 (.split 6 0 (.step 7 (.step 9 (.split 17 0 (.step 7 (.step 21 (.step 43 (.step 7 (.step 16 (.close 22)))))) (.step 7 (.close 4))))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.split 21 0 (.split 25 0 (.step 7 (.step 18 (.step 15 (.step 21 (.step 3 (.step 7 (.close 16))))))) (.step 3 (.step 15 (.step 21 (.step 3 (.step 16 (.close 22))))))) (.step 7 (.step 18 (.close 3)))))) (.step 18 (.step 7 (.step 18 (.step 5 (.close 9)))))) (.step 18 (.step 7 (.step 9 (.step 3 (.close 7)))))) (.split 10 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 7 (.step 15 (.close 16)))))))) (.step 53 (.step 62 (.step 4 (.close 7))))) (.step 5 (.step 57 (.step 9 (.step 21 (.step 53 (.step 3 (.step 15 (.step 16 (.close 26)))))))))) (.step 48 (.step 53 (.step 58 (.close 3))))) (.step 9 (.step 21 (.step 53 (.step 57 (.step 3 (.close 7))))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416615058687603566144160993955633614273257904377779617323514941914626472585026472135979108994225943593654423762089054189365944412798976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 72 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 12 0 (.split 6 0 (.step 7 (.step 9 (.split 17 0 (.step 7 (.step 43 (.step 52 (.step 3 (.step 16 (.step 21 (.close 22))))))) (.step 7 (.close 4))))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.split 21 0 (.split 25 0 (.step 7 (.step 18 (.step 15 (.step 16 (.close 7))))) (.step 3 (.step 15 (.step 16 (.close 4))))) (.step 7 (.step 18 (.close 3)))))) (.step 18 (.step 7 (.step 18 (.step 5 (.close 9)))))) (.step 18 (.step 7 (.step 9 (.step 3 (.close 7)))))) (.split 16 0 (.step 52 (.close 7)) (.step 7 (.close 9)))) (.step 9 (.step 18 (.step 26 (.step 29 (.step 52 (.step 3 (.step 15 (.close 16))))))))) (.step 52 (.step 62 (.step 4 (.close 7))))) (.step 5 (.step 16 (.step 9 (.step 57 (.step 52 (.step 3 (.step 26 (.close 21))))))))) (.step 48 (.step 52 (.step 58 (.close 3))))) (.step 9 (.step 52 (.step 57 (.step 3 (.close 7)))))) (.step 52 (.step 54 (.step 57 (.split 72 1 (.split 16 0 (.step 52 (.close 7)) (.step 7 (.close 9))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))))))) (.step 52 (.split 56 1 (.split 72 1 (.split 16 0 (.step 52 (.step 7 (.close 21))) (.step 18 (.step 27 (.step 52 (.close 4))))) (.step 9 (.step 21 (.step 18 (.step 26 (.step 7 (.step 16 (.close 22)))))))) (.step 5 (.step 9 (.step 16 (.step 21 (.step 52 (.close 22))))))))))
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
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935123878833676862859059191519952000574561785986584128552650300398665533421468607053694306327889033620047433449001189376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 25 0 (.split 49 0 (.step 45 (.step 4 (.close 7))) (.step 7 (.step 26 (.step 16 (.close 21))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 15 (.close 26)))) (.step 29 (.step 75 (.split 21 0 (.step 45 (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 26 (.step 29 (.close 45)))))) (.step 28 (.step 45 (.step 5 (.step 7 (.step 9 (.step 16 (.close 21)))))))) (.step 5 (.step 7 (.step 28 (.step 45 (.step 26 (.step 9 (.step 38 (.close 45))))))))) (.step 26 (.step 29 (.step 57 (.split 55 1 (.split 56 1 (.split 10 0 (.step 26 (.step 57 (.close 3))) (.step 7 (.step 9 (.close 15)))) (.step 10 (.step 22 (.step 26 (.step 45 (.step 3 (.close 16))))))) (.step 3 (.step 9 (.step 26 (.step 39 (.step 45 (.step 16 (.close 21)))))))))))) (.step 18 (.step 26 (.step 29 (.step 38 (.step 40 (.step 57 (.step 58 (.step 9 (.step 7 (.step 15 (.close 26)))))))))))) (.step 26 (.step 57 (.step 58 (.split 50 1 (.step 18 (.step 29 (.step 40 (.step 58 (.step 9 (.step 7 (.step 15 (.step 26 (.step 15 (.close 21)))))))))) (.step 9 (.step 52 (.step 7 (.step 21 (.step 26 (.step 29 (.step 15 (.step 16 (.close 22))))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935123878833676862859059191519952000574561785986584128552650300398665533421468607053694306327889033620047433449001189376⟩
def references : Fin 4 → Box := ![Part2.root, Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 4 := (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.split 51 1 (.reuse 1) (.run (.step 53 (.step 54 (.step 57 (.split 72 1 (.split 10 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))))))))) (.reuse 2)) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.close 9)) (.step 3 (.split 21 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 3 (.step 7 (.close 9)))) (.split 72 1 (.split 6 0 (.split 12 0 (.step 7 (.close 9)) (.step 3 (.step 46 (.close 7)))) (.step 3 (.close 46))) (.step 3 (.step 7 (.close 9))))) (.step 9 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 3 (.step 9 (.close 7)))) (.step 46 (.split 54 1 (.split 56 1 (.split 72 1 (.split 6 0 (.step 54 (.close 3)) (.step 3 (.close 46))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.close 7)))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.step 7 (.close 52)))))))) (.reuse 3))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416615058687603566146623619342908269224025344384038593186332425619030563001773240473744466604944519256867815403019361416916358662193152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.step 7 (.step 5 (.step 7 (.step 21 (.step 16 (.close 22))))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 21))))) (.step 48 (.split 16 0 (.step 28 (.step 48 (.step 21 (.step 37 (.step 3 (.close 22)))))) (.step 3 (.step 15 (.close 21)))))) (.step 3 (.step 7 (.step 28 (.step 3 (.step 7 (.close 15))))))) (.step 10 (.split 10 0 (.step 48 (.split 12 0 (.split 16 0 (.step 28 (.step 48 (.step 9 (.step 3 (.close 9))))) (.step 3 (.step 9 (.close 21)))) (.step 10 (.close 3)))) (.step 3 (.step 9 (.close 15)))))) (.step 29 (.step 38 (.step 75 (.split 6 0 (.step 41 (.close 3)) (.step 9 (.close 3))))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 58 (.close 3))))) (.step 28 (.step 58 (.step 59 (.step 3 (.step 5 (.step 7 (.step 3 (.step 9 (.close 16)))))))))) (.step 5 (.step 28 (.step 41 (.close 58))))) (.step 3 (.step 21 (.step 48 (.step 57 (.step 10 (.step 28 (.step 38 (.step 3 (.step 26 (.step 3 (.close 41)))))))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.step 28 (.step 26 (.close 41))))))))) (.step 5 (.step 21 (.step 58 (.step 9 (.close 26)))))) (.step 5 (.step 48 (.step 16 (.step 57 (.step 58 (.step 3 (.step 9 (.close 26))))))))))
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
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203979496340767072204264539074732142412855220466682097812186882874655189202742495293581668027368993580913270565841225350043646038336595552687327352865228531915952667412328670021282633280728196626914559918080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 25 0 (.split 49 0 (.step 39 (.step 4 (.close 7))) (.step 7 (.step 22 (.step 16 (.step 26 (.step 15 (.close 16))))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 15 (.step 22 (.step 15 (.close 26)))))) (.step 29 (.step 75 (.split 21 0 (.split 49 0 (.step 39 (.step 3 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 22 (.step 26 (.step 29 (.step 37 (.close 21)))))))) (.step 22 (.step 28 (.step 39 (.step 3 (.close 9)))))) (.step 5 (.step 7 (.step 28 (.step 58 (.step 9 (.close 15))))))) (.step 22 (.step 29 (.step 57 (.step 3 (.close 7)))))) (.step 18 (.step 22 (.step 29 (.step 38 (.step 40 (.step 9 (.step 57 (.step 7 (.step 26 (.step 37 (.close 26)))))))))))) (.step 22 (.step 57 (.step 58 (.step 55 (.step 9 (.step 7 (.step 26 (.step 37 (.step 26 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52))))))))))))))) (.step 45 (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 9 (.step 22 (.step 26 (.step 29 (.step 39 (.close 37)))))))) (.step 7 (.step 9 (.step 29 (.step 38 (.step 39 (.step 45 (.step 37 (.close 53))))))))) (.step 7 (.step 9 (.step 29 (.step 57 (.step 39 (.step 38 (.step 45 (.close 52))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414973595399782259359350968109242584605011756964535318834327339450921577348216647801732944212862691969073152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 75 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.step 29 (.split 6 0 (.step 38 (.step 7 (.step 18 (.step 15 (.close 16))))) (.step 9 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 7 (.step 29 (.step 37 (.close 22))))))))) (.step 3 (.step 29 (.step 38 (.step 48 (.step 58 (.step 59 (.step 3 (.close 9))))))))) (.step 3 (.step 18 (.step 29 (.step 38 (.step 9 (.close 16))))))) (.step 9 (.step 21 (.step 29 (.step 57 (.step 3 (.close 7)))))))) (.step 3 (.step 18 (.step 53 (.step 55 (.step 9 (.step 7 (.step 26 (.step 38 (.close 54)))))))))) (.step 9 (.step 21 (.step 18 (.step 21 (.close 26)))))) (.step 9 (.step 53 (.step 57 (.step 58 (.step 75 (.split 51 1 (.split 59 1 (.step 18 (.step 21 (.step 29 (.step 38 (.step 3 (.step 7 (.close 26))))))) (.step 26 (.step 18 (.step 21 (.step 29 (.step 37 (.step 22 (.close 38)))))))) (.step 3 (.step 7 (.close 52)))))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 21 (.step 29 (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732142412855220466682097812186882874655189202742492585896419862510729925327825834519996127628025269584262431361434646076471570228608624329261386210212594793506234855807520866304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 25 0 (.split 49 0 (.split 72 1 (.split 50 0 (.split 17 0 (.step 37 (.step 4 (.close 7))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 21)))) (.step 29 (.step 37 (.step 3 (.close 7))))) (.step 7 (.step 15 (.step 16 (.step 21 (.step 16 (.close 22))))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 15 (.step 22 (.close 26))))) (.step 29 (.step 75 (.split 21 0 (.step 37 (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 15 (.step 26 (.step 16 (.step 28 (.step 21 (.close 22))))))))) (.step 28 (.step 37 (.step 3 (.step 7 (.close 9)))))) (.step 5 (.step 7 (.step 28 (.step 37 (.step 9 (.step 26 (.step 37 (.close 21))))))))) (.step 15 (.step 29 (.step 57 (.step 59 (.step 75 (.split 55 1 (.split 16 0 (.step 57 (.step 3 (.close 7))) (.step 7 (.step 9 (.close 21)))) (.step 3 (.step 9 (.step 16 (.close 37))))))))))) (.step 15 (.step 18 (.step 29 (.step 38 (.step 40 (.step 9 (.step 7 (.step 37 (.step 26 (.step 52 (.step 39 (.step 45 (.close 53)))))))))))))) (.step 15 (.step 16 (.step 57 (.step 58 (.step 52 (.step 7 (.step 9 (.step 21 (.close 26)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524437163561525551523153049289878610032553483862239440022541140087827962678325090355963576188928⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 37 (.split 49 1 (.split 50 1 (.step 45 (.step 29 (.step 37 (.step 7 (.step 9 (.step 15 (.step 26 (.close 37)))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.step 45 (.close 52))))))))))) (.step 7 (.step 9 (.step 15 (.step 16 (.step 37 (.step 38 (.close 52))))))))))) (.run (.step 16 (.step 28 (.step 37 (.step 38 (.step 41 (.step 58 (.step 37 (.step 3 (.close 9))))))))))) (.run (.step 37 (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 9 (.step 15 (.step 22 (.step 26 (.step 29 (.close 37)))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.step 21 (.step 22 (.step 26 (.step 39 (.close 52))))))))))) (.step 7 (.step 9 (.step 15 (.step 16 (.step 37 (.step 38 (.close 52))))))))))) (.run (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500249432784896, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569129900084964207831971393854518999119738677950872741378442793402236928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 29 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.step 29 (.split 6 0 (.split 21 0 (.split 34 0 (.split 36 0 (.split 16 0 (.step 58 (.step 3 (.close 7))) (.step 3 (.step 4 (.close 7)))) (.step 7 (.step 16 (.close 21)))) (.step 7 (.step 15 (.step 16 (.close 21))))) (.step 3 (.close 5))) (.step 10 (.step 29 (.step 3 (.close 9)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 9 (.step 26 (.step 29 (.step 3 (.step 16 (.step 3 (.close 21))))))))) (.step 28 (.step 5 (.step 9 (.step 3 (.close 26)))))) (.step 5 (.step 28 (.step 9 (.step 3 (.close 26)))))) (.step 3 (.step 29 (.step 3 (.step 9 (.step 28 (.close 16))))))) (.step 3 (.step 7 (.step 9 (.step 28 (.close 26)))))) (.step 5 (.step 9 (.step 57 (.step 58 (.step 3 (.close 26))))))) (.step 5 (.step 48 (.step 9 (.step 16 (.step 57 (.step 58 (.step 3 (.close 26))))))))) (.step 3 (.step 7 (.step 9 (.close 10))))) (.step 7 (.step 28 (.step 29 (.step 3 (.close 7)))))) (.step 10 (.step 28 (.split 49 1 (.step 28 (.step 10 (.step 21 (.step 28 (.step 5 (.step 21 (.step 3 (.close 26)))))))) (.step 5 (.step 9 (.step 16 (.step 21 (.step 28 (.close 26)))))))))) (.step 7 (.step 28 (.step 29 (.step 3 (.close 7)))))) (.step 7 (.step 16 (.step 28 (.step 5 (.step 7 (.step 9 (.step 15 (.close 16))))))))) (.step 3 (.close 7)))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131585081630904746958560542961937846655780272399150164222862377877504⟩
def references : Fin 6 → Box := ![Part6.root, Part7.root, Part8.root, Part9.root, Part11.root, Part12.root]
def proof : Chunks.Proof 6 := (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.reuse 0) (.split 42 1 (.split 43 1 (.reuse 1) (.run (.step 3 (.step 7 (.step 9 (.close 10)))))) (.run (.step 7 (.step 38 (.step 28 (.step 45 (.step 76 (.step 41 (.step 58 (.split 10 0 (.split 12 0 (.step 45 (.step 3 (.close 9))) (.step 10 (.step 37 (.step 38 (.step 3 (.step 21 (.step 26 (.step 3 (.close 22))))))))) (.step 3 (.step 7 (.step 15 (.step 9 (.close 22)))))))))))))))) (.step 7 (.split 38 1 (.reuse 2) (.run (.step 38 (.step 28 (.step 45 (.split 49 1 (.step 39 (.step 41 (.step 58 (.step 39 (.step 3 (.step 9 (.step 16 (.close 21)))))))) (.step 5 (.step 7 (.step 10 (.step 16 (.step 21 (.step 22 (.step 38 (.close 39)))))))))))))))) (.reuse 3)) (.reuse 4)) (.run (.step 7 (.step 18 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 18 (.step 53 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))))) (.step 3 (.close 7))) (.step 3 (.step 18 (.close 7)))))))) (.reuse 5)) (.run (.step 7 (.step 18 (.split 25 1 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 4 (.step 9 (.close 18))))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 26 (.step 55 (.step 27 (.close 52))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 18 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 18))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462068164602697931120404006285255135015797802725726486528⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 25 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.step 18 (.step 4 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 43 (.close 4)) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 4 (.step 7 (.step 9 (.step 7 (.step 17 (.close 26))))))) (.step 4 (.step 9 (.close 57)))))) (.step 3 (.close 4))) (.step 3 (.step 4 (.close 5)))) (.step 3 (.step 7 (.step 9 (.step 26 (.close 54)))))) (.step 3 (.step 4 (.step 9 (.step 18 (.step 26 (.close 53))))))) (.step 3 (.step 4 (.step 9 (.step 18 (.close 52)))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 4 (.step 9 (.step 15 (.close 26))))))) (.step 3 (.step 4 (.step 5 (.step 21 (.step 3 (.step 4 (.close 22)))))))) (.step 3 (.step 7 (.step 22 (.step 4 (.step 9 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 9 (.step 7 (.step 18 (.step 26 (.close 38)))))))) (.step 3 (.step 7 (.step 37 (.step 4 (.close 9)))))) (.step 3 (.step 4 (.step 5 (.step 28 (.step 3 (.close 4)))))))))))
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

namespace Part15
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195295895165062208669205892950056583036928⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 22 1 (.split 25 1 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 4 (.step 9 (.close 18))))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 22 (.step 55 (.step 27 (.close 52))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 18 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 18)))))) (.step 7 (.step 18 (.split 25 1 (.step 7 (.close 52)) (.step 4 (.step 5 (.close 28))))))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 25 1 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 4 (.step 9 (.close 18))))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 21 (.step 42 (.step 52 (.close 7))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 18 (.close 7))))) (.step 3 (.step 4 (.step 5 (.step 7 (.close 18)))))) (.step 7 (.step 18 (.split 25 1 (.step 7 (.close 52)) (.step 4 (.step 5 (.close 28))))))) (.step 7 (.step 18 (.step 19 (.split 25 1 (.step 7 (.close 52)) (.step 4 (.step 5 (.close 28))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459739099333687395542992527424274267832346969225240482345527196258400969721455414810278306553437701015866930363670158716705370040442179138883922742680806548378197426176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 25 0 (.split 35 0 (.split 49 0 (.split 34 0 (.step 7 (.step 9 (.step 7 (.close 15)))) (.step 15 (.close 3))) (.step 9 (.step 7 (.step 15 (.close 3))))) (.step 9 (.step 15 (.close 3)))) (.step 9 (.step 29 (.close 3)))) (.step 9 (.step 7 (.step 15 (.close 3))))) (.step 9 (.step 15 (.step 3 (.step 7 (.step 21 (.close 22))))))) (.step 3 (.step 15 (.split 21 0 (.split 34 0 (.split 35 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 3 (.step 16 (.step 22 (.step 15 (.step 48 (.step 9 (.step 15 (.step 3 (.close 26)))))))))) (.step 3 (.step 9 (.step 48 (.step 15 (.close 58)))))) (.step 3 (.step 15 (.step 57 (.step 62 (.step 70 (.split 6 0 (.step 7 (.close 9)) (.step 9 (.close 7))))))))) (.step 9 (.step 15 (.step 21 (.step 15 (.close 53)))))) (.step 9 (.step 15 (.step 16 (.step 15 (.close 52)))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 15 (.step 26 (.step 29 (.split 55 1 (.split 56 1 (.split 10 0 (.step 26 (.step 37 (.split 21 0 (.step 45 (.step 7 (.close 9))) (.step 3 (.step 7 (.close 9)))))) (.step 7 (.step 9 (.close 15)))) (.step 10 (.step 16 (.step 22 (.step 26 (.step 15 (.close 3))))))) (.step 3 (.step 9 (.step 15 (.step 22 (.close 26))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185307026158613566586880⟩
def references : Fin 2 → Box := ![Part15.root, Part16.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 25 1 (.step 57 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.reuse 1) (.run (.step 3 (.step 16 (.step 21 (.step 48 (.step 15 (.step 10 (.step 28 (.step 41 (.step 15 (.step 3 (.step 15 (.close 26)))))))))))))) (.run (.step 7 (.step 15 (.step 22 (.step 29 (.step 57 (.step 37 (.step 39 (.step 22 (.step 75 (.split 55 1 (.split 21 0 (.step 39 (.step 7 (.step 9 (.close 15)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.step 15 (.close 26)))))))))))))))) (.run (.step 9 (.step 15 (.step 21 (.step 29 (.close 38))))))) (.run (.step 7 (.step 15 (.step 29 (.close 37)))))) (.run (.step 3 (.step 7 (.step 18 (.step 9 (.close 15)))))))) (.run (.step 3 (.step 16 (.step 29 (.step 9 (.step 15 (.step 3 (.step 15 (.step 21 (.close 28))))))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 18 (.step 9 (.close 15))))))))) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.close 7))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 18 (.step 9 (.close 15))))))))) (.run (.step 3 (.step 4 (.step 7 (.step 18 (.step 9 (.close 15))))))))) (.run (.step 7 (.step 18 (.split 12 1 (.split 25 1 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.close 15)))) (.step 18 (.step 7 (.step 9 (.step 7 (.close 15)))))) (.step 18 (.step 52 (.close 7))))) (.step 3 (.close 7))) (.step 3 (.step 18 (.close 7)))) (.step 3 (.close 7))) (.step 3 (.step 15 (.step 3 (.close 7)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2305843011361177600, 11031304526203984395224077729546701486925133544052459739099333687395542992527424274267832346969225240484808154934371377055054372626371229296290604166177192890095824977045523341455928295692388211471514098585337098928128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 9 (.split 42 1 (.split 43 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 67 1 (.split 25 0 (.split 51 0 (.split 67 0 (.split 21 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 9 (.close 3)) (.step 7 (.step 9 (.close 3)))) (.step 9 (.close 3))) (.step 15 (.step 3 (.close 7)))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.close 3))) (.step 3 (.split 34 0 (.split 36 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 3 (.step 10 (.step 3 (.close 9))))) (.step 3 (.step 9 (.close 3)))) (.step 3 (.step 57 (.step 70 (.split 21 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 9 (.step 10 (.step 29 (.split 21 0 (.split 34 0 (.step 26 (.split 49 0 (.step 45 (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 15 (.step 26 (.step 37 (.close 45))))) (.step 7 (.close 9))))))))) (.step 3 (.step 10 (.step 3 (.close 9))))) (.step 7 (.step 9 (.step 10 (.step 29 (.step 57 (.step 45 (.split 21 0 (.split 49 0 (.step 39 (.step 3 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9)))))))))) (.step 9 (.close 3))) (.step 7 (.step 9 (.step 10 (.step 15 (.step 29 (.step 39 (.step 45 (.split 21 0 (.split 49 0 (.split 50 0 (.step 37 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185308179080118173433856⟩
def references : Fin 2 → Box := ![Part17.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 6 1 (.reuse 0) (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 25 1 (.step 57 (.split 30 1 (.reuse 1) (.run (.step 3 (.step 7 (.step 9 (.step 3 (.step 7 (.close 9))))))))) (.run (.step 3 (.step 9 (.step 10 (.step 3 (.close 9))))))) (.run (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.close 9)))))))) (.run (.step 4 (.step 7 (.close 9))))) (.run (.step 3 (.step 4 (.step 7 (.step 11 (.close 9))))))) (.run (.step 3 (.step 4 (.step 7 (.step 11 (.close 9))))))) (.run (.step 9 (.step 21 (.step 9 (.step 3 (.close 7))))))) (.run (.step 3 (.step 7 (.step 9 (.step 3 (.step 7 (.close 9)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part19

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part19.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case147

namespace FiveColour.Packed.EnumerationChunks.Projected.Case147
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 34 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 34 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 34 0).upper i := by decide +kernel
lemma budget_model : (⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 34), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 34) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 34 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 34 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 34) (Archive.root 34) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 34 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 34 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case147

namespace FiveColour.Packed.EnumerationChunks.Case147
def root : Box := Archive.root 34
def families : Fin 78 → List Cut := Enumeration.families 34
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case147.original_covered points
end FiveColour.Packed.EnumerationChunks.Case147
