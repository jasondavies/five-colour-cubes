module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case15
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725704980689733589940654927499936733694823693447950867335537345167360⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908284911715838913447, 5789234131004114107589341883129531770018971867894994468411955019690277647889009051559687699629171582451667236722394843212749036780556536815853887133914354043305755671668584339630966863574716854696998678016360900365014533121, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459739099333684040314422763363333928265197587993432278272503716389658032955707765325523374683096263963998164365581293864080527785109399079700137253939917935628494307328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.step 18 (.step 9 (.step 7 (.step 28 (.close 15)))))) (.split 16 0 (.split 21 0 (.split 26 0 (.step 7 (.close 9)) (.step 9 (.step 3 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 3))))) (.step 29 (.step 7 (.step 18 (.step 9 (.step 15 (.close 16))))))) (.step 7 (.step 3 (.step 7 (.close 9))))) (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.step 18 (.step 26 (.step 7 (.step 28 (.close 15))))))) (.step 9 (.step 7 (.step 18 (.close 26))))) (.step 7 (.step 3 (.step 7 (.step 9 (.close 21))))))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 4 0 (.split 10 0 (.step 28 (.step 3 (.step 5 (.step 7 (.step 15 (.close 16)))))) (.step 3 (.step 7 (.close 15)))) (.step 3 (.step 7 (.close 15)))) (.step 10 (.step 48 (.step 28 (.step 3 (.close 9)))))) (.step 28 (.step 75 (.step 3 (.step 9 (.close 15)))))) (.step 3 (.close 7))) (.step 5 (.step 9 (.step 7 (.step 22 (.step 26 (.step 3 (.step 28 (.close 15)))))))))) (.step 58 (.step 18 (.step 9 (.step 3 (.step 18 (.step 15 (.close 26)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030096902105339556840570123932040257941863907391135525342799424601052960944707063902428528518354070880339647857100795027922827847993279942289500357525504⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 55 1 (.split 59 1 (.split 67 1 (.split 56 1 (.split 72 1 (.split 4 0 (.step 57 (.step 7 (.step 18 (.close 16)))) (.step 3 (.step 7 (.step 9 (.close 15))))) (.step 9 (.step 26 (.step 29 (.step 7 (.close 15)))))) (.step 22 (.step 9 (.step 28 (.step 3 (.step 15 (.step 26 (.close 15)))))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 9 (.step 26 (.close 57)))) (.step 3 (.step 9 (.step 48 (.step 57 (.close 3)))))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.step 7 (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 54 (.step 3 (.step 7 (.step 9 (.close 21)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 9 (.step 7 (.step 21 (.close 26)))))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 4 0 (.split 10 0 (.step 62 (.split 67 1 (.step 9 (.step 7 (.step 18 (.step 21 (.step 7 (.step 15 (.step 26 (.close 15)))))))) (.step 7 (.step 3 (.step 7 (.step 9 (.close 21))))))) (.step 7 (.step 18 (.step 52 (.step 7 (.close 9)))))) (.step 7 (.step 18 (.step 53 (.step 62 (.step 7 (.close 9))))))) (.step 53 (.close 7))) (.step 5 (.step 9 (.step 21 (.step 7 (.step 22 (.step 53 (.step 3 (.close 15))))))))) (.step 48 (.step 53 (.step 3 (.step 7 (.step 21 (.close 22))))))) (.step 9 (.step 21 (.step 53 (.step 7 (.step 18 (.step 55 (.close 57))))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617831357297686959020572369817757356961340814854993141942785822004146333111413521741155494284367487882770177931336937065482972823552⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.reuse 0) (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 4 0 (.split 10 0 (.step 62 (.split 67 1 (.step 9 (.step 7 (.step 18 (.split 25 0 (.step 7 (.step 16 (.step 26 (.step 15 (.close 16))))) (.step 3 (.step 7 (.step 16 (.step 21 (.step 26 (.close 21)))))))))) (.step 7 (.step 3 (.step 7 (.step 9 (.close 21))))))) (.step 7 (.step 18 (.step 52 (.step 3 (.close 4)))))) (.step 7 (.step 18 (.step 52 (.step 62 (.step 7 (.close 9))))))) (.step 52 (.close 7))) (.step 5 (.step 9 (.step 16 (.step 7 (.step 22 (.step 52 (.step 3 (.step 21 (.close 26)))))))))) (.step 48 (.step 52 (.step 3 (.step 22 (.close 26)))))) (.step 9 (.step 52 (.step 57 (.step 3 (.close 7)))))) (.step 52 (.step 7 (.close 21)))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.step 9 (.split 55 1 (.split 56 1 (.split 6 0 (.step 7 (.close 9)) (.step 3 (.step 9 (.close 7)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9))))) (.step 46 (.step 9 (.step 7 (.close 9))))) (.step 9 (.step 7 (.close 46)))) (.step 9 (.step 7 (.step 27 (.close 46)))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341459064137514009958959958259550426456143716329702193824302763437785604977949112169968554595248619111572836450304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 4 0 (.split 10 0 (.step 28 (.step 3 (.step 5 (.step 7 (.step 15 (.close 16)))))) (.step 3 (.step 7 (.close 15)))) (.step 3 (.step 7 (.close 15)))) (.step 10 (.step 48 (.step 28 (.step 3 (.close 9)))))) (.step 28 (.step 38 (.step 3 (.step 9 (.close 15)))))) (.step 3 (.close 7))) (.step 5 (.step 9 (.step 7 (.step 21 (.step 26 (.step 3 (.step 28 (.close 15))))))))) (.step 28 (.step 41 (.step 3 (.step 5 (.step 3 (.step 7 (.step 3 (.close 9))))))))) (.step 3 (.step 21 (.step 48 (.step 9 (.step 28 (.step 41 (.step 57 (.close 3))))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 9 (.step 21 (.step 7 (.close 21)))))) (.step 5 (.step 9 (.step 16 (.step 57 (.step 58 (.close 3))))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 28 (.step 38 (.step 41 (.step 45 (.step 3 (.step 9 (.step 16 (.close 21))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461412680096783792187847740147215793171092012251102144173470728757137186974226778412018294247003880275868385280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 54 1 (.step 39 (.step 7 (.step 9 (.step 16 (.close 21))))) (.step 22 (.step 9 (.step 29 (.step 7 (.step 15 (.step 26 (.close 15)))))))) (.step 7 (.step 21 (.step 9 (.close 15))))) (.step 7 (.step 9 (.step 22 (.step 26 (.step 28 (.step 29 (.step 15 (.close 16))))))))) (.step 22 (.step 28 (.step 39 (.close 3))))) (.step 5 (.step 7 (.step 28 (.step 22 (.step 9 (.close 39))))))) (.step 7 (.step 9 (.step 21 (.step 22 (.step 29 (.step 26 (.step 37 (.close 26))))))))) (.step 18 (.step 22 (.step 29 (.step 40 (.step 9 (.step 7 (.step 22 (.step 37 (.step 39 (.close 21))))))))))) (.step 39 (.step 7 (.step 9 (.step 21 (.step 22 (.step 26 (.step 29 (.step 15 (.step 37 (.close 39))))))))))) (.step 28 (.step 38 (.step 39 (.step 5 (.step 7 (.step 9 (.step 21 (.step 16 (.close 22))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414973595399782259359350968111095258032808816091312454594466345976573897102866896826364265556990401554939904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 4 0 (.step 29 (.step 7 (.step 18 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 9 (.close 15))))) (.step 9 (.step 7 (.step 18 (.step 21 (.step 26 (.step 7 (.step 28 (.close 15))))))))) (.step 3 (.step 29 (.step 38 (.step 3 (.step 9 (.close 15))))))) (.step 3 (.step 18 (.step 29 (.step 9 (.step 21 (.step 37 (.step 22 (.step 26 (.step 15 (.close 16))))))))))) (.step 9 (.step 21 (.step 29 (.step 57 (.close 3)))))) (.step 9 (.step 21 (.step 7 (.close 21))))) (.step 9 (.step 53 (.step 29 (.step 18 (.step 21 (.step 52 (.step 3 (.step 16 (.step 22 (.close 26)))))))))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 21 (.step 29 (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524437163561525553375826477086937736809689244001245965674860894738076987309646434483673162055680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 54 1 (.split 6 0 (.split 21 0 (.split 25 0 (.split 26 0 (.step 7 (.step 15 (.step 16 (.close 21)))) (.step 28 (.step 7 (.close 15)))) (.step 28 (.step 7 (.close 15)))) (.step 3 (.step 7 (.step 15 (.close 22))))) (.step 29 (.step 37 (.step 3 (.close 7))))) (.step 15 (.step 29 (.step 37 (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 15 (.step 26 (.step 16 (.step 21 (.step 28 (.close 21))))))))) (.step 28 (.step 37 (.close 3)))) (.step 5 (.step 7 (.step 28 (.step 37 (.close 9)))))) (.step 7 (.step 9 (.step 15 (.step 21 (.step 29 (.close 37))))))) (.step 15 (.step 7 (.step 9 (.step 16 (.step 26 (.step 21 (.step 26 (.close 29))))))))) (.step 37 (.step 7 (.close 9)))) (.step 16 (.step 28 (.step 37 (.step 5 (.step 7 (.step 9 (.close 21)))))))) (.step 37 (.step 7 (.close 9)))) (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889714586173329685272964986055608646157263431285528775366322267541946989419692032⟩
def references : Fin 5 → Box := ![Part2.root, Part3.root, Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 5 := (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 72 1 (.step 45 (.step 29 (.step 7 (.close 9)))) (.step 26 (.step 29 (.step 45 (.close 3))))) (.step 7 (.step 21 (.step 9 (.close 15))))) (.step 7 (.step 9 (.step 26 (.step 29 (.step 15 (.step 37 (.close 21)))))))) (.step 28 (.step 45 (.close 3)))) (.step 5 (.step 7 (.step 28 (.step 26 (.step 9 (.close 45))))))) (.step 7 (.step 9 (.step 21 (.step 26 (.step 29 (.step 37 (.step 22 (.step 37 (.close 45)))))))))) (.step 18 (.step 26 (.step 29 (.step 40 (.step 9 (.step 7 (.step 26 (.step 37 (.step 45 (.close 21)))))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.run (.step 7 (.step 18 (.step 7 (.step 9 (.close 18))))))) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 49 1 (.split 50 1 (.step 29 (.split 54 1 (.split 59 1 (.split 51 1 (.step 29 (.close 7)) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 9 (.step 7 (.step 18 (.step 26 (.step 7 (.close 28))))))) (.step 9 (.step 29 (.step 7 (.close 26)))))) (.step 9 (.step 27 (.step 21 (.step 18 (.step 29 (.step 3 (.close 26)))))))) (.step 9 (.step 27 (.step 57 (.step 58 (.step 62 (.step 18 (.step 29 (.close 26))))))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725703335185176267236573594266577355956278321661792852477182037983232⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 25 1 (.reuse 0) (.run (.step 7 (.step 29 (.split 34 1 (.split 36 1 (.split 38 1 (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.step 28 (.split 51 1 (.step 29 (.split 54 1 (.split 67 1 (.step 58 (.step 3 (.step 7 (.step 9 (.step 3 (.step 7 (.close 15))))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.step 15 (.close 28)))))) (.step 3 (.step 7 (.step 9 (.close 21)))))) (.step 5 (.step 9 (.step 29 (.step 21 (.close 53)))))) (.step 5 (.step 9 (.step 16 (.step 57 (.step 58 (.close 3))))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 28 (.step 5 (.step 9 (.close 16))))))) (.step 10 (.step 28 (.step 5 (.step 9 (.step 16 (.step 3 (.close 21)))))))) (.step 7 (.step 28 (.step 5 (.step 9 (.close 16)))))) (.step 7 (.step 16 (.step 28 (.close 9))))))))) (.run (.step 7 (.step 18 (.step 7 (.step 4 (.step 9 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459739099333687395542992527424274267832346969225240484808154934371377055054372626371229299997760273165644209203589793964297141320776477731282679463145062475336075182080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 56 1 (.split 72 1 (.split 4 0 (.step 15 (.step 7 (.step 9 (.step 7 (.step 15 (.close 3)))))) (.step 3 (.step 7 (.step 9 (.close 15))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 16 (.step 22 (.step 9 (.step 15 (.close 3)))))) (.step 3 (.step 7 (.step 9 (.close 15))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 3 (.step 9 (.step 15 (.step 48 (.step 15 (.step 3 (.step 22 (.close 26))))))))) (.step 3 (.step 9 (.step 7 (.close 15))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 9 (.step 15 (.step 7 (.step 18 (.step 3 (.step 7 (.step 21 (.step 22 (.close 26)))))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 15 (.step 26 (.step 29 (.step 37 (.step 7 (.step 9 (.close 15))))))))) (.step 3 (.step 15 (.step 16 (.step 21 (.step 28 (.step 41 (.step 48 (.step 9 (.step 15 (.step 3 (.close 22)))))))))))) (.step 7 (.step 15 (.step 22 (.step 29 (.step 37 (.step 22 (.step 39 (.step 7 (.step 9 (.close 15))))))))))) (.step 9 (.step 15 (.step 21 (.step 29 (.close 38)))))) (.step 7 (.step 15 (.step 3 (.step 7 (.step 21 (.close 22))))))) (.step 9 (.step 15 (.step 28 (.step 7 (.step 18 (.step 21 (.step 22 (.close 26))))))))) (.step 3 (.step 9 (.step 16 (.step 28 (.step 15 (.step 28 (.step 3 (.close 15))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725704980689733589940654927499936733694823693447949714412933226692608⟩
def references : Fin 2 → Box := ![Part8.root, Part9.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 25 1 (.step 4 (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 36 1 (.step 4 (.split 38 1 (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 4 (.step 7 (.close 9))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.step 17 (.close 26)))))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.step 18 (.close 26)))))))) (.step 7 (.step 4 (.close 9))))) (.step 3 (.close 4)))) (.step 7 (.step 4 (.step 9 (.step 15 (.close 26)))))) (.step 3 (.step 7 (.close 9)))) (.step 4 (.step 7 (.step 9 (.step 18 (.step 15 (.close 26))))))) (.step 7 (.close 37))) (.step 4 (.step 7 (.step 9 (.step 7 (.step 18 (.close 29))))))))) (.step 3 (.step 4 (.step 3 (.step 5 (.step 3 (.close 22))))))))))) (.run (.step 7 (.step 18 (.step 7 (.close 18)))))) (.run (.step 7 (.step 18 (.step 7 (.close 18)))))) (.split 16 1 (.split 17 1 (.step 57 (.step 18 (.split 21 1 (.reuse 1) (.run (.step 4 (.step 9 (.step 7 (.step 15 (.close 7))))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.close 18))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.close 18)))))))) (.run (.step 7 (.step 18 (.split 12 1 (.step 7 (.step 18 (.step 7 (.step 9 (.step 15 (.close 18)))))) (.step 3 (.step 15 (.close 3))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725704980689733589940654927499936733694823693447950867335537345167360⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.split 4 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 12 1 (.step 7 (.step 18 (.step 7 (.step 9 (.close 18))))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 7 (.close 15))))))))))) (.run (.split 4 1 (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.step 9 (.step 7 (.step 18 (.split 21 1 (.split 25 1 (.step 9 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 4 0 (.split 25 0 (.split 51 0 (.step 9 (.close 3)) (.step 3 (.step 7 (.close 9)))) (.step 9 (.close 3))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 10 (.close 3)))) (.step 3 (.step 9 (.close 7)))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 10 (.step 26 (.step 29 (.step 7 (.close 9))))))) (.step 3 (.step 10 (.close 3)))) (.step 7 (.step 10 (.step 29 (.step 39 (.step 7 (.close 9))))))) (.step 7 (.step 10 (.step 15 (.step 29 (.step 37 (.step 3 (.close 7))))))))) (.step 3 (.step 9 (.close 10)))) (.step 4 (.step 7 (.close 9))))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.close 9))))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.close 9))))))) (.step 9 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 9 (.close 3)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part11.excludes
end FiveColour.Packed.ProjectedChunks.Case15
