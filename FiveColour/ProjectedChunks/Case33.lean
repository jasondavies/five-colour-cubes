module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case33
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379522046674022425821715511990081822916608⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908284911715872467959, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691003773395856797335276228224145743890145446228163347693427359436041631246125966867020082117046907873927859536897, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464719674871529011794140077050684683751126919805810196994116122425772302515819629913835895682350818748816504040035877791514899964739254647634384955031817289728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.split 12 0 (.step 7 (.step 18 (.step 16 (.close 21)))) (.step 18 (.step 9 (.step 7 (.step 15 (.step 16 (.close 21)))))))) (.step 29 (.step 7 (.step 18 (.step 26 (.close 15)))))) (.step 7 (.step 3 (.step 7 (.step 9 (.close 21)))))) (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.step 26 (.split 12 0 (.step 7 (.step 18 (.step 16 (.close 21)))) (.step 18 (.step 15 (.step 26 (.step 7 (.step 16 (.close 21)))))))))) (.step 9 (.step 18 (.close 26)))) (.step 7 (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 3 (.step 7 (.step 22 (.step 16 (.close 21))))) (.step 22 (.step 3 (.step 15 (.step 16 (.close 21)))))) (.step 3 (.step 7 (.close 15)))) (.step 28 (.step 75 (.step 3 (.step 15 (.close 16)))))) (.step 3 (.close 7))) (.step 5 (.step 7 (.step 9 (.step 22 (.step 26 (.step 3 (.step 28 (.step 15 (.close 16))))))))))) (.step 58 (.step 18 (.step 9 (.step 48 (.step 7 (.step 18 (.step 29 (.step 15 (.close 26)))))))))) (.step 57 (.step 58 (.split 56 1 (.step 18 (.step 9 (.close 57))) (.step 3 (.step 22 (.step 48 (.step 9 (.close 57))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030096902105339556840570123932040257941863907391135525342799424601052960944705254651034195452800577583698887108540587684412427214180162264616772596400128⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.step 7 (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 54 (.close 3))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 54 (.step 7 (.step 9 (.step 21 (.close 26))))))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.step 62 (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.split 12 0 (.step 7 (.step 18 (.step 21 (.close 16)))) (.step 18 (.step 15 (.step 21 (.step 7 (.close 16)))))))) (.step 9 (.step 18 (.step 21 (.step 7 (.step 26 (.close 15))))))) (.step 7 (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))))) (.step 7 (.step 18 (.step 52 (.step 7 (.step 9 (.close 15))))))) (.step 53 (.close 7))) (.step 5 (.step 9 (.step 21 (.step 7 (.step 22 (.step 53 (.step 3 (.close 15))))))))) (.step 48 (.step 53 (.step 3 (.step 21 (.close 22)))))) (.step 9 (.step 21 (.step 53 (.step 18 (.step 55 (.close 57)))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617831357297686959020572369817757356961340814854993141940976570609813267557920225100394745724160144372369544118219259392755211698176⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.reuse 0) (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.step 62 (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.split 12 0 (.step 7 (.step 18 (.step 16 (.step 21 (.close 22))))) (.step 18 (.step 15 (.step 16 (.close 7))))))) (.step 9 (.step 18 (.step 26 (.step 7 (.step 16 (.close 21))))))) (.step 7 (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))))) (.step 7 (.step 18 (.close 52)))) (.step 52 (.close 7))) (.step 5 (.step 9 (.step 16 (.step 7 (.step 22 (.step 52 (.step 3 (.step 21 (.close 26)))))))))) (.step 48 (.step 52 (.step 3 (.step 22 (.close 26)))))) (.step 9 (.step 52 (.step 57 (.step 3 (.close 7)))))) (.step 52 (.step 7 (.close 21)))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.step 7 (.step 3 (.step 7 (.close 9)))) (.step 46 (.step 7 (.step 3 (.step 7 (.close 9)))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.close 7)))) (.step 46 (.step 54 (.step 3 (.step 7 (.close 9)))))) (.step 9 (.step 7 (.step 27 (.close 46))))) (.step 9 (.step 27 (.close 46))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341459064137514009958959958259550426454334464935369128270809466797024856417741768659567920782130941438845075324928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 3 (.step 7 (.step 21 (.step 16 (.close 22))))) (.step 21 (.step 28 (.step 3 (.step 15 (.close 16)))))) (.step 3 (.step 7 (.close 15)))) (.step 28 (.step 38 (.step 3 (.step 15 (.close 16)))))) (.step 3 (.close 7))) (.step 5 (.step 7 (.step 9 (.step 21 (.step 26 (.step 3 (.step 28 (.step 15 (.close 16)))))))))) (.step 28 (.step 58 (.step 41 (.step 3 (.close 4)))))) (.step 3 (.step 21 (.step 48 (.step 57 (.close 3)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 21 (.step 7 (.close 9))))) (.step 5 (.step 16 (.step 9 (.step 57 (.step 58 (.step 3 (.close 26)))))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 28 (.step 38 (.step 41 (.step 45 (.step 5 (.step 7 (.step 16 (.step 21 (.step 16 (.close 41))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461412680096783792187847740147215791361840617918036590680174087996388626766883268011384481129326207548107259904⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 72 1 (.step 45 (.step 7 (.step 16 (.close 21)))) (.step 26 (.step 29 (.step 45 (.close 3))))) (.step 7 (.step 15 (.step 21 (.close 15))))) (.step 7 (.step 26 (.step 29 (.step 37 (.step 39 (.step 37 (.close 21)))))))) (.step 28 (.step 45 (.close 3)))) (.step 5 (.step 7 (.step 28 (.step 45 (.close 16)))))) (.step 7 (.step 21 (.step 26 (.step 29 (.step 45 (.step 15 (.close 16)))))))) (.step 18 (.step 26 (.step 29 (.step 40 (.step 57 (.step 7 (.step 26 (.step 37 (.step 45 (.close 21)))))))))))))) (.reuse 1)) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.step 57 (.step 39 (.step 7 (.step 16 (.close 21))))) (.step 7 (.step 15 (.step 21 (.close 15))))) (.step 7 (.step 22 (.step 26 (.step 29 (.step 15 (.step 37 (.close 21)))))))) (.step 22 (.step 28 (.step 39 (.close 3))))) (.step 5 (.step 7 (.step 28 (.step 39 (.close 16)))))) (.step 7 (.step 21 (.step 22 (.step 29 (.step 39 (.step 15 (.step 16 (.close 26))))))))) (.step 18 (.step 22 (.step 29 (.step 40 (.step 57 (.step 7 (.step 37 (.step 21 (.close 26)))))))))) (.step 39 (.step 7 (.step 22 (.step 26 (.step 29 (.step 37 (.step 21 (.step 22 (.step 26 (.step 39 (.step 45 (.close 52))))))))))))) (.step 28 (.step 38 (.step 39 (.step 5 (.step 7 (.step 21 (.step 22 (.step 16 (.close 39)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524437163561525553374017225692604671256195947360485217114653551227676353496528756810945400930304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 54 1 (.split 21 0 (.split 26 0 (.split 49 0 (.split 17 0 (.step 37 (.step 4 (.close 7))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 16)))) (.step 28 (.step 7 (.step 15 (.close 21))))) (.step 7 (.step 15 (.close 22)))) (.step 15 (.step 29 (.step 37 (.step 7 (.close 21)))))) (.step 7 (.step 15 (.step 26 (.step 29 (.step 16 (.step 21 (.close 22)))))))) (.step 28 (.step 37 (.close 3)))) (.step 5 (.step 7 (.step 28 (.step 37 (.step 21 (.close 26))))))) (.step 7 (.step 15 (.step 21 (.step 29 (.step 37 (.step 26 (.close 53)))))))) (.step 15 (.step 7 (.step 16 (.step 29 (.step 26 (.step 21 (.step 26 (.close 52))))))))) (.step 37 (.step 7 (.step 15 (.step 29 (.step 37 (.close 52))))))) (.step 16 (.step 28 (.step 37 (.step 7 (.step 21 (.close 41))))))) (.step 37 (.step 7 (.step 15 (.step 29 (.step 37 (.close 52))))))) (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937037204078189673955052097146162668935477054035558650054330634207232⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.split 54 1 (.step 58 (.split 56 1 (.step 7 (.step 18 (.step 38 (.step 3 (.close 7))))) (.step 3 (.step 38 (.step 3 (.step 15 (.close 16))))))) (.step 21 (.step 57 (.close 3))))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 29))))))) (.step 9 (.step 21 (.step 7 (.close 21))))) (.step 9 (.step 53 (.step 57 (.step 58 (.step 62 (.step 18 (.step 21 (.step 29 (.step 38 (.step 3 (.step 7 (.close 26)))))))))))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 21 (.step 29 (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))) (.reuse 1)) (.run (.step 7 (.step 18 (.step 7 (.close 18)))))) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.step 7 (.step 18 (.close 26)))) (.step 3 (.step 7 (.step 9 (.step 26 (.step 29 (.close 26))))))) (.step 9 (.step 57 (.step 58 (.step 62 (.step 18 (.step 21 (.step 29 (.close 26))))))))) (.step 9 (.step 57 (.step 58 (.step 62 (.split 50 1 (.step 18 (.step 29 (.close 26))) (.step 21 (.step 18 (.step 29 (.step 3 (.step 7 (.step 26 (.step 29 (.close 52)))))))))))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.step 7 (.step 4 (.close 18)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379522046672754775221487282588585119711232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.step 57 (.step 18 (.split 21 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 56 1 (.step 15 (.step 7 (.step 9 (.step 18 (.close 15))))) (.step 3 (.step 16 (.step 22 (.step 9 (.step 15 (.close 3))))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 3 (.step 9 (.step 15 (.step 48 (.step 15 (.step 3 (.step 22 (.close 26))))))))) (.step 3 (.step 15 (.step 54 (.step 9 (.step 7 (.close 15))))))) (.step 9 (.step 15 (.step 7 (.step 18 (.step 3 (.step 7 (.step 21 (.step 22 (.close 26)))))))))) (.step 9 (.step 15 (.close 52)))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 15 (.step 26 (.step 29 (.step 37 (.step 7 (.close 15)))))))) (.step 3 (.step 15 (.step 16 (.step 21 (.step 28 (.step 41 (.step 48 (.step 15 (.step 3 (.step 22 (.step 3 (.step 22 (.close 26)))))))))))))) (.step 7 (.step 15 (.step 22 (.step 29 (.step 37 (.step 22 (.step 39 (.step 7 (.close 15)))))))))) (.step 9 (.step 15 (.step 21 (.step 29 (.close 38)))))) (.step 7 (.step 15 (.step 3 (.step 7 (.step 21 (.close 22))))))) (.step 9 (.step 15 (.step 28 (.close 29))))) (.step 4 (.step 9 (.step 15 (.close 7))))))) (.step 3 (.step 4 (.step 7 (.step 15 (.close 18)))))) (.step 3 (.step 4 (.step 7 (.step 15 (.close 18)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379522046674022425821715511990081822916608⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 4 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 43 1 (.split 38 1 (.step 57 (.split 42 1 (.step 4 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 4 (.step 7 (.step 9 (.step 7 (.close 17))))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 9 (.close 26))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.step 18 (.close 26)))))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.step 26 (.close 52))))))))) (.step 7 (.step 4 (.close 15))))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 4 (.step 15 (.close 26))))) (.step 4 (.step 7 (.step 18 (.step 26 (.step 29 (.step 15 (.close 26)))))))) (.step 7 (.close 37))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 29))))))))))) (.run (.step 7 (.step 18 (.step 7 (.close 18)))))) (.run (.step 7 (.step 18 (.step 7 (.step 18 (.close 19))))))) (.reuse 1)) (.run (.step 7 (.step 18 (.split 12 1 (.step 18 (.step 7 (.step 15 (.close 18)))) (.step 15 (.close 3)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case33
