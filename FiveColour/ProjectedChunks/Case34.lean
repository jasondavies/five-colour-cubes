module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case34
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185308179080118173433856⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052456053589153194253837624370217837571926411532114119348166667577424574415609621682462158014700366528776761822378454553407789069921236983499145876846982409065688782077952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 16 (.close 21))))) (.step 18 (.step 9 (.step 15 (.step 43 (.step 3 (.step 16 (.close 21))))))))) (.split 16 0 (.split 21 0 (.split 34 0 (.step 7 (.close 9)) (.step 15 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 3)))) (.step 7 (.step 9 (.close 3))))) (.step 29 (.step 75 (.step 7 (.step 9 (.close 15)))))) (.step 7 (.step 3 (.step 7 (.close 9))))) (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.step 9 (.step 26 (.split 12 0 (.step 7 (.step 26 (.step 5 (.step 7 (.step 16 (.close 21)))))) (.step 18 (.step 15 (.step 26 (.step 3 (.step 16 (.close 21)))))))))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.step 7 (.step 18 (.close 26))))) (.step 26 (.step 62 (.close 7))))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.step 7 (.step 5 (.step 9 (.step 7 (.step 22 (.step 16 (.close 21))))))) (.step 48 (.step 28 (.step 3 (.step 15 (.step 16 (.close 21))))))) (.step 3 (.step 7 (.close 15)))) (.step 10 (.step 48 (.split 10 0 (.split 30 0 (.step 10 (.step 22 (.step 9 (.close 3)))) (.step 3 (.close 9))) (.step 3 (.close 9)))))) (.step 29 (.step 75 (.step 59 (.close 3))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 9 (.step 22 (.step 26 (.step 28 (.step 7 (.step 15 (.close 16)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723026823511497443414970556934235212658789647265345092460553316133232956827146449715919748199299251030963049754647320915202263361566816073205108462244069376⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.split 55 1 (.reuse 0) (.run (.step 58 (.step 18 (.step 9 (.step 48 (.step 7 (.step 18 (.step 15 (.close 26)))))))))) (.run (.split 55 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.split 21 0 (.split 34 0 (.step 57 (.step 7 (.step 3 (.step 21 (.close 26))))) (.step 15 (.step 29 (.step 39 (.step 7 (.step 9 (.step 16 (.close 21)))))))) (.step 7 (.step 9 (.step 18 (.step 3 (.close 22)))))) (.step 9 (.step 15 (.close 57)))) (.step 9 (.step 26 (.step 29 (.step 57 (.close 3)))))) (.step 3 (.step 9 (.step 7 (.close 21))))) (.step 9 (.step 26 (.close 57)))) (.step 3 (.step 9 (.step 48 (.step 57 (.close 3)))))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.step 3 (.step 9 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 9 (.close 7))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 54 (.step 3 (.step 7 (.step 9 (.close 21)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 54 (.step 7 (.step 9 (.step 21 (.close 26)))))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416615058687603566144160993955633614273257904377779617323514941914626472585026472135979108994225943593654423762089054189365944412798976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.split 16 0 (.step 62 (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 43 (.close 52))))) (.step 9 (.step 7 (.step 18 (.step 15 (.step 16 (.close 7))))))) (.step 9 (.step 7 (.step 18 (.step 26 (.step 7 (.step 16 (.close 21))))))))) (.step 18 (.step 55 (.split 59 1 (.step 18 (.step 7 (.close 9))) (.step 27 (.step 18 (.step 26 (.step 18 (.step 7 (.close 9)))))))))) (.step 7 (.step 18 (.step 52 (.step 4 (.step 3 (.close 7))))))) (.step 52 (.close 7))) (.step 5 (.step 9 (.step 16 (.step 57 (.step 7 (.step 28 (.step 3 (.step 7 (.step 21 (.close 26))))))))))) (.step 48 (.step 52 (.step 3 (.step 22 (.close 26)))))) (.step 9 (.step 52 (.step 57 (.step 3 (.close 7)))))) (.step 52 (.split 72 1 (.split 16 0 (.step 52 (.step 5 (.step 3 (.close 21)))) (.step 5 (.step 18 (.step 7 (.step 18 (.step 5 (.close 9))))))) (.step 9 (.step 18 (.step 21 (.step 7 (.step 26 (.step 15 (.step 16 (.close 22))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617831357297686959020572369817757356961340814854993140090112394207087206334277761602148968632047733232521153300015592937773386956800⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.split 16 0 (.step 62 (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 21 (.step 7 (.step 3 (.close 16))))))) (.step 9 (.step 7 (.step 18 (.step 15 (.step 21 (.step 43 (.step 3 (.step 7 (.close 16)))))))))) (.step 9 (.step 7 (.step 18 (.step 21 (.step 7 (.step 26 (.close 15))))))))) (.step 18 (.step 21 (.step 18 (.step 7 (.step 21 (.step 7 (.close 9)))))))) (.step 7 (.step 18 (.step 52 (.step 7 (.close 9)))))) (.step 53 (.close 7))) (.step 5 (.step 9 (.step 21 (.step 54 (.step 57 (.step 7 (.step 28 (.step 3 (.step 7 (.step 15 (.close 16)))))))))))) (.step 48 (.step 53 (.step 9 (.step 21 (.step 28 (.step 7 (.close 53)))))))) (.step 9 (.step 21 (.step 53 (.step 57 (.close 3)))))))) (.reuse 1)) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.step 9 (.split 6 0 (.step 7 (.step 3 (.close 9))) (.step 3 (.step 7 (.close 9))))) (.step 46 (.step 70 (.step 3 (.close 7))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.close 7)))) (.step 46 (.step 54 (.step 3 (.step 7 (.close 9)))))) (.step 9 (.step 7 (.step 27 (.close 46))))) (.step 9 (.step 27 (.close 46))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341459064137514009958959958259550424603470288532643067047167003298779079325629357519719529963927274983863250583552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.step 7 (.step 5 (.step 9 (.step 7 (.step 21 (.step 16 (.close 22))))))) (.step 48 (.step 28 (.step 3 (.step 15 (.step 16 (.close 21))))))) (.step 3 (.step 7 (.close 15)))) (.step 10 (.step 48 (.split 10 0 (.split 30 0 (.step 10 (.step 21 (.step 9 (.close 3)))) (.step 3 (.close 9))) (.step 3 (.close 9)))))) (.step 29 (.step 38 (.step 48 (.step 75 (.close 3)))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 9 (.step 21 (.step 7 (.step 26 (.step 7 (.step 28 (.step 15 (.close 16)))))))))) (.step 28 (.step 58 (.step 41 (.step 3 (.step 5 (.step 3 (.close 9)))))))) (.step 3 (.step 21 (.step 48 (.step 57 (.close 3)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 21 (.step 7 (.step 9 (.close 21)))))) (.step 5 (.step 16 (.step 9 (.step 57 (.step 58 (.step 3 (.close 26)))))))) (.step 3 (.step 7 (.close 9))))) (.step 7 (.step 28 (.step 38 (.step 41 (.step 45 (.step 58 (.step 45 (.step 3 (.close 9)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461412680096783792187847740147213940497664215191975367037710589750611534654472128162993662925659752566282518528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.split 21 0 (.step 39 (.step 7 (.step 21 (.step 16 (.step 22 (.step 16 (.close 26))))))) (.step 7 (.step 15 (.step 22 (.step 15 (.close 26)))))) (.step 29 (.step 57 (.step 39 (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 22 (.step 26 (.step 29 (.step 15 (.step 37 (.close 21))))))))) (.step 22 (.step 28 (.step 39 (.close 3))))) (.step 5 (.step 7 (.step 28 (.step 39 (.step 9 (.step 22 (.step 26 (.step 16 (.close 21)))))))))) (.step 18 (.step 22 (.step 29 (.step 38 (.step 40 (.step 9 (.step 7 (.step 22 (.step 39 (.step 15 (.step 16 (.close 26))))))))))))) (.step 18 (.step 22 (.step 29 (.step 40 (.step 9 (.step 57 (.step 7 (.step 37 (.step 21 (.close 26))))))))))) (.step 45 (.split 49 1 (.step 39 (.step 7 (.step 9 (.step 21 (.step 22 (.step 26 (.step 29 (.step 15 (.step 37 (.close 39)))))))))) (.step 7 (.step 9 (.step 29 (.step 37 (.step 22 (.step 26 (.step 21 (.step 39 (.step 21 (.step 45 (.close 52)))))))))))))) (.step 28 (.step 38 (.step 39 (.step 41 (.step 58 (.step 39 (.close 3))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414973595399782259359350968109242584605011756964535318834327339450921577348216647801732944212862691969073152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.step 7 (.step 18 (.step 21 (.step 15 (.close 16))))) (.step 9 (.step 3 (.close 7)))) (.step 9 (.step 7 (.step 18 (.step 21 (.step 7 (.step 26 (.step 15 (.close 16))))))))) (.step 3 (.step 38 (.step 3 (.step 9 (.step 15 (.close 16))))))) (.step 3 (.step 18 (.step 38 (.close 9))))) (.step 9 (.step 21 (.step 57 (.close 3)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 9 (.step 21 (.step 7 (.close 21))))) (.step 9 (.step 53 (.step 57 (.step 18 (.step 21 (.step 29 (.step 52 (.step 3 (.step 16 (.step 22 (.step 26 (.close 38)))))))))))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 21 (.step 29 (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732142412855220466682097812186882874655189202742495293581668029831616619647582487517615271032582554097620325686990506789360811925238735022843010497410971457417916901897384493056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 25 0 (.split 54 1 (.split 49 0 (.split 17 0 (.step 37 (.step 4 (.close 7))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 16)))) (.step 15 (.step 29 (.step 37 (.step 3 (.close 7)))))) (.step 28 (.step 29 (.close 7)))) (.step 7 (.step 15 (.step 22 (.close 26))))) (.step 29 (.step 75 (.split 16 0 (.step 15 (.step 37 (.step 7 (.close 9)))) (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 15 (.step 26 (.step 16 (.step 21 (.step 28 (.step 21 (.close 22)))))))))) (.step 28 (.step 37 (.step 3 (.close 9))))) (.step 5 (.step 7 (.step 28 (.step 37 (.step 9 (.step 26 (.step 21 (.close 37))))))))) (.step 15 (.step 7 (.step 9 (.step 21 (.step 29 (.step 37 (.step 26 (.close 53))))))))) (.step 15 (.step 16 (.step 18 (.step 29 (.step 40 (.step 9 (.step 7 (.step 16 (.step 26 (.step 21 (.step 26 (.close 52))))))))))))) (.step 37 (.split 49 1 (.step 45 (.step 7 (.step 9 (.step 15 (.step 21 (.step 26 (.step 29 (.step 16 (.close 37))))))))) (.step 7 (.step 9 (.step 15 (.step 16 (.step 37 (.close 52))))))))) (.step 16 (.step 28 (.step 37 (.step 38 (.step 37 (.step 7 (.step 9 (.step 21 (.close 41)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886009239317735567019410714535330633105958791776228277317059624853692669759586304⟩
def references : Fin 5 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root, Part7.root]
def proof : Chunks.Proof 5 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.step 45 (.split 21 0 (.split 25 0 (.step 7 (.step 16 (.close 26))) (.step 28 (.step 3 (.step 5 (.step 3 (.close 16)))))) (.step 3 (.step 7 (.close 26))))) (.step 29 (.step 75 (.split 16 0 (.step 26 (.step 9 (.close 3))) (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 26 (.step 29 (.step 37 (.step 39 (.step 37 (.close 21))))))))) (.step 28 (.step 45 (.step 3 (.step 9 (.step 16 (.close 21))))))) (.step 5 (.step 7 (.step 28 (.step 45 (.step 9 (.step 26 (.step 38 (.close 45))))))))) (.step 18 (.step 26 (.step 29 (.step 38 (.step 40 (.step 9 (.step 7 (.step 26 (.step 45 (.step 15 (.close 16)))))))))))) (.step 18 (.step 26 (.step 29 (.step 40 (.step 57 (.step 58 (.step 9 (.step 7 (.step 15 (.step 21 (.step 15 (.close 26)))))))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.step 7 (.split 35 1 (.split 36 1 (.reuse 4) (.run (.step 37 (.split 49 1 (.step 39 (.step 7 (.step 9 (.step 15 (.step 21 (.step 22 (.step 26 (.step 16 (.step 29 (.step 16 (.close 37))))))))))) (.step 7 (.step 9 (.step 15 (.step 16 (.step 37 (.close 52)))))))))) (.run (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))) (.run (.step 7 (.step 18 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 3 (.step 7 (.step 9 (.close 18)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569129900084964207831971393854518999119739945601472969607844290105442304⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 25 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.split 59 1 (.step 28 (.split 54 1 (.split 67 1 (.split 21 0 (.split 34 0 (.split 6 0 (.step 7 (.step 9 (.step 3 (.step 7 (.close 16))))) (.step 3 (.close 9))) (.step 7 (.step 9 (.step 15 (.close 16))))) (.step 3 (.close 5))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.step 3 (.close 28)))))) (.step 5 (.step 9 (.step 26 (.step 28 (.step 3 (.close 28)))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 9 (.step 57 (.step 58 (.close 3)))))) (.step 5 (.step 9 (.step 16 (.step 57 (.step 58 (.step 3 (.close 26)))))))) (.step 3 (.step 7 (.close 9))))) (.step 7 (.step 28 (.step 5 (.step 7 (.step 9 (.step 16 (.close 29)))))))) (.step 10 (.step 28 (.step 5 (.step 9 (.step 21 (.step 3 (.close 26)))))))) (.step 7 (.step 28 (.step 5 (.step 7 (.step 9 (.step 16 (.close 29)))))))) (.step 7 (.step 16 (.step 28 (.step 5 (.step 9 (.close 15))))))) (.step 3 (.close 7)))))) (.run (.step 7 (.step 18 (.split 25 1 (.step 7 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.close 15)))) (.step 18 (.step 7 (.step 9 (.step 7 (.close 15)))))) (.step 3 (.step 7 (.step 9 (.step 15 (.close 18))))))) (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462068164602697931120404007552905735244027204222429691904⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 26 (.split 25 1 (.step 7 (.split 35 1 (.split 49 1 (.step 7 (.step 4 (.step 9 (.close 18)))) (.step 18 (.close 7))) (.step 4 (.step 7 (.step 9 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7))))))))))) (.run (.step 7 (.step 18 (.split 25 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 4 (.step 18 (.split 43 1 (.split 42 1 (.step 4 (.step 57 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.split 59 1 (.split 67 1 (.step 4 (.close 7)) (.step 3 (.step 7 (.close 9)))) (.step 4 (.step 7 (.step 9 (.close 7))))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 9 (.close 26))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.step 18 (.close 26)))))))) (.step 3 (.step 4 (.step 9 (.step 7 (.step 18 (.step 26 (.close 52)))))))))) (.step 7 (.step 4 (.step 9 (.close 15))))) (.step 3 (.step 7 (.close 9)))))) (.step 3 (.step 4 (.step 3 (.close 5))))) (.step 3 (.step 7 (.step 22 (.step 4 (.step 9 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.step 15 (.close 26))))))) (.step 3 (.step 7 (.step 37 (.close 4))))) (.step 3 (.step 4 (.step 5 (.step 28 (.close 3))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459739099333687395542992527424274267832346969225240484808154934371377055054374663407205630776690434622881299473986028513917007392180261060833350768685612807598955823104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 25 0 (.split 35 0 (.split 34 0 (.split 36 0 (.step 15 (.step 3 (.close 7))) (.step 7 (.step 9 (.close 15)))) (.step 15 (.close 3))) (.step 9 (.step 15 (.close 3)))) (.step 9 (.step 29 (.close 3)))) (.step 7 (.step 9 (.step 15 (.close 3))))) (.step 9 (.step 15 (.step 3 (.step 21 (.close 22)))))) (.step 3 (.step 9 (.step 7 (.close 15))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 3 (.step 9 (.step 48 (.step 15 (.step 3 (.step 22 (.close 26)))))))) (.step 3 (.step 15 (.step 54 (.step 9 (.step 7 (.close 15))))))) (.step 9 (.step 15 (.step 7 (.step 18 (.step 3 (.step 7 (.step 21 (.step 22 (.close 26)))))))))) (.step 9 (.step 15 (.close 52)))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 15 (.step 26 (.step 29 (.step 37 (.step 45 (.step 7 (.step 9 (.close 15)))))))))) (.step 3 (.step 16 (.step 21 (.step 15 (.step 28 (.step 48 (.step 10 (.step 15 (.step 38 (.step 3 (.step 15 (.step 22 (.close 26)))))))))))))) (.step 7 (.step 15 (.step 22 (.step 29 (.step 37 (.step 22 (.step 39 (.step 7 (.step 9 (.close 15))))))))))) (.step 9 (.step 15 (.step 21 (.step 29 (.close 38)))))) (.step 7 (.step 15 (.step 29 (.step 3 (.step 7 (.step 21 (.close 22)))))))) (.step 3 (.step 7 (.step 15 (.step 7 (.close 15)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2305843011361177600, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185308179080118173433856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 9 (.split 25 1 (.step 7 (.split 34 1 (.split 36 1 (.split 38 1 (.step 9 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 25 0 (.split 56 1 (.split 16 0 (.split 51 0 (.step 9 (.close 3)) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 10 (.close 3))) (.step 9 (.close 3))) (.step 3 (.step 9 (.close 7)))) (.step 3 (.step 54 (.step 9 (.close 7))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 10 (.step 26 (.step 29 (.split 21 0 (.step 45 (.step 7 (.close 9))) (.step 3 (.step 7 (.close 9)))))))))) (.step 3 (.step 10 (.close 3)))) (.step 7 (.step 9 (.step 10 (.step 29 (.step 39 (.step 22 (.step 9 (.close 3))))))))) (.step 7 (.step 9 (.step 10 (.step 15 (.step 29 (.step 37 (.split 21 0 (.step 37 (.step 7 (.close 9))) (.step 3 (.step 7 (.close 9)))))))))))) (.step 3 (.step 10 (.close 3))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.close 9))))))) (.step 4 (.step 7 (.close 9)))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 7 (.close 9))))))) (.step 3 (.step 4 (.step 7 (.step 11 (.close 9)))))) (.step 9 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 3 (.close 7)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185308179080118173433856⟩
def references : Fin 3 → Box := ![Part10.root, Part11.root, Part12.root]
def proof : Chunks.Proof 3 := (.split 6 1 (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 22 1 (.step 22 (.split 25 1 (.step 7 (.split 35 1 (.split 49 1 (.step 7 (.step 4 (.step 9 (.close 18)))) (.step 18 (.close 7))) (.step 4 (.step 7 (.step 9 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7))))))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.split 25 1 (.step 7 (.split 35 1 (.split 49 1 (.step 7 (.step 4 (.step 9 (.close 18)))) (.step 18 (.close 7))) (.step 4 (.step 7 (.step 9 (.close 18)))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7))))))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 19)))))))) (.split 10 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 57 (.split 25 1 (.reuse 1) (.run (.step 3 (.step 16 (.step 29 (.step 3 (.step 9 (.close 15))))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 7 (.step 15 (.close 17))))))))) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.close 7))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 18 (.close 9)))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 18 (.close 9)))))))) (.run (.step 3 (.step 7 (.step 15 (.close 3))))))) (.reuse 2))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case34
