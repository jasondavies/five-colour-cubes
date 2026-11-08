module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case146
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379522046674022425821715511990081822916608⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908284911715872467959, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691003773395856797335276228224145743890145446228163347693427359436041631246125966867020082117046907873927859536897, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052456053589153194253837624370217837571926411532114119348166667577424574415609621682462158016551230705179487883602097016906034847013349394638994267665186075520670606819328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 26 0 (.step 7 (.step 9 (.step 7 (.step 37 (.close 21))))) (.step 29 (.step 3 (.close 7)))) (.step 7 (.step 9 (.step 7 (.step 15 (.step 7 (.step 3 (.close 4)))))))) (.step 7 (.step 18 (.close 15)))) (.step 7 (.step 18 (.close 15)))) (.step 29 (.step 75 (.step 7 (.step 18 (.step 15 (.close 16))))))) (.step 7 (.step 3 (.step 7 (.step 9 (.step 21 (.close 26))))))) (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 7 (.split 16 0 (.step 9 (.step 26 (.step 55 (.step 7 (.step 28 (.step 16 (.close 21))))))) (.step 7 (.step 4 (.close 18))))) (.step 9 (.step 18 (.step 15 (.step 26 (.step 43 (.step 7 (.step 16 (.step 21 (.close 22)))))))))) (.step 7 (.step 9 (.close 15)))) (.step 9 (.step 26 (.close 7)))) (.step 26 (.step 62 (.close 7))))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.step 7 (.step 5 (.step 7 (.step 22 (.step 16 (.close 21))))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 21))))) (.step 48 (.split 16 0 (.step 22 (.step 28 (.step 3 (.step 15 (.step 16 (.close 21)))))) (.step 3 (.step 15 (.close 21)))))) (.step 3 (.step 7 (.close 15)))) (.step 29 (.step 75 (.step 59 (.close 3))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 10 (.step 22 (.step 28 (.step 57 (.step 7 (.step 15 (.close 16))))))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723026823511497443414970556934235212658789647265345092460553316133232956827148300580096150925360474673426548000424413027613403209957634276871563444068810752⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.split 55 1 (.reuse 0) (.run (.step 58 (.step 18 (.step 9 (.step 48 (.step 58 (.step 3 (.step 15 (.step 18 (.step 29 (.step 16 (.close 26))))))))))))) (.run (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 34 0 (.step 7 (.step 9 (.step 18 (.close 57)))) (.step 15 (.step 7 (.step 16 (.step 21 (.close 22)))))) (.step 9 (.step 29 (.step 7 (.close 4))))) (.step 9 (.step 18 (.close 57)))) (.step 9 (.step 26 (.step 29 (.step 57 (.close 3)))))) (.step 3 (.step 57 (.split 12 0 (.step 7 (.step 9 (.close 21))) (.step 9 (.step 7 (.step 21 (.close 26)))))))) (.step 9 (.step 26 (.step 57 (.close 3))))) (.step 3 (.step 22 (.step 48 (.step 9 (.close 57)))))) (.step 3 (.step 9 (.step 48 (.step 57 (.step 18 (.step 29 (.step 38 (.close 26))))))))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.step 7 (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 54 (.step 3 (.step 7 (.step 9 (.step 26 (.step 21 (.close 29)))))))) (.step 54 (.step 62 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 57 (.close 7))))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416615058687603566144160993955633614273257904377779617325365806091029198646250114599477354771318056004794272152907257855820926237540352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 7 (.split 16 0 (.step 9 (.split 17 0 (.step 18 (.split 34 0 (.step 55 (.step 7 (.step 28 (.step 21 (.close 22))))) (.step 7 (.step 16 (.close 21))))) (.step 7 (.step 4 (.close 18))))) (.step 7 (.step 4 (.close 18))))) (.step 9 (.step 18 (.step 15 (.step 37 (.step 52 (.close 3))))))) (.step 7 (.step 9 (.close 15)))) (.step 9 (.step 29 (.step 18 (.step 26 (.step 7 (.step 16 (.close 21)))))))) (.step 52 (.close 7))) (.step 52 (.step 7 (.step 18 (.step 22 (.close 26)))))) (.step 5 (.step 16 (.step 9 (.step 57 (.step 7 (.step 52 (.step 3 (.step 26 (.close 21)))))))))) (.step 48 (.step 52 (.step 3 (.step 22 (.step 26 (.step 22 (.close 28)))))))) (.step 9 (.step 52 (.step 57 (.step 3 (.close 7)))))) (.step 52 (.step 54 (.step 57 (.step 52 (.close 7)))))) (.step 52 (.split 72 1 (.split 16 0 (.step 52 (.step 5 (.step 3 (.close 21)))) (.step 5 (.step 18 (.step 27 (.step 18 (.step 7 (.step 3 (.close 4)))))))) (.step 9 (.step 21 (.step 29 (.step 18 (.step 26 (.step 7 (.step 15 (.step 16 (.close 22)))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416615058687603566144160993955633614273257904377779617325365806091029198646250114599477354771318056004794272152907257855820926237540352⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 7 (.split 16 0 (.step 9 (.split 17 0 (.step 18 (.step 21 (.step 7 (.step 16 (.close 22))))) (.step 7 (.step 4 (.close 18))))) (.step 7 (.step 4 (.close 18))))) (.step 9 (.step 18 (.step 15 (.step 21 (.step 53 (.close 3))))))) (.step 7 (.step 9 (.close 15)))) (.step 9 (.step 29 (.step 18 (.step 21 (.step 7 (.step 26 (.close 15)))))))) (.step 53 (.close 7))) (.step 53 (.step 7 (.step 21 (.close 22))))) (.step 5 (.step 21 (.step 9 (.step 57 (.step 7 (.step 53 (.step 3 (.step 15 (.step 16 (.close 26))))))))))) (.step 48 (.step 53 (.step 58 (.close 3))))) (.step 9 (.step 21 (.step 53 (.step 57 (.step 3 (.close 7))))))) (.step 53 (.step 54 (.step 57 (.step 53 (.close 7)))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935123878833676862859059191519952000574563636850760531278711524041129031667245699166105446176279851823713888430825930752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 72 1 (.step 45 (.step 7 (.step 26 (.step 16 (.close 21))))) (.step 29 (.step 45 (.step 3 (.close 7))))) (.step 7 (.step 15 (.step 21 (.step 22 (.step 21 (.close 28))))))) (.step 7 (.step 26 (.step 29 (.close 45))))) (.step 28 (.step 45 (.close 3)))) (.step 5 (.step 7 (.step 28 (.step 45 (.close 16)))))) (.step 26 (.step 29 (.step 57 (.step 59 (.split 55 1 (.split 10 0 (.step 26 (.step 39 (.step 7 (.step 37 (.close 21))))) (.step 7 (.close 15))) (.step 3 (.step 26 (.step 39 (.step 45 (.close 16))))))))))) (.step 18 (.step 26 (.step 29 (.step 38 (.step 40 (.step 57 (.step 7 (.step 26 (.step 45 (.step 15 (.close 16)))))))))))) (.step 26 (.step 57 (.step 58 (.step 55 (.step 9 (.step 52 (.step 7 (.step 15 (.step 21 (.close 26)))))))))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341459064137514009958959958259550426454334464935369128270809466797024856417741768659567920782130941438845075324928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.step 7 (.step 5 (.step 7 (.step 21 (.step 16 (.close 22))))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 21))))) (.step 48 (.split 16 0 (.step 28 (.step 48 (.step 21 (.step 37 (.step 3 (.close 22)))))) (.step 3 (.step 15 (.close 21)))))) (.step 3 (.step 7 (.close 15)))) (.step 29 (.step 38 (.step 75 (.step 41 (.close 3)))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.step 10 (.step 21 (.step 7 (.step 28 (.step 37 (.close 22))))))))) (.step 28 (.step 58 (.step 59 (.step 3 (.step 5 (.step 3 (.step 7 (.close 16))))))))) (.step 3 (.step 21 (.step 48 (.step 57 (.step 3 (.step 15 (.close 26)))))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 5 (.step 21 (.step 7 (.step 9 (.step 21 (.close 26))))))) (.step 5 (.step 42 (.step 16 (.step 57 (.step 58 (.step 3 (.step 9 (.close 26))))))))) (.step 3 (.step 7 (.step 9 (.close 10)))))) (.step 7 (.step 38 (.step 28 (.step 45 (.step 76 (.step 41 (.step 58 (.step 45 (.step 3 (.close 16))))))))))))
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
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461412680096783792187847740147215791361840617918036590680174087996388626766883268011384481129326207548107259904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 72 1 (.split 21 0 (.step 39 (.step 7 (.step 21 (.step 16 (.step 22 (.step 15 (.close 16))))))) (.step 7 (.step 15 (.close 22)))) (.step 29 (.step 39 (.step 3 (.close 7))))) (.step 7 (.step 15 (.step 22 (.close 28))))) (.step 7 (.step 15 (.step 21 (.step 22 (.step 21 (.close 28))))))) (.step 7 (.step 22 (.step 26 (.step 29 (.step 37 (.close 21))))))) (.step 22 (.step 28 (.step 39 (.close 3))))) (.step 5 (.step 7 (.step 28 (.step 39 (.step 22 (.step 16 (.close 26)))))))) (.step 22 (.step 29 (.step 39 (.step 7 (.step 22 (.step 26 (.step 39 (.step 15 (.step 16 (.close 21))))))))))) (.step 18 (.step 22 (.step 29 (.step 38 (.step 40 (.step 57 (.step 7 (.step 26 (.step 37 (.close 26))))))))))) (.step 22 (.step 57 (.step 7 (.step 29 (.step 52 (.step 16 (.step 21 (.close 26))))))))) (.step 45 (.split 49 1 (.step 39 (.step 7 (.step 29 (.step 38 (.step 45 (.step 37 (.close 53))))))) (.step 7 (.step 29 (.step 57 (.step 39 (.step 38 (.step 45 (.close 52)))))))))) (.step 38 (.step 28 (.step 45 (.split 49 1 (.step 39 (.step 5 (.step 7 (.step 21 (.step 22 (.step 16 (.close 39))))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 38 (.close 39))))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414973595399782259359350968111093448781414483025758961297825585228013689759356496192551147879317673793814528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 75 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.step 29 (.step 38 (.step 7 (.step 18 (.step 15 (.close 16)))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 9 (.step 26 (.step 29 (.step 18 (.step 21 (.step 7 (.step 26 (.step 37 (.close 22)))))))))) (.step 3 (.step 29 (.step 38 (.step 3 (.step 15 (.step 22 (.step 15 (.close 16))))))))) (.step 3 (.step 18 (.step 29 (.step 38 (.close 16)))))) (.step 9 (.step 21 (.step 29 (.step 57 (.step 3 (.close 7)))))))) (.step 3 (.step 57 (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 29))))))))) (.step 9 (.step 21 (.step 38 (.step 18 (.step 21 (.close 26))))))) (.step 9 (.step 53 (.step 57 (.step 58 (.step 75 (.split 51 1 (.split 59 1 (.step 29 (.step 18 (.step 21 (.step 38 (.step 3 (.step 7 (.close 26))))))) (.step 26 (.step 29 (.step 18 (.step 21 (.step 37 (.step 22 (.close 38)))))))) (.step 3 (.step 7 (.close 52)))))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 3 (.step 21 (.step 29 (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732142412855220466682097812186882874655189202742495293581668029831618968190165261350843160513179345285511877772265476332873982714456044323980536245702825974619968125582241169408⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 49 0 (.split 50 0 (.split 17 0 (.step 37 (.step 4 (.close 7))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 21)))) (.step 7 (.step 15 (.close 16)))) (.step 28 (.step 7 (.step 15 (.close 21))))) (.step 7 (.step 15 (.close 22)))) (.step 29 (.step 37 (.step 3 (.close 7))))) (.step 7 (.step 15 (.step 26 (.step 29 (.step 16 (.step 21 (.close 22)))))))) (.step 28 (.step 37 (.step 3 (.close 7))))) (.step 5 (.step 7 (.step 28 (.step 37 (.step 21 (.close 26))))))) (.step 15 (.step 29 (.step 57 (.step 39 (.step 37 (.step 57 (.close 3)))))))) (.step 15 (.step 7 (.step 21 (.step 29 (.step 37 (.step 26 (.step 52 (.step 39 (.step 45 (.close 53))))))))))) (.step 15 (.step 16 (.step 52 (.step 7 (.step 16 (.step 26 (.step 29 (.step 21 (.step 26 (.close 21))))))))))) (.step 37 (.split 49 1 (.step 45 (.step 7 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.step 45 (.close 52)))))))))) (.step 7 (.step 15 (.step 16 (.step 29 (.step 37 (.step 38 (.close 52)))))))))) (.step 16 (.step 28 (.step 37 (.step 38 (.step 37 (.step 7 (.step 21 (.close 41))))))))) (.step 37 (.split 49 1 (.step 39 (.step 7 (.step 15 (.step 29 (.step 37 (.step 21 (.step 22 (.step 26 (.step 39 (.close 52)))))))))) (.step 7 (.step 15 (.step 16 (.step 29 (.step 37 (.step 38 (.close 52)))))))))))
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
def root : Box := ⟨3705346855594118253554271520278013051304639509300498049262642688253222295961600, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921935352207411492758967885408703223942018374732509149864274261658566656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 29 (.split 30 1 (.split 38 1 (.step 29 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 59 1 (.split 67 1 (.step 29 (.close 7)) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 9 (.step 26 (.step 29 (.step 7 (.step 17 (.close 18))))))) (.step 3 (.step 18 (.step 28 (.step 21 (.close 26)))))) (.step 9 (.step 29 (.step 7 (.step 18 (.close 26)))))) (.step 3 (.step 7 (.step 9 (.step 57 (.step 21 (.close 26))))))) (.step 9 (.step 57 (.step 58 (.split 51 1 (.split 59 1 (.step 29 (.step 7 (.step 18 (.close 26)))) (.step 21 (.step 26 (.step 18 (.close 29))))) (.step 3 (.step 7 (.step 21 (.close 53))))))))) (.step 9 (.step 57 (.step 58 (.split 50 1 (.split 51 1 (.split 59 1 (.step 29 (.step 7 (.step 18 (.close 26)))) (.step 26 (.step 27 (.close 29)))) (.step 3 (.step 7 (.close 52)))) (.step 21 (.step 27 (.close 52)))))))) (.step 3 (.step 7 (.close 9))))) (.step 3 (.step 21 (.step 28 (.step 3 (.step 21 (.step 16 (.step 26 (.step 16 (.close 29)))))))))) (.step 3 (.step 7 (.close 18))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937037204078189673955052097146162668935477054035558650054330634207232⟩
def references : Fin 7 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root, Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 7 := (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.step 7 (.step 3 (.step 7 (.close 9)))) (.split 72 1 (.split 12 0 (.step 7 (.close 9)) (.step 3 (.step 46 (.close 7)))) (.step 3 (.step 7 (.close 9))))) (.step 9 (.close 7))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 3 (.step 9 (.close 7)))) (.step 46 (.split 54 1 (.split 56 1 (.step 54 (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.close 7)))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.step 7 (.close 52)))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.step 7 (.split 35 1 (.reuse 5) (.run (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))) (.run (.step 7 (.step 18 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.step 9 (.step 18 (.close 52)))))) (.step 18 (.close 7))))))) (.reuse 6)) (.run (.step 7 (.step 18 (.step 7 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 4 (.close 18)))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 4 (.step 18 (.close 7)))) (.step 4 (.step 18 (.step 26 (.step 7 (.step 18 (.close 7))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996657671928742189814526555305472898095761868906823680⟩
def references : Fin 1 → Box := ![Part10.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 4 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 43 1 (.split 49 1 (.split 38 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 42 1 (.split 51 1 (.step 4 (.split 56 1 (.split 67 1 (.step 4 (.step 7 (.step 15 (.step 7 (.close 17))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 4)))) (.step 3 (.step 7 (.step 9 (.close 26))))) (.step 7 (.step 4 (.step 15 (.close 26))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.close 26))))))) (.step 4 (.step 9 (.close 57)))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.step 26 (.close 53)))))))) (.step 3 (.close 4))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.close 52))))))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 22 (.step 4 (.step 26 (.step 29 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.step 29 (.step 26 (.close 38)))))))) (.step 7 (.step 37 (.close 29)))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 29))))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.step 7 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 4 (.close 18)))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 4 (.step 18 (.close 7)))) (.step 4 (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))))) (.step 7 (.step 18 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29))))))))))
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
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459739099333687395542992527424274267832346969225240484808154934371377055054372626371229298141468342579918951319467440543769118548042036060232387205589515925874597167104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 34 0 (.step 7 (.step 9 (.step 15 (.step 7 (.step 15 (.close 3)))))) (.step 15 (.close 3))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 9 (.step 15 (.step 7 (.step 21 (.close 22)))))) (.step 3 (.step 15 (.split 21 0 (.split 26 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9)))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 3 (.step 15 (.step 16 (.step 22 (.step 15 (.step 3 (.step 9 (.step 15 (.step 21 (.close 26))))))))))) (.step 3 (.step 9 (.step 48 (.step 15 (.close 58)))))) (.step 3 (.step 15 (.step 57 (.step 62 (.step 70 (.step 7 (.step 9 (.close 15))))))))) (.step 9 (.step 15 (.step 21 (.close 53))))) (.step 9 (.step 15 (.close 52)))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 15 (.step 26 (.step 29 (.step 37 (.step 26 (.step 45 (.step 7 (.close 15)))))))))) (.step 3 (.step 16 (.step 21 (.step 15 (.step 28 (.step 48 (.step 41 (.step 15 (.step 3 (.step 15 (.close 26)))))))))))) (.step 7 (.step 15 (.step 22 (.step 29 (.step 37 (.step 39 (.step 22 (.step 7 (.step 15 (.close 38))))))))))) (.step 9 (.step 15 (.step 21 (.step 29 (.close 38)))))) (.step 7 (.step 15 (.close 37)))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379522046674022425821715511990081822916608⟩
def references : Fin 2 → Box := ![Part11.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 7 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 4 (.close 18)))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 4 (.step 18 (.close 7)))) (.step 4 (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))))) (.step 7 (.step 18 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29)))))) (.step 7 (.step 18 (.step 19 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29))))))))))) (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 57 (.split 26 1 (.split 30 1 (.reuse 1) (.run (.step 3 (.step 7 (.step 18 (.close 15)))))) (.run (.step 9 (.step 15 (.step 18 (.step 28 (.close 29)))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 18 (.close 15)))))))) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.close 7))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 18 (.close 15)))))))) (.run (.step 3 (.step 4 (.step 7 (.step 18 (.close 15)))))))) (.run (.step 7 (.step 18 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 15 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18))))))) (.step 18 (.close 7))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18))))))) (.step 15 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part13.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case146

namespace FiveColour.Packed.EnumerationChunks.Projected.Case146
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 33 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 33 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 33 0).upper i := by decide +kernel
lemma budget_model : (⟨32908284911715872467959, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691003773395856797335276228224145743890145446228163347693427359436041631246125966867020082117046907873927859536897, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 33), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908284911715872467959, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691003773395856797335276228224145743890145446228163347693427359436041631246125966867020082117046907873927859536897, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 33) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 33 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 33 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 33) (Archive.root 33) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 33 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 33 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case146

namespace FiveColour.Packed.EnumerationChunks.Case146
def root : Box := Archive.root 33
def families : Fin 78 → List Cut := Enumeration.families 33
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case146.original_covered points
end FiveColour.Packed.EnumerationChunks.Case146
