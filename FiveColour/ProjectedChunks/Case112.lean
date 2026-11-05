module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case112
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079166450589158585345283312557861340749338639804069091894963296504675806186831872⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨37630511536740893520887, 5789234131009374248507346766749886964179117598075761631441503938856419104125729984377942245333425284026394393415169773689373755704242316349912225571028696891635007459092358541327061333498215709696615525420286517587399934977, 0⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000409413503253965452678337730340540649546387030196892732096284700566868009505471869653912252061526303102697623786215098274097793940865153274320126391930472292666296881905664⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 57 1 (.split 59 1 (.split 67 1 (.split 45 1 (.split 55 1 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.step 31 (.close 21))) (.step 3 (.step 7 (.step 3 (.close 18))))) (.step 3 (.close 18))) (.step 3 (.step 18 (.close 3)))) (.step 3 (.step 18 (.step 3 (.step 4 (.close 12)))))) (.step 3 (.close 7))) (.step 58 (.close 3))) (.step 48 (.close 3))) (.step 3 (.close 7))) (.split 67 1 (.step 48 (.step 58 (.split 10 0 (.step 55 (.split 11 0 (.split 34 0 (.split 16 0 (.step 55 (.step 3 (.step 7 (.step 3 (.close 21))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 9 (.step 18 (.step 31 (.close 48)))))) (.step 3 (.step 18 (.close 12))))) (.step 3 (.step 18 (.close 12)))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53)))))))) (.step 3 (.step 48 (.split 55 1 (.split 10 0 (.step 60 (.split 45 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 38 0 (.split 43 0 (.step 60 (.close 3)) (.step 3 (.step 31 (.step 3 (.close 48))))) (.step 31 (.step 3 (.step 32 (.close 48))))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 18 (.step 31 (.close 48)))) (.step 60 (.close 3))) (.step 48 (.step 4 (.step 12 (.close 18)))))) (.step 3 (.step 31 (.step 3 (.step 18 (.step 12 (.close 48))))))) (.step 48 (.step 58 (.step 5 (.close 31)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110638088186794583850658653746480219292209514700383857906579188412462163577883705309255121709817890000573377386762211508755015775296959103697413489723697491083264⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 53 1 (.split 56 1 (.reuse 0) (.run (.step 3 (.split 57 1 (.step 3 (.step 58 (.split 45 1 (.split 55 1 (.split 59 1 (.split 11 0 (.split 16 0 (.split 10 0 (.split 17 0 (.step 28 (.split 22 0 (.step 31 (.step 3 (.close 48))) (.step 3 (.step 16 (.step 21 (.close 31)))))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 31)))))) (.step 3 (.step 12 (.step 16 (.close 31))))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 31)))))) (.step 3 (.step 43 (.step 31 (.close 18))))) (.step 3 (.step 22 (.step 31 (.close 48))))) (.step 3 (.step 5 (.step 31 (.close 48))))) (.step 10 (.step 22 (.step 31 (.step 3 (.step 48 (.close 4))))))))) (.step 26 (.step 28 (.step 48 (.step 51 (.step 60 (.step 3 (.close 16))))))))))) (.run (.step 3 (.step 51 (.split 57 1 (.step 3 (.step 48 (.split 45 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 17 0 (.step 3 (.step 51 (.step 18 (.split 34 0 (.step 48 (.step 3 (.close 4))) (.step 3 (.step 4 (.close 14))))))) (.step 8 (.step 18 (.step 3 (.close 18))))) (.step 8 (.step 18 (.close 56)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 24 (.step 43 (.close 51))))) (.step 5 (.step 18 (.step 3 (.step 48 (.step 51 (.step 3 (.close 48)))))))) (.step 3 (.step 4 (.step 18 (.close 48))))))) (.step 8 (.step 44 (.step 48 (.step 51 (.step 60 (.step 3 (.close 12))))))))))))
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
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 14696649931972027310843563361000416961428110644959694905460647464469174318179182005046179800195600271401316668653718141385594890081780162240723231876842391305451111198466180334739406281823075470164361216⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 10 0 (.step 55 (.split 11 0 (.split 34 0 (.split 16 0 (.step 55 (.step 3 (.step 7 (.step 3 (.close 21))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 31 (.close 48))))))) (.step 3 (.step 18 (.close 12))))) (.step 3 (.step 18 (.close 12)))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 53 (.split 45 1 (.split 55 1 (.split 11 0 (.split 16 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 53 (.step 62 (.close 3))) (.step 3 (.step 21 (.close 32)))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 26 (.step 3 (.step 31 (.close 48))))))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 18 (.step 31 (.close 48)))))))) (.step 18 (.step 3 (.step 27 (.step 44 (.step 3 (.close 48))))))) (.step 3 (.step 18 (.step 12 (.close 48))))) (.step 3 (.step 48 (.step 3 (.step 21 (.close 31)))))) (.step 3 (.step 48 (.close 3)))))) (.step 3 (.step 32 (.step 48 (.step 50 (.step 48 (.close 3))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.close 53))))))) (.step 3 (.step 18 (.step 48 (.close 12))))) (.step 3 (.step 53 (.close 7))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 14696649931972027310843563361000416961428110638094890704942162988250685582587906259194844660941331772055135159844992219033107349712990745045470924165263335075927552977842937590387124889645348829276405760⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 10 0 (.step 55 (.split 11 0 (.split 34 0 (.split 16 0 (.step 55 (.step 3 (.step 7 (.step 3 (.close 21))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 9 (.step 18 (.step 31 (.close 48)))))) (.step 3 (.step 12 (.close 17))))) (.step 3 (.step 18 (.close 12)))))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 52)))))) (.step 52 (.split 45 1 (.split 55 1 (.split 11 0 (.split 16 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 52 (.step 62 (.close 3))) (.step 3 (.step 31 (.step 32 (.close 48))))) (.step 3 (.step 9 (.step 18 (.step 26 (.step 3 (.step 31 (.close 48)))))))) (.step 9 (.step 18 (.step 26 (.step 18 (.step 31 (.close 48))))))) (.step 18 (.step 3 (.step 27 (.step 44 (.step 3 (.close 48))))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 48 (.step 3 (.step 31 (.close 21)))))) (.step 3 (.step 48 (.close 3)))))) (.step 3 (.step 12 (.step 48 (.step 49 (.step 48 (.close 3))))))) (.step 3 (.step 22 (.step 31 (.step 48 (.step 49 (.step 21 (.close 52)))))))) (.step 3 (.step 18 (.step 34 (.close 48))))) (.step 3 (.step 52 (.close 7)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959694911853988495516326408048693131662584394368729267579177585613271594698356211184660152247110130950873948240776666135106944024616860473005483777446641664⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.reuse 0) (.run (.step 3 (.step 48 (.step 55 (.split 53 1 (.split 56 1 (.split 57 1 (.step 55 (.close 3)) (.step 48 (.step 3 (.close 60)))) (.step 3 (.step 22 (.step 31 (.step 48 (.step 21 (.step 59 (.close 60)))))))) (.step 3 (.step 18 (.step 48 (.step 34 (.step 56 (.close 60)))))))))))) (.run (.step 3 (.step 51 (.step 3 (.step 7 (.close 54))))))) (.reuse 1)) (.step 55 (.split 50 1 (.reuse 2) (.run (.step 48 (.step 52 (.step 55 (.step 58 (.split 45 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 52 (.split 30 0 (.step 52 (.close 3)) (.step 3 (.step 18 (.close 52))))) (.step 3 (.step 21 (.step 32 (.step 26 (.step 3 (.close 32))))))) (.step 9 (.step 21 (.step 52 (.step 3 (.step 18 (.step 31 (.step 3 (.close 48))))))))) (.step 9 (.step 21 (.step 34 (.close 52))))) (.step 21 (.step 27 (.step 52 (.step 3 (.close 18)))))) (.step 3 (.step 34 (.step 12 (.step 44 (.step 3 (.close 12))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.close 52))))))) (.step 3 (.step 48 (.close 52)))) (.step 3 (.step 18 (.step 34 (.close 48))))) (.step 3 (.step 48 (.step 3 (.close 52)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959694911853994592681463743971020048844673834146670182809924978135050616489292979488837534601836928423731494123532837672081790521927203144832982387378880512⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 47 1 (.reuse 0) (.run (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 55 1 (.split 10 0 (.step 60 (.split 45 1 (.split 11 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.split 43 0 (.step 50 (.close 3)) (.step 3 (.step 31 (.step 3 (.close 48))))) (.step 31 (.step 3 (.step 21 (.close 32))))) (.step 3 (.step 31 (.close 32)))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 18 (.step 31 (.close 48)))) (.step 50 (.close 3))) (.step 32 (.step 48 (.step 3 (.step 12 (.close 18))))))) (.step 3 (.step 31 (.step 3 (.step 18 (.step 12 (.close 48))))))) (.step 32 (.step 48 (.step 50 (.close 3))))))) (.step 48 (.step 50 (.step 51 (.step 50 (.step 3 (.step 26 (.step 44 (.close 48))))))))) (.step 28 (.step 48 (.step 50 (.step 51 (.step 50 (.step 3 (.step 16 (.step 21 (.step 16 (.close 31))))))))))) (.step 8 (.step 48 (.step 50 (.step 51 (.step 50 (.step 3 (.step 12 (.close 18))))))))) (.step 3 (.step 48 (.step 50 (.close 3))))) (.step 3 (.step 32 (.step 48 (.step 50 (.step 48 (.close 3))))))) (.step 3 (.step 12 (.step 48 (.step 49 (.step 53 (.step 55 (.step 48 (.step 3 (.close 18)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990267083870003099861869432894311455986916414392301921744782029664530156461517996173663058471232560752347912120573124247319565630963712⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.step 48 (.step 58 (.split 46 1 (.reuse 0) (.run (.split 47 1 (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 55 1 (.split 10 0 (.step 60 (.split 30 0 (.split 45 1 (.split 11 0 (.split 16 0 (.step 49 (.step 3 (.close 21))) (.step 18 (.step 31 (.close 48)))) (.step 49 (.close 3))) (.step 12 (.step 48 (.step 3 (.close 18))))) (.step 3 (.step 31 (.step 3 (.step 18 (.step 32 (.close 48)))))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 31)))))) (.step 12 (.step 48 (.step 49 (.close 3))))))) (.step 48 (.step 49 (.step 51 (.step 49 (.step 3 (.step 12 (.step 3 (.step 26 (.close 48)))))))))) (.step 28 (.step 48 (.step 49 (.step 51 (.step 49 (.step 3 (.step 21 (.close 31))))))))) (.step 8 (.step 48 (.step 49 (.step 51 (.step 49 (.step 3 (.step 12 (.close 18))))))))) (.step 3 (.step 48 (.step 49 (.close 3))))) (.step 3 (.step 32 (.step 48 (.step 50 (.step 48 (.close 3))))))) (.step 3 (.step 12 (.step 48 (.step 49 (.step 52 (.step 55 (.step 48 (.step 3 (.close 18))))))))))) (.step 48 (.step 49 (.step 3 (.step 50 (.step 51 (.step 49 (.step 3 (.step 12 (.step 3 (.step 32 (.step 3 (.close 48)))))))))))))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 9797766621314684873895712959598777356905878862334473725247485496648379858215221514099244892491368381026853549637640676157725998533763916352993648821034588551711149617337892696624276945063026478851031040⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 47 1 (.split 49 1 (.split 52 1 (.split 53 1 (.step 21 (.split 56 1 (.split 57 1 (.step 3 (.step 58 (.split 45 1 (.split 55 1 (.split 59 1 (.split 11 0 (.split 16 0 (.split 10 0 (.split 17 0 (.step 28 (.split 22 0 (.step 31 (.step 3 (.step 21 (.close 41)))) (.step 3 (.step 16 (.step 21 (.close 31)))))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 31)))))) (.step 3 (.step 12 (.step 16 (.close 31))))) (.step 3 (.step 18 (.step 16 (.step 21 (.close 31)))))) (.step 3 (.step 43 (.step 31 (.close 18))))) (.step 3 (.step 21 (.step 31 (.step 41 (.close 48)))))) (.step 3 (.step 5 (.step 31 (.step 21 (.step 41 (.close 48))))))) (.step 10 (.step 21 (.step 31 (.step 3 (.close 48)))))))) (.step 26 (.step 28 (.step 48 (.step 51 (.step 60 (.step 3 (.step 16 (.step 21 (.close 22)))))))))) (.step 28 (.step 41 (.step 58 (.step 41 (.split 45 1 (.split 51 1 (.split 59 1 (.step 59 (.close 3)) (.step 3 (.step 21 (.step 22 (.step 31 (.close 41)))))) (.step 3 (.close 21))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 41 (.close 3))))))))))))) (.step 3 (.step 4 (.step 5 (.step 41 (.step 51 (.step 24 (.step 43 (.step 60 (.split 16 0 (.step 43 (.step 31 (.step 14 (.step 41 (.close 56))))) (.step 3 (.step 18 (.close 41))))))))))))) (.step 3 (.step 21 (.step 31 (.step 48 (.close 41)))))) (.step 3 (.step 21 (.step 31 (.step 48 (.step 49 (.step 41 (.step 52 (.close 58))))))))) (.step 21 (.step 32 (.step 41 (.close 50))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230363111319255460318525553261787946959086412342497425559385908302398641431932280078503656322870418555403306532864⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 3 (.step 10 (.step 30 (.step 47 (.step 3 (.split 45 1 (.step 3 (.split 49 1 (.split 50 1 (.split 51 1 (.step 58 (.step 3 (.step 7 (.step 9 (.step 27 (.close 46)))))) (.step 3 (.close 46))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 3 (.step 9 (.step 27 (.step 46 (.close 52))))))) (.step 3 (.close 47)))))))))) (.run (.step 7 (.step 31 (.step 58 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.step 60 (.split 53 1 (.step 31 (.step 3 (.close 7))) (.step 3 (.close 31)))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 31 (.close 53))))))) (.step 3 (.step 9 (.step 18 (.step 31 (.close 52))))))) (.step 3 (.step 31 (.step 3 (.close 50))))) (.step 3 (.step 31 (.close 49))))))))) (.step 3 (.step 10 (.step 21 (.step 48 (.step 58 (.split 42 1 (.split 46 1 (.reuse 1) (.run (.step 21 (.step 41 (.step 48 (.step 28 (.step 49 (.step 41 (.step 51 (.step 60 (.step 49 (.step 3 (.step 21 (.close 22)))))))))))))) (.run (.step 3 (.step 21 (.step 31 (.step 3 (.step 28 (.close 41))))))))))))))
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

namespace Part9
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469336940644096410194278052263838533193596621954141684051910093037750905611628943079352584634368⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 58 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 53 1 (.split 57 1 (.step 31 (.step 3 (.close 7))) (.step 28 (.step 31 (.close 3)))) (.step 3 (.step 31 (.close 56)))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 22 (.step 31 (.close 53)))))))) (.step 3 (.step 9 (.step 18 (.step 22 (.step 31 (.close 52)))))))) (.step 3 (.step 31 (.step 3 (.close 50))))) (.step 3 (.step 31 (.close 49)))) (.step 7 (.step 31 (.step 7 (.step 22 (.close 39)))))) (.step 3 (.step 21 (.step 31 (.step 28 (.close 39))))))))))) (.run (.step 7 (.step 31 (.split 36 1 (.step 58 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 53 1 (.split 57 1 (.step 31 (.step 3 (.close 7))) (.step 28 (.step 31 (.close 3)))) (.step 3 (.step 31 (.close 14)))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 31 (.step 52 (.close 53)))))))) (.step 3 (.step 9 (.step 16 (.step 18 (.step 31 (.close 52)))))))) (.step 3 (.step 31 (.step 3 (.step 49 (.step 3 (.step 14 (.close 50)))))))) (.step 3 (.step 31 (.close 49)))) (.step 7 (.step 31 (.step 7 (.step 28 (.close 37)))))) (.step 3 (.step 16 (.step 21 (.step 28 (.step 31 (.step 37 (.close 3))))))))) (.step 7 (.step 31 (.close 37))))))))
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079166450589158585345283312557858417746063977995634000794829993665568252750725120⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 30 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 38 1 (.split 46 1 (.step 3 (.split 47 1 (.step 7 (.split 49 1 (.step 18 (.split 53 1 (.step 3 (.step 7 (.step 3 (.close 31)))) (.step 3 (.close 18)))) (.step 3 (.step 7 (.step 18 (.close 52)))))) (.step 3 (.step 18 (.close 31))))) (.step 3 (.step 18 (.step 31 (.close 49))))) (.step 3 (.close 31))))))))) (.run (.step 7 (.step 18 (.step 48 (.split 38 1 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 56 (.step 60 (.split 56 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.close 18)))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52))))) (.step 3 (.step 18 (.step 3 (.close 50))))) (.step 3 (.step 18 (.close 49)))) (.step 3 (.step 18 (.step 41 (.step 49 (.step 41 (.close 50)))))))))))) (.run (.step 7 (.step 18 (.step 48 (.split 22 1 (.split 38 1 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 56 (.split 56 1 (.split 57 1 (.step 18 (.step 3 (.close 7))) (.step 8 (.step 18 (.close 3)))) (.step 3 (.step 18 (.close 59)))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52))))) (.step 3 (.step 18 (.step 3 (.close 50))))) (.step 3 (.step 18 (.close 49)))) (.step 3 (.step 18 (.step 41 (.step 49 (.step 41 (.close 50))))))) (.step 7 (.step 18 (.step 7 (.step 8 (.close 20)))))))))))
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
def root : Box := ⟨2596148429267413814265251385835520, 9797766621314684873895712959598777356905878862334470448660200987817796464171149891257960871997697965256705486051572186336874329592461175368554743757640808137073857146151518381980827375090529162852564992⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.split 59 1 (.split 34 1 (.split 36 1 (.split 42 1 (.step 34 (.split 45 1 (.split 55 1 (.split 16 0 (.split 17 0 (.step 3 (.split 22 0 (.split 34 0 (.split 36 0 (.step 48 (.step 3 (.close 4))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 14 (.step 3 (.close 12)))))) (.step 8 (.step 18 (.step 3 (.close 14))))) (.step 8 (.step 18 (.step 14 (.close 3))))) (.step 12 (.step 18 (.step 3 (.step 14 (.close 48)))))) (.step 3 (.step 4 (.step 18 (.step 12 (.step 14 (.close 48)))))))) (.step 3 (.step 4 (.step 14 (.close 31))))) (.step 3 (.step 4 (.step 14 (.close 31))))) (.step 3 (.step 4 (.close 31)))) (.step 3 (.step 18 (.step 34 (.close 48)))))) (.step 12 (.step 8 (.step 18 (.step 44 (.step 48 (.step 51 (.step 60 (.step 3 (.step 12 (.close 14))))))))))) (.step 3 (.step 4 (.step 5 (.step 31 (.step 51 (.step 24 (.step 43 (.step 60 (.split 16 0 (.step 43 (.step 14 (.step 3 (.step 31 (.close 59))))) (.step 3 (.close 14)))))))))))) (.step 14 (.step 34 (.step 8 (.step 48 (.step 14 (.step 51 (.split 34 1 (.split 36 1 (.split 42 1 (.split 51 1 (.split 55 1 (.split 59 1 (.step 56 (.close 3)) (.step 3 (.close 14))) (.step 3 (.step 12 (.step 14 (.close 3))))) (.step 3 (.close 14))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14))))))))))) (.step 3 (.step 12 (.step 18 (.step 34 (.step 48 (.close 14))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2596148429267413814265251385835520, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079166450589158585345283312557861340749338639804066556593762840045872812780421120⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.step 30 (.step 34 (.step 48 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 50 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 34 (.step 48 (.close 14))))))) (.run (.step 12 (.step 14 (.step 18 (.step 48 (.step 8 (.step 50 (.step 14 (.step 51 (.step 60 (.step 50 (.step 3 (.step 12 (.close 14))))))))))))))) (.run (.step 12 (.step 8 (.step 14 (.step 18 (.step 34 (.close 49)))))))) (.run (.step 3 (.step 4 (.step 5 (.step 14 (.step 31 (.step 41 (.step 49 (.step 50 (.step 60 (.split 16 0 (.split 17 0 (.step 43 (.split 22 0 (.split 56 1 (.step 24 (.step 43 (.step 14 (.close 41)))) (.step 41 (.close 3))) (.step 3 (.step 14 (.close 41))))) (.step 3 (.step 5 (.step 14 (.close 41))))) (.step 3 (.step 5 (.step 14 (.close 41)))))))))))))))) (.run (.step 3 (.step 14 (.step 18 (.step 3 (.step 8 (.close 14)))))))) (.run (.step 3 (.step 14 (.step 18 (.step 3 (.step 8 (.step 14 (.close 3))))))))) (.run (.step 3 (.step 14 (.step 18 (.step 8 (.step 14 (.step 3 (.close 19)))))))))))))))
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079166450589158585345283312557861340749338639804069091894963296504675806186831872⟩
def references : Fin 2 → Box := ![Part10.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 11 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.step 48 (.split 22 1 (.split 38 1 (.split 46 1 (.split 47 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 56 (.split 56 1 (.split 57 1 (.step 18 (.step 3 (.close 7))) (.step 8 (.step 18 (.close 3)))) (.step 3 (.step 18 (.close 41)))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52))))) (.step 3 (.step 18 (.step 3 (.close 50))))) (.step 3 (.step 18 (.close 49)))) (.step 3 (.step 18 (.step 41 (.step 49 (.close 50)))))) (.step 7 (.step 18 (.step 7 (.step 8 (.close 19))))))) (.step 7 (.step 18 (.close 19)))))))) (.reuse 1)) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 11 1 (.split 38 1 (.split 46 1 (.step 3 (.split 47 1 (.step 7 (.split 49 1 (.step 18 (.split 53 1 (.step 3 (.step 7 (.step 3 (.close 31)))) (.step 3 (.close 14)))) (.step 3 (.step 7 (.step 18 (.close 52)))))) (.step 3 (.step 18 (.close 31))))) (.step 3 (.step 12 (.step 18 (.step 31 (.close 49)))))) (.step 3 (.close 31))) (.step 3 (.close 14)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case112
