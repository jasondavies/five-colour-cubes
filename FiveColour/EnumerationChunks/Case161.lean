module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case161
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475476381120379074882537373524376559072823736861674438656⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908284911715939576823, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857309521993999462306427087381105369261884265993783467999530422928012791073057088273642977565022587162213165827073, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544048682091164331652901596069789229568681009490311697678919790461277178950253217472830376031289520898509840960381794197411867257736731104847356183808782432035350411137253376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 10 0 (.split 12 0 (.step 7 (.step 9 (.step 43 (.step 7 (.step 38 (.close 16)))))) (.split 21 0 (.split 34 0 (.step 7 (.step 9 (.split 35 0 (.step 58 (.close 7)) (.step 7 (.step 16 (.step 21 (.close 22))))))) (.step 15 (.step 7 (.close 15)))) (.step 7 (.step 9 (.step 18 (.step 3 (.step 7 (.step 3 (.close 15))))))))) (.step 7 (.close 15))) (.step 7 (.step 18 (.close 15)))) (.step 7 (.step 18 (.close 15)))) (.split 10 0 (.step 29 (.step 75 (.split 12 0 (.step 7 (.step 18 (.step 16 (.close 21)))) (.step 75 (.step 7 (.close 4)))))) (.step 18 (.step 7 (.close 15))))) (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 3 (.close 7)))) (.step 3 (.step 70 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26))))))) (.split 67 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 12 0 (.step 7 (.step 9 (.step 26 (.step 7 (.step 26 (.step 43 (.step 7 (.step 38 (.close 16))))))))) (.step 9 (.step 26 (.step 15 (.step 43 (.step 58 (.close 7))))))) (.step 18 (.step 7 (.step 3 (.close 9))))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 3 (.close 4))))))) (.step 7 (.step 9 (.close 15)))) (.step 9 (.step 26 (.close 7)))) (.step 26 (.step 62 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459739099333684040314422763363333928265197587993432278272503716389658032955707765325523372828613584772605972034952237084313253572582300919050478809500896136290658942976⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 56 1 (.reuse 0) (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 28 (.step 59 (.step 3 (.step 7 (.close 16))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 21))))) (.step 48 (.split 30 0 (.split 35 0 (.split 43 0 (.split 49 0 (.step 59 (.close 3)) (.step 3 (.step 15 (.close 16)))) (.step 3 (.close 9))) (.step 22 (.step 21 (.step 9 (.step 37 (.step 3 (.close 26))))))) (.step 3 (.step 15 (.close 22)))))) (.step 3 (.step 7 (.step 58 (.close 15))))) (.step 29 (.step 75 (.split 10 0 (.split 12 0 (.step 59 (.close 3)) (.step 22 (.step 26 (.step 3 (.step 15 (.close 16)))))) (.step 3 (.close 15)))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 57 (.step 26 (.step 10 (.close 58))))))))) (.run (.step 58 (.step 18 (.step 48 (.step 62 (.step 9 (.step 58 (.step 3 (.step 15 (.step 18 (.step 16 (.step 26 (.close 16))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723026823511497443414970556934235212658789647265345092460553316133232956827146447906668353866233697537666408993898760707858752960933002955527436833994571776⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.split 21 0 (.split 34 0 (.step 7 (.step 18 (.step 9 (.close 57)))) (.step 15 (.step 29 (.split 38 0 (.step 7 (.step 37 (.step 21 (.close 22)))) (.step 38 (.step 3 (.step 16 (.close 22)))))))) (.step 7 (.step 9 (.step 18 (.step 3 (.step 7 (.step 3 (.close 22)))))))) (.step 9 (.step 15 (.close 57)))) (.step 9 (.step 26 (.step 57 (.step 3 (.close 7)))))) (.step 3 (.step 57 (.split 10 0 (.split 12 0 (.step 70 (.close 7)) (.step 9 (.step 15 (.step 26 (.step 7 (.close 21)))))) (.step 7 (.step 9 (.close 15))))))) (.step 9 (.step 26 (.step 57 (.step 3 (.close 7)))))) (.step 3 (.step 22 (.step 48 (.close 57))))) (.step 3 (.step 9 (.step 48 (.step 57 (.close 58)))))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 3 (.close 7)))) (.step 3 (.split 16 0 (.split 17 0 (.step 57 (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 54 (.step 3 (.step 7 (.step 9 (.step 26 (.step 21 (.close 54)))))))) (.step 54 (.step 62 (.close 7)))) (.step 3 (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.step 57 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11031304526203984395224077729546701486925133544052459742698464719678144919619690281947063874380578726072022452243037180911909063670611953424465837022768561784297584901051916036266755216323707486562198433881750270640128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 12 0 (.step 7 (.step 9 (.split 21 0 (.step 7 (.step 53 (.step 7 (.step 16 (.close 21))))) (.step 7 (.step 18 (.close 3)))))) (.step 9 (.split 21 0 (.split 35 0 (.split 34 0 (.step 53 (.step 3 (.step 16 (.close 21)))) (.step 7 (.close 15))) (.step 15 (.step 18 (.close 21)))) (.step 15 (.step 18 (.close 3)))))) (.step 18 (.step 7 (.step 3 (.close 9))))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 3 (.close 4))))))) (.step 7 (.step 9 (.close 15)))) (.step 9 (.step 38 (.step 18 (.step 26 (.step 7 (.step 15 (.close 16)))))))) (.split 72 1 (.split 10 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.close 7))) (.step 7 (.step 9 (.close 26)))) (.step 3 (.step 7 (.step 9 (.close 26))))) (.step 7 (.step 9 (.close 22)))) (.step 7 (.step 9 (.close 15)))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 53)))))))) (.step 53 (.step 62 (.step 4 (.close 7))))) (.step 5 (.step 48 (.step 57 (.step 21 (.step 9 (.step 53 (.step 3 (.step 15 (.step 16 (.close 26))))))))))) (.step 48 (.step 53 (.step 58 (.close 3))))) (.step 9 (.step 21 (.step 53 (.step 57 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304526203984395224077729546701486925133544052459742698464723026826708167958938546601868990775966991944351909590549483774613009683483527108458108348869427147074682187461561538176179134805871730051118640987635712000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 12 0 (.step 7 (.step 9 (.split 21 0 (.step 7 (.step 52 (.step 3 (.step 16 (.step 21 (.close 22)))))) (.step 7 (.step 18 (.close 3)))))) (.step 9 (.split 21 0 (.split 35 0 (.split 34 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.close 16))) (.step 7 (.close 15))) (.step 15 (.step 18 (.step 16 (.step 7 (.close 21)))))) (.step 15 (.step 18 (.close 3)))))) (.step 18 (.step 7 (.step 3 (.close 9))))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 3 (.close 4))))))) (.step 7 (.step 9 (.close 15)))) (.step 9 (.step 40 (.step 26 (.step 18 (.step 75 (.step 3 (.close 16)))))))) (.split 72 1 (.split 16 0 (.step 52 (.close 7)) (.step 7 (.step 9 (.close 21)))) (.step 3 (.step 7 (.step 9 (.step 26 (.step 21 (.close 52)))))))) (.step 52 (.step 62 (.step 4 (.close 7))))) (.step 5 (.step 48 (.step 16 (.step 57 (.step 9 (.step 52 (.step 3 (.step 26 (.close 21)))))))))) (.step 48 (.step 52 (.step 58 (.close 3))))) (.step 9 (.step 52 (.step 57 (.step 7 (.close 4)))))) (.step 52 (.step 54 (.step 57 (.split 72 1 (.split 16 0 (.step 52 (.close 7)) (.step 7 (.step 9 (.close 21)))) (.step 3 (.step 7 (.step 9 (.step 26 (.step 21 (.close 52))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617831357297686959020572369817757356961340814854993140088303142812754140780784464961388220071840389722120519486897915266145137459200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.step 7 (.close 9)) (.step 3 (.split 16 0 (.split 34 0 (.split 36 0 (.step 9 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 3 (.step 7 (.close 9)))) (.split 72 1 (.split 12 0 (.step 70 (.close 3)) (.step 3 (.step 46 (.close 7)))) (.step 3 (.step 7 (.close 9))))) (.step 9 (.step 7 (.step 27 (.close 46))))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.step 9 (.close 46))))) (.step 3 (.step 9 (.close 7)))) (.step 46 (.split 54 1 (.split 56 1 (.step 54 (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 9 (.close 7)))))) (.step 9 (.step 27 (.step 9 (.step 46 (.step 7 (.close 53))))))) (.step 9 (.step 27 (.step 9 (.step 46 (.step 7 (.close 52))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11031304526203979496340767072204264539074732142412855220466682097812183686204139665626697560538018359825071904667872598861549517683836392868337207485615442185542327512205752723865627891520593597041516542982429637345280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 7 (.step 16 (.close 26))) (.split 49 0 (.step 28 (.close 45)) (.step 5 (.step 7 (.step 21 (.step 16 (.close 26))))))) (.split 72 1 (.split 49 0 (.step 39 (.close 45)) (.step 7 (.step 22 (.step 26 (.step 16 (.close 21)))))) (.step 29 (.step 39 (.close 45))))) (.split 72 1 (.split 10 0 (.step 45 (.close 7)) (.step 7 (.close 15))) (.step 29 (.step 37 (.close 45))))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.step 26 (.step 45 (.step 15 (.step 16 (.close 21))))))) (.step 28 (.step 45 (.step 5 (.step 7 (.step 16 (.step 45 (.close 16)))))))) (.step 5 (.step 7 (.step 45 (.close 58))))) (.step 26 (.step 29 (.step 57 (.split 55 1 (.split 56 1 (.split 10 0 (.split 16 0 (.step 26 (.step 57 (.close 3))) (.step 7 (.step 21 (.close 15)))) (.step 7 (.step 15 (.close 22)))) (.step 22 (.step 26 (.step 48 (.step 57 (.close 3)))))) (.step 3 (.step 26 (.step 39 (.close 57))))))))) (.step 26 (.step 57 (.step 58 (.split 56 1 (.step 58 (.step 55 (.step 9 (.step 53 (.step 7 (.step 15 (.step 21 (.close 26)))))))) (.step 5 (.step 7 (.step 21 (.step 22 (.step 26 (.step 15 (.step 37 (.step 53 (.step 15 (.step 16 (.close 45)))))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935123878833676862859059191519952000574561784177332734219584746905368892660720046846350795927255220502369761820751691776⟩
def references : Fin 5 → Box := ![Part2.root, Part3.root, Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 5 := (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.split 51 1 (.reuse 1) (.run (.step 53 (.step 54 (.step 57 (.split 72 1 (.split 10 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 43 0 (.step 53 (.step 3 (.step 4 (.close 7)))) (.step 9 (.close 7))) (.step 7 (.step 9 (.close 26)))) (.step 3 (.step 7 (.step 9 (.close 26))))) (.step 7 (.step 9 (.close 22)))) (.step 7 (.step 9 (.close 15)))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 53))))))))))))) (.split 50 1 (.reuse 2) (.run (.step 52 (.split 56 1 (.split 72 1 (.split 16 0 (.step 52 (.step 7 (.close 21))) (.step 27 (.step 18 (.step 53 (.close 5))))) (.step 9 (.step 21 (.close 52)))) (.step 5 (.step 9 (.step 21 (.step 5 (.step 16 (.step 52 (.close 22)))))))))))) (.reuse 3)) (.step 7 (.split 49 1 (.reuse 4) (.run (.step 26 (.step 57 (.step 58 (.split 50 1 (.split 56 1 (.step 58 (.step 55 (.step 9 (.step 52 (.step 7 (.step 15 (.step 21 (.close 26)))))))) (.step 5 (.step 7 (.step 16 (.step 22 (.step 26 (.step 21 (.step 38 (.step 45 (.close 52)))))))))) (.step 9 (.step 52 (.step 55 (.step 58 (.close 52)))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11031304526203984395224077729546701486925133544052456053589153194253837624370217837571926411532114119350629292964699229366377061688721133877516040981786519173571729594532385932079605303202136883964171958944474781974528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 28 (.split 30 0 (.split 21 0 (.step 58 (.step 16 (.step 21 (.close 22)))) (.step 3 (.step 5 (.close 22)))) (.step 3 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 22))))) (.step 3 (.step 5 (.step 7 (.close 21))))) (.step 48 (.split 30 0 (.split 35 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 37 (.step 3 (.close 22))) (.step 3 (.close 15))) (.step 3 (.step 15 (.close 21)))) (.step 3 (.step 15 (.close 16)))) (.step 3 (.close 9))) (.step 21 (.step 28 (.step 37 (.step 38 (.close 3)))))) (.step 3 (.step 15 (.close 22)))))) (.step 3 (.step 7 (.step 38 (.step 3 (.step 7 (.close 15))))))) (.step 29 (.step 38 (.step 75 (.split 10 0 (.split 12 0 (.step 41 (.close 3)) (.step 21 (.step 26 (.step 37 (.close 3))))) (.step 3 (.close 15))))))) (.step 3 (.step 7 (.step 9 (.close 21))))) (.step 5 (.step 26 (.step 58 (.close 3))))) (.step 28 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 17 0 (.step 41 (.step 5 (.step 16 (.close 21)))) (.step 3 (.step 5 (.step 7 (.step 22 (.close 38)))))) (.step 59 (.step 3 (.close 16)))) (.step 3 (.step 7 (.step 38 (.close 41))))) (.step 38 (.step 41 (.close 16)))) (.step 3 (.step 7 (.step 21 (.close 26))))) (.step 5 (.step 21 (.step 22 (.step 26 (.step 57 (.close 41))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203979496340767072204264539074732142412855220466682097812186882874655189202742495293581668027368993580913270565841225350043646038334786301292994287311735235275191918852121326510881999467610518955286310420480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 34 0 (.split 38 0 (.split 42 0 (.step 7 (.step 16 (.step 22 (.step 16 (.close 21))))) (.split 49 0 (.step 39 (.close 7)) (.step 7 (.step 22 (.step 16 (.close 26)))))) (.split 72 1 (.split 49 0 (.step 28 (.step 39 (.close 4))) (.step 5 (.step 7 (.step 21 (.step 22 (.step 16 (.close 26))))))) (.step 28 (.step 38 (.close 39))))) (.split 72 1 (.split 10 0 (.split 12 0 (.split 49 0 (.step 39 (.close 7)) (.step 7 (.step 16 (.step 21 (.step 16 (.close 22)))))) (.step 29 (.close 37))) (.step 7 (.close 15))) (.step 29 (.step 37 (.close 39))))) (.step 7 (.step 15 (.step 22 (.step 15 (.close 26)))))) (.step 7 (.step 22 (.step 26 (.step 39 (.step 21 (.step 15 (.close 16)))))))) (.step 22 (.step 28 (.step 39 (.step 3 (.step 5 (.step 7 (.close 16)))))))) (.step 5 (.step 7 (.step 58 (.step 15 (.close 26)))))) (.step 22 (.step 29 (.step 57 (.step 3 (.close 7)))))) (.step 22 (.step 57 (.step 7 (.step 38 (.step 53 (.step 15 (.close 26)))))))) (.step 22 (.step 57 (.step 58 (.split 72 1 (.step 55 (.step 9 (.close 52))) (.step 7 (.step 26 (.step 15 (.close 21))))))))) (.split 49 1 (.step 45 (.split 50 1 (.step 39 (.step 7 (.step 45 (.step 37 (.close 57))))) (.step 7 (.step 38 (.step 57 (.step 37 (.step 45 (.step 52 (.close 53))))))))) (.step 7 (.step 22 (.step 26 (.step 57 (.step 45 (.step 38 (.close 52))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461412680096783792187847740147213938688412820858909813544413948989862974447128617762359849807982080938033020928⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 36 1 (.split 38 1 (.reuse 0) (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.reuse 1) (.run (.step 5 (.step 28 (.close 58))))) (.run (.step 3 (.step 21 (.step 48 (.step 57 (.step 10 (.step 41 (.close 3))))))))) (.run (.step 3 (.step 7 (.step 54 (.close 21)))))) (.run (.step 5 (.step 21 (.step 5 (.step 58 (.step 9 (.close 26)))))))) (.run (.step 5 (.step 48 (.step 16 (.step 57 (.step 58 (.step 3 (.step 9 (.step 26 (.close 52))))))))))) (.run (.step 3 (.step 7 (.step 9 (.close 10)))))) (.run (.step 7 (.step 38 (.step 45 (.step 76 (.step 28 (.split 49 1 (.step 41 (.split 54 1 (.step 45 (.step 3 (.close 16))) (.step 21 (.step 26 (.step 38 (.step 39 (.step 45 (.step 3 (.close 16))))))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 26 (.step 38 (.step 41 (.step 39 (.close 45)))))))))))))))))) (.step 7 (.split 38 1 (.reuse 2) (.run (.step 38 (.step 45 (.split 49 1 (.step 28 (.split 54 1 (.split 55 1 (.split 59 1 (.step 39 (.step 7 (.step 16 (.close 21)))) (.step 5 (.step 7 (.step 21 (.step 22 (.step 26 (.step 38 (.step 37 (.close 39))))))))) (.step 5 (.step 7 (.step 38 (.step 39 (.step 16 (.close 22))))))) (.step 21 (.step 22 (.step 38 (.step 39 (.close 16))))))) (.step 5 (.step 7 (.step 16 (.step 21 (.step 22 (.step 38 (.step 39 (.step 26 (.step 45 (.close 52)))))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617831357297686959020572372111255972951412326465814035390390083609319129949065588698977059458763265810605327556916468376270824013824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.step 29 (.split 12 0 (.step 38 (.step 7 (.step 18 (.step 16 (.close 21))))) (.split 17 0 (.split 22 0 (.step 21 (.step 37 (.step 38 (.close 3)))) (.step 18 (.step 15 (.close 22)))) (.step 18 (.step 15 (.close 22)))))) (.step 18 (.step 7 (.close 15)))) (.step 29 (.close 38))) (.step 3 (.step 7 (.step 9 (.step 21 (.step 26 (.close 38))))))) (.step 9 (.step 26 (.step 38 (.step 40 (.step 26 (.step 18 (.step 21 (.close 38))))))))) (.step 3 (.step 29 (.step 38 (.step 58 (.split 10 0 (.step 48 (.step 59 (.step 3 (.close 15)))) (.step 3 (.close 15)))))))) (.step 3 (.step 18 (.step 38 (.step 16 (.close 57)))))) (.step 9 (.step 21 (.step 38 (.step 57 (.step 7 (.close 26))))))) (.step 3 (.step 57 (.step 3 (.step 7 (.step 9 (.step 26 (.step 21 (.close 38))))))))) (.step 9 (.step 21 (.step 38 (.step 18 (.step 21 (.close 26))))))) (.step 9 (.step 53 (.step 57 (.step 58 (.step 75 (.split 51 1 (.split 59 1 (.split 67 1 (.step 40 (.split 10 0 (.step 21 (.step 18 (.split 55 0 (.step 38 (.step 3 (.step 7 (.close 26)))) (.step 16 (.step 3 (.close 38)))))) (.step 15 (.step 7 (.close 18))))) (.step 3 (.step 7 (.step 21 (.step 26 (.close 52)))))) (.step 26 (.step 40 (.step 52 (.close 22))))) (.step 3 (.step 7 (.close 52)))))))))) (.step 3 (.step 9 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732142412855220466682097812186882874655189202742492585896419862510729925327825834519996127628025269582453179967101580522978273587847875769054042699811960980388557184179271368704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 7 (.step 15 (.step 16 (.close 21)))) (.split 49 0 (.step 45 (.step 7 (.step 29 (.close 37)))) (.step 7 (.step 15 (.step 16 (.close 21)))))) (.split 72 1 (.split 49 0 (.step 28 (.step 37 (.step 3 (.close 7)))) (.step 5 (.step 7 (.step 15 (.close 16))))) (.step 28 (.close 37)))) (.split 10 0 (.split 12 0 (.split 72 1 (.split 49 0 (.step 39 (.step 7 (.step 21 (.close 22)))) (.step 7 (.step 16 (.step 21 (.step 16 (.close 22)))))) (.step 29 (.close 37))) (.step 29 (.close 37))) (.step 7 (.step 15 (.close 37))))) (.step 7 (.step 15 (.step 22 (.close 26))))) (.step 7 (.step 15 (.step 26 (.close 37))))) (.step 28 (.step 37 (.split 59 1 (.step 37 (.step 3 (.step 4 (.close 7)))) (.step 5 (.step 7 (.step 15 (.step 16 (.step 22 (.step 26 (.step 37 (.close 21)))))))))))) (.step 5 (.step 7 (.step 37 (.close 58))))) (.step 15 (.step 29 (.step 57 (.step 59 (.step 75 (.split 55 1 (.split 16 0 (.split 21 0 (.split 22 0 (.step 57 (.close 3)) (.step 7 (.step 22 (.close 26)))) (.step 7 (.step 22 (.close 26)))) (.step 7 (.close 21))) (.step 3 (.step 16 (.step 37 (.step 21 (.close 26)))))))))))) (.step 15 (.step 57 (.step 7 (.step 38 (.step 37 (.step 26 (.step 53 (.step 16 (.step 22 (.step 26 (.step 45 (.close 53))))))))))))) (.step 15 (.step 16 (.step 57 (.step 58 (.step 52 (.step 7 (.step 21 (.step 26 (.close 21)))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524437163561525551521343797895545544479060187221478691462333796577427328865207412684335326691328⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.step 37 (.step 7 (.step 15 (.close 37)))) (.step 15 (.step 29 (.step 37 (.step 7 (.step 26 (.step 37 (.step 21 (.step 39 (.step 45 (.close 52))))))))))) (.step 7 (.step 15 (.step 37 (.step 38 (.step 57 (.step 37 (.step 45 (.step 16 (.close 52))))))))))) (.step 7 (.step 15 (.step 16 (.step 26 (.step 52 (.step 37 (.close 52)))))))))) (.run (.step 16 (.step 38 (.step 28 (.step 37 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.step 37 (.step 3 (.step 4 (.close 7)))) (.step 5 (.step 7 (.step 15 (.step 16 (.step 21 (.step 26 (.close 37)))))))) (.step 37 (.step 7 (.step 21 (.close 41))))) (.step 5 (.step 7 (.step 37 (.step 21 (.close 41)))))) (.step 15 (.step 16 (.step 21 (.step 37 (.step 3 (.close 41))))))))))))) (.run (.split 49 1 (.step 45 (.split 50 1 (.step 37 (.step 39 (.step 7 (.step 15 (.step 37 (.step 21 (.step 22 (.step 26 (.step 39 (.close 52)))))))))) (.step 7 (.step 15 (.step 22 (.step 37 (.step 21 (.step 26 (.step 38 (.step 57 (.step 37 (.step 52 (.step 45 (.step 26 (.close 53))))))))))))))) (.step 7 (.step 15 (.step 16 (.step 37 (.step 52 (.step 37 (.close 52)))))))))) (.run (.step 29 (.step 38 (.step 37 (.close 7)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨3291009114642412084309938365114701009965471731267159728844701696, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475474883081200810705716985483987508781595380973834338304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 18 (.step 48 (.split 43 1 (.split 49 1 (.split 50 1 (.split 42 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 51 1 (.split 56 1 (.split 67 1 (.step 4 (.split 12 0 (.step 43 (.close 4)) (.step 4 (.step 7 (.close 9))))) (.step 3 (.step 7 (.step 9 (.close 26))))) (.step 3 (.close 4))) (.step 3 (.step 7 (.step 9 (.step 26 (.close 54)))))) (.step 4 (.step 7 (.step 15 (.step 7 (.close 17)))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.step 26 (.close 54)))))))) (.step 4 (.step 9 (.close 57)))) (.step 7 (.step 4 (.step 15 (.close 26))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.close 53))))))) (.step 3 (.step 4 (.step 7 (.step 9 (.step 18 (.close 52))))))) (.step 3 (.step 7 (.close 9)))))) (.step 3 (.step 4 (.step 5 (.step 18 (.step 4 (.close 22))))))) (.step 3 (.step 7 (.step 22 (.step 4 (.step 26 (.close 39))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 38)))))) (.step 3 (.step 7 (.step 37 (.step 4 (.close 38)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475476379658877437550305226057256210255407508648758345728⟩
def references : Fin 4 → Box := ![Part10.root, Part11.root, Part13.root, Part14.root]
def proof : Chunks.Proof 4 := (.split 17 1 (.split 21 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 1) (.run (.step 7 (.step 29 (.step 38 (.step 7 (.step 16 (.step 22 (.step 37 (.step 22 (.close 38))))))))))) (.run (.step 3 (.step 21 (.step 29 (.step 38 (.step 3 (.close 38)))))))) (.run (.step 7 (.step 29 (.step 38 (.step 39 (.step 7 (.step 22 (.step 37 (.close 38))))))))))) (.reuse 2)) (.run (.step 7 (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.step 9 (.step 18 (.close 53)))))) (.step 18 (.step 53 (.step 7 (.step 9 (.step 18 (.close 52))))))) (.step 18 (.close 7))))))) (.run (.step 7 (.step 18 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 4 (.close 18)))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 26 (.step 55 (.step 27 (.close 52))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 18 (.close 7))))))))) (.reuse 3)) (.run (.step 7 (.step 18 (.split 22 1 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 4 (.close 18)))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 22 (.step 55 (.step 27 (.close 52))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 18 (.close 7))))) (.step 7 (.step 18 (.step 52 (.close 53)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part13.excludes
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459739099333687395542992527424274267832344261539992317487265889213299267491276277664696884855754259700068420844055958144672121505228874554676553195958674381074333696000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 7 (.step 15 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 3 (.step 7 (.close 15)))))) (.step 3 (.step 15 (.close 3)))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 15 (.step 3 (.close 7)))) (.step 9 (.step 15 (.step 3 (.close 7))))) (.step 9 (.step 15 (.step 7 (.step 21 (.close 22)))))) (.step 3 (.step 15 (.split 10 0 (.split 21 0 (.split 34 0 (.split 35 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15))))))) (.step 9 (.step 15 (.step 7 (.step 18 (.step 3 (.step 21 (.step 22 (.close 26))))))))) (.step 3 (.step 16 (.step 22 (.step 15 (.step 48 (.step 9 (.step 15 (.step 3 (.close 26)))))))))) (.step 3 (.step 9 (.step 48 (.step 15 (.step 58 (.close 3))))))) (.step 3 (.step 15 (.step 57 (.step 62 (.step 70 (.split 16 0 (.split 21 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9))) (.step 7 (.close 9))))))))) (.step 9 (.step 15 (.step 21 (.step 15 (.close 53)))))) (.step 9 (.step 15 (.step 16 (.step 15 (.close 52)))))) (.step 3 (.step 9 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475476381120379074882537372256725958844594335364971233280⟩
def references : Fin 1 → Box := ![Part16.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 30 1 (.step 57 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 15 (.step 26 (.step 29 (.split 55 1 (.split 56 1 (.split 10 0 (.split 16 0 (.step 26 (.step 37 (.step 45 (.step 7 (.close 15))))) (.step 7 (.step 15 (.close 21)))) (.step 7 (.close 15))) (.step 16 (.step 22 (.step 26 (.step 37 (.step 45 (.step 3 (.close 15)))))))) (.step 3 (.step 15 (.step 26 (.step 22 (.close 38)))))))))))) (.run (.step 3 (.step 16 (.step 21 (.step 48 (.step 15 (.step 58 (.split 42 1 (.split 56 1 (.step 15 (.step 3 (.step 9 (.step 15 (.step 26 (.step 3 (.close 22))))))) (.step 10 (.step 22 (.step 15 (.step 3 (.step 15 (.step 26 (.step 3 (.close 38))))))))) (.step 10 (.step 26 (.step 37 (.step 38 (.step 15 (.close 22))))))))))))))) (.run (.step 7 (.step 15 (.step 22 (.step 29 (.step 57 (.step 37 (.step 39 (.step 75 (.split 55 1 (.split 21 0 (.step 39 (.step 7 (.close 15))) (.step 3 (.step 7 (.close 15)))) (.step 3 (.step 15 (.step 26 (.close 38))))))))))))))) (.run (.step 9 (.step 15 (.step 21 (.close 38)))))) (.run (.step 7 (.step 15 (.close 37)))))) (.run (.step 3 (.step 7 (.step 15 (.step 18 (.step 15 (.close 52)))))))) (.run (.step 3 (.step 4 (.step 7 (.step 15 (.step 18 (.step 15 (.close 26))))))))) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.close 7))))))) (.run (.step 3 (.step 4 (.step 7 (.step 18 (.step 15 (.close 22)))))))) (.run (.step 3 (.step 4 (.step 7 (.step 18 (.step 15 (.close 21))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475476381120379074882537373524376559072823736861674438656⟩
def references : Fin 2 → Box := ![Part15.root, Part17.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 35 1 (.split 38 1 (.step 7 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 4 (.close 18)))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 21 (.step 42 (.step 53 (.step 7 (.step 18 (.close 7))))))))) (.step 3 (.step 4 (.step 5 (.step 3 (.close 7)))))) (.step 3 (.step 4 (.step 18 (.close 7))))) (.step 7 (.step 18 (.step 52 (.close 53))))) (.step 7 (.step 18 (.split 35 1 (.step 18 (.split 38 1 (.step 7 (.step 19 (.step 25 (.step 52 (.close 53))))) (.step 4 (.step 5 (.close 19))))) (.step 3 (.step 4 (.step 18 (.close 19)))))))))))) (.reuse 1)) (.run (.step 7 (.step 18 (.split 12 1 (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 15 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18))))))) (.step 18 (.step 52 (.close 7)))) (.step 18 (.close 7)))) (.step 3 (.step 15 (.step 3 (.close 7)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part18.excludes
end FiveColour.Packed.EnumerationChunks.Case161
