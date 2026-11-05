module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case78
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773171863878174890806736363335616415772624338566512640⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨8697816018884211022835, 5789228615357111146520048038021683988769484383179567732815818416086450779233412664265074676308133956708084476189281768283666591250201089101977864971187095671403204624927834713340492290444220293581974657099303306801573789696, 0⟩]
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
def root : Box := ⟨3221225472, 5789228615351851005602038365663647631691745714007632075886312496697112349585736988441388256341501146092180898375065817305193665235883317317149411336457534886735056477029666469063267278505103026084798933320394276291193339904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 60 1 (.split 2 0 (.split 10 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.step 5 (.close 3))) (.step 31 (.close 3))) (.step 3 (.close 7))) (.step 7 (.step 3 (.close 5)))) (.step 3 (.step 5 (.close 3)))) (.step 7 (.step 3 (.close 5)))) (.step 7 (.step 18 (.close 3)))) (.step 31 (.step 18 (.step 5 (.close 3))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.step 3 (.split 22 0 (.step 12 (.step 5 (.step 3 (.close 16)))) (.step 3 (.close 5)))) (.step 10 (.step 18 (.step 31 (.close 5))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 12)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 5 (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))))) (.step 7 (.step 3 (.close 5)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 5 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 63 (.close 3))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17367685846055542743093384618702621871432296752599099927088260413234157054066650838055471332421944133672862146918030203275499182385984720202418278999254013923101320452108802563411058775725187489752204107183615850790706479104⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 73 1 (.split 74 1 (.reuse 0) (.run (.step 63 (.split 2 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 20 0 (.split 34 0 (.split 36 0 (.step 44 (.step 18 (.step 27 (.step 5 (.close 3))))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 17)))) (.step 5 (.step 3 (.step 17 (.close 21))))) (.step 3 (.step 18 (.close 3)))) (.step 3 (.step 18 (.close 3)))) (.step 18 (.step 3 (.step 18 (.close 3))))) (.step 23 (.step 63 (.step 3 (.step 23 (.close 3)))))) (.step 23 (.step 18 (.step 5 (.close 3)))))))) (.run (.step 63 (.split 2 0 (.split 60 1 (.split 74 1 (.split 14 0 (.split 10 0 (.split 13 0 (.split 16 0 (.step 10 (.step 76 (.step 3 (.step 5 (.step 18 (.close 5)))))) (.step 3 (.step 5 (.close 18)))) (.step 10 (.step 76 (.close 3)))) (.step 3 (.step 16 (.step 3 (.close 5))))) (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 39 0 (.step 16 (.step 5 (.close 3))) (.step 5 (.step 12 (.step 5 (.close 3))))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 5 (.close 63))) (.step 5 (.step 10 (.step 63 (.step 18 (.close 12)))))) (.step 5 (.step 10 (.step 63 (.split 10 0 (.split 30 0 (.split 40 0 (.split 16 0 (.step 76 (.close 3)) (.step 3 (.close 5))) (.step 5 (.close 3))) (.step 3 (.close 5))) (.step 3 (.close 5))))))))))
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
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895066722327963115254234945441966491108737060116113883864340250685194456562460794915434416171902033055184863622591166060879222985692422128597564491532846882260934463274941196311893667479552⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 62 1 (.split 67 1 (.split 69 1 (.reuse 0) (.run (.step 63 (.step 76 (.split 60 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.step 72 (.step 3 (.step 4 (.close 7)))) (.step 3 (.step 5 (.close 12)))) (.step 18 (.step 3 (.close 27)))) (.step 18 (.step 3 (.close 27)))) (.step 3 (.step 5 (.step 12 (.close 18))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 10 (.step 22 (.step 76 (.step 3 (.close 5)))))) (.step 18 (.step 63 (.step 10 (.step 18 (.step 22 (.step 4 (.close 12)))))))))))) (.run (.step 3 (.step 7 (.close 70))))) (.run (.step 63 (.step 65 (.step 76 (.split 67 1 (.split 60 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.step 65 (.split 10 0 (.step 65 (.step 3 (.close 5))) (.step 3 (.step 4 (.close 7))))) (.step 3 (.step 5 (.close 12)))) (.step 18 (.step 3 (.close 27)))) (.step 18 (.step 3 (.close 27)))) (.step 3 (.step 5 (.step 12 (.close 18))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.close 18)))) (.step 10 (.step 21 (.step 76 (.step 3 (.close 5)))))) (.step 65 (.step 3 (.close 5)))) (.step 63 (.step 10 (.step 21 (.step 18 (.step 22 (.step 4 (.close 12)))))))) (.step 3 (.step 65 (.close 7)))))))))
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
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075220535848183527813978853271330606774333605997516375111441791405663019418568551318242771938276723755565851862946004895468530961824571913395043852507147658565564575274562603398175129600⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 61 1 (.reuse 0) (.run (.step 63 (.step 64 (.step 76 (.split 67 1 (.split 60 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.split 34 0 (.split 10 0 (.split 13 0 (.split 30 0 (.split 36 0 (.step 64 (.close 3)) (.step 3 (.step 10 (.step 3 (.step 7 (.close 4)))))) (.step 3 (.step 7 (.close 52)))) (.step 10 (.step 34 (.step 3 (.close 12))))) (.step 3 (.step 18 (.step 3 (.close 52))))) (.step 3 (.step 10 (.step 18 (.step 31 (.close 3)))))) (.step 18 (.step 3 (.close 27)))) (.step 3 (.step 5 (.close 12)))) (.step 18 (.step 3 (.close 27)))) (.step 18 (.step 3 (.close 27)))) (.step 3 (.step 5 (.close 12)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.step 14 (.close 18))))) (.step 10 (.step 76 (.step 3 (.close 5))))) (.step 64 (.step 3 (.step 5 (.close 12))))) (.step 64 (.step 3 (.step 5 (.close 12))))) (.step 63 (.close 64))) (.step 3 (.step 64 (.close 7)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416711979597824, 17367685846055553016801216213680285552638276834970265342049554478986508512646879912974256500353264015694628316057543793220114438805050671772177939675996014607305187094456598228832355401967657372571886963543352026620209659904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 63 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 74 1 (.step 3 (.split 60 1 (.split 2 0 (.split 13 0 (.split 10 0 (.split 20 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 34 0 (.step 27 (.step 61 (.step 3 (.close 5)))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 18 (.step 3 (.close 5))))) (.step 27 (.step 34 (.step 18 (.step 5 (.step 3 (.close 5))))))) (.step 27 (.split 17 0 (.split 22 0 (.step 22 (.step 61 (.step 3 (.close 5)))) (.step 3 (.step 18 (.close 3)))) (.step 18 (.close 3))))) (.step 3 (.step 18 (.step 5 (.step 3 (.close 4)))))) (.step 34 (.step 27 (.split 10 0 (.split 20 0 (.step 61 (.step 3 (.close 5))) (.step 5 (.close 3))) (.step 3 (.close 5)))))) (.step 27 (.split 10 0 (.split 20 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 51 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 5 (.close 3))) (.step 3 (.close 5))))) (.step 5 (.step 3 (.close 61))))) (.step 27 (.step 44 (.step 61 (.step 5 (.close 3)))))) (.step 3 (.step 5 (.step 22 (.step 23 (.step 44 (.close 5))))))) (.step 3 (.step 5 (.step 22 (.step 18 (.step 12 (.close 61))))))) (.step 3 (.step 5 (.step 61 (.step 63 (.step 65 (.step 61 (.step 5 (.step 12 (.step 21 (.step 12 (.close 22)))))))))))) (.step 3 (.step 12 (.step 61 (.step 63 (.step 64 (.step 5 (.step 61 (.step 5 (.step 21 (.close 22)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087302011879424, 17367685846055553016806115096990942895075224693476189584672690932506759691863021613572594649901932577077141806670821548211882739616001329840385466074953774052523833749228110249972960686167080924994216046986460218683821129728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 22 (.step 63 (.split 58 1 (.step 76 (.split 59 1 (.split 61 1 (.split 62 1 (.split 74 1 (.step 22 (.split 60 1 (.step 3 (.split 73 1 (.split 2 0 (.split 14 0 (.split 20 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 42 0 (.split 16 0 (.step 58 (.step 10 (.step 18 (.close 3)))) (.step 3 (.step 5 (.step 12 (.step 14 (.close 18)))))) (.step 3 (.step 22 (.step 3 (.step 5 (.close 16)))))) (.step 43 (.close 3))) (.step 3 (.close 22))) (.step 31 (.step 3 (.step 22 (.step 3 (.close 5)))))) (.step 10 (.step 18 (.close 5)))) (.step 18 (.close 5))) (.step 43 (.step 18 (.step 10 (.step 22 (.step 31 (.close 5))))))) (.step 10 (.step 22 (.step 76 (.step 5 (.close 3))))))) (.step 10 (.step 18 (.step 22 (.step 31 (.step 5 (.close 12)))))))) (.step 3 (.step 5 (.step 18 (.step 5 (.close 16)))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 21 (.step 22 (.step 68 (.step 76 (.step 3 (.step 43 (.close 3)))))))))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 22 (.step 64 (.step 68 (.step 64 (.step 76 (.split 2 0 (.split 34 0 (.split 39 0 (.step 64 (.close 3)) (.step 3 (.step 5 (.close 12)))) (.step 3 (.step 12 (.step 16 (.close 21))))) (.step 3 (.step 5 (.close 12)))))))))))))) (.step 3 (.step 5 (.step 22 (.step 23 (.step 31 (.step 5 (.step 16 (.close 21)))))))))) (.step 3 (.step 5 (.step 22 (.step 43 (.step 58 (.step 17 (.step 21 (.step 23 (.close 21))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584672690932506759691863021613572594649901932577077141806670821548211882739616001329840385466074953774052523833749228110249972960686167080924994216046986460218683821129728⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 3 := (.split 56 1 (.split 58 1 (.step 63 (.split 59 1 (.reuse 0) (.run (.step 44 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 60 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 62 (.step 3 (.step 7 (.close 5)))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 27)))))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 27)))))) (.step 27 (.step 31 (.step 44 (.step 3 (.step 4 (.close 17))))))) (.step 3 (.step 5 (.step 16 (.close 21))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.step 31 (.close 5))))) (.step 3 (.step 5 (.step 31 (.close 16))))) (.step 3 (.step 62 (.close 7)))) (.step 3 (.step 26 (.step 44 (.step 62 (.step 7 (.close 70))))))) (.step 3 (.step 53 (.step 65 (.step 7 (.step 9 (.step 27 (.close 52)))))))) (.step 3 (.step 64 (.step 7 (.step 9 (.step 27 (.close 53))))))))))) (.step 3 (.split 59 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 27 (.step 44 (.step 61 (.step 3 (.close 5))))))))))) (.reuse 2))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745968720583371162137149592003791758831406565404122338738836088895356449131219108554789770027347620923915900471918352297829662546093571543762919968576897024⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 55 1 (.reuse 0) (.run (.step 3 (.step 63 (.split 56 1 (.split 58 1 (.split 59 1 (.step 63 (.split 61 1 (.split 62 1 (.split 69 1 (.step 58 (.step 3 (.split 74 1 (.step 58 (.split 73 1 (.step 3 (.step 18 (.step 3 (.close 5)))) (.step 5 (.close 3)))) (.step 5 (.step 18 (.step 5 (.close 17))))))) (.step 3 (.step 5 (.step 18 (.step 5 (.step 12 (.step 22 (.step 12 (.close 21))))))))) (.step 3 (.step 18 (.step 5 (.step 58 (.step 5 (.step 21 (.step 22 (.step 12 (.close 65)))))))))) (.step 3 (.step 12 (.step 18 (.step 64 (.step 5 (.step 21 (.close 22))))))))) (.step 3 (.step 31 (.step 44 (.step 48 (.step 3 (.step 5 (.step 16 (.close 58))))))))) (.step 5 (.step 27 (.step 58 (.step 48 (.step 3 (.close 32))))))) (.step 3 (.step 5 (.step 22 (.step 28 (.step 58 (.step 16 (.close 22)))))))))))) (.run (.step 3 (.step 58 (.step 62 (.step 63 (.step 72 (.split 56 1 (.step 3 (.step 61 (.step 70 (.split 61 1 (.split 62 1 (.split 74 1 (.step 3 (.close 54)) (.step 3 (.close 4))) (.step 3 (.close 54))) (.step 3 (.step 54 (.close 7))))))) (.step 3 (.step 4 (.close 18)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 17367685846055553016806115096990942895075224689416013706545967561906957395344963788917120737587762021749513055636528331423020479676458404902399140109806281996823540154707706666310464030163060926458418167009002208679167000576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 63 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 55 1 (.split 59 1 (.split 60 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 20 0 (.split 22 0 (.split 30 0 (.split 38 0 (.step 53 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 16 (.close 21))))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 3 (.step 7 (.close 52)))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 27)))))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 27)))))) (.step 27 (.step 31 (.step 52 (.step 3 (.step 18 (.step 3 (.close 5)))))))) (.step 3 (.step 5 (.step 16 (.close 21))))) (.step 3 (.close 5))) (.step 3 (.step 5 (.step 31 (.close 5))))) (.step 53 (.close 3))) (.step 31 (.step 48 (.step 3 (.step 5 (.close 16)))))) (.step 27 (.step 44 (.step 48 (.step 55 (.step 63 (.split 2 0 (.split 13 0 (.step 53 (.close 3)) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 17)))))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 58 (.step 62 (.step 5 (.step 16 (.close 22)))))))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 53 (.step 7 (.step 9 (.step 27 (.close 52))))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 53 (.step 64 (.step 7 (.step 9 (.step 27 (.close 53))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 17367685846055553016806115096990942895075224689423928286941031756639982877864278757512095921668832461854125770027712976224414967941304912051672573190033113726008092374074202418040499871573533290741317586953095231161446170624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 56 1 (.split 58 1 (.step 63 (.split 61 1 (.split 62 1 (.split 67 1 (.split 69 1 (.split 73 1 (.split 74 1 (.split 55 1 (.split 59 1 (.split 60 1 (.split 2 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 52 (.split 20 0 (.split 22 0 (.split 30 0 (.step 3 (.close 5)) (.step 3 (.close 7))) (.step 3 (.close 4))) (.step 3 (.close 5)))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 27)))))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 27)))))) (.step 27 (.step 31 (.step 34 (.close 3))))) (.step 3 (.step 5 (.close 16)))) (.step 3 (.close 5))) (.step 3 (.step 5 (.step 31 (.close 5))))) (.step 52 (.close 3))) (.step 31 (.step 48 (.step 3 (.step 5 (.close 16)))))) (.step 27 (.step 34 (.step 44 (.step 31 (.step 48 (.step 55 (.step 3 (.step 23 (.close 3)))))))))) (.step 3 (.step 5 (.step 23 (.step 52 (.step 58 (.step 62 (.step 5 (.step 16 (.step 21 (.close 22))))))))))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.step 52 (.step 7 (.step 9 (.step 27 (.close 53))))))) (.step 3 (.step 52 (.step 53 (.step 64 (.step 65 (.step 4 (.step 7 (.step 9 (.close 27)))))))))) (.step 3 (.step 52 (.close 64))))) (.step 3 (.step 5 (.step 27 (.step 34 (.step 52 (.step 61 (.step 3 (.step 5 (.close 31)))))))))) (.step 3 (.step 5 (.step 22 (.step 23 (.step 31 (.step 58 (.close 21)))))))) (.step 3 (.step 52 (.close 54)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713798035928887745312018171789332443379310520245463206389347738687803161787417513005260560974562891600865266539428538578590862671872⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.step 58 (.step 62 (.split 51 1 (.split 56 1 (.split 58 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 27 (.step 53 (.step 61 (.split 60 1 (.split 55 1 (.split 10 0 (.split 30 0 (.split 49 0 (.split 50 2 (.split 55 0 (.step 3 (.step 61 (.step 3 (.close 5)))) (.step 5 (.step 31 (.step 32 (.step 3 (.step 40 (.step 44 (.step 3 (.close 5))))))))) (.step 53 (.step 31 (.step 21 (.close 18))))) (.step 34 (.step 52 (.step 53 (.step 3 (.close 5)))))) (.step 3 (.step 18 (.step 17 (.close 21))))) (.step 3 (.step 12 (.step 18 (.step 12 (.close 17)))))) (.step 5 (.step 32 (.step 31 (.step 48 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 31 (.step 32 (.step 17 (.close 44)))))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 22 (.step 23 (.step 31 (.step 5 (.step 16 (.step 53 (.step 16 (.close 58))))))))))))) (.run (.step 3 (.step 53 (.close 54)))))))) (.step 58 (.step 62 (.split 50 1 (.reuse 2) (.run (.step 52 (.step 53 (.step 58 (.step 52 (.step 53 (.step 3 (.step 5 (.step 21 (.step 22 (.close 31))))))))))))))) (.run (.step 3 (.step 10 (.step 27 (.step 52 (.step 53 (.step 62 (.step 64 (.step 65 (.step 72 (.split 51 1 (.step 58 (.step 3 (.step 10 (.step 3 (.close 46))))) (.step 3 (.close 46))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343948716212224, 17367685846055553016801216213680285552638276834962350769202415133896575783926233688542407190691047457978195482719778461478504771993403938203260908783902016196523152382341197922772742780124839618736996242645717134098171953152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 60 1 (.split 74 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 22 0 (.split 43 0 (.split 49 0 (.step 43 (.close 3)) (.step 3 (.step 5 (.step 3 (.step 5 (.close 17)))))) (.step 3 (.step 5 (.close 3)))) (.step 3 (.step 5 (.close 3)))) (.step 18 (.step 5 (.step 17 (.close 21))))) (.step 3 (.step 5 (.step 3 (.step 5 (.step 12 (.close 18))))))) (.step 3 (.step 5 (.step 3 (.step 5 (.close 18)))))) (.step 5 (.step 18 (.step 5 (.step 17 (.close 21)))))) (.step 10 (.step 43 (.close 3)))) (.step 10 (.step 22 (.step 36 (.step 68 (.step 76 (.split 2 0 (.split 34 0 (.step 72 (.close 3)) (.step 3 (.step 12 (.step 16 (.close 21))))) (.step 3 (.step 5 (.close 12)))))))))) (.step 10 (.step 21 (.step 32 (.step 65 (.step 68 (.step 65 (.step 76 (.split 2 0 (.split 34 0 (.step 65 (.close 3)) (.step 3 (.step 16 (.step 22 (.close 31))))) (.step 3 (.step 5 (.close 12)))))))))))) (.step 10 (.step 12 (.step 34 (.step 64 (.step 65 (.step 68 (.step 64 (.step 76 (.split 2 0 (.split 36 0 (.split 39 0 (.step 43 (.close 3)) (.step 3 (.step 5 (.close 21)))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 5 (.close 21))))))))))))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 5 (.step 3 (.step 18 (.step 23 (.close 17))))))) (.step 4 (.step 5 (.step 31 (.step 63 (.step 24 (.close 64))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304548574784714603058847686183674818285285461366754565556395368432740616111839243313834104455039013669509253913887586123776⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 40 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 44 (.step 76 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 61 1 (.split 62 1 (.split 69 1 (.step 43 (.step 31 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 22 (.step 16 (.close 31)))))) (.step 3 (.step 10 (.step 18 (.step 21 (.step 31 (.close 65))))))) (.step 3 (.step 10 (.step 18 (.step 31 (.close 64)))))))) (.step 7 (.step 9 (.step 18 (.step 21 (.close 31)))))) (.step 7 (.step 9 (.step 18 (.step 31 (.step 21 (.close 44))))))))))))) (.step 3 (.step 31 (.step 43 (.step 58 (.split 49 1 (.step 43 (.split 50 1 (.split 58 1 (.split 59 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 23 (.step 21 (.close 22))))))) (.run (.step 3 (.step 5 (.step 27 (.step 31 (.close 61))))))) (.run (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.close 53))))))))) (.run (.step 3 (.step 5 (.step 23 (.step 31 (.step 34 (.step 52 (.step 5 (.close 21)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17367685846055553016801216213680285552638276834962350769206100644077065570403032081687903547029833513852348956526233921757615722712616815700533905534926496138212546260806626448410744245376470868562581624612098780765562601472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 63 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 27 (.split 74 1 (.step 3 (.split 60 1 (.split 2 0 (.split 55 1 (.split 13 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 34 0 (.step 27 (.step 42 (.step 3 (.close 5)))) (.step 3 (.step 5 (.close 17)))) (.step 5 (.step 3 (.step 17 (.close 21))))) (.step 3 (.step 18 (.step 3 (.close 5))))) (.step 3 (.step 18 (.step 3 (.close 5))))) (.step 27 (.step 34 (.step 42 (.close 3))))) (.step 3 (.step 18 (.step 5 (.step 3 (.close 4)))))) (.step 34 (.step 27 (.split 10 0 (.step 32 (.step 21 (.step 5 (.close 3)))) (.step 3 (.close 5)))))) (.step 27 (.step 32 (.step 42 (.step 3 (.close 5)))))) (.step 27 (.step 42 (.split 10 0 (.split 20 0 (.split 16 0 (.step 32 (.split 51 0 (.step 5 (.close 3)) (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 5 (.close 3))) (.step 3 (.close 5)))))) (.step 5 (.step 3 (.step 32 (.step 18 (.step 3 (.step 18 (.close 17))))))))) (.step 27 (.step 42 (.step 5 (.step 3 (.step 5 (.close 12)))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 44 (.step 5 (.close 3)))))))) (.step 3 (.step 5 (.step 42 (.step 58 (.step 42 (.step 5 (.step 12 (.close 21))))))))) (.step 3 (.step 5 (.step 21 (.close 42))))) (.step 3 (.step 12 (.step 42 (.step 58 (.step 63 (.step 64 (.step 5 (.step 42 (.step 5 (.step 21 (.close 22))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 17367685846055553016801216213680285548287190256396348411218724915685925496203043979789151707104786405188925639230476890720121847186775952603528800237860389921678468241355192004771426262415441987773777256335949744490962485248⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 76 (.split 59 1 (.split 61 1 (.split 69 1 (.split 74 1 (.step 10 (.step 21 (.split 51 1 (.split 55 1 (.split 60 1 (.step 3 (.split 73 1 (.split 2 0 (.split 14 0 (.split 20 0 (.split 34 0 (.split 36 0 (.split 39 0 (.split 42 0 (.split 16 0 (.step 58 (.step 10 (.step 18 (.close 3)))) (.step 3 (.step 5 (.step 12 (.step 14 (.close 18)))))) (.step 3 (.step 21 (.step 3 (.close 5))))) (.step 43 (.close 3))) (.step 3 (.step 22 (.step 21 (.step 3 (.close 5)))))) (.step 31 (.step 3 (.step 31 (.close 3))))) (.step 10 (.step 18 (.close 5)))) (.step 18 (.close 5))) (.step 43 (.step 18 (.step 10 (.step 21 (.step 31 (.close 5))))))) (.step 10 (.step 21 (.step 76 (.step 5 (.close 3))))))) (.step 10 (.step 18 (.step 21 (.step 31 (.step 5 (.close 12))))))) (.step 3 (.step 5 (.step 28 (.step 41 (.close 3)))))) (.step 3 (.close 4))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 5 (.close 16))))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 21 (.step 22 (.step 58 (.step 68 (.step 43 (.step 3 (.step 16 (.close 31))))))))))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 21 (.step 58 (.step 64 (.step 68 (.step 76 (.split 2 0 (.step 68 (.step 64 (.step 43 (.step 3 (.close 41))))) (.step 3 (.step 5 (.step 12 (.step 5 (.step 18 (.close 22))))))))))))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 5 (.step 31 (.step 16 (.close 41)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 17367685846055553016801216213680285548287190256404262991613789110418944281365175192877860844199742551398751497966644854090816376269844621228547338538525533836015668949598612526907578260562196994443393093410667820129769750528⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 49 1 (.step 43 (.split 56 1 (.split 58 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 21 (.step 22 (.step 32 (.step 42 (.step 43 (.step 3 (.close 5))))))))))) (.run (.step 5 (.step 10 (.step 21 (.step 22 (.step 41 (.step 43 (.step 58 (.split 61 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 60 1 (.split 67 1 (.split 74 1 (.split 73 1 (.split 13 0 (.split 20 0 (.split 49 0 (.step 28 (.split 2 0 (.split 14 0 (.step 41 (.close 3)) (.step 18 (.step 31 (.step 5 (.close 12))))) (.step 41 (.close 3)))) (.step 3 (.step 21 (.step 22 (.step 3 (.step 5 (.step 16 (.close 31)))))))) (.step 10 (.step 18 (.step 21 (.step 18 (.step 5 (.step 16 (.close 22)))))))) (.step 10 (.step 21 (.step 22 (.step 41 (.close 3)))))) (.step 10 (.step 21 (.step 22 (.close 41))))) (.step 5 (.step 18 (.step 22 (.step 16 (.close 31)))))) (.step 3 (.step 4 (.step 18 (.close 41))))) (.step 5 (.step 10 (.step 18 (.step 21 (.step 22 (.step 31 (.step 5 (.close 41))))))))) (.step 3 (.step 5 (.step 21 (.step 22 (.step 31 (.step 16 (.close 41)))))))) (.step 3 (.step 5 (.step 28 (.close 41))))) (.step 3 (.step 4 (.step 18 (.close 41))))) (.step 3 (.step 10 (.step 18 (.step 21 (.step 22 (.step 41 (.step 3 (.close 5))))))))))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.step 42 (.step 5 (.step 16 (.step 41 (.step 52 (.close 58))))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 31 (.step 3 (.step 22 (.step 39 (.close 41))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166758516101496759435687649185804237208348593941749699307833035094941216393943691907902920799325732263098844184576⟩
def references : Fin 3 → Box := ![Part12.root, Part13.root, Part15.root]
def proof : Chunks.Proof 3 := (.split 38 1 (.split 39 1 (.reuse 0) (.step 3 (.step 31 (.step 58 (.split 40 1 (.split 49 1 (.split 50 1 (.split 56 1 (.step 44 (.split 58 1 (.split 59 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 27 (.step 42 (.step 44 (.step 42 (.step 3 (.step 5 (.close 31))))))))))) (.run (.step 5 (.step 27 (.step 42 (.step 61 (.split 60 1 (.split 61 1 (.step 42 (.step 32 (.step 44 (.step 42 (.close 3))))) (.step 3 (.step 5 (.step 12 (.close 42))))) (.step 5 (.step 32 (.close 42))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 22 (.step 31 (.step 41 (.step 43 (.step 58 (.step 23 (.step 31 (.step 32 (.step 31 (.close 42))))))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 27 (.step 32 (.step 42 (.close 3))))))))) (.run (.step 3 (.step 5 (.step 27 (.step 34 (.step 42 (.step 44 (.step 42 (.step 52 (.step 3 (.close 5)))))))))))) (.run (.step 3 (.step 5 (.step 21 (.step 27 (.step 31 (.close 42)))))))))))) (.step 3 (.step 21 (.step 43 (.step 58 (.step 63 (.split 39 1 (.reuse 2) (.run (.step 3 (.step 5 (.step 21 (.step 31 (.step 32 (.step 41 (.step 42 (.step 43 (.step 3 (.close 5))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986546435457024, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586499036568112700443540233863090806942043748746684259013921504867150170088084256787048122286080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.step 34 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 3))) (.step 10 (.step 31 (.close 3)))) (.step 3 (.step 10 (.step 16 (.step 7 (.step 22 (.step 21 (.close 31)))))))) (.step 3 (.step 10 (.step 16 (.step 18 (.step 21 (.step 31 (.close 64)))))))) (.step 3 (.step 10 (.step 16 (.step 18 (.step 31 (.close 64))))))))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 21 (.close 31))))))) (.step 7 (.step 9 (.step 15 (.step 16 (.step 18 (.step 31 (.step 21 (.close 34))))))))) (.step 31 (.step 7 (.step 22 (.close 37))))) (.step 16 (.step 21 (.step 31 (.step 3 (.step 28 (.close 37))))))) (.step 31 (.close 37))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837619031759681657804967772300230982253521903501355020598440361984⟩
def references : Fin 2 → Box := ![Part16.root, Part17.root]
def proof : Chunks.Proof 2 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 36 (.step 31 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.step 7 (.step 31 (.close 3))) (.step 10 (.step 22 (.step 3 (.step 31 (.close 3)))))) (.step 3 (.step 10 (.step 18 (.step 22 (.step 16 (.close 31))))))) (.step 3 (.step 10 (.step 18 (.step 21 (.step 22 (.step 31 (.close 65)))))))) (.step 3 (.step 10 (.step 18 (.step 22 (.step 31 (.close 64))))))))) (.step 7 (.step 9 (.step 18 (.step 21 (.step 22 (.close 31))))))) (.step 7 (.step 9 (.step 18 (.step 22 (.step 31 (.close 21))))))) (.step 31 (.step 7 (.step 22 (.close 39))))) (.step 21 (.step 31 (.step 3 (.step 22 (.close 39)))))))))))) (.reuse 1)) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 38 1 (.step 3 (.step 18 (.step 42 (.step 3 (.step 7 (.close 18)))))) (.step 3 (.close 31))))))))) (.run (.step 7 (.step 18 (.step 26 (.split 38 1 (.split 39 1 (.split 40 1 (.step 18 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 61 1 (.split 62 1 (.step 7 (.step 5 (.close 18))) (.step 18 (.close 26))) (.step 18 (.close 26)))) (.step 3 (.step 7 (.close 18)))) (.step 18 (.close 3))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 53)))))) (.step 3 (.step 7 (.step 18 (.step 26 (.close 52))))))) (.step 3 (.step 5 (.step 18 (.close 24))))) (.step 5 (.step 18 (.step 23 (.close 42))))) (.step 3 (.step 5 (.step 18 (.close 24))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨3213876088517980551083924184682325205044405987565588891828224, 11584105258621123583049441304845207688494695732571619412538015541862596403905330917262551660650182042322578144664960619586144564894416743005095141457782086974900409649478569696769581066089942461582230600825682062389650915328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 56 1 (.split 58 1 (.step 3 (.step 31 (.split 59 1 (.split 61 1 (.step 23 (.split 62 1 (.split 69 1 (.split 40 1 (.split 73 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 40 0 (.split 42 0 (.split 43 0 (.split 51 0 (.step 23 (.close 3)) (.step 3 (.step 5 (.close 3)))) (.step 3 (.step 5 (.close 3)))) (.step 3 (.step 5 (.close 3)))) (.step 18 (.step 5 (.close 17)))) (.step 5 (.step 18 (.close 5)))) (.step 3 (.step 5 (.step 3 (.step 5 (.step 17 (.close 21))))))) (.step 3 (.step 5 (.step 3 (.step 5 (.step 17 (.close 21))))))) (.step 5 (.step 3 (.step 18 (.step 16 (.close 22)))))) (.step 18 (.step 5 (.close 23)))) (.step 3 (.step 5 (.step 18 (.close 34))))) (.step 3 (.step 5 (.step 18 (.step 34 (.close 65))))))) (.step 3 (.step 5 (.step 18 (.step 34 (.step 63 (.close 64))))))) (.step 3 (.step 5 (.step 9 (.step 23 (.step 26 (.step 44 (.step 55 (.split 2 0 (.split 13 0 (.step 62 (.close 3)) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 17)))))))))))))) (.step 5 (.step 9 (.step 22 (.step 11 (.step 23 (.step 3 (.close 61)))))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 22 (.step 23 (.step 31 (.close 43))))))))) (.step 4 (.step 5 (.step 18 (.step 23 (.step 21 (.close 40))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨3223322624, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635770175785518856224415664578726947907342586184113061888⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 5 (.step 18 (.step 31 (.step 5 (.step 58 (.step 63 (.split 38 1 (.split 39 1 (.split 49 1 (.step 5 (.split 50 1 (.split 56 1 (.split 59 1 (.split 61 1 (.step 5 (.split 62 1 (.split 69 1 (.split 58 1 (.split 73 1 (.step 18 (.step 31 (.step 5 (.split 74 1 (.split 16 0 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 5 (.close 3)))))) (.step 5 (.step 3 (.step 16 (.step 22 (.step 16 (.close 31))))))) (.step 5 (.step 3 (.step 18 (.step 3 (.step 23 (.close 18))))))) (.step 3 (.step 5 (.step 12 (.close 21))))) (.step 3 (.step 5 (.step 12 (.step 21 (.step 12 (.step 22 (.step 12 (.close 65)))))))))) (.step 3 (.step 5 (.step 12 (.step 63 (.step 64 (.step 5 (.close 21)))))))) (.step 3 (.step 5 (.step 17 (.step 21 (.step 23 (.close 21))))))) (.step 5 (.step 22 (.step 31 (.step 22 (.step 43 (.close 16))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 44 (.step 34 (.close 53))))))))) (.step 3 (.step 5 (.step 23 (.step 34 (.step 52 (.step 5 (.close 21)))))))) (.step 5 (.step 21 (.step 32 (.close 42))))) (.step 5 (.step 21 (.step 31 (.step 41 (.step 21 (.step 43 (.step 16 (.close 22)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635770175785518856224415664578726947907342586184113061888⟩
def references : Fin 3 → Box := ![Part18.root, Part19.root, Part20.root]
def proof : Chunks.Proof 3 := (.split 2 1 (.split 20 1 (.reuse 0) (.step 3 (.step 18 (.step 23 (.step 31 (.step 43 (.step 63 (.split 38 1 (.split 39 1 (.split 49 1 (.split 50 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 9 (.step 21 (.step 23 (.step 32 (.step 48 (.step 53 (.step 55 (.step 53 (.step 61 (.split 2 0 (.split 13 0 (.step 23 (.close 3)) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 17))))))))))))))))) (.run (.step 3 (.step 5 (.step 9 (.step 12 (.step 23 (.step 34 (.step 48 (.step 52 (.step 55 (.step 52 (.step 61 (.split 2 0 (.split 16 0 (.step 52 (.close 3)) (.step 3 (.step 18 (.close 21)))) (.step 3 (.step 5 (.close 21))))))))))))))))) (.run (.step 5 (.step 9 (.step 21 (.step 11 (.step 23 (.step 32 (.step 42 (.step 23 (.step 3 (.step 5 (.close 3))))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 18 (.step 31 (.step 23 (.close 41)))))))))))))))) (.reuse 2))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes
  · exact Part19.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2923003274661805836407369665432566039315086311424, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773171863875384575397982132634016287532880845826162688⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.step 21 (.split 2 1 (.split 17 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.step 18 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 61 1 (.split 62 1 (.step 7 (.step 5 (.close 18))) (.step 18 (.close 21))) (.step 18 (.close 21)))) (.step 3 (.step 7 (.close 18)))) (.step 18 (.close 3))) (.step 3 (.step 7 (.step 18 (.step 3 (.step 42 (.close 53))))))) (.step 3 (.step 7 (.step 18 (.step 21 (.step 42 (.close 52)))))))) (.step 3 (.step 5 (.step 18 (.close 21))))) (.step 5 (.step 18 (.step 21 (.close 42))))) (.step 3 (.step 5 (.step 18 (.close 21))))) (.step 18 (.step 7 (.step 11 (.step 17 (.close 19)))))) (.step 18 (.step 7 (.step 11 (.close 19))))) (.step 3 (.step 5 (.step 18 (.close 5)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2787593149816327892691964784081048409473024, 17367685846055553016801216213680285552634023581504247751423625426016782130226440994815378625252275428337967361093092772502230002534379860528189820954631011574954696067260958189329036883982309262917867344608438147469128237056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 62 1 (.step 23 (.step 31 (.step 34 (.split 69 1 (.split 73 1 (.step 27 (.split 74 1 (.step 3 (.step 63 (.split 2 1 (.split 55 1 (.split 2 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 20 0 (.split 34 0 (.split 36 0 (.step 63 (.step 18 (.step 27 (.step 31 (.step 34 (.step 5 (.close 3))))))) (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.close 17)))) (.step 5 (.step 3 (.close 17)))) (.step 3 (.step 18 (.close 3)))) (.step 3 (.step 18 (.close 3)))) (.step 18 (.step 3 (.close 17)))) (.step 23 (.step 63 (.step 3 (.step 23 (.close 3)))))) (.step 23 (.step 18 (.step 5 (.close 3))))) (.step 12 (.step 18 (.step 5 (.close 17))))) (.step 5 (.close 3))))) (.split 2 1 (.split 51 1 (.split 55 1 (.split 60 1 (.split 67 1 (.split 2 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 11 (.step 77 (.close 3))) (.step 18 (.close 17))) (.step 11 (.step 18 (.step 17 (.close 3))))) (.step 11 (.step 18 (.close 17)))) (.step 11 (.step 23 (.close 17)))) (.step 3 (.close 4))) (.step 3 (.step 5 (.step 11 (.close 17))))) (.step 11 (.step 12 (.step 17 (.close 3))))) (.step 3 (.step 4 (.close 17)))) (.step 3 (.step 5 (.close 17)))))) (.step 3 (.step 5 (.step 12 (.step 23 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 16 (.step 5 (.step 17 (.close 12)))))))))) (.step 3 (.step 5 (.step 16 (.step 18 (.step 16 (.step 17 (.step 34 (.step 17 (.step 42 (.step 61 (.close 63)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2787593149816327892691964784081048409473024, 17367685846055553016801216213680285552634023589616684927289378992844347530700759205736508397632245612012484310264036178795814061067657110350660927205353754612146644032889282610529399694823058908592708095362798976546858074112⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 17 (.step 23 (.step 27 (.step 34 (.step 44 (.step 31 (.step 48 (.step 23 (.step 3 (.close 17)))))))))))))) (.run (.step 5 (.step 11 (.step 12 (.step 17 (.step 18 (.step 23 (.step 27 (.step 34 (.step 36 (.step 44 (.step 61 (.step 5 (.step 17 (.step 3 (.step 5 (.close 17)))))))))))))))))) (.run (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 31 (.step 5 (.close 17)))))))))) (.run (.step 3 (.step 5 (.step 17 (.step 23 (.step 27 (.step 31 (.step 34 (.step 48 (.step 53 (.step 61 (.step 63 (.split 2 0 (.step 55 (.step 62 (.step 23 (.split 13 0 (.split 16 0 (.step 55 (.step 3 (.step 23 (.step 44 (.close 3))))) (.step 3 (.close 17))) (.step 3 (.step 5 (.close 17))))))) (.step 3 (.step 17 (.step 5 (.step 21 (.step 5 (.close 17)))))))))))))))))))) (.run (.step 3 (.step 5 (.step 17 (.step 18 (.step 17 (.step 23 (.step 17 (.close 31)))))))))) (.run (.step 5 (.step 11 (.step 12 (.step 17 (.step 18 (.step 23 (.step 27 (.step 34 (.step 36 (.step 42 (.step 44 (.step 42 (.step 5 (.step 3 (.close 17))))))))))))))))) (.run (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 21 (.step 31 (.step 5 (.close 17))))))))))) (.run (.step 3 (.step 5 (.step 17 (.step 18 (.close 3))))))) (.run (.step 3 (.step 5 (.step 17 (.step 18 (.step 3 (.step 11 (.close 17)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773171863878172168547798460526708252316961891014410240⟩
def references : Fin 3 → Box := ![Part21.root, Part22.root, Part24.root]
def proof : Chunks.Proof 3 := (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 5 (.step 7 (.step 18 (.step 22 (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.step 18 (.step 61 (.split 49 1 (.split 50 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 18 (.step 23 (.step 77 (.split 2 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 5 (.close 18))))))) (.step 5 (.step 18 (.close 22)))) (.step 5 (.step 18 (.close 22)))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 7 (.step 18 (.step 3 (.close 53)))))) (.step 3 (.step 7 (.step 18 (.step 3 (.step 22 (.close 52))))))))) (.step 3 (.step 5 (.step 18 (.close 22))))) (.step 5 (.step 18 (.step 22 (.close 42))))) (.step 3 (.step 5 (.step 18 (.close 22))))) (.step 18 (.step 7 (.step 11 (.step 17 (.close 20)))))))))))) (.reuse 1)) (.step 3 (.step 5 (.step 23 (.step 31 (.step 34 (.step 58 (.step 63 (.split 16 1 (.reuse 2) (.run (.step 3 (.step 5 (.step 17 (.step 18 (.step 11 (.step 17 (.step 3 (.close 19))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes
  · exact Part22.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2722258935367507707706996859457366917120, 17356389790220709873110487066644460702415839187353095256594049037293331496658421945255739050613304692774076066702230075960938096359633577823194779165703975104789866207408588940129496776896981627536663888661197141089879851008⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 74 1 (.split 2 1 (.split 34 1 (.split 36 1 (.split 40 1 (.step 3 (.split 16 1 (.step 22 (.step 26 (.split 42 1 (.split 2 0 (.split 60 1 (.split 14 0 (.split 10 0 (.split 13 2 (.split 16 0 (.step 10 (.split 20 0 (.split 17 0 (.split 22 0 (.step 16 (.step 3 (.step 5 (.close 3)))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 16 (.close 3)))) (.step 3 (.step 5 (.step 12 (.step 14 (.close 16)))))) (.step 10 (.split 38 0 (.split 39 0 (.step 16 (.close 3)) (.step 12 (.step 21 (.step 5 (.close 3))))) (.step 16 (.close 3))))) (.step 3 (.step 12 (.close 3)))) (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 12 (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5))) (.step 3 (.close 5)))) (.step 10 (.step 12 (.step 16 (.step 3 (.close 5)))))) (.step 10 (.step 16 (.split 10 0 (.split 30 0 (.split 40 0 (.split 16 0 (.step 12 (.step 16 (.step 3 (.close 5)))) (.step 3 (.close 5))) (.step 5 (.close 3))) (.step 3 (.close 5))) (.step 3 (.close 5)))))) (.step 10 (.step 16 (.step 26 (.step 31 (.close 3)))))))) (.step 3 (.step 5 (.step 14 (.close 18)))))) (.step 10 (.step 12 (.step 16 (.step 3 (.step 18 (.step 31 (.step 34 (.step 43 (.close 3)))))))))) (.step 3 (.step 10 (.step 16 (.step 22 (.close 31)))))) (.step 3 (.step 10 (.step 16 (.step 3 (.close 5)))))) (.step 3 (.step 5 (.step 3 (.close 16))))) (.step 3 (.step 5 (.step 18 (.step 31 (.close 63)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2722258935367507707706996859457366917120, 17367685846055553016801216213680285552638272693559219064082581208677257066199391014339344585401561976558121372885714878568594916466328961451185298997428222105579836821850473017805314809649544651819495385381760655027028885504⟩
def references : Fin 1 → Box := ![Part26.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 69 1 (.split 73 1 (.reuse 0) (.run (.step 5 (.step 10 (.step 16 (.step 21 (.step 22 (.step 26 (.step 16 (.step 3 (.step 12 (.close 76)))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 16 (.step 18 (.step 22 (.step 16 (.step 3 (.close 5))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 16 (.step 21 (.step 22 (.step 16 (.step 5 (.step 18 (.close 65)))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 12 (.step 16 (.step 18 (.step 21 (.step 22 (.step 3 (.step 26 (.step 3 (.step 34 (.close 64))))))))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 17 (.step 31 (.step 16 (.step 5 (.close 17)))))))))) (.run (.step 3 (.step 5 (.step 12 (.step 17 (.step 21 (.step 22 (.step 23 (.step 34 (.step 43 (.step 62 (.step 65 (.split 73 1 (.step 5 (.close 3)) (.step 5 (.step 3 (.close 16))))))))))))))))) (.run (.step 5 (.step 10 (.step 16 (.step 21 (.step 22 (.step 26 (.step 31 (.step 43 (.step 16 (.step 5 (.step 3 (.close 16)))))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 12 (.step 16 (.step 31 (.step 58 (.step 3 (.close 18))))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 17 (.step 21 (.step 31 (.step 58 (.step 62 (.step 16 (.step 5 (.close 17))))))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 17 (.step 34 (.step 16 (.step 21 (.close 52))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨3221225472, 17367685846055553016806115096990942895075224693476189584680061952867745975273757927985468041713803451304553623166763213191141796586503110640065369415712770757837622245635773171863878174890806736363335616415772624338566512640⟩
def references : Fin 2 → Box := ![Part25.root, Part27.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 13 1 (.reuse 0) (.step 3 (.step 5 (.step 18 (.step 31 (.step 63 (.step 43 (.split 14 1 (.split 20 1 (.split 38 1 (.split 39 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 12 (.step 17 (.step 21 (.step 22 (.step 23 (.step 34 (.step 36 (.step 41 (.step 43 (.step 62 (.step 72 (.split 58 1 (.split 73 1 (.split 59 1 (.step 5 (.close 3)) (.step 3 (.close 5))) (.step 5 (.step 3 (.close 16)))) (.step 5 (.step 3 (.close 17))))))))))))))))))) (.run (.step 5 (.step 10 (.step 16 (.step 21 (.step 22 (.step 26 (.step 31 (.step 41 (.step 43 (.step 16 (.step 5 (.step 3 (.step 16 (.step 3 (.close 5))))))))))))))))) (.run (.step 3 (.step 5 (.step 10 (.step 16 (.step 18 (.step 16 (.close 3))))))))) (.run (.step 3 (.step 5 (.step 12 (.step 16 (.step 17 (.step 18 (.step 23 (.step 3 (.step 5 (.close 34))))))))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 13 1 (.split 14 1 (.split 38 1 (.step 3 (.step 18 (.split 39 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.close 17))))) (.step 3 (.close 16))) (.step 3 (.close 17))) (.step 3 (.close 16)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes
  · exact Part27.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part28

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part28.excludes
end FiveColour.Packed.ProjectedChunks.Case78
