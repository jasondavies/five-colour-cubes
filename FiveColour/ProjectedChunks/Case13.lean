module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case13
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087146421207577694727294249362682625979366454932906013879649123174400⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908127039438309876725, 5783586103091957813513448549065477704101332453097102403927030543402094319394105471139001457519683735055563446735996945722220748621036873120632536151717721108831365180663724494250117897918544598836570003200200417898320102401, 0⟩]
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
def root : Box := ⟨2147483648, 5515652263101992197612038864773350743462566775890767394370008915011218877801894671274203033914486895084061655970370187687930313911541865831692570949043573210603788847363647124681341312989683227466453006939825635328000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 11 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 3 (.close 31)) (.split 38 0 (.step 18 (.close 31)) (.step 21 (.step 3 (.close 31))))) (.step 7 (.close 31))) (.step 28 (.step 18 (.close 29)))) (.step 7 (.step 26 (.step 18 (.close 26))))) (.step 48 (.step 43 (.step 18 (.close 31))))) (.step 7 (.step 18 (.step 29 (.close 48))))) (.step 7 (.split 17 0 (.step 18 (.step 21 (.step 18 (.close 21)))) (.step 7 (.close 18))))) (.split 21 0 (.split 26 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.split 52 0 (.split 34 0 (.step 9 (.step 18 (.step 48 (.close 3)))) (.step 15 (.step 7 (.close 15)))) (.step 48 (.close 3))) (.step 21 (.step 16 (.step 3 (.close 31))))) (.step 26 (.close 3))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 29 (.step 18 (.close 12)))) (.step 18 (.step 9 (.step 43 (.step 15 (.close 48))))))) (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 48 (.step 3 (.step 48 (.close 37)))) (.step 7 (.close 4))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.split 16 0 (.step 18 (.step 15 (.step 3 (.close 48)))) (.step 3 (.close 4))))) (.split 11 0 (.split 12 0 (.step 7 (.step 3 (.step 28 (.step 3 (.close 12))))) (.step 3 (.step 18 (.step 15 (.close 3))))) (.step 7 (.close 4)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133547913223299695288696184241696596342196103242393249572419370787222679026303986231653224482511536339810733103250509593739501357629604086557552589410083744984795164034987983872⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 55 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 1 0 (.reuse 0) (.run (.split 10 0 (.split 11 0 (.split 12 0 (.split 16 0 (.step 48 (.step 4 (.step 3 (.close 16)))) (.step 4 (.close 18))) (.step 18 (.step 9 (.step 48 (.close 3))))) (.step 4 (.step 3 (.step 4 (.close 3))))) (.step 7 (.close 4))))) (.run (.step 29 (.split 1 0 (.split 10 0 (.split 11 0 (.step 75 (.split 21 0 (.split 49 0 (.step 48 (.step 75 (.step 3 (.close 31)))) (.step 18 (.step 26 (.close 31)))) (.step 18 (.close 31)))) (.step 18 (.step 4 (.close 31)))) (.step 7 (.step 18 (.close 31)))) (.step 18 (.step 4 (.close 75))))))) (.run (.step 7 (.step 3 (.close 29))))) (.run (.split 67 1 (.split 72 1 (.split 1 0 (.step 55 (.split 10 0 (.split 11 0 (.split 12 0 (.split 26 0 (.split 16 0 (.split 34 0 (.step 55 (.close 62)) (.step 7 (.close 58))) (.step 7 (.close 48))) (.step 18 (.close 58))) (.step 55 (.step 9 (.step 18 (.step 15 (.step 26 (.close 58))))))) (.step 18 (.step 48 (.close 3)))) (.step 55 (.close 7)))) (.step 18 (.step 3 (.close 48)))) (.step 18 (.close 26))) (.split 11 0 (.step 62 (.step 7 (.close 3))) (.step 3 (.close 7)))))) (.run (.step 58 (.close 3))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534785137368582231835142109317809293086644176423858456398680430791070438184226612762404843440047463108334916126680523622478849759470000964880191463498239904665198134272⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 56 1 (.split 57 1 (.reuse 0) (.run (.split 55 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 35 0 (.step 60 (.close 3)) (.step 48 (.close 3))) (.step 48 (.close 28))) (.step 3 (.step 18 (.close 48)))) (.step 48 (.step 31 (.step 26 (.close 48))))) (.split 12 0 (.step 60 (.close 18)) (.step 24 (.close 48)))) (.step 3 (.step 49 (.close 60)))) (.split 11 0 (.step 4 (.step 18 (.step 4 (.step 48 (.close 38))))) (.step 4 (.close 3)))) (.step 29 (.step 48 (.close 60)))) (.step 3 (.close 12))) (.step 48 (.close 58))) (.step 58 (.close 3))))) (.run (.split 67 1 (.split 72 1 (.split 55 1 (.split 59 1 (.split 1 0 (.split 11 0 (.split 57 1 (.split 10 0 (.step 28 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 48 (.step 59 (.close 3))) (.step 5 (.close 59))) (.step 3 (.close 31))) (.step 5 (.close 59))) (.step 5 (.step 3 (.close 21)))) (.step 48 (.step 59 (.step 3 (.close 31)))))) (.step 7 (.step 3 (.close 59)))) (.step 51 (.step 60 (.close 3)))) (.step 28 (.step 43 (.step 51 (.step 3 (.close 31)))))) (.step 3 (.step 4 (.close 59)))) (.step 5 (.close 58))) (.step 5 (.close 58))) (.step 26 (.step 28 (.step 58 (.split 1 0 (.split 10 0 (.step 48 (.step 59 (.close 75))) (.step 3 (.close 59))) (.step 3 (.step 4 (.close 59)))))))) (.step 3 (.step 7 (.close 9))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 11031304526203984395224077729546701486925133551781534788740014394268379120531819348651001804599423503971605359281005493818757289259852300997359346882239685368211784741871633147641089303216174864302348287081847191503872⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.step 24 (.split 11 0 (.split 12 0 (.split 1 0 (.split 26 0 (.split 16 0 (.split 34 0 (.split 36 0 (.step 18 (.step 8 (.step 3 (.close 18)))) (.step 4 (.close 3))) (.step 4 (.close 3))) (.step 7 (.close 18))) (.step 3 (.step 4 (.close 3)))) (.step 3 (.close 4))) (.step 4 (.step 3 (.close 48)))) (.step 24 (.split 34 0 (.split 36 0 (.split 38 0 (.split 1 0 (.step 3 (.step 48 (.close 56))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 4 (.close 3))) (.step 4 (.close 7)))))) (.step 3 (.step 23 (.close 7)))) (.step 4 (.close 3))) (.step 3 (.close 7))) (.step 44 (.step 18 (.step 4 (.close 48))))) (.step 3 (.step 60 (.step 8 (.close 48))))) (.step 3 (.close 51))) (.step 5 (.step 18 (.close 48)))) (.step 4 (.close 18))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534788740017826667209185836676842508756242478459700886550662485728328465052324780716240951346204884617168549080966694791531743124370107260261147688966308234399263491072⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 45 1 (.split 52 1 (.split 53 1 (.split 54 1 (.reuse 0) (.run (.split 55 1 (.split 56 1 (.split 57 1 (.split 1 0 (.split 10 0 (.split 67 1 (.split 16 0 (.split 17 0 (.step 57 (.step 9 (.split 59 1 (.split 21 0 (.split 72 1 (.split 26 0 (.step 48 (.close 3)) (.step 28 (.step 18 (.close 29)))) (.step 26 (.step 18 (.close 48)))) (.step 48 (.close 7))) (.step 26 (.step 48 (.close 3)))))) (.step 22 (.step 18 (.step 29 (.step 48 (.close 18)))))) (.step 21 (.step 18 (.close 57)))) (.step 3 (.step 7 (.step 9 (.close 57))))) (.step 18 (.step 15 (.step 18 (.step 29 (.step 55 (.close 57))))))) (.step 57 (.split 10 0 (.step 57 (.step 4 (.close 31))) (.step 3 (.close 4))))) (.step 48 (.step 26 (.step 48 (.close 3))))) (.step 22 (.step 51 (.step 48 (.close 57))))) (.step 48 (.step 9 (.close 58)))))) (.reuse 1)) (.run (.step 55 (.split 53 1 (.split 54 1 (.split 57 1 (.split 56 1 (.split 11 0 (.split 12 0 (.split 46 0 (.split 47 0 (.step 55 (.step 18 (.step 9 (.step 23 (.close 55))))) (.step 55 (.close 48))) (.step 55 (.close 48))) (.step 55 (.close 31))) (.step 3 (.close 48))) (.step 3 (.close 48))) (.step 48 (.close 3))) (.step 55 (.close 31))) (.step 3 (.step 18 (.close 48))))))) (.run (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.step 48 (.close 18)) (.step 48 (.close 3))) (.step 31 (.close 48))) (.step 48 (.close 57))) (.step 4 (.close 48)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11031304526203984395224077729546701486925133551781534788740017830022434558930222259272275681726748831908608759679869737685425977079253382266137623639969013183132727774450382973873442891707949107221494187896140042601472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 51 1 (.split 53 1 (.split 54 1 (.split 45 1 (.split 56 1 (.split 57 1 (.split 59 1 (.step 58 (.split 67 1 (.split 72 1 (.split 1 0 (.step 55 (.split 10 0 (.split 11 0 (.split 12 0 (.split 26 0 (.split 16 0 (.split 34 0 (.step 55 (.step 7 (.step 9 (.step 18 (.close 21))))) (.step 7 (.close 58))) (.step 7 (.close 48))) (.step 18 (.close 58))) (.step 55 (.step 18 (.step 15 (.step 21 (.step 3 (.close 53))))))) (.step 18 (.step 48 (.close 3)))) (.step 55 (.close 7)))) (.step 18 (.step 3 (.close 48)))) (.step 18 (.step 9 (.step 21 (.step 26 (.step 18 (.close 48))))))) (.split 72 1 (.split 12 0 (.step 7 (.step 3 (.close 7))) (.step 3 (.close 53))) (.step 3 (.close 53))))) (.step 62 (.split 11 0 (.step 62 (.close 3)) (.step 18 (.step 48 (.close 7)))))) (.step 26 (.step 48 (.step 55 (.close 3))))) (.step 5 (.step 48 (.step 21 (.step 7 (.step 22 (.close 53))))))) (.step 48 (.close 53))) (.step 21 (.step 55 (.step 9 (.step 53 (.step 57 (.close 48))))))) (.step 4 (.step 48 (.close 53)))) (.step 3 (.step 57 (.step 61 (.step 53 (.step 70 (.split 72 1 (.split 12 0 (.step 7 (.step 3 (.close 7))) (.step 3 (.close 53))) (.step 3 (.close 53)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304526203984395224077729546701486925133551781534788740017830022437755600737782848320616482312140110905846244367826615884456855980038646798175079964016376582264790228850636650911212089794045948589779100293683741696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 50 1 (.split 51 1 (.split 53 1 (.split 54 1 (.split 45 1 (.split 56 1 (.split 57 1 (.split 59 1 (.step 58 (.split 67 1 (.split 72 1 (.split 1 0 (.step 55 (.split 10 0 (.split 11 0 (.split 12 0 (.split 26 0 (.split 16 0 (.split 34 0 (.step 55 (.step 7 (.step 9 (.step 18 (.close 21))))) (.step 7 (.close 58))) (.step 7 (.close 48))) (.step 18 (.close 58))) (.step 55 (.step 18 (.step 15 (.step 16 (.step 7 (.close 12))))))) (.step 18 (.step 48 (.close 3)))) (.step 55 (.close 7)))) (.step 18 (.step 3 (.close 48)))) (.step 18 (.step 26 (.step 29 (.step 18 (.close 58)))))) (.split 72 1 (.split 12 0 (.step 7 (.step 3 (.close 7))) (.step 3 (.close 52))) (.step 3 (.close 52))))) (.step 62 (.split 11 0 (.step 62 (.close 3)) (.step 18 (.step 48 (.close 7)))))) (.step 26 (.step 48 (.step 55 (.close 3))))) (.step 5 (.step 16 (.close 58)))) (.step 48 (.close 52))) (.step 55 (.step 57 (.step 9 (.step 48 (.close 18)))))) (.step 4 (.step 48 (.close 52)))) (.step 3 (.step 57 (.step 61 (.step 52 (.step 70 (.split 72 1 (.split 12 0 (.step 7 (.step 3 (.close 7))) (.step 3 (.close 52))) (.step 3 (.close 52))))))))) (.step 55 (.split 53 1 (.split 56 1 (.step 52 (.split 72 1 (.split 11 0 (.split 16 0 (.step 52 (.close 58)) (.step 18 (.step 48 (.close 7)))) (.step 18 (.step 48 (.close 7)))) (.step 21 (.step 18 (.step 26 (.close 52)))))) (.step 21 (.step 48 (.close 52)))) (.step 18 (.step 27 (.step 34 (.step 48 (.close 3))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨6097165137335922326917182089439777940915230747392521779021790936768304177382354726797472857545882756171536974846497310342671827498612079722496, 11031304526203984395224077729546701486925133551781534788740017830022437755603786365416988577645770731155625735214825441989580717745490934115182327168655193739981001219001792014736679699513042701119925692849598649861120⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 45 1 (.split 67 1 (.split 72 1 (.split 1 0 (.split 10 0 (.split 12 0 (.step 60 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 30 0 (.split 34 0 (.step 50 (.step 3 (.close 26))) (.step 49 (.step 31 (.close 3)))) (.step 3 (.close 50))) (.split 30 0 (.step 47 (.step 67 (.step 48 (.close 50)))) (.step 18 (.close 28)))) (.step 18 (.step 21 (.step 3 (.close 48))))) (.step 48 (.close 58))) (.step 28 (.step 50 (.close 31)))) (.step 50 (.close 48)))) (.step 58 (.split 56 1 (.split 57 1 (.split 11 0 (.step 48 (.step 31 (.step 18 (.step 21 (.close 3))))) (.step 24 (.close 48))) (.step 50 (.close 3))) (.step 31 (.step 3 (.close 48)))))) (.step 48 (.step 50 (.step 3 (.step 49 (.step 3 (.step 48 (.close 3)))))))) (.step 48 (.step 50 (.step 58 (.split 56 1 (.split 11 0 (.step 4 (.step 18 (.step 4 (.step 48 (.close 38))))) (.step 4 (.close 3))) (.step 3 (.step 4 (.close 59)))))))) (.step 48 (.step 58 (.step 60 (.step 29 (.step 38 (.step 48 (.close 50)))))))) (.step 3 (.close 18))) (.step 48 (.close 3))) (.step 48 (.step 21 (.step 51 (.step 48 (.close 53)))))) (.step 3 (.step 50 (.step 4 (.step 60 (.step 50 (.close 48))))))) (.step 48 (.step 3 (.close 50)))) (.step 3 (.close 18))) (.step 50 (.step 53 (.step 50 (.close 18))))) (.step 49 (.step 53 (.step 49 (.close 18))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456543758745600, 11031304526203984395224077729546701486925133551781534788740017830022437755600740759979735331288135830141222955510940539130897832110754951630654018978488128854476208868772574212215448095378293312213405536828564489372672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 45 1 (.split 67 1 (.split 72 1 (.split 1 0 (.split 10 0 (.split 12 0 (.step 60 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 49 (.step 3 (.close 49))) (.step 50 (.step 18 (.close 48)))) (.step 49 (.close 3))) (.step 3 (.step 31 (.close 3)))) (.split 30 0 (.step 47 (.step 66 (.step 48 (.close 28)))) (.step 18 (.close 28)))) (.step 18 (.step 48 (.close 3)))) (.step 48 (.close 58))) (.step 28 (.step 49 (.close 31)))) (.step 49 (.close 58)))) (.step 58 (.split 56 1 (.split 57 1 (.split 11 0 (.step 48 (.step 31 (.step 18 (.step 9 (.close 48))))) (.step 16 (.close 12))) (.step 49 (.close 3))) (.step 16 (.step 31 (.close 3)))))) (.step 48 (.step 49 (.step 3 (.close 49))))) (.step 48 (.step 49 (.step 58 (.split 56 1 (.split 11 0 (.step 4 (.step 18 (.step 4 (.step 48 (.close 38))))) (.step 4 (.close 3))) (.step 3 (.step 4 (.close 59)))))))) (.step 48 (.step 58 (.step 60 (.step 29 (.step 48 (.step 49 (.close 3)))))))) (.step 3 (.close 18))) (.step 48 (.close 3))) (.step 48 (.step 55 (.step 51 (.step 48 (.close 18)))))) (.step 3 (.step 49 (.step 4 (.step 60 (.step 49 (.step 8 (.step 4 (.close 3))))))))) (.step 48 (.step 3 (.close 49)))) (.step 3 (.close 18))) (.step 50 (.step 52 (.step 50 (.close 18))))) (.step 49 (.step 52 (.step 49 (.close 18))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406065121288542000802422895582297588297529437341222915613341546759920839182750923168555564707320722379639358595702854149698429649920⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 53 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 72 1 (.split 11 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 70 (.step 7 (.close 3))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.close 9))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 7))) (.step 7 (.close 9))) (.step 3 (.close 9))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 58))) (.step 3 (.step 9 (.close 3)))) (.step 3 (.step 7 (.close 8)))) (.step 3 (.step 46 (.split 54 1 (.split 55 1 (.split 72 1 (.split 12 0 (.step 7 (.step 3 (.close 7))) (.step 3 (.close 46))) (.step 7 (.close 9))) (.step 3 (.close 46))) (.step 3 (.close 9)))))) (.step 3 (.step 46 (.split 53 1 (.split 56 1 (.step 53 (.split 11 0 (.step 9 (.step 7 (.close 3))) (.step 3 (.close 7)))) (.step 7 (.close 9))) (.step 4 (.close 27)))))) (.step 3 (.step 46 (.split 53 1 (.split 56 1 (.step 52 (.split 11 0 (.step 9 (.step 7 (.close 3))) (.step 3 (.close 7)))) (.step 7 (.close 9))) (.step 7 (.step 8 (.close 27))))))) (.step 3 (.close 9))) (.step 3 (.close 9))) (.step 9 (.step 31 (.step 3 (.step 27 (.close 46))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790165660684202627399290527708574486804337309215736681386283148871827099828064682326683453446094329307308645374043882496⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 1 0 (.split 11 0 (.split 12 0 (.split 21 0 (.split 46 0 (.split 47 0 (.split 49 0 (.step 45 (.step 7 (.close 45))) (.step 7 (.close 45))) (.step 31 (.close 45))) (.step 31 (.close 45))) (.step 7 (.close 45))) (.step 29 (.step 31 (.step 37 (.close 45))))) (.step 28 (.step 31 (.close 45)))) (.step 7 (.step 4 (.close 45)))) (.step 7 (.step 26 (.step 29 (.close 58))))) (.step 31 (.close 45))) (.step 7 (.step 31 (.close 45)))) (.step 29 (.step 31 (.step 26 (.step 7 (.close 45)))))) (.step 7 (.step 28 (.step 4 (.close 56))))) (.step 3 (.step 31 (.close 45)))) (.step 18 (.step 31 (.step 7 (.step 21 (.step 26 (.close 45))))))) (.step 26 (.step 31 (.step 29 (.step 40 (.step 52 (.close 58))))))) (.step 28 (.step 31 (.step 50 (.step 31 (.close 45)))))) (.step 28 (.step 31 (.step 49 (.step 31 (.close 45)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406065121288542003265048282856952539064969443600198778430825251164011255929519260933913175425896385593030999526010081700112679044096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 67 1 (.split 55 1 (.split 56 1 (.split 72 1 (.split 59 1 (.split 1 0 (.split 11 0 (.split 57 1 (.split 10 0 (.step 28 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 48 (.step 41 (.close 21))) (.step 5 (.close 41))) (.step 3 (.close 31))) (.step 5 (.step 3 (.close 22)))) (.step 5 (.close 41))) (.step 48 (.step 41 (.step 3 (.close 31)))))) (.step 7 (.step 3 (.close 41)))) (.step 28 (.step 60 (.close 31)))) (.step 43 (.step 41 (.close 4)))) (.step 3 (.step 4 (.close 41)))) (.step 5 (.close 58))) (.step 26 (.step 28 (.step 38 (.step 48 (.step 41 (.step 60 (.step 3 (.close 31))))))))) (.step 28 (.step 41 (.close 21)))) (.step 5 (.step 41 (.close 58)))) (.step 3 (.step 7 (.close 26)))) (.step 3 (.step 21 (.step 48 (.step 28 (.step 41 (.step 48 (.step 57 (.close 3))))))))) (.step 4 (.step 43 (.step 28 (.step 24 (.step 41 (.close 4))))))) (.step 3 (.step 48 (.close 16)))) (.step 3 (.step 7 (.close 54)))) (.step 5 (.step 21 (.close 58)))) (.step 48 (.step 5 (.step 48 (.step 9 (.step 58 (.close 3))))))) (.step 3 (.step 21 (.step 28 (.step 41 (.step 50 (.step 21 (.close 3)))))))) (.step 3 (.step 28 (.step 50 (.step 60 (.step 49 (.step 41 (.close 31)))))))) (.step 21 (.step 48 (.close 4)))) (.step 3 (.step 7 (.close 9)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311938444637015128376470226376989463726816768025608215510872156157207609927461275281198958612920964491325211648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 1 0 (.split 11 0 (.split 12 0 (.split 21 0 (.split 46 0 (.split 47 0 (.split 49 0 (.step 39 (.step 7 (.close 31))) (.step 7 (.step 29 (.close 39)))) (.step 31 (.close 39))) (.step 31 (.close 39))) (.step 7 (.close 39))) (.step 29 (.step 31 (.step 37 (.close 39))))) (.step 7 (.step 28 (.close 39)))) (.step 7 (.step 4 (.close 39)))) (.step 7 (.step 26 (.step 29 (.close 58))))) (.step 28 (.step 31 (.step 39 (.close 60))))) (.step 7 (.step 28 (.step 31 (.close 39))))) (.step 29 (.step 31 (.close 39)))) (.step 7 (.step 28 (.step 4 (.close 56))))) (.step 3 (.step 31 (.close 39)))) (.step 18 (.step 31 (.step 7 (.step 21 (.step 29 (.close 39))))))) (.step 22 (.step 31 (.step 29 (.step 40 (.step 52 (.step 26 (.close 39)))))))) (.step 28 (.step 31 (.step 50 (.step 31 (.close 39)))))) (.step 28 (.step 31 (.step 49 (.step 31 (.close 39)))))) (.split 46 1 (.split 47 1 (.split 49 1 (.step 39 (.step 31 (.step 7 (.step 57 (.step 45 (.step 31 (.close 3))))))) (.step 29 (.step 31 (.step 37 (.close 39))))) (.step 31 (.close 39))) (.step 31 (.step 37 (.close 39))))) (.step 38 (.step 41 (.step 39 (.step 31 (.step 7 (.step 41 (.step 21 (.step 22 (.step 31 (.close 3))))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133551781534788740017830022437755603789339641048395269166858988647612931673515706018721762604426868379461285418718753451533116518901574633877215839940350390048269549588627588096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.step 75 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 54 1 (.split 67 1 (.step 29 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 21 0 (.split 49 0 (.step 38 (.step 18 (.close 31))) (.step 18 (.close 38))) (.step 18 (.close 31))) (.step 38 (.close 18))) (.step 18 (.step 4 (.close 31)))) (.step 7 (.step 18 (.close 31)))) (.step 18 (.step 4 (.close 38))))) (.step 3 (.step 7 (.close 9)))) (.step 21 (.step 29 (.step 57 (.close 3))))) (.step 26 (.step 29 (.step 18 (.step 26 (.step 18 (.step 38 (.close 48)))))))) (.step 18 (.step 29 (.step 75 (.step 48 (.close 60)))))) (.step 57 (.step 58 (.step 28 (.step 41 (.step 48 (.step 38 (.step 59 (.step 3 (.close 31)))))))))) (.step 18 (.close 58)))) (.step 4 (.close 38))) (.step 3 (.step 40 (.step 29 (.step 21 (.step 38 (.step 48 (.step 55 (.close 15))))))))) (.step 3 (.step 7 (.step 18 (.step 21 (.close 75)))))) (.step 18 (.step 21 (.step 9 (.step 18 (.close 21)))))) (.step 55 (.step 57 (.step 58 (.step 53 (.split 51 1 (.step 75 (.split 59 1 (.step 18 (.step 21 (.step 29 (.step 40 (.step 18 (.close 58)))))) (.step 9 (.step 26 (.step 18 (.step 21 (.step 18 (.close 52)))))))) (.step 3 (.close 52)))))))) (.step 18 (.step 21 (.step 48 (.step 50 (.step 38 (.close 18))))))) (.step 48 (.step 50 (.step 58 (.step 66 (.step 4 (.step 29 (.step 38 (.step 48 (.step 38 (.close 49))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732150141930266508235204804524539702589448427175831875144960874318237941936568078121589033727167992997080131365220594366011376018414008252878871202886215387391828744118944662528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 1 0 (.split 12 0 (.split 21 0 (.split 46 0 (.split 47 0 (.split 49 0 (.split 50 0 (.split 56 1 (.split 10 0 (.split 17 0 (.step 37 (.step 7 (.close 26))) (.step 7 (.close 22))) (.step 7 (.close 15))) (.step 37 (.close 3))) (.step 7 (.step 28 (.close 37)))) (.step 7 (.close 37))) (.step 28 (.step 31 (.step 3 (.close 37))))) (.step 31 (.close 37))) (.step 7 (.close 37))) (.step 29 (.step 31 (.close 37)))) (.step 7 (.step 31 (.close 37)))) (.step 7 (.step 15 (.step 26 (.close 58))))) (.step 28 (.step 31 (.step 37 (.step 3 (.close 4)))))) (.step 7 (.step 31 (.close 37)))) (.step 29 (.step 31 (.step 37 (.step 7 (.close 37)))))) (.step 7 (.step 28 (.step 4 (.close 37))))) (.step 3 (.step 31 (.close 37)))) (.step 18 (.step 31 (.step 7 (.step 21 (.step 29 (.close 37))))))) (.step 18 (.step 31 (.step 15 (.step 31 (.step 7 (.step 16 (.close 52)))))))) (.step 28 (.step 31 (.step 49 (.step 31 (.step 50 (.close 37))))))) (.step 28 (.step 31 (.close 49)))) (.split 46 1 (.split 47 1 (.step 37 (.step 7 (.step 31 (.close 37)))) (.step 31 (.close 45))) (.step 31 (.close 37)))) (.step 16 (.step 28 (.step 37 (.step 38 (.step 41 (.step 7 (.step 4 (.step 15 (.step 3 (.close 37))))))))))) (.split 46 1 (.split 47 1 (.step 37 (.step 7 (.step 31 (.close 37)))) (.step 31 (.close 39))) (.step 31 (.close 37)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860625786047755327046382201842712242881026645428646036097814129234946167974012351567888618882048⟩
def references : Fin 11 → Box := ![Part4.root, Part5.root, Part6.root, Part7.root, Part8.root, Part9.root, Part10.root, Part11.root, Part12.root, Part13.root, Part14.root]
def proof : Chunks.Proof 11 := (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 3 (.split 45 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 72 1 (.split 11 0 (.split 12 0 (.split 26 0 (.split 35 0 (.step 54 (.step 7 (.close 3))) (.step 3 (.close 7))) (.step 3 (.close 54))) (.step 3 (.step 7 (.close 26)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 54)))) (.step 3 (.close 12))) (.step 3 (.close 54))) (.step 3 (.step 57 (.close 3)))) (.step 3 (.close 54))) (.step 31 (.step 3 (.close 44))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 47 1 (.reuse 4) (.run (.step 49 (.step 51 (.step 60 (.step 69 (.split 72 1 (.step 50 (.step 51 (.step 48 (.close 3)))) (.step 48 (.close 49)))))))))) (.reuse 5)) (.reuse 6)) (.split 42 1 (.reuse 7) (.run (.step 28 (.step 31 (.step 38 (.step 45 (.step 76 (.step 41 (.step 7 (.step 21 (.step 26 (.close 48))))))))))))) (.reuse 8)) (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 45 1 (.reuse 9) (.run (.step 48 (.close 55)))) (.run (.step 7 (.step 9 (.close 3))))) (.run (.step 29 (.step 31 (.step 38 (.step 58 (.step 38 (.step 45 (.step 3 (.step 4 (.close 48))))))))))) (.run (.step 4 (.step 41 (.step 29 (.step 38 (.step 3 (.close 31)))))))) (.run (.step 29 (.step 31 (.step 38 (.step 58 (.step 38 (.step 39 (.step 3 (.step 4 (.close 48)))))))))))) (.step 7 (.step 31 (.split 35 1 (.reuse 10) (.run (.step 29 (.step 38 (.step 37 (.step 49 (.step 38 (.step 7 (.step 31 (.close 37)))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898085459779036323457036046227686384520025644546986633459031204876518400⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 30 1 (.reuse 0) (.run (.step 3 (.step 31 (.split 38 1 (.split 47 1 (.split 49 1 (.step 7 (.step 3 (.close 18))) (.step 18 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 7))))))) (.run (.split 30 1 (.split 35 1 (.split 43 1 (.split 45 1 (.split 46 1 (.step 29 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 54 1 (.split 67 1 (.step 29 (.step 18 (.close 48))) (.step 3 (.step 7 (.close 9)))) (.step 29 (.close 4))) (.step 26 (.step 29 (.step 26 (.step 18 (.close 29)))))) (.step 28 (.step 29 (.close 48)))) (.step 28 (.close 29))) (.step 18 (.close 58))) (.step 4 (.close 18))) (.step 40 (.step 29 (.close 55)))) (.step 3 (.step 7 (.step 9 (.step 18 (.close 75)))))) (.step 55 (.step 57 (.split 51 1 (.split 59 1 (.step 18 (.step 29 (.close 53))) (.step 26 (.step 18 (.step 29 (.close 48))))) (.step 3 (.close 53)))))) (.step 55 (.step 57 (.step 58 (.split 50 1 (.split 51 1 (.split 59 1 (.step 18 (.step 29 (.close 52))) (.step 26 (.step 18 (.step 29 (.close 48))))) (.step 3 (.close 52))) (.step 21 (.step 27 (.close 52)))))))) (.step 28 (.step 29 (.step 48 (.step 18 (.step 4 (.step 29 (.close 48))))))))) (.step 18 (.step 28 (.step 48 (.step 58 (.step 60 (.step 29 (.close 49)))))))) (.step 31 (.step 48 (.close 55)))) (.step 7 (.step 9 (.close 3)))) (.step 29 (.close 4))) (.step 7 (.close 18)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨3291009114642412084309938365114701009965471731267159728844701696, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087146421207577693229255071098505804293251851248907878391137200768000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 24 (.step 48 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 24 (.step 4 (.step 7 (.step 43 (.step 4 (.close 7)))))) (.step 4 (.close 18))) (.step 3 (.close 7))) (.step 4 (.step 9 (.step 18 (.close 3))))) (.step 24 (.close 48))) (.step 4 (.step 22 (.step 24 (.step 3 (.close 4)))))) (.step 5 (.close 58))) (.step 3 (.close 55))) (.step 3 (.step 7 (.close 26)))) (.step 18 (.step 48 (.close 53)))) (.step 18 (.step 48 (.close 52)))) (.step 24 (.step 21 (.step 48 (.close 3))))) (.step 24 (.step 48 (.close 49)))) (.step 3 (.step 7 (.close 9)))) (.step 18 (.step 26 (.step 4 (.close 31))))) (.step 4 (.step 21 (.step 28 (.step 41 (.step 43 (.step 24 (.close 41)))))))) (.step 18 (.step 31 (.close 39)))) (.step 4 (.step 18 (.close 38)))) (.step 16 (.step 7 (.step 4 (.step 31 (.close 37)))))) (.step 4 (.step 18 (.close 29)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087146421207577694725832747725350392533825119950381690518812124775424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 22 1 (.split 26 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.close 18)) (.step 18 (.close 3))) (.step 5 (.close 59))) (.step 36 (.step 51 (.split 26 0 (.split 35 0 (.step 56 (.step 4 (.close 7))) (.step 3 (.close 4))) (.step 3 (.close 4)))))) (.step 3 (.step 18 (.close 19)))) (.step 22 (.step 18 (.step 7 (.close 20))))) (.step 18 (.step 24 (.step 50 (.step 3 (.close 4)))))) (.step 18 (.step 8 (.step 24 (.step 49 (.step 3 (.close 4))))))) (.step 4 (.step 18 (.close 48)))) (.step 4 (.step 5 (.step 24 (.step 41 (.step 3 (.step 19 (.close 20)))))))) (.step 7 (.step 18 (.close 4)))) (.step 18 (.step 25 (.split 26 1 (.split 35 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 26 0 (.step 20 (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 18 (.close 20))) (.step 7 (.step 18 (.close 17)))) (.step 7 (.step 17 (.step 18 (.close 19))))) (.step 18 (.close 20))) (.step 18 (.step 20 (.close 19)))) (.step 18 (.close 20))) (.step 18 (.step 19 (.close 20)))) (.step 4 (.step 7 (.close 18)))) (.step 7 (.step 18 (.close 4))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11031304526203979496340767072204264539074732150141926580998054715018047741309443954978191940294007961976649369701693196270525432380910129004669110905245368947576601238573411464930105846343276883358948647419105748452352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 26 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.close 18)) (.step 18 (.close 3))) (.step 5 (.step 7 (.close 19)))) (.split 57 1 (.step 4 (.split 59 1 (.split 26 0 (.split 35 0 (.step 56 (.close 19)) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 7 (.close 18)))) (.step 18 (.close 56)))) (.step 3 (.step 18 (.close 19)))) (.step 18 (.step 7 (.close 17)))) (.step 21 (.step 18 (.step 7 (.close 19))))) (.step 18 (.step 24 (.close 50)))) (.step 18 (.step 8 (.step 24 (.step 49 (.step 3 (.close 4))))))) (.step 4 (.step 7 (.step 18 (.close 19))))) (.step 4 (.step 5 (.step 24 (.step 41 (.close 19)))))) (.step 7 (.step 18 (.close 4)))) (.step 18 (.step 19 (.split 26 1 (.split 45 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 26 0 (.step 19 (.step 7 (.close 4))) (.step 7 (.close 18))) (.step 4 (.step 7 (.close 18)))) (.step 7 (.close 18))) (.step 18 (.close 19))) (.step 7 (.close 19))) (.step 18 (.close 19))) (.step 7 (.step 18 (.close 17)))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 7 (.step 18 (.close 4))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087146421207577694727294249362681295452028804783097973538468057318400⟩
def references : Fin 4 → Box := ![Part16.root, Part17.root, Part18.root, Part19.root]
def proof : Chunks.Proof 4 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 26 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.close 18)) (.step 18 (.close 3))) (.step 5 (.step 7 (.close 19)))) (.step 60 (.step 73 (.split 26 0 (.split 35 0 (.step 56 (.close 25)) (.step 3 (.close 4))) (.step 3 (.close 4)))))) (.step 3 (.step 18 (.close 19)))) (.step 18 (.step 7 (.close 17)))) (.step 26 (.step 18 (.step 7 (.close 25))))) (.step 18 (.step 24 (.step 50 (.step 3 (.close 4)))))) (.step 18 (.step 8 (.step 24 (.step 49 (.step 3 (.close 4))))))) (.step 4 (.step 7 (.step 18 (.close 25))))) (.step 4 (.step 5 (.step 24 (.step 41 (.step 3 (.step 19 (.close 20)))))))) (.step 7 (.step 18 (.close 4)))))))) (.reuse 1)) (.reuse 2)) (.step 7 (.step 18 (.split 17 1 (.reuse 3) (.run (.step 18 (.step 19 (.split 26 1 (.split 45 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 26 0 (.step 19 (.step 7 (.close 4))) (.step 7 (.close 18))) (.step 4 (.step 7 (.close 18)))) (.step 7 (.close 18))) (.step 18 (.close 19))) (.step 7 (.close 19))) (.step 18 (.close 19))) (.step 7 (.step 18 (.close 17)))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.close 19))) (.step 7 (.step 18 (.close 4)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part18.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548403292451594421185942844481398154504594093000265847099038171067179307863379502618751557745270400469380042735036479987964793084445696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 1 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 45 1 (.split 59 1 (.split 67 1 (.step 15 (.step 9 (.split 72 1 (.split 26 0 (.split 38 0 (.step 58 (.close 26)) (.step 15 (.close 31))) (.step 15 (.close 28))) (.step 15 (.close 31))))) (.step 7 (.step 3 (.close 15)))) (.step 15 (.close 48))) (.step 15 (.close 48))) (.step 18 (.step 26 (.step 3 (.close 15))))) (.step 15 (.close 3))) (.step 18 (.step 22 (.step 15 (.step 18 (.step 29 (.close 48))))))) (.step 18 (.step 21 (.step 15 (.step 18 (.close 12)))))) (.split 38 0 (.step 15 (.step 4 (.step 3 (.close 12)))) (.step 3 (.step 4 (.step 12 (.step 15 (.close 21))))))) (.step 48 (.step 26 (.step 48 (.close 3))))) (.step 16 (.step 22 (.step 48 (.step 15 (.close 3)))))) (.step 48 (.step 9 (.close 58)))) (.step 57 (.step 26 (.step 15 (.close 4))))) (.step 4 (.close 15))) (.step 48 (.step 55 (.close 15)))) (.step 15 (.step 55 (.step 57 (.step 3 (.step 7 (.close 15))))))) (.step 21 (.step 55 (.step 15 (.step 4 (.step 15 (.close 53))))))) (.step 12 (.step 34 (.step 15 (.step 9 (.step 52 (.step 48 (.close 3)))))))) (.step 24 (.step 48 (.step 21 (.step 55 (.split 54 1 (.split 56 1 (.step 48 (.close 3)) (.step 16 (.close 48))) (.step 12 (.close 57)))))))) (.step 16 (.step 48 (.step 12 (.step 55 (.step 66 (.close 48))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2596148429267413814265250312093696, 11031304526203984395224077729546701486925133551781534788740017830022437755603786365416988577645770731155625735214825441989580717745490934115182327168655193739981001219001792014736679700811116915753632599982222732166144⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 47 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 55 1 (.split 45 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.step 24 (.split 12 0 (.split 16 0 (.split 1 0 (.split 26 0 (.split 17 0 (.split 34 0 (.split 36 0 (.step 24 (.step 8 (.step 3 (.close 18)))) (.step 4 (.close 3))) (.step 4 (.close 3))) (.step 7 (.close 18))) (.step 3 (.step 4 (.close 3)))) (.step 4 (.close 3))) (.step 7 (.close 18))) (.step 4 (.step 3 (.step 4 (.close 3)))))) (.step 3 (.step 23 (.close 7)))) (.step 4 (.close 3))) (.step 3 (.close 7))) (.step 4 (.step 15 (.close 48)))) (.step 3 (.step 60 (.step 8 (.close 48))))) (.step 3 (.step 28 (.step 43 (.step 24 (.step 51 (.step 3 (.close 4)))))))) (.step 4 (.close 48))) (.step 18 (.step 3 (.step 34 (.close 48))))) (.step 4 (.close 15))) (.step 24 (.split 45 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 57 1 (.split 26 0 (.step 8 (.split 34 0 (.step 56 (.close 3)) (.step 4 (.close 14)))) (.step 4 (.close 14))) (.step 14 (.close 4))) (.step 4 (.close 14))) (.step 3 (.close 7))) (.step 4 (.step 8 (.close 14)))) (.step 4 (.close 14))))) (.step 3 (.step 15 (.step 18 (.step 14 (.close 55)))))) (.step 3 (.step 7 (.close 48)))) (.step 15 (.step 48 (.step 4 (.step 34 (.close 48)))))) (.step 4 (.step 15 (.step 34 (.step 48 (.close 52)))))) (.step 3 (.step 24 (.step 49 (.step 60 (.step 50 (.step 8 (.step 4 (.close 3))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2596148429267413814265250312093696, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087144775703020372023212916129323248240821083146749151943897934464000⟩
def references : Fin 1 → Box := ![Part22.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.reuse 0) (.run (.step 12 (.step 34 (.step 49 (.step 3 (.step 49 (.step 4 (.step 8 (.step 14 (.step 4 (.close 3)))))))))))) (.run (.step 8 (.step 3 (.step 7 (.close 27)))))) (.run (.step 4 (.step 15 (.step 43 (.step 4 (.step 14 (.step 3 (.step 24 (.step 37 (.close 39))))))))))) (.run (.step 4 (.step 43 (.step 49 (.step 50 (.step 59 (.step 60 (.step 3 (.step 28 (.step 24 (.step 41 (.close 4))))))))))))) (.run (.step 4 (.step 15 (.step 43 (.step 28 (.step 4 (.step 14 (.step 24 (.step 7 (.step 37 (.close 56)))))))))))) (.run (.step 4 (.step 15 (.step 48 (.step 4 (.close 14))))))) (.run (.step 4 (.step 15 (.step 37 (.step 43 (.step 4 (.step 14 (.close 37))))))))) (.run (.step 3 (.step 31 (.step 7 (.close 14)))))) (.run (.step 4 (.step 15 (.step 50 (.step 40 (.step 28 (.step 4 (.close 14))))))))) (.run (.step 7 (.step 17 (.step 18 (.step 60 (.step 73 (.split 35 1 (.split 46 1 (.split 47 1 (.split 50 1 (.split 52 1 (.split 26 0 (.step 8 (.step 14 (.split 35 0 (.step 14 (.step 4 (.close 7))) (.step 3 (.close 4))))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 14 (.close 18)))) (.step 4 (.step 7 (.close 14)))) (.step 14 (.close 4))) (.step 14 (.close 4))) (.step 4 (.close 14))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2596148429267413814265250312093696, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087146421207577694727294249362682625978098804332677784478152419968000⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.step 24 (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 17 (.step 18 (.step 25 (.split 35 1 (.split 46 1 (.split 47 1 (.split 50 1 (.split 52 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 26 0 (.step 8 (.step 14 (.split 35 0 (.step 14 (.step 4 (.close 7))) (.step 3 (.close 4))))) (.step 3 (.step 4 (.close 14)))) (.step 4 (.close 14))) (.step 4 (.step 7 (.close 14)))) (.step 14 (.close 4))) (.step 3 (.step 14 (.close 18)))) (.step 4 (.step 7 (.step 14 (.close 17))))) (.step 14 (.close 4))) (.step 14 (.close 4))) (.step 4 (.close 14))))))))) (.run (.step 7 (.step 17 (.step 18 (.step 19 (.step 35 (.step 50 (.split 46 1 (.split 52 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 26 0 (.step 8 (.step 14 (.split 35 0 (.step 14 (.step 4 (.close 7))) (.step 3 (.close 4))))) (.step 3 (.step 4 (.close 14)))) (.step 4 (.close 14))) (.step 4 (.step 7 (.close 14)))) (.step 14 (.close 4))) (.step 3 (.step 14 (.close 18)))) (.step 14 (.close 4))))))))))) (.run (.step 4 (.step 15 (.step 24 (.close 3)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087146421207577694727294249362682625979366454932906013879649123173376⟩
def references : Fin 3 → Box := ![Part20.root, Part21.root, Part24.root]
def proof : Chunks.Proof 3 := (.split 10 1 (.split 11 1 (.split 12 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 1) (.run (.step 10 (.step 3 (.step 9 (.close 7)))))) (.run (.step 15 (.step 29 (.step 31 (.step 26 (.step 7 (.close 15)))))))) (.run (.step 4 (.step 16 (.step 21 (.step 48 (.step 15 (.step 28 (.step 3 (.close 26)))))))))) (.run (.step 15 (.step 31 (.step 22 (.step 15 (.step 7 (.close 26)))))))) (.run (.step 15 (.step 21 (.step 29 (.step 38 (.step 48 (.step 15 (.close 38))))))))) (.run (.step 15 (.step 31 (.close 37))))) (.run (.step 3 (.step 18 (.close 12))))) (.run (.step 15 (.step 29 (.close 48))))) (.run (.step 4 (.step 18 (.close 15))))) (.run (.step 4 (.step 18 (.close 15))))) (.run (.step 4 (.step 18 (.close 15)))))) (.reuse 2)) (.run (.step 3 (.step 18 (.step 31 (.split 11 1 (.split 12 1 (.split 26 1 (.split 35 1 (.split 47 1 (.split 49 1 (.step 7 (.step 3 (.close 18))) (.step 18 (.close 7))) (.step 3 (.close 12))) (.step 7 (.close 18))) (.step 7 (.close 18))) (.step 12 (.step 15 (.step 3 (.close 7))))) (.step 3 (.step 7 (.close 14)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes
  · exact Part21.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133551781534788740017830022437755603789342548406067828973790168123311940740375375860627823083731663385141898087146421207577694727294249362682625979366454932906013879649123174400⟩
def references : Fin 1 → Box := ![Part25.root]
def proof : Chunks.Proof 1 := (.split 1 1 (.reuse 0) (.run (.step 3 (.step 48 (.split 11 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.step 58 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.step 4 (.split 49 1 (.split 50 1 (.split 52 1 (.split 57 1 (.step 4 (.close 40)) (.step 4 (.close 48))) (.step 3 (.close 55))) (.step 3 (.step 40 (.close 48)))) (.step 3 (.step 34 (.step 40 (.close 48)))))) (.step 48 (.step 4 (.close 50)))) (.step 4 (.step 48 (.close 49)))) (.step 3 (.step 28 (.step 4 (.close 45))))) (.step 3 (.step 4 (.step 41 (.close 4))))) (.step 3 (.step 5 (.step 31 (.step 4 (.step 39 (.close 38))))))) (.step 4 (.step 38 (.close 34)))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 4 (.close 37)))))))) (.step 4 (.step 29 (.close 27)))) (.step 3 (.step 4 (.close 18)))) (.step 3 (.step 4 (.close 18)))) (.step 3 (.step 4 (.close 18)))) (.step 4 (.step 15 (.close 26)))) (.step 4 (.close 14)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part26.excludes
end FiveColour.Packed.ProjectedChunks.Case13
