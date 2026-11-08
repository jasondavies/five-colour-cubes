module
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case189
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root 76
def families : Fin 78 → List Cut := Enumeration.families 76
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid 76
def reduced28 : Array Cut := #[⟨137438953472, 2404907604760405225358828131112281116032698930082119547604265954848982041717359046106827774346003151904701415424, 0⟩,⟨37394132762624, 2772672338344690020572809991806503085245381390211866573669042962104148162143044182546386666858261051813637549887463235232932560896, 0⟩,⟨37531571716096, 2772672338344690022977717596566908310604209521324147689701741892186267709747310137395368708575620097920465324233466387137633976320, 2⟩,⟨153368677935220768, 5136851466355833507620537598146800668155772859886196469132333408512980551636985683606388382310806482161031035325732048333692157261452371711311190736218611147056781795977495387865572381631627867592147148472320, 0⟩,⟨153368815374174240, 5136851466355833507620537598146800668155772859886196469132333408512980551636985683606388382310808887068635795730957407161823269542568404410241272855766215413011630778019212746911679209405973870744051849887744, 1⟩,⟨153370887695894560, 5136851466355833507620537598146800668155772859886196469132333408512980551636988456278726727000827054971022841828817293713093076182386894185651765891793470830837503579454962779155530111608877342777246578900992, 1⟩,⟨153371025134848032, 5136851466355833507620537598146800668155772859886196469132333408512980551636988456278726727000829459878627602234042652541224188463502926884581848011341075096792352561496680138201636939383223345929151280316416, 3⟩,⟨1180591623069040115712, 3048582568670736543482183899601127995099283984237044234188508092130581451883300082487321282439784643579959198833119948656535846583084223823872, 1⟩,⟨1180591658253412204544, 3048582568670736543482183899601127995099283984237044236177801037769728020504829075074604642841609246769350068594975856229173834633217725956096, 3⟩,⟨1180744991746975336480, 5136851466355833507620537598146800668155772859886196469132333408516029134205656420149870566210407610156130319309969092567880665353582953163194490818705932429496566439557454586698692330288163714175231372296192, 5⟩]
def witnesses28 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid28 : ∀ c ∈ reduced28.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered28 : ∀ c ∈ families 31, possible root 14 c →
    ∃ d ∈ reduced28.toList, relaxes root c d = true :=
  covers_sound root 14 reduced28 (families 31) witnesses28 (by decide +kernel)
def reduced31 : Array Cut := #[⟨2147485696, 4455508415646675018204269146191690746966043464109921807206245465930705026292083588673864622885823944033405756259538458868925052825776006795791654544447328932792935940390907643887135802523648, 0⟩,⟨37394132762624, 2772672338344690020572809991806503085245381390211866573669042962104148162143044182546386666858261051813637549887463235232932560896, 0⟩,⟨37394132764672, 4455508415646675018204269146191690746966043464109921807206245465933349250167244583069672286305205752977720592309536957432306542352630344214351160956708083054266652186729833703550539760926720, 1⟩,⟨70370891661312, 2772669694120814859578414184143083703436437077318485467396208651534083214629144529682381245156279099349203620700307857034182656000, 0⟩,⟨70370891663360, 4455508415646675018204269146191690746966043464109921807206245465930705026292083588673864622885823944033407698928430684597995972287682830314698296951286381072314187752800646548172341011021824, 1⟩,⟨107762876940288, 2772672338344690020572809991806503085245381392154535465894772033023610068966563089188793505910400573065449959626367520438141059072, 1⟩,⟨107762876942336, 4455508415646675018204269146191690746966043464109921807206245465933349250167244583069672286305205752977722534978429183161377461814537167733257803363547135193787903999139572607835744969424896, 2⟩,⟨1180591623069040115712, 3048582568670736543482183899601127995099283984237044234188508092130581451883300082487321282439784643579959198833119948656535846583084223823872, 1⟩,⟨1180591623069040117760, 4455508415646675018204269146191690746966043464112970389774913429804493089376825138254779763786357551830518888535093869841227738286955522452608399213621183992047958497836482086898391052189696, 2⟩,⟨1180591658253412204544, 3048582568670736543482183899601127995099283984237044236177801037769728020504829075074604642841609246769350068594975856229173834633217725956096, 2⟩,⟨1180591658253412206592, 4455508415646675018204269146191690746966043464112970389774913429804493089376825138254779763786357551832508181480733016409849267279542805813010223816810574861809814405409120074948524554321920, 3⟩,⟨1180591693437784293376, 3048582568670736543482183899601127995099283984237044234190450761022807180954219544394144801346427050419011338354371761066274750868289432322048, 2⟩,⟨1180591693437784295424, 4455508415646675018204269146191690746966043464112970389774913429804493089376825138254779763786357551830520831203986095570298657748862345971515041620460236131569210310246220991183596260687872, 3⟩,⟨1180591728622156382208, 3048582568670736543482183899601127995099283984237044236179743706661953749575748536981428161748251653608402208116227668638912738918422934454272, 3⟩,⟨1180591728622156384256, 4455508415646675018204269146191690746966043464112970389774913429804493089376825138254779763786357551832510124149625242138920186741449629331916866223649627001331066217818858979233729762820096, 4⟩,⟨1180600630268294858784, 5136851466355833507620537598146800668155772859886196469132333408516029134205656420149870566210407610156130319309969092565889427841913990801313496544424807166348839484926738227320010119131256624063501716946944, 3⟩,⟨1180600665452666947616, 5136851466355833507620537598146800668155772859886196469132333408516029134205656420149870566210407610156130319309969092567878720787553137369935025537012090526750664088116129097081866026703894612113635219079168, 4⟩,⟨1180600700637039036448, 5136851466355833507620537598146800668155772859886196469132333408516029134205656420149870566210407610156130319309969092565891370510806216530384416006331630685255481891765790366841261931540995528348706925445120, 4⟩,⟨1180600735821411125280, 5136851466355833507620537598146800668155772859886196469132333408516029134205656420149870566210407610156130319309969092567880663456445363099005944998918914045657306494955181236603117839113633516398840427577344, 5⟩]
def witnesses31 : List Nat := [3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid31 : ∀ c ∈ reduced31.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered31 : ∀ c ∈ families 34, possible root 14 c →
    ∃ d ∈ reduced31.toList, relaxes root c d = true :=
  covers_sound root 14 reduced31 (families 34) witnesses31 (by decide +kernel)
def reduced45 : Array Cut := #[⟨35184372088832, 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224, 1⟩,⟨37394132762624, 2772672338344690020572809991806503085245381390211866573669042962104148162143044182546386666858261051813637549887463235232932560896, 2⟩,⟨153368677935220768, 5136851466355833507620537598146800668155772859886196469132333408512980551636985683606388382310806482161031035325732048333692157261452371711311190736218611147056781795977495387865572381631627867592147148472320, 3⟩,⟨153370887695894560, 5136851466355833507620537598146800668155772859886196469132333408512980551636988456278726727000827054971022841828817293713093076182386894185651765891793470830837503579454962779155530111608877342777246578900992, 4⟩,⟨1180744989399775709216, 5136851466355833507620537598146800668155772859886196469132333408516029134205653647477532221520384632438533752401658488360348634151532397989923833543583468479760995674038269836362627772536568235838227240452096, 4⟩,⟨1180744991609536383008, 5136851466355833507620537598146800668155772859886196469132333408516029134205656420149870566210405205248525558904743733739749553072466920464264408699158328163541717457515737227652585502513817711023326670880768, 5⟩]
def witnesses45 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid45 : ∀ c ∈ reduced45.toList, c.Valid := by
  apply list_valid_of_weights
  apply FastWeight.list_weights_of_fast
  decide +kernel

theorem covered45 : ∀ c ∈ families 48, possible root 14 c →
    ∃ d ∈ reduced45.toList, relaxes root c d = true :=
  covers_sound root 14 reduced45 (families 48) witnesses45 (by decide +kernel)
def checkedFamilies (r : Fin 78) : List Cut :=
  match r.val with
  | 31 => reduced28.toList
  | 34 => reduced31.toList
  | 48 => reduced45.toList
  | _ => families r
theorem checkedFamilies_valid : ∀ r, ∀ c ∈ checkedFamilies r, c.Valid := by
  intro r
  fin_cases r
  · exact families_valid 0
  · exact families_valid 1
  · exact families_valid 2
  · exact families_valid 3
  · exact families_valid 4
  · exact families_valid 5
  · exact families_valid 6
  · exact families_valid 7
  · exact families_valid 8
  · exact families_valid 9
  · exact families_valid 10
  · exact families_valid 11
  · exact families_valid 12
  · exact families_valid 13
  · exact families_valid 14
  · exact families_valid 15
  · exact families_valid 16
  · exact families_valid 17
  · exact families_valid 18
  · exact families_valid 19
  · exact families_valid 20
  · exact families_valid 21
  · exact families_valid 22
  · exact families_valid 23
  · exact families_valid 24
  · exact families_valid 25
  · exact families_valid 26
  · exact families_valid 27
  · exact families_valid 28
  · exact families_valid 29
  · exact families_valid 30
  · exact valid28
  · exact families_valid 32
  · exact families_valid 33
  · exact valid31
  · exact families_valid 35
  · exact families_valid 36
  · exact families_valid 37
  · exact families_valid 38
  · exact families_valid 39
  · exact families_valid 40
  · exact families_valid 41
  · exact families_valid 42
  · exact families_valid 43
  · exact families_valid 44
  · exact families_valid 45
  · exact families_valid 46
  · exact families_valid 47
  · exact valid45
  · exact families_valid 49
  · exact families_valid 50
  · exact families_valid 51
  · exact families_valid 52
  · exact families_valid 53
  · exact families_valid 54
  · exact families_valid 55
  · exact families_valid 56
  · exact families_valid 57
  · exact families_valid 58
  · exact families_valid 59
  · exact families_valid 60
  · exact families_valid 61
  · exact families_valid 62
  · exact families_valid 63
  · exact families_valid 64
  · exact families_valid 65
  · exact families_valid 66
  · exact families_valid 67
  · exact families_valid 68
  · exact families_valid 69
  · exact families_valid 70
  · exact families_valid 71
  · exact families_valid 72
  · exact families_valid 73
  · exact families_valid 74
  · exact families_valid 75
  · exact families_valid 76
  · exact families_valid 77
theorem checkedFamilies_cover : ∀ r, ∀ c ∈ families r, possible root 14 c →
    ∃ d ∈ checkedFamilies r, relaxes root c d = true := by
  intro r
  fin_cases r
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered28
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered31
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered45
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
namespace Part0
def root : Box := ⟨2, 5260135901548373507240989882880128665554204340346194632619378241831841263940103671587036994856464153116356181750708692256867704353528451149109989800074996372159268087382359341910673950294640752640864086015344642⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 31 (.step 48 (.run (.close 34))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part0
/-- All empty-root chunks prove exclusion. -/
theorem excludes : Chunks.Excludes 14 families root :=
  excludes_of_covered root (Archive.root_valid 76) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part0.covered
end FiveColour.Packed.EnumerationChunks.Case189
