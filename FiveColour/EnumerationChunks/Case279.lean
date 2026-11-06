module
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case279
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root 166
def families : Fin 78 → List Cut := Enumeration.families 166
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid 166
def points : List Nat := []
def reduced28 : Array Cut := #[⟨261460928709758000, 5265272753014729345311051038100474741082115877820730749655482637964803075651204340977781137381846289631622434588857777346734955207706242234000635590574691994683272027276709459523273856128710513268111862977789952, 0⟩,⟨920462218077442632, 5386379168201990986199831492300060909654604011336892906863603575868449242452748752482705433585241155311336004118991875076408786708859227555364658958095842362438437456095506023735774779472622357855568696992484818944, 0⟩,⟨1145858065613954680, 5391644440955005715545142543338161380343424829479368948051209352133642309919097592605040296504972986584457854223245070276740435802297614225720963507410141990093280659307933548230071714947160386325036836128343195648, 1⟩,⟨11518838754879452521096, 5386379163190433359397370174955576615808304760235063506432290680758118528206737396587211648121578966222481996798374186552295137637906088686180295163863082668876073677511212580910371187870300661266160219169612628992, 0⟩,⟨11519100215807893810872, 5391644435943448088742681225993677086497125578377539551134672859010183769743819445839219838283261671168976216514832417597802702830794761963002148631492752530993913683733101901724734968037745443817985247877498143744, 1⟩,⟨11519759214886954775240, 5386379168206889869510488834741257863998539787730935443429680825405425654424570045688068503837992646712893369982524498306119136893237746444366218696214304567708057367225554623962878897654253264117061652571324679168, 1⟩,⟨11519984610734491287288, 5391644440959904598855799885779358334687360605873411484617286601670618721890918885810403366757724477986015220086777693506450785986676133114722523245528604195362900570437982148457175833128791292586529791707183055872, 2⟩,⟨26296986603234732000528, 5260135901553157577536494311480059341140459886599243819284490698725595141805138145662295962096339419945337636886831430242805160415149059204058168796524388942023639625951447618578332799661165098649631644305063937, 0⟩,⟨26297248059678149299504, 5265272753019513411044114849078206141808615659459133530530025022202952708613560305953985155737726196888781320798897299174719169982921476473565454325740024142062662572666907394956618524594713448480775208835219457, 1⟩,⟨26297907065452540974936, 5391639304103544143777367986611540964943483173488147464635614762181275276055984735539398138571638353388143939037748079774812422106955343649156569958931461921503617829916070082709193618583599594992775245481697607681, 1⟩,⟨26298132456815053496184, 5391644440955010499610875607149139111744151329261007350832083894517880459552059948570016500523328866491715013109455109798568420017072829459960528326145307322240660049853323746165505059615626389260249499474200625153, 2⟩,⟨37483747928980773175294, 5653548961323977941106329334149636230834377968676893342677075896382147238876408603138096228023050429717107534437076598418567490874517036166131388967819017393700516247012395782970072207331174158284051884962358459630617601, 0⟩,⟨37483783957777798660094, 5653548961323977941106329334149636230834382024899342039114455265176988129918736094860679944440955305935476016647042179346001477078912125617377853759408706669876611220211345472960893646710066394702030767840478991586690049, 1⟩,⟨37483783957777803444222, 5653548961323977941106329334149636230834382020938194855669700460466344281983603992503469793907990580962320557335169662854180940932407313671680879745879080126991568736511709169714865271179592341912964805486453802608362497, 1⟩,⟨37483783957777807835134, 5653548961323977941106329334149636230834382024899345816762390267211478800254195877900820706397783063220704340144629488398212105674777516116979548218684106890008577831959070493024356636877067732075044479187873283359900673, 2⟩,⟨37519524531292516378520, 5391639299091986516974906669267056671097183922386314465073266232513838313379167230858417257350281522763578543507911896555275407714593668431390624121930862743608481279766694637757011677270752571261673961595838923777, 1⟩,⟨37519785987735933677496, 5391644435943452872808414289804654817897852078159174354784511766837315670945975653018708946543922909540521987191823962424207321724161440848660131407460078378808520302713410097533389962995686119611505105160369079297, 2⟩,⟨37520444991300018632664, 5391639304108443027088025329052737919287418949882186402070656377161145439596999879959274113066695203253989916692062208309099406969925326189576547654282084642440464969481036680809519387054705174112575394997550973953, 2⟩,⟨37520670382662531153912, 5391644440959909382921532949590336066088087105655046288267125509497750623093075092989892475018385716357560990763769238332855404880042812000380506021495930043177507189418290344265830828086731968380049648990053991425, 3⟩,⟨37778895834160131473406, 5653548961323977941106329334149636230834382024899342039118050881436220700152810454933619600254723821679243876581153173838799844145339416313734399557755800690864398003731295904189954294149250177615001517646746460359754753, 1⟩,⟨37778895834160136257534, 5653548961323977941106329334149636230834382020938194855673296076725576852217678352576409449721759096706088417269280657346979307998834604368037425544226174147979355520031659600943925918618776124825935555292721271381427201, 1⟩,⟨37778895834160140648446, 5653548961323977941106329334149636230834382024899345816765985883470711370488270237973760362211551578964472200078740482891010472741204806813336094017031200910996364615479020924253417284316251514988015228994140752132965377, 2⟩,⟨37778931862957152534526, 5653548961323977941106329334149636230834382024899342039118054396212622687024984525666828729928051063630117549953522783804090947143449315913633086308291819355596547948718162189059460259554461834453237581138092627277644801, 2⟩,⟨37778931862957157318654, 5653548961323977941106329334149636230834382020938194855673299591501978839089852423309618579395086338656962090641650267312270410996944503967936112294762192812711505465018525885813431884023987781664171618784067438299317249, 2⟩,⟨37778931862957161709566, 5653548961323977941106329334149636230834382024899345816765989398247113357360444308706969491884878820915345873451110092856301575739314706413234780767567219575728514560465887209122923249721463171826251292485486919050855425, 4⟩]
def witnesses28 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,11,1,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,3,0,0,0,0,0,0,3,0,0,0,0,0,3,3,0,5,0,0,1,0,1,1,0,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,7,0,0,0,7,0,7,0,0,9,0,0,1,0,1,0,0,0,1,1,0,1,0,0,0,15,0,0,3,0,3,3,0,0,3,3,0,3,0,0,0,17,1,0,0,1,0,0,0,1,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid28 : ∀ c ∈ reduced28.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered28 : ∀ c ∈ families 31, possible root 14 c →
    ∃ d ∈ reduced28.toList, relaxes root c d = true :=
  covers_sound root 14 reduced28 (families 31) witnesses28 (by decide +kernel)
def checkedFamilies (r : Fin 78) : List Cut :=
  match r.val with
  | 31 => reduced28.toList
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
  · exact families_valid 34
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
  · exact families_valid 48
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
def root : Box := ⟨3, 5789234136395753411692881238169227500374415492528067878354290168620771460259396997008401244563915906581361930636727773888120870699057044488710021599111385617677419917271276362521899362738396754436956325986280152474873496579⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 2 (.step 31 (.run (.close 2))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part0
/-- Every admissible vector in the original root is one of the explicit points. -/
theorem covered : Enumeration.Covers points 14 families root :=
  Enumeration.covers_of_weakened points root (Archive.root_valid 166) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part0.covered
end FiveColour.Packed.EnumerationChunks.Case279
