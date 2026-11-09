module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case173
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644320647064274132271104,32908392998381874375671,5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859361899508584915508177230179531154389992449,0⟩
theorem header_valid : Projection.HeaderValid 14 60 0 11 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 60).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644320647064274132271104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨32908392998381874375671, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859361899508584915508177230179531154389992449, 0⟩]
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
def points : List Nat := [8104522595470689372094546612048386401482849493406639438065421906282312194009598640247690832260516139630734067652120489716524574352906024022270887037121590409858910989281788952576,8104522595470689372094546615318580338863467787374894379329712856201867675554574499272502423629993555374857182540387388592891715725325045372362637664493908228648712838456675401728,4052261297735344686047273310935877447843399339745574349741011947472926103907245318012518285369243886925840373891542155106495966781710896325722681841149429292598618687726029897728,6553174556823330892116254320152311038743984532257676392010356342897936776196255120964575276122865568303196758178120263374620574327040550850784057622528,8104522595470689372094546608778192464102231199438384496801130956362756712464622781222879240891038723886610952763853590840157432980487002672179136409749272591069109140106902503424,4052261297735344686047273307665683510462781045777319408476720997553370622362269458987706693999766471181717259003275256230128825409291874975630931213777111473808816838551143448576,6553174556823330892116254320152311038743984532259916136752534147108494218476823565242696921620100217838096747279082726017804950356548524536995384393728,8104522595470689372094546612048386401482849493406639438065421906282309845469255611156640746990476792574275136247693226893888516596834480914209564299858287656241403713850364133376,8104522595470689372094546615318580338863467787374894379329712856201865327014231470181452338359954208318398251135960125770255657969253502264301314927230605475031205563025250582528,4052261297735344686047273310935877447843399339745574349741011947472923755366902288921468200099204539869381442487114892283859909025639353217661359103886126538981111412294605078528,8104522595470689372094546608778192464102231199438384496801130956362754363924279752131829155620999376830152021359426328017521375224415459564117813672485969837451601864675477684224,4052261297735344686047273307665683510462781045777319408476720997553368273821926429896656608729727124125258327598847993407492767653220331867569608476513808720191309563119718629376,6553174556823330892116254320152311038743982183719573107661484061838454871420364633838269658797464160082025204171021403280541647602931017261563959574528,8104522595470689372094546612048386401482849493406636730380173741424050886966736682759689499325492160215428322008776691247638319956533513148228717834495015621635333986877781835776,8104522595470689372094546615318580338863467787374891671644464691343606368511712541784501090694969575959551436897043590124005461328952534498320468461867333440425135836052668284928,4052261297735344686047273310935877447843399339745571642055763782614664796864383360524516952434219907510534628248198356637609712385338385451680512638522854504375041685322022780928,8104522595470689372094546608778192464102231199438381789115882791504495405421760823734877907956014744471305207120509792371271178584114491798136967207122697802845532137702895386624,4052261297735344686047273307665683510462781045777316700791472832695109315319407501499705361064742491766411513359931457761242571012919364101588762011150536685585239836147136331776,6553174556823330892116251612467062873885723225217054179264532814173470239061517819599353123151213963441724236405040556815178375568324947534591377276928,8104522595470689372094546615318580338863467787374888963959216526485340364376965802403510566167079691028485607057607031857067676714887223680234227662368213706543635651571507789824,8104522595470689372094546612048386401482849493406634022694925576565784882831989943378698974797602275284362492169340132980700535342468202330142477034995895887753833802396621340672,4052261297735344686047273310935877447843399339745568934370515617756398792729636621143526427906330022579468798408761798370671927771273074633594271839023734770493541500840862285824,8104522595470689372094546608778192464102231199438379081430634626646229401287014084353887383428124859540239377281073234104333393970049180980050726407623578068964031953221734891520,4052261297735344686047273307665683510462781045777313993106224667836843311184660762118714836536852606835345683520494899494304786398854053283502521211651416951703739651665975836672,6553174556823330892116248904781814709027457221082307439883542289645580354130451989759916564884276178827658925586954316015679255834443447350110216781824,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024,8104522595470689372094546615318580338863467787374888963959216526485340364376965802403510566167079691028485607057607031857067675219771048690720542339998629837786106543552516325376,8104522595470689372094546612048386401482849493406634022694925576565784882831989943378698974797602275284362492169340132980700533847352027340628791712626312018996304694377629876224,4052261297735344686047273310935877447843399339745568934370515617756398792729636621143526427906330022579468798408761798370671926276156899644080586516654150901736012392821870821376,8104522595470689372094546608778192464102231199438379081430634626646229401287014084353887383428124859540239377281073234104333392474933005990537041085253994200206502845202743427072,4052261297735344686047273307665683510462781045777313993106224667836843311184660762118714836536852606835345683520494899494304784903737878293988835889281833082946210543646984372224,6553174556823330892116248904781814709027457221082307439883542289645580354130451989759916564884276177332542750597440630693309671965685918242091225317376,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576,8104522595470689372094546615318580338863467787374888963959216526485340364376965802403510566167079691028485607055922035190370761729182036874626403663469577012851132891158464692224,8104522595470689372094546612048386401482849493406634022694925576565784882831989943378698974797602275284362492167655136314003620356763015524534653036097259194061331041983578243072,4052261297735344686047273310935877447843399339745568934370515617756398792729636621143526427906330022579468798407076801703975012785567887827986447840125098076801038740427819188224,8104522595470689372094546608778192464102231199438379081430634626646229401287014084353887383428124859540239377279388237437636478984343994174442902408724941375271529192808691793920,4052261297735344686047273307665683510462781045777313993106224667836843311184660762118714836536852606835345683518809902827607871413148866477894697212752780258011236891252932739072,6553174556823330892116248904781814709027457221082307439883542289645580354130451989758231568217579263841953738781346492016780619140750944589697173684224,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424]
namespace Part0
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486921081282747169098543282348458491817253560211410079528250249916447819765314548169410993333974180157294286131481861375947870741484162762797346943454374736080161910261659233079525376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 67 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 34 0 (.split 12 0 (.step 7 (.run (.close 9))) (.split 35 0 (.step 7 (.run (.close 9))) (.step 9 (.step 7 (.step 15 (.step 18 (.run (.close 21)))))))) (.split 35 0 (.step 7 (.step 9 (.step 7 (.run (.close 15))))) (.step 15 (.step 7 (.run (.close 21)))))) (.step 7 (.step 9 (.step 7 (.step 15 (.step 17 (.run (.close 18)))))))) (.split 21 0 (.step 7 (.step 9 (.step 7 (.step 15 (.step 17 (.run (.close 18))))))) (.step 7 (.step 17 (.run (.close 18)))))) (.split 17 0 (.split 21 0 (.step 7 (.step 9 (.step 7 (.step 15 (.step 17 (.run (.close 18))))))) (.step 7 (.step 17 (.run (.close 18))))) (.step 7 (.run (.close 18))))) (.split 10 0 (.split 12 0 (.step 18 (.split 16 0 (.step 29 (.step 75 (.run (.close 7)))) (.step 18 (.run (.close 7))))) (.step 9 (.split 16 0 (.split 17 0 (.step 26 (.step 75 (.step 7 (.run (.close 18))))) (.step 18 (.step 15 (.step 18 (.run (.close 21)))))) (.step 18 (.step 15 (.step 18 (.run (.close 21)))))))) (.step 18 (.split 12 0 (.step 7 (.step 9 (.step 15 (.run (.close 18))))) (.step 15 (.run (.close 7))))))) (.split 72 1 (.split 21 0 (.split 35 0 (.split 10 0 (.step 70 (.run (.close 7))) (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.step 21 (.run (.close 26)))))) (.step 7 (.step 9 (.run (.close 26))))) (.step 7 (.step 9 (.step 26 (.step 21 (.step 54 (.run (.close 57)))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part0
namespace Part1
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384264315699200, 11031304526203984395224077729546701486925133544044904446828460657397434823063526609582539270131159620200379099931298045612181862426357859598628248613617910094743402755701560707737664574975365249031868091706248450277376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 72 0 (.split 10 0 (.split 16 0 (.step 9 (.step 7 (.step 18 (.step 22 (.run (.close 26)))))) (.step 18 (.step 9 (.run (.close 21))))) (.step 15 (.step 7 (.run (.close 9))))) (.step 18 (.step 9 (.run (.close 26))))) (.step 18 (.step 9 (.step 7 (.step 22 (.step 18 (.run (.close 26)))))))) (.split 12 0 (.step 18 (.step 9 (.step 7 (.run (.close 21))))) (.step 9 (.step 15 (.step 21 (.step 7 (.step 18 (.run (.close 26))))))))) (.step 15 (.step 18 (.step 9 (.step 18 (.step 21 (.run (.close 26)))))))) (.step 18 (.step 9 (.step 18 (.step 15 (.step 18 (.step 21 (.step 18 (.run (.close 26)))))))))) (.step 9 (.step 57 (.run (.close 7))))) (.step 57 (.split 10 0 (.split 16 0 (.split 12 0 (.split 21 0 (.split 34 0 (.step 70 (.step 7 (.step 9 (.run (.close 21))))) (.step 7 (.step 9 (.run (.close 26))))) (.step 7 (.step 9 (.run (.close 26))))) (.step 9 (.step 15 (.step 26 (.run (.close 57)))))) (.step 7 (.step 9 (.step 21 (.run (.close 26)))))) (.step 7 (.step 9 (.step 15 (.run (.close 26)))))))) (.step 9 (.step 26 (.step 57 (.step 7 (.run (.close 18)))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part1
namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660749386805549175884476045519682621152070220555079396390043072223356798867117014992814086484636469259678209525254359177288413835952018510578314660701798400⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Enumeration.Proof 2 := (.split 51 1 (.split 54 1 (.split 59 1 (.reuse 0) (.split 67 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 12 0 (.split 21 0 (.step 62 (.run (.close 7))) (.step 9 (.run (.close 18)))) (.step 9 (.split 21 0 (.step 62 (.run (.close 7))) (.step 15 (.step 18 (.step 21 (.step 18 (.run (.close 26))))))))) (.step 55 (.step 27 (.step 18 (.step 7 (.step 18 (.run (.close 21)))))))) (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 15 (.run (.close 18)))))) (.step 15 (.step 7 (.run (.close 9)))))) (.step 9 (.step 62 (.step 18 (.run (.close 15)))))) (.step 26 (.step 62 (.run (.close 7)))))) (.reuse 1)) (.split 54 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 59 1 (.step 54 (.run (.close 7))) (.step 62 (.run (.close 7)))) (.step 7 (.step 9 (.step 52 (.step 9 (.run (.close 15))))))) (.step 7 (.step 9 (.step 27 (.step 22 (.run (.close 54))))))) (.step 7 (.step 9 (.step 27 (.step 21 (.step 26 (.run (.close 53)))))))) (.step 7 (.step 9 (.step 21 (.step 26 (.run (.close 21))))))) (.step 7 (.step 9 (.step 26 (.run (.close 54)))))) (.step 7 (.step 9 (.step 26 (.step 21 (.step 54 (.run (.close 57)))))))) (.step 54 (.step 7 (.step 9 (.step 54 (.step 21 (.step 26 (.step 57 (.run (.close 70)))))))))) (.step 57 (.run (.close 7)))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.covered
  · exact Part1.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part2
namespace Part3
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922103644135012059424734283689937543763013994501621657294080218808964757922244700851138879601264205679804898147291491562572142870528000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 12 0 (.split 17 0 (.split 22 0 (.step 9 (.step 18 (.run (.close 52)))) (.step 7 (.step 9 (.step 7 (.run (.close 18)))))) (.step 55 (.step 7 (.run (.close 9))))) (.step 9 (.split 21 0 (.split 35 0 (.split 34 0 (.step 7 (.step 26 (.run (.close 18)))) (.step 15 (.run (.close 7)))) (.step 15 (.step 53 (.step 7 (.step 18 (.run (.close 26))))))) (.step 15 (.step 18 (.step 21 (.step 18 (.run (.close 26))))))))) (.step 55 (.step 27 (.step 18 (.step 7 (.step 18 (.run (.close 21)))))))) (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 15 (.run (.close 18)))))) (.step 15 (.step 7 (.run (.close 9)))))) (.step 9 (.step 62 (.step 40 (.step 52 (.step 15 (.step 18 (.run (.close 21))))))))) (.step 52 (.step 7 (.run (.close 9))))) (.step 52 (.step 7 (.step 18 (.run (.close 26)))))) (.step 9 (.step 52 (.step 57 (.step 7 (.run (.close 18))))))) (.step 52 (.step 7 (.step 9 (.run (.close 52)))))) (.step 52 (.step 7 (.step 18 (.run (.close 21))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part3
namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106416804706180239593862104121686846717430938697033110655389288545372543552506476761919575670309819382995538502452966143971844685824⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Enumeration.Proof 2 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 12 0 (.split 17 0 (.split 22 0 (.step 9 (.step 18 (.run (.close 53)))) (.step 7 (.step 9 (.step 7 (.run (.close 18)))))) (.step 55 (.step 7 (.run (.close 9))))) (.step 9 (.split 21 0 (.split 35 0 (.split 22 0 (.step 53 (.step 7 (.run (.close 15)))) (.step 7 (.step 15 (.step 18 (.run (.close 26)))))) (.step 15 (.step 21 (.run (.close 7))))) (.step 15 (.step 18 (.step 21 (.step 18 (.run (.close 26))))))))) (.step 55 (.step 27 (.step 18 (.step 7 (.step 18 (.run (.close 21)))))))) (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 15 (.run (.close 18)))))) (.step 15 (.step 7 (.run (.close 9)))))) (.step 9 (.step 62 (.step 38 (.step 7 (.step 15 (.step 18 (.run (.close 53))))))))) (.step 53 (.run (.close 7)))) (.step 53 (.step 7 (.run (.close 26))))) (.step 9 (.step 53 (.step 57 (.step 7 (.run (.close 18))))))) (.step 53 (.step 7 (.run (.close 9)))))) (.reuse 1)) (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 22 0 (.step 9 (.step 7 (.step 9 (.run (.close 46))))) (.step 7 (.step 9 (.run (.close 27))))) (.step 7 (.step 9 (.run (.close 46))))) (.step 7 (.step 9 (.run (.close 27))))) (.step 7 (.step 9 (.run (.close 27))))) (.step 7 (.run (.close 9)))) (.step 7 (.run (.close 9)))) (.step 7 (.run (.close 9)))) (.step 70 (.step 7 (.run (.close 9))))) (.step 9 (.run (.close 7)))) (.step 54 (.step 7 (.run (.close 9))))) (.step 9 (.step 27 (.run (.close 46))))) (.step 9 (.step 27 (.step 46 (.run (.close 52)))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.covered
  · exact Part3.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part4
namespace Part5
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452123411166788548947610075842614532351263478466837987518627380693192075645315780456802274236057420639647458918400⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Enumeration.Proof 1 := (.split 42 1 (.reuse 0) (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 21 0 (.split 34 0 (.split 36 0 (.step 7 (.step 21 (.run (.close 26)))) (.split 49 0 (.step 7 (.step 29 (.step 39 (.step 7 (.run (.close 21)))))) (.step 7 (.step 21 (.run (.close 26)))))) (.split 49 0 (.split 72 1 (.split 50 0 (.step 7 (.step 9 (.run (.close 15)))) (.step 7 (.step 15 (.run (.close 21))))) (.step 29 (.step 37 (.run (.close 45))))) (.step 7 (.step 15 (.step 21 (.run (.close 26))))))) (.step 7 (.step 15 (.run (.close 26))))) (.step 26 (.split 10 0 (.split 12 0 (.step 7 (.step 45 (.step 38 (.step 26 (.run (.close 52)))))) (.step 9 (.step 15 (.step 18 (.step 26 (.step 21 (.step 37 (.run (.close 57))))))))) (.step 7 (.run (.close 15)))))) (.step 26 (.step 29 (.step 57 (.split 21 0 (.split 10 0 (.split 16 0 (.split 12 0 (.step 45 (.step 7 (.step 21 (.step 26 (.run (.close 52)))))) (.step 15 (.step 26 (.step 18 (.step 21 (.step 37 (.run (.close 57)))))))) (.step 7 (.step 18 (.step 15 (.run (.close 21)))))) (.step 7 (.step 15 (.run (.close 7))))) (.step 7 (.step 18 (.step 15 (.run (.close 26)))))))))) (.step 26 (.step 57 (.step 62 (.split 10 0 (.split 12 0 (.step 7 (.step 38 (.step 26 (.run (.close 52))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.run (.close 53)))))))) (.step 7 (.run (.close 15)))))))) (.step 26 (.step 57 (.step 62 (.split 50 1 (.split 10 0 (.split 12 0 (.step 7 (.step 45 (.step 38 (.step 26 (.run (.close 52)))))) (.step 9 (.step 15 (.step 18 (.step 26 (.step 21 (.step 37 (.run (.close 52))))))))) (.step 7 (.run (.close 15)))) (.step 9 (.step 52 (.step 7 (.run (.close 21))))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part5
namespace Part6
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203979496340767072204264539074732142405299924596678035534750176926387658708231078033304913143084022008172098353367136336740104587205998257104147246117336343144450774475584795097950282749561115337437403414528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 21 0 (.split 34 0 (.split 42 0 (.step 7 (.step 21 (.run (.close 26)))) (.split 49 0 (.step 7 (.step 29 (.step 39 (.run (.close 21))))) (.step 7 (.step 21 (.run (.close 26)))))) (.split 49 0 (.split 72 1 (.split 50 0 (.step 7 (.step 9 (.run (.close 15)))) (.step 7 (.step 15 (.run (.close 21))))) (.step 29 (.step 37 (.run (.close 39))))) (.step 7 (.step 15 (.step 21 (.step 26 (.run (.close 21)))))))) (.step 7 (.step 15 (.run (.close 26))))) (.step 57 (.step 7 (.step 26 (.step 37 (.step 38 (.step 15 (.step 26 (.run (.close 52)))))))))) (.step 29 (.step 57 (.run (.close 7))))) (.step 57 (.split 72 1 (.split 34 0 (.step 55 (.step 9 (.step 53 (.run (.close 7))))) (.step 7 (.step 15 (.step 21 (.step 38 (.step 52 (.run (.close 62)))))))) (.step 7 (.step 26 (.step 15 (.run (.close 21)))))))) (.step 57 (.split 50 1 (.split 72 1 (.split 34 0 (.step 55 (.step 9 (.step 52 (.step 7 (.step 21 (.run (.close 26))))))) (.step 7 (.step 15 (.step 21 (.step 52 (.run (.close 26))))))) (.step 7 (.step 26 (.step 15 (.run (.close 21)))))) (.step 9 (.step 52 (.step 7 (.step 21 (.run (.close 26)))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part6
namespace Part7
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452123413460287164937681587453435427653350419263402976686908504430780915032238656545287082306075973749773145473024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 18 (.split 16 0 (.step 29 (.split 30 0 (.step 38 (.run (.close 7))) (.step 7 (.run (.close 18))))) (.step 18 (.run (.close 7))))) (.step 9 (.split 17 0 (.split 21 0 (.step 38 (.step 7 (.step 21 (.run (.close 26))))) (.step 15 (.step 18 (.run (.close 21))))) (.step 18 (.step 15 (.step 18 (.run (.close 21)))))))) (.step 18 (.split 12 0 (.step 7 (.step 9 (.step 15 (.run (.close 18))))) (.step 15 (.run (.close 7)))))) (.step 29 (.step 38 (.run (.close 7))))) (.step 75 (.step 7 (.step 9 (.step 21 (.step 26 (.run (.close 57)))))))) (.step 9 (.step 26 (.step 75 (.step 40 (.step 38 (.step 18 (.run (.close 21))))))))) (.step 9 (.step 38 (.step 57 (.run (.close 7)))))) (.step 57 (.step 7 (.step 9 (.step 53 (.step 26 (.step 62 (.step 38 (.step 70 (.run (.close 75))))))))))) (.step 9 (.step 21 (.step 38 (.step 53 (.split 10 0 (.step 21 (.step 18 (.run (.close 21)))) (.step 15 (.step 18 (.run (.close 21)))))))))) (.step 9 (.step 53 (.step 57 (.step 62 (.split 51 1 (.step 75 (.split 67 1 (.split 10 0 (.split 21 0 (.split 34 0 (.step 53 (.step 40 (.split 36 0 (.step 52 (.step 18 (.run (.close 26)))) (.step 18 (.step 26 (.run (.close 37))))))) (.step 15 (.step 18 (.step 21 (.step 26 (.run (.close 37))))))) (.step 18 (.step 21 (.run (.close 26))))) (.step 15 (.step 18 (.run (.close 21))))) (.step 7 (.step 26 (.step 21 (.run (.close 52))))))) (.step 7 (.run (.close 52))))))))) (.step 9 (.run (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 7 (.step 37 (.run (.close 38))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part7
namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762002869938770909476934032216990377794945951885006779211721752447241263771153730546005074358518476177408000⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part7.root]
def proof : Enumeration.Proof 3 := (.split 35 1 (.split 36 1 (.reuse 0) (.step 7 (.split 42 1 (.reuse 1) (.split 49 1 (.split 50 1 (.step 45 (.split 59 1 (.split 21 0 (.split 49 0 (.step 39 (.step 7 (.step 26 (.step 15 (.step 38 (.step 15 (.step 39 (.run (.close 57))))))))) (.step 7 (.step 37 (.step 21 (.step 26 (.step 21 (.step 39 (.run (.close 57))))))))) (.step 7 (.step 15 (.step 26 (.step 15 (.run (.close 39))))))) (.step 7 (.step 57 (.step 45 (.step 38 (.step 62 .point))))))) (.step 7 (.step 26 (.step 38 (.step 57 (.step 37 (.step 62 (.step 15 (.step 45 (.split 49 0 (.step 2 .point) (.step 0 (.step 1 .point)))))))))))) (.step 7 (.step 26 (.step 57 (.split 34 0 (.step 62 (.step 21 (.step 38 .point))) (.step 15 (.step 37 (.split 50 1 (.step 2 (.split 50 0 (.step 2 .point) (.step 0 (.step 1 .point)))) (.step 0 (.step 1 .point))))))))))))) (.split 36 1 (.reuse 2) (.step 7 (.step 29 (.step 38 (.step 7 (.step 37 (.run (.close 38)))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.covered
  · exact Part6.covered
  · exact Part7.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part8
namespace Part9
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732142405299924596678035534750176926387658708231078033304913143084019659631755324276086251470065240149539325699719983294700285388379231367523472360686979995943608062005978595328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 21 0 (.split 36 0 (.split 42 0 (.step 7 (.step 15 (.run (.close 21)))) (.split 49 0 (.step 7 (.step 29 (.step 37 (.step 7 (.step 15 (.run (.close 21))))))) (.step 7 (.step 15 (.step 21 (.run (.close 26))))))) (.split 49 0 (.split 72 1 (.split 50 0 (.step 7 (.step 9 (.run (.close 15)))) (.step 7 (.step 15 (.run (.close 21))))) (.step 29 (.step 37 (.step 7 (.run (.close 21)))))) (.step 7 (.step 15 (.step 21 (.step 26 (.run (.close 21)))))))) (.step 7 (.step 15 (.run (.close 26))))) (.step 15 (.step 7 (.step 26 (.step 37 (.step 38 (.step 26 (.run (.close 52))))))))) (.step 15 (.step 29 (.step 57 (.step 75 (.split 21 0 (.split 49 0 (.split 16 0 (.split 22 0 (.step 57 (.run (.close 7))) (.step 7 (.run (.close 26)))) (.step 7 (.run (.close 21)))) (.step 7 (.step 37 (.step 21 (.step 26 (.run (.close 52))))))) (.step 7 (.run (.close 26))))))))) (.step 15 (.step 57 (.split 72 1 (.split 35 0 (.step 55 (.step 9 (.step 52 (.step 7 (.step 26 (.step 57 (.run (.close 62)))))))) (.step 7 (.step 21 (.run (.close 38))))) (.step 7 (.step 26 (.step 21 (.run (.close 37))))))))) (.step 15 (.step 52 (.step 57 (.step 7 (.step 52 (.step 75 (.step 21 (.run (.close 26))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part9
namespace Part10
def root : Box := ⟨4697089645037150811387382308463235191639921341107634210713651743042619977812959247249288758524523951425585152, 11031304526203979496340767072204264539074732142405299924596678035534750176926387658708231080740990161307942283315219439800339493278096243451182440891303734335580691896610623263551554548042937179428546447326384624762880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 49 1 (.split 50 1 (.step 45 (.split 59 1 (.step 37 (.split 21 0 (.split 49 0 (.step 39 (.step 7 (.step 15 (.step 26 (.step 21 (.step 37 (.run (.close 39)))))))) (.step 7 (.step 15 (.step 37 (.run (.close 52)))))) (.step 7 (.step 15 (.step 26 (.run (.close 37))))))) (.step 7 (.step 15 (.step 57 (.step 37 (.step 26 (.step 38 (.step 45 (.step 52 .point)))))))))) (.step 7 (.step 15 (.step 38 (.step 57 (.step 37 (.step 26 (.step 45 (.step 75 (.step 52 (.split 49 0 (.step 2 .point) (.step 0 (.step 1 .point))))))))))))) (.step 7 (.step 15 (.step 37 (.step 57 (.split 50 1 (.step 37 (.step 75 (.step 52 (.step 37 (.split 50 0 (.step 2 .point) (.step 0 (.step 1 .point))))))) (.step 0 (.step 1 (.step 38 (.step 52 .point))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part10
namespace Part11
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507669761939882174912725046102278478199165360061331754999348453967921152⟩
def references : Fin 3 → Box := ![Part8.root, Part9.root, Part10.root]
def proof : Enumeration.Proof 3 := (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 1) (.split 49 1 (.split 50 1 (.step 45 (.split 59 1 (.split 21 0 (.split 49 0 (.step 45 (.step 29 (.step 39 (.step 45 (.step 7 (.run (.close 15))))))) (.step 7 (.step 15 (.step 37 (.run (.close 52)))))) (.step 7 (.step 15 (.step 26 (.run (.close 37)))))) (.step 7 (.step 15 (.step 57 (.step 37 (.step 38 (.step 45 (.step 52 .point))))))))) (.step 7 (.step 15 (.step 26 (.step 38 (.step 57 (.step 37 (.step 62 (.step 45 (.split 49 0 (.step 2 .point) (.step 0 (.step 1 .point)))))))))))) (.step 7 (.step 15 (.step 26 (.step 57 (.split 50 1 (.step 37 (.step 62 (.step 37 (.split 50 0 (.step 2 .point) (.step 0 (.step 1 .point)))))) (.step 0 (.step 1 (.step 38 (.step 52 .point))))))))))) (.reuse 2)) (.step 29 (.step 38 (.step 37 (.step 7 (.step 37 (.run (.close 38)))))))))) (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.step 7 (.step 18 (.run (.close 7)))) (.step 7 (.run (.close 18)))) (.step 18 (.run (.close 53)))) (.step 18 (.step 53 (.step 7 (.step 9 (.step 15 (.run (.close 18)))))))) (.step 18 (.step 53 (.step 18 (.split 54 1 (.step 7 (.step 53 (.step 7 (.step 9 (.step 15 (.run (.close 18))))))) (.step 9 (.step 18 (.run (.close 52))))))))) (.step 18 (.step 7 (.step 9 (.step 18 (.run (.close 38)))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.covered
  · exact Part9.covered
  · exact Part10.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part11
namespace Part12
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429148918254945690599483432967365594029418708386292170752⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Enumeration.Proof 1 := (.split 21 1 (.split 22 1 (.reuse 0) (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 21 0 (.step 7 (.step 18 (.run (.close 7)))) (.step 7 (.step 17 (.run (.close 18))))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 18 (.run (.close 26)))) (.step 18 (.step 26 (.step 55 (.step 53 (.run (.close 7))))))) (.step 18 (.step 26 (.step 55 (.step 53 (.step 18 (.step 62 (.step 18 (.run (.close 7)))))))))) (.step 18 (.step 26 (.step 7 (.step 18 (.run (.close 7))))))))) (.step 7 (.step 18 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.step 18 (.split 50 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 26 (.run (.close 54))))) (.step 9 (.split 34 0 (.step 7 (.step 18 (.step 26 (.step 54 (.run (.close 26)))))) (.step 7 (.run (.close 15)))))) (.step 7 (.step 18 (.step 15 (.run (.close 26)))))) (.step 9 (.step 18 (.step 26 (.step 54 (.step 57 (.run (.close 62)))))))) (.step 9 (.run (.close 57)))) (.step 9 (.step 18 (.run (.close 53)))))) (.step 9 (.step 18 (.step 55 (.step 53 (.step 18 (.run (.close 52)))))))) (.step 7 (.run (.close 9)))) (.step 7 (.step 26 (.step 15 (.run (.close 39)))))) (.step 7 (.run (.close 39)))) (.step 7 (.step 9 (.step 18 (.step 38 (.run (.close 39))))))) (.step 7 (.step 37 (.step 38 (.run (.close 57)))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part12
namespace Part13
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954774974591744319128219513855717148721152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.split 17 0 (.split 21 0 (.split 22 0 (.step 7 (.step 18 (.run (.close 7)))) (.step 7 (.step 17 (.run (.close 18))))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 18 (.run (.close 21)))) (.step 18 (.step 21 (.step 42 (.step 53 (.step 18 (.run (.close 7)))))))) (.step 18 (.step 21 (.step 42 (.step 53 (.step 18 (.step 55 (.step 27 (.step 52 (.step 7 (.step 17 (.step 18 (.run (.close 53)))))))))))))) (.step 18 (.step 21 (.step 7 (.step 18 (.run (.close 7))))))) (.step 7 (.step 18 (.split 35 1 (.step 18 (.step 53 (.split 49 1 (.step 2 (.split 49 0 (.step 2 .point) (.split 50 1 (.step 2 .point) (.step 0 (.step 1 .point))))) (.split 50 1 (.step 2 (.split 50 0 (.step 2 .point) (.step 0 (.step 1 .point)))) (.step 0 (.step 1 .point)))))) (.step 18 .point))))) (.step 7 (.step 18 (.split 35 1 (.split 49 1 (.step 25 (.step 18 (.step 19 (.step 53 (.split 49 0 (.step 2 .point) (.split 50 1 (.step 2 .point) (.step 0 (.step 1 .point)))))))) (.step 18 (.step 53 (.split 50 1 (.step 19 (.step 25 (.split 50 0 (.step 2 .point) (.step 0 (.step 1 .point))))) (.step 0 (.step 1 .point)))))) (.step 18 (.step 19 .point))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part13
namespace Part14
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752660196157072026346058709379448751222437197125439454832555514724895000913419667368971441370966418073051659960163035464077433251276733389682312690532352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.step 18 (.split 21 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 72 0 (.split 10 0 (.split 16 0 (.step 9 (.step 7 (.run (.close 15)))) (.step 18 (.step 9 (.run (.close 15))))) (.step 15 (.run (.close 7)))) (.step 15 (.run (.close 7)))) (.step 18 (.step 9 (.step 7 (.run (.close 15)))))) (.step 15 (.run (.close 7)))) (.step 15 (.run (.close 7)))) (.step 15 (.run (.close 7)))) (.step 9 (.step 15 (.run (.close 7))))) (.step 15 (.split 10 0 (.split 16 0 (.split 21 0 (.split 34 0 (.split 35 0 (.step 70 (.step 9 (.run (.close 15)))) (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.step 15 (.run (.close 21)))))) (.step 7 (.step 9 (.run (.close 15))))))) (.step 9 (.step 15 (.run (.close 7)))))) (.step 15 (.step 21 (.step 22 (.step 26 (.step 9 (.step 15 (.step 7 (.step 18 (.step 21 (.step 22 (.run (.close 26))))))))))))) (.step 15 (.step 21 (.step 15 (.step 18 (.run (.close 15))))))) (.step 7 (.step 15 (.step 57 (.step 62 (.split 21 1 (.split 67 1 (.split 10 0 (.split 16 0 (.split 21 0 (.split 34 0 (.split 35 0 (.step 54 (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.run (.close 15))))) (.step 7 (.step 9 (.run (.close 21))))) (.step 7 (.step 9 (.run (.close 15))))) (.step 70 (.run (.close 7)))) (.step 7 (.step 9 (.run (.close 15)))))))))) (.step 15 (.step 21 (.step 22 (.step 26 (.step 9 (.step 15 (.step 21 (.run (.close 53))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part14
namespace Part15
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303819740104044092417662777429065728⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Enumeration.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.step 15 (.step 21 (.step 22 (.step 26 (.step 9 (.step 15 (.run (.close 52))))))))) (.step 7 (.step 9 (.step 7 (.step 27 (.run (.close 46))))))) (.step 7 (.step 15 (.step 26 (.step 29 (.split 21 1 (.split 21 0 (.split 10 0 (.split 16 0 (.split 22 0 (.step 15 (.run (.close 7))) (.step 7 (.run (.close 15)))) (.step 7 (.run (.close 15)))) (.step 7 (.run (.close 15)))) (.step 7 (.run (.close 15)))) (.step 7 (.run (.close 15))))))))) (.step 7 (.step 15 (.step 29 (.step 57 (.step 75 (.split 21 1 (.split 42 1 (.split 21 0 (.split 49 0 (.split 50 0 (.step 7 (.run (.close 15))) (.step 7 (.run (.close 15)))) (.step 7 (.run (.close 15)))) (.step 7 (.run (.close 15)))) (.step 37 (.step 39 (.step 7 (.run (.close 15)))))) (.step 7 (.run (.close 15)))))))))) (.step 9 (.step 15 (.step 21 (.step 22 (.step 26 (.step 9 (.step 15 (.step 21 (.step 26 (.step 22 (.step 26 (.run (.close 38)))))))))))))) (.step 7 (.step 15 (.step 7 (.run (.close 37)))))) (.step 7 (.step 18 (.step 15 (.step 52 (.run (.close 53)))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part15
namespace Part16
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565993757032507671448582053429150416294123954776303821007754644320647064274132271104⟩
def references : Fin 3 → Box := ![Part12.root, Part13.root, Part15.root]
def proof : Enumeration.Proof 3 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.step 18 (.split 22 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.split 16 0 (.split 21 0 (.split 22 0 (.step 7 (.step 18 (.run (.close 7)))) (.step 7 (.step 17 (.run (.close 18))))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 18 (.run (.close 22)))) (.step 18 (.step 22 (.step 55 (.step 53 (.run (.close 7))))))) (.step 18 (.step 22 (.step 55 (.step 53 (.step 18 (.step 61 (.step 7 (.step 18 (.step 7 (.run (.close 53)))))))))))) (.step 18 (.step 22 (.step 7 (.step 18 (.run (.close 7))))))) (.step 7 (.step 18 (.split 35 1 (.step 18 (.step 62 (.split 49 1 (.step 2 (.split 49 0 (.step 2 .point) (.split 50 1 (.step 2 .point) (.step 0 (.step 1 .point))))) (.split 50 1 (.step 2 (.split 50 0 (.step 2 .point) (.step 0 (.step 1 .point)))) (.step 0 (.step 1 .point)))))) (.step 18 .point)))))))) (.reuse 1)) (.reuse 2)) (.step 7 (.split 12 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 72 1 (.step 7 (.step 18 (.run (.close 7)))) (.step 7 (.step 15 (.run (.close 18))))) (.step 18 (.run (.close 15)))) (.step 18 (.split 54 1 (.step 7 (.step 52 (.step 7 (.step 9 (.run (.close 15)))))) (.step 9 (.step 15 (.step 7 (.step 18 (.run (.close 52))))))))) (.step 18 (.step 52 (.step 18 (.run (.close 7)))))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.run (.close 18)))))))) (.step 15 (.run (.close 18))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.covered
  · exact Part13.covered
  · exact Part15.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part16
theorem covered : Enumeration.Covers points 11 families root := Part16.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families 11 header := rfl
end Core
namespace Lift0
def root : Box := ⟨8104522595470689372094546612048386401482849493406639438065421906282312194009598640247690832260516139630734067652120489716524574352906024022270887037121590409858910989281788952576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨8104522595470689372094546615318580338863467787374894379329712856201867675554574499272502423629993555374857182540387388592891715725325045372362637664493908228648712838456675401728, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 21 (.step 22 (.step 23 (.step 26 (.step 27 (.step 28 (.step 29 (.step 31 (.step 37 (.step 21 (.step 22 (.step 26 (.run (.close 39)))))))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨4052261297735344686047273310935877447843399339745574349741011947472926103907245318012518285369243886925840373891542155106495966781710896325722681841149429292598618687726029897728, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
namespace Lift3
def root : Box := ⟨6553174556823330892116254320152311038743984532257676392010356342897936776196255120964575276122865568303196758178120263374620574327040550850784057622528, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37)))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift3
namespace Lift4
def root : Box := ⟨8104522595470689372094546608778192464102231199438384496801130956362756712464622781222879240891038723886610952763853590840157432980487002672179136409749272591069109140106902503424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37)))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift4
namespace Lift5
def root : Box := ⟨4052261297735344686047273307665683510462781045777319408476720997553370622362269458987706693999766471181717259003275256230128825409291874975630931213777111473808816838551143448576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift5
namespace Lift6
def root : Box := ⟨6553174556823330892116254320152311038743984532259916136752534147108494218476823565242696921620100217838096747279082726017804950356548524536995384393728, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift6
namespace Lift7
def root : Box := ⟨8104522595470689372094546612048386401482849493406639438065421906282309845469255611156640746990476792574275136247693226893888516596834480914209564299858287656241403713850364133376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift7
namespace Lift8
def root : Box := ⟨8104522595470689372094546615318580338863467787374894379329712856201865327014231470181452338359954208318398251135960125770255657969253502264301314927230605475031205563025250582528, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 21 (.step 22 (.step 23 (.step 26 (.step 27 (.step 28 (.step 29 (.step 31 (.run (.close 37)))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift8
namespace Lift9
def root : Box := ⟨4052261297735344686047273310935877447843399339745574349741011947472923755366902288921468200099204539869381442487114892283859909025639353217661359103886126538981111412294605078528, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift9
namespace Lift10
def root : Box := ⟨8104522595470689372094546608778192464102231199438384496801130956362754363924279752131829155620999376830152021359426328017521375224415459564117813672485969837451601864675477684224, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37)))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift10
namespace Lift11
def root : Box := ⟨4052261297735344686047273307665683510462781045777319408476720997553368273821926429896656608729727124125258327598847993407492767653220331867569608476513808720191309563119718629376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift11
namespace Lift12
def root : Box := ⟨6553174556823330892116254320152311038743982183719573107661484061838454871420364633838269658797464160082025204171021403280541647602931017261563959574528, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift12
namespace Lift13
def root : Box := ⟨8104522595470689372094546612048386401482849493406636730380173741424050886966736682759689499325492160215428322008776691247638319956533513148228717834495015621635333986877781835776, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift13
namespace Lift14
def root : Box := ⟨8104522595470689372094546615318580338863467787374891671644464691343606368511712541784501090694969575959551436897043590124005461328952534498320468461867333440425135836052668284928, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 21 (.step 22 (.step 23 (.step 26 (.step 27 (.step 28 (.step 29 (.step 31 (.run (.close 37)))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift14
namespace Lift15
def root : Box := ⟨4052261297735344686047273310935877447843399339745571642055763782614664796864383360524516952434219907510534628248198356637609712385338385451680512638522854504375041685322022780928, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift15
namespace Lift16
def root : Box := ⟨8104522595470689372094546608778192464102231199438381789115882791504495405421760823734877907956014744471305207120509792371271178584114491798136967207122697802845532137702895386624, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37)))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift16
namespace Lift17
def root : Box := ⟨4052261297735344686047273307665683510462781045777316700791472832695109315319407501499705361064742491766411513359931457761242571012919364101588762011150536685585239836147136331776, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift17
namespace Lift18
def root : Box := ⟨6553174556823330892116251612467062873885723225217054179264532814173470239061517819599353123151213963441724236405040556815178375568324947534591377276928, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 5 (.step 7 (.step 9 (.step 15 (.step 16 (.step 17 (.step 21 (.step 22 (.step 26 (.step 27 (.step 29 (.step 31 (.run (.close 37))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift18
namespace Lift19
def root : Box := ⟨8104522595470689372094546615318580338863467787374888963959216526485340364376965802403510566167079691028485607057607031857067676714887223680234227662368213706543635651571507789824, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift19
namespace Lift20
def root : Box := ⟨8104522595470689372094546612048386401482849493406634022694925576565784882831989943378698974797602275284362492169340132980700535342468202330142477034995895887753833802396621340672, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift20
namespace Lift21
def root : Box := ⟨4052261297735344686047273310935877447843399339745568934370515617756398792729636621143526427906330022579468798408761798370671927771273074633594271839023734770493541500840862285824, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift21
namespace Lift22
def root : Box := ⟨8104522595470689372094546608778192464102231199438379081430634626646229401287014084353887383428124859540239377281073234104333393970049180980050726407623578068964031953221734891520, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.run (.close 20))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift22
namespace Lift23
def root : Box := ⟨4052261297735344686047273307665683510462781045777313993106224667836843311184660762118714836536852606835345683520494899494304786398854053283502521211651416951703739651665975836672, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift23
namespace Lift24
def root : Box := ⟨6553174556823330892116248904781814709027457221082307439883542289645580354130451989759916564884276178827658925586954316015679255834443447350110216781824, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift24
namespace Lift25
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift25
namespace Lift26
def root : Box := ⟨8104522595470689372094546615318580338863467787374888963959216526485340364376965802403510566167079691028485607057607031857067675219771048690720542339998629837786106543552516325376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift26
namespace Lift27
def root : Box := ⟨8104522595470689372094546612048386401482849493406634022694925576565784882831989943378698974797602275284362492169340132980700533847352027340628791712626312018996304694377629876224, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift27
namespace Lift28
def root : Box := ⟨4052261297735344686047273310935877447843399339745568934370515617756398792729636621143526427906330022579468798408761798370671926276156899644080586516654150901736012392821870821376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift28
namespace Lift29
def root : Box := ⟨8104522595470689372094546608778192464102231199438379081430634626646229401287014084353887383428124859540239377281073234104333392474933005990537041085253994200206502845202743427072, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.run (.close 20))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift29
namespace Lift30
def root : Box := ⟨4052261297735344686047273307665683510462781045777313993106224667836843311184660762118714836536852606835345683520494899494304784903737878293988835889281833082946210543646984372224, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift30
namespace Lift31
def root : Box := ⟨6553174556823330892116248904781814709027457221082307439883542289645580354130451989759916564884276177332542750597440630693309671965685918242091225317376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift31
namespace Lift32
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift32
namespace Lift33
def root : Box := ⟨8104522595470689372094546615318580338863467787374888963959216526485340364376965802403510566167079691028485607055922035190370761729182036874626403663469577012851132891158464692224, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift33
namespace Lift34
def root : Box := ⟨8104522595470689372094546612048386401482849493406634022694925576565784882831989943378698974797602275284362492167655136314003620356763015524534653036097259194061331041983578243072, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift34
namespace Lift35
def root : Box := ⟨4052261297735344686047273310935877447843399339745568934370515617756398792729636621143526427906330022579468798407076801703975012785567887827986447840125098076801038740427819188224, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift35
namespace Lift36
def root : Box := ⟨8104522595470689372094546608778192464102231199438379081430634626646229401287014084353887383428124859540239377279388237437636478984343994174442902408724941375271529192808691793920, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.run (.close 20))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift36
namespace Lift37
def root : Box := ⟨4052261297735344686047273307665683510462781045777313993106224667836843311184660762118714836536852606835345683518809902827607871413148866477894697212752780258011236891252932739072, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift37
namespace Lift38
def root : Box := ⟨6553174556823330892116248904781814709027457221082307439883542289645580354130451989758231568217579263841953738781346492016780619140750944589697173684224, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 4 (.step 7 (.step 8 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift38
namespace Lift39
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 60) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 60) root :=
  Fast.check_sound 14 (Enumeration.families 60) (Enumeration.families_valid 60)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift39
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 60) (CoreExtension.extension 60 p) := by
  exact List.forall_mem_cons.mpr ⟨(by simpa only [Lift0.root, upper_eq, CoreExtension.extension] using Lift0.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift1.root, upper_eq, CoreExtension.extension] using Lift1.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift2.root, upper_eq, CoreExtension.extension] using Lift2.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift3.root, upper_eq, CoreExtension.extension] using Lift3.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift4.root, upper_eq, CoreExtension.extension] using Lift4.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift5.root, upper_eq, CoreExtension.extension] using Lift5.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift6.root, upper_eq, CoreExtension.extension] using Lift6.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift7.root, upper_eq, CoreExtension.extension] using Lift7.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift8.root, upper_eq, CoreExtension.extension] using Lift8.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift9.root, upper_eq, CoreExtension.extension] using Lift9.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift10.root, upper_eq, CoreExtension.extension] using Lift10.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift11.root, upper_eq, CoreExtension.extension] using Lift11.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift12.root, upper_eq, CoreExtension.extension] using Lift12.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift13.root, upper_eq, CoreExtension.extension] using Lift13.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift14.root, upper_eq, CoreExtension.extension] using Lift14.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift15.root, upper_eq, CoreExtension.extension] using Lift15.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift16.root, upper_eq, CoreExtension.extension] using Lift16.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift17.root, upper_eq, CoreExtension.extension] using Lift17.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift18.root, upper_eq, CoreExtension.extension] using Lift18.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift19.root, upper_eq, CoreExtension.extension] using Lift19.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift20.root, upper_eq, CoreExtension.extension] using Lift20.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift21.root, upper_eq, CoreExtension.extension] using Lift21.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift22.root, upper_eq, CoreExtension.extension] using Lift22.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift23.root, upper_eq, CoreExtension.extension] using Lift23.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift24.root, upper_eq, CoreExtension.extension] using Lift24.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift25.root, upper_eq, CoreExtension.extension] using Lift25.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift26.root, upper_eq, CoreExtension.extension] using Lift26.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift27.root, upper_eq, CoreExtension.extension] using Lift27.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift28.root, upper_eq, CoreExtension.extension] using Lift28.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift29.root, upper_eq, CoreExtension.extension] using Lift29.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift30.root, upper_eq, CoreExtension.extension] using Lift30.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift31.root, upper_eq, CoreExtension.extension] using Lift31.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift32.root, upper_eq, CoreExtension.extension] using Lift32.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift33.root, upper_eq, CoreExtension.extension] using Lift33.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift34.root, upper_eq, CoreExtension.extension] using Lift34.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift35.root, upper_eq, CoreExtension.extension] using Lift35.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift36.root, upper_eq, CoreExtension.extension] using Lift36.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift37.root, upper_eq, CoreExtension.extension] using Lift37.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift38.root, upper_eq, CoreExtension.extension] using Lift38.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift39.root, upper_eq, CoreExtension.extension] using Lift39.excludes),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 60) (Archive.root 60) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 60)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case173
