module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case171
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473034770628323890015303129108578304,11593776385211162737655,5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424,0⟩
theorem header_valid : Projection.HeaderValid 14 58 0 11 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 58).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473034770628323890015303129108578304⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩]
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
def points : List Nat := [11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424,11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797498561161601720831629746784392225796814106738090890859931077209253557225549206701564962646976646339454285381632,11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797496212621258691740579661514352878740355175333663628037295019453182014117487883964301659893359139064022860562432,11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396464775278045821939237254118739763343628413849368246381508361094747092391044822812881046351507037498938387858753069337050278264832]
namespace Part0
def root : Box := ⟨2147483648, 11567166695907501132681281905800300230278306580764339324022964269698161193987192145795861221865650331035951124682972355085029926420630813678771802534202852461851308071532311824383518927912793342163569234157660769754653130752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 1 (.split 14 0 (.split 16 0 (.split 34 0 (.step 7 (.run (.close 3))) (.step 7 (.step 15 (.run (.close 37))))) (.step 7 (.step 38 (.run (.close 19))))) (.split 10 0 (.split 16 0 (.step 3 (.split 17 0 (.split 34 0 (.step 3 (.step 7 (.run (.close 37)))) (.step 29 (.step 37 (.run (.close 3))))) (.step 7 (.step 3 (.run (.close 19)))))) (.split 30 0 (.step 11 (.step 67 (.step 3 (.step 7 (.run (.close 19)))))) (.step 3 (.step 7 (.run (.close 19)))))) (.step 3 (.step 7 (.run (.close 17)))))) (.split 10 0 (.split 14 0 (.split 16 0 (.step 3 (.split 17 0 (.split 22 0 (.split 30 0 (.step 3 (.step 37 (.step 39 (.step 66 (.run (.close 69)))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 7 (.step 3 (.run (.close 19)))))) (.step 11 (.step 67 (.step 3 (.step 7 (.run (.close 19))))))) (.step 11 (.step 77 (.step 3 (.step 77 (.step 17 (.run (.close 7)))))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 66 (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.step 7 (.step 3 (.run (.close 17)))))) (.step 3 (.step 11 (.step 17 (.step 7 (.run (.close 19))))))))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993925877836143429696690957731067867747567084912312220080475601571065221129460089588115160067528359303968881752396194988183806196447338939416124095009630328894786402041014229845278266359487555174400⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Enumeration.Proof 1 := (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.reuse 0) (.split 74 1 (.split 10 0 (.split 14 0 (.split 30 0 (.step 29 (.step 75 (.run (.close 3)))) (.step 3 (.split 16 0 (.step 29 (.step 38 (.step 7 (.run (.close 37))))) (.step 3 (.run (.close 7)))))) (.step 29 (.step 40 (.step 69 (.step 3 (.step 75 (.step 3 (.step 38 (.run (.close 67)))))))))) (.step 3 (.split 14 0 (.step 3 (.split 16 0 (.split 17 0 (.step 29 (.run (.close 75))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 3 (.run (.close 66)))))) (.step 75 (.step 11 (.step 23 (.step 69 (.run (.close 3)))))))) (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 22 0 (.split 30 0 (.step 74 (.run (.close 3))) (.step 3 (.step 37 (.run (.close 38))))) (.step 3 (.step 69 (.step 3 (.run (.close 37)))))) (.step 67 (.step 3 (.step 38 (.run (.close 69)))))) (.step 74 (.run (.close 3)))) (.step 3 (.step 66 (.step 3 (.run (.close 17)))))) (.step 11 (.step 69 (.step 74 (.run (.close 3)))))) (.step 29 (.step 69 (.step 74 (.run (.close 3))))))) (.split 71 1 (.split 72 1 (.split 74 1 (.step 7 (.run (.close 3))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 69))))) (.step 3 (.step 74 (.split 72 1 (.split 74 1 (.split 14 0 (.split 16 0 (.step 3 (.step 15 (.run (.close 39)))) (.step 3 (.run (.close 19)))) (.step 3 (.step 19 (.run (.close 20))))) (.step 3 (.step 69 (.step 19 (.step 20 (.step 42 (.run (.close 61)))))))) (.step 3 (.step 69 (.step 15 (.step 39 (.run (.close 57))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part1
namespace Part2
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863332063217099735612567131388118500908379528921477156543941149474965073061048180440347529167771712160688997842276817076157398881665024⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Enumeration.Proof 1 := (.split 51 1 (.split 63 1 (.split 64 1 (.reuse 0) (.split 71 1 (.split 72 1 (.split 74 1 (.step 3 (.split 10 0 (.split 65 1 (.split 14 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.step 3 (.step 15 (.step 37 (.run (.close 66))))) (.step 67 (.run (.close 3)))) (.step 3 (.step 37 (.run (.close 38))))) (.step 3 (.run (.close 67)))) (.step 67 (.run (.close 3)))) (.step 67 (.run (.close 3)))) (.step 3 (.step 67 (.run (.close 3))))) (.step 3 (.step 66 (.step 3 (.run (.close 17))))))) (.step 11 (.step 67 (.run (.close 3))))) (.step 29 (.step 67 (.step 3 (.step 39 (.step 45 (.run (.close 66)))))))) (.step 67 (.run (.close 3))))) (.split 64 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 3 (.split 10 0 (.split 65 1 (.split 14 0 (.split 16 0 (.split 30 0 (.step 66 (.run (.close 3))) (.step 3 (.step 37 (.run (.close 38))))) (.step 67 (.step 3 (.step 38 (.run (.close 66)))))) (.step 66 (.run (.close 3)))) (.step 3 (.step 66 (.run (.close 3))))) (.step 3 (.run (.close 66))))) (.step 11 (.step 66 (.step 3 (.step 20 (.step 25 (.run (.close 67)))))))) (.step 29 (.step 66 (.run (.close 3))))) (.step 66 (.run (.close 3)))) (.step 66 (.run (.close 3))))) (.step 3 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 7 (.run (.close 3))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 51)))) (.step 3 (.step 7 (.run (.close 3))))) (.step 3 (.run (.close 51)))) (.step 3 (.step 51 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part2
namespace Part3
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11567172216946143397859013993930440276761051891909598902673568038891978140819468640406180763583123112312546430359927287384778377598839531851350004286991075073525758820243251602222551083980615109495325843832803729355416010752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 64 1 (.step 7 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 14 0 (.split 65 0 (.split 74 0 (.split 16 0 (.step 45 (.step 3 (.run (.close 7)))) (.step 7 (.step 37 (.run (.close 38))))) (.step 7 (.step 37 (.run (.close 39))))) (.step 3 (.step 7 (.step 15 (.run (.close 39)))))) (.step 3 (.step 7 (.step 37 (.run (.close 39)))))) (.step 3 (.step 75 (.step 23 (.split 10 0 (.step 77 (.step 37 (.step 39 (.step 66 (.run (.close 74)))))) (.step 3 (.run (.close 7)))))))) (.step 29 (.step 69 (.step 75 (.step 3 (.run (.close 7))))))) (.step 29 (.step 69 (.step 74 (.split 14 0 (.split 65 0 (.split 10 0 (.split 16 0 (.step 45 (.step 66 (.step 67 (.step 69 (.step 3 (.step 39 (.run (.close 74)))))))) (.step 3 (.step 38 (.step 37 (.run (.close 39)))))) (.step 3 (.step 39 (.step 37 (.step 45 (.run (.close 66))))))) (.step 3 (.step 39 (.step 15 (.step 45 (.run (.close 69))))))) (.step 3 (.step 69 (.step 37 (.run (.close 74)))))))))) (.step 3 (.step 69 (.step 15 (.step 57 (.step 15 (.run (.close 74))))))))) (.step 3 (.step 29 (.step 67 (.step 69 (.split 65 1 (.split 14 0 (.split 65 0 (.split 10 0 (.split 16 0 (.step 45 (.step 66 (.run (.close 67)))) (.step 3 (.step 38 (.step 37 (.run (.close 39)))))) (.step 3 (.step 45 (.step 37 (.step 39 (.run (.close 66))))))) (.step 3 (.step 45 (.step 15 (.step 39 (.run (.close 67))))))) (.step 3 (.run (.close 67)))) (.step 3 (.run (.close 67)))))))))
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
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334835886793856427426712150845226765916193248033129149853347330228236590675856773261540674386841414875538697186776864497930887757824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.step 7 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 14 0 (.split 65 0 (.split 74 0 (.split 10 0 (.step 39 (.run (.close 3))) (.step 7 (.step 37 (.run (.close 39))))) (.step 7 (.step 37 (.run (.close 39))))) (.step 3 (.step 7 (.step 15 (.run (.close 39)))))) (.step 3 (.step 7 (.step 37 (.run (.close 39)))))) (.step 3 (.step 74 (.step 7 (.step 37 (.step 39 (.run (.close 45)))))))) (.step 29 (.step 75 (.step 3 (.run (.close 7)))))) (.step 29 (.step 74 (.run (.close 3))))) (.step 3 (.step 39 (.step 15 (.step 57 (.step 39 (.run (.close 75))))))))) (.step 3 (.step 29 (.step 67 (.step 74 (.step 75 (.split 65 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 51 0 (.step 67 (.run (.close 39))) (.step 3 (.step 15 (.run (.close 39))))) (.step 3 (.step 37 (.run (.close 39))))) (.step 3 (.step 37 (.run (.close 39))))) (.step 3 (.step 37 (.run (.close 38))))) (.step 3 (.step 37 (.run (.close 45))))) (.step 3 (.step 37 (.run (.close 39))))) (.step 3 (.step 39 (.step 15 (.run (.close 67)))))))))))) (.step 3 (.step 29 (.step 66 (.step 74 (.step 75 (.split 65 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 37 (.step 3 (.step 38 (.step 39 (.run (.close 45)))))) (.step 3 (.step 37 (.run (.close 39))))) (.step 3 (.step 37 (.run (.close 38))))) (.step 3 (.run (.close 37)))) (.step 3 (.step 37 (.run (.close 39))))) (.step 3 (.step 15 (.step 39 (.run (.close 66)))))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part4
namespace Part5
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710571549221520149702034641977677192813174361847375949345432920381318993606501990400⟩
def references : Fin 3 → Box := ![Part2.root, Part3.root, Part4.root]
def proof : Enumeration.Proof 3 := (.split 36 1 (.split 42 1 (.split 43 1 (.reuse 0) (.step 3 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 7 (.run (.close 3))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.step 9 (.step 3 (.run (.close 11)))))) (.step 3 (.step 7 (.run (.close 3))))) (.step 3 (.step 9 (.step 11 (.run (.close 9)))))) (.step 3 (.step 9 (.step 11 (.step 3 (.step 29 (.step 3 (.run (.close 47))))))))) (.step 3 (.step 7 (.step 3 (.step 9 (.step 3 (.run (.close 27)))))))))) (.split 43 1 (.split 51 1 (.split 63 1 (.reuse 1) (.step 3 (.step 29 (.step 66 (.step 69 (.split 65 1 (.split 14 0 (.split 65 0 (.split 10 0 (.split 16 0 (.step 45 (.run (.close 66))) (.step 3 (.step 37 (.step 38 (.run (.close 39)))))) (.step 3 (.step 37 (.step 39 (.step 45 (.run (.close 66))))))) (.step 3 (.step 15 (.step 39 (.step 45 (.run (.close 66))))))) (.step 3 (.step 37 (.run (.close 66))))) (.step 3 (.step 15 (.run (.close 66)))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.split 42 1 (.reuse 2) (.step 7 (.step 45 (.split 63 1 (.split 64 1 (.split 65 1 (.split 74 1 (.split 71 1 (.split 16 0 (.step 39 (.step 3 (.run (.close 37)))) (.step 7 (.step 38 (.step 37 (.run (.close 39)))))) (.step 29 (.step 39 (.step 37 (.run (.close 74)))))) (.step 7 (.step 45 (.step 37 (.run (.close 74)))))) (.step 3 (.run (.close 39)))) (.step 29 (.step 67 (.step 74 (.split 14 0 (.step 45 (.step 3 (.run (.close 67)))) (.step 3 (.step 37 (.step 39 (.run (.close 45)))))))))) (.step 29 (.step 37 (.step 66 (.step 74 (.step 45 (.step 3 (.run (.close 66)))))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.covered
  · exact Part3.covered
  · exact Part4.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part5
namespace Part6
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284971111641244310303216007308934677514281085263718115490388093639430481539745137429386777291401487335029156610048⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.split 30 0 (.step 29 (.split 16 0 (.split 22 0 (.split 34 0 (.step 3 (.run (.close 38))) (.step 38 (.run (.close 3)))) (.step 3 (.step 40 (.step 38 (.step 3 (.run (.close 69))))))) (.step 3 (.step 38 (.run (.close 19)))))) (.step 3 (.step 38 (.step 3 (.run (.close 7)))))) (.step 29 (.step 40 (.split 34 0 (.split 16 0 (.split 30 0 (.split 17 0 (.step 38 (.step 3 (.run (.close 69)))) (.step 3 (.step 19 (.step 69 (.run (.close 74)))))) (.step 3 (.run (.close 38)))) (.step 3 (.step 19 (.run (.close 38))))) (.step 3 (.step 37 (.run (.close 38)))))))) (.step 3 (.split 14 0 (.step 3 (.split 16 0 (.split 17 0 (.step 29 (.step 38 (.step 3 (.run (.close 7))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 3 (.run (.close 38)))))) (.step 75 (.step 11 (.step 23 (.split 10 0 (.split 34 0 (.step 77 (.step 3 (.step 38 (.run (.close 74))))) (.step 3 (.step 17 (.step 37 (.run (.close 38)))))) (.step 3 (.run (.close 17)))))))) (.step 29 (.step 38 (.step 7 (.run (.close 69)))))) (.step 29 (.step 38 (.step 74 (.run (.close 3)))))) (.step 3 (.step 40 (.step 9 (.step 38 (.step 3 (.run (.close 7)))))))) (.step 3 (.step 38 (.step 15 (.step 57 (.run (.close 74))))))) (.step 29 (.step 38 (.step 67 (.step 3 (.run (.close 38))))))) (.step 29 (.step 38 (.step 66 (.run (.close 3)))))) (.step 3 (.step 40 (.step 51 (.step 57 (.step 3 (.step 7 (.run (.close 9))))))))) (.step 3 (.step 9 (.run (.close 7))))) (.step 7 (.step 29 (.step 38 (.step 3 (.step 7 (.run (.close 37))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334835886793856427426709802304883736825143162763089802796888398823809327853220715505469131278780092138275394433159357222499462938624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.step 7 (.split 65 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 14 0 (.split 65 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 37 (.run (.close 3))) (.step 7 (.run (.close 37)))) (.step 7 (.run (.close 37)))) (.step 7 (.run (.close 37)))) (.step 7 (.run (.close 37)))) (.step 3 (.step 7 (.step 15 (.run (.close 37)))))) (.step 3 (.step 7 (.run (.close 37))))) (.step 3 (.step 66 (.step 7 (.step 37 (.step 17 (.step 39 (.run (.close 45))))))))) (.step 29 (.step 75 (.step 3 (.run (.close 7)))))) (.step 29 (.step 66 (.step 74 (.step 75 (.split 14 0 (.split 16 0 (.split 30 0 (.step 74 (.run (.close 3))) (.step 3 (.run (.close 37)))) (.step 3 (.run (.close 37)))) (.step 3 (.step 37 (.step 69 (.run (.close 74))))))))))) (.step 3 (.step 15 (.step 37 (.step 39 (.step 74 (.step 37 (.run (.close 75)))))))))) (.step 3 (.step 29 (.step 66 (.step 67 (.step 75 (.split 65 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 67 0 (.step 67 (.run (.close 37))) (.step 3 (.run (.close 37)))) (.step 3 (.run (.close 37)))) (.step 3 (.run (.close 37)))) (.step 3 (.run (.close 37)))) (.step 3 (.run (.close 37)))) (.step 3 (.step 37 (.run (.close 67))))) (.step 3 (.step 37 (.step 39 (.run (.close 67)))))))))))) (.step 3 (.step 29 (.step 66 (.run (.close 3)))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878621701000088909131876905224388669307493450465302002849734043909010401935780749597003795660800⟩
def references : Fin 3 → Box := ![Part5.root, Part6.root, Part7.root]
def proof : Enumeration.Proof 3 := (.split 34 1 (.split 35 1 (.reuse 0) (.split 36 1 (.reuse 1) (.step 7 (.step 29 (.step 38 (.step 7 (.step 38 (.run (.close 39))))))))) (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 2) (.step 7 (.step 37 (.split 63 1 (.split 64 1 (.split 65 1 (.split 74 1 (.split 71 1 (.split 14 0 (.step 45 (.run (.close 3))) (.step 7 (.run (.close 37)))) (.step 29 (.step 39 (.step 66 (.step 69 (.step 74 (.run (.close 3)))))))) (.step 7 (.step 37 (.step 45 (.step 17 (.step 66 (.run (.close 74)))))))) (.step 3 (.step 15 (.step 37 (.run (.close 74)))))) (.step 29 (.step 66 (.step 67 (.split 65 1 (.split 14 0 (.step 45 (.run (.close 3))) (.step 3 (.step 37 (.run (.close 67))))) (.step 3 (.step 37 (.run (.close 67))))))))) (.step 15 (.step 37 (.run (.close 66)))))))) (.step 7 (.step 37 (.split 63 1 (.split 64 1 (.split 65 1 (.split 74 1 (.split 71 1 (.split 14 0 (.step 39 (.run (.close 3))) (.step 7 (.run (.close 37)))) (.step 29 (.step 39 (.step 37 (.step 66 (.run (.close 74))))))) (.step 7 (.step 37 (.step 45 (.step 17 (.step 39 (.step 66 (.run (.close 74))))))))) (.step 3 (.step 15 (.step 37 (.run (.close 39)))))) (.step 29 (.step 66 (.step 67 (.step 74 (.step 37 (.run (.close 3)))))))) (.step 15 (.step 37 (.run (.close 66)))))))) (.step 7 (.step 29 (.step 37 (.step 38 (.step 3 (.step 7 (.run (.close 37))))))))))
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
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567172216946143397859013993925877836143429696690957731067867747567084912312220080475601571065221129460089588115160067528359303968881752396194988183806196449023936082821009996797017337725128958116551371687052139556530814976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 7 (.split 65 1 (.split 71 1 (.split 72 1 (.split 16 0 (.split 17 0 (.step 7 (.step 11 (.split 10 0 (.split 14 0 (.step 3 (.step 7 (.run (.close 19)))) (.step 17 (.step 77 (.run (.close 3))))) (.step 3 (.step 7 (.run (.close 17))))))) (.split 34 0 (.split 35 0 (.step 7 (.step 11 (.step 20 (.step 7 (.step 17 (.run (.close 25))))))) (.step 3 (.step 7 (.step 19 (.step 20 (.run (.close 25))))))) (.step 7 (.step 17 (.run (.close 20)))))) (.split 34 0 (.split 74 1 (.split 10 0 (.split 35 0 (.step 25 (.run (.close 3))) (.step 3 (.step 7 (.run (.close 19))))) (.step 7 (.step 17 (.run (.close 19))))) (.step 11 (.step 19 (.run (.close 25))))) (.step 7 (.step 17 (.step 19 (.run (.close 20))))))) (.step 3 (.step 69 (.step 77 (.step 11 (.step 23 (.split 10 0 (.step 75 (.step 19 (.step 20 (.step 67 (.run (.close 74)))))) (.step 3 (.run (.close 7)))))))))) (.step 11 (.step 69 (.step 74 (.split 35 0 (.split 65 0 (.split 10 0 (.split 14 0 (.split 16 0 (.step 3 (.step 20 (.run (.close 69)))) (.step 67 (.step 3 (.run (.close 20))))) (.step 17 (.step 25 (.step 67 (.step 69 (.step 3 (.step 20 (.run (.close 74))))))))) (.step 3 (.step 17 (.step 19 (.run (.close 20)))))) (.step 3 (.step 20 (.step 19 (.step 25 (.run (.close 69))))))) (.step 3 (.step 69 (.step 19 (.run (.close 74)))))))))) (.step 3 (.step 69 (.step 19 (.step 61 (.step 19 (.step 42 (.run (.close 74))))))))))
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
def root : Box := ⟨3369993333393829974333376885877453834204643052817571560140098764800, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351416920862357228923406966562077843489298713778954698752⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Enumeration.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.reuse 0) (.step 3 (.step 11 (.step 67 (.step 69 (.split 65 1 (.split 35 0 (.split 65 0 (.split 10 0 (.step 67 (.run (.close 3))) (.step 3 (.step 17 (.step 19 (.run (.close 20)))))) (.step 3 (.step 19 (.step 20 (.step 25 (.run (.close 67))))))) (.step 3 (.step 19 (.run (.close 67))))) (.step 3 (.step 42 (.run (.close 67)))))))))) (.step 3 (.step 11 (.step 66 (.step 69 (.split 65 1 (.split 35 0 (.split 65 0 (.split 10 0 (.split 14 0 (.split 16 0 (.step 3 (.step 20 (.run (.close 66)))) (.step 67 (.step 3 (.run (.close 20))))) (.step 17 (.step 25 (.run (.close 66))))) (.step 3 (.step 17 (.step 19 (.run (.close 20)))))) (.step 3 (.step 25 (.step 19 (.step 20 (.run (.close 66))))))) (.step 3 (.run (.close 66)))) (.step 3 (.run (.close 66))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 69 (.step 74 (.step 75 (.step 3 (.split 10 0 (.split 14 0 (.step 40 (.step 75 (.step 7 (.run (.close 19))))) (.step 3 (.step 69 (.step 19 (.step 38 (.step 74 (.run (.close 75)))))))) (.step 3 (.run (.close 7))))))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part10
namespace Part11
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710571549221520149702034641977678689390850988691964189918701621855131121281425997824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.step 7 (.split 65 1 (.split 71 1 (.split 72 1 (.split 16 0 (.split 22 0 (.step 7 (.step 11 (.split 10 0 (.split 14 0 (.step 3 (.step 7 (.run (.close 19)))) (.step 17 (.step 77 (.run (.close 3))))) (.step 3 (.step 7 (.run (.close 17))))))) (.split 34 0 (.split 35 0 (.step 7 (.step 11 (.step 20 (.run (.close 25))))) (.step 3 (.step 7 (.step 19 (.step 20 (.run (.close 25))))))) (.step 7 (.step 17 (.run (.close 20)))))) (.split 34 0 (.split 74 1 (.split 10 0 (.split 35 0 (.step 20 (.run (.close 3))) (.step 3 (.step 7 (.run (.close 19))))) (.step 7 (.step 17 (.run (.close 19))))) (.step 11 (.step 19 (.run (.close 20))))) (.step 7 (.step 17 (.step 19 (.run (.close 20))))))) (.step 3 (.step 74 (.step 7 (.step 19 (.run (.close 69))))))) (.step 11 (.step 74 (.run (.close 3))))) (.step 3 (.step 20 (.step 42 (.step 61 (.step 20 (.run (.close 77))))))))) (.step 3 (.step 11 (.step 67 (.step 74 (.step 77 (.split 65 1 (.split 10 0 (.step 67 (.run (.close 3))) (.step 3 (.step 17 (.run (.close 19))))) (.step 3 (.step 19 (.step 20 (.run (.close 67)))))))))))) (.step 3 (.step 11 (.step 66 (.step 74 (.step 77 (.split 65 1 (.split 10 0 (.split 14 0 (.split 16 0 (.step 3 (.run (.close 19))) (.step 67 (.step 3 (.run (.close 19))))) (.step 17 (.step 51 (.step 66 (.step 3 (.run (.close 20))))))) (.step 3 (.step 17 (.run (.close 19))))) (.step 3 (.step 20 (.step 19 (.run (.close 66)))))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part11
namespace Part12
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418417440033855767995207135346544963110841453878706176⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Enumeration.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.step 3 (.step 7 (.step 66 (.step 67 (.step 74 (.step 77 (.split 10 0 (.split 14 0 (.step 40 (.step 38 (.step 3 (.run (.close 19))))) (.step 3 (.step 19 (.step 69 (.step 19 (.run (.close 38))))))) (.step 3 (.run (.close 7))))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 7 (.step 25 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 71 1 (.split 34 0 (.step 20 (.step 3 (.run (.close 19)))) (.step 7 (.step 17 (.step 19 (.run (.close 20)))))) (.step 11 (.step 20 (.step 19 (.run (.close 74)))))) (.step 7 (.step 25 (.step 19 (.run (.close 74)))))) (.step 3 (.run (.close 20)))) (.step 11 (.step 19 (.step 67 (.step 74 (.step 25 (.step 3 (.run (.close 67))))))))) (.step 11 (.step 66 (.step 74 (.split 10 0 (.split 34 0 (.split 65 1 (.step 25 (.step 3 (.run (.close 19)))) (.step 3 (.step 20 (.run (.close 66))))) (.step 3 (.step 17 (.step 19 (.run (.close 20)))))) (.step 3 (.step 17 (.step 19 (.run (.close 20)))))))))) (.step 3 (.step 7 (.step 19 (.step 66 (.step 74 (.split 14 0 (.step 19 (.step 75 (.step 19 .point))) (.step 19 (.step 20 (.step 25 (.run (.close 75)))))))))))))))
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
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710571549221520149702034641977677194274675999178278867549117753097602013262434533376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.step 7 (.split 65 1 (.split 71 1 (.split 72 1 (.split 17 0 (.split 22 0 (.step 7 (.step 11 (.split 14 0 (.step 3 (.step 7 (.run (.close 19)))) (.step 17 (.step 67 (.step 3 (.step 7 (.run (.close 69))))))))) (.split 34 0 (.split 74 1 (.split 35 0 (.step 7 (.step 11 (.step 17 (.run (.close 19))))) (.step 3 (.step 7 (.run (.close 19))))) (.step 11 (.step 19 (.run (.close 25))))) (.step 7 (.step 17 (.run (.close 19)))))) (.split 34 0 (.split 74 1 (.split 10 0 (.split 30 0 (.split 35 0 (.step 20 (.step 19 (.step 3 (.run (.close 19))))) (.step 3 (.step 7 (.run (.close 19))))) (.step 7 (.run (.close 19)))) (.step 7 (.step 17 (.run (.close 19))))) (.step 11 (.step 19 (.run (.close 20))))) (.step 7 (.step 17 (.run (.close 19)))))) (.step 3 (.step 67 (.step 7 (.step 69 (.step 19 (.step 20 (.run (.close 38))))))))) (.step 11 (.step 67 (.step 74 (.step 77 (.split 10 0 (.step 74 (.run (.close 3))) (.step 3 (.step 17 (.run (.close 19)))))))))) (.step 3 (.step 19 (.step 42 (.step 20 (.step 74 (.step 19 (.run (.close 77)))))))))) (.step 3 (.step 11 (.step 67 (.run (.close 3)))))) (.step 3 (.step 11 (.step 66 (.step 67 (.step 77 (.split 65 1 (.split 10 0 (.split 14 0 (.split 17 0 (.step 3 (.run (.close 66))) (.step 51 (.step 66 (.run (.close 3))))) (.step 17 (.step 66 (.step 3 (.run (.close 19)))))) (.step 3 (.step 17 (.run (.close 19))))) (.step 3 (.step 19 (.step 20 (.run (.close 66)))))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))
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
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901535493098898125339031377679393861109811249152⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Enumeration.Proof 1 := (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.step 3 (.step 7 (.step 38 (.step 3 (.step 66 (.step 67 (.step 74 (.step 7 (.step 77 (.step 19 (.run (.close 38))))))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 7 (.step 19 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 71 1 (.split 35 0 (.step 25 (.run (.close 3))) (.step 7 (.run (.close 19)))) (.step 11 (.step 20 (.step 67 (.step 69 (.step 74 (.run (.close 3)))))))) (.step 7 (.step 19 (.step 25 (.step 38 (.step 67 (.run (.close 74)))))))) (.step 3 (.step 19 (.run (.close 74))))) (.step 11 (.step 19 (.run (.close 67))))) (.step 11 (.step 66 (.step 67 (.split 10 0 (.split 34 0 (.split 65 1 (.step 25 (.step 3 (.step 19 (.run (.close 66))))) (.step 3 (.step 19 (.run (.close 66))))) (.step 3 (.step 17 (.run (.close 19))))) (.step 3 (.step 17 (.run (.close 19))))))))) (.step 3 (.step 7 (.step 19 (.step 66 (.step 67 (.step 74 (.step 19 (.step 75 (.step 19 .point))))))))))))) (.step 7 (.step 19 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 71 1 (.split 35 0 (.step 20 (.run (.close 3))) (.step 7 (.run (.close 19)))) (.step 11 (.step 20 (.step 19 (.step 67 (.run (.close 74))))))) (.step 7 (.step 19 (.step 25 (.step 38 (.step 20 (.step 67 (.run (.close 74))))))))) (.step 3 (.step 19 (.run (.close 20))))) (.step 11 (.step 19 (.run (.close 67))))) (.step 11 (.step 66 (.step 67 (.step 74 (.step 19 (.run (.close 3)))))))) (.step 3 (.step 7 (.step 19 (.step 66 (.step 67 (.step 74 (.step 19 (.step 38 .point))))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part14
namespace Part15
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582725106862932750327987969825813665638203742725676240020156477489167991036149025554405274496498519322323517839564622543996022158691085636156981589509224267776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 11 (.split 30 0 (.split 36 0 (.step 3 (.step 15 (.run (.close 69)))) (.step 3 (.step 37 (.step 69 (.run (.close 74)))))) (.step 3 (.run (.close 17))))) (.step 3 (.step 23 (.step 3 (.step 17 (.run (.close 37))))))) (.step 3 (.step 11 (.split 30 0 (.step 3 (.run (.close 17))) (.step 3 (.run (.close 7))))))) (.step 11 (.split 34 0 (.split 35 0 (.step 7 (.step 3 (.run (.close 17)))) (.step 3 (.run (.close 17)))) (.step 3 (.step 7 (.step 3 (.run (.close 17)))))))) (.step 11 (.split 17 0 (.step 67 (.step 3 (.step 7 (.step 3 (.run (.close 17)))))) (.step 17 (.step 3 (.run (.close 7))))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 66 (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.step 7 (.step 3 (.run (.close 17)))))) (.step 3 (.step 11 (.step 17 (.run (.close 7)))))))) (.step 11 (.step 17 (.run (.close 7))))) (.step 77 (.step 11 (.step 23 (.split 10 0 (.split 34 0 (.split 16 0 (.step 75 (.step 3 (.step 17 (.run (.close 74))))) (.step 3 (.step 17 (.run (.close 38))))) (.step 3 (.step 37 (.step 66 (.run (.close 74)))))) (.step 3 (.run (.close 66)))))))) (.step 11 (.step 17 (.step 74 (.run (.close 3)))))) (.step 3 (.step 23 (.step 11 (.step 17 (.step 3 (.run (.close 7)))))))) (.step 3 (.step 17 (.step 42 (.step 61 (.run (.close 74))))))) (.step 11 (.step 17 (.step 67 (.run (.close 3)))))) (.step 11 (.step 17 (.step 66 (.step 3 (.run (.close 17)))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part15
namespace Part16
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460183827084136443896789531466851308460946267023810258800930402015142566826945994187336382264144254782668800⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Enumeration.Proof 1 := (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.reuse 0) (.step 3 (.step 23 (.step 51 (.step 61 (.step 3 (.step 7 (.run (.close 11))))))))) (.step 3 (.step 11 (.step 3 (.step 7 (.run (.close 27))))))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 69 (.step 74 (.step 77 (.step 3 (.split 10 0 (.split 16 0 (.step 29 (.step 40 (.step 77 (.step 7 (.run (.close 37)))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))))))))) (.step 3 (.step 7 (.step 66 (.step 67 (.step 74 (.step 75 (.split 42 1 (.split 10 0 (.split 16 0 (.split 17 0 (.step 29 (.step 40 (.step 77 (.step 7 (.step 37 (.run (.close 45))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 7 (.split 35 0 (.step 37 (.step 75 (.step 37 (.step 77 .point)))) (.step 37 (.step 39 (.step 45 (.run (.close 77))))))))))))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 75 (.split 36 1 (.step 77 (.split 42 1 (.split 10 0 (.split 16 0 (.step 29 (.step 40 (.split 34 0 (.split 30 0 (.split 17 0 (.split 36 0 (.step 69 (.step 75 (.step 3 (.step 38 (.run (.close 77)))))) (.step 3 (.step 38 (.run (.close 74))))) (.step 3 (.step 17 (.run (.close 74))))) (.step 3 (.step 17 (.run (.close 38))))) (.step 3 (.step 38 (.run (.close 17))))))) (.step 3 (.step 17 (.run (.close 38))))) (.step 3 (.step 17 (.run (.close 38))))) (.step 3 (.step 37 (.run (.close 38)))))) (.step 3 (.run (.close 38))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part16
namespace Part17
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473033502977723661785901632405372928⟩
def references : Fin 1 → Box := ![Part16.root]
def proof : Enumeration.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 3 (.step 7 (.step 66 (.step 67 (.step 74 (.step 75 (.split 35 1 (.split 36 1 (.split 42 1 (.step 17 (.step 3 (.step 7 (.step 37 (.run (.close 17)))))) (.step 7 (.step 37 (.step 75 (.step 17 (.step 37 .point)))))) (.step 7 (.step 37 (.step 74 (.step 37 (.step 17 .point)))))) (.step 3 (.step 17 (.step 37 (.step 17 (.run (.close 38)))))))))))))) (.step 3 (.step 7 (.step 67 (.split 63 1 (.split 71 1 (.step 7 (.step 11 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 77 (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.run (.close 17)))) (.step 3 (.step 17 (.run (.close 66))))))))) (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.run (.close 17)))))))) (.step 7 (.step 11 (.step 17 (.step 7 (.step 17 (.run (.close 20)))))))) (.step 7 (.step 11 (.step 17 (.step 19 (.step 3 (.run (.close 17))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part17
namespace Part18
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901536886895473034770628323890015303129108578304⟩
def references : Fin 5 → Box := ![Part8.root, Part10.root, Part12.root, Part14.root, Part17.root]
def proof : Enumeration.Proof 5 := (.split 10 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.reuse 0) (.step 3 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.split 72 1 (.step 7 (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 67))))) (.step 3 (.run (.close 67)))) (.step 3 (.step 67 (.step 3 (.run (.close 66)))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.step 7 (.step 38 (.step 3 (.run (.close 7))))))) (.step 3 (.run (.close 7)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.split 72 1 (.step 7 (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 66))))) (.step 3 (.step 66 (.step 3 (.run (.close 67)))))) (.step 3 (.step 66 (.run (.close 3))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.step 7 (.step 66 (.split 64 1 (.split 71 1 (.step 7 (.step 29 (.split 16 0 (.split 22 0 (.step 38 (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.run (.close 38)))) (.step 3 (.step 38 (.run (.close 66))))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.step 7 (.step 17 (.step 3 (.run (.close 7)))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.covered
  · exact Part10.covered
  · exact Part12.covered
  · exact Part14.covered
  · exact Part17.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part18
theorem covered : Enumeration.Covers points 11 families root := Part18.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families 11 header := rfl
end Core
namespace Lift0
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 58) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 58) root :=
  Fast.check_sound 14 (Enumeration.families 58) (Enumeration.families_valid 58)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 58) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 58) root :=
  Fast.check_sound 14 (Enumeration.families 58) (Enumeration.families_valid 58)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 58) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 58) root :=
  Fast.check_sound 14 (Enumeration.families 58) (Enumeration.families_valid 58)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
namespace Lift3
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797498561161601720831629746784392225796814106738090890859931077209253557225549206701564962646976646339454285381632, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 11 (.step 15 (.step 17 (.step 23 (.run (.close 31))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 58) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 58) root :=
  Fast.check_sound 14 (Enumeration.families 58) (Enumeration.families_valid 58)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift3
namespace Lift4
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797496212621258691740579661514352878740355175333663628037295019453182014117487883964301659893359139064022860562432, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 11 (.step 15 (.step 17 (.step 23 (.run (.close 31))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 58) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 58) root :=
  Fast.check_sound 14 (Enumeration.families 58) (Enumeration.families_valid 58)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift4
namespace Lift5
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396464775278045821939237254118739763343628413849368246381508361094747092391044822812881046351507037498938387858753069337050278264832, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 11 (.step 15 (.step 17 (.step 23 (.run (.close 31))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 58) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 58) root :=
  Fast.check_sound 14 (Enumeration.families 58) (Enumeration.families_valid 58)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift5
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 58) (CoreExtension.extension 58 p) := by
  exact List.forall_mem_cons.mpr ⟨(by simpa only [Lift0.root, upper_eq, CoreExtension.extension] using Lift0.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift1.root, upper_eq, CoreExtension.extension] using Lift1.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift2.root, upper_eq, CoreExtension.extension] using Lift2.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift3.root, upper_eq, CoreExtension.extension] using Lift3.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift4.root, upper_eq, CoreExtension.extension] using Lift4.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift5.root, upper_eq, CoreExtension.extension] using Lift5.excludes),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 58) (Archive.root 58) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 58)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case171
