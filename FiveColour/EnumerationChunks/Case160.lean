module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case160
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168169420385382274271979204042031104⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32016031753816174816247, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859360537049889235969407502623246962523112449, 0⟩]
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
def root : Box := ⟨2147483648, 5515652268243860120477985486598169856314825191138241325747871086031027321906045293217139789486325657918887818555530405535821492432195100097777675046622406600251565971199975115300130584084710192691137135989603094757376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 10 0 (.split 12 0 (.split 22 0 (.split 30 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 61 0 (.step 9 (.step 7 (.close 22))) (.step 52 (.step 9 (.step 7 (.close 22))))) (.step 7 (.step 9 (.step 21 (.close 22))))) (.split 35 0 (.step 7 (.step 9 (.close 15))) (.step 7 (.close 15)))) (.step 63 (.split 34 0 (.step 7 (.step 4 (.close 9))) (.step 7 (.close 4))))) (.step 7 (.step 9 (.step 22 (.close 52))))) (.step 7 (.step 4 (.close 27)))) (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 42 0 (.step 9 (.split 61 0 (.step 71 (.step 16 (.close 7))) (.step 15 (.step 7 (.close 22))))) (.step 7 (.step 9 (.step 15 (.close 16))))) (.step 7 (.step 9 (.step 15 (.step 7 (.step 16 (.close 21))))))) (.step 7 (.step 15 (.step 7 (.close 9))))) (.step 7 (.close 4))) (.step 7 (.step 9 (.step 18 (.step 15 (.step 7 (.close 4)))))))) (.step 7 (.step 52 (.close 9)))) (.step 7 (.step 18 (.step 4 (.close 27))))) (.step 7 (.step 18 (.step 4 (.close 27))))))
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
def root : Box := ⟨2147483648, 11031304536482698885562547197194112834423063950174857392339646204413516153733319857776542781775511722586255184008216891876080097358734371724180907507659229826338941979911553154629924278593568408835509632306949103026176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 69 1 (.split 72 1 (.reuse 0) (.run (.split 10 0 (.split 12 0 (.step 7 (.split 16 0 (.split 17 0 (.step 9 (.step 18 (.step 26 (.step 68 (.step 71 (.close 7)))))) (.step 7 (.step 4 (.close 18)))) (.step 7 (.step 4 (.close 18))))) (.split 21 0 (.split 30 0 (.step 26 (.split 34 0 (.step 26 (.step 9 (.step 15 (.step 7 (.step 18 (.step 16 (.step 21 (.close 22)))))))) (.step 7 (.close 15)))) (.step 7 (.step 9 (.step 15 (.step 7 (.step 16 (.close 18))))))) (.step 9 (.step 15 (.step 18 (.close 4)))))) (.step 7 (.step 9 (.close 15)))))) (.run (.split 72 1 (.split 12 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 43 0 (.split 34 0 (.step 72 (.close 7)) (.step 22 (.step 7 (.close 15)))) (.step 10 (.step 52 (.close 53)))) (.step 10 (.step 22 (.step 57 (.close 7))))) (.step 7 (.step 53 (.close 9)))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.step 7 (.step 4 (.step 7 (.step 9 (.close 22)))))) (.step 7 (.step 52 (.close 9)))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 64 (.step 10 (.step 22 (.step 7 (.step 31 (.step 21 (.close 26))))))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7)))) (.step 4 (.step 57 (.close 71))))))
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
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 11031304536487720240955970973196335463521655586841957786504911440018864431493121431666867092157404200652664389845661957499105107686104440381448559095426617793685743054488503627832598186024333160249697203428410735460352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 12 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 43 0 (.split 35 0 (.step 65 (.close 7)) (.step 21 (.step 22 (.close 26)))) (.step 10 (.step 52 (.close 53)))) (.step 10 (.step 64 (.step 7 (.step 16 (.step 7 (.close 21))))))) (.step 7 (.close 53))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.step 7 (.step 4 (.step 7 (.step 9 (.close 22)))))) (.step 7 (.step 52 (.close 9)))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 64 (.step 10 (.step 21 (.step 65 (.close 7))))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7)))) (.step 4 (.step 71 (.close 15)))) (.split 72 1 (.step 72 (.step 7 (.step 4 (.step 7 (.close 16))))) (.step 4 (.step 10 (.step 21 (.step 4 (.step 22 (.step 57 (.close 65))))))))) (.step 63 (.step 65 (.close 71)))) (.step 65 (.step 70 (.step 7 (.close 15))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 11031304536487720240955970973196339712625598120978747303210563859767883068238063247922252687710509803881143276663603870799123229520389791496084449067434740566320444276146418903992428318723148710899863886574162989285376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 12 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 43 0 (.split 49 0 (.step 71 (.step 21 (.close 22))) (.step 52 (.close 7))) (.step 10 (.step 52 (.close 53)))) (.step 10 (.step 15 (.step 7 (.close 22))))) (.step 7 (.step 52 (.step 9 (.step 10 (.step 22 (.close 53))))))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.step 7 (.step 4 (.step 7 (.step 9 (.close 22)))))) (.step 7 (.close 52))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.step 7 (.step 4 (.step 27 (.close 36))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 64 (.close 7)) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.close 7)))) (.step 4 (.step 15 (.close 71)))) (.split 72 1 (.step 72 (.step 7 (.step 4 (.step 7 (.close 15))))) (.step 4 (.step 10 (.step 22 (.step 4 (.step 15 (.step 57 (.close 64))))))))) (.step 63 (.step 64 (.step 9 (.step 15 (.step 21 (.step 26 (.step 38 (.close 64))))))))) (.step 64 (.step 70 (.step 7 (.close 15))))) (.step 64 (.split 72 1 (.split 21 0 (.split 30 0 (.split 36 0 (.step 64 (.step 4 (.close 5))) (.step 7 (.step 10 (.close 64)))) (.step 7 (.step 53 (.close 15)))) (.step 7 (.step 10 (.step 18 (.step 4 (.step 31 (.step 22 (.close 26)))))))) (.step 4 (.step 10 (.step 21 (.step 4 (.step 15 (.close 64))))))))))
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
def root : Box := ⟨8104522595470689372094546608771799123071184047348509570304018222052056272290836223436927829974812098219136497287696853871865529444163623648216552410378835326291370709770720772096, 11031304536487720240955970973191984381088552892067228024602880890328166304234237178175691500562418503801310316409288156392266813292892305043406796007752747042687624841505342651990650578642398712142159347532987105280000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 10 0 (.step 62 (.split 12 0 (.split 17 0 (.split 30 0 (.step 9 (.step 4 (.step 7 (.close 21)))) (.step 7 (.close 9))) (.step 7 (.close 4))) (.step 9 (.step 26 (.step 7 (.close 15)))))) (.step 18 (.step 7 (.step 52 (.step 9 (.close 15)))))) (.step 18 (.step 7 (.step 27 (.step 4 (.close 36)))))) (.step 9 (.step 26 (.close 7)))) (.step 26 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 61 0 (.step 62 (.step 72 (.close 4))) (.step 52 (.split 16 0 (.step 62 (.step 64 (.close 72))) (.step 4 (.step 7 (.step 27 (.close 36))))))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 26 (.step 15 (.step 16 (.close 52))))))))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 26 (.step 15 (.step 16 (.close 52))))))))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 15 (.step 16 (.close 26)))))))) (.step 7 (.step 53 (.step 57 (.step 9 (.close 52)))))) (.step 7 (.step 52 (.step 57 (.step 9 (.close 53)))))))) (.step 18 (.step 26 (.step 62 (.step 15 (.close 21)))))) (.step 26 (.step 62 (.step 7 (.step 26 (.step 44 (.close 70))))))))
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
def root : Box := ⟨8104522595470689372094546608771799123071184047348509570304018222052056272290836223436927829974812098219136497287696853871865529444163623648216552410378835326291370709770720772096, 11031304536487720240955970973196339712629650382276482647896611133072268967799598839945926942495661812992169304799749288910841693435377197545194017316078588993256377040868500715816536594928338128563009571929047275929600⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 61 1 (.split 62 1 (.reuse 0) (.run (.step 26 (.step 53 (.step 70 (.step 71 (.step 72 (.split 10 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 61 0 (.step 62 (.step 4 (.close 7))) (.step 52 (.step 64 (.step 65 (.close 4))))) (.step 4 (.step 7 (.step 9 (.step 26 (.step 15 (.step 16 (.close 22)))))))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 15 (.step 16 (.close 26)))))))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 16 (.close 22))))))) (.step 7 (.step 52 (.step 9 (.close 15)))))))))))) (.run (.step 26 (.step 70 (.step 71 (.split 62 1 (.step 52 (.split 69 1 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 62 0 (.step 62 (.split 12 0 (.step 62 (.step 4 (.close 7))) (.step 4 (.step 9 (.close 15))))) (.step 53 (.step 64 (.close 4)))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 22 (.close 26))))))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 22 (.close 26))))))) (.step 4 (.step 7 (.step 9 (.step 15 (.close 22)))))) (.step 7 (.step 53 (.step 9 (.close 15))))) (.step 64 (.close 21)))) (.step 64 (.close 21))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384264315699200, 11031304536487720240955970973191984381084500630769492683515964652658337510921132392300802732873024189331817594753747196370018413915095195249529776642221584335688420583599976938733155146832649045685825806870233902743552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 61 0 (.split 62 0 (.split 68 0 (.split 10 0 (.step 57 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 4 (.step 9 (.step 16 (.close 22)))))) (.step 54 (.step 21 (.step 5 (.step 9 (.step 53 (.step 7 (.close 16)))))))) (.step 15 (.step 4 (.step 52 (.step 9 (.step 54 (.step 7 (.close 26)))))))) (.step 7 (.step 9 (.step 22 (.step 31 (.step 7 (.step 15 (.step 16 (.close 26))))))))) (.step 57 (.close 7))) (.step 15 (.step 7 (.step 9 (.step 31 (.step 7 (.step 16 (.step 7 (.close 21))))))))) (.step 18 (.step 9 (.close 57)))) (.step 9 (.step 26 (.step 57 (.step 4 (.close 7)))))) (.step 4 (.step 22 (.step 57 (.close 7))))) (.step 4 (.step 9 (.step 57 (.close 71))))) (.step 57 (.step 72 (.split 68 1 (.split 10 0 (.split 16 0 (.step 26 (.split 21 0 (.split 30 0 (.step 57 (.step 4 (.close 9))) (.step 7 (.step 53 (.step 9 (.close 15))))) (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 7 (.step 9 (.close 21))))) (.step 7 (.step 15 (.step 26 (.step 52 (.close 9)))))) (.step 4 (.step 7 (.step 9 (.step 26 (.step 54 (.step 57 (.close 52))))))))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742168706826074048029646094712429591419507633702611280353747000311757972567493800426566199191274713193105547685216814383149439323777879769821716621178360037376⟩
def references : Fin 5 → Box := ![Part1.root, Part2.root, Part3.root, Part5.root, Part6.root]
def proof : Chunks.Proof 5 := (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.reuse 0) (.run (.split 12 0 (.step 71 (.step 7 (.step 18 (.step 63 (.close 71))))) (.step 4 (.step 71 (.step 9 (.step 15 (.step 18 (.step 16 (.step 26 (.step 16 (.close 21)))))))))))) (.run (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 35 0 (.step 70 (.split 10 0 (.step 70 (.step 4 (.step 7 (.step 15 (.close 16))))) (.step 7 (.step 15 (.close 26))))) (.step 7 (.step 9 (.step 26 (.step 53 (.step 15 (.step 16 (.close 22)))))))) (.step 7 (.step 9 (.step 4 (.close 22))))) (.step 7 (.step 9 (.step 26 (.close 70))))) (.step 70 (.step 7 (.close 15)))) (.step 7 (.step 70 (.close 71)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 59 1 (.split 61 1 (.split 62 1 (.reuse 4) (.run (.step 4 (.step 21 (.step 4 (.step 57 (.step 71 (.step 72 (.split 67 1 (.split 10 0 (.step 57 (.step 9 (.step 7 (.step 15 (.close 26))))) (.step 7 (.step 10 (.step 15 (.step 7 (.step 52 (.close 22))))))) (.step 10 (.step 26 (.step 53 (.step 54 (.step 57 (.close 7))))))))))))))) (.run (.step 4 (.step 71 (.split 62 1 (.split 67 1 (.split 69 1 (.step 4 (.step 15 (.step 57 (.split 10 0 (.step 57 (.step 9 (.step 7 (.close 26)))) (.step 7 (.step 10 (.step 31 (.close 52)))))))) (.step 10 (.step 22 (.step 4 (.step 15 (.step 57 (.close 7))))))) (.step 4 (.step 10 (.step 15 (.step 26 (.step 52 (.step 54 (.step 57 (.step 7 (.close 53)))))))))) (.step 10 (.step 21 (.step 64 (.step 4 (.step 26 (.close 7))))))))))) (.run (.step 9 (.step 26 (.step 57 (.step 62 (.close 64))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106659202662400, 11031304536487720240955970973196339712629650382276482651495742172062051447141575062858231868839708638655760708474495156220685410271104635115217984954543119347244866627344068045132222223771465839302349596282919139147776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 10 0 (.split 12 0 (.step 53 (.step 7 (.close 9))) (.step 9 (.split 22 0 (.step 21 (.split 61 0 (.split 68 0 (.step 53 (.step 5 (.close 7))) (.step 5 (.step 7 (.close 53)))) (.step 5 (.step 15 (.step 52 (.step 7 (.close 22))))))) (.step 18 (.close 4))))) (.step 18 (.step 7 (.step 52 (.step 9 (.close 15)))))) (.step 18 (.step 7 (.step 27 (.step 4 (.close 36)))))) (.step 18 (.step 7 (.step 21 (.step 27 (.close 36)))))) (.step 9 (.step 55 (.step 26 (.step 18 (.step 21 (.step 7 (.close 53)))))))) (.step 71 (.split 10 0 (.split 30 0 (.split 34 0 (.step 53 (.step 65 (.step 53 (.step 72 (.step 4 (.close 7)))))) (.step 4 (.step 7 (.step 9 (.step 22 (.step 15 (.step 16 (.close 26)))))))) (.step 7 (.close 53))) (.step 7 (.step 52 (.close 53)))))) (.step 18 (.step 53 (.step 15 (.close 57))))) (.step 53 (.step 7 (.step 9 (.step 27 (.close 52)))))) (.step 53 (.close 7))) (.step 65 (.step 52 (.step 70 (.step 71 (.split 69 1 (.split 30 0 (.split 34 0 (.step 53 (.step 65 (.step 53 (.split 12 0 (.split 17 0 (.step 64 (.step 4 (.close 7))) (.step 4 (.close 7))) (.step 4 (.step 9 (.close 15))))))) (.step 4 (.step 7 (.step 9 (.step 15 (.close 22)))))) (.step 7 (.close 53))) (.step 64 (.close 21)))))))) (.step 53 (.close 7))) (.step 9 (.step 21 (.step 53 (.step 57 (.close 53)))))) (.step 53 (.close 54))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304536487720240955970973191984381084500630769492679916833617023783601343217109728062180532829802892581374837640827211006829154631555374957779199103901809201229092561728502944010622819054233206109253382256459776000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 16 0 (.split 17 0 (.split 12 0 (.step 52 (.step 7 (.step 9 (.close 21)))) (.step 9 (.split 22 0 (.split 30 0 (.split 34 0 (.split 62 0 (.split 68 0 (.step 52 (.step 5 (.close 7))) (.step 16 (.step 18 (.step 16 (.close 22))))) (.step 16 (.step 21 (.step 4 (.step 16 (.close 52)))))) (.step 15 (.step 7 (.close 16)))) (.step 18 (.step 16 (.step 22 (.close 26))))) (.step 18 (.close 4))))) (.step 18 (.step 7 (.step 27 (.step 4 (.close 36)))))) (.step 18 (.step 7 (.step 27 (.step 4 (.close 36)))))) (.step 9 (.step 55 (.step 26 (.step 18 (.step 52 (.step 7 (.close 16)))))))) (.step 71 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 61 0 (.split 12 0 (.split 16 0 (.step 52 (.step 72 (.close 4))) (.step 4 (.step 7 (.step 27 (.close 36))))) (.step 4 (.step 9 (.step 16 (.step 22 (.close 26)))))) (.step 52 (.close 4))) (.step 4 (.step 7 (.step 9 (.step 16 (.step 22 (.step 26 (.close 52)))))))) (.step 4 (.step 7 (.step 9 (.step 16 (.step 22 (.step 26 (.close 52)))))))) (.step 4 (.step 7 (.step 9 (.step 16 (.step 22 (.close 26))))))) (.step 7 (.close 52))) (.step 7 (.close 52))))) (.step 18 (.step 52 (.step 16 (.step 21 (.close 57)))))) (.step 52 (.step 7 (.step 9 (.step 27 (.close 53)))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434276803595271946858057795038993245151143890047831291495878536394538122540694403643122535707909690544153310778029445187487072780288000⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 49 1 (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 54 1 (.step 70 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 35 0 (.step 54 (.step 7 (.step 9 (.step 22 (.step 26 (.step 15 (.step 16 (.close 52)))))))) (.step 7 (.step 9 (.step 22 (.step 53 (.step 15 (.step 16 (.close 26)))))))) (.step 7 (.step 9 (.step 4 (.close 22))))) (.step 7 (.step 9 (.step 22 (.step 26 (.close 54)))))) (.step 22 (.step 54 (.step 7 (.close 15))))) (.step 7 (.step 54 (.close 71)))) (.step 65 (.split 72 1 (.step 54 (.step 7 (.close 15))) (.step 4 (.step 7 (.step 10 (.step 21 (.step 22 (.step 26 (.step 53 (.close 54))))))))))) (.step 64 (.split 72 1 (.step 54 (.step 7 (.close 15))) (.step 4 (.step 7 (.step 10 (.step 15 (.step 22 (.step 26 (.step 52 (.step 53 (.close 54)))))))))))) (.step 54 (.step 62 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))))) (.step 22 (.step 57 (.close 54)))))) (.reuse 1)) (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.reuse 2) (.run (.step 53 (.step 70 (.step 71 (.step 64 (.step 65 (.split 16 0 (.step 52 (.split 17 0 (.step 65 (.step 4 (.close 7))) (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 27))))))))))) (.run (.step 52 (.step 64 (.step 52 (.step 4 (.close 7))))))) (.run (.step 52 (.close 7)))) (.run (.step 9 (.step 52 (.step 57 (.close 52)))))) (.run (.step 52 (.close 54)))) (.run (.step 52 (.close 7)))))
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
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991353375948800, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775634760222489937077505622052248734149581064040202605968330172676848182290800644805214904974011045554577368678400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.step 7 (.step 26 (.step 31 (.step 7 (.close 15))))) (.step 29 (.split 10 0 (.split 12 0 (.step 7 (.close 26)) (.step 26 (.close 7))) (.step 7 (.close 15))))) (.step 7 (.step 4 (.step 26 (.step 15 (.close 21)))))) (.step 4 (.step 7 (.step 26 (.step 15 (.step 31 (.step 15 (.close 21)))))))) (.step 7 (.step 26 (.step 31 (.step 41 (.step 15 (.step 26 (.step 15 (.step 39 (.close 57)))))))))) (.step 7 (.step 26 (.step 31 (.step 64 (.step 15 (.step 21 (.close 26)))))))) (.step 7 (.step 26 (.step 15 (.close 21))))) (.step 26 (.step 31 (.step 29 (.step 57 (.step 31 (.split 21 0 (.split 49 0 (.step 45 (.close 7)) (.step 7 (.step 26 (.step 15 (.close 21))))) (.step 7 (.close 15))))))))) (.step 7 (.step 26 (.step 55 (.step 9 (.step 53 (.step 18 (.step 38 (.step 45 (.step 18 (.step 26 (.step 15 (.step 52 (.close 53)))))))))))))) (.step 7 (.step 26 (.step 55 (.step 9 (.step 52 (.step 18 (.step 45 (.step 18 (.step 26 (.step 37 (.step 21 (.step 15 (.close 52))))))))))))))))
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
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775634760222489937077505622052248734149581064040202605968330172676848182290800644805214904974011045554577368678400⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 70 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 35 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 49 0 (.split 50 0 (.split 61 0 (.step 29 (.close 10)) (.split 62 0 (.step 10 (.close 7)) (.step 10 (.close 7)))) (.step 46 (.close 7))) (.split 50 0 (.step 46 (.close 7)) (.step 9 (.close 46)))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 7 (.close 27))) (.step 7 (.close 46))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 10 (.step 30 (.step 10 (.close 46))))) (.step 7 (.step 9 (.close 46)))) (.step 10 (.step 30 (.step 10 (.step 46 (.step 7 (.step 52 (.step 53 (.close 65))))))))) (.step 10 (.step 30 (.step 10 (.step 46 (.step 7 (.step 52 (.step 53 (.close 64))))))))) (.step 9 (.step 27 (.close 46))))) (.step 9 (.step 10 (.step 7 (.step 27 (.step 10 (.close 7))))))) (.step 46 (.step 54 (.step 7 (.close 9))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.step 46 (.close 52))))))) (.reuse 1))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404237493564800576407533357227799741497031882949738789004315842677511864567039135128106881121069659446362913487514740252367313174528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.step 7 (.step 40 (.step 57 (.step 7 (.close 15))))) (.step 29 (.split 10 0 (.split 12 0 (.step 7 (.step 26 (.step 7 (.step 4 (.step 15 (.close 21)))))) (.step 31 (.step 37 (.step 7 (.close 21))))) (.step 7 (.close 15))))) (.step 7 (.step 4 (.step 31 (.step 15 (.step 26 (.step 15 (.close 21)))))))) (.step 4 (.step 7 (.step 31 (.close 39))))) (.step 7 (.step 31 (.step 39 (.step 15 (.step 21 (.step 26 (.step 39 (.close 57))))))))) (.step 7 (.step 31 (.step 39 (.step 41 (.step 64 (.step 15 (.close 26)))))))) (.step 7 (.step 26 (.step 15 (.close 21))))) (.step 31 (.step 29 (.step 57 (.close 7))))) (.step 7 (.step 57 (.step 7 (.step 37 (.step 26 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52))))))))))) (.step 7 (.step 57 (.step 58 (.split 72 1 (.step 55 (.step 9 (.close 52))) (.step 7 (.step 26 (.step 15 (.close 21))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304536487720240955970973196339712629650382276482651495742172058778056533678920988218679142881039503544066430745590047192190414619322214115397340456414244087243593930770200391585028850733390826482756339716298113024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 72 1 (.step 9 (.split 34 0 (.step 21 (.step 7 (.split 36 0 (.step 7 (.step 57 (.close 15))) (.step 7 (.close 15))))) (.step 15 (.step 7 (.step 21 (.close 7)))))) (.step 29 (.step 75 (.close 21)))) (.step 7 (.step 29 (.step 40 (.step 7 (.close 15)))))) (.step 9 (.step 18 (.step 21 (.step 18 (.step 4 (.step 26 (.step 4 (.close 15))))))))) (.step 18 (.step 40 (.step 7 (.step 29 (.step 40 (.step 7 (.close 15)))))))) (.step 18 (.step 40 (.split 72 1 (.step 18 (.close 7)) (.step 29 (.step 38 (.close 4))))))) (.step 7 (.step 18 (.step 29 (.split 12 0 (.step 7 (.step 15 (.step 18 (.close 21)))) (.step 15 (.close 7))))))) (.step 4 (.step 57 (.close 71)))) (.step 4 (.step 29 (.step 71 (.step 15 (.close 26)))))) (.step 7 (.step 26 (.step 53 (.step 9 (.step 71 (.close 38))))))) (.step 4 (.step 21 (.step 4 (.step 53 (.step 71 (.close 10))))))) (.step 4 (.step 63 (.step 15 (.step 71 (.step 10 (.step 22 (.close 53)))))))) (.step 9 (.step 21 (.step 26 (.step 71 (.step 75 (.step 53 (.step 18 (.step 26 (.step 62 (.close 7))))))))))) (.step 9 (.step 21 (.step 57 (.step 7 (.step 4 (.step 18 (.close 26)))))))) (.step 22 (.step 53 (.step 57 (.step 7 (.step 53 (.step 9 (.step 62 (.step 54 (.step 26 (.step 38 (.step 15 (.step 52 (.step 54 (.step 38 (.close 70)))))))))))))))))
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
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775634762515988553067577133663069629451668004836767595136611296414437021677723520893699713044029598664703055233024⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 9 (.step 21 (.step 38 (.step 18 (.step 21 (.close 26)))))))) (.run (.step 9 (.step 21 (.step 53 (.step 57 (.step 62 (.step 71 (.split 51 1 (.split 67 1 (.split 72 1 (.step 53 (.step 18 (.split 34 0 (.split 68 0 (.step 52 (.step 7 (.close 26))) (.step 16 (.step 7 (.close 52)))) (.step 15 (.step 7 (.close 26)))))) (.step 21 (.step 26 (.step 18 (.step 38 (.close 22)))))) (.step 7 (.step 21 (.step 26 (.close 52))))) (.step 7 (.step 22 (.close 52)))))))))))) (.run (.step 9 (.step 7 (.close 10))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 41 (.split 61 1 (.step 29 (.split 68 1 (.split 69 1 (.step 38 (.split 10 0 (.split 12 0 (.step 7 (.step 21 (.step 26 (.step 7 (.step 4 (.close 15)))))) (.step 31 (.step 37 (.step 7 (.close 21))))) (.step 7 (.close 15)))) (.step 4 (.step 7 (.step 21 (.step 26 (.step 15 (.close 31))))))) (.step 4 (.step 7 (.step 31 (.step 38 (.close 21))))))) (.step 4 (.step 7 (.step 15 (.step 21 (.step 26 (.step 31 (.step 38 (.step 39 (.close 64))))))))))) (.step 7 (.step 21 (.step 26 (.step 15 (.close 37)))))) (.step 9 (.step 21 (.step 26 (.step 31 (.close 38)))))) (.step 7 (.step 21 (.close 26)))) (.step 7 (.step 21 (.step 26 (.step 37 (.close 38)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111058571326900805023143666418788695380519316503456482003705408553886748635502143176743027983433406087168000⟩
def references : Fin 3 → Box := ![Part12.root, Part13.root, Part15.root]
def proof : Chunks.Proof 3 := (.split 35 1 (.split 36 1 (.reuse 0) (.step 7 (.split 42 1 (.reuse 1) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.step 39 (.split 62 1 (.split 69 1 (.split 12 0 (.step 7 (.step 26 (.step 39 (.step 4 (.close 7))))) (.step 29 (.step 31 (.step 37 (.step 7 (.close 21)))))) (.step 7 (.step 31 (.close 39)))) (.step 7 (.step 31 (.step 39 (.step 41 (.step 57 (.close 64)))))))) (.step 7 (.step 26 (.step 31 (.step 39 (.step 41 (.step 64 (.step 15 (.step 26 (.close 57)))))))))) (.step 7 (.step 26 (.step 39 (.step 37 (.step 21 (.close 26))))))) (.step 26 (.step 29 (.step 31 (.step 39 (.step 37 (.close 57))))))) (.step 7 (.step 26 (.step 38 (.step 57 (.step 15 (.step 37 (.step 45 (.step 52 (.close 53)))))))))) (.step 7 (.step 26 (.step 57 (.step 45 (.step 38 (.step 37 (.close 52)))))))))))) (.split 36 1 (.reuse 2) (.run (.step 7 (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 41 (.step 29 (.split 61 1 (.step 38 (.split 10 0 (.split 12 0 (.step 7 (.step 21 (.close 38))) (.step 31 (.step 37 (.step 7 (.close 21))))) (.step 7 (.close 15)))) (.step 4 (.step 7 (.step 15 (.step 21 (.step 31 (.step 26 (.close 38)))))))))) (.step 7 (.step 21 (.step 26 (.step 15 (.close 37)))))) (.step 7 (.step 21 (.close 26)))) (.step 7 (.step 21 (.step 37 (.step 26 (.close 38)))))) (.step 29 (.step 38 (.step 7 (.step 4 (.step 15 (.close 21))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404237493564800576407531008687456712405981797679699441947856911273084601744403077372035338013008336709099610733897232976935888355328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.split 68 1 (.split 69 1 (.split 72 1 (.step 7 (.step 15 (.step 31 (.step 7 (.close 21))))) (.step 29 (.split 10 0 (.split 12 0 (.step 7 (.step 15 (.step 26 (.step 7 (.step 4 (.close 21)))))) (.step 15 (.close 7))) (.step 7 (.close 15))))) (.step 7 (.step 4 (.step 15 (.step 21 (.step 26 (.step 21 (.close 31)))))))) (.step 4 (.step 7 (.step 31 (.step 37 (.close 21)))))) (.step 7 (.step 31 (.step 15 (.step 21 (.step 26 (.step 37 (.step 39 (.step 26 (.close 65)))))))))) (.step 7 (.step 15 (.step 31 (.step 15 (.close 64)))))) (.step 7 (.step 15 (.step 21 (.close 26))))) (.step 15 (.step 29 (.step 31 (.step 57 (.step 75 (.step 7 (.step 21 (.close 26))))))))) (.step 7 (.step 15 (.step 57 (.step 7 (.step 37 (.step 26 (.step 37 (.step 38 (.step 26 (.close 52))))))))))) (.step 7 (.step 15 (.step 52 (.step 7 (.step 26 (.step 52 (.step 26 (.close 37))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404240201250048741265792315732558414636160934825280863643731101194550045710523981303307837988014297782906346467501687472611502587904⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 37 (.split 69 1 (.split 12 0 (.step 7 (.step 15 (.step 26 (.step 31 (.step 7 (.close 21)))))) (.step 29 (.step 31 (.close 37)))) (.step 7 (.step 31 (.step 15 (.step 21 (.close 26))))))) (.step 7 (.step 26 (.step 31 (.step 37 (.step 41 (.step 64 (.step 39 (.step 26 (.close 65)))))))))) (.step 7 (.step 15 (.step 31 (.close 64))))) (.step 7 (.step 15 (.step 26 (.close 37))))) (.step 15 (.step 26 (.step 29 (.step 31 (.step 37 (.step 7 (.step 26 (.step 37 (.step 21 (.step 39 (.close 52)))))))))))) (.step 7 (.step 15 (.step 26 (.step 37 (.step 38 (.step 52 (.step 45 (.close 53))))))))) (.step 7 (.step 15 (.step 26 (.step 52 (.step 37 (.close 52)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨4591476721464498631642756675165310770149373269331031546544977656975773335919329938030798861206796734824448, 11031304536487715342072660315853902764779248980636878129263959546844141427910890695220404240201250048741265794666568639804459460335916698548282845417673663943198675812331868209583962288479834618236518625351440221077504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 15 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 41 (.step 29 (.split 68 1 (.split 69 1 (.step 38 (.split 10 0 (.split 12 0 (.step 7 (.step 15 (.step 21 (.step 31 (.step 7 (.close 26)))))) (.step 15 (.close 7))) (.step 7 (.close 15)))) (.step 4 (.step 7 (.step 15 (.step 21 (.step 31 (.step 26 (.close 37)))))))) (.step 4 (.step 7 (.step 31 (.step 37 (.step 21 (.close 38))))))))) (.step 7 (.step 15 (.step 21 (.step 26 (.close 37)))))) (.step 9 (.step 15 (.step 21 (.step 31 (.close 38)))))) (.step 7 (.step 15 (.step 21 (.close 26))))) (.step 7 (.step 15 (.step 21 (.step 37 (.step 26 (.close 38))))))) (.step 29 (.step 37 (.step 21 (.close 7))))) (.step 29 (.step 37 (.step 21 (.close 7)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244811554998574619695868897366901790430875013596117410043452853321728⟩
def references : Fin 3 → Box := ![Part16.root, Part18.root, Part19.root]
def proof : Chunks.Proof 3 := (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.split 35 1 (.split 36 1 (.reuse 1) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 61 1 (.step 39 (.split 62 1 (.split 69 1 (.split 12 0 (.step 7 (.step 15 (.close 37))) (.step 29 (.step 31 (.close 37)))) (.step 7 (.step 31 (.step 15 (.step 21 (.close 26)))))) (.step 7 (.step 31 (.step 37 (.step 39 (.step 15 (.close 64)))))))) (.step 7 (.step 15 (.step 31 (.step 37 (.close 64)))))) (.step 7 (.step 15 (.step 26 (.close 37))))) (.step 15 (.step 29 (.step 31 (.step 37 (.step 7 (.step 26 (.step 37 (.step 21 (.step 39 (.close 52))))))))))) (.step 7 (.step 15 (.step 37 (.step 26 (.step 38 (.step 45 (.step 52 (.step 39 (.step 45 (.step 26 (.close 53)))))))))))) (.step 7 (.step 15 (.step 37 (.step 52 (.step 37 (.close 52))))))))) (.reuse 2)))) (.run (.step 7 (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.step 18 (.step 15 (.close 31)))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 7 (.step 9 (.step 18 (.close 53))))))) (.step 7 (.step 18 (.step 53 (.step 7 (.step 9 (.step 18 (.close 52)))))))) (.step 7 (.step 18 (.close 7)))))))) (.run (.step 7 (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 18 (.step 63 (.close 64)))) (.step 4 (.step 5 (.step 4 (.close 18))))) (.step 7 (.step 18 (.step 26 (.step 7 (.step 18 (.close 7))))))) (.step 7 (.step 18 (.step 26 (.step 55 (.step 27 (.close 52))))))) (.step 4 (.step 5 (.step 4 (.step 18 (.close 7))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part18.excludes
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131940901911052336084347781379996331983043623316201930752⟩
def references : Fin 1 → Box := ![Part20.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.reuse 0) (.run (.step 18 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.split 62 1 (.step 18 (.step 4 (.split 67 1 (.step 4 (.split 69 1 (.split 72 1 (.step 68 (.step 4 (.close 9))) (.step 4 (.step 7 (.step 15 (.step 7 (.close 17)))))) (.step 4 (.close 7)))) (.step 7 (.step 26 (.step 4 (.step 9 (.close 10)))))))) (.step 4 (.step 21 (.step 31 (.step 5 (.step 10 (.step 63 (.step 68 (.step 5 (.step 7 (.close 22))))))))))) (.step 4 (.step 31 (.step 5 (.step 34 (.step 10 (.step 63 (.step 65 (.step 5 (.step 7 (.step 18 (.close 22)))))))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 26)))))) (.step 4 (.step 9 (.step 18 (.close 57))))) (.step 4 (.step 7 (.step 22 (.close 54))))) (.step 4 (.step 9 (.step 18 (.close 53))))) (.step 4 (.step 9 (.step 18 (.close 52))))) (.step 4 (.step 7 (.step 9 (.close 10))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 4 (.step 15 (.close 26)))))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 31 (.step 26 (.close 39)))))))) (.step 4 (.step 7 (.step 9 (.step 18 (.close 38)))))) (.step 4 (.step 7 (.step 4 (.step 24 (.step 31 (.step 15 (.step 37 (.close 38))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600259838940156949866173138770647058481152⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 22 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 18 (.step 63 (.close 64)))) (.step 4 (.step 5 (.step 4 (.close 18))))) (.step 7 (.step 18 (.step 22 (.step 7 (.step 18 (.close 7))))))) (.step 7 (.step 18 (.step 22 (.step 55 (.step 27 (.close 52))))))) (.step 4 (.step 5 (.step 4 (.step 18 (.close 7)))))) (.step 7 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.step 64 (.close 65))) (.step 7 (.close 53))) (.step 7 (.step 52 (.close 53))))))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 7 (.step 18 (.step 63 (.close 64)))) (.step 4 (.step 5 (.step 4 (.close 18))))) (.step 7 (.step 18 (.step 21 (.step 7 (.step 18 (.close 7))))))) (.step 7 (.step 18 (.step 21 (.step 42 (.step 53 (.step 7 (.step 18 (.close 7))))))))) (.step 4 (.step 5 (.step 4 (.step 18 (.close 7)))))) (.step 7 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.step 64 (.close 65))) (.step 7 (.close 53))) (.step 7 (.step 52 (.close 53))))))) (.step 7 (.step 18 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.step 19 (.step 20 (.step 64 (.close 65))))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 53)))) (.step 7 (.step 19 (.step 25 (.step 52 (.close 53))))))) (.step 5 (.step 7 (.step 18 (.close 19))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196335463521655586841957786504911440018864431493121431666867092157404200652664389845661957499105107686104440381448559095426617793685743054488503627832599515252328945165570107235471015804928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 62 1 (.split 67 1 (.split 68 1 (.split 69 1 (.split 72 1 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 61 0 (.split 62 0 (.split 68 0 (.split 69 0 (.step 7 (.step 9 (.step 7 (.close 15)))) (.step 57 (.step 4 (.close 7)))) (.step 7 (.step 4 (.step 9 (.close 15))))) (.split 10 0 (.step 53 (.step 4 (.step 9 (.close 15)))) (.step 4 (.step 7 (.step 9 (.close 15)))))) (.step 15 (.step 4 (.close 7)))) (.step 7 (.step 9 (.close 15)))) (.step 15 (.step 7 (.close 9)))) (.step 15 (.step 4 (.close 7)))) (.step 15 (.step 4 (.close 7)))) (.step 9 (.step 15 (.step 4 (.close 7))))) (.step 4 (.step 15 (.step 16 (.step 22 (.step 9 (.step 15 (.close 7)))))))) (.step 4 (.step 9 (.step 15 (.close 71))))) (.step 15 (.split 68 1 (.split 69 1 (.split 10 0 (.split 16 0 (.step 26 (.split 17 0 (.split 21 0 (.split 34 0 (.step 70 (.step 7 (.close 15))) (.step 7 (.step 9 (.close 15)))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 9))))) (.step 4 (.step 7 (.step 9 (.close 15))))) (.step 7 (.step 15 (.close 10)))) (.step 4 (.step 10 (.step 16 (.step 22 (.step 15 (.step 7 (.step 15 (.close 26))))))))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 16 (.step 26 (.step 22 (.close 53))))))))))) (.step 4 (.step 16 (.step 21 (.step 4 (.step 15 (.step 10 (.step 64 (.step 71 (.step 72 (.split 67 1 (.step 15 (.step 7 (.step 15 (.close 22)))) (.step 26 (.step 53 (.close 15)))))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨2658455991569831745807614122708172800, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093243126558331877704708702208923964392741768476985581528070444158025728⟩
def references : Fin 1 → Box := ![Part23.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 61 1 (.reuse 0) (.run (.step 4 (.step 15 (.step 16 (.step 64 (.step 4 (.step 15 (.close 10))))))))) (.run (.step 9 (.step 15 (.step 26 (.step 62 (.close 65))))))) (.run (.step 9 (.step 15 (.close 4))))) (.run (.step 15 (.step 22 (.step 57 (.step 62 (.step 64 (.step 70 (.split 68 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 22 (.split 62 1 (.step 15 (.close 54)) (.step 10 (.step 15 (.step 16 (.step 15 (.step 7 (.close 26)))))))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 9)))) (.step 4 (.step 7 (.step 9 (.step 15 (.step 16 (.step 26 (.close 53)))))))))))))))) (.run (.step 9 (.step 15 (.step 21 (.close 53)))))) (.run (.step 9 (.step 15 (.step 16 (.close 52)))))) (.run (.step 9 (.step 10 (.step 27 (.step 10 (.close 46))))))) (.run (.step 7 (.step 15 (.step 26 (.step 31 (.step 29 (.split 10 0 (.split 16 0 (.step 15 (.close 7)) (.step 7 (.close 15))) (.step 7 (.close 15)))))))))) (.run (.step 7 (.step 15 (.step 31 (.step 29 (.step 57 (.step 37 (.step 7 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26)))))))))))))) (.run (.step 9 (.step 15 (.step 21 (.step 15 (.close 38))))))) (.run (.step 7 (.step 15 (.step 7 (.close 15)))))) (.run (.step 7 (.step 15 (.step 18 (.step 15 (.step 31 (.step 15 (.step 16 (.close 52))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2147483648, 11031304536487720240955970973196339712629650382276482651495742172062054643812090586434279578972651315837775637111060811071642984864390200195555350093244813200503131942399950230600261168169420385382274271979204042031104⟩
def references : Fin 2 → Box := ![Part22.root, Part24.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.reuse 1) (.run (.step 4 (.step 5 (.step 4 (.step 7 (.step 15 (.step 18 (.step 15 (.close 26)))))))))) (.run (.step 4 (.step 7 (.step 9 (.step 15 (.close 7))))))) (.run (.step 4 (.step 5 (.step 7 (.step 18 (.step 15 (.close 22)))))))) (.run (.step 4 (.step 5 (.step 7 (.step 18 (.step 15 (.close 21))))))))) (.run (.step 7 (.step 18 (.split 12 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 7 (.step 18 (.step 15 (.step 16 (.close 31))))) (.step 7 (.step 18 (.close 7)))) (.step 7 (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18)))))))) (.step 7 (.step 18 (.step 52 (.close 7))))) (.step 7 (.step 18 (.close 7)))) (.step 15 (.step 7 (.close 16))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part25

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part25.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case160

namespace FiveColour.Packed.EnumerationChunks.Projected.Case160
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 47 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 47 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 47 0).upper i := by decide +kernel
lemma budget_model : (⟨32016031753816174816247, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859360537049889235969407502623246962523112449, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 47), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32016031753816174816247, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859360537049889235969407502623246962523112449, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 47) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 47 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 47 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 47) (Archive.root 47) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 47 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 47 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case160

namespace FiveColour.Packed.EnumerationChunks.Case160
def root : Box := Archive.root 47
def families : Fin 78 → List Cut := Enumeration.families 47
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case160.original_covered points
end FiveColour.Packed.EnumerationChunks.Case160
