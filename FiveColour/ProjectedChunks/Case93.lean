module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case93
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087064675018302608505394988439643462044672⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908127039438376985589, 5783586103091957813513448549065477704101332453097102403927030543402094319394108592887551773511915116652793239902302694320363413592187732277592161523456540874451485486766787986221277724849666005459465451175879706183626392577, 0⟩]
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
def root : Box := ⟨3221225472, 5515652263101992197612038864773350743462566775890767394370008915011218877801894671274203033914486895084061655970370187687930313911541865829839897521246514083826653087224640599029021558339434202835131662813216634830848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 11 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 58 (.step 3 (.step 26 (.step 31 (.close 12))))) (.step 3 (.step 4 (.step 12 (.close 18))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 12)))) (.split 12 0 (.step 3 (.step 18 (.step 22 (.step 26 (.step 21 (.close 31)))))) (.step 22 (.step 3 (.step 12 (.step 21 (.close 26))))))) (.split 12 0 (.split 16 0 (.split 17 0 (.step 31 (.step 18 (.close 21))) (.step 3 (.step 4 (.step 18 (.close 21))))) (.step 3 (.step 4 (.step 18 (.close 21))))) (.step 21 (.step 9 (.step 31 (.step 4 (.close 12))))))) (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.close 3)) (.step 3 (.step 16 (.close 21)))) (.step 3 (.step 7 (.step 16 (.close 21))))) (.step 3 (.step 7 (.step 16 (.close 21))))) (.step 29 (.step 31 (.step 3 (.close 12)))))) (.step 3 (.step 18 (.step 48 (.close 3))))) (.split 12 0 (.step 3 (.step 18 (.step 12 (.step 4 (.step 3 (.close 15)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.step 3 (.step 15 (.close 3)))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 4))))) (.split 11 0 (.step 3 (.step 18 (.step 12 (.step 3 (.close 15))))) (.step 3 (.close 4)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230379595797340204830138293440962015917874573043435949354140902174702650128528444637858315421373857220908745981007245147066316391190215359857033947067248290269354979437948043154949120⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.reuse 0) (.run (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 3 (.step 18 (.step 48 (.split 38 0 (.split 46 0 (.step 3 (.close 4)) (.step 4 (.step 3 (.close 12)))) (.step 3 (.step 4 (.step 12 (.step 15 (.close 16))))))))) (.step 4 (.close 3))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 4 (.step 24 (.step 3 (.step 4 (.close 3)))))))) (.run (.step 58 (.close 3)))) (.run (.step 48 (.split 11 0 (.step 48 (.close 3)) (.step 48 (.close 3)))))) (.run (.split 45 1 (.split 55 1 (.split 1 0 (.split 11 0 (.step 29 (.split 12 0 (.split 21 0 (.split 45 0 (.split 49 0 (.split 10 0 (.step 75 (.step 3 (.step 18 (.step 16 (.close 21))))) (.step 3 (.step 18 (.step 12 (.step 15 (.step 21 (.close 31))))))) (.step 18 (.step 26 (.close 31)))) (.step 26 (.step 31 (.step 18 (.close 21))))) (.step 18 (.step 4 (.step 26 (.step 16 (.close 21)))))) (.step 26 (.step 31 (.step 12 (.step 4 (.close 18))))))) (.step 18 (.step 4 (.step 12 (.close 31))))) (.step 18 (.step 29 (.step 40 (.step 4 (.close 31)))))) (.step 18 (.step 31 (.step 26 (.close 48))))) (.step 9 (.step 26 (.step 31 (.step 18 (.close 48)))))))) (.run (.step 3 (.step 7 (.step 3 (.step 12 (.close 18)))))))
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
def root : Box := ⟨7729075046034516689390703781863974688597854659412869997314470502903038284579120849072387533163845155924927232063004354354730157322085975311485817346934161497393964850872320, 16546956789305971693952805936977615282529194403429675353941027508486758466322997115713437697003526557605311822549273238684846545322323612094766633205097794086599367252168081366743789092857186991034854589947008537068544⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 69 (.split 72 1 (.split 45 1 (.split 1 0 (.split 10 0 (.split 12 0 (.split 55 1 (.split 11 0 (.split 21 0 (.split 16 0 (.split 17 0 (.split 35 0 (.split 43 0 (.step 60 (.close 3)) (.step 3 (.step 31 (.step 3 (.step 9 (.close 48)))))) (.step 31 (.step 18 (.step 21 (.step 26 (.step 21 (.close 48))))))) (.step 3 (.step 18 (.step 31 (.step 18 (.close 48)))))) (.step 3 (.step 18 (.step 31 (.step 18 (.step 21 (.close 48))))))) (.split 17 0 (.step 26 (.step 3 (.step 48 (.step 3 (.close 16))))) (.step 8 (.step 18 (.close 3))))) (.step 60 (.step 3 (.close 4)))) (.step 58 (.step 3 (.step 5 (.close 31))))) (.step 58 (.split 11 0 (.split 16 0 (.step 26 (.step 48 (.step 3 (.close 16)))) (.step 24 (.step 31 (.step 4 (.step 12 (.step 18 (.close 21))))))) (.step 12 (.step 24 (.close 60)))))) (.step 58 (.step 31 (.step 3 (.step 12 (.step 18 (.close 12))))))) (.step 58 (.split 10 0 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 12 0 (.step 60 (.step 3 (.close 4))) (.step 4 (.step 12 (.step 4 (.step 3 (.step 18 (.close 48))))))) (.step 3 (.step 4 (.step 12 (.close 21))))) (.step 3 (.step 4 (.step 22 (.step 12 (.close 21)))))) (.step 4 (.step 18 (.step 4 (.close 31))))) (.step 3 (.step 31 (.close 4)))) (.step 3 (.close 4))) (.step 4 (.step 3 (.step 24 (.close 48))))) (.step 3 (.close 4))))) (.step 48 (.step 3 (.close 12)))) (.step 26 (.step 31 (.step 4 (.step 12 (.step 4 (.close 18)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087302011879424, 16546956789305976592836116594320052230387700327672298490394547759665974608023595453862986365564909071095925100304265006985657495980391819621165590964543012733254138764189221972027988516409609320118297698139072148538368⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 57 1 (.split 59 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 11 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.split 21 0 (.split 10 0 (.split 22 0 (.split 30 0 (.step 31 (.step 3 (.close 48))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.step 12 (.close 31)))) (.step 3 (.step 22 (.step 4 (.close 31)))))) (.step 3 (.step 18 (.step 3 (.step 22 (.close 31)))))) (.step 3 (.step 18 (.step 3 (.close 31))))) (.step 10 (.step 22 (.step 31 (.step 3 (.step 12 (.step 3 (.step 21 (.close 48))))))))) (.step 3 (.step 43 (.step 31 (.step 24 (.close 18)))))) (.step 3 (.step 31 (.close 4)))) (.step 3 (.step 5 (.step 31 (.close 48))))) (.step 10 (.step 22 (.step 31 (.close 48))))) (.step 31 (.step 3 (.step 22 (.close 38))))) (.step 3 (.step 22 (.step 26 (.step 31 (.step 48 (.step 12 (.step 16 (.close 21))))))))) (.step 28 (.step 31 (.step 48 (.step 51 (.step 60 (.step 3 (.step 12 (.step 15 (.close 16))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 16546956789305976592836116594320052230387700327672298497592809830935088820520457066160557339756424460378991713265473923164597625054772412131630688730768384173127595777822654169161214205200488822531921987523334316753920⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 55 1 (.split 67 1 (.split 45 1 (.split 10 0 (.split 16 0 (.split 1 0 (.split 12 0 (.split 11 0 (.step 9 (.split 17 0 (.step 57 (.split 42 0 (.step 48 (.close 3)) (.step 26 (.step 3 (.step 31 (.close 48)))))) (.step 3 (.step 18 (.step 22 (.step 18 (.step 31 (.step 18 (.close 48))))))))) (.split 30 0 (.split 38 0 (.step 9 (.step 15 (.step 57 (.step 3 (.step 4 (.step 12 (.close 18))))))) (.step 3 (.step 4 (.step 12 (.step 15 (.step 21 (.close 22))))))) (.step 3 (.close 4)))) (.step 9 (.step 57 (.close 3)))) (.step 9 (.step 57 (.step 3 (.step 4 (.close 3)))))) (.step 21 (.step 3 (.step 18 (.step 31 (.step 4 (.step 12 (.close 18)))))))) (.step 31 (.step 9 (.step 15 (.step 3 (.step 4 (.step 12 (.close 18)))))))) (.step 9 (.step 48 (.step 3 (.close 12))))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 48 (.step 9 (.step 31 (.close 57)))))) (.step 9 (.step 26 (.step 57 (.step 3 (.step 4 (.step 18 (.close 16)))))))) (.step 3 (.step 9 (.step 26 (.step 57 (.step 48 (.close 3))))))) (.step 26 (.step 48 (.step 51 (.step 48 (.step 9 (.close 12))))))) (.step 3 (.step 10 (.step 22 (.step 31 (.step 48 (.step 51 (.step 3 (.step 12 (.close 57))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970105039749120, 16546956789305976592836116594320052230387700327672298497599839383739062564868598532578816686410908362126338458004693853746803621274571611929004189802805713637424347200687530567791227120912198665795997792493436135277568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 51 (.split 54 1 (.split 57 1 (.step 3 (.split 59 1 (.step 51 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 24 (.split 34 0 (.split 36 0 (.split 38 0 (.step 18 (.step 24 (.step 3 (.step 4 (.step 12 (.close 48)))))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 4 (.close 14))))) (.step 3 (.step 18 (.close 3)))) (.step 18 (.step 3 (.close 12)))) (.step 18 (.step 8 (.close 56)))) (.step 24 (.split 34 0 (.split 35 0 (.step 3 (.split 11 0 (.step 4 (.close 3)) (.step 12 (.step 4 (.close 3))))) (.step 4 (.close 12))) (.step 3 (.close 4))))) (.step 24 (.step 3 (.step 18 (.close 4))))) (.step 18 (.step 3 (.step 4 (.step 24 (.close 48)))))) (.step 4 (.step 3 (.step 18 (.close 48))))) (.step 4 (.step 18 (.close 4))))) (.step 3 (.step 4 (.step 18 (.step 4 (.close 48))))))) (.step 4 (.step 44 (.step 48 (.step 51 (.step 60 (.step 8 (.step 4 (.close 3))))))))) (.step 3 (.step 4 (.step 24 (.step 48 (.step 57 (.step 4 (.close 12)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672298497599846248536722695478313514479615767804125631561638601310103248210262806817755009585056312362446375091979324496998922048649264242900198382439810366521727250334720⟩
def references : Fin 5 → Box := ![Part1.root, Part2.root, Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 5 := (.split 52 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.reuse 0) (.run (.step 26 (.split 67 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.step 55 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.step 55 (.split 43 0 (.step 58 (.close 3)) (.step 3 (.close 9)))) (.step 3 (.step 18 (.close 32)))) (.step 3 (.step 18 (.close 26)))) (.step 3 (.step 18 (.step 4 (.close 48))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 21))))) (.step 9 (.step 26 (.step 55 (.step 3 (.step 58 (.step 15 (.step 3 (.close 4))))))))) (.step 3 (.step 18 (.step 12 (.step 4 (.close 15)))))) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.step 18 (.close 48)))) (.step 48 (.step 31 (.step 9 (.step 26 (.step 3 (.close 12))))))) (.step 48 (.step 3 (.step 9 (.close 12))))) (.step 3 (.close 7)))))) (.step 3 (.split 59 1 (.reuse 1) (.run (.step 3 (.step 26 (.step 48 (.step 58 (.close 3))))))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.run (.step 3 (.step 48 (.step 55 (.split 53 1 (.split 54 1 (.split 56 1 (.split 72 1 (.split 57 1 (.step 55 (.step 3 (.step 18 (.step 31 (.step 3 (.close 4)))))) (.step 48 (.step 3 (.step 18 (.step 3 (.step 16 (.close 21))))))) (.step 9 (.step 26 (.step 23 (.step 55 (.step 3 (.step 15 (.step 16 (.close 21))))))))) (.step 3 (.step 22 (.step 31 (.step 48 (.close 21)))))) (.step 9 (.step 48 (.step 51 (.step 55 (.step 3 (.step 15 (.step 26 (.step 15 (.close 31)))))))))) (.step 3 (.step 18 (.step 24 (.step 48 (.close 34)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 16546956789305976592836116594320052230379595797340204830138293440968562699090365327175975733534557373007083412620530767437282004110049488501555330117011687250968199504517133225289067209266724782446750224054700210127872⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.step 55 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.step 55 (.split 43 0 (.step 58 (.close 3)) (.step 3 (.close 9)))) (.step 3 (.step 18 (.close 32)))) (.step 3 (.step 18 (.close 26)))) (.step 3 (.step 18 (.step 4 (.close 48))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 21))))) (.step 9 (.step 21 (.step 55 (.step 3 (.step 18 (.step 15 (.step 12 (.step 3 (.close 22)))))))))) (.step 3 (.step 18 (.step 12 (.step 4 (.close 15)))))) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.step 18 (.close 48)))) (.step 48 (.step 31 (.step 9 (.step 21 (.close 3)))))) (.step 48 (.step 3 (.step 9 (.close 12))))) (.step 9 (.step 21 (.step 26 (.step 18 (.step 40 (.step 31 (.close 53)))))))) (.step 3 (.close 7))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672298497599846255247173441665404348006654646300703893605754795698386066651010111414829292214639149873150064360082846656316624510147409811795574301504866125845208808555520⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.step 3 (.step 51 (.step 3 (.step 62 (.split 54 1 (.split 67 1 (.split 72 1 (.step 55 (.step 3 (.close 7))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 18 (.close 12)))))))))) (.step 55 (.split 51 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.reuse 1) (.run (.step 26 (.step 53 (.split 45 1 (.split 55 1 (.split 1 0 (.split 11 0 (.step 53 (.split 12 0 (.split 21 0 (.split 34 0 (.split 10 0 (.split 22 0 (.step 53 (.close 3)) (.step 3 (.step 18 (.step 3 (.step 26 (.close 48)))))) (.step 3 (.step 18 (.step 3 (.step 12 (.step 18 (.close 48))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 26 (.step 3 (.step 31 (.close 48))))))))) (.step 3 (.step 18 (.step 21 (.step 18 (.close 48)))))) (.step 9 (.step 21 (.step 26 (.step 53 (.close 3))))))) (.step 3 (.close 53))) (.step 3 (.step 21 (.step 26 (.close 48))))) (.step 3 (.step 48 (.close 53)))) (.step 3 (.step 48 (.close 53)))))))) (.run (.step 3 (.step 26 (.step 32 (.step 48 (.step 55 (.step 3 (.step 4 (.close 12)))))))))) (.run (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.step 12 (.close 53))))))))) (.run (.step 3 (.step 9 (.step 21 (.step 48 (.step 53 (.step 55 (.step 57 (.step 48 (.close 53))))))))))) (.run (.step 3 (.step 4 (.step 18 (.step 48 (.step 12 (.close 53)))))))) (.run (.step 3 (.step 53 (.close 7)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 16546956789305976592836116594320052230379595797340204830138293440962022311215604090588039223652028791107244301657440815719232380927310533670067083887235153453215465221772295182588883708011980146809170620356350437229568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.step 55 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.step 55 (.split 43 0 (.step 58 (.close 3)) (.step 3 (.close 9)))) (.step 3 (.step 18 (.close 32)))) (.step 3 (.step 18 (.close 26)))) (.step 3 (.step 18 (.step 4 (.close 48))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 21))))) (.step 9 (.step 34 (.step 55 (.step 31 (.step 34 (.close 12))))))) (.step 3 (.step 12 (.close 4)))) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 48 (.step 31 (.step 9 (.close 52))))) (.step 48 (.step 3 (.step 9 (.close 12))))) (.step 9 (.step 26 (.step 40 (.step 55 (.step 18 (.step 31 (.close 52)))))))) (.step 3 (.close 7))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 16546956789305976592836116594320052230387700327672298497599839383739068958209629579730906555922034978530932631133690031607720580828024924690325292682795720024323421232244465893346163761675888543250188974901743417558016⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.reuse 0) (.run (.step 26 (.step 52 (.split 45 1 (.split 55 1 (.split 1 0 (.split 11 0 (.step 52 (.split 12 0 (.split 21 0 (.split 34 0 (.split 10 0 (.split 22 0 (.split 30 0 (.step 62 (.close 3)) (.step 3 (.step 18 (.step 3 (.step 32 (.step 18 (.close 48))))))) (.step 3 (.step 18 (.step 3 (.step 26 (.close 48)))))) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.step 9 (.step 18 (.step 26 (.step 3 (.step 31 (.close 48)))))))) (.step 3 (.step 18 (.step 26 (.step 18 (.close 48)))))) (.step 9 (.step 26 (.step 34 (.close 52)))))) (.step 3 (.step 34 (.close 12)))) (.step 3 (.step 26 (.step 12 (.step 18 (.close 48)))))) (.step 3 (.step 48 (.close 52)))) (.step 3 (.step 48 (.close 52)))))))) (.run (.step 3 (.step 12 (.step 26 (.step 48 (.step 55 (.step 3 (.close 4))))))))) (.run (.step 3 (.step 16 (.step 22 (.step 31 (.step 48 (.step 21 (.close 52))))))))) (.run (.step 3 (.step 9 (.step 48 (.step 52 (.step 55 (.step 57 (.split 45 1 (.split 55 1 (.split 59 1 (.split 1 0 (.split 10 0 (.split 11 0 (.step 57 (.step 48 (.close 3))) (.step 3 (.step 12 (.step 4 (.close 18))))) (.step 3 (.step 12 (.close 15)))) (.step 3 (.step 12 (.step 18 (.step 48 (.step 18 (.close 21))))))) (.step 26 (.step 52 (.close 3)))) (.step 12 (.step 48 (.close 52)))) (.step 12 (.step 48 (.step 18 (.step 26 (.step 18 (.step 21 (.close 52)))))))))))))))) (.run (.step 3 (.step 4 (.step 18 (.step 34 (.step 48 (.close 52))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672298497599846255247179835006435395158744515811830510010348968827382244511927070968282604975960252753140070746981920687873559835702346452559264178959057308253516090835968⟩
def references : Fin 2 → Box := ![Part8.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 49 1 (.reuse 0) (.step 55 (.split 50 1 (.split 51 1 (.reuse 1) (.run (.step 3 (.step 52 (.close 7))))) (.run (.step 48 (.step 52 (.step 55 (.step 58 (.split 72 1 (.split 45 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 1 0 (.split 11 0 (.step 52 (.split 12 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 10 0 (.step 53 (.close 3)) (.step 3 (.step 18 (.step 3 (.close 12))))) (.step 3 (.step 9 (.step 18 (.step 3 (.step 21 (.step 31 (.close 48)))))))) (.step 9 (.step 21 (.step 18 (.close 48))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 31 (.step 3 (.close 48)))))))) (.step 3 (.step 18 (.step 21 (.step 18 (.close 48)))))) (.step 9 (.step 21 (.step 34 (.close 52)))))) (.step 3 (.step 34 (.step 3 (.step 12 (.step 21 (.close 26))))))) (.step 3 (.step 21 (.step 34 (.step 3 (.step 48 (.step 26 (.step 36 (.step 48 (.close 52)))))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.step 12 (.step 16 (.close 52))))))))) (.step 3 (.step 48 (.close 52)))) (.step 3 (.step 18 (.step 34 (.step 48 (.close 52)))))) (.step 3 (.step 48 (.close 52)))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 26 (.step 31 (.step 52 (.close 3)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨6097165137335922326917182089439777940915230747392521779021790936768304177382354726797472857545882756171536974846497310342671827498613153464320, 5515652263101992197612038864773350743462566775890771079880189404797695676201137332767877742297283390103607270050250502052668921773427022124738258006019046025834116925087808287412111194116236748953439655054056693433344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 1 0 (.split 10 0 (.split 12 0 (.split 55 1 (.split 11 0 (.split 21 0 (.split 16 0 (.split 17 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 50 (.step 3 (.step 16 (.close 21)))) (.step 3 (.step 31 (.step 3 (.close 48))))) (.step 3 (.step 31 (.step 3 (.step 9 (.close 48)))))) (.step 21 (.step 31 (.step 18 (.step 21 (.close 48)))))) (.step 3 (.step 18 (.step 31 (.step 18 (.close 48)))))) (.step 3 (.step 18 (.step 21 (.step 31 (.step 18 (.close 48))))))) (.split 17 0 (.step 21 (.step 3 (.step 18 (.step 48 (.close 3))))) (.step 8 (.step 18 (.close 3))))) (.step 50 (.step 3 (.close 4)))) (.step 32 (.step 50 (.step 3 (.close 16))))) (.step 58 (.split 11 0 (.split 16 0 (.split 17 0 (.step 21 (.step 32 (.step 48 (.close 3)))) (.step 24 (.step 21 (.step 22 (.step 12 (.step 3 (.step 18 (.close 48)))))))) (.step 21 (.close 3))) (.step 12 (.step 24 (.step 32 (.step 4 (.step 15 (.close 3))))))))) (.step 58 (.step 31 (.step 3 (.step 12 (.step 18 (.close 12))))))) (.step 58 (.split 10 0 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 32 (.split 12 0 (.step 50 (.step 3 (.close 4))) (.step 4 (.step 12 (.step 4 (.step 3 (.step 18 (.close 48)))))))) (.step 3 (.step 4 (.step 21 (.step 12 (.close 22)))))) (.step 4 (.step 18 (.step 4 (.step 21 (.close 31)))))) (.step 3 (.step 31 (.close 4)))) (.step 3 (.close 4))) (.step 4 (.step 3 (.step 21 (.step 24 (.close 48)))))) (.step 3 (.close 4))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672298497599846255247179835012532560296080438138747692099788746768297475259319592747304395912728556930522425473779393545419442591873883427405761489301729135752126023074816⟩
def references : Fin 2 → Box := ![Part11.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 47 1 (.reuse 0) (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 51 1 (.step 69 (.split 45 1 (.reuse 1) (.run (.step 32 (.step 48 (.step 3 (.close 12))))))) (.run (.step 3 (.step 12 (.close 18))))) (.run (.step 18 (.step 31 (.step 48 (.step 4 (.step 12 (.step 4 (.close 18))))))))) (.run (.step 3 (.step 26 (.step 48 (.step 58 (.close 3))))))) (.run (.step 48 (.step 50 (.step 51 (.step 60 (.step 50 (.step 69 (.step 50 (.close 3)))))))))) (.run (.step 28 (.step 31 (.step 48 (.step 50 (.step 3 (.step 51 (.step 50 (.step 3 (.step 21 (.step 12 (.step 26 (.step 12 (.step 15 (.close 16)))))))))))))))) (.run (.step 21 (.step 32 (.step 48 (.step 51 (.step 53 (.step 55 (.step 75 (.split 57 1 (.step 48 (.step 3 (.step 9 (.close 12)))) (.step 26 (.close 48)))))))))))) (.run (.step 4 (.step 24 (.step 48 (.step 50 (.step 51 (.step 60 (.step 69 (.step 50 (.step 4 (.close 3)))))))))))) (.run (.step 3 (.step 48 (.step 3 (.close 50)))))) (.run (.step 3 (.step 32 (.step 48 (.step 50 (.step 53 (.step 55 (.step 18 (.close 21)))))))))) (.run (.step 3 (.step 12 (.step 48 (.step 49 (.step 53 (.step 55 (.step 4 (.step 18 (.close 21)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456544832487424, 5515652263101992197612038864773350743462566775890771079880189404797695676195046121893371249582013588074801710642480696335303150503955057155681641625684916254824532224629372682369647985846737971140399343011988372455424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 12 0 (.split 55 1 (.split 11 0 (.split 21 0 (.split 16 0 (.split 17 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 49 (.step 3 (.close 21))) (.step 3 (.step 31 (.step 3 (.close 48))))) (.step 3 (.step 31 (.step 3 (.step 9 (.close 48)))))) (.step 31 (.step 18 (.step 21 (.step 26 (.step 21 (.close 48))))))) (.step 3 (.step 18 (.step 31 (.step 18 (.close 48)))))) (.step 3 (.step 18 (.step 31 (.step 18 (.step 21 (.close 48))))))) (.split 17 0 (.split 34 0 (.split 35 0 (.step 3 (.step 49 (.close 3))) (.step 18 (.step 4 (.step 21 (.step 22 (.close 26)))))) (.step 3 (.step 16 (.close 4)))) (.step 8 (.step 18 (.close 3))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 12 (.step 3 (.step 12 (.step 3 (.close 31))))) (.step 3 (.step 4 (.close 12)))) (.step 8 (.close 12))) (.step 8 (.step 18 (.close 3)))) (.step 8 (.step 18 (.close 3))))) (.step 12 (.step 49 (.step 3 (.step 21 (.close 22)))))) (.step 12 (.split 11 0 (.split 16 0 (.split 17 0 (.step 48 (.split 22 0 (.step 12 (.step 16 (.step 12 (.close 3)))) (.step 3 (.step 4 (.step 12 (.close 16)))))) (.step 24 (.step 12 (.step 3 (.close 16))))) (.step 24 (.step 12 (.step 3 (.step 12 (.step 3 (.close 16))))))) (.step 12 (.close 3))))) (.step 12 (.step 31 (.step 3 (.step 12 (.close 3)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456544832487424, 16546956789305971693952805936977615282537298926032693975368063630029260225764210411055611509810644127384738750201223463497556775870016968686139589742655129731423499598118671302278837579057181505793568809298341920769024⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 51 1 (.step 69 (.split 45 1 (.split 1 0 (.reuse 0) (.run (.step 58 (.split 10 0 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 12 (.step 3 (.close 49))) (.step 3 (.step 4 (.step 12 (.step 21 (.close 22)))))) (.step 4 (.step 12 (.step 4 (.step 18 (.close 31)))))) (.step 3 (.step 12 (.close 31)))) (.step 3 (.close 4))) (.step 4 (.step 3 (.step 12 (.step 24 (.close 48)))))) (.step 3 (.close 4)))))) (.run (.step 12 (.step 48 (.close 3)))))) (.run (.step 3 (.step 12 (.close 18))))) (.run (.step 18 (.step 31 (.step 12 (.step 48 (.step 4 (.close 18)))))))) (.run (.step 3 (.step 26 (.step 48 (.step 58 (.close 3))))))) (.run (.step 48 (.step 49 (.step 51 (.step 60 (.step 69 (.split 1 0 (.split 30 0 (.step 60 (.close 3)) (.step 49 (.close 3))) (.step 12 (.close 49)))))))))) (.run (.step 28 (.step 31 (.step 48 (.step 49 (.step 3 (.step 51 (.step 49 (.step 3 (.step 12 (.step 21 (.step 26 (.step 21 (.close 31))))))))))))))) (.run (.step 12 (.step 48 (.step 51 (.step 52 (.step 55 (.step 75 (.split 57 1 (.step 48 (.step 3 (.step 9 (.close 18)))) (.step 26 (.step 48 (.close 3)))))))))))) (.run (.step 4 (.step 24 (.step 48 (.step 49 (.step 51 (.step 60 (.step 69 (.step 49 (.step 4 (.step 8 (.step 4 (.step 3 (.close 12))))))))))))))) (.run (.step 3 (.step 48 (.step 3 (.close 49)))))) (.run (.step 3 (.step 32 (.step 48 (.step 50 (.step 52 (.step 55 (.step 12 (.step 4 (.step 18 (.close 21))))))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609096328090188917543189820794407488664744963140579997681438716679209340984577238834457479080980377119346465093631357232962223473664⟩
def references : Fin 2 → Box := ![Part13.root, Part15.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.step 48 (.step 58 (.split 46 1 (.reuse 0) (.split 47 1 (.step 3 (.split 49 1 (.reuse 1) (.run (.step 3 (.step 12 (.step 48 (.step 49 (.step 52 (.step 55 (.step 4 (.step 18 (.step 21 (.close 26))))))))))))) (.run (.step 48 (.step 49 (.step 3 (.step 50 (.step 51 (.step 60 (.step 69 (.split 72 1 (.step 50 (.step 12 (.step 32 (.step 50 (.close 3))))) (.step 12 (.step 31 (.step 48 (.close 49))))))))))))))))) (.run (.step 3 (.step 9 (.step 10 (.step 30 (.step 47 (.step 3 (.split 45 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 46 1 (.step 3 (.split 47 1 (.step 9 (.step 3 (.close 7))) (.step 3 (.close 9)))) (.step 3 (.step 8 (.close 9)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 46)))))) (.step 3 (.close 46))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 3 (.step 9 (.step 27 (.step 46 (.close 52)))))) (.step 3 (.close 9)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 16546956789305971693952805936977615282537298926032693975368056765228326704546593333021969809108951878741512997091174889116122428461705562991606072239891154062248266663099661207601317945909749281934853781861009165648896⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 53 1 (.step 21 (.split 54 1 (.split 56 1 (.step 3 (.split 57 1 (.split 59 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 11 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.split 21 0 (.split 10 0 (.split 22 0 (.split 30 0 (.step 31 (.step 3 (.step 21 (.close 41)))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.step 12 (.close 31)))) (.step 3 (.step 21 (.step 4 (.close 31)))))) (.step 3 (.step 18 (.step 3 (.close 31))))) (.step 3 (.step 18 (.step 3 (.step 21 (.close 31)))))) (.step 10 (.step 21 (.step 31 (.step 3 (.close 12)))))) (.step 3 (.step 43 (.step 31 (.step 24 (.close 18)))))) (.step 3 (.step 31 (.close 4)))) (.step 3 (.step 5 (.step 31 (.step 21 (.step 41 (.close 12))))))) (.step 10 (.step 21 (.step 31 (.step 3 (.close 48)))))) (.step 31 (.step 3 (.step 22 (.close 38))))) (.step 3 (.step 21 (.step 26 (.step 31 (.step 48 (.close 12))))))) (.step 28 (.step 31 (.step 48 (.step 60 (.step 31 (.step 3 (.close 12))))))))) (.step 28 (.step 41 (.step 3 (.step 58 (.step 41 (.step 48 (.step 3 (.step 21 (.step 3 (.step 26 (.step 3 (.close 4))))))))))))) (.step 3 (.step 10 (.step 21 (.step 31 (.step 48 (.step 57 (.step 58 (.step 41 (.step 57 (.step 26 (.step 41 (.close 48)))))))))))))) (.step 3 (.step 4 (.step 5 (.step 41 (.step 43 (.step 51 (.step 24 (.step 43 (.step 60 (.step 3 (.step 31 (.step 24 (.step 3 (.close 18))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184963209433920794659983249949694566708154505330321062410355722227717700468143625693743218421454721325141950727168⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 10 (.step 21 (.step 48 (.step 58 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 52 1 (.reuse 0) (.run (.step 3 (.step 21 (.step 31 (.step 48 (.close 41))))))) (.run (.step 3 (.step 21 (.step 31 (.step 48 (.step 16 (.step 49 (.step 48 (.step 41 (.step 52 (.step 41 (.close 58))))))))))))) (.run (.step 21 (.step 31 (.step 32 (.step 41 (.close 50))))))) (.run (.step 21 (.step 31 (.step 41 (.step 48 (.step 28 (.step 41 (.step 49 (.step 3 (.step 60 (.split 55 1 (.split 1 0 (.split 30 0 (.split 35 0 (.split 36 0 (.split 38 2 (.split 42 0 (.split 54 1 (.step 49 (.close 3)) (.step 12 (.step 16 (.step 21 (.step 31 (.step 3 (.step 41 (.step 3 (.close 48))))))))) (.step 31 (.step 3 (.close 12)))) (.step 41 (.close 49))) (.step 31 (.step 3 (.step 12 (.step 21 (.close 41)))))) (.step 12 (.step 31 (.step 3 (.close 21))))) (.step 3 (.step 31 (.step 12 (.step 21 (.close 41)))))) (.step 3 (.step 12 (.step 31 (.step 21 (.step 4 (.close 41))))))) (.step 5 (.step 12 (.step 32 (.step 3 (.step 31 (.close 48)))))))))))))))))) (.run (.step 3 (.step 21 (.step 31 (.step 28 (.step 41 (.close 3)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967906519086342326439028910888145382209256695418879050097136809660764886193854910630145819451490862548014597120⟩
def references : Fin 2 → Box := ![Part16.root, Part18.root]
def proof : Chunks.Proof 2 := (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 58 (.split 46 1 (.step 7 (.split 47 1 (.step 75 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.step 31 (.step 59 (.step 60 (.step 31 (.step 7 (.step 22 (.close 38))))))) (.step 9 (.step 26 (.step 31 (.step 3 (.close 12)))))) (.step 3 (.step 4 (.step 31 (.close 12))))) (.step 3 (.step 26 (.step 31 (.step 12 (.close 55)))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 26 (.step 31 (.close 53)))))))) (.step 3 (.step 9 (.step 18 (.step 26 (.step 31 (.close 52)))))))) (.step 31 (.step 3 (.step 12 (.step 24 (.close 50))))))) (.step 3 (.step 31 (.close 49))))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.step 58 (.split 38 1 (.split 42 1 (.split 46 1 (.step 7 (.split 47 1 (.step 75 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.step 31 (.step 59 (.split 57 1 (.step 31 (.step 7 (.step 22 (.close 38)))) (.step 28 (.step 31 (.close 3)))))) (.step 9 (.step 22 (.step 31 (.step 3 (.close 12)))))) (.step 3 (.step 4 (.step 31 (.close 12))))) (.step 3 (.step 22 (.step 31 (.step 12 (.close 55)))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 22 (.step 31 (.close 53)))))))) (.step 3 (.step 9 (.step 18 (.step 22 (.step 31 (.close 52)))))))) (.step 31 (.step 3 (.step 12 (.step 24 (.close 50))))))) (.step 3 (.step 31 (.close 49)))) (.step 7 (.step 31 (.close 39)))) (.step 3 (.step 21 (.step 31 (.step 28 (.close 39)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 16546956789305971693952805936977615282537298926032697660878237255014803502939738829378311367834525312481553160874361803147617213992347994231280505499646895043609088840984448571555669172168338243200874001294491140490240⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 53 1 (.step 21 (.step 75 (.split 54 1 (.step 58 (.split 56 1 (.split 57 1 (.split 59 1 (.split 43 1 (.split 45 1 (.split 51 1 (.split 55 1 (.split 67 1 (.split 72 1 (.split 1 0 (.split 11 0 (.step 29 (.split 12 0 (.split 21 0 (.split 45 0 (.split 49 0 (.split 10 0 (.step 38 (.step 3 (.step 18 (.step 21 (.close 16))))) (.step 3 (.step 18 (.step 12 (.step 15 (.step 21 (.close 31))))))) (.step 18 (.step 21 (.close 31)))) (.step 21 (.step 31 (.step 18 (.close 26))))) (.step 18 (.step 4 (.step 21 (.close 31))))) (.step 21 (.step 31 (.step 12 (.step 4 (.close 18))))))) (.step 18 (.step 4 (.step 12 (.close 31))))) (.step 18 (.step 29 (.step 40 (.step 4 (.close 31)))))) (.step 29 (.close 38))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 18 (.step 31 (.step 21 (.step 38 (.close 12))))))) (.step 3 (.step 12 (.close 18)))) (.step 9 (.step 18 (.step 21 (.step 31 (.step 38 (.step 18 (.close 48)))))))) (.step 3 (.close 9))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 18 (.step 40 (.step 18 (.step 31 (.close 48)))))))))) (.step 18 (.step 31 (.step 48 (.step 55 (.step 58 (.step 60 (.close 12)))))))) (.step 3 (.step 31 (.step 3 (.step 28 (.close 38))))))) (.step 9 (.step 21 (.step 31 (.step 38 (.step 48 (.step 57 (.step 31 (.step 4 (.step 18 (.close 26))))))))))))) (.step 3 (.step 4 (.step 18 (.step 4 (.step 15 (.step 26 (.step 15 (.step 31 (.close 38)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911106083574306582052132529935986383138288548857386659384284838443660039607087599761959488597082799387706368⟩
def references : Fin 2 → Box := ![Part19.root, Part20.root]
def proof : Chunks.Proof 2 := (.split 35 1 (.reuse 0) (.step 3 (.step 21 (.step 48 (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 52 1 (.reuse 1) (.run (.step 3 (.step 4 (.step 9 (.step 18 (.step 21 (.step 31 (.step 32 (.step 38 (.step 40 (.step 48 (.step 38 (.step 55 (.step 31 (.close 12)))))))))))))))) (.run (.step 3 (.step 4 (.step 9 (.step 18 (.step 21 (.step 31 (.step 38 (.step 48 (.step 52 (.step 55 (.step 40 (.step 57 (.step 58 (.step 75 (.split 34 0 (.step 55 (.step 40 (.step 62 (.step 18 (.step 31 (.close 52)))))) (.step 3 (.step 15 (.step 31 (.close 26))))))))))))))))))))) (.run (.step 18 (.step 21 (.step 31 (.step 38 (.close 50))))))) (.run (.step 18 (.step 21 (.step 31 (.step 48 (.step 49 (.step 50 (.step 52 (.step 58 (.step 66 (.step 75 (.split 53 1 (.step 75 (.step 49 (.step 21 (.close 48)))) (.step 4 (.close 18))))))))))))))) (.run (.step 3 (.step 4 (.step 21 (.step 29 (.step 31 (.step 38 (.close 3))))))))) (.run (.step 3 (.step 4 (.step 21 (.step 31 (.step 28 (.close 38)))))))) (.run (.step 3 (.step 4 (.step 21 (.step 29 (.step 31 (.step 38 (.step 3 (.step 22 (.close 39)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563736168967137450786291425753734468463110858792612849878742754968732672⟩
def references : Fin 1 → Box := ![Part21.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.step 58 (.split 38 1 (.split 42 1 (.split 46 1 (.step 7 (.split 47 1 (.step 75 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.step 31 (.step 59 (.split 57 1 (.step 31 (.step 7 (.step 22 (.close 37)))) (.step 28 (.step 31 (.close 3)))))) (.step 9 (.step 31 (.step 3 (.close 12))))) (.step 3 (.step 4 (.step 31 (.close 12))))) (.step 3 (.step 31 (.step 12 (.step 15 (.step 52 (.close 55))))))) (.step 3 (.step 9 (.step 18 (.step 15 (.step 21 (.step 31 (.step 52 (.close 53))))))))) (.step 3 (.step 9 (.step 16 (.step 18 (.step 15 (.step 31 (.close 52))))))))) (.step 31 (.step 3 (.step 12 (.step 14 (.step 24 (.close 49)))))))) (.step 3 (.step 16 (.step 31 (.close 49))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 16 (.step 21 (.step 28 (.step 31 (.close 37)))))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 4 (.step 21 (.step 29 (.step 31 (.close 37))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 35 1 (.step 18 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.split 47 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.step 18 (.close 31)))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.close 31)))) (.step 3 (.step 18 (.close 31))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨3291009114642412084309938365114701009965471731267159729918443520, 16546956789305971693952805936977615282537298926032697660874725911014926480025555892634494751875668459999977703905541223090323330922504009359574085058484274057412626331978705827048040715530270441408088447799092205061120⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 49 1 (.step 24 (.split 50 1 (.split 55 1 (.split 56 1 (.split 57 1 (.step 3 (.step 31 (.split 59 1 (.split 72 1 (.split 52 1 (.split 54 1 (.step 24 (.step 3 (.step 4 (.close 3)))) (.step 4 (.step 3 (.step 18 (.close 15))))) (.step 3 (.step 4 (.step 18 (.step 4 (.step 12 (.step 4 (.close 48)))))))) (.step 4 (.step 9 (.step 18 (.step 15 (.step 24 (.step 15 (.close 26)))))))) (.step 3 (.step 4 (.step 18 (.step 48 (.step 12 (.step 34 (.step 24 (.step 12 (.close 55)))))))))))) (.step 4 (.step 8 (.step 24 (.step 4 (.step 31 (.step 48 (.step 3 (.close 16))))))))) (.step 3 (.step 4 (.step 10 (.step 22 (.step 31 (.step 43 (.step 24 (.step 31 (.step 24 (.step 26 (.step 31 (.step 16 (.close 21)))))))))))))) (.step 3 (.step 4 (.step 5 (.step 18 (.step 24 (.close 48))))))) (.step 3 (.step 18 (.step 48 (.close 53)))))) (.step 3 (.step 4 (.step 18 (.step 34 (.step 48 (.close 52))))))) (.step 4 (.step 8 (.step 21 (.step 24 (.step 32 (.step 48 (.step 8 (.step 50 (.step 24 (.step 4 (.step 31 (.step 48 (.close 3)))))))))))))) (.step 4 (.step 8 (.step 12 (.step 16 (.step 24 (.step 48 (.step 8 (.step 49 (.step 24 (.step 4 (.step 31 (.step 48 (.step 3 (.close 16))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959258677843440558711031646073401137398717462619617231872⟩
def references : Fin 2 → Box := ![Part22.root, Part23.root]
def proof : Chunks.Proof 2 := (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 26 (.step 18 (.step 48 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.step 18 (.step 56 (.step 60 (.split 56 1 (.step 24 (.split 45 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 4 (.step 12 (.close 18)))))) (.step 3 (.close 18)))))) (.step 3 (.step 18 (.step 12 (.close 23))))) (.step 3 (.step 18 (.step 12 (.step 23 (.step 26 (.close 53))))))) (.step 3 (.step 18 (.step 23 (.step 26 (.close 52)))))) (.step 18 (.step 3 (.step 4 (.step 3 (.close 50))))))) (.step 3 (.step 18 (.step 24 (.close 49))))) (.step 3 (.step 18 (.step 41 (.step 49 (.step 41 (.close 50)))))))))))))) (.step 3 (.step 18 (.step 24 (.step 31 (.step 48 (.step 55 (.split 35 1 (.split 38 1 (.reuse 1) (.run (.step 3 (.step 4 (.step 5 (.step 10 (.step 21 (.step 24 (.step 31 (.step 32 (.step 41 (.step 43 (.step 41 (.step 24 (.step 31 (.step 12 (.step 16 (.step 24 (.step 26 (.step 22 (.close 41))))))))))))))))))))) (.run (.step 3 (.step 4 (.step 9 (.step 18 (.step 21 (.step 4 (.step 31 (.close 38)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087062013963627308205778907757281330332672⟩
def references : Fin 1 → Box := ![Part24.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 22 (.step 18 (.step 48 (.split 22 1 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.step 18 (.step 56 (.split 56 1 (.step 24 (.split 57 1 (.step 18 (.step 3 (.close 7))) (.step 8 (.step 18 (.close 3))))) (.step 3 (.close 18))))) (.step 3 (.step 18 (.step 12 (.close 22))))) (.step 3 (.step 18 (.step 12 (.step 22 (.close 53)))))) (.step 3 (.step 18 (.step 22 (.close 52))))) (.step 18 (.step 3 (.step 4 (.step 3 (.close 50))))))) (.step 3 (.step 18 (.step 22 (.close 49))))) (.step 3 (.step 18 (.step 41 (.step 49 (.step 41 (.close 50))))))) (.step 7 (.step 18 (.step 7 (.step 8 (.step 14 (.close 20)))))))))))))) (.run (.step 7 (.step 18 (.step 21 (.step 18 (.split 17 1 (.step 48 (.split 22 1 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.step 18 (.step 56 (.split 56 1 (.step 24 (.split 57 1 (.step 18 (.step 3 (.close 7))) (.step 8 (.step 18 (.close 3))))) (.step 3 (.close 18))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 18 (.step 12 (.step 21 (.close 53)))))) (.step 3 (.step 18 (.step 21 (.close 52))))) (.step 18 (.step 3 (.step 4 (.step 3 (.step 41 (.close 50)))))))) (.step 3 (.step 18 (.step 21 (.close 49))))) (.step 3 (.step 18 (.step 41 (.close 49))))) (.step 7 (.step 18 (.step 7 (.step 8 (.step 14 (.close 19)))))))) (.step 7 (.step 18 (.step 7 (.step 8 (.close 19))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2658455991569831745807614123781914624, 5515652263101997096495349522115787691312968177530375602111975462414438957401097549794813926768681989013467827792347996720486078820359079512207263036000181610761367930983021630667241438035122195005348754187121378460672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 52 1 (.split 55 1 (.split 1 0 (.split 11 0 (.split 16 0 (.step 9 (.split 51 1 (.split 67 1 (.split 12 2 (.split 10 0 (.split 17 0 (.split 22 0 (.split 21 0 (.split 35 0 (.split 38 0 (.step 15 (.step 12 (.step 3 (.close 15)))) (.step 12 (.step 15 (.close 3)))) (.step 15 (.step 3 (.close 12)))) (.step 15 (.close 3))) (.step 3 (.step 26 (.step 4 (.step 3 (.close 12)))))) (.step 3 (.step 18 (.step 22 (.step 15 (.step 3 (.step 4 (.step 12 (.close 15))))))))) (.step 3 (.step 12 (.close 3)))) (.split 35 0 (.split 38 0 (.step 15 (.close 3)) (.step 12 (.step 15 (.close 3)))) (.step 15 (.close 3)))) (.step 3 (.close 12))) (.step 3 (.close 12)))) (.step 3 (.step 21 (.step 3 (.step 18 (.step 12 (.step 3 (.close 15)))))))) (.step 3 (.split 10 0 (.split 30 0 (.split 38 0 (.split 43 0 (.split 45 0 (.split 46 0 (.step 15 (.close 3)) (.step 4 (.close 12))) (.step 4 (.step 12 (.close 15)))) (.step 3 (.close 4))) (.step 3 (.step 4 (.step 12 (.close 15))))) (.step 3 (.close 4))) (.step 3 (.close 4))))) (.step 3 (.split 10 0 (.split 30 0 (.split 38 0 (.split 43 0 (.split 45 0 (.split 46 0 (.step 15 (.step 3 (.close 4))) (.step 4 (.close 12))) (.step 4 (.step 12 (.close 15)))) (.step 3 (.close 4))) (.step 3 (.step 4 (.step 12 (.close 15))))) (.step 3 (.close 4))) (.step 3 (.close 4))))) (.step 3 (.step 12 (.step 48 (.step 3 (.close 15)))))) (.step 3 (.step 9 (.step 12 (.step 48 (.step 55 (.step 3 (.close 15)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2658455991569831745807614123781914624, 16546956789305971693952805936977615282537298926032697653672949063337272220791700076874282115501815995211748605698170228332556209201089750136114519681581746677775930955270238482812942568987811709075601621044840445772800⟩
def references : Fin 1 → Box := ![Part26.root]
def proof : Chunks.Proof 1 := (.step 58 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 34 1 (.split 36 1 (.split 16 1 (.split 17 1 (.step 26 (.split 30 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 45 1 (.reuse 0) (.run (.step 9 (.step 12 (.step 15 (.step 3 (.close 48))))))) (.run (.step 12 (.close 3)))) (.run (.step 3 (.close 9)))) (.run (.step 3 (.step 9 (.step 15 (.step 16 (.step 26 (.step 31 (.close 3))))))))) (.run (.step 3 (.step 12 (.close 15)))))) (.run (.step 3 (.step 4 (.step 12 (.step 17 (.step 4 (.close 15)))))))) (.run (.step 3 (.step 4 (.step 12 (.step 17 (.close 18))))))) (.run (.step 3 (.step 9 (.step 15 (.step 16 (.step 22 (.step 31 (.close 3))))))))) (.run (.step 3 (.step 9 (.step 15 (.step 16 (.close 31))))))) (.run (.step 9 (.step 12 (.step 15 (.step 18 (.step 26 (.step 15 (.step 31 (.close 4)))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 21 (.step 22 (.step 26 (.step 15 (.step 12 (.step 15 (.step 48 (.close 3)))))))))))))) (.run (.step 10 (.step 12 (.step 21 (.step 22 (.step 24 (.step 26 (.step 31 (.step 48 (.step 3 (.step 55 (.step 48 (.close 3)))))))))))))) (.run (.step 3 (.step 10 (.step 12 (.step 15 (.step 16 (.step 22 (.step 31 (.step 48 (.step 15 (.step 26 (.step 48 (.close 4)))))))))))))))
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
def root : Box := ⟨2658455991569831745807614123781914624, 16546956789305971693952805936977615282537298926032697660878240687416913352199623651619564607579514283045554449335145923182513278576454865460486842095791529713788031270703853749994926257545806037502549966513607200998400⟩
def references : Fin 1 → Box := ![Part27.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 54 1 (.reuse 0) (.run (.step 9 (.step 12 (.step 15 (.step 21 (.step 22 (.step 26 (.step 48 (.step 57 (.step 58 (.split 55 1 (.split 57 1 (.split 30 1 (.split 30 0 (.step 57 (.step 3 (.close 4))) (.step 15 (.close 3))) (.step 3 (.step 12 (.close 15)))) (.step 12 (.step 26 (.step 15 (.close 3))))) (.step 3 (.step 12 (.step 15 (.close 4)))))))))))))))) (.run (.step 3 (.step 4 (.step 12 (.step 14 (.step 18 (.step 24 (.step 31 (.step 48 (.step 12 (.step 4 (.close 15))))))))))))) (.run (.step 3 (.step 4 (.step 9 (.step 12 (.step 15 (.step 21 (.step 22 (.step 26 (.step 48 (.step 53 (.step 55 (.step 57 (.step 15 (.step 53 (.step 3 (.step 12 (.close 15))))))))))))))))))) (.run (.step 3 (.step 4 (.step 9 (.step 12 (.step 15 (.step 18 (.step 21 (.step 22 (.step 26 (.step 3 (.step 34 (.close 52)))))))))))))) (.run (.step 10 (.step 12 (.step 14 (.step 21 (.step 22 (.step 24 (.step 31 (.step 32 (.step 48 (.step 51 (.step 53 (.step 55 (.step 59 (.step 75 (.split 54 1 (.split 57 1 (.split 56 1 (.step 48 (.close 3)) (.step 10 (.step 22 (.step 15 (.close 3))))) (.step 26 (.step 48 (.step 3 (.close 4))))) (.step 9 (.step 15 (.step 48 (.step 3 (.close 15)))))))))))))))))))))) (.run (.step 3 (.step 4 (.step 10 (.step 12 (.step 15 (.step 16 (.step 21 (.step 31 (.step 48 (.step 57 (.step 41 (.step 58 (.step 15 (.step 26 (.close 41)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part27.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨2596148429267413814265251385835520, 16546956789305971693952805936977615282537298918296070997278605369056781662738258409632485506845364787564749759700896290995020488092026642732562636175830275641111465303017097539332361013470189656378381239006814948819968⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 59 1 (.split 72 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 45 1 (.split 49 1 (.split 55 1 (.split 1 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 24 (.split 34 0 (.split 36 0 (.split 38 0 (.step 18 (.step 24 (.step 3 (.step 4 (.close 12))))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.step 4 (.close 14))))) (.step 3 (.step 12 (.step 3 (.step 4 (.close 14)))))) (.step 18 (.step 3 (.close 12)))) (.step 18 (.step 8 (.step 14 (.close 3))))) (.step 24 (.split 34 0 (.split 35 0 (.step 3 (.step 12 (.step 4 (.close 3)))) (.step 4 (.close 12))) (.step 3 (.close 4))))) (.step 24 (.step 3 (.step 14 (.step 3 (.close 4)))))) (.step 12 (.step 18 (.step 3 (.step 4 (.close 14)))))) (.step 3 (.step 4 (.step 12 (.close 14))))) (.step 4 (.step 3 (.step 18 (.step 12 (.step 14 (.close 48))))))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.step 14 (.step 12 (.close 31)))))) (.step 3 (.step 4 (.close 31)))) (.step 4 (.step 12 (.step 18 (.step 4 (.step 15 (.close 31))))))) (.step 3 (.step 4 (.step 15 (.step 18 (.step 4 (.step 12 (.step 34 (.close 48)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part29

namespace Part30
def root : Box := ⟨2596148429267413814265251385835520, 16546956789305971693952805936977615282537298926032693975361027212421082766261071248309744982890583055019039288165634740077865763942967021857228207402065815894050804361180228227811411599012009374229032417872337537336320⟩
def references : Fin 1 → Box := ![Part29.root]
def proof : Chunks.Proof 1 := (.split 54 1 (.split 56 1 (.split 57 1 (.reuse 0) (.run (.step 4 (.step 8 (.step 12 (.step 18 (.step 44 (.step 48 (.step 51 (.step 60 (.split 45 1 (.split 1 0 (.split 10 0 (.split 11 2 (.split 16 0 (.split 17 0 (.split 21 0 (.split 30 0 (.step 24 (.step 8 (.close 60))) (.step 3 (.close 4))) (.step 8 (.step 12 (.step 14 (.step 4 (.close 3)))))) (.step 8 (.step 18 (.step 12 (.step 3 (.close 4)))))) (.step 8 (.step 18 (.step 12 (.step 3 (.close 4)))))) (.step 8 (.step 60 (.step 3 (.close 4))))) (.step 8 (.step 12 (.step 3 (.close 14))))) (.step 8 (.step 12 (.step 14 (.close 4))))) (.step 4 (.step 8 (.step 12 (.step 3 (.step 18 (.close 48))))))))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 31 (.step 43 (.step 51 (.step 24 (.step 43 (.step 24 (.step 60 (.step 3 (.step 31 (.close 14))))))))))))))) (.run (.step 3 (.step 4 (.step 12 (.step 15 (.step 4 (.close 14))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part29.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part30

namespace Part31
def root : Box := ⟨2596148429267413814265251385835520, 16546956789305971693952805936977615282537298926032693975368063630029263422434719980368829790331939424506119460302350194702497528442141886903463180143510348643058898715864311630523764336080658429964557216557250874704896⟩
def references : Fin 1 → Box := ![Part30.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.step 24 (.split 52 1 (.split 53 1 (.reuse 0) (.run (.step 4 (.step 8 (.step 14 (.step 24 (.step 34 (.step 48 (.step 51 (.split 34 1 (.split 36 1 (.split 42 1 (.split 45 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 1 0 (.split 30 1 (.split 34 0 (.split 35 0 (.step 8 (.step 14 (.step 56 (.close 3)))) (.step 18 (.step 12 (.step 4 (.close 14))))) (.step 8 (.step 14 (.step 18 (.close 14))))) (.step 3 (.step 12 (.close 14)))) (.step 3 (.step 8 (.step 14 (.step 24 (.close 14)))))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 12 (.close 14)))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.step 8 (.step 12 (.step 14 (.step 3 (.close 4)))))))) (.step 3 (.step 12 (.close 14)))) (.step 3 (.step 4 (.step 8 (.close 14))))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14))))))))))))) (.run (.step 3 (.step 12 (.step 15 (.step 18 (.step 24 (.step 34 (.step 24 (.step 48 (.close 14)))))))))))) (.run (.step 3 (.step 4 (.step 15 (.step 18 (.step 34 (.step 48 (.close 14)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part30.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part31

namespace Part32
def root : Box := ⟨2596148429267413814265251385835520, 16546956789305971693952805936977615282537298926032693975368063630029263422440823099768995142270503986656193456776410850479916800730713503807943172117940928325644259730497641537824375077504154272836860559512402418205696⟩
def references : Fin 1 → Box := ![Part31.root]
def proof : Chunks.Proof 1 := (.split 46 1 (.split 47 1 (.reuse 0) (.run (.step 4 (.step 8 (.step 12 (.step 14 (.step 18 (.step 24 (.step 48 (.step 50 (.step 51 (.step 60 (.step 69 (.split 45 1 (.split 53 1 (.split 72 1 (.split 1 0 (.split 10 0 (.split 11 2 (.split 17 0 (.split 21 0 (.split 22 0 (.split 45 0 (.step 50 (.close 3)) (.step 4 (.step 3 (.step 12 (.step 14 (.step 18 (.close 48))))))) (.step 8 (.step 18 (.step 3 (.close 4))))) (.step 8 (.step 12 (.step 14 (.step 4 (.close 3)))))) (.step 8 (.step 18 (.step 12 (.step 3 (.close 4)))))) (.step 8 (.step 50 (.step 3 (.close 4))))) (.step 8 (.step 12 (.step 3 (.close 14))))) (.step 8 (.step 12 (.step 14 (.close 4))))) (.step 4 (.step 12 (.close 14)))) (.step 8 (.step 14 (.close 4)))) (.step 4 (.step 8 (.step 12 (.step 14 (.step 3 (.step 18 (.close 48))))))))))))))))))))) (.run (.step 4 (.step 8 (.step 12 (.step 8 (.step 14 (.step 18 (.step 34 (.close 49))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part31.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part32

namespace Part33
def root : Box := ⟨2596148429267413814265251385835520, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087064675015767307304938529636650055631872⟩
def references : Fin 1 → Box := ![Part32.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 24 (.step 31 (.step 34 (.step 48 (.step 58 (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 38 1 (.reuse 0) (.run (.step 3 (.step 4 (.step 5 (.step 14 (.step 24 (.step 31 (.step 41 (.step 49 (.step 50 (.step 60 (.split 1 0 (.split 12 0 (.split 16 0 (.step 43 (.split 17 0 (.split 56 1 (.split 10 0 (.split 21 0 (.split 30 0 (.split 34 0 (.step 24 (.step 43 (.step 24 (.step 31 (.step 41 (.step 3 (.close 14))))))) (.step 3 (.step 4 (.step 14 (.close 31))))) (.step 3 (.close 14))) (.step 12 (.step 14 (.step 21 (.step 3 (.step 4 (.close 14))))))) (.step 3 (.step 12 (.close 14)))) (.step 41 (.close 3))) (.step 3 (.close 14)))) (.step 3 (.step 5 (.close 14)))) (.step 3 (.step 4 (.step 12 (.close 14))))) (.step 3 (.step 4 (.step 12 (.close 14))))))))))))))))) (.run (.step 3 (.step 4 (.step 12 (.step 15 (.step 18 (.step 31 (.step 4 (.step 12 (.close 14))))))))))) (.run (.step 3 (.step 4 (.step 14 (.step 18 (.close 3))))))) (.run (.step 3 (.step 4 (.step 14 (.step 18 (.step 3 (.step 8 (.close 14))))))))) (.run (.step 3 (.step 4 (.step 14 (.step 18 (.step 8 (.step 14 (.step 3 (.close 19)))))))))) (.run (.step 3 (.step 4 (.step 12 (.step 14 (.step 15 (.step 18 (.step 24 (.close 3))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part32.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part33

namespace Part34
def root : Box := ⟨3221227520, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087064675018302608505394988439643462044672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 4 (.step 31 (.step 48 (.split 11 1 (.split 12 1 (.step 58 (.split 35 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.step 4 (.split 57 1 (.step 4 (.step 57 (.step 58 (.split 59 1 (.step 4 (.step 31 (.step 4 (.step 3 (.step 26 (.step 3 (.close 12))))))) (.step 3 (.step 26 (.step 48 (.step 4 (.close 12))))))))) (.step 4 (.step 3 (.step 31 (.step 48 (.step 4 (.step 12 (.step 3 (.step 4 (.close 31))))))))))) (.step 3 (.step 4 (.step 31 (.step 4 (.step 12 (.step 21 (.close 32)))))))) (.step 4 (.step 12 (.step 18 (.close 12))))) (.step 3 (.step 4 (.step 23 (.step 48 (.step 12 (.close 55))))))) (.step 3 (.step 4 (.step 21 (.step 40 (.step 48 (.step 53 (.step 4 (.step 53 (.step 4 (.step 12 (.close 23)))))))))))) (.step 3 (.step 4 (.step 12 (.step 40 (.step 48 (.step 52 (.step 53 (.step 4 (.step 52 (.step 4 (.step 21 (.close 23))))))))))))) (.step 4 (.step 31 (.step 32 (.step 48 (.step 50 (.step 3 (.close 4)))))))) (.step 4 (.step 12 (.step 24 (.step 31 (.step 48 (.step 49 (.close 4)))))))) (.step 3 (.step 4 (.step 31 (.step 24 (.step 32 (.step 41 (.close 4)))))))) (.step 4 (.step 21 (.step 23 (.step 31 (.step 38 (.step 23 (.step 40 (.step 31 (.step 4 (.close 49)))))))))))) (.step 4 (.step 12 (.step 4 (.step 15 (.step 26 (.close 31))))))) (.step 4 (.step 12 (.close 14))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part34

namespace Part35
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087064675018302608505394988439643462044672⟩
def references : Fin 4 → Box := ![Part25.root, Part28.root, Part33.root, Part34.root]
def proof : Chunks.Proof 4 := (.split 1 1 (.split 10 1 (.split 11 1 (.split 12 1 (.reuse 0) (.step 3 (.step 12 (.step 18 (.step 31 (.step 48 (.step 55 (.split 21 1 (.split 35 1 (.reuse 1) (.run (.step 4 (.step 9 (.step 12 (.step 15 (.step 21 (.step 22 (.step 26 (.step 31 (.step 38 (.step 48 (.step 57 (.step 15 (.step 31 (.step 4 (.step 12 (.step 4 (.close 18))))))))))))))))))) (.run (.step 3 (.step 4 (.step 9 (.step 12 (.step 4 (.step 15 (.step 3 (.step 18 (.close 15)))))))))))))))))) (.reuse 2)) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 11 1 (.split 12 1 (.split 35 1 (.step 18 (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.split 47 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.step 12 (.step 18 (.close 31))))))) (.step 3 (.step 12 (.step 18 (.close 31))))) (.step 3 (.close 31)))) (.step 3 (.step 12 (.close 15)))) (.step 3 (.step 12 (.close 15)))) (.step 3 (.close 14))))))))) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes
  · exact Part28.excludes
  · exact Part33.excludes
  · exact Part34.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part35

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part35.excludes
end FiveColour.Packed.ProjectedChunks.Case93
