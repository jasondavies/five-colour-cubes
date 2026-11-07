module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
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
def root : Box := ⟨3221225472, 5515652263101992197612038864773350743462566775890771079880189404797695676195040170537896717152793770211462723661353408719841842743677472313930750551193843752628337372306128386294836462319825863675479561693853275653120⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 45 1 (.split 55 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 58 (.step 3 (.close 48))) (.step 3 (.close 26))) (.step 3 (.close 48))) (.step 3 (.close 48))) (.split 12 0 (.step 18 (.close 31)) (.step 22 (.step 3 (.close 48))))) (.split 12 0 (.split 16 0 (.split 17 0 (.step 31 (.close 48)) (.step 18 (.close 21))) (.step 18 (.close 21))) (.step 21 (.step 31 (.close 18))))) (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.close 3)) (.step 3 (.close 26))) (.step 3 (.step 7 (.close 22)))) (.step 3 (.step 7 (.close 21)))) (.step 31 (.close 12)))) (.step 3 (.step 18 (.step 48 (.close 3))))) (.split 12 0 (.step 3 (.step 18 (.step 12 (.step 4 (.close 31))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.step 3 (.close 48))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 4))))) (.split 11 0 (.step 3 (.step 18 (.step 12 (.close 31)))) (.step 3 (.close 4)))) (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 3 (.step 18 (.step 48 (.split 38 0 (.split 46 0 (.step 3 (.close 4)) (.step 4 (.close 48))) (.step 3 (.close 31)))))) (.step 4 (.close 3))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 24 (.step 3 (.step 4 (.close 3)))))) (.step 58 (.close 3))) (.split 11 0 (.step 48 (.close 3)) (.step 48 (.close 3)))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700319935675519510387987570787716997644227483297863711206192924702184800735474081752349203832033006965117504532843920188256719659523480682163619658669104681270808657811728237568⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.split 67 1 (.split 72 1 (.reuse 0) (.run (.split 45 1 (.split 55 1 (.split 1 0 (.split 11 0 (.step 29 (.split 12 0 (.split 45 0 (.split 49 0 (.split 10 0 (.step 75 (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 18 (.close 75))) (.step 31 (.close 48))) (.step 26 (.step 31 (.step 12 (.close 18)))))) (.step 18 (.step 4 (.close 31)))) (.step 40 (.step 4 (.close 31)))) (.step 18 (.close 58))) (.step 31 (.close 48))))) (.run (.step 3 (.step 7 (.step 3 (.close 18)))))) (.run (.step 26 (.split 67 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.step 55 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 43 0 (.step 58 (.close 3)) (.step 3 (.close 9))) (.step 18 (.close 32))) (.step 18 (.close 26))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 18 (.close 21)))) (.step 26 (.step 55 (.step 3 (.step 58 (.step 15 (.close 18))))))) (.step 3 (.close 48))) (.step 18 (.close 62))) (.step 3 (.close 48))) (.step 48 (.step 31 (.close 62)))) (.step 48 (.close 62))) (.step 3 (.close 7))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672298490394547759665974608023595453862986365564909071095925100304265006985657495980391819621165590964543012733254138764189221972027988516409609320118297698139072148538368⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 56 1 (.split 57 1 (.reuse 0) (.run (.step 3 (.split 59 1 (.step 69 (.split 72 1 (.split 45 1 (.split 1 0 (.split 10 0 (.split 12 0 (.split 55 1 (.split 11 0 (.split 21 0 (.split 17 0 (.split 35 0 (.split 43 0 (.step 60 (.close 3)) (.step 31 (.close 55))) (.step 31 (.close 48))) (.step 31 (.close 60))) (.split 17 0 (.step 26 (.step 48 (.close 60))) (.step 18 (.close 3)))) (.step 60 (.step 3 (.close 4)))) (.step 58 (.close 60))) (.step 58 (.split 11 0 (.split 16 0 (.step 26 (.step 48 (.close 31))) (.step 31 (.close 48))) (.step 12 (.step 24 (.close 60)))))) (.step 58 (.step 31 (.step 3 (.step 12 (.close 60)))))) (.split 10 0 (.split 34 0 (.split 35 0 (.split 12 0 (.step 60 (.step 3 (.close 4))) (.step 12 (.step 4 (.close 48)))) (.step 18 (.close 60))) (.step 3 (.close 60))) (.step 3 (.close 4)))) (.step 48 (.close 60))) (.step 26 (.close 60)))) (.step 48 (.step 58 (.close 3))))))) (.run (.step 3 (.split 57 1 (.split 59 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 11 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.split 10 0 (.split 22 0 (.split 30 0 (.step 31 (.step 3 (.close 48))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.close 31)))) (.step 3 (.close 59))) (.step 18 (.close 31))) (.step 31 (.step 3 (.close 48)))) (.step 43 (.step 31 (.step 24 (.close 18))))) (.step 3 (.step 5 (.step 31 (.close 48))))) (.step 31 (.close 48))) (.step 31 (.step 3 (.close 38)))) (.step 3 (.step 31 (.close 58)))) (.step 51 (.step 60 (.step 3 (.close 31))))))))
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
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970105039749120, 16546956789305976592836116594320052230387700327672298497599839383739062564868598532578816686410908362126338458004693853746803621274571611929004189802805713637424347200687530567791227120912198665795997792493436135277568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 57 1 (.step 3 (.split 59 1 (.step 51 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 24 (.split 34 0 (.split 36 0 (.split 38 0 (.step 24 (.step 3 (.step 4 (.close 48)))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 31)))) (.step 18 (.close 3))) (.step 18 (.close 56))) (.step 18 (.step 8 (.close 56)))) (.step 24 (.split 34 0 (.split 35 0 (.step 3 (.split 11 0 (.step 4 (.close 3)) (.step 12 (.close 24)))) (.step 4 (.close 12))) (.step 3 (.close 4))))) (.step 24 (.step 18 (.close 4)))) (.step 18 (.step 4 (.step 24 (.close 48))))) (.step 4 (.step 18 (.close 48)))) (.step 18 (.close 4)))) (.step 18 (.step 4 (.close 48))))) (.step 44 (.step 51 (.step 60 (.step 8 (.close 48)))))) (.step 24 (.step 48 (.step 57 (.step 4 (.close 12)))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672298497599846255240626660449612064266628266907048695301321511606299937072043528678637024621829800763383524175431038342014851141892289669777139788413095339738551753376768⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 51 1 (.split 52 1 (.split 53 1 (.split 54 1 (.reuse 0) (.run (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 55 1 (.split 67 1 (.split 45 1 (.split 10 0 (.split 16 0 (.split 1 0 (.split 11 0 (.step 9 (.split 17 0 (.step 57 (.split 42 0 (.step 48 (.close 3)) (.step 26 (.close 48)))) (.step 31 (.step 18 (.close 48))))) (.split 30 0 (.split 38 0 (.step 9 (.step 57 (.close 48))) (.step 3 (.close 48))) (.step 3 (.close 4)))) (.step 57 (.step 4 (.close 3)))) (.step 21 (.step 3 (.step 18 (.close 57))))) (.step 31 (.step 15 (.step 3 (.close 48))))) (.step 48 (.close 57))) (.step 3 (.close 18))) (.step 48 (.step 31 (.close 57)))) (.step 26 (.step 57 (.close 75)))) (.step 9 (.step 26 (.step 57 (.step 48 (.close 3)))))) (.step 26 (.step 51 (.step 48 (.close 55))))) (.step 51 (.close 57))))) (.reuse 1)) (.run (.split 53 1 (.split 54 1 (.split 56 1 (.split 72 1 (.split 57 1 (.step 55 (.step 31 (.step 3 (.close 4)))) (.step 48 (.step 18 (.step 3 (.close 31))))) (.step 26 (.step 23 (.step 55 (.close 22))))) (.step 3 (.step 31 (.step 48 (.close 21))))) (.step 55 (.close 57))) (.step 3 (.step 18 (.step 24 (.step 48 (.close 34)))))))) (.run (.step 51 (.step 3 (.split 54 1 (.split 67 1 (.split 72 1 (.step 55 (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 54))) (.step 3 (.close 51)))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672298497599846255247173441665404348006654646300703893605754795698386066651010111414829292214639149873150064360082846656316624510147409811795574301504866125845208808555520⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.reuse 0) (.run (.step 55 (.split 51 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.step 55 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 43 0 (.step 58 (.close 3)) (.step 3 (.close 9))) (.step 18 (.close 32))) (.step 3 (.step 18 (.close 26)))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 18 (.close 21)))) (.step 9 (.step 21 (.step 55 (.step 3 (.step 18 (.step 15 (.close 58)))))))) (.step 3 (.close 48))) (.step 18 (.close 53))) (.step 3 (.close 48))) (.step 48 (.step 31 (.close 53)))) (.step 48 (.close 53))) (.step 9 (.step 21 (.step 26 (.step 18 (.step 40 (.step 31 (.close 53)))))))) (.step 3 (.close 7))) (.step 26 (.split 1 0 (.split 11 0 (.split 12 0 (.split 34 0 (.split 10 0 (.split 22 0 (.step 53 (.close 3)) (.step 18 (.close 53))) (.step 18 (.close 53))) (.step 9 (.step 26 (.step 31 (.close 48))))) (.step 21 (.close 62))) (.step 3 (.close 53))) (.step 3 (.close 53))))) (.step 26 (.step 32 (.step 48 (.step 55 (.close 18)))))) (.step 3 (.step 31 (.close 58)))) (.step 3 (.step 9 (.step 21 (.step 53 (.step 55 (.step 57 (.step 48 (.close 53))))))))) (.step 3 (.step 18 (.step 48 (.close 53))))) (.step 3 (.close 54))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 16546956789305976592836116594320052230387700327672298497599839390442972923180928129517919055024958042270615541429886720469501302688906939727098781083732869107775135077260394986589189188552829949223473948118567920600064⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 10 0 (.split 11 0 (.split 12 0 (.step 55 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 43 0 (.step 58 (.close 3)) (.step 3 (.close 9))) (.step 18 (.close 32))) (.step 3 (.step 18 (.close 26)))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 18 (.close 21)))) (.step 9 (.step 34 (.step 55 (.step 31 (.step 34 (.close 12))))))) (.step 3 (.close 48))) (.step 18 (.close 52))) (.step 3 (.close 48))) (.step 48 (.step 31 (.close 52)))) (.step 48 (.close 52))) (.step 9 (.step 26 (.step 40 (.step 55 (.step 18 (.step 31 (.close 52)))))))) (.step 3 (.close 7))) (.split 11 0 (.split 12 0 (.split 34 0 (.split 10 0 (.split 30 0 (.step 62 (.close 3)) (.step 18 (.close 52))) (.step 18 (.close 52))) (.step 26 (.step 3 (.close 52)))) (.step 34 (.close 52))) (.step 3 (.close 62)))) (.step 12 (.step 26 (.step 48 (.step 55 (.close 18)))))) (.step 3 (.step 31 (.close 58)))) (.step 3 (.step 9 (.step 55 (.step 57 (.split 55 1 (.split 59 1 (.split 11 0 (.step 57 (.step 48 (.close 3))) (.step 3 (.step 12 (.close 18)))) (.step 52 (.close 3))) (.step 48 (.close 52)))))))) (.step 4 (.step 18 (.step 48 (.close 52))))) (.step 3 (.close 54))))
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
def root : Box := ⟨6097165137335922326917182089439777940915230747392521779021790936768304177382354726797472857545882756171536974846497310342671827498613153464320, 16546956789305976592836116594320052230387700327672298497599846255247179835012532560296080438138747692099788746768297475259319592747304395912728556930522425473779393545419442591873883427405761489301729135752126023074816⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 51 1 (.step 69 (.split 45 1 (.split 1 0 (.split 10 0 (.split 12 0 (.split 55 1 (.split 11 0 (.split 21 0 (.split 43 0 (.split 51 0 (.step 50 (.close 31)) (.step 31 (.close 48))) (.step 31 (.close 50))) (.split 17 0 (.step 21 (.step 48 (.close 3))) (.step 18 (.close 3)))) (.step 50 (.step 3 (.close 4)))) (.step 32 (.step 50 (.close 31)))) (.step 58 (.split 11 0 (.split 16 0 (.split 17 0 (.step 21 (.step 48 (.close 3))) (.step 24 (.step 22 (.close 48)))) (.step 21 (.close 3))) (.step 24 (.close 50))))) (.step 58 (.step 31 (.step 3 (.step 12 (.close 50)))))) (.split 10 0 (.split 34 0 (.split 36 0 (.step 32 (.split 12 0 (.step 50 (.step 3 (.close 4))) (.step 12 (.step 4 (.close 48))))) (.step 3 (.close 50))) (.step 3 (.close 50))) (.step 3 (.close 4)))) (.step 48 (.close 50)))) (.step 3 (.close 18))) (.step 31 (.step 48 (.close 50)))) (.step 48 (.step 58 (.close 3)))) (.step 51 (.step 60 (.step 69 (.step 50 (.close 3)))))) (.step 31 (.step 48 (.step 50 (.step 3 (.step 51 (.step 50 (.step 3 (.close 48))))))))) (.step 21 (.step 51 (.step 55 (.step 75 (.split 57 1 (.step 48 (.close 18)) (.step 26 (.close 48)))))))) (.step 24 (.step 51 (.step 60 (.step 69 (.step 50 (.step 4 (.close 3)))))))) (.step 48 (.step 3 (.close 50)))) (.step 32 (.step 50 (.step 55 (.close 50))))) (.step 12 (.step 49 (.step 55 (.close 49)))))))
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
def root : Box := ⟨5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456544832487424, 16546956789305971693952805936977615282537298926032693975361027212421079569590561678996526702369287757897658578064508008872925011370842103639904617001210598627919962564640630054535667399339037432793909644193291932009472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 72 1 (.split 51 1 (.step 69 (.split 45 1 (.split 1 0 (.split 12 0 (.split 55 1 (.split 11 0 (.split 21 0 (.split 17 0 (.split 35 0 (.split 43 0 (.split 51 0 (.step 49 (.close 31)) (.step 31 (.close 48))) (.step 31 (.close 49))) (.step 31 (.close 48))) (.step 31 (.close 49))) (.split 17 0 (.split 35 0 (.step 3 (.step 49 (.close 3))) (.step 18 (.close 31))) (.step 18 (.close 3)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 12 (.step 3 (.close 49))) (.step 3 (.close 12))) (.step 18 (.close 3))) (.step 18 (.close 3)))) (.step 49 (.close 48))) (.split 11 0 (.split 16 0 (.split 17 0 (.step 48 (.split 22 0 (.step 12 (.step 16 (.step 12 (.close 3)))) (.step 3 (.close 49)))) (.step 24 (.step 12 (.close 31)))) (.step 24 (.step 12 (.step 3 (.step 12 (.close 31)))))) (.step 12 (.close 3)))) (.step 58 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 12 (.step 3 (.close 49))) (.step 3 (.close 49))) (.step 12 (.step 18 (.close 31)))) (.step 3 (.close 49))) (.step 3 (.close 4))) (.step 24 (.close 48))))) (.step 12 (.step 48 (.close 3))))) (.step 3 (.close 18))) (.step 31 (.step 12 (.step 48 (.close 18))))) (.step 48 (.step 58 (.close 3)))) (.step 51 (.step 69 (.split 30 0 (.step 60 (.close 3)) (.step 49 (.close 3)))))) (.step 31 (.step 48 (.step 49 (.step 3 (.step 51 (.step 49 (.step 3 (.close 48))))))))) (.step 12 (.step 51 (.step 55 (.step 75 (.split 57 1 (.step 48 (.close 18)) (.step 26 (.close 49)))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609096328090188917543189820794407488664744963140579997681438716679209340984577238834457479080980377119346465093631357232962223473664⟩
def references : Fin 4 → Box := ![Part5.root, Part6.root, Part7.root, Part8.root]
def proof : Chunks.Proof 4 := (.split 43 1 (.step 48 (.step 58 (.split 46 1 (.split 47 1 (.split 49 1 (.reuse 0) (.step 55 (.split 50 1 (.reuse 1) (.run (.step 55 (.step 58 (.split 72 1 (.split 53 1 (.split 56 1 (.split 11 0 (.step 52 (.split 12 0 (.split 34 0 (.split 36 0 (.split 10 0 (.step 53 (.close 3)) (.step 18 (.close 52))) (.step 18 (.step 3 (.close 53)))) (.step 21 (.close 52))) (.step 34 (.close 52)))) (.step 34 (.step 3 (.close 52)))) (.step 31 (.step 48 (.close 52)))) (.step 48 (.close 52))) (.step 18 (.step 21 (.step 26 (.step 52 (.close 3)))))))))))) (.reuse 2)) (.split 47 1 (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.reuse 3) (.run (.step 24 (.step 51 (.step 60 (.step 69 (.step 49 (.step 4 (.step 8 (.step 4 (.close 18))))))))))) (.run (.step 48 (.step 3 (.close 49))))) (.run (.step 32 (.step 48 (.step 50 (.step 55 (.close 49))))))) (.run (.step 12 (.step 49 (.step 55 (.close 49))))))) (.run (.step 48 (.step 49 (.step 51 (.step 60 (.step 69 (.split 72 1 (.step 50 (.step 12 (.step 50 (.close 3)))) (.step 48 (.close 49))))))))))))) (.run (.step 30 (.step 47 (.split 45 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 46 1 (.step 3 (.split 47 1 (.step 9 (.step 3 (.close 7))) (.step 3 (.close 9)))) (.step 3 (.close 47))) (.step 3 (.close 46))) (.step 3 (.close 46))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 3 (.step 46 (.close 52)))) (.step 3 (.close 9)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 16546956789305976592836116594320052230387700327672298497599846255247179835012532563203440880660563495931728385923233208742826788383245340397474662021048988003480234776960440617177505276038825978648978132135018984637440⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 47 1 (.split 49 1 (.split 52 1 (.split 53 1 (.step 21 (.split 54 1 (.split 56 1 (.step 3 (.split 57 1 (.split 59 1 (.split 72 1 (.split 45 1 (.split 55 1 (.split 1 0 (.split 11 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.split 10 0 (.split 22 0 (.split 30 0 (.step 31 (.step 3 (.close 48))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.close 31)))) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 21 (.step 31 (.step 3 (.close 12))))) (.step 43 (.step 31 (.step 24 (.close 18))))) (.step 3 (.step 31 (.close 4)))) (.step 3 (.step 5 (.step 31 (.close 48))))) (.step 31 (.close 48))) (.step 31 (.step 3 (.close 38)))) (.step 3 (.step 21 (.close 58)))) (.step 28 (.step 60 (.close 41))))) (.step 28 (.step 41 (.step 3 (.step 58 (.step 41 (.step 48 (.step 3 (.close 31))))))))) (.step 3 (.step 10 (.step 21 (.step 31 (.step 57 (.step 58 (.step 57 (.step 26 (.step 41 (.close 48)))))))))))) (.step 4 (.step 43 (.step 51 (.step 24 (.step 60 (.step 31 (.step 24 (.close 41))))))))) (.step 3 (.step 48 (.close 41)))) (.step 3 (.step 21 (.step 48 (.step 16 (.step 49 (.step 48 (.close 58)))))))) (.step 21 (.step 32 (.step 41 (.close 50))))))
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
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 16546956789305971693952805936977615282537298926032697660878244119815743417504484122608733762972059418150749869994979436857921723769215859318890942570991496001498340453263739824401087912550440833248987136869327351841792⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 52 1 (.split 53 1 (.step 21 (.step 75 (.split 54 1 (.step 58 (.split 56 1 (.split 57 1 (.split 59 1 (.split 43 1 (.split 45 1 (.split 51 1 (.split 55 1 (.split 67 1 (.split 72 1 (.split 1 0 (.split 11 0 (.step 29 (.split 12 0 (.split 21 0 (.split 45 0 (.split 49 0 (.split 10 0 (.step 38 (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 18 (.close 38))) (.step 31 (.close 48))) (.step 18 (.close 31))) (.step 21 (.step 31 (.step 12 (.close 18)))))) (.step 18 (.close 38))) (.step 40 (.step 4 (.close 31)))) (.step 29 (.close 38))) (.step 3 (.close 18))) (.step 31 (.close 58))) (.step 3 (.close 18))) (.step 31 (.step 38 (.close 48)))) (.step 3 (.close 9))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 40 (.step 31 (.close 48)))))))) (.step 31 (.step 48 (.step 58 (.step 60 (.close 12)))))) (.step 31 (.step 3 (.close 38))))) (.step 21 (.step 48 (.step 57 (.step 31 (.close 48)))))))) (.step 18 (.step 4 (.close 38)))) (.step 3 (.step 9 (.step 32 (.step 40 (.step 48 (.step 38 (.step 55 (.close 38))))))))) (.step 3 (.step 9 (.step 21 (.step 52 (.step 55 (.step 40 (.step 57 (.step 58 (.step 75 (.split 34 0 (.step 55 (.step 40 (.step 62 (.step 31 (.close 52))))) (.step 15 (.step 31 (.close 26)))))))))))))) (.step 21 (.step 31 (.close 50)))) (.step 31 (.step 48 (.step 49 (.step 50 (.step 58 (.step 66 (.split 53 1 (.step 75 (.step 49 (.step 21 (.close 48)))) (.step 4 (.close 18)))))))))) (.step 31 (.step 38 (.close 3)))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911106083574306582052132529935986383138288548857386659384284838443660039607087599761959488597082799387706368⟩
def references : Fin 3 → Box := ![Part9.root, Part10.root, Part11.root]
def proof : Chunks.Proof 3 := (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 58 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.step 31 (.step 60 (.step 31 (.close 45)))) (.step 31 (.close 57))) (.step 4 (.step 31 (.close 12)))) (.step 31 (.close 55))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 50)))) (.step 31 (.close 49)))))) (.step 58 (.split 42 1 (.split 46 1 (.reuse 1) (.run (.step 21 (.step 31 (.step 48 (.step 28 (.step 41 (.step 49 (.step 3 (.step 60 (.split 55 1 (.split 35 0 (.split 36 0 (.split 38 2 (.split 42 0 (.split 54 1 (.step 49 (.close 3)) (.step 21 (.step 31 (.close 48)))) (.step 31 (.close 41))) (.step 41 (.close 49))) (.step 31 (.close 41))) (.step 31 (.close 32))) (.step 5 (.step 32 (.step 31 (.close 48))))))))))))))) (.run (.step 31 (.step 28 (.close 45))))))) (.run (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 57 1 (.step 31 (.close 39)) (.step 31 (.close 3))) (.step 31 (.close 57))) (.step 4 (.step 31 (.close 12)))) (.step 31 (.close 55))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 50)))) (.step 31 (.close 49))))) (.step 3 (.split 36 1 (.split 38 1 (.reuse 2) (.run (.step 3 (.step 31 (.close 38))))) (.run (.step 31 (.step 38 (.close 39)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739538960470844616265759130620345916945063435665667450302892920013824⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.split 36 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 54 1 (.split 57 1 (.step 31 (.close 37)) (.step 31 (.close 3))) (.step 31 (.close 57))) (.step 4 (.step 31 (.close 12)))) (.step 31 (.close 55))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 50)))) (.step 31 (.close 49))) (.step 7 (.step 31 (.close 37)))))) (.run (.step 31 (.split 35 1 (.step 18 (.split 38 1 (.split 46 1 (.split 47 1 (.step 3 (.step 7 (.close 18))) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 3 (.close 31)))) (.step 18 (.close 31)))))) (.run (.step 26 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.step 18 (.step 60 (.split 56 1 (.step 24 (.split 45 1 (.step 18 (.close 7)) (.step 4 (.close 18)))) (.step 3 (.close 18))))) (.step 18 (.close 23))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50)))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 49 (.step 41 (.close 50)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261670998793812400208127219938540346341717969465246720⟩
def references : Fin 1 → Box := ![Part13.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 48 (.step 55 (.split 35 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.step 24 (.split 50 1 (.split 55 1 (.split 56 1 (.split 57 1 (.step 3 (.step 31 (.split 59 1 (.split 72 1 (.split 52 1 (.split 54 1 (.step 24 (.step 3 (.step 4 (.close 3)))) (.step 4 (.step 3 (.close 57)))) (.step 3 (.step 18 (.step 4 (.close 55))))) (.step 4 (.step 18 (.close 31)))) (.step 18 (.step 48 (.close 62)))))) (.step 24 (.step 48 (.close 31)))) (.step 4 (.step 22 (.step 31 (.step 43 (.step 24 (.step 31 (.close 60)))))))) (.step 5 (.step 18 (.step 24 (.close 48))))) (.step 3 (.step 18 (.step 48 (.close 53)))))) (.step 3 (.step 18 (.step 48 (.close 52))))) (.step 21 (.step 50 (.step 24 (.step 31 (.step 48 (.close 3))))))) (.step 49 (.step 24 (.step 48 (.close 31))))) (.step 4 (.step 24 (.step 31 (.step 32 (.step 43 (.step 41 (.step 24 (.step 31 (.step 24 (.close 41))))))))))) (.step 18 (.step 21 (.step 4 (.step 31 (.close 38)))))))))) (.run (.step 22 (.step 48 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.step 18 (.step 56 (.split 56 1 (.step 24 (.split 57 1 (.step 18 (.close 7)) (.step 18 (.close 3)))) (.step 3 (.close 18))))) (.step 18 (.close 22))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50)))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 49 (.step 41 (.close 50))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨2658455991569831745807614123781914624, 16546956789305976592836116594320052230387700327664750565544908116064225529137780913988754437764756320749012540221796917587188165909538810750232204867313671849745090509369779145364089588024458015578517791657226322052096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 57 1 (.split 59 1 (.split 72 1 (.split 34 1 (.split 36 1 (.split 16 1 (.split 17 1 (.step 26 (.split 30 1 (.split 42 1 (.split 46 1 (.split 45 1 (.split 52 1 (.split 55 1 (.split 1 0 (.split 11 0 (.split 16 0 (.step 9 (.split 51 1 (.split 67 1 (.split 12 2 (.split 17 0 (.split 22 0 (.split 21 0 (.split 35 0 (.split 38 0 (.step 15 (.step 12 (.close 58))) (.step 12 (.step 15 (.close 3)))) (.step 15 (.close 31))) (.step 15 (.close 3))) (.step 3 (.step 26 (.close 15)))) (.step 18 (.step 22 (.step 15 (.close 48))))) (.split 38 0 (.step 15 (.close 3)) (.step 12 (.step 15 (.close 3))))) (.step 3 (.close 12))) (.step 3 (.close 12)))) (.step 21 (.step 3 (.step 18 (.close 15))))) (.split 38 0 (.split 46 0 (.step 15 (.close 3)) (.step 4 (.close 12))) (.step 4 (.close 15)))) (.split 38 0 (.split 46 0 (.step 15 (.step 3 (.close 4))) (.step 4 (.close 12))) (.step 3 (.step 4 (.close 31))))) (.step 12 (.step 48 (.step 3 (.close 15))))) (.step 55 (.close 15))) (.step 12 (.step 15 (.step 3 (.close 48))))) (.step 12 (.close 3))) (.step 31 (.close 3))) (.step 3 (.close 31)))) (.step 3 (.close 22))) (.step 4 (.close 18))) (.step 31 (.close 3))) (.step 15 (.close 31))) (.step 12 (.step 18 (.step 26 (.step 15 (.step 31 (.close 4))))))) (.step 3 (.step 9 (.step 12 (.step 21 (.step 22 (.step 26 (.step 15 (.step 12 (.step 48 (.close 3))))))))))) (.step 12 (.step 24 (.step 26 (.step 55 (.step 48 (.close 3))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨2658455991569831745807614123781914624, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087064672419618878037524715371401891021824⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.step 18 (.step 31 (.step 55 (.split 21 1 (.split 35 1 (.split 38 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 54 1 (.step 58 (.split 56 1 (.reuse 0) (.run (.step 3 (.step 16 (.step 31 (.step 48 (.step 15 (.step 48 (.close 4)))))))))) (.run (.step 12 (.step 21 (.step 22 (.step 26 (.step 48 (.step 57 (.split 55 1 (.split 57 1 (.split 30 0 (.step 57 (.close 4)) (.step 15 (.close 3))) (.step 12 (.step 26 (.step 15 (.close 3))))) (.step 12 (.step 15 (.close 4)))))))))))) (.run (.step 4 (.step 24 (.step 48 (.step 12 (.step 4 (.close 15)))))))) (.run (.step 21 (.step 22 (.step 26 (.step 48 (.step 55 (.step 57 (.step 15 (.step 53 (.step 3 (.close 15)))))))))))) (.run (.step 12 (.step 15 (.step 26 (.close 52)))))) (.run (.step 12 (.step 21 (.step 24 (.step 55 (.step 59 (.step 75 (.split 54 1 (.split 57 1 (.split 56 1 (.step 48 (.close 3)) (.step 22 (.close 48))) (.step 26 (.step 48 (.close 4)))) (.step 48 (.close 15))))))))))) (.run (.step 3 (.step 4 (.step 10 (.step 16 (.step 21 (.step 31 (.step 48 (.step 57 (.step 58 (.step 15 (.close 41))))))))))))) (.run (.step 12 (.step 21 (.step 22 (.step 26 (.step 38 (.step 48 (.step 57 (.step 15 (.step 31 (.close 48)))))))))))) (.run (.step 12 (.step 4 (.step 15 (.step 3 (.step 18 (.close 15)))))))))))
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
def root : Box := ⟨2596148429267413814265251385835520, 16546956789305976592836116594320052230387700327672298497592809837638999178832786663099665256417547630317846217174625000275507766211131203550675177249184593293255382217867136223992630058287343032408018244651728651682816⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 56 1 (.split 57 1 (.step 3 (.split 59 1 (.split 72 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 45 1 (.split 49 1 (.split 55 1 (.split 1 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 24 (.split 34 0 (.split 36 0 (.split 38 0 (.step 24 (.step 3 (.step 4 (.close 12)))) (.step 3 (.close 4))) (.step 3 (.close 4))) (.step 3 (.close 31)))) (.step 3 (.step 12 (.step 4 (.close 14))))) (.step 18 (.step 3 (.close 12)))) (.step 18 (.step 14 (.close 3)))) (.step 24 (.split 34 0 (.split 35 0 (.step 3 (.step 12 (.step 4 (.close 3)))) (.step 4 (.close 12))) (.step 3 (.close 4))))) (.step 24 (.step 14 (.close 4)))) (.step 12 (.step 18 (.close 48)))) (.step 3 (.close 34))) (.step 4 (.step 18 (.close 48)))) (.step 3 (.close 31))) (.step 4 (.close 31))) (.step 4 (.close 31))) (.step 18 (.step 4 (.close 31)))) (.step 3 (.step 18 (.close 48))))) (.step 12 (.step 44 (.step 51 (.step 60 (.split 45 1 (.split 1 0 (.split 10 0 (.split 11 2 (.split 16 0 (.split 17 0 (.split 21 0 (.split 30 0 (.step 24 (.step 8 (.close 60))) (.step 3 (.close 4))) (.step 12 (.step 14 (.close 24)))) (.step 18 (.close 24))) (.step 18 (.close 24))) (.step 60 (.step 3 (.close 4)))) (.step 12 (.step 3 (.close 14)))) (.step 8 (.step 12 (.step 14 (.close 4))))) (.step 4 (.step 12 (.step 18 (.close 48)))))))))) (.step 31 (.step 51 (.step 43 (.step 24 (.step 60 (.step 3 (.step 31 (.close 14))))))))) (.step 4 (.step 12 (.step 15 (.close 24))))))
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
def root : Box := ⟨2596148429267413814265251385835520, 16546956789305976592836116594320052230387700327672298497599846255247179835012538514558915415797468561955000385785401110677558802998877685501390141965059705724848837587184549534005593536779487931015846386291793532552192⟩
def references : Fin 1 → Box := ![Part17.root]
def proof : Chunks.Proof 1 := (.split 46 1 (.split 47 1 (.split 50 1 (.step 24 (.split 52 1 (.split 53 1 (.reuse 0) (.run (.step 8 (.step 24 (.step 34 (.step 51 (.split 36 1 (.split 42 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 34 0 (.split 35 0 (.step 8 (.step 56 (.close 3))) (.step 18 (.close 14))) (.step 18 (.close 14))) (.step 4 (.close 14))) (.step 3 (.close 14))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.close 14))) (.step 3 (.step 4 (.close 14)))) (.step 3 (.step 4 (.close 14)))))))))) (.run (.step 3 (.step 48 (.close 14)))))) (.run (.step 3 (.step 15 (.step 18 (.step 34 (.step 48 (.close 14)))))))) (.run (.step 8 (.step 12 (.step 24 (.step 50 (.step 51 (.step 60 (.step 69 (.split 45 1 (.split 53 1 (.split 72 1 (.split 1 0 (.split 10 0 (.split 11 2 (.split 17 0 (.split 21 0 (.split 22 0 (.split 45 0 (.step 50 (.close 3)) (.step 4 (.close 50))) (.step 18 (.close 24))) (.step 12 (.step 14 (.close 24)))) (.step 18 (.close 24))) (.step 50 (.close 14))) (.step 12 (.step 3 (.close 14)))) (.step 12 (.step 14 (.close 4)))) (.step 4 (.close 14))) (.step 14 (.close 4))) (.step 4 (.step 12 (.step 14 (.step 18 (.close 48))))))))))))))) (.run (.step 12 (.step 14 (.step 34 (.close 49))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part17.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087064675018302608505394988439643462042624⟩
def references : Fin 3 → Box := ![Part14.root, Part16.root, Part18.root]
def proof : Chunks.Proof 3 := (.split 10 1 (.split 11 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 21 (.split 17 1 (.step 48 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.step 18 (.step 56 (.split 56 1 (.step 24 (.split 57 1 (.step 18 (.close 7)) (.step 18 (.close 3)))) (.step 3 (.close 18))))) (.step 18 (.close 21))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50)))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 41 (.close 49)))))) (.step 18 (.step 7 (.close 19))))))) (.reuse 1)) (.step 24 (.step 31 (.step 48 (.step 58 (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 38 1 (.reuse 2) (.run (.step 4 (.step 14 (.step 31 (.step 41 (.step 49 (.step 50 (.step 60 (.split 1 0 (.split 12 0 (.split 16 0 (.step 43 (.split 17 0 (.split 56 1 (.split 34 0 (.step 24 (.step 43 (.step 24 (.step 41 (.close 14))))) (.step 4 (.step 14 (.close 31)))) (.step 41 (.close 3))) (.step 3 (.close 14)))) (.step 3 (.step 5 (.close 14)))) (.step 4 (.close 14))) (.step 4 (.close 14)))))))))))) (.run (.step 15 (.step 18 (.step 31 (.step 4 (.step 12 (.close 14)))))))) (.run (.step 14 (.step 18 (.close 3))))) (.run (.step 18 (.step 3 (.close 14))))) (.run (.step 18 (.step 3 (.close 19))))) (.run (.step 4 (.step 12 (.step 15 (.step 24 (.close 3)))))))))))) (.run (.step 31 (.split 11 1 (.split 12 1 (.split 35 1 (.step 18 (.split 38 1 (.split 46 1 (.split 47 1 (.step 3 (.step 7 (.close 18))) (.step 18 (.close 31))) (.step 18 (.close 31))) (.step 3 (.close 31)))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.close 14))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes
  · exact Part16.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700327672302183110026745033656633405684013822609101743460685252184967911110563063790941734625597489519692563739542251479959261673921797087064675018302608505394988439643462044672⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 1 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 48 (.split 11 1 (.split 12 1 (.split 35 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 4 (.step 57 (.step 58 (.split 59 1 (.step 31 (.step 4 (.step 3 (.close 75)))) (.step 3 (.step 26 (.step 48 (.close 12)))))))) (.step 31 (.step 48 (.step 4 (.close 60))))) (.step 3 (.step 31 (.step 4 (.close 32))))) (.step 4 (.close 56))) (.step 3 (.step 23 (.step 48 (.close 55))))) (.step 3 (.step 40 (.step 48 (.step 53 (.step 4 (.step 53 (.close 57)))))))) (.step 3 (.step 12 (.step 40 (.step 48 (.step 52 (.step 53 (.step 4 (.step 52 (.close 57)))))))))) (.step 31 (.step 48 (.step 50 (.close 4))))) (.step 31 (.step 48 (.step 49 (.close 4))))) (.step 3 (.step 4 (.step 31 (.step 24 (.step 32 (.step 41 (.close 4)))))))) (.step 4 (.step 38 (.step 40 (.step 31 (.step 4 (.close 49))))))) (.step 12 (.step 4 (.step 15 (.close 31))))) (.step 4 (.close 14)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part20.excludes
end FiveColour.Packed.ProjectedChunks.Case93
