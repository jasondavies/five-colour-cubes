module
public import FiveColour.EnumerationChunks.Case32.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case32
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part770
def root : Box := ⟨3351951982485652252024923737026979342715018142828855200029607172622291296318817758578573301640927606626674728096592153736305067360462419647908513105051648, 5789234136395753406676424723379602756368638487163863180229018976102161271192821577321572392130949074755990688842026015136763309749320583304879412656082945267809425319000247902309682380141234764420731412381180731860818329600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 6 0 (.split 74 0 (.split 42 0 (.split 72 0 (.split 66 0 (.split 71 0 (.split 12 0 (.split 24 0 (.step 2 (.run (.close 5))) (.step 68 (.step 5 (.step 2 (.run (.close 31)))))) (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 58 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 55 (.step 68 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 58 (.step 71 (.step 68 (.run (.close 2)))))) (.step 68 (.step 58 (.step 55 (.run (.close 28)))))) (.step 2 (.run (.close 68)))) (.step 68 (.step 55 (.step 2 (.run (.close 48)))))) (.step 68 (.step 55 (.step 48 (.run (.close 2)))))) (.step 68 (.step 55 (.step 48 (.run (.close 2)))))) (.step 55 (.step 68 (.step 63 (.run (.close 48)))))) (.step 2 (.run (.close 68))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part770
namespace Part771
def root : Box := ⟨4562440617622195218641171605700291324896580459231045579854086026921496322861362087539475093804885993576009825956929369225368753910538471660800792324243241805105011242454462553973054434546024448, 5789234136395753406676424723384165196986260682382504351834719267427054499700070137252151584648848349923199366228531927948080681149099225614453007063393633972530800756998500563629404594329486759095091677331263606053064933376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 8 0 (.split 66 0 (.split 71 0 (.split 7 0 (.split 13 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 50 0 (.split 30 0 (.step 3 (.step 53 (.step 9 (.run (.close 2))))) (.step 31 (.run (.close 53)))) (.step 65 (.run (.close 53)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 63 (.step 68 (.run (.close 57)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 68 (.step 63 (.step 2 (.run (.close 24)))))) (.step 68 (.step 71 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 68 (.step 63 (.step 68 (.run (.close 2)))))) (.step 68 (.step 55 (.step 63 (.run (.close 11)))))) (.step 68 (.step 55 (.step 63 (.step 11 (.run (.close 2))))))) (.step 68 (.step 63 (.step 55 (.run (.close 2)))))) (.step 68 (.step 63 (.step 48 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
def root : Box := ⟨4455508415646675018204269146191690750317995446595571082099751715482166558161925043821962967316714304963846763777925203069393627367501863718299619091068841646231406643377550130495549127786496, 5789234136395753406676424723384169652494676329057522556103865459117801465743534247173958790891541610934104843452542187628560483269606821944833450026682023316969005225199670732243974635554278675859426223570595662835904151552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 66 0 (.split 8 0 (.split 14 0 (.split 64 0 (.split 71 0 (.split 7 0 (.split 13 0 (.split 18 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 19 0 (.split 23 0 (.split 31 0 (.step 54 (.step 46 (.step 54 (.step 2 (.run (.close 23)))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 3)))) (.step 18 (.run (.close 3)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 18 (.run (.close 3))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.run (.close 52)))) (.step 55 (.step 63 (.step 68 (.run (.close 11)))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 63 (.step 2 (.run (.close 24)))))) (.step 68 (.step 71 (.step 55 (.step 71 (.run (.close 68))))))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 68 (.step 63 (.step 55 (.step 68 (.run (.close 2))))))) (.step 68 (.step 55 (.step 63 (.run (.close 11)))))) (.step 68 (.step 55 (.step 63 (.step 11 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part772
namespace Part773
def root : Box := ⟨3351951985607397825209501253602752882477867339310880630179564948226673342960333653499814809283339765611622975680854547974423190989645579569468527605710848, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509106883772992531334636618847936226703148240757681101793075398420843082589125531302734224215134462485401380556536305253183209645199589376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.step 54 (.step 2 (.run (.close 23)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 55 (.run (.close 54)))) (.step 55 (.step 18 (.split 6 0 (.step 68 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2))))))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 55 (.step 3 (.step 71 (.run (.close 68)))))) (.step 2 (.run (.close 68)))) (.step 55 (.run (.close 27)))) (.step 55 (.step 3 (.step 63 (.run (.close 68)))))) (.step 2 (.step 68 (.run (.close 55))))) (.step 2 (.run (.close 68)))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 2 (.run (.close 68)))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 68 (.step 55 (.split 4 0 (.step 18 (.run (.close 3))) (.step 2 (.run (.close 29))))))) (.step 2 (.run (.close 9)))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.split 46 0 (.step 11 (.run (.close 54))) (.step 2 (.run (.close 48))))))) (.step 2 (.step 68 (.run (.close 63))))) (.step 2 (.step 68 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part773
namespace Part774
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509106883772992531334636618847936226703148240757681101793075398420843082589125531302734224215134462485401380556536305253183209645199589376⟩
def references : Fin 12 → Box := ![Part760.root, Part761.root, Part763.root, Part765.root, Part766.root, Part767.root, Part768.root, Part769.root, Part770.root, Part771.root, Part772.root, Part773.root]
def proof : Enumeration.Proof 12 := (.split 48 0 (.split 63 0 (.split 64 0 (.split 46 0 (.split 47 0 (.split 66 0 (.split 71 0 (.split 57 0 (.split 61 0 (.split 62 0 (.split 18 0 (.split 19 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 58 0 (.split 41 0 (.split 4 0 (.step 22 (.split 10 0 (.step 9 (.run (.close 2))) (.step 18 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 9)))) (.step 3 (.run (.close 40)))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 7)))) (.step 68 (.step 3 (.run (.close 11))))) (.step 2 (.step 68 (.run (.close 27))))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.step 68 (.run (.close 54))))) (.step 2 (.step 68 (.run (.close 9)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)) (.reuse 7)) (.reuse 8)) (.reuse 9)) (.split 5 0 (.split 11 0 (.reuse 10) (.step 68 (.step 63 (.step 55 (.run (.close 2)))))) (.step 68 (.step 63 (.step 48 (.run (.close 55))))))) (.reuse 11))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part760.covered
  · exact Part761.covered
  · exact Part763.covered
  · exact Part765.covered
  · exact Part766.covered
  · exact Part767.covered
  · exact Part768.covered
  · exact Part769.covered
  · exact Part770.covered
  · exact Part771.covered
  · exact Part772.covered
  · exact Part773.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part774
namespace Part775
def root : Box := ⟨3351951982485649274896348235987935367100909329686845005226912708932701219507936485770598561382226623186123938312878255780988296694222081147733111837032448, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669246286629248372991933631961344724263370719109748048948836895433968161833437356659891503104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.step 46 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 18 (.split 6 0 (.step 68 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2)))))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 55 (.run (.close 9)))) (.step 55 (.split 46 0 (.step 71 (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 71)))))) (.step 2 (.run (.close 68)))) (.step 55 (.run (.close 27)))) (.step 55 (.split 46 0 (.step 63 (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))))) (.step 2 (.step 68 (.run (.close 55))))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 68 (.step 55 (.split 35 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68))))))) (.step 2 (.run (.close 68)))) (.step 68 (.step 55 (.split 10 0 (.split 30 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))))) (.step 68 (.step 55 (.split 4 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 71 (.run (.close 68)))) (.step 2 (.run (.close 29))))))) (.step 2 (.run (.close 9)))) (.step 68 (.step 55 (.split 8 0 (.split 14 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part775
namespace Part776
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797369505676280601061248670718155620945908532829124217007722778424001770241878230375801552896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144058495722242433610700744189317322955345060370443038584064104781633666919992801971052555733683981124213145600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 70 0 (.split 72 0 (.split 73 0 (.split 74 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 55))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.step 18 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 33 (.step 68 (.step 54 (.run (.close 31))))) (.step 2 (.run (.close 68)))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.step 68 (.run (.close 18)))))) (.step 2 (.run (.close 7)))) (.step 55 (.step 31 (.step 27 (.run (.close 2)))))) (.step 2 (.step 63 (.run (.close 16))))) (.step 55 (.step 18 (.step 9 (.run (.close 2)))))) (.step 2 (.step 71 (.step 63 (.run (.close 40)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 53 (.step 27 (.run (.close 2))))) (.step 3 (.run (.close 54)))) (.step 2 (.run (.close 27)))))) (.step 2 (.step 68 (.run (.close 58))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.run (.close 54)))) (.step 2 (.run (.close 9)))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 53 (.step 27 (.run (.close 2))))) (.step 3 (.step 53 (.run (.close 31))))) (.step 2 (.run (.close 27)))))) (.step 2 (.step 68 (.run (.close 18)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part776
namespace Part777
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797369505676280601061248670718155620945908532829124217007722778424001770241878230375801552896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114141043902368428812648239333376⟩
def references : Fin 1 → Box := ![Part776.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.reuse 0) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 33))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 2 (.step 55 (.run (.close 29))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 53 (.step 27 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 55 (.step 31 (.step 27 (.run (.close 2))))))) (.step 2 (.step 3 (.step 71 (.run (.close 23)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.step 53 (.run (.close 18))))) (.step 2 (.run (.close 9)))))) (.step 2 (.step 55 (.run (.close 27))))) (.step 2 (.step 55 (.run (.close 27))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part776.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part777
namespace Part778
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103865455603025063756665194851775900593313432069095654962749732364432414704606175394330030715407794849028545452662143180792447813219870687369169152680326131469646823424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 54 0 (.split 56 0 (.split 58 0 (.split 70 0 (.split 72 0 (.split 73 0 (.split 74 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 55))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.step 18 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 13 (.run (.close 2))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13))))) (.step 2 (.run (.close 7)))) (.step 55 (.step 31 (.step 27 (.split 4 0 (.step 36 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68)))))))) (.step 2 (.step 63 (.run (.close 16))))) (.step 55 (.step 18 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 2 (.step 71 (.step 63 (.run (.close 40)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 27))))) (.step 3 (.run (.close 13)))) (.step 2 (.run (.close 27)))))) (.step 2 (.step 68 (.run (.close 58))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 13)))) (.step 2 (.run (.close 9))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part778
namespace Part779
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502513868588072281082720339096387582951424⟩
def references : Fin 1 → Box := ![Part778.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.reuse 0) (.step 2 (.step 68 (.run (.close 48))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.step 3 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 3 (.run (.close 31))))) (.step 3 (.step 52 (.run (.close 31))))) (.step 2 (.run (.close 27)))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 55 (.step 18 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 2 (.step 71 (.step 18 (.run (.close 68)))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 2 (.step 55 (.run (.close 29))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 3 (.run (.close 31)))) (.step 68 (.run (.close 27))))) (.step 2 (.run (.close 3)))) (.step 31 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 55 (.step 31 (.step 27 (.split 4 0 (.step 36 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part778.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part779
namespace Part780
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 4 → Box := ![Part774.root, Part775.root, Part777.root, Part779.root]
def proof : Enumeration.Proof 4 := (.split 9 0 (.split 29 0 (.split 44 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.reuse 1) (.step 68 (.step 55 (.split 4 0 (.split 8 0 (.split 14 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68))))))) (.step 68 (.step 55 (.split 4 0 (.split 8 0 (.split 10 0 (.split 30 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 31)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 11))))))) (.step 2 (.step 68 (.run (.close 63))))) (.step 2 (.step 68 (.run (.close 63)))))) (.reuse 2)) (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.reuse 3) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 15)))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 68 (.run (.close 27))))) (.step 3 (.step 52 (.run (.close 18))))) (.step 2 (.run (.close 9)))))) (.step 2 (.step 55 (.run (.close 27))))) (.step 2 (.step 55 (.run (.close 27))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 12 0 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 15)))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 68 (.run (.close 27)))) (.step 9 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part774.covered
  · exact Part775.covered
  · exact Part777.covered
  · exact Part779.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part780
namespace Part781
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 12 → Box := ![Part681.root, Part683.root, Part694.root, Part696.root, Part709.root, Part715.root, Part721.root, Part726.root, Part739.root, Part745.root, Part752.root, Part780.root]
def proof : Enumeration.Proof 12 := (.split 51 0 (.split 61 0 (.split 25 0 (.split 34 0 (.split 5 0 (.split 11 0 (.split 62 0 (.split 67 0 (.split 4 0 (.split 10 0 (.split 69 0 (.reuse 0) (.split 44 0 (.split 48 0 (.split 63 0 (.reuse 1) (.split 35 0 (.split 36 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 49 0 (.split 50 0 (.split 56 0 (.split 7 0 (.split 13 0 (.step 31 (.split 64 0 (.split 71 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 3)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2)))))) (.step 2 (.step 68 (.step 63 (.run (.close 55)))))) (.step 2 (.step 68 (.step 63 (.run (.close 55))))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)) (.reuse 7)) (.reuse 8)) (.reuse 9)) (.reuse 10)) (.reuse 11))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part681.covered
  · exact Part683.covered
  · exact Part694.covered
  · exact Part696.covered
  · exact Part709.covered
  · exact Part715.covered
  · exact Part721.covered
  · exact Part726.covered
  · exact Part739.covered
  · exact Part745.covered
  · exact Part752.covered
  · exact Part780.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part781
namespace Part782
def root : Box := ⟨1073741824, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 10 → Box := ![Part347.root, Part368.root, Part371.root, Part372.root, Part373.root, Part398.root, Part493.root, Part527.root, Part644.root, Part781.root]
def proof : Enumeration.Proof 10 := (.split 43 0 (.split 51 0 (.split 25 0 (.split 34 0 (.split 5 0 (.split 11 0 (.reuse 0) (.split 16 0 (.reuse 1) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 7 0 (.reuse 2) (.step 2 (.step 4 (.run (.close 11))))) (.split 24 0 (.split 36 0 (.split 49 0 (.split 50 0 (.split 42 0 (.split 67 0 (.split 59 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 63 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 48 (.step 2 (.run (.close 4))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 24))))) (.step 4 (.step 58 (.step 48 (.step 24 (.run (.close 27)))))))) (.step 2 (.step 63 (.step 4 (.run (.close 61)))))) (.step 2 (.step 63 (.step 4 (.run (.close 61)))))) (.step 2 (.step 63 (.step 4 (.run (.close 61)))))) (.reuse 3)) (.reuse 4)))) (.reuse 5)) (.reuse 6)) (.reuse 7)) (.reuse 8)) (.reuse 9))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part347.covered
  · exact Part368.covered
  · exact Part371.covered
  · exact Part372.covered
  · exact Part373.covered
  · exact Part398.covered
  · exact Part493.covered
  · exact Part527.covered
  · exact Part644.covered
  · exact Part781.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part782
end FiveColour.Packed.EnumerationChunks.Case32
