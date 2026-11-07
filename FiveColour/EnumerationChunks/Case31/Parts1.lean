module
public import FiveColour.EnumerationChunks.Case31.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case31
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part769
def root : Box := ⟨3351951982485649274896348235987935367100909329686845005226912708932701219507936485770598561382226623186123938312878255780988296694222081147733111837032448, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669246286629248372991933630276348057566455731943059606010109978331646635424651576590915862528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.step 46 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 18 (.split 6 0 (.step 68 (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 68)))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 55 (.run (.close 9)))) (.step 55 (.split 46 0 (.step 71 (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 71)))))) (.step 55 (.step 3 (.split 46 0 (.step 71 (.run (.close 29))) (.step 2 (.run (.close 71))))))) (.step 55 (.run (.close 27)))) (.step 55 (.split 46 0 (.step 63 (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))))) (.step 55 (.step 3 (.split 46 0 (.step 63 (.run (.close 11))) (.step 2 (.run (.close 55))))))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 68 (.step 55 (.split 26 0 (.split 35 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68))))))) (.step 2 (.run (.close 3)))) (.step 68 (.step 55 (.split 49 0 (.step 18 (.run (.close 3))) (.step 71 (.run (.close 68))))))) (.step 68 (.step 55 (.split 4 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 71 (.run (.close 68)))) (.step 2 (.run (.close 29))))))) (.step 2 (.step 71 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part769
namespace Part770
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
end Part770
namespace Part771
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797369505676280601061248670718155620945908532829124217007722778424001770241878230375801552896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114141043902368428812648239333376⟩
def references : Fin 1 → Box := ![Part770.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.reuse 0) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 33))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 3 (.step 55 (.step 31 (.step 27 (.run (.close 2))))))) (.step 2 (.step 71 (.step 63 (.step 18 (.run (.close 68))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.step 53 (.run (.close 18))))) (.step 2 (.run (.close 9)))))) (.step 2 (.step 68 (.step 55 (.run (.close 31)))))) (.step 3 (.step 55 (.step 31 (.step 27 (.run (.close 2))))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 3 (.step 57 (.run (.close 7))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part770.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
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
end Part772
namespace Part773
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142280632300150036071945601024⟩
def references : Fin 1 → Box := ![Part772.root]
def proof : Enumeration.Proof 1 := (.split 11 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.reuse 0) (.step 2 (.step 68 (.run (.close 48))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.step 3 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 3 (.run (.close 31))))) (.step 3 (.step 52 (.run (.close 31))))) (.step 2 (.run (.close 27)))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 55 (.step 18 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 2 (.step 71 (.step 18 (.run (.close 68)))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 18 (.step 55 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 3 (.step 55 (.step 31 (.step 27 (.split 4 0 (.step 36 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 15)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 68 (.run (.close 27))))) (.step 3 (.step 52 (.run (.close 18))))) (.step 2 (.run (.close 9)))))) (.step 2 (.step 68 (.step 55 (.run (.close 31))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part772.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part773
namespace Part774
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 4 → Box := ![Part768.root, Part769.root, Part771.root, Part773.root]
def proof : Enumeration.Proof 4 := (.split 9 0 (.split 29 0 (.split 44 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.step 68 (.step 55 (.split 8 0 (.split 14 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))))) (.step 68 (.step 55 (.split 4 0 (.split 8 0 (.split 14 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68))))))) (.step 68 (.step 55 (.split 4 0 (.split 8 0 (.split 10 0 (.split 30 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 11))))))) (.step 2 (.step 71 (.run (.close 55))))) (.step 2 (.step 71 (.run (.close 55)))))) (.reuse 2)) (.split 6 0 (.split 7 0 (.split 8 0 (.reuse 3) (.step 3 (.step 55 (.step 31 (.step 27 (.split 4 0 (.step 36 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 3 (.step 57 (.run (.close 7)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part768.covered
  · exact Part769.covered
  · exact Part771.covered
  · exact Part773.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part774
namespace Part775
def root : Box := ⟨1073741824, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 5 → Box := ![Part640.root, Part735.root, Part740.root, Part747.root, Part774.root]
def proof : Enumeration.Proof 5 := (.split 43 0 (.reuse 0) (.split 51 0 (.split 61 0 (.split 25 0 (.reuse 1) (.split 34 0 (.reuse 2) (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 49 0 (.split 50 0 (.split 6 0 (.step 28 (.step 29 (.run (.close 2)))) (.step 2 (.run (.close 28)))) (.step 71 (.step 2 (.run (.close 71))))) (.step 58 (.run (.close 2)))) (.step 71 (.step 43 (.run (.close 28))))) (.step 5 (.step 43 (.run (.close 28))))) (.step 5 (.step 43 (.run (.close 28))))) (.step 2 (.run (.close 4)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.step 55 (.step 58 (.step 2 (.run (.close 4))))))) (.step 2 (.run (.close 4)))) (.step 71 (.step 55 (.step 58 (.step 43 (.run (.close 2))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))) (.reuse 3)) (.reuse 4)))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part640.covered
  · exact Part735.covered
  · exact Part740.covered
  · exact Part747.covered
  · exact Part774.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part775
end FiveColour.Packed.EnumerationChunks.Case31
