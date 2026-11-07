module
public import FiveColour.EnumerationChunks.Case51.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case51
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part769
def root : Box := ⟨2521728396569246669585858566409191283525105122561182919814244271168366954124381686474023440946447717536374316096028672, 5789234136395753406676424723384169652494676329057522556103865459117798113791554880221674516131288568873115290626484525656927987913387999487623977889060275329812177992142431328974647234147722693243630337993167570572329091072⟩
def references : Fin 1 → Box := ![Part768.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 13 0 (.split 49 0 (.split 50 0 (.split 67 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 42 0 (.split 53 0 (.split 56 0 (.step 32 (.split 57 0 (.step 9 (.step 55 (.run (.close 2)))) (.step 58 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 4)))))) (.split 42 0 (.split 53 0 (.split 56 0 (.split 57 0 (.split 14 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 61 0 (.split 31 0 (.step 21 (.step 27 (.step 2 (.run (.close 4))))) (.step 3 (.step 40 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 58 (.step 40 (.run (.close 55)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 23 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 3)))) (.step 58 (.step 4 (.step 2 (.run (.close 63))))))) (.split 14 0 (.split 58 0 (.split 67 0 (.split 74 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 5))) (.step 58 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.step 58 (.run (.close 2))))))) (.split 13 0 (.split 42 0 (.split 56 0 (.split 73 0 (.split 53 0 (.split 57 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 23)))) (.step 63 (.step 58 (.step 2 (.run (.close 5)))))) (.step 2 (.run (.close 23)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part768.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part769
namespace Part770
def root : Box := ⟨1811018241397843937822879938261491478723170994297509432074646356326009012224, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396365663482762687255876623024143773432430129058029392166797669152521943140343802968920888888427394283552275066804764672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 39 0 (.split 46 0 (.split 47 0 (.split 7 0 (.split 8 0 (.split 13 0 (.split 49 0 (.split 50 0 (.split 67 0 (.split 42 0 (.split 35 0 (.step 2 (.run (.close 23))) (.split 59 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2))))) (.split 53 0 (.split 26 0 (.split 35 0 (.split 56 0 (.step 3 (.step 18 (.split 73 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 63)))))) (.step 2 (.run (.close 63)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 4))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.step 3 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.split 42 0 (.split 56 0 (.split 57 0 (.split 35 0 (.split 44 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 23)))) (.step 4 (.step 55 (.step 2 (.run (.close 55)))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 58 (.run (.close 2))))) (.split 42 0 (.split 56 0 (.split 57 0 (.split 35 0 (.split 44 0 (.step 27 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 4 (.step 58 (.run (.close 29))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 58 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.split 42 0 (.split 46 0 (.split 47 0 (.split 7 0 (.split 13 0 (.split 56 0 (.split 57 0 (.split 44 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 58 (.step 5 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part770
namespace Part771
def root : Box := ⟨2037035976334487895519840021474931654348109154414496457979650849988194416288086830899789824, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397711580715241241531899777877101102329312925606294096718972923657656635828941903898763846203108505812397482573824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 49 0 (.split 50 0 (.split 67 0 (.split 8 0 (.split 58 0 (.split 59 0 (.split 14 0 (.step 2 (.run (.close 4))) (.split 27 0 (.split 32 0 (.step 63 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 26 0 (.split 35 0 (.step 18 (.run (.close 2))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.step 2 (.run (.close 71)))))) (.split 35 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 27 0 (.split 54 0 (.split 32 0 (.step 63 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.split 8 0 (.split 14 0 (.split 6 0 (.split 12 0 (.split 19 0 (.step 58 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
def root : Box := ⟨2037035976334487895519840021474931654348109154414496457979650849988194416288086830899789824, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002241945623794081911176891620457795220242729422705890543162187237556224⟩
def references : Fin 1 → Box := ![Part771.root]
def proof : Enumeration.Proof 1 := (.split 9 0 (.split 18 0 (.split 24 0 (.split 39 0 (.reuse 0) (.split 62 0 (.split 69 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.step 5 (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.step 5 (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 5))))) (.step 2 (.run (.close 4))))) (.split 8 0 (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 35 0 (.split 39 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 48 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 18 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 68 (.step 43 (.step 2 (.run (.close 71)))))) (.step 68 (.step 63 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part771.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part772
namespace Part773
def root : Box := ⟨1809251396018062220190211627927437003146070427502955339525310530193692033024, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397711580715241241531897740841124767843226657162290684007508787176429658335629994675416813348217528255760274817024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 67 0 (.split 35 0 (.step 2 (.run (.close 4))) (.split 74 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.step 43 (.step 3 (.split 13 0 (.split 26 0 (.step 43 (.step 58 (.run (.close 23)))) (.step 4 (.run (.close 29)))) (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.step 3 (.split 26 0 (.split 35 0 (.step 51 (.step 43 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part773
namespace Part774
def root : Box := ⟨1809251396018062220190211627927437003146070427502955339525310530193692033024, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390464150032408292946541733797942211082616242200123777075624952672354001601776661486152947073024⟩
def references : Fin 1 → Box := ![Part773.root]
def proof : Enumeration.Proof 1 := (.split 24 0 (.split 39 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 6 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 58)))) (.step 68 (.step 63 (.run (.close 58))))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 6 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 58)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part773.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part774
namespace Part775
def root : Box := ⟨1809251396018062220190211627927437003146070427502955339525310530193692033024, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778826164058308900733947159831744232299328942256213196800⟩
def references : Fin 1 → Box := ![Part774.root]
def proof : Enumeration.Proof 1 := (.split 30 0 (.split 9 0 (.split 18 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 23 0 (.split 59 0 (.split 12 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 48 (.run (.close 2)))) (.step 63 (.step 48 (.run (.close 2))))) (.step 68 (.run (.close 26)))) (.step 63 (.step 48 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 35 0 (.split 39 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.split 6 0 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 26 0 (.step 5 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.run (.close 5)))) (.step 18 (.run (.close 2)))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 48 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 18 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 5))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part774.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part775
namespace Part776
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524750124716392448, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778826164058308900733947159831744232299328942256213196800⟩
def references : Fin 5 → Box := ![Part767.root, Part769.root, Part770.root, Part772.root, Part775.root]
def proof : Enumeration.Proof 5 := (.split 22 0 (.split 30 0 (.split 24 0 (.split 39 0 (.reuse 0) (.split 38 0 (.split 46 0 (.split 47 0 (.split 7 0 (.reuse 1) (.split 8 0 (.split 14 0 (.split 58 0 (.split 67 0 (.split 74 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 5))) (.step 58 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.step 58 (.run (.close 2)))))) (.step 2 (.run (.close 23))))) (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 67 0 (.split 14 0 (.step 2 (.run (.close 5))) (.step 58 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 48 (.step 2 (.run (.close 4))))))) (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 67 0 (.split 14 0 (.step 2 (.run (.close 5))) (.step 58 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 48 (.step 2 (.run (.close 4))))))) (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 67 0 (.split 14 0 (.step 2 (.run (.close 5))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 5 (.run (.close 2))))))) (.split 38 0 (.reuse 2) (.step 2 (.run (.close 29))))) (.reuse 3)) (.reuse 4))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part767.covered
  · exact Part769.covered
  · exact Part770.covered
  · exact Part772.covered
  · exact Part775.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part776
namespace Part777
def root : Box := ⟨1809251394333065553493298137338425187051931750973902514590336877799640399872, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397711580715241241531897740841124767843226657160605687340811873685840646519535855998887760523282554603366223183872⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 67 0 (.split 35 0 (.step 2 (.run (.close 4))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.step 43 (.step 3 (.split 13 0 (.split 26 0 (.step 43 (.step 58 (.run (.close 23)))) (.step 4 (.run (.close 29)))) (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.step 3 (.split 26 0 (.split 35 0 (.step 51 (.step 43 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part777
namespace Part778
def root : Box := ⟨1809251394333065553493298137338425187051931750973902514590336877799640399872, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390464150032408292946541733796257214415919328709534765259530813995824948776841687833758895439872⟩
def references : Fin 1 → Box := ![Part777.root]
def proof : Enumeration.Proof 1 := (.split 24 0 (.split 39 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 6 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 58)))) (.step 68 (.step 63 (.run (.close 58))))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 6 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 58)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part777.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part778
namespace Part779
def root : Box := ⟨1809251394333065553493298137338425187051931750973902514590336877799640399872, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002241945623794081912673469297084639808483302691407364355289862161563648⟩
def references : Fin 1 → Box := ![Part778.root]
def proof : Enumeration.Proof 1 := (.split 30 0 (.split 9 0 (.split 18 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 19 0 (.split 58 0 (.split 12 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 23)))) (.step 48 (.run (.close 2)))) (.step 63 (.step 48 (.run (.close 2))))) (.step 68 (.step 43 (.run (.close 2))))) (.step 63 (.step 48 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 35 0 (.split 39 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.split 6 0 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 26 0 (.step 5 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.run (.close 5)))) (.step 18 (.run (.close 2)))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 48 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 18 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 5))))))
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
def root : Box := ⟨1809251394333065553493296642222250197538246428604318645832807769780648935424, 5789234136395753406676424723384169652494676329053565269680295786572830070178653249821006668570220696325861482986496614572383011715401533601354702058167099539516143335941077420821216605634298546974351090857375529510683803648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 59 0 (.split 67 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 27 0 (.split 35 0 (.step 2 (.run (.close 4))) (.split 61 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 8 0 (.step 50 (.step 29 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.split 61 0 (.split 62 0 (.split 69 0 (.split 7 0 (.split 13 0 (.step 47 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 63 (.step 2 (.run (.close 4)))))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 63 (.step 2 (.run (.close 4)))))) (.split 12 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.step 43 (.step 3 (.split 13 0 (.split 26 0 (.step 43 (.step 58 (.run (.close 23)))) (.step 4 (.run (.close 29)))) (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part780
namespace Part781
def root : Box := ⟨1809251394333065553493296642222250197538246428604318645832807769780648935424, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390464150032408292946539966949192436031589743916917847351501301189558489289126037119538611355648⟩
def references : Fin 1 → Box := ![Part780.root]
def proof : Enumeration.Proof 1 := (.split 39 0 (.split 49 0 (.split 50 0 (.split 58 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.step 3 (.split 26 0 (.split 35 0 (.step 51 (.step 43 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 6 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 58)))) (.step 68 (.step 63 (.run (.close 58))))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part780.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part781
namespace Part782
def root : Box := ⟨1809251394333065553493296642222250197538246428604318645832807769780648935424, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390464150032408292946541733796257214415920859709959456158875487020483753157307062845136986701824⟩
def references : Fin 1 → Box := ![Part781.root]
def proof : Enumeration.Proof 1 := (.split 9 0 (.split 18 0 (.split 24 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 62 0 (.split 69 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 6 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 58)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 8 0 (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 12 0 (.split 23 0 (.split 39 0 (.split 50 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 48 (.step 2 (.run (.close 4))))) (.step 48 (.run (.close 2)))) (.step 63 (.step 48 (.run (.close 2))))) (.step 68 (.run (.close 21)))) (.step 63 (.step 48 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 35 0 (.split 39 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part781.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part782
namespace Part783
def root : Box := ⟨1809251394333065553493296642222250197538246428604318645832807769780648935424, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778826165519810538064850078035429065015611961912145739776⟩
def references : Fin 1 → Box := ![Part782.root]
def proof : Enumeration.Proof 1 := (.split 22 0 (.split 30 0 (.reuse 0) (.split 6 0 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 26 0 (.step 5 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.run (.close 5)))) (.step 18 (.run (.close 2)))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 48 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 18 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 5)))))) (.split 6 0 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 29 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 43))))) (.step 4 (.step 2 (.run (.close 43))))) (.step 4 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 5)))) (.step 24 (.run (.close 23)))) (.step 24 (.step 4 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 24 (.step 4 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 24 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part782.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part783
namespace Part784
def root : Box := ⟨1809251394333065553493296642222250197538246428604318645832807769780648935424, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827662097487164909438318608697766489424089587069747200⟩
def references : Fin 1 → Box := ![Part783.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.reuse 0) (.split 6 0 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 33 0 (.split 41 0 (.split 59 0 (.split 73 0 (.split 26 0 (.split 35 0 (.split 8 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 24 0 (.split 39 0 (.split 72 0 (.split 58 0 (.step 23 (.step 2 (.run (.close 4)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 43))))) (.step 58 (.step 18 (.run (.close 2))))) (.step 58 (.step 18 (.run (.close 2))))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 8 (.run (.close 11)))) (.step 24 (.step 4 (.step 71 (.run (.close 2)))))) (.step 24 (.step 4 (.step 2 (.run (.close 43)))))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 23)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 24 (.step 4 (.run (.close 2))))) (.step 24 (.run (.close 23)))) (.step 24 (.run (.close 23)))) (.step 18 (.run (.close 2)))) (.step 24 (.step 23 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 24 (.step 4 (.run (.close 2))))) (.step 24 (.step 18 (.run (.close 2))))) (.step 24 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part783.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part784
namespace Part785
def root : Box := ⟨1809251394333065553493296640760748560207344808474848446823431882748798697472, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396365663482762687255876623024143773432430129058029392166797669152521943140343802968922186962642027990459407690887069696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 42 0 (.split 9 0 (.split 24 0 (.split 6 0 (.split 39 0 (.split 12 0 (.split 49 0 (.split 67 0 (.split 50 0 (.step 2 (.run (.close 4))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 8 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 50 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 49 0 (.split 50 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71)))))) (.split 14 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 23)))) (.split 12 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 4 (.step 63 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part785
namespace Part786
def root : Box := ⟨1809251394333065553493296640760748560207344808474848446823431882748798697472, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827660635985527578536698479227567480048202555219509248⟩
def references : Fin 1 → Box := ![Part785.root]
def proof : Enumeration.Proof 1 := (.split 38 0 (.split 17 0 (.split 22 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 49 0 (.split 50 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 24 0 (.split 39 0 (.split 54 0 (.split 49 0 (.split 50 0 (.split 7 0 (.split 13 0 (.split 8 0 (.split 27 0 (.split 32 0 (.split 58 0 (.step 60 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.split 12 0 (.split 24 0 (.split 39 0 (.split 54 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 58 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.step 63 (.step 2 (.run (.close 5))))))) (.step 2 (.run (.close 58)))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 5))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part785.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part786
namespace Part787
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524750124716392448, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827662097487164909439616682912400196331222211152052224⟩
def references : Fin 4 → Box := ![Part776.root, Part779.root, Part784.root, Part786.root]
def proof : Enumeration.Proof 4 := (.split 11 0 (.split 16 0 (.split 17 0 (.reuse 0) (.split 22 0 (.reuse 1) (.split 6 0 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 29 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 43))))) (.step 4 (.step 2 (.run (.close 43))))) (.step 4 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 5)))) (.step 24 (.run (.close 23)))) (.step 24 (.step 4 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 24 (.step 4 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 24 (.step 4 (.run (.close 2))))))) (.reuse 2)) (.split 16 0 (.reuse 3) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 24 0 (.split 39 0 (.split 54 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 61 0 (.split 67 0 (.split 27 0 (.step 50 (.split 48 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 14 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part776.covered
  · exact Part779.covered
  · exact Part784.covered
  · exact Part786.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part787
namespace Part788
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116525876024623235072, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396365663482762687255876623024143773432430129058029392166797669152521943140343802968920888888427394283553400966711607296⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 42 0 (.split 9 0 (.split 24 0 (.split 6 0 (.split 39 0 (.split 12 0 (.split 49 0 (.split 67 0 (.split 50 0 (.step 2 (.run (.close 4))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 8 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 50 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 49 0 (.split 50 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 9))))) (.split 14 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 23)))) (.split 12 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 4 (.step 63 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part788
namespace Part789
def root : Box := ⟨1809251394333065553493298137338425187051931750973902514590338003699547242496, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396365663482762687255876623026180809408764615144297839540203714010489895278374809002872187013372003465914645416794652672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 24 0 (.split 39 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 58 0 (.split 8 0 (.split 9 0 (.split 27 0 (.split 57 0 (.step 51 (.step 8 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 2 (.run (.close 4)))) (.step 4 (.step 71 (.step 63 (.step 2 (.run (.close 5))))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part789
namespace Part790
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116525876024623235072, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827660635985527578535400405012933773142195831044046848⟩
def references : Fin 2 → Box := ![Part788.root, Part789.root]
def proof : Enumeration.Proof 2 := (.split 38 0 (.split 17 0 (.split 22 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 49 0 (.split 50 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 24 0 (.split 39 0 (.split 54 0 (.split 49 0 (.split 26 0 (.split 50 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 27 0 (.split 32 0 (.split 53 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 2 (.run (.close 58))))) (.reuse 1)) (.step 2 (.run (.close 5))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part788.covered
  · exact Part789.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part790
namespace Part791
def root : Box := ⟨1809251394333065553493296640760748560207343511668284413344754151621419597824, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397711580715241241531899777877101102329312925606294096717403648223809964244186382934139847278109842956150397468672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 30 0 (.split 58 0 (.split 74 0 (.split 67 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 48))) (.step 58 (.step 2 (.run (.close 48))))) (.split 35 0 (.split 63 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 49 0 (.split 50 0 (.split 59 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 5 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.step 58 (.step 3 (.split 31 0 (.split 33 0 (.step 29 (.step 48 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))) (.step 4 (.run (.close 58)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 26 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 58 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 33 0 (.split 41 0 (.split 6 0 (.split 12 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 35 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 5 (.step 2 (.run (.close 48)))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 58 (.step 5 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part791
namespace Part792
def root : Box := ⟨1809251394333065553493296640760748560207343511668284413344754151621419597824, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397711580715241241531899777877101102329312925607979093384100563210976654080921684759406116359426840391371141939200⟩
def references : Fin 1 → Box := ![Part791.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 14 0 (.split 22 0 (.reuse 0) (.split 12 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 49 0 (.split 58 0 (.split 44 0 (.split 48 0 (.split 7 0 (.step 7 (.run (.close 2))) (.step 55 (.step 2 (.run (.close 4))))) (.step 23 (.step 2 (.run (.close 4))))) (.step 23 (.step 2 (.run (.close 4))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 49))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 58 (.run (.close 2))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 4 (.step 58 (.step 2 (.run (.close 4)))))) (.step 18 (.run (.close 2)))) (.step 55 (.step 48 (.step 2 (.run (.close 4)))))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 49 0 (.step 3 (.split 50 0 (.split 58 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5)))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 5))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.step 5 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 63 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 2 (.step 4 (.run (.close 68))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 9)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part791.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part792
namespace Part793
def root : Box := ⟨1809251394333065553493296640760748560207343511668284413344754151621419597824, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460777293668517443011875590112145221217011562482879822823424⟩
def references : Fin 1 → Box := ![Part792.root]
def proof : Enumeration.Proof 1 := (.split 24 0 (.split 39 0 (.split 19 0 (.reuse 0) (.split 14 0 (.split 22 0 (.split 30 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 4))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 55 (.step 48 (.step 2 (.run (.close 4)))))) (.step 63 (.step 55 (.run (.close 2)))))) (.split 26 0 (.split 35 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 49 0 (.split 50 0 (.split 56 0 (.split 58 0 (.split 59 0 (.split 6 0 (.step 18 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 58 (.run (.close 27)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 3)))) (.step 58 (.run (.close 27)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 58))))) (.step 4 (.step 71 (.run (.close 58)))))) (.split 26 0 (.split 35 0 (.split 39 0 (.split 46 0 (.split 47 0 (.split 49 0 (.split 50 0 (.split 56 0 (.split 57 0 (.split 58 0 (.split 59 0 (.split 6 0 (.step 18 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 58 (.run (.close 27)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 58 (.run (.close 3)))) (.step 58 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 58 (.run (.close 27)))) (.step 4 (.step 71 (.run (.close 58))))) (.step 2 (.step 4 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part792.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part793
namespace Part794
def root : Box := ⟨1809251394333065553493296640760748560207343511668284413344754151621419597824, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827660635985527578536699745640227668993349676930433024⟩
def references : Fin 1 → Box := ![Part793.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 18 0 (.reuse 0) (.split 14 0 (.split 22 0 (.split 30 0 (.split 67 0 (.split 74 0 (.split 42 0 (.split 35 0 (.split 39 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 48 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 18 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 68 (.step 43 (.step 2 (.run (.close 58)))))) (.step 18 (.run (.close 2)))) (.step 48 (.step 24 (.run (.close 2))))) (.step 63 (.step 48 (.run (.close 2)))))) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 24 0 (.split 32 0 (.split 49 0 (.split 39 0 (.split 50 0 (.split 44 0 (.step 7 (.step 4 (.step 2 (.run (.close 24))))) (.step 4 (.step 40 (.run (.close 8))))) (.step 58 (.step 4 (.run (.close 24))))) (.step 48 (.step 4 (.step 71 (.run (.close 5)))))) (.step 48 (.step 4 (.run (.close 24))))) (.step 4 (.step 55 (.run (.close 2))))) (.step 48 (.step 58 (.step 4 (.step 71 (.run (.close 2))))))) (.step 55 (.step 24 (.run (.close 2))))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 4 (.run (.close 5)))) (.step 4 (.step 55 (.step 58 (.step 2 (.run (.close 4))))))) (.step 4 (.step 55 (.step 43 (.run (.close 2)))))) (.step 55 (.step 4 (.step 43 (.run (.close 2)))))) (.step 18 (.run (.close 2)))) (.step 55 (.step 48 (.step 24 (.run (.close 2)))))) (.step 55 (.step 48 (.step 24 (.run (.close 2)))))) (.step 48 (.step 24 (.step 2 (.run (.close 4)))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part793.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part794
namespace Part795
def root : Box := ⟨1809251394333065553493296640760748560207343511668284413344754151621419597824, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827662097487164909439617949325060385276369332862976000⟩
def references : Fin 1 → Box := ![Part794.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 24 0 (.split 32 0 (.split 49 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 35 0 (.split 44 0 (.step 7 (.run (.close 2))) (.step 40 (.step 3 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 58 (.step 4 (.step 71 (.run (.close 43)))))) (.step 48 (.step 4 (.run (.close 7))))) (.step 48 (.step 58 (.step 4 (.step 71 (.run (.close 43))))))) (.step 48 (.step 4 (.run (.close 7))))) (.step 4 (.step 55 (.run (.close 50))))) (.step 43 (.run (.close 7)))) (.step 55 (.step 24 (.run (.close 2))))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 4 (.run (.close 5)))) (.step 4 (.step 55 (.step 43 (.step 2 (.run (.close 4))))))) (.step 55 (.step 4 (.step 43 (.step 2 (.run (.close 4))))))) (.step 55 (.step 43 (.step 4 (.step 2 (.run (.close 4))))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 55 (.step 48 (.step 24 (.step 2 (.run (.close 4))))))) (.step 55 (.step 48 (.step 24 (.step 2 (.run (.close 4))))))) (.step 24 (.step 5 (.run (.close 2))))) (.step 4 (.step 48 (.step 2 (.run (.close 4)))))) (.step 4 (.step 48 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part794.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part795
namespace Part796
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524751224228020224, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397711580715241241531899777877101102329312925607979093384100563210976652687125109849974518204290399335822181531648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 22 0 (.split 30 0 (.split 58 0 (.split 74 0 (.split 67 0 (.split 49 0 (.step 2 (.run (.close 48))) (.split 35 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2))))) (.split 49 0 (.split 50 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 5 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 69 0 (.step 58 (.step 3 (.split 31 0 (.split 33 0 (.step 29 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 6 0 (.split 12 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.step 5 (.step 2 (.run (.close 48)))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 3))))) (.split 12 0 (.split 54 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part796
namespace Part797
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524751224228020224, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778826164058308900733948457904720925966951821604814848000⟩
def references : Fin 1 → Box := ![Part796.root]
def proof : Enumeration.Proof 1 := (.split 18 0 (.split 24 0 (.split 39 0 (.split 19 0 (.split 8 0 (.split 14 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 49 0 (.step 3 (.split 50 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 5)))) (.step 2 (.run (.close 4))))) (.step 2 (.step 43 (.run (.close 4))))) (.step 2 (.run (.close 18)))) (.split 26 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 49 0 (.split 50 0 (.split 56 0 (.split 57 0 (.split 58 0 (.split 59 0 (.split 6 0 (.step 18 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 58 (.run (.close 27)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 58 (.run (.close 3)))) (.step 58 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.step 71 (.run (.close 58))))) (.step 2 (.step 4 (.run (.close 68)))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 18))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part796.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part797
namespace Part798
def root : Box := ⟨1809251394333065553493296642222250197538246428604318645832807770880160563200, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827662097487164909439616681674460157046968935671398400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 24 0 (.split 32 0 (.split 49 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 35 0 (.split 44 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 3)))) (.step 4 (.run (.close 2)))) (.step 58 (.step 4 (.step 71 (.run (.close 2)))))) (.step 48 (.step 4 (.run (.close 7))))) (.step 48 (.step 58 (.step 4 (.step 71 (.run (.close 2))))))) (.step 48 (.step 4 (.run (.close 7))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 18))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part798
namespace Part799
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524751224228020224, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827662097487164909439617949325060385276370432374603776⟩
def references : Fin 2 → Box := ![Part797.root, Part798.root]
def proof : Enumeration.Proof 2 := (.split 10 0 (.split 16 0 (.split 17 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 24 0 (.split 32 0 (.split 49 0 (.split 39 0 (.split 50 0 (.split 35 0 (.split 44 0 (.step 7 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 3)))) (.step 4 (.run (.close 2)))) (.step 58 (.step 4 (.run (.close 24))))) (.step 48 (.step 4 (.step 71 (.run (.close 2)))))) (.step 48 (.step 4 (.run (.close 24))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 18))))) (.reuse 1)) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 44 0 (.split 48 0 (.split 7 0 (.step 7 (.split 24 0 (.split 39 0 (.split 14 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 58 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 24))))) (.step 4 (.run (.close 58)))) (.step 2 (.run (.close 43))))) (.step 2 (.run (.close 18)))) (.step 2 (.step 63 (.run (.close 3))))) (.step 2 (.step 63 (.run (.close 3))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 18 (.step 5 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part797.covered
  · exact Part798.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part799
namespace Part800
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524750124716392448, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126108149961910827390466187068384627432628002243630620460778827662097487164909439617950563000424561750707273728000⟩
def references : Fin 4 → Box := ![Part787.root, Part790.root, Part795.root, Part799.root]
def proof : Enumeration.Proof 4 := (.split 4 0 (.split 10 0 (.split 5 0 (.reuse 0) (.split 11 0 (.split 16 0 (.reuse 1) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 24 0 (.split 39 0 (.split 54 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 61 0 (.split 67 0 (.split 27 0 (.step 50 (.step 8 (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 2 (.step 4 (.run (.close 71)))))) (.split 9 0 (.reuse 2) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 49 0 (.split 50 0 (.split 67 0 (.split 74 0 (.split 39 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 4))))) (.step 3 (.run (.close 2)))))) (.split 9 0 (.reuse 3) (.step 2 (.run (.close 18)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part787.covered
  · exact Part790.covered
  · exact Part795.covered
  · exact Part799.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part800
namespace Part801
def root : Box := ⟨2348542582773833227889480596789338836627076881973873364003931732280769232458118844097512114909518827748327424, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876607790573801135339067731516432522017332150998729589225373357032633474446017725379301575684590747166243920281600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 32 0 (.split 22 0 (.split 30 0 (.split 67 0 (.split 63 0 (.split 64 0 (.split 12 0 (.step 2 (.run (.close 5))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.split 49 0 (.split 50 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 29)))) (.step 71 (.run (.close 29)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 9 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 46 0 (.split 47 0 (.split 70 0 (.split 56 0 (.split 57 0 (.split 73 0 (.step 29 (.run (.close 2))) (.step 18 (.run (.close 28)))) (.step 48 (.run (.close 28)))) (.step 59 (.run (.close 28)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 28 (.run (.close 71))))) (.step 3 (.step 28 (.run (.close 71))))) (.step 28 (.run (.close 48)))) (.step 28 (.run (.close 48)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 18 (.run (.close 31))))) (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 74 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.step 2 (.run (.close 4))))))) (.split 22 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 12 0 (.split 49 0 (.split 50 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part801
namespace Part802
def root : Box := ⟨2348542582773833227889480596789338836627076881973873364003931732280769232458118844097512114909518827748327424, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876607790573801135339067731516432522017332150998729589225373358529211152466658888528038791940972770949070613118976⟩
def references : Fin 1 → Box := ![Part801.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 8 0 (.split 14 0 (.reuse 0) (.split 7 0 (.split 13 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 73 0 (.split 9 0 (.split 18 0 (.split 19 0 (.step 63 (.step 3 (.step 74 (.run (.close 29))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 5)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.split 7 0 (.split 13 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 73 0 (.split 9 0 (.split 18 0 (.split 19 0 (.step 63 (.step 3 (.step 74 (.step 43 (.step 4 (.step 63 (.run (.close 2)))))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63))))) (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 32 0 (.split 70 0 (.split 9 0 (.split 13 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 14 0 (.split 53 0 (.step 29 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.step 63 (.step 2 (.run (.close 4))))))) (.step 48 (.step 28 (.run (.close 63))))) (.step 18 (.step 3 (.run (.close 31))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 5))))) (.step 55 (.step 4 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part801.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part802
namespace Part803
def root : Box := ⟨2348542582773833227889480596789338836627076881973873364003931732280769232458118844097512114909518827748327424, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876607790573801135339067731516432522017332150998729589225373358530672654103989792744316691407395961101350627966976⟩
def references : Fin 1 → Box := ![Part802.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 11 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 54 0 (.split 7 0 (.split 13 0 (.step 51 (.split 8 0 (.step 28 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.step 4 (.step 63 (.run (.close 2))))))) (.step 2 (.run (.close 48))))) (.split 9 0 (.split 61 0 (.split 32 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 30 0 (.split 11 0 (.split 13 0 (.split 53 0 (.step 29 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 28)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 5 (.run (.close 3)))) (.step 5 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 48 (.step 4 (.run (.close 2))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 3 (.step 43 (.step 18 (.run (.close 31)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part802.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part803
namespace Part804
def root : Box := ⟨2348542582773833227889480596789338836627076881973873364003931732280769232458118844097512114909518827748327424, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876607790573801135339067731516432522017332150998729589225373358530672654103989792745584342007624190503946842800128⟩
def references : Fin 1 → Box := ![Part803.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 10 0 (.reuse 0) (.split 9 0 (.split 29 0 (.split 8 0 (.split 14 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 11 0 (.split 16 0 (.split 7 0 (.split 13 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 39 (.step 18 (.step 29 (.run (.close 2))))) (.step 59 (.step 28 (.run (.close 4))))) (.step 28 (.run (.close 3)))) (.step 28 (.run (.close 3)))) (.step 28 (.run (.close 3)))) (.step 28 (.run (.close 63)))) (.step 28 (.run (.close 63)))) (.step 5 (.step 41 (.step 39 (.run (.close 2)))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 58 (.step 5 (.run (.close 2))))) (.step 58 (.step 5 (.run (.close 2))))) (.step 58 (.step 5 (.run (.close 2))))) (.step 5 (.step 2 (.run (.close 4))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 5 (.step 71 (.step 4 (.run (.close 2)))))) (.step 5 (.step 71 (.step 4 (.run (.close 2)))))) (.step 18 (.step 3 (.step 28 (.step 18 (.run (.close 31))))))) (.step 18 (.step 3 (.step 28 (.step 18 (.run (.close 31)))))))) (.split 9 0 (.split 29 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 8 0 (.split 14 0 (.step 28 (.split 32 0 (.split 70 0 (.split 11 0 (.step 39 (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 5 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 5)))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 2 (.step 4 (.run (.close 3))))) (.step 2 (.step 4 (.run (.close 3))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part803.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part804
namespace Part805
def root : Box := ⟨2462627735817237724600667895739572652156320331480972390620132341697089891487808121332235738442422137069241997721600, 5789234136390493270774876349876928662611796200388014929877472612713331792548975125562851457761296723972959171590919630381510975294327905695589840837789517234948226252031820594556435678028574236152211634421621011177514467328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 50 0 (.split 59 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 7 0 (.split 11 0 (.split 13 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 56 0 (.split 57 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 67)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 58)))) (.split 8 0 (.step 28 (.step 43 (.step 28 (.run (.close 58))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.split 8 0 (.split 14 0 (.split 67 0 (.split 74 0 (.split 6 0 (.step 28 (.split 11 0 (.step 63 (.step 40 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 48)))) (.step 4 (.step 63 (.run (.close 58))))) (.step 71 (.step 2 (.run (.close 5))))) (.step 4 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 5))))) (.split 8 0 (.split 14 0 (.split 59 0 (.split 67 0 (.split 74 0 (.split 6 0 (.step 28 (.split 11 0 (.step 63 (.step 40 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 48)))) (.step 4 (.step 63 (.run (.close 58))))) (.step 71 (.step 2 (.run (.close 5))))) (.step 58 (.run (.close 2)))) (.step 63 (.run (.close 5)))) (.step 2 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part805
namespace Part806
def root : Box := ⟨2348542582773833227889480596789338836627076881973873364003931732280769232458118844097512114909518827748327424, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544962339233177848456086106507737775408384834815855402820005972141696296030264822565455958975982937931419180260999036928⟩
def references : Fin 2 → Box := ![Part804.root, Part805.root]
def proof : Enumeration.Proof 2 := (.split 38 0 (.split 5 0 (.reuse 0) (.split 12 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 8 0 (.split 14 0 (.split 56 0 (.split 74 0 (.split 73 0 (.split 4 0 (.split 42 0 (.split 54 0 (.split 16 0 (.split 64 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 60 (.step 28 (.run (.close 4))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 49 0 (.reuse 1) (.split 8 0 (.split 14 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 74 0 (.split 6 0 (.step 28 (.split 11 0 (.step 63 (.step 40 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 48)))) (.step 4 (.step 63 (.run (.close 58))))) (.step 71 (.step 2 (.run (.close 5))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.run (.close 5)))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part804.covered
  · exact Part805.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part806
namespace Part807
def root : Box := ⟨2348542582773833227889480596789338836627076881973873364003931732280769232458118844097512114909518827748327424, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397713929257821828112316959506007005411774295284231445299194483081824556142681778456318752618982932988708811440128⟩
def references : Fin 1 → Box := ![Part806.root]
def proof : Enumeration.Proof 1 := (.split 41 0 (.split 58 0 (.reuse 0) (.split 61 0 (.split 8 0 (.split 14 0 (.split 5 0 (.split 11 0 (.split 49 0 (.split 16 0 (.split 17 0 (.split 50 0 (.split 22 0 (.split 53 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 32 0 (.split 59 0 (.split 70 0 (.step 29 (.split 10 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 4 (.step 48 (.step 55 (.run (.close 3)))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 4 (.step 48 (.step 2 (.run (.close 4)))))) (.step 4 (.step 48 (.step 2 (.run (.close 4)))))) (.step 5 (.step 58 (.run (.close 2))))) (.step 5 (.step 63 (.run (.close 51))))) (.step 58 (.run (.close 2))))) (.split 61 0 (.split 62 0 (.split 6 0 (.split 12 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 14 0 (.split 22 0 (.split 49 0 (.split 58 0 (.split 50 0 (.split 59 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 58 (.run (.close 2))))) (.step 40 (.step 5 (.run (.close 2))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 43 (.step 71 (.run (.close 2))))) (.step 58 (.step 4 (.step 5 (.run (.close 2)))))) (.step 2 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part806.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part807
namespace Part808
def root : Box := ⟨2348542584961083952672492521161841063744698247327042794897144168706539838868071843296888038133032004771381248, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498504493601221608151709214903017314722694183547159403248020454357734767318922358264629507168126077214130176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 6 0 (.split 12 0 (.split 67 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 4 (.run (.close 31)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 58 (.run (.close 2))))) (.step 71 (.step 40 (.step 5 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 58))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 58 (.step 43 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 43 (.step 71 (.run (.close 2))))) (.step 58 (.step 4 (.step 5 (.run (.close 2)))))) (.step 2 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part808
namespace Part809
def root : Box := ⟨2348542582773835313814320363303091175515461813177110280707566846199489883865938982983963072566305959547240448, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498504493601223694076548981416769653611079114750396319951655568276455418726742497151080464824913209013043200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 6 0 (.split 12 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 58 (.run (.close 2))))) (.step 40 (.step 5 (.step 2 (.run (.close 4)))))) (.step 58 (.step 43 (.step 2 (.run (.close 4)))))) (.step 58 (.step 43 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.step 43 (.step 40 (.step 2 (.run (.close 4))))))) (.step 43 (.step 5 (.step 31 (.step 4 (.run (.close 2))))))) (.step 2 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part809
namespace Part810
def root : Box := ⟨2348542582773833227889480596789338836627076881973873364003931732280769232458118844097512114909518827748327424, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498504493601223694076548981416769653611079114750396319951655568276455418726742497151080464824913209013043200⟩
def references : Fin 3 → Box := ![Part807.root, Part808.root, Part809.root]
def proof : Enumeration.Proof 3 := (.split 31 0 (.split 33 0 (.split 39 0 (.reuse 0) (.split 61 0 (.split 8 0 (.split 14 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 49 0 (.split 50 0 (.split 22 0 (.split 53 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 32 0 (.split 41 0 (.split 58 0 (.split 59 0 (.split 70 0 (.step 29 (.split 10 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 48 (.step 43 (.run (.close 2))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 55 (.step 2 (.run (.close 4)))))) (.step 4 (.step 58 (.step 48 (.step 55 (.run (.close 3))))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 5 (.step 58 (.run (.close 2))))) (.step 63 (.step 5 (.step 55 (.step 58 (.step 43 (.run (.close 2)))))))) (.step 58 (.run (.close 2))))) (.reuse 1)) (.reuse 2))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part807.covered
  · exact Part808.covered
  · exact Part809.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part810
namespace Part811
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524750124716392448, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498504493601223694076548981416769655377926179528780649534953069019373934554226394026699422946519410305662976⟩
def references : Fin 2 → Box := ![Part800.root, Part810.root]
def proof : Enumeration.Proof 2 := (.split 36 0 (.reuse 0) (.split 24 0 (.reuse 1) (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 47 0 (.split 10 0 (.split 30 0 (.split 57 0 (.split 42 0 (.split 12 0 (.split 8 0 (.split 35 0 (.split 56 0 (.split 14 0 (.step 3 (.step 29 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 4 (.run (.close 29)))) (.step 29 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 71 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 58 (.step 2 (.run (.close 4)))))) (.step 58 (.step 43 (.run (.close 2))))) (.step 58 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 5)))) (.step 63 (.step 58 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part800.covered
  · exact Part810.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part811
namespace Part812
def root : Box := ⟨2239744742177804210557442282377695672454711050727946175660737661171135381580794758497402243396323508224, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876605442033458106248017646246393174960873219594302326402737299276561931337956402642038272930973239890812495462400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 32 0 (.split 22 0 (.split 30 0 (.split 67 0 (.split 63 0 (.split 64 0 (.split 12 0 (.step 2 (.run (.close 5))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.split 49 0 (.split 50 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 29)))) (.step 71 (.run (.close 29)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 9 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 7 0 (.split 13 0 (.split 46 0 (.split 47 0 (.split 70 0 (.split 56 0 (.split 57 0 (.split 73 0 (.step 29 (.run (.close 2))) (.step 18 (.run (.close 28)))) (.step 48 (.run (.close 28)))) (.step 59 (.run (.close 28)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 28 (.run (.close 71))))) (.step 3 (.step 16 (.step 3 (.run (.close 28)))))) (.step 28 (.run (.close 48)))) (.step 28 (.run (.close 48)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 18 (.run (.close 31))))) (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 74 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.step 2 (.run (.close 4))))))) (.split 22 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 12 0 (.split 49 0 (.split 50 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part812
namespace Part813
def root : Box := ⟨2239744742177804210557442282377695672454711050727946175660737661171135381580794758497402243396323508224, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876605442033458106248017646246393174960873219594302326402737300773139609358597565790775489187355263673639188299776⟩
def references : Fin 1 → Box := ![Part812.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 8 0 (.split 14 0 (.reuse 0) (.split 7 0 (.split 13 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 73 0 (.split 9 0 (.split 18 0 (.split 19 0 (.step 63 (.step 3 (.step 66 (.run (.close 29))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 5)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.split 7 0 (.split 13 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 73 0 (.split 9 0 (.split 18 0 (.split 19 0 (.step 63 (.step 3 (.step 29 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63))))) (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 32 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 8 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 14 0 (.split 53 0 (.step 29 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 29)))) (.step 4 (.step 71 (.step 63 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.run (.close 3))))) (.step 48 (.step 49 (.run (.close 4))))) (.step 48 (.step 49 (.step 63 (.run (.close 2)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 5))))) (.step 55 (.step 4 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part812.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part813
namespace Part814
def root : Box := ⟨2239744742177804210557442282377695672454711050727946175660737661171135381580794758497402243396323508224, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876605442033458106248017646246393174960873219594302326402737300774601110995928470007053388653778453825919203147776⟩
def references : Fin 1 → Box := ![Part813.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 11 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 50 0 (.split 59 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.step 49 (.step 28 (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.step 4 (.step 63 (.run (.close 2))))))) (.step 2 (.run (.close 48))))) (.split 9 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 30 0 (.split 12 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 5 (.run (.close 3)))) (.step 5 (.step 2 (.run (.close 4))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 3 (.step 43 (.step 18 (.run (.close 31)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part813.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part814
namespace Part815
def root : Box := ⟨2239744742177804210557442282377695672454711050727946175660737661171135381580794758497402243396323508224, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544959876605442033458106248017646246393174960873219594302326402737300774601110995928470008321039254006683228515417980928⟩
def references : Fin 1 → Box := ![Part814.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 10 0 (.reuse 0) (.split 29 0 (.split 8 0 (.split 14 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 11 0 (.split 16 0 (.split 7 0 (.split 13 0 (.split 44 0 (.split 17 0 (.split 47 0 (.split 56 0 (.split 22 0 (.step 16 (.step 66 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 49 (.run (.close 16)))) (.step 49 (.run (.close 16)))) (.step 49 (.step 4 (.run (.close 2))))) (.step 49 (.step 48 (.run (.close 2))))) (.step 49 (.run (.close 16)))) (.step 28 (.run (.close 63)))) (.step 5 (.step 49 (.run (.close 7))))) (.step 3 (.step 49 (.run (.close 2))))) (.step 58 (.step 5 (.run (.close 2))))) (.step 58 (.step 5 (.run (.close 2))))) (.step 58 (.step 5 (.run (.close 2))))) (.step 5 (.step 2 (.run (.close 4))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 5 (.step 71 (.step 4 (.run (.close 2)))))) (.step 5 (.step 71 (.step 4 (.run (.close 2)))))) (.step 18 (.step 3 (.step 28 (.step 18 (.run (.close 31)))))))) (.split 9 0 (.split 29 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 8 0 (.split 14 0 (.step 28 (.split 70 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 4 (.run (.close 37)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 4))))) (.step 5 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 5)))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 58 (.step 5 (.run (.close 29))))) (.step 2 (.step 4 (.run (.close 3))))) (.step 2 (.step 4 (.run (.close 3))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part814.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part815
namespace Part816
def root : Box := ⟨2462625387276894695509617810469533305099861400076545127797496283941018348379746798594972435688804629793810572902400, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544962339230829308113057015457652505367140640766859809846923362487256197276453739075371366711457711257526256113553506304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 32 0 (.split 70 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 7 0 (.split 11 0 (.split 13 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 56 0 (.split 57 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 67)))) (.step 2 (.run (.close 49)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 58)))) (.split 8 0 (.step 28 (.step 43 (.step 28 (.run (.close 58))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.split 8 0 (.split 14 0 (.split 67 0 (.split 74 0 (.split 6 0 (.step 28 (.split 11 0 (.step 63 (.step 40 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 48)))) (.step 4 (.step 63 (.run (.close 58))))) (.step 71 (.step 2 (.run (.close 5))))) (.step 4 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 5))))) (.split 8 0 (.split 14 0 (.split 59 0 (.split 67 0 (.split 74 0 (.split 6 0 (.step 28 (.split 11 0 (.step 63 (.step 40 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 48)))) (.step 4 (.step 63 (.run (.close 58))))) (.step 71 (.step 2 (.run (.close 5))))) (.step 58 (.run (.close 2)))) (.step 63 (.run (.close 5)))) (.step 2 (.run (.close 5))))) (.split 14 0 (.split 50 0 (.split 59 0 (.split 67 0 (.step 49 (.step 29 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.run (.close 5))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part816
namespace Part817
def root : Box := ⟨2348544822518575405693691154231619405071355003619370598653466632269870196249990024258457495787012099355443200, 5789234136390493270774876349876928662611796196335753632142127926666058484889684956131117564073852241993350908348249448195267818834750426822607437604115157985951352487429548256487928827324018892925698370771420096236307349504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 9 0 (.split 29 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 4 0 (.split 10 0 (.split 7 0 (.split 12 0 (.split 16 0 (.split 13 0 (.split 17 0 (.split 5 0 (.split 11 0 (.step 37 (.step 39 (.step 2 (.run (.close 4))))) (.step 28 (.run (.close 4)))) (.step 28 (.run (.close 4)))) (.step 5 (.step 59 (.run (.close 28))))) (.step 49 (.run (.close 29)))) (.step 7 (.run (.close 28)))) (.step 29 (.run (.close 2)))) (.step 28 (.run (.close 63)))) (.step 7 (.step 49 (.run (.close 29))))) (.step 28 (.run (.close 29)))) (.step 28 (.run (.close 29)))) (.step 28 (.run (.close 29)))) (.step 28 (.run (.close 29)))) (.step 28 (.step 63 (.run (.close 18))))) (.step 28 (.run (.close 39)))) (.split 5 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 48))))) (.split 19 0 (.split 23 0 (.split 48 0 (.step 29 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63))))) (.split 19 0 (.split 23 0 (.split 29 0 (.split 48 0 (.step 29 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 49)))) (.step 2 (.run (.close 49)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63))))) (.step 28 (.step 43 (.run (.close 39))))) (.split 14 0 (.split 5 0 (.split 13 0 (.split 44 0 (.step 45 (.step 39 (.step 7 (.run (.close 2))))) (.step 63 (.step 43 (.run (.close 28))))) (.step 40 (.step 16 (.run (.close 29))))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 2))))) (.step 28 (.step 43 (.step 28 (.step 7 (.run (.close 48))))))) (.step 28 (.split 8 0 (.step 37 (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 43))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part817
namespace Part818
def root : Box := ⟨2348544822518575405693691154231619405071355003619370598653466632269870196249990024258457495787012099355443200, 5789234136395753406676424723384169652494676329053565269680295786572830073455240528232672114628345146072544962339233177850695830848685541985965827115384299680941651469376345830930253923529247830156143883312296673532606152704⟩
def references : Fin 1 → Box := ![Part817.root]
def proof : Enumeration.Proof 1 := (.split 27 0 (.split 32 0 (.split 70 0 (.split 49 0 (.split 50 0 (.split 59 0 (.reuse 0) (.split 14 0 (.split 74 0 (.split 5 0 (.split 11 0 (.step 29 (.step 2 (.run (.close 5)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 63 (.run (.close 45)))) (.step 63 (.step 48 (.run (.close 5)))))) (.split 14 0 (.split 74 0 (.split 5 0 (.split 11 0 (.step 29 (.step 16 (.step 2 (.run (.close 5))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 63 (.step 48 (.run (.close 5))))) (.step 63 (.step 48 (.run (.close 5)))))) (.split 74 0 (.split 5 0 (.split 11 0 (.step 29 (.step 49 (.step 16 (.run (.close 58))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 63 (.step 48 (.run (.close 5)))))) (.split 8 0 (.split 14 0 (.split 49 0 (.split 50 0 (.step 28 (.step 43 (.step 28 (.step 4 (.run (.close 2)))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 40)))) (.step 2 (.run (.close 4))))) (.split 6 0 (.split 8 0 (.split 14 0 (.split 49 0 (.split 50 0 (.split 59 0 (.step 28 (.step 43 (.step 28 (.step 7 (.step 2 (.run (.close 48))))))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 40)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 29))))) (.split 8 0 (.split 14 0 (.step 28 (.step 43 (.step 28 (.run (.close 4))))) (.step 4 (.run (.close 40)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part817.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part818
namespace Part819
def root : Box := ⟨3957286423569672544968040336314355040562101585619389438625008897486355603944254616902866627537331002211258415270969280157568016209645680530616120062425049184067951750702694400, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964535511169971236719533452400340723410604402945715835217862423757909698805967671479161942888728568637774173998962381886985338880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 8 0 (.split 14 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 49 0 (.split 22 0 (.split 53 0 (.split 67 0 (.split 69 0 (.split 32 0 (.split 70 0 (.step 29 (.split 7 0 (.split 13 0 (.split 73 0 (.split 46 0 (.split 10 0 (.split 30 0 (.step 29 (.step 2 (.run (.close 63)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 3)))) (.step 48 (.run (.close 49)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 63 (.step 2 (.run (.close 4)))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 48 (.step 43 (.run (.close 2))))) (.step 58 (.step 55 (.step 2 (.run (.close 4)))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 5 (.step 63 (.step 43 (.run (.close 2)))))) (.step 5 (.step 63 (.step 43 (.run (.close 2)))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part819
namespace Part820
def root : Box := ⟨2644223875160994395809900976873261963524176174139502572811049892148351111120906120961927977140441934148862250343489756725248, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155393846397713929260061572854494763716564447692342739562353090796429132616724545243645570327498913564363810481980418555904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 6 0 (.split 12 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 18 0 (.split 19 0 (.split 54 0 (.split 49 0 (.split 27 0 (.split 32 0 (.split 58 0 (.split 50 0 (.split 59 0 (.split 7 0 (.split 9 0 (.split 29 0 (.step 45 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 58 (.step 2 (.run (.close 4)))))) (.step 40 (.step 58 (.step 5 (.run (.close 2)))))) (.step 2 (.step 58 (.run (.close 43))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 4 (.step 58 (.step 43 (.step 2 (.run (.close 4))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 43 (.step 71 (.run (.close 2))))) (.step 4 (.step 58 (.step 43 (.step 5 (.step 48 (.step 2 (.run (.close 43))))))))) (.step 2 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part820
namespace Part821
def root : Box := ⟨2521728396569248909330600744213401840967385691005461041459741505817901854113482650265894621107393098413867587703144448, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498506731158713061172907847972795656049350939839487207004342917921065124700840539226198964822106171798192128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 14 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 49 0 (.split 50 0 (.split 22 0 (.split 53 0 (.split 67 0 (.split 69 0 (.split 32 0 (.split 41 0 (.split 58 0 (.split 59 0 (.split 70 0 (.step 29 (.split 74 0 (.split 10 0 (.step 2 (.run (.close 4))) (.step 58 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4)))))) (.step 4 (.step 2 (.run (.close 4))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 58 (.step 43 (.run (.close 2))))) (.step 58 (.step 55 (.step 2 (.run (.close 4)))))) (.step 58 (.step 55 (.step 48 (.step 43 (.run (.close 2))))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 4 (.step 48 (.step 43 (.run (.close 2)))))) (.step 4 (.step 48 (.step 43 (.run (.close 2)))))) (.step 5 (.step 55 (.step 63 (.step 58 (.step 43 (.run (.close 2)))))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part821
namespace Part822
def root : Box := ⟨2241931992902587222481814784604813293820064220158839388097163431777545334579994134420625756573346562048, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498506733345963785955919772345297883166972305192656637897555354346835731110793538425574888045619348821245952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 6 0 (.split 12 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 7 0 (.split 10 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 39 0 (.split 30 0 (.step 2 (.run (.close 5))) (.step 4 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 31)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.step 2 (.run (.close 5)))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 58 (.step 2 (.run (.close 4)))))) (.step 40 (.step 5 (.step 58 (.run (.close 2)))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 58 (.step 43 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 43 (.step 71 (.run (.close 2))))) (.step 58 (.step 43 (.step 5 (.step 31 (.step 2 (.run (.close 43)))))))) (.step 2 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part822
namespace Part823
def root : Box := ⟨2239744744263729050323956034716584057385914287644649810774656381822543201719681209455059030528122421248, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498506733345965871880759538859050222055357236395893554601190468265556382518613677312025845702406480620158976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 6 0 (.split 12 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 54 0 (.split 4 0 (.split 7 0 (.split 10 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 4))) (.step 71 (.step 2 (.run (.close 5))))) (.step 71 (.step 58 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.step 58 (.step 2 (.run (.close 4)))))) (.step 40 (.step 5 (.step 58 (.run (.close 2)))))) (.step 58 (.step 43 (.step 4 (.run (.close 2)))))) (.step 58 (.step 43 (.step 4 (.step 2 (.run (.close 4))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.step 43 (.step 5 (.run (.close 2)))))) (.step 43 (.step 5 (.step 31 (.step 4 (.step 2 (.run (.close 43)))))))) (.step 2 (.step 63 (.run (.close 58))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part823
namespace Part824
def root : Box := ⟨2239744742177804210557442282379462519519489435057529473161480579686962865477670377455523849597616128000, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498506733345965871880759538859050223822204301174277884184487969008474898346097574187644803824012681912778752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 10 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 47 0 (.split 30 0 (.split 36 0 (.split 57 0 (.split 42 0 (.split 12 0 (.split 8 0 (.split 35 0 (.split 56 0 (.split 14 0 (.step 3 (.step 29 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 58 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 4 (.run (.close 29)))) (.step 29 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 29 (.step 2 (.run (.close 5))))) (.step 71 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 31)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 58 (.step 43 (.run (.close 2))))) (.step 58 (.step 43 (.run (.close 2))))) (.step 4 (.step 58 (.step 43 (.run (.close 2)))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 43)))) (.step 63 (.step 58 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part824
namespace Part825
def root : Box := ⟨1809251394333065553493296640760748560207343510400633813116524750124716392448, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216213964538155396368126110498506733345965871880759538859050223822204301174277884184487969008474898346097574187644803824012681912778752⟩
def references : Fin 10 → Box := ![Part811.root, Part815.root, Part816.root, Part818.root, Part819.root, Part820.root, Part821.root, Part822.root, Part823.root, Part824.root]
def proof : Enumeration.Proof 10 := (.split 34 0 (.reuse 0) (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 36 0 (.split 38 0 (.split 5 0 (.reuse 1) (.split 6 0 (.split 12 0 (.split 50 0 (.split 59 0 (.split 62 0 (.split 7 0 (.split 13 0 (.split 26 0 (.split 56 0 (.split 74 0 (.split 73 0 (.split 4 0 (.split 27 0 (.split 42 0 (.split 54 0 (.step 49 (.split 16 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 60 (.step 40 (.step 49 (.step 3 (.run (.close 2))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.split 27 0 (.reuse 2) (.step 2 (.run (.close 5))))) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)) (.reuse 7)) (.reuse 8)) (.reuse 9)))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part811.covered
  · exact Part815.covered
  · exact Part816.covered
  · exact Part818.covered
  · exact Part819.covered
  · exact Part820.covered
  · exact Part821.covered
  · exact Part822.covered
  · exact Part823.covered
  · exact Part824.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part825
namespace Part826
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214686113105584791270823485892952297428070508076943723814097285154852527584922180829950652025487480029156996606249245397167768940146721473409029356176539648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 56 0 (.split 73 0 (.split 46 0 (.split 47 0 (.split 41 0 (.split 58 0 (.split 33 0 (.split 16 0 (.split 19 0 (.split 18 0 (.split 17 0 (.step 55 (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 36)))) (.step 55 (.step 24 (.run (.close 2))))) (.step 36 (.run (.close 2)))) (.split 18 0 (.split 19 0 (.step 24 (.step 18 (.step 31 (.step 2 (.run (.close 71)))))) (.step 55 (.run (.close 24)))) (.step 24 (.run (.close 2))))) (.step 36 (.run (.close 23)))) (.step 61 (.step 2 (.run (.close 23))))) (.step 36 (.split 23 0 (.split 57 0 (.step 61 (.step 77 (.step 27 (.step 23 (.run (.close 18)))))) (.step 71 (.run (.close 44)))) (.step 44 (.run (.close 68)))))) (.split 16 0 (.split 17 0 (.split 33 0 (.step 18 (.split 19 0 (.step 36 (.step 2 (.run (.close 4)))) (.step 24 (.step 4 (.run (.close 55)))))) (.step 36 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 27 0 (.split 47 0 (.step 36 (.split 53 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.step 51 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4)))))) (.split 59 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 24))))) (.step 4 (.step 44 (.step 18 (.run (.close 2)))))) (.step 4 (.step 3 (.step 22 (.step 2 (.run (.close 4)))))))) (.split 59 0 (.split 54 0 (.split 72 0 (.split 16 0 (.step 2 (.run (.close 24))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 4 (.step 24 (.step 55 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part826
namespace Part827
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214686113105584791270823485892952297428072970702333291967664042666370397381680300400595852680893395078618499552699352256836538500349575652688119623185334272⟩
def references : Fin 1 → Box := ![Part826.root]
def proof : Enumeration.Proof 1 := (.split 35 0 (.split 13 0 (.split 38 0 (.reuse 0) (.split 14 0 (.split 59 0 (.split 54 0 (.split 72 0 (.step 2 (.run (.close 24))) (.step 58 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 4))))) (.step 5 (.step 71 (.run (.close 2)))))) (.split 14 0 (.split 54 0 (.split 59 0 (.split 72 0 (.step 2 (.run (.close 24))) (.step 23 (.run (.close 2)))) (.split 24 0 (.step 3 (.run (.close 2))) (.step 5 (.run (.close 63))))) (.step 5 (.run (.close 2)))) (.split 27 0 (.split 32 0 (.step 5 (.split 16 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 13 0 (.split 27 0 (.split 32 0 (.split 38 0 (.split 14 0 (.split 16 0 (.split 72 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 4 (.run (.close 55)))) (.step 4 (.step 71 (.step 55 (.run (.close 68)))))) (.step 40 (.step 75 (.run (.close 23))))) (.step 71 (.step 4 (.step 55 (.run (.close 24)))))) (.step 23 (.step 43 (.run (.close 74))))) (.split 16 0 (.split 17 0 (.step 31 (.step 40 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 3 (.step 18 (.step 4 (.step 55 (.run (.close 2))))))) (.step 3 (.split 14 0 (.split 24 0 (.step 18 (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 14 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 3 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part826.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part827
namespace Part828
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007520239417628265633668502992682646971072273832468088719727617963830735023399501824, 5789234136395748269820059484240009140673214437432980755741006239099214686113105584791270823485895659982676237828963640337069366272845507542963103848948213571205464138335282569831724979582552262556109940578486741908873805824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 13 0 (.split 31 0 (.split 33 0 (.split 16 0 (.split 41 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 29 (.step 55 (.run (.close 2)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 75 (.run (.close 29)))) (.step 24 (.step 29 (.step 63 (.run (.close 24)))))) (.step 40 (.run (.close 2)))) (.step 40 (.step 24 (.step 29 (.step 63 (.run (.close 24))))))) (.step 23 (.step 31 (.step 2 (.run (.close 23)))))) (.step 23 (.split 35 0 (.step 2 (.run (.close 23))) (.step 4 (.run (.close 40)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.step 40 (.step 57 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 23 (.step 26 (.step 4 (.run (.close 2)))))) (.split 13 0 (.step 24 (.step 4 (.step 40 (.step 31 (.step 4 (.step 68 (.run (.close 51)))))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 24 0 (.split 38 0 (.step 40 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.step 4 (.step 55 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part828
namespace Part829
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214686113105584791270823485895659982676237828963640337069366272845507542963103848948213571205464138335282569831724979582552262556109940578486741908873805824⟩
def references : Fin 2 → Box := ![Part827.root, Part828.root]
def proof : Enumeration.Proof 2 := (.split 26 0 (.split 42 0 (.reuse 0) (.split 38 0 (.split 13 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 14 0 (.split 70 0 (.split 16 0 (.split 17 0 (.step 43 (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.run (.close 24)))) (.step 24 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 63 (.step 55 (.step 68 (.step 43 (.run (.close 2))))))) (.step 40 (.step 29 (.split 39 0 (.step 63 (.step 38 (.step 63 (.step 68 (.run (.close 24)))))) (.step 4 (.run (.close 68))))))) (.step 3 (.step 4 (.step 40 (.run (.close 2)))))) (.split 35 0 (.step 3 (.step 44 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 24 0 (.step 3 (.split 27 0 (.split 32 0 (.step 55 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 23))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 31 0 (.split 33 0 (.step 43 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 43)))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part827.covered
  · exact Part828.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part829
namespace Part830
def root : Box := ⟨3351951982485649274896345463318241246286049751272660862143209272495625843691361315291017946760918817560500898338472151641410199303011119744161282862874624, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203565513497729743562907931884758902195258123886197803637398984054736676657152601640907605413031423583063717707776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 42 0 (.split 59 0 (.split 48 0 (.split 16 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 66 0 (.split 17 0 (.split 19 0 (.split 22 0 (.split 63 0 (.step 2 (.run (.close 23))) (.step 51 (.run (.close 2)))) (.step 55 (.step 43 (.step 55 (.run (.close 2)))))) (.step 23 (.run (.close 2)))) (.step 40 (.step 2 (.run (.close 18))))) (.step 51 (.step 2 (.run (.close 23))))) (.step 51 (.step 2 (.run (.close 4))))) (.step 51 (.step 2 (.run (.close 4))))) (.step 51 (.step 2 (.run (.close 4))))) (.split 35 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 24 (.step 2 (.run (.close 18))))) (.step 58 (.run (.close 11)))) (.step 55 (.run (.close 29))))) (.step 51 (.run (.close 2)))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 26 0 (.split 13 0 (.split 27 0 (.step 51 (.step 55 (.step 2 (.run (.close 23))))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 55))))) (.step 55 (.run (.close 2)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 55 (.run (.close 18))))) (.split 16 0 (.split 22 0 (.split 59 0 (.step 51 (.split 46 0 (.split 14 0 (.step 2 (.run (.close 23))) (.step 63 (.run (.close 55)))) (.step 48 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 55))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part830
namespace Part831
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621514042666466487902515390415473605607424, 5789234136390488133918511110732768150790334308767430415938183061724940003223167800311813720950839008757701954761856894346195757092834511857083856316188791170552007324506334155568735409180898915886616001782961782145366884352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 47 0 (.split 44 0 (.split 38 0 (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.step 57 (.step 22 (.step 2 (.run (.close 23))))) (.step 55 (.step 4 (.step 24 (.step 55 (.run (.close 57))))))) (.step 4 (.step 55 (.step 24 (.step 55 (.run (.close 57))))))) (.step 4 (.step 55 (.step 24 (.step 55 (.run (.close 57))))))) (.step 4 (.step 55 (.step 24 (.step 55 (.run (.close 57))))))) (.split 48 0 (.split 66 0 (.split 63 0 (.step 4 (.split 64 0 (.step 61 (.step 15 (.step 43 (.run (.close 27))))) (.step 24 (.run (.close 27))))) (.step 29 (.run (.close 27)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.split 31 0 (.split 33 0 (.split 41 0 (.step 63 (.step 23 (.step 4 (.step 24 (.run (.close 15)))))) (.step 55 (.run (.close 15)))) (.step 55 (.run (.close 36)))) (.step 55 (.run (.close 52))))) (.step 4 (.split 57 0 (.split 56 0 (.split 14 0 (.step 57 (.step 55 (.step 57 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 57)))) (.step 4 (.step 2 (.run (.close 48))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.run (.close 2))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 23)))) (.step 63 (.run (.close 23))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.step 51 (.split 38 0 (.step 55 (.split 24 0 (.step 21 (.run (.close 2))) (.step 4 (.run (.close 2))))) (.step 63 (.run (.close 2)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part831
namespace Part832
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621514042666466487902515390415473605607424, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203565513497729743562907931884757005057668059697651983850380601712054408681725169013902167855847941741407977340928⟩
def references : Fin 1 → Box := ![Part831.root]
def proof : Enumeration.Proof 1 := (.split 32 0 (.split 53 0 (.split 70 0 (.split 13 0 (.split 46 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 31 (.step 51 (.split 47 0 (.step 55 (.split 24 0 (.split 26 0 (.step 31 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 63 (.run (.close 2)))))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 16 0 (.split 22 0 (.step 22 (.split 46 0 (.step 9 (.split 23 0 (.split 41 0 (.step 4 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 15 (.run (.close 2))))) (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 24 0 (.step 3 (.split 31 0 (.split 33 0 (.split 39 0 (.step 4 (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.step 51 (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part831.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part832
namespace Part833
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203565513497729743562907931884758902195258123886197803637398984054736676657153930868903390328904327390123998052352⟩
def references : Fin 3 → Box := ![Part829.root, Part830.root, Part832.root]
def proof : Enumeration.Proof 3 := (.split 12 0 (.split 44 0 (.split 48 0 (.reuse 0) (.split 42 0 (.split 59 0 (.split 66 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 56 0 (.split 38 0 (.split 63 0 (.split 16 0 (.step 36 (.split 17 0 (.split 27 0 (.split 31 0 (.step 51 (.run (.close 2))) (.step 55 (.run (.close 2)))) (.step 40 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 40 (.step 2 (.run (.close 18))))) (.step 51 (.step 40 (.run (.close 2))))) (.step 23 (.run (.close 2)))) (.step 23 (.run (.close 2)))) (.step 51 (.run (.close 2)))) (.step 51 (.run (.close 2)))) (.step 51 (.run (.close 2)))) (.step 51 (.run (.close 2)))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 24 0 (.split 13 0 (.split 27 0 (.step 51 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 71 (.step 63 (.run (.close 55)))))) (.split 16 0 (.split 22 0 (.split 59 0 (.step 51 (.step 55 (.step 2 (.run (.close 23))))) (.step 68 (.step 63 (.run (.close 55))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))))) (.reuse 1)) (.split 27 0 (.reuse 2) (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part829.covered
  · exact Part830.covered
  · exact Part832.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part833
namespace Part834
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986643639529917932109824, 5789234136390488133918511110732768150790334308767430415938183061724940003223167800311813720950839008757701954761856894346195757092834511857083856316188791170552007324506334155568735409180898915886616001784114703649973731328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 47 0 (.split 57 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 18 0 (.split 14 0 (.split 31 0 (.split 16 0 (.split 54 0 (.step 11 (.run (.close 9))) (.step 57 (.run (.close 68)))) (.step 24 (.run (.close 9)))) (.split 63 0 (.step 22 (.step 27 (.step 40 (.run (.close 23))))) (.step 55 (.run (.close 2))))) (.step 11 (.run (.close 2)))) (.split 63 0 (.split 14 0 (.step 22 (.run (.close 9))) (.step 55 (.step 24 (.run (.close 2))))) (.step 55 (.run (.close 9))))) (.step 23 (.step 57 (.run (.close 2))))) (.step 23 (.step 51 (.step 57 (.run (.close 2)))))) (.step 23 (.step 9 (.run (.close 2))))) (.step 4 (.step 9 (.run (.close 40))))) (.step 4 (.step 9 (.step 55 (.run (.close 57)))))) (.step 4 (.step 9 (.split 56 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.split 38 0 (.step 55 (.split 24 0 (.step 51 (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 31 (.split 56 0 (.step 55 (.split 24 0 (.split 26 0 (.step 21 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part834
namespace Part835
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986643639529917932109824, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203565513497729743562907931884757005057668059697651983850380601712054408681725169013902167855849094662912584187904⟩
def references : Fin 1 → Box := ![Part834.root]
def proof : Enumeration.Proof 1 := (.split 32 0 (.split 53 0 (.split 70 0 (.split 13 0 (.split 46 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.split 47 0 (.step 31 (.split 56 0 (.step 55 (.split 24 0 (.step 51 (.split 31 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 16 0 (.split 22 0 (.step 22 (.split 46 0 (.step 9 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 12 0 (.step 40 (.run (.close 2))) (.step 4 (.run (.close 9)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 13 0 (.split 38 0 (.split 39 0 (.split 58 0 (.split 73 0 (.step 51 (.step 4 (.run (.close 31)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part834.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part835
namespace Part836
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470704195568306223042499969024, 5783586108478331834826161266555599884946511729609277596917677010415947946210831728551740503558426420263990055775475950939192681579408179612179639398064488126960706301562932026094834674344824166240432907932073697208122212352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 24 0 (.split 27 0 (.split 44 0 (.split 74 0 (.step 61 (.step 23 (.step 11 (.run (.close 2))))) (.step 77 (.run (.close 11)))) (.step 23 (.run (.close 11)))) (.step 61 (.step 63 (.step 23 (.run (.close 2)))))) (.step 27 (.run (.close 11)))) (.step 18 (.step 77 (.step 58 (.step 71 (.step 63 (.run (.close 71)))))))) (.step 18 (.split 27 0 (.split 32 0 (.step 71 (.step 63 (.step 58 (.run (.close 11))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))))) (.split 27 0 (.split 32 0 (.step 18 (.step 51 (.step 63 (.step 58 (.run (.close 11)))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58))))) (.step 40 (.step 18 (.run (.close 2))))) (.step 40 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 4 (.step 24 (.run (.close 2))))))) (.split 26 0 (.split 35 0 (.split 72 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.step 23 (.step 5 (.step 61 (.run (.close 23))))) (.step 55 (.run (.close 23)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 55 (.run (.close 23)))) (.step 55 (.run (.close 11)))) (.step 55 (.run (.close 11)))) (.step 55 (.run (.close 11))))) (.split 26 0 (.split 35 0 (.split 72 0 (.split 16 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.step 23 (.step 5 (.step 61 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 11)))) (.step 55 (.run (.close 11)))) (.step 55 (.run (.close 11)))) (.step 2 (.run (.close 11)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part836
namespace Part837
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470704195568306223042499969024, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203565513497729743562907931884758902195258123886197803637398984054736676655792801401219637683977801496530706759680⟩
def references : Fin 1 → Box := ![Part836.root]
def proof : Enumeration.Proof 1 := (.split 38 0 (.split 56 0 (.split 14 0 (.split 73 0 (.split 42 0 (.reuse 0) (.step 40 (.split 27 0 (.split 32 0 (.step 77 (.step 11 (.step 63 (.step 55 (.run (.close 43)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 6 0 (.step 3 (.step 23 (.split 12 0 (.step 3 (.step 2 (.run (.close 24)))) (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 4))))) (.split 18 0 (.split 73 0 (.step 11 (.step 23 (.step 11 (.step 61 (.step 2 (.run (.close 24))))))) (.step 63 (.run (.close 11)))) (.step 63 (.step 23 (.run (.close 68)))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 27 0 (.split 32 0 (.step 63 (.split 35 0 (.split 54 0 (.split 14 0 (.step 3 (.step 2 (.run (.close 24)))) (.step 63 (.run (.close 61)))) (.step 4 (.step 68 (.run (.close 51))))) (.step 63 (.run (.close 5))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4))))) (.split 12 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 54 0 (.split 70 0 (.split 72 0 (.split 14 0 (.step 43 (.step 3 (.step 2 (.run (.close 24))))) (.step 63 (.run (.close 11)))) (.step 63 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 68 (.run (.close 51))))) (.step 63 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part836.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part837
namespace Part838
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702987823078229130736566272, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203565513497729743562907931884758902195258123886197803637398984054736675263357355960739443984103679891823422078976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 48))) (.split 38 0 (.step 26 (.run (.close 2))) (.step 68 (.run (.close 2))))) (.split 12 0 (.split 31 0 (.split 33 0 (.step 5 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 59 0 (.split 6 0 (.split 12 0 (.step 23 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.step 3 (.split 12 0 (.step 23 (.run (.close 2))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 35 0 (.split 54 0 (.split 13 0 (.step 3 (.run (.close 2))) (.step 5 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 32 0 (.split 35 0 (.split 53 0 (.split 54 0 (.split 13 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.step 3 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part838
namespace Part839
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203565513497729743562907931884758902195258123886197803637398984054736676657153930868903391539011891546975190908928⟩
def references : Fin 4 → Box := ![Part833.root, Part835.root, Part837.root, Part838.root]
def proof : Enumeration.Proof 4 := (.split 7 0 (.split 8 0 (.split 6 0 (.reuse 0) (.split 27 0 (.reuse 1) (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 13 0 (.reuse 2) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.step 23 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 24))) (.step 71 (.run (.close 2)))) (.step 63 (.step 23 (.run (.close 71)))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))))) (.split 8 0 (.split 14 0 (.reuse 3) (.split 6 0 (.split 12 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 53 0 (.split 54 0 (.step 3 (.step 23 (.split 70 0 (.split 13 0 (.split 16 0 (.step 31 (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 48 (.step 24 (.run (.close 2))))) (.step 4 (.run (.close 2)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.step 23 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 24))) (.step 71 (.run (.close 2)))) (.step 63 (.step 23 (.run (.close 71)))))) (.step 63 (.run (.close 23)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part833.covered
  · exact Part835.covered
  · exact Part837.covered
  · exact Part838.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part839
namespace Part840
def root : Box := ⟨3351951982485649274893506249551461531869841457496640927204723588819921604307723771576151123450045727629798936078830537828046914166685640871377116357197824, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203567862040312517396135821365355691532285499567061715290572774860502342159064827401467580177411395388278390652928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 53 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 59 0 (.step 2 (.run (.close 57))) (.step 22 (.step 71 (.step 68 (.run (.close 2)))))) (.step 51 (.step 4 (.run (.close 57))))) (.split 7 0 (.split 38 0 (.split 42 0 (.step 43 (.step 55 (.step 57 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 7 0 (.split 38 0 (.split 42 0 (.step 43 (.step 40 (.step 57 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 38 0 (.step 3 (.step 2 (.run (.close 24)))) (.step 4 (.run (.close 2))))) (.step 3 (.split 59 0 (.step 2 (.run (.close 24))) (.step 4 (.run (.close 71)))))) (.split 12 0 (.split 35 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 29))))) (.step 51 (.step 5 (.step 43 (.step 55 (.run (.close 68))))))) (.step 51 (.step 4 (.run (.close 2))))) (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.step 31 (.step 40 (.split 27 0 (.step 51 (.step 63 (.step 55 (.step 43 (.run (.close 24)))))) (.step 4 (.run (.close 2)))))) (.step 4 (.run (.close 43)))) (.step 4 (.run (.close 43)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 55))))) (.split 7 0 (.split 13 0 (.split 18 0 (.split 27 0 (.split 23 0 (.split 32 0 (.step 51 (.step 63 (.step 40 (.step 43 (.run (.close 24)))))) (.step 4 (.run (.close 2)))) (.step 63 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 55 (.run (.close 40)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part840
namespace Part841
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203567862040312517396135821365355691532285499568746711957269691345708208866179045477346855238010276315678222843904⟩
def references : Fin 2 → Box := ![Part839.root, Part840.root]
def proof : Enumeration.Proof 2 := (.split 36 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 1) (.split 44 0 (.split 48 0 (.split 66 0 (.split 46 0 (.split 53 0 (.split 6 0 (.split 47 0 (.step 40 (.step 4 (.step 68 (.run (.close 43))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 55 (.step 68 (.run (.close 2)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))) (.split 44 0 (.split 48 0 (.split 66 0 (.split 46 0 (.split 64 0 (.split 27 0 (.split 7 0 (.split 13 0 (.step 40 (.step 43 (.step 68 (.step 74 (.step 2 (.run (.close 24))))))) (.step 4 (.run (.close 23)))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 68 (.run (.close 43))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))) (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 18 0 (.step 43 (.split 38 0 (.split 46 0 (.step 23 (.step 7 (.run (.close 24)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 23))))) (.step 43 (.run (.close 2)))) (.step 4 (.step 55 (.run (.close 68))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 43))))) (.step 68 (.run (.close 3)))) (.step 4 (.step 68 (.run (.close 43))))) (.step 4 (.step 68 (.run (.close 43))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part839.covered
  · exact Part840.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part841
namespace Part842
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360932430300464025890769090103534313140282909789149810903583200326610559280474658546827395072, 5789234136395748269820059484240009140673214433380719458005661553051941381727209145004229118643083315522363171319276070307209929614264881741064375176288826143668801878795999178994575687995261397639061107105457963973998542848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.step 2 (.run (.close 23))) (.step 51 (.split 19 0 (.split 33 0 (.step 51 (.run (.close 2))) (.step 55 (.run (.close 2)))) (.step 23 (.run (.close 2)))))) (.step 51 (.split 19 0 (.split 33 0 (.step 18 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))) (.step 51 (.split 8 0 (.step 32 (.run (.close 4))) (.step 2 (.run (.close 4)))))) (.split 19 0 (.split 33 0 (.step 51 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 19 0 (.split 33 0 (.step 51 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55))))) (.split 8 0 (.step 32 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 8 0 (.step 32 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 7 0 (.split 47 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 51 (.split 44 0 (.split 46 0 (.step 5 (.step 71 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.step 40 (.run (.close 2)))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.step 4 (.step 40 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part842
namespace Part843
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360932430300464025890769090103534313140282909789149810903583200326610559280474658546827395072, 5789234136395748269820059484240009140673214433380719458005661553051941381727209145004229118643086023207611336177539725894894405677671908367242588061863819544742280941923370540245133524347420958134070086903698083527606140928⟩
def references : Fin 1 → Box := ![Part842.root]
def proof : Enumeration.Proof 1 := (.split 36 0 (.split 42 0 (.split 6 0 (.split 12 0 (.split 26 0 (.reuse 0) (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 47 0 (.split 18 0 (.split 19 0 (.split 48 0 (.split 44 0 (.step 55 (.step 2 (.run (.close 23)))) (.step 9 (.run (.close 2)))) (.step 51 (.run (.close 2)))) (.step 22 (.run (.close 2)))) (.step 21 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 34 (.step 2 (.run (.close 23))))) (.step 40 (.run (.close 12)))) (.step 3 (.run (.close 2)))) (.step 40 (.step 2 (.run (.close 23))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 21 (.step 2 (.run (.close 23))))) (.step 40 (.step 2 (.run (.close 23))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 8 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 39 0 (.split 35 0 (.split 42 0 (.step 2 (.run (.close 23))) (.step 43 (.run (.close 2)))) (.step 40 (.run (.close 31)))) (.step 40 (.run (.close 2)))) (.step 24 (.step 40 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part842.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part843
namespace Part844
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360932430300464025890769090103534313140282909789149810903583200326610559280474658546827395072, 5789234136395748269820059484240009140673214433380719458005661553051941381727209145004229118643086023207611336177539725894894405677671908367242588061863819546427277608620287025451000231461639034013345147502579010927438331904⟩
def references : Fin 1 → Box := ![Part843.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.split 36 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 36 0 (.split 42 0 (.split 14 0 (.split 22 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 26 0 (.split 6 0 (.split 7 0 (.split 12 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 23 (.run (.close 18)))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.step 2 (.run (.close 23)))))) (.step 40 (.step 24 (.step 23 (.run (.close 2)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 40 (.step 23 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part843.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part844
namespace Part845
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438471940926681771988688224387072, 5789234136395748269820059484240009140673214433380719458005661553051941381727209145004229118643083315522363171319276070307209929614264881741064377028962253940727928655931759318001101340315016047889323678466087470858971906048⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 48 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 8 0 (.split 29 0 (.split 57 0 (.step 36 (.step 55 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 32 (.step 2 (.run (.close 23))))) (.step 23 (.run (.close 2)))) (.split 19 0 (.split 33 0 (.step 18 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 19 0 (.split 33 0 (.step 51 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 19 0 (.split 33 0 (.step 51 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55))))) (.step 51 (.run (.close 2)))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2))))) (.step 51 (.run (.close 2)))) (.split 8 0 (.step 32 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 3 (.run (.close 2))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 3 (.run (.close 2))))) (.split 8 0 (.split 29 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 40 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.step 4 (.step 40 (.run (.close 2))))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 3 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part845
namespace Part846
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438471940926681771988688224387072, 5789234136395748269820059484240009140673214433380719458005661553051941381727209145004229118643086023207611336177539725894894405677671908367242588061863819546427277608620285527411821967286147875237629553351769243871480905728⟩
def references : Fin 1 → Box := ![Part845.root]
def proof : Enumeration.Proof 1 := (.split 22 0 (.split 36 0 (.split 42 0 (.split 6 0 (.split 12 0 (.reuse 0) (.split 7 0 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 40 (.step 2 (.run (.close 23))))) (.step 3 (.run (.close 2))))) (.split 7 0 (.split 13 0 (.split 14 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 21 (.step 2 (.run (.close 23))))) (.step 40 (.step 2 (.run (.close 23))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 8 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 35 0 (.split 42 0 (.step 2 (.run (.close 23))) (.step 43 (.run (.close 2)))) (.step 40 (.run (.close 31)))) (.step 40 (.run (.close 2)))) (.step 24 (.step 40 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.run (.close 2)))))) (.split 36 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part845.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part846
namespace Part847
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438471940926681771988688224387072, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203567862040312517396135823354648637171432068190275704544553051747532812055569915239204000750687549746086624100352⟩
def references : Fin 1 → Box := ![Part846.root]
def proof : Enumeration.Proof 1 := (.split 59 0 (.split 16 0 (.split 17 0 (.reuse 0) (.split 36 0 (.split 42 0 (.split 14 0 (.split 22 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 26 0 (.split 6 0 (.split 7 0 (.split 12 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.step 2 (.run (.close 23)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 40 (.step 23 (.run (.close 2)))))) (.split 32 0 (.split 53 0 (.split 70 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.step 15 (.step 2 (.run (.close 55)))))) (.step 55 (.step 2 (.run (.close 23))))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.step 9 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part846.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part847
namespace Part848
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890362967476983852872830468914262951104017973976358212557763349578920057367942249945119508660224, 5789234136395748269820054700174276076862240855547823136952329947857239469447127817783897174735537928976577002542308561680964295048997024359231124641858911374381090632245299645411311664581966193551072150205535679453228695552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 56 0 (.split 73 0 (.split 23 0 (.split 26 0 (.split 8 0 (.split 46 0 (.split 14 0 (.split 35 0 (.split 47 0 (.split 57 0 (.split 12 0 (.split 63 0 (.step 31 (.step 42 (.split 16 0 (.step 42 (.step 68 (.run (.close 31)))) (.step 68 (.run (.close 2)))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 43 (.run (.close 3)))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 71 (.step 43 (.step 68 (.run (.close 2)))))) (.step 63 (.step 42 (.step 68 (.step 18 (.run (.close 68))))))) (.split 47 0 (.step 63 (.step 71 (.step 55 (.run (.close 2))))) (.step 58 (.run (.close 2))))) (.split 27 0 (.step 63 (.step 42 (.step 11 (.run (.close 2))))) (.step 63 (.run (.close 2))))) (.split 46 0 (.split 47 0 (.split 16 0 (.split 27 0 (.step 24 (.step 71 (.step 27 (.run (.close 57))))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 24)))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5))))) (.split 46 0 (.split 47 0 (.split 57 0 (.split 53 0 (.step 24 (.step 3 (.step 55 (.run (.close 3))))) (.step 68 (.run (.close 3)))) (.step 71 (.run (.close 23)))) (.step 71 (.run (.close 23)))) (.step 71 (.step 68 (.run (.close 2)))))) (.split 63 0 (.step 3 (.step 63 (.step 4 (.step 71 (.run (.close 23)))))) (.step 4 (.run (.close 63))))) (.split 8 0 (.split 12 0 (.split 24 0 (.split 14 0 (.split 31 0 (.split 33 0 (.step 3 (.step 58 (.run (.close 2)))) (.step 71 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 4 (.run (.close 63)))) (.step 68 (.step 4 (.run (.close 23))))) (.step 71 (.run (.close 5)))) (.step 68 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part848
namespace Part849
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890362967476983852872830468914262951104017973976358212557763349578920057367942249945119508660224, 5789234136395748269820054700174276076862240855547823136952329947857239469447127817783897174735537928976577005004933948955619245816437030618206987459342615778471507379013637410768922384518758874626466934367414581099157782528⟩
def references : Fin 1 → Box := ![Part848.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 13 0 (.split 38 0 (.reuse 0) (.split 8 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 14 0 (.split 27 0 (.split 39 0 (.split 58 0 (.step 3 (.step 58 (.step 40 (.run (.close 41))))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 42)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 71)))) (.step 68 (.step 4 (.run (.close 42))))) (.step 71 (.step 4 (.run (.close 18))))) (.step 68 (.run (.close 4))))) (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 27 0 (.step 18 (.step 68 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 31)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 13 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 18 (.split 31 0 (.split 33 0 (.split 36 0 (.split 16 0 (.step 9 (.step 4 (.run (.close 68)))) (.step 68 (.run (.close 24)))) (.step 71 (.step 68 (.run (.close 43))))) (.step 4 (.step 43 (.step 23 (.run (.close 31)))))) (.step 4 (.step 43 (.step 23 (.step 43 (.run (.close 57)))))))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 48))))) (.step 71 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 3))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part848.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part849
namespace Part850
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890362967476983852872830468914262951104017973976358212557763349578920057367942249945119508660224, 5789234136395748269820054700174276076862240855547823136952329947857239469447127817783897174735537928976577005004933948955619245816437030618206987459342615778471507380582912844615592575477706230428383539573595062932577714176⟩
def references : Fin 1 → Box := ![Part849.root]
def proof : Enumeration.Proof 1 := (.split 19 0 (.split 7 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 31 0 (.split 27 0 (.split 33 0 (.split 59 0 (.split 32 0 (.step 68 (.step 55 (.step 7 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 18)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 2))))) (.split 8 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 53 0 (.split 74 0 (.split 27 0 (.step 31 (.step 3 (.run (.close 22)))) (.step 4 (.step 2 (.run (.close 23))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 31)))) (.step 68 (.run (.close 22)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 24)))) (.step 43 (.run (.close 3)))) (.step 68 (.step 55 (.run (.close 24))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 58 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.step 43 (.run (.close 2)))))) (.step 68 (.step 55 (.step 40 (.run (.close 29)))))) (.step 68 (.step 63 (.step 24 (.run (.close 9)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part849.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part850
namespace Part851
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890362967476983852872830468914262951104017973976358212557763349578920057367942249945119508660224, 5789234136395748269820059484240009140673214437432980755741006239099214686113105584791270823485895659982676237828965988879652140106075434059536227672061857699442781836367041329196923124859632239444714146857102811229562339328⟩
def references : Fin 1 → Box := ![Part850.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.split 18 0 (.reuse 0) (.split 8 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 27 0 (.step 22 (.step 3 (.step 31 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 23))))) (.step 43 (.step 24 (.run (.close 2))))) (.step 40 (.step 43 (.run (.close 3))))) (.step 68 (.step 55 (.run (.close 42))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.step 2 (.run (.close 4)))))) (.step 68 (.step 55 (.step 43 (.run (.close 2)))))) (.step 68 (.step 40 (.step 55 (.run (.close 2)))))) (.step 68 (.step 63 (.step 24 (.run (.close 9))))))) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 55 (.step 63 (.step 68 (.step 55 (.run (.close 43)))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 58 (.step 63 (.step 55 (.step 23 (.run (.close 68))))))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.step 40 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part850.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part851
namespace Part852
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890362967476983852872830468914262951104017973976358212557763349578920057367942249945119508660224, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203567862040312517396137858401332026018371768014435121335430742814101874802429681617796209619310039652384406241280⟩
def references : Fin 1 → Box := ![Part851.root]
def proof : Enumeration.Proof 1 := (.split 44 0 (.split 48 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 73 0 (.split 14 0 (.step 51 (.split 18 0 (.split 19 0 (.step 68 (.step 55 (.run (.close 43)))) (.step 68 (.run (.close 57)))) (.step 55 (.run (.close 2))))) (.step 63 (.step 55 (.step 23 (.run (.close 68)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 55 (.step 23 (.run (.close 11))))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.step 40 (.run (.close 3))))))) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 73 0 (.split 14 0 (.step 51 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 19 0 (.split 18 0 (.step 71 (.run (.close 55))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))) (.step 63 (.step 55 (.run (.close 11))))) (.step 63 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 55 (.step 63 (.run (.close 11))))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.step 40 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part851.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part852
namespace Part853
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890362967476983852872830468914262951104017973976358212557763349578920057367942249945119508660224, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203567862040312517396137860390624971657518336635964113922714103215926477991820551379652117191948027702517908373504⟩
def references : Fin 1 → Box := ![Part852.root]
def proof : Enumeration.Proof 1 := (.split 29 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 31))) (.step 18 (.step 68 (.run (.close 23))))) (.step 18 (.step 43 (.step 2 (.run (.close 23)))))) (.step 18 (.step 40 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.step 42 (.run (.close 2)))))) (.step 3 (.step 23 (.run (.close 18))))) (.step 3 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 53 (.step 55 (.step 43 (.run (.close 3)))))))) (.step 3 (.step 23 (.step 18 (.run (.close 31)))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 53 (.step 9 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part852.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part853
namespace Part854
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214686113108706539821142317340808359620447203567862040312517396137860390624971657518336635964113922714103215926477991820551379653355131987313082792807497728⟩
def references : Fin 4 → Box := ![Part841.root, Part844.root, Part847.root, Part853.root]
def proof : Enumeration.Proof 4 := (.split 30 0 (.split 9 0 (.split 29 0 (.reuse 0) (.split 59 0 (.reuse 1) (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 23))) (.step 55 (.step 2 (.run (.close 23))))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 2)))))) (.reuse 2)) (.split 9 0 (.reuse 3) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 73 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.split 18 0 (.split 19 0 (.step 18 (.run (.close 2))) (.step 32 (.run (.close 2)))) (.step 32 (.run (.close 2))))) (.step 18 (.step 43 (.run (.close 2))))) (.step 18 (.step 43 (.step 2 (.run (.close 23)))))) (.step 18 (.step 40 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.step 36 (.run (.close 2)))))) (.step 3 (.step 23 (.run (.close 18))))) (.step 3 (.run (.close 2)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 22 (.step 2 (.run (.close 68))))))) (.step 3 (.step 23 (.step 18 (.run (.close 31)))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 22 (.step 2 (.run (.close 68)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part841.covered
  · exact Part844.covered
  · exact Part847.covered
  · exact Part853.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part854
namespace Part855
def root : Box := ⟨3355225373093545416763519439248289131022058097194141409220373652298537141314791418755351844634051761079658851230749072784447687959532527879661741852852224, 5789234136390488133918506326667030631470945080207250724568875136712331776193667893506028658627320474881322054761885006669633470292873100295813602358933494122834404834232354021937000016193710636247961223842775516537291800576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 64 0 (.split 71 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 13 0 (.split 42 0 (.split 72 0 (.split 24 0 (.split 73 0 (.step 61 (.step 53 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 61 (.step 3 (.run (.close 27))))) (.step 62 (.step 61 (.step 2 (.run (.close 68)))))) (.step 62 (.step 3 (.step 24 (.run (.close 2)))))) (.step 3 (.step 57 (.step 5 (.run (.close 2)))))) (.split 14 0 (.split 16 0 (.split 72 0 (.split 13 0 (.split 59 0 (.step 3 (.step 43 (.step 24 (.run (.close 2))))) (.step 57 (.step 3 (.step 43 (.step 2 (.run (.close 68))))))) (.step 68 (.run (.close 22)))) (.step 18 (.run (.close 43)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55))))) (.step 53 (.split 14 0 (.step 53 (.step 21 (.step 61 (.run (.close 53))))) (.step 68 (.run (.close 23)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.step 57 (.split 22 0 (.split 59 0 (.step 2 (.run (.close 24))) (.step 62 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 43)))) (.step 55 (.run (.close 43)))) (.step 68 (.run (.close 27))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 68 (.run (.close 57))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 53 (.split 9 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 53 (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 55 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part855
namespace Part856
def root : Box := ⟨3355225373093545416763519439248289131022058097194141409220373652298537141314791418755351844634051761079658851230749072784447687959532527879661741852852224, 5789234136395748269820054700174276076862240855547819272414806930598894777368627490641135045738721950086896424949326306449213854893680684303146715807978019246266785109191373511789093165523609216652391540284113204210409930752⟩
def references : Fin 1 → Box := ![Part855.root]
def proof : Enumeration.Proof 1 := (.split 38 0 (.split 56 0 (.split 53 0 (.split 70 0 (.split 63 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 9 0 (.step 52 (.split 18 0 (.split 19 0 (.split 23 0 (.step 68 (.step 63 (.step 55 (.step 68 (.step 57 (.run (.close 66))))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 3 (.step 62 (.step 3 (.step 71 (.run (.close 63))))))) (.split 13 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 31 (.step 55 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 55)))) (.step 71 (.run (.close 55)))) (.step 4 (.run (.close 63))))) (.split 53 0 (.split 13 0 (.split 63 0 (.step 55 (.step 3 (.run (.close 57)))) (.step 71 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 68))))) (.split 36 0 (.split 53 0 (.split 13 0 (.split 42 0 (.split 56 0 (.split 63 0 (.step 55 (.step 3 (.step 57 (.step 68 (.run (.close 21)))))) (.step 71 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part855.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part856
namespace Part857
def root : Box := ⟨3355225373093545416763519439248289131022058097194141409220373652298537141314791418755351844634051761079658851230749072784447687959532527879661741852852224, 5789234136395748269820054700174276076862240855547819272414806930598894777368627490641135045738721950086896424949326306449213857029667720224058695340589789604364719498914278211124131087993978893873341002906868490517692284928⟩
def references : Fin 1 → Box := ![Part856.root]
def proof : Enumeration.Proof 1 := (.split 27 0 (.split 32 0 (.split 8 0 (.reuse 0) (.split 38 0 (.split 26 0 (.split 13 0 (.split 35 0 (.split 73 0 (.split 18 0 (.split 24 0 (.split 19 0 (.split 23 0 (.split 53 0 (.split 58 0 (.split 36 0 (.split 9 0 (.step 61 (.step 11 (.run (.close 2)))) (.step 55 (.step 18 (.step 55 (.run (.close 2)))))) (.step 55 (.run (.close 68)))) (.step 61 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 55 (.step 24 (.run (.close 2))))) (.step 55 (.step 24 (.run (.close 2))))) (.step 61 (.run (.close 27)))) (.step 55 (.step 31 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 55 (.step 24 (.run (.close 11))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 55 (.run (.close 27)))) (.step 68 (.step 4 (.run (.close 55)))))) (.split 13 0 (.split 38 0 (.split 73 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 36 0 (.split 42 0 (.step 61 (.step 53 (.step 61 (.step 42 (.step 2 (.run (.close 4))))))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 36)))) (.step 4 (.run (.close 3)))) (.step 3 (.run (.close 53)))) (.step 3 (.step 53 (.run (.close 2))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 36 0 (.step 27 (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 3 (.step 71 (.run (.close 5)))))) (.step 3 (.step 53 (.step 5 (.run (.close 9)))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part856.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part857
namespace Part858
def root : Box := ⟨3355225373093545416763519439248289131022058097194141409220373652298537141314791418755351844634051761079658851230749072784447687959532527879661741852852224, 5789234136395748269820059484240009140673214437432976891203483221840869994034605257648508694489079681092995657773358346373246751319306123665387935553309031525335993954696874200164595748517546555862521302187349120409904611328⟩
def references : Fin 1 → Box := ![Part857.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.split 7 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 16 0 (.split 17 0 (.step 9 (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 5 (.run (.close 23))))) (.step 4 (.step 5 (.run (.close 23))))) (.step 5 (.step 3 (.step 63 (.run (.close 4)))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 55 (.split 26 0 (.split 30 0 (.split 36 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 71 (.step 68 (.run (.close 55)))))) (.step 71 (.step 68 (.step 71 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 55 (.step 40 (.run (.close 29)))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 68 (.step 55 (.run (.close 68))))) (.step 63 (.step 68 (.step 71 (.step 55 (.run (.close 68))))))) (.step 55 (.step 68 (.step 23 (.step 55 (.run (.close 18))))))) (.step 55 (.step 23 (.run (.close 11))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part857.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part858
namespace Part859
def root : Box := ⟨3355225373093545416763519439248289131022058097194141409220373652298537141314791418755351844634051761079658851230749072784447687959532527879661741852852224, 5789234136395748269820059484240009140673214437432980755741006239099214689386499311384403309408640769125224108174915546490531705850881519016114142847625813754572145762977115057214416618436323705394090217243777105676025724928⟩
def references : Fin 1 → Box := ![Part858.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.split 57 0 (.reuse 0) (.split 36 0 (.split 38 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 42 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 55)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 31)))) (.step 4 (.run (.close 31)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.run (.close 55)))) (.step 63 (.run (.close 55)))) (.step 63 (.step 58 (.run (.close 2))))) (.step 4 (.step 71 (.step 63 (.step 68 (.run (.close 2)))))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 6 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 24 0 (.split 26 0 (.step 32 (.run (.close 2))) (.step 71 (.step 63 (.run (.close 55))))) (.step 55 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 71 (.step 68 (.step 55 (.run (.close 3)))))) (.step 3 (.step 55 (.step 57 (.step 2 (.run (.close 68))))))) (.step 63 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.step 71 (.step 55 (.run (.close 68))))))) (.step 55 (.run (.close 3)))) (.step 55 (.step 63 (.step 68 (.step 23 (.step 55 (.run (.close 3)))))))) (.step 55 (.step 63 (.step 23 (.run (.close 11)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part858.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part859
namespace Part860
def root : Box := ⟨3355225373093545416763519439248289131022058097194141409220373652298537141314791418755351844634051761079658851230749072784447687959532527879661741852852224, 5789234136395748269820059484240009140673214437432980755741006239099214689386499314435963009491316738407505183211913783520859594560517663301922595087621800969861987055657622373879370268741694417142011653395448583251797475328⟩
def references : Fin 1 → Box := ![Part859.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 32 0 (.split 74 0 (.split 6 0 (.split 12 0 (.split 24 0 (.step 32 (.split 9 0 (.step 51 (.step 55 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.run (.close 31)))) (.step 4 (.step 71 (.step 68 (.run (.close 55)))))) (.step 63 (.step 71 (.step 68 (.step 4 (.run (.close 55))))))) (.step 63 (.run (.close 55)))) (.step 63 (.run (.close 55))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 55))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 31)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 63 (.step 2 (.run (.close 4)))))) (.step 63 (.step 4 (.step 58 (.run (.close 2)))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part859.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part860
namespace Part861
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136390488133918506326662468190853322884988609552963174845387438547689616004090973042154355955277421579672465658356405029351574234712896388612174245413116222845771117139084939185677204115254593340005891805976092213248⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 71 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 59 0 (.split 72 0 (.split 13 0 (.split 73 0 (.split 24 0 (.split 74 0 (.split 9 0 (.step 61 (.step 2 (.run (.close 68)))) (.step 3 (.run (.close 2)))) (.step 61 (.step 55 (.step 2 (.run (.close 24)))))) (.step 61 (.step 27 (.run (.close 2))))) (.step 3 (.run (.close 5)))) (.step 3 (.run (.close 52)))) (.step 62 (.step 57 (.step 2 (.run (.close 23)))))) (.step 62 (.step 52 (.step 57 (.run (.close 2)))))) (.split 16 0 (.split 17 0 (.step 57 (.step 3 (.split 22 0 (.step 52 (.step 3 (.step 18 (.run (.close 62))))) (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.step 53 (.split 17 0 (.step 57 (.step 9 (.step 52 (.split 9 0 (.step 43 (.step 55 (.step 2 (.run (.close 40))))) (.step 55 (.step 2 (.run (.close 40)))))))) (.step 68 (.run (.close 55)))))) (.split 16 0 (.split 6 0 (.split 17 0 (.step 57 (.split 22 0 (.split 74 0 (.split 12 0 (.step 2 (.run (.close 40))) (.step 15 (.split 33 0 (.split 41 0 (.step 29 (.run (.close 2))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 43)))) (.step 57 (.step 9 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 43)))))) (.split 31 0 (.split 41 0 (.split 9 0 (.step 57 (.run (.close 68))) (.step 55 (.run (.close 57)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.run (.close 52)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part861
namespace Part862
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136395748269820054700174276076862240855547819272414806930598894777371824161156658621783656705650204624783787483672647834584720454770827233651045754837179561811960051524899143830619691476941742991090084817427207553024⟩
def references : Fin 1 → Box := ![Part861.root]
def proof : Enumeration.Proof 1 := (.split 56 0 (.split 53 0 (.split 70 0 (.split 63 0 (.split 64 0 (.reuse 0) (.step 53 (.split 9 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 59 0 (.step 68 (.run (.close 57))) (.step 61 (.step 68 (.run (.close 62))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 55 (.run (.close 2)))))) (.step 52 (.split 31 0 (.split 33 0 (.split 41 0 (.split 9 0 (.step 52 (.split 18 0 (.split 19 0 (.step 71 (.step 55 (.step 68 (.run (.close 57))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))))) (.step 62 (.step 4 (.step 62 (.step 3 (.step 61 (.step 71 (.run (.close 4))))))))) (.split 73 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 26 0 (.split 35 0 (.split 36 0 (.step 3 (.run (.close 61))) (.step 4 (.run (.close 57)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 61)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 63))))) (.split 36 0 (.split 53 0 (.split 13 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 3 (.run (.close 57))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 18))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part861.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part862
namespace Part863
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136395748269820054700174276076862240855547819272414806930598894777371824161156658621783656705650204627246412870947302785352160461029803096468529459241269978558728389290256755942991929598497330267379704408364051070976⟩
def references : Fin 1 → Box := ![Part862.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 38 0 (.reuse 0) (.split 36 0 (.split 42 0 (.split 53 0 (.split 70 0 (.split 13 0 (.split 56 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 3 (.step 57 (.step 43 (.step 2 (.run (.close 4)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 18))))) (.step 71 (.step 68 (.step 58 (.run (.close 18))))))) (.split 38 0 (.split 56 0 (.split 26 0 (.split 35 0 (.split 13 0 (.split 73 0 (.split 24 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 36 0 (.step 61 (.step 52 (.run (.close 17)))) (.step 68 (.run (.close 55)))) (.step 55 (.run (.close 34)))) (.step 31 (.run (.close 52)))) (.step 55 (.step 31 (.run (.close 52))))) (.step 61 (.step 52 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 17))))) (.step 55 (.step 68 (.run (.close 52))))) (.step 68 (.step 4 (.run (.close 55))))) (.step 68 (.step 4 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part862.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part863
namespace Part864
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136395748269820054700174276076862240855547819272414806930598894777371824161156658621783656705650204627246412870947302787488147496950713178863551165410822093161432911646909525890033537420717057256946074045955312713728⟩
def references : Fin 1 → Box := ![Part863.root]
def proof : Enumeration.Proof 1 := (.split 32 0 (.split 8 0 (.reuse 0) (.split 38 0 (.split 56 0 (.split 26 0 (.split 35 0 (.split 13 0 (.split 73 0 (.split 24 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 53 0 (.split 58 0 (.split 31 0 (.split 33 0 (.split 36 0 (.split 17 0 (.split 9 0 (.step 63 (.step 61 (.run (.close 11)))) (.step 55 (.run (.close 52)))) (.step 24 (.run (.close 11)))) (.step 55 (.run (.close 68)))) (.step 55 (.step 31 (.run (.close 2))))) (.step 55 (.step 31 (.run (.close 2))))) (.step 61 (.run (.close 2)))) (.step 68 (.run (.close 61)))) (.step 55 (.step 24 (.step 2 (.run (.close 23)))))) (.step 55 (.step 31 (.step 2 (.run (.close 23)))))) (.step 55 (.step 31 (.step 2 (.run (.close 23)))))) (.step 61 (.step 9 (.run (.close 27))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 11))))) (.step 55 (.step 43 (.run (.close 27))))) (.step 68 (.step 4 (.run (.close 55))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 13 0 (.split 38 0 (.split 73 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 36 0 (.split 42 0 (.split 63 0 (.step 61 (.step 3 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.run (.close 36)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 3 (.step 53 (.step 71 (.run (.close 5))))))) (.step 4 (.step 53 (.step 3 (.step 71 (.run (.close 5))))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part863.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part864
namespace Part865
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136395748269820054700174276076862240855547819272414806930598894777371824161156658621783656705650204627246412870947302787488147496950715076001141229599367912948451293989591793865462299275718279731183051315388744728576⟩
def references : Fin 1 → Box := ![Part864.root]
def proof : Enumeration.Proof 1 := (.split 7 0 (.split 27 0 (.reuse 0) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 36 0 (.step 27 (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 36)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 3 (.step 52 (.split 8 0 (.step 57 (.step 3 (.step 71 (.run (.close 63))))) (.step 4 (.run (.close 63)))))))) (.step 4 (.step 3 (.step 27 (.run (.close 71)))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63))))) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 16 0 (.split 17 0 (.step 9 (.step 57 (.step 52 (.step 57 (.step 71 (.run (.close 2))))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.step 4 (.step 63 (.run (.close 2)))))) (.step 4 (.step 5 (.run (.close 23))))) (.step 5 (.run (.close 3)))) (.step 5 (.step 3 (.step 63 (.run (.close 4)))))) (.step 63 (.step 4 (.step 2 (.run (.close 5)))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part864.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part865
namespace Part866
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136395748269820059484240009140673214437432980755741006239099214689389692860151376569461344143091302517305696362390477971338210436585810898136438433983955218906411067343710919568973522680616133496363689021544360574976⟩
def references : Fin 1 → Box := ![Part865.root]
def proof : Enumeration.Proof 1 := (.split 57 0 (.split 66 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 22 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 55 (.split 50 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.step 71 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.step 63 (.run (.close 3)))))) (.step 71 (.step 68 (.step 71 (.step 55 (.run (.close 40))))))) (.step 71 (.step 68 (.step 71 (.step 55 (.step 40 (.run (.close 29)))))))) (.step 63 (.step 55 (.run (.close 68))))) (.step 68 (.step 55 (.run (.close 68))))) (.step 58 (.step 55 (.run (.close 68))))) (.step 55 (.step 63 (.step 23 (.run (.close 17)))))) (.step 55 (.step 63 (.step 23 (.run (.close 11))))))) (.split 36 0 (.split 38 0 (.split 8 0 (.split 14 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 26 0 (.split 35 0 (.step 55 (.split 50 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 18)))) (.step 4 (.run (.close 55)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 4 (.step 71 (.step 68 (.step 2 (.run (.close 48))))))) (.step 71 (.step 63 (.run (.close 62))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 4 (.step 71 (.step 63 (.step 58 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part865.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part866
namespace Part867
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136395748269820059484240009140673214437432980755741006239099214689389695981899926885453575524688532310472002110988620636309361295742770523508177253749575339212514130835682079395904644087239028944339368309829666865152⟩
def references : Fin 1 → Box := ![Part866.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 7 0 (.split 22 0 (.split 30 0 (.split 74 0 (.split 6 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 29 0 (.split 35 0 (.step 12 (.step 2 (.run (.close 23)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 32 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 55))))) (.step 55 (.step 2 (.run (.close 23))))) (.step 3 (.step 55 (.step 2 (.run (.close 40)))))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 3 (.step 55 (.step 57 (.step 2 (.run (.close 68))))))) (.step 63 (.run (.close 55)))) (.step 71 (.step 18 (.run (.close 2))))) (.step 68 (.step 71 (.step 55 (.run (.close 68)))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 68 (.step 71 (.step 55 (.run (.close 68))))))) (.step 58 (.step 55 (.step 23 (.run (.close 31)))))) (.step 55 (.step 63 (.step 23 (.step 31 (.run (.close 55))))))) (.step 55 (.step 63 (.step 23 (.step 61 (.run (.close 11))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part866.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part867
namespace Part868
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738077812566966403072, 5789234136395748269820059484240009140673214437432980755741006239099214689389695984951486585536251493970813385509000348018948525018997440028578975748173240964865180505194638152347033046210014798986950380491039787405438615552⟩
def references : Fin 1 → Box := ![Part867.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 36 0 (.split 38 0 (.split 16 0 (.split 17 0 (.split 7 0 (.split 22 0 (.split 30 0 (.split 42 0 (.split 32 0 (.split 74 0 (.split 6 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 39 0 (.step 18 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 55 (.run (.close 2))))) (.step 4 (.step 55 (.run (.close 2))))) (.step 4 (.run (.close 31)))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 31)))) (.step 63 (.step 58 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 58 (.run (.close 31)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.step 58 (.step 2 (.run (.close 4))))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 8 0 (.split 14 0 (.split 36 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 42 0 (.split 50 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 55 (.step 2 (.run (.close 4))))) (.step 55 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 31)))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 58 (.run (.close 31)))) (.step 71 (.step 63 (.step 58 (.step 2 (.run (.close 4))))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part867.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part868
namespace Part869
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395748269820059484240009140673214437432980755741006239099214689389695984951486588375465260750527801717296472581466237337909005213415148722744331514237399698155276145280824896848942770715550404968297340274976227328⟩
def references : Fin 3 → Box := ![Part854.root, Part860.root, Part868.root]
def proof : Enumeration.Proof 3 := (.split 49 0 (.split 50 0 (.reuse 0) (.split 44 0 (.reuse 1) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 6 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 58 (.step 55 (.run (.close 3))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 58 (.step 55 (.run (.close 3))))) (.step 58 (.step 55 (.run (.close 3))))) (.step 55 (.step 63 (.run (.close 11))))) (.step 55 (.step 63 (.run (.close 11))))))) (.split 44 0 (.reuse 2) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 74 0 (.split 6 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 63 0 (.step 2 (.run (.close 23))) (.step 63 (.run (.close 12)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 55 (.step 63 (.run (.close 3))))) (.step 55 (.step 48 (.run (.close 3))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 58 (.step 18 (.run (.close 2))))) (.step 58 (.step 55 (.run (.close 68))))) (.step 58 (.step 55 (.run (.close 3))))) (.step 58 (.step 68 (.step 18 (.run (.close 2)))))) (.step 55 (.step 63 (.run (.close 27))))) (.step 55 (.step 63 (.run (.close 27)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part854.covered
  · exact Part860.covered
  · exact Part868.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part869
namespace Part870
def root : Box := ⟨5136851466355833503165029182500125649951503713694505725518241926888708019324249239896839008703423927049448899954501901665811546825206865160554331153690584315042362662957884391360017341545551390193660641411072, 5789234131009374243485986584588438705696133760256265754490267127221081799720565100350150190848989688136315389397189488922978316211623119640057815062637823180809334573385408143303386681617693303853303148450678881604599808000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 16 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 72 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 2 (.run (.close 58))))) (.split 72 0 (.split 6 0 (.split 12 0 (.split 74 0 (.split 38 0 (.step 36 (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.run (.close 31)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 72 0 (.split 57 0 (.split 38 0 (.split 74 0 (.split 56 0 (.split 6 0 (.step 36 (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 6 0 (.step 5 (.split 7 0 (.step 36 (.split 17 0 (.step 48 (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 63))))) (.step 5 (.run (.close 2))))) (.step 4 (.run (.close 5))))) (.split 72 0 (.split 57 0 (.split 38 0 (.split 56 0 (.split 14 0 (.split 74 0 (.split 53 0 (.split 6 0 (.split 9 0 (.split 36 0 (.split 7 0 (.step 36 (.run (.close 5))) (.step 5 (.run (.close 2)))) (.step 68 (.run (.close 23)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 61)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 2))))) (.split 6 0 (.step 5 (.split 7 0 (.step 31 (.split 13 0 (.split 18 0 (.step 61 (.run (.close 2))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 57)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part870
namespace Part871
def root : Box := ⟨5136851466355833503165029182500125649951503713694505725518241926888708019324249239896839008703423927049448899954501901665811546825206865160554331153690584315042362662957884391360017341545551390193660641411072, 5789234131009374243485986584588438705696133760256265754490267127221081799720565103401709890931665657418596464434187728246804820911330775536687164457394178989723291811482799336563705371165694754335057285942247595916132352000⟩
def references : Fin 1 → Box := ![Part870.root]
def proof : Enumeration.Proof 1 := (.split 26 0 (.split 35 0 (.split 46 0 (.split 47 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.split 36 0 (.split 12 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.run (.close 2))))) (.split 16 0 (.split 8 0 (.split 12 0 (.split 54 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 48))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 48)))) (.step 63 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 31 0 (.step 18 (.split 33 0 (.step 4 (.split 8 0 (.step 18 (.run (.close 57))) (.step 4 (.run (.close 68))))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 55)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 32 0 (.split 53 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 31 0 (.split 33 0 (.step 4 (.split 8 0 (.split 14 0 (.step 18 (.run (.close 57))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part870.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part871
namespace Part872
def root : Box := ⟨5136851466355833503165029182500125649951503713694505725518241926888708019324249239896839008703423927049448899954501901665811546825206865160554331153690584315042362662957884391360017341545551390193660641411072, 5789234136395753406671525840073507850193981290883612502975573741914189889636173156339873494044317196740154948701156241090881581538879719911778214233266991940563467695617797026159419514425778099072144311478023769060620107776⟩
def references : Fin 1 → Box := ![Part871.root]
def proof : Enumeration.Proof 1 := (.split 64 0 (.split 66 0 (.split 71 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 53 0 (.step 22 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 55)))) (.step 71 (.run (.close 36)))) (.step 71 (.run (.close 36)))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 2 (.run (.close 4)))))) (.split 8 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.run (.close 68))))) (.split 35 0 (.split 36 0 (.split 8 0 (.split 14 0 (.split 42 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 36)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part871.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part872
namespace Part873
def root : Box := ⟨5136851466355833503165029182500125649951503713694505725518241926888708019324249239896839008703423927049448899954501901665811546825206865160554331153690584315042362662957884391360017341545551390193660641411072, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231016279241839348290219091472249369504048630538175399118282568294201050621792469922030686745149382581692720533588939399943372652754763776⟩
def references : Fin 1 → Box := ![Part872.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.split 63 0 (.reuse 0) (.split 35 0 (.split 36 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 49 0 (.split 50 0 (.split 56 0 (.split 7 0 (.split 13 0 (.step 31 (.split 64 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2))))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 36)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2)))))) (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 39 0 (.split 54 0 (.split 58 0 (.split 72 0 (.split 74 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 57)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part872.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part873
namespace Part874
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439738353586870716009910028468224, 5789234136395753406671521056007779241891423355673469220144558200283075591420213983227134161609725830611241029990053084777579195804112336065946867801687950962879679381504478618695548087790068567572835331050741085733990170624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 18 0 (.split 36 0 (.split 73 0 (.split 58 0 (.split 19 0 (.split 14 0 (.split 23 0 (.split 17 0 (.split 53 0 (.split 16 0 (.step 52 (.step 31 (.run (.close 68)))) (.step 68 (.run (.close 31)))) (.step 63 (.run (.close 61)))) (.step 24 (.step 63 (.step 68 (.run (.close 31)))))) (.split 35 0 (.step 24 (.run (.close 3))) (.step 68 (.run (.close 40))))) (.step 63 (.split 16 0 (.split 17 0 (.step 68 (.step 18 (.step 31 (.run (.close 68))))) (.step 24 (.run (.close 17)))) (.step 24 (.run (.close 17)))))) (.step 31 (.split 63 0 (.split 35 0 (.split 64 0 (.step 18 (.step 24 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 2)))))) (.step 61 (.step 52 (.split 19 0 (.step 31 (.run (.close 68))) (.step 43 (.run (.close 23))))))) (.split 53 0 (.step 62 (.step 3 (.step 63 (.step 58 (.run (.close 5)))))) (.step 63 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.step 68 (.step 18 (.step 43 (.run (.close 2))))) (.step 68 (.run (.close 4)))) (.step 68 (.step 71 (.run (.close 24))))) (.step 43 (.step 68 (.run (.close 4))))) (.step 43 (.step 23 (.step 24 (.run (.close 5))))))) (.split 35 0 (.split 63 0 (.split 31 0 (.step 31 (.split 64 0 (.split 71 0 (.step 18 (.split 14 0 (.step 31 (.step 54 (.step 43 (.step 24 (.run (.close 2)))))) (.step 68 (.step 63 (.run (.close 24)))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))) (.step 43 (.step 24 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 53)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part874
namespace Part875
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439738353586870716009910028468224, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499251329920121937920921271160321399806999961021452946613856735643286076769659141449313181929656486171846471004366291598220900099575669166440448⟩
def references : Fin 1 → Box := ![Part874.root]
def proof : Enumeration.Proof 1 := (.split 56 0 (.split 47 0 (.split 57 0 (.reuse 0) (.split 18 0 (.split 19 0 (.split 23 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 49 0 (.step 68 (.step 71 (.run (.close 55)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 3)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 63 (.run (.close 3)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 18))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 57 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 49 0 (.step 68 (.step 71 (.run (.close 55)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 3)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 63 (.run (.close 3)))) (.step 58 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 18))))) (.split 24 0 (.split 35 0 (.split 14 0 (.split 39 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 49 0 (.split 58 0 (.step 39 (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 71 (.run (.close 5)))) (.step 63 (.run (.close 54)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 55 (.run (.close 2))))) (.step 4 (.step 68 (.step 55 (.run (.close 2)))))) (.step 58 (.run (.close 61)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 58 (.run (.close 61)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part874.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part875
namespace Part876
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439738353586870716009910028468224, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961190638509073572673536466321868631648628994594095980313053984261768339216273063328971533035674032910105237610326654976⟩
def references : Fin 1 → Box := ![Part875.root]
def proof : Enumeration.Proof 1 := (.split 12 0 (.split 46 0 (.split 26 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 53 0 (.split 70 0 (.split 18 0 (.split 47 0 (.split 57 0 (.split 16 0 (.step 15 (.step 7 (.step 68 (.run (.close 18))))) (.step 68 (.run (.close 43)))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68)))) (.step 71 (.step 18 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 68 (.step 43 (.run (.close 31)))))) (.step 68 (.step 4 (.step 43 (.run (.close 31)))))) (.step 68 (.step 4 (.step 43 (.run (.close 31))))))) (.split 18 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 39 0 (.split 47 0 (.split 19 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 36 0 (.step 71 (.step 63 (.run (.close 2)))) (.step 55 (.run (.close 4)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.run (.close 64)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 31)))) (.step 71 (.step 68 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 58 (.run (.close 31)))) (.step 55 (.step 71 (.run (.close 2)))))) (.split 53 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 18 (.split 69 0 (.split 16 0 (.split 17 0 (.split 31 0 (.split 33 0 (.step 15 (.run (.close 24))) (.step 18 (.step 24 (.run (.close 3))))) (.step 18 (.run (.close 15)))) (.step 68 (.step 63 (.run (.close 24))))) (.step 68 (.step 63 (.run (.close 24))))) (.step 71 (.step 63 (.run (.close 57)))))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5)))) (.step 71 (.step 58 (.run (.close 5))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 63 (.step 58 (.run (.close 5)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part875.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part876
namespace Part877
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439738353586870716009910028468224, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961193101134460847328489369748910811534574207099506553955585333734628461226653728946242568647040743857882810986662985728⟩
def references : Fin 1 → Box := ![Part876.root]
def proof : Enumeration.Proof 1 := (.split 32 0 (.split 38 0 (.reuse 0) (.split 14 0 (.split 24 0 (.split 12 0 (.split 39 0 (.split 18 0 (.split 19 0 (.split 35 0 (.split 46 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 58 0 (.step 58 (.step 23 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.run (.close 58)))) (.step 71 (.run (.close 33)))) (.step 58 (.run (.close 68)))) (.step 55 (.run (.close 18)))) (.step 58 (.run (.close 2)))) (.step 71 (.run (.close 48)))) (.step 68 (.step 55 (.run (.close 18))))) (.step 55 (.step 71 (.step 2 (.run (.close 4)))))) (.step 58 (.run (.close 42)))) (.step 68 (.step 58 (.run (.close 5))))) (.step 58 (.step 68 (.run (.close 3))))) (.step 68 (.step 63 (.run (.close 13)))))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 46 0 (.split 47 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 24 0 (.split 38 0 (.split 31 0 (.split 33 0 (.split 57 0 (.step 54 (.step 31 (.step 4 (.step 23 (.run (.close 31)))))) (.step 63 (.run (.close 2)))) (.step 3 (.run (.close 31)))) (.step 31 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 68 (.run (.close 31)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.step 2 (.run (.close 4)))))) (.step 68 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.run (.close 63)))) (.step 71 (.run (.close 63)))) (.step 71 (.run (.close 63)))) (.step 43 (.step 63 (.step 40 (.step 24 (.run (.close 2))))))) (.step 40 (.run (.close 36)))) (.step 40 (.step 23 (.run (.close 2))))) (.step 71 (.step 4 (.step 63 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part876.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part877
namespace Part878
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439738353586870716009910028468224, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961193101134460847328489369748910811534574207099506553955585333734628461226653730307372036330794597712534162218342678528⟩
def references : Fin 1 → Box := ![Part877.root]
def proof : Enumeration.Proof 1 := (.split 13 0 (.split 6 0 (.reuse 0) (.split 32 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 16 0 (.split 70 0 (.split 57 0 (.split 73 0 (.split 69 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 14 0 (.step 57 (.step 15 (.step 18 (.step 68 (.run (.close 43)))))) (.step 18 (.run (.close 15)))) (.step 68 (.run (.close 24)))) (.step 18 (.run (.close 9)))) (.step 18 (.run (.close 9)))) (.step 68 (.step 24 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 57))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.run (.close 3)))) (.step 71 (.step 63 (.run (.close 3))))) (.step 68 (.step 24 (.run (.close 2))))) (.step 71 (.step 48 (.run (.close 3))))) (.step 58 (.run (.close 18)))) (.step 58 (.run (.close 18)))) (.step 71 (.step 48 (.run (.close 3)))))) (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 41 0 (.split 46 0 (.split 47 0 (.split 64 0 (.split 53 0 (.step 18 (.split 57 0 (.split 38 0 (.split 56 0 (.split 74 0 (.split 16 0 (.step 54 (.step 18 (.run (.close 2)))) (.step 63 (.step 4 (.step 63 (.run (.close 2)))))) (.step 63 (.run (.close 4)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.step 71 (.run (.close 16)))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 48)))) (.step 63 (.step 71 (.step 2 (.run (.close 4)))))) (.step 58 (.run (.close 2)))) (.step 4 (.step 40 (.step 24 (.run (.close 2)))))) (.step 71 (.run (.close 18)))) (.step 4 (.step 68 (.run (.close 18))))) (.step 71 (.run (.close 18)))) (.step 4 (.step 40 (.step 24 (.run (.close 2)))))) (.step 4 (.step 40 (.step 24 (.run (.close 2)))))) (.step 63 (.step 4 (.step 2 (.run (.close 5)))))) (.step 63 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part877.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part878
namespace Part879
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439738353586870716009910028468224, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961193101134460847328489369748910811534574207099506553955585333734628461226653730307372036330795807818945397564928688128⟩
def references : Fin 1 → Box := ![Part878.root]
def proof : Enumeration.Proof 1 := (.split 7 0 (.split 8 0 (.reuse 0) (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 32 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 70 0 (.split 69 0 (.split 6 0 (.split 12 0 (.split 58 0 (.split 17 0 (.split 36 0 (.split 42 0 (.step 11 (.step 24 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 24 (.run (.close 11)))) (.step 61 (.run (.close 68)))) (.step 68 (.step 24 (.run (.close 23))))) (.step 24 (.step 18 (.run (.close 9))))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 7)))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 4)))) (.step 63 (.step 4 (.run (.close 68))))) (.step 68 (.step 63 (.run (.close 7))))) (.step 23 (.step 24 (.run (.close 3))))) (.step 23 (.step 63 (.step 24 (.run (.close 40)))))) (.step 23 (.step 24 (.run (.close 3))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 46 0 (.split 18 0 (.step 7 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 5))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 18)))) (.step 71 (.run (.close 18)))) (.step 71 (.run (.close 18)))) (.step 40 (.step 4 (.step 24 (.run (.close 2)))))) (.step 40 (.step 4 (.step 24 (.run (.close 2)))))) (.step 40 (.step 4 (.step 24 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part878.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part879
namespace Part880
def root : Box := ⟨4784065733063810973581885157618788676291241978568617960252656648542256607282467631102665487188022377325179999333882336758599463442389545816181639518497005011282036281101727533884970605019084829491200, 5789234136395753406671525840073512305702396937558630707244719933604936855679637266261680700287010457751060425925166500771361383659387314252865711557408812663472679576535606792949386366259701553321198578975220055455750422528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 18 (.split 46 0 (.step 55 (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 68))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 43 (.step 71 (.run (.close 68)))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 55 (.step 43 (.run (.close 31))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 71 (.step 68 (.run (.close 43)))))) (.step 68 (.step 71 (.step 55 (.run (.close 3)))))) (.step 58 (.step 63 (.step 55 (.step 68 (.step 55 (.run (.close 43)))))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 48 (.step 40 (.step 24 (.run (.close 15)))))) (.step 58 (.step 43 (.step 18 (.step 43 (.step 68 (.run (.close 3)))))))) (.step 63 (.step 58 (.step 68 (.step 2 (.run (.close 4))))))) (.step 68 (.step 48 (.step 40 (.step 18 (.step 40 (.run (.close 55))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part880
namespace Part881
def root : Box := ⟨3351951985607397825209498480933058761663007760896696487095861511789597967143758483020234194662031959985999935706448443834846361249034846395298195334758400, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231016279241839348290219091472249369504048630538173409825336929147632429092799882638670284920546193190822959944094026950899343741056712704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 39 0 (.split 46 0 (.split 47 0 (.step 68 (.step 55 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 48)))) (.step 71 (.run (.close 68)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 43 (.step 71 (.run (.close 68)))))) (.step 43 (.step 18 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 55 (.step 43 (.run (.close 31))))) (.step 55 (.step 43 (.step 2 (.run (.close 55)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 71 (.step 68 (.run (.close 3)))))) (.step 68 (.step 71 (.step 55 (.run (.close 3)))))) (.step 58 (.step 55 (.step 43 (.step 23 (.step 68 (.run (.close 3)))))))) (.step 63 (.step 58 (.step 68 (.run (.close 2)))))) (.step 48 (.step 40 (.step 18 (.step 55 (.run (.close 3))))))) (.step 58 (.step 55 (.step 43 (.step 18 (.step 23 (.run (.close 11)))))))) (.step 63 (.step 58 (.step 68 (.step 2 (.run (.close 4))))))) (.step 68 (.step 48 (.step 40 (.step 18 (.step 40 (.run (.close 55))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part881
namespace Part882
def root : Box := ⟨3351951982485649274896345463318241246286049751272660862143209272495625843691361315291017946760918817560500898338472151641411466953611347973562779566080000, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004635299768373932021760949449738594661509903718722978465019075599308277854338043829750931672694051428156896610594324480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 54 0 (.step 18 (.split 49 0 (.split 50 0 (.step 51 (.step 3 (.run (.close 4)))) (.step 71 (.run (.close 68)))) (.step 68 (.step 71 (.run (.close 68)))))) (.step 71 (.run (.close 68)))) (.step 68 (.step 55 (.step 2 (.run (.close 48)))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 43 (.step 18 (.run (.close 2))))) (.step 43 (.step 18 (.run (.close 2))))) (.step 55 (.step 43 (.run (.close 31))))) (.step 55 (.step 43 (.step 2 (.run (.close 55)))))) (.step 55 (.step 23 (.step 2 (.run (.close 55)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 71 (.step 24 (.run (.close 29)))))) (.step 68 (.step 71 (.step 55 (.run (.close 3)))))) (.step 55 (.step 63 (.step 43 (.run (.close 11)))))) (.step 63 (.step 58 (.step 68 (.run (.close 2)))))) (.step 48 (.step 40 (.step 18 (.run (.close 9)))))) (.step 55 (.step 63 (.step 43 (.step 18 (.run (.close 11))))))) (.step 63 (.step 58 (.step 68 (.step 2 (.run (.close 4))))))) (.step 68 (.step 48 (.step 40 (.step 18 (.run (.close 9)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part882
namespace Part883
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360932430300464025890769090103534313140282909789149810903583201594261159508704060043530600448, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004635299768373932021760949449740583954455542865291599994011662882668679678941233220620693528601624064992025239489609728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 53 0 (.split 57 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.step 31 (.step 2 (.run (.close 23))))) (.step 23 (.step 22 (.step 9 (.step 31 (.step 2 (.run (.close 23)))))))) (.step 12 (.step 2 (.run (.close 23))))) (.step 42 (.step 2 (.run (.close 55))))) (.step 68 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 3 (.split 18 0 (.step 51 (.run (.close 54))) (.step 68 (.run (.close 24))))))) (.step 31 (.split 18 0 (.split 19 0 (.step 18 (.run (.close 67))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 24)))))) (.step 18 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 36 (.step 3 (.run (.close 61)))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.step 36 (.run (.close 2)))))) (.step 18 (.step 3 (.step 36 (.run (.close 2)))))) (.step 18 (.step 3 (.step 40 (.run (.close 31)))))) (.step 18 (.step 36 (.step 42 (.run (.close 3)))))) (.step 3 (.step 31 (.step 23 (.run (.close 18)))))) (.step 3 (.step 31 (.step 22 (.run (.close 2)))))) (.step 3 (.step 31 (.step 22 (.step 15 (.run (.close 3))))))) (.step 3 (.step 31 (.step 23 (.step 18 (.run (.close 42))))))) (.step 3 (.step 31 (.step 22 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part883
namespace Part884
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439739591526910001390184927592448, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004635299768373932021760949449740583954455542865291599994011662882668679678941233220620693529839564104277405514388733952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 12 (.run (.close 68))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 3 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.run (.close 23))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 3))))))) (.step 31 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.run (.close 13))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 3)))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 3 (.step 36 (.step 27 (.step 3 (.run (.close 61)))))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.step 36 (.run (.close 2)))))) (.step 18 (.step 3 (.step 36 (.run (.close 2)))))) (.step 18 (.step 3 (.step 40 (.run (.close 31)))))) (.step 18 (.step 3 (.step 36 (.step 27 (.run (.close 2))))))) (.step 3 (.step 31 (.step 23 (.run (.close 18)))))) (.step 3 (.step 31 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 3 (.step 31 (.split 16 0 (.step 22 (.step 15 (.run (.close 2)))) (.step 55 (.run (.close 31))))))) (.step 3 (.step 31 (.step 23 (.step 18 (.run (.close 42))))))) (.step 3 (.step 31 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part884
namespace Part885
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004635299768373932021760949449740583954455542865291599994011662882668679678941233220620693529839564105430327018995580928⟩
def references : Fin 8 → Box := ![Part869.root, Part873.root, Part879.root, Part880.root, Part881.root, Part882.root, Part883.root, Part884.root]
def proof : Enumeration.Proof 8 := (.split 10 0 (.split 69 0 (.reuse 0) (.split 44 0 (.reuse 1) (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 39 0 (.split 54 0 (.split 58 0 (.split 72 0 (.split 74 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 2 (.step 4 (.run (.close 68))))))) (.split 9 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 27 0 (.reuse 2) (.split 6 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 31 0 (.split 33 0 (.step 7 (.step 4 (.run (.close 2)))) (.step 3 (.run (.close 36)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 40 (.step 4 (.step 23 (.run (.close 2)))))) (.step 40 (.step 4 (.step 23 (.run (.close 2)))))) (.step 40 (.step 4 (.step 23 (.run (.close 2)))))) (.step 71 (.step 48 (.run (.close 46)))))) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.split 6 0 (.reuse 6) (.step 3 (.step 31 (.step 22 (.step 15 (.step 18 (.run (.close 2))))))))) (.split 6 0 (.reuse 7) (.step 3 (.step 31 (.split 12 0 (.split 16 0 (.step 22 (.step 15 (.step 57 (.step 2 (.run (.close 68)))))) (.step 55 (.run (.close 31)))) (.step 15 (.run (.close 2)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part869.covered
  · exact Part873.covered
  · exact Part879.covered
  · exact Part880.covered
  · exact Part881.covered
  · exact Part882.covered
  · exact Part883.covered
  · exact Part884.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part885
namespace Part886
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5783586108478336971677622838323369986164720647849769929632714413679694899111382521263249281363026240510888936214196938761180612467066004988713665002241028225460212688664311395086905872583920623845649541539238263820359041024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 14 0 (.split 47 0 (.split 57 0 (.split 23 0 (.split 35 0 (.split 36 0 (.split 58 0 (.split 63 0 (.split 64 0 (.split 31 0 (.step 61 (.run (.close 7))) (.step 31 (.step 7 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.split 16 0 (.step 68 (.run (.close 2))) (.step 68 (.run (.close 43)))))) (.step 61 (.run (.close 2)))) (.split 54 0 (.split 63 0 (.step 7 (.run (.close 31))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43))))) (.split 54 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 36 0 (.step 24 (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 71 (.step 68 (.run (.close 43)))))) (.split 53 0 (.split 35 0 (.split 63 0 (.split 64 0 (.step 70 (.step 18 (.step 43 (.step 24 (.run (.close 2)))))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 23)))) (.step 43 (.run (.close 18)))) (.step 2 (.step 71 (.run (.close 5)))))) (.split 23 0 (.split 31 0 (.step 7 (.step 63 (.step 4 (.run (.close 55))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55))))) (.split 23 0 (.split 31 0 (.split 33 0 (.step 7 (.step 63 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55))))) (.split 36 0 (.split 42 0 (.step 63 (.step 27 (.split 35 0 (.split 58 0 (.step 24 (.step 68 (.run (.close 7)))) (.step 61 (.run (.close 68)))) (.step 43 (.run (.close 68)))))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part886
namespace Part887
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5789234136395753406671521056007779241891423355673473084682081217541420286772104918266038160619731506328520762262302773327049374074173016545521903816935328438844678953496390943904822544544491325451304556420886648877979009024⟩
def references : Fin 1 → Box := ![Part886.root]
def proof : Enumeration.Proof 1 := (.split 26 0 (.split 19 0 (.split 46 0 (.split 73 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 23 0 (.split 35 0 (.split 47 0 (.split 63 0 (.split 64 0 (.step 62 (.step 63 (.step 18 (.run (.close 7))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 2 (.run (.close 48)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 63))))) (.step 2 (.step 71 (.run (.close 63)))))) (.split 23 0 (.split 54 0 (.split 31 0 (.split 33 0 (.split 49 0 (.split 50 0 (.split 59 0 (.step 55 (.step 48 (.step 55 (.step 3 (.run (.close 2)))))) (.step 63 (.run (.close 7)))) (.step 63 (.run (.close 7)))) (.step 58 (.run (.close 68)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 58 (.run (.close 5)))) (.step 2 (.run (.close 55))))) (.split 46 0 (.split 47 0 (.split 57 0 (.split 53 0 (.split 35 0 (.split 31 0 (.split 63 0 (.split 64 0 (.split 14 0 (.step 54 (.step 18 (.step 24 (.run (.close 2))))) (.step 68 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 31)))) (.step 43 (.run (.close 18)))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 19 0 (.step 7 (.step 71 (.step 68 (.run (.close 43))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part886.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part887
namespace Part888
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961190638509073572673536466321868631648628994594095980313053984260235843675407174470613186008523723726486499587654680576⟩
def references : Fin 1 → Box := ![Part887.root]
def proof : Enumeration.Proof 1 := (.split 12 0 (.split 56 0 (.reuse 0) (.split 14 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 39 0 (.split 19 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 16 0 (.split 58 0 (.step 58 (.step 23 (.run (.close 2)))) (.step 71 (.run (.close 23)))) (.step 55 (.run (.close 7)))) (.step 4 (.run (.close 55)))) (.step 58 (.run (.close 23)))) (.step 58 (.run (.close 61)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 58 (.run (.close 61)))) (.step 4 (.step 71 (.run (.close 58))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 61)))) (.step 68 (.step 63 (.run (.close 7)))))) (.split 46 0 (.split 47 0 (.split 31 0 (.split 33 0 (.split 53 0 (.split 70 0 (.split 73 0 (.split 57 0 (.split 69 0 (.split 19 0 (.split 23 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 16 0 (.step 18 (.step 57 (.step 7 (.run (.close 68))))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 18 (.run (.close 68)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 71 (.run (.close 61)))) (.step 71 (.run (.close 24)))) (.step 71 (.step 48 (.step 2 (.run (.close 4)))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 4 (.step 71 (.run (.close 61))))) (.step 24 (.step 18 (.step 24 (.run (.close 3)))))) (.step 24 (.step 18 (.step 24 (.run (.close 3)))))) (.step 71 (.step 58 (.run (.close 24))))) (.step 71 (.step 58 (.run (.close 24))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part887.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part888
namespace Part889
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961193101134460847328487233761874890624491812077800384403470731030106104573883781904634746427314963217332789124087676928⟩
def references : Fin 1 → Box := ![Part888.root]
def proof : Enumeration.Proof 1 := (.split 38 0 (.split 18 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 14 0 (.split 63 0 (.split 53 0 (.split 64 0 (.split 71 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 3 (.step 57 (.step 18 (.run (.close 68))))) (.step 68 (.step 24 (.run (.close 2))))) (.step 68 (.step 24 (.run (.close 2))))) (.step 18 (.run (.close 7)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 68 (.step 63 (.step 24 (.step 55 (.step 24 (.run (.close 2)))))))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 31)))) (.step 68 (.step 40 (.step 71 (.step 18 (.run (.close 68))))))) (.step 2 (.step 43 (.step 40 (.run (.close 29))))))) (.split 14 0 (.split 24 0 (.split 31 0 (.split 12 0 (.split 18 0 (.split 26 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 58 0 (.step 58 (.step 59 (.step 40 (.step 55 (.run (.close 7)))))) (.step 71 (.run (.close 23)))) (.step 4 (.run (.close 58)))) (.step 58 (.run (.close 5)))) (.step 58 (.run (.close 68)))) (.step 58 (.run (.close 42)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 18)))) (.step 58 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 63 (.run (.close 7))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part888.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part889
namespace Part890
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961193101134460847328489369748910811534574207099506553955585333734628461226653728946242568647040743859035733590781460480⟩
def references : Fin 1 → Box := ![Part889.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 32 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 46 0 (.split 47 0 (.split 14 0 (.split 74 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 10 0 (.split 16 0 (.step 71 (.step 4 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 63))))) (.step 2 (.step 4 (.run (.close 63))))) (.step 2 (.run (.close 7)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 71 (.step 48 (.run (.close 3)))))) (.split 32 0 (.split 53 0 (.split 70 0 (.split 12 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 73 0 (.split 69 0 (.split 18 0 (.split 19 0 (.split 16 0 (.split 17 0 (.step 9 (.step 43 (.step 24 (.run (.close 2))))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 24)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 7)))) (.split 31 0 (.split 33 0 (.split 38 0 (.split 41 0 (.split 46 0 (.step 18 (.step 57 (.run (.close 9)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part889.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part890
namespace Part891
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961193101134460847328489369748910811534574207099506553955585333734628461226653730307372036330795806638353777947029012480⟩
def references : Fin 1 → Box := ![Part890.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 13 0 (.reuse 0) (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 18 0 (.split 19 0 (.split 46 0 (.split 6 0 (.split 12 0 (.split 23 0 (.split 54 0 (.split 10 0 (.split 16 0 (.step 71 (.step 54 (.step 2 (.run (.close 5))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 7 (.run (.close 2)))) (.step 71 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 71 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 63 (.step 71 (.run (.close 4))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 63 (.step 71 (.run (.close 2)))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 14 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 46 0 (.split 47 0 (.split 31 0 (.split 32 0 (.split 53 0 (.split 57 0 (.split 70 0 (.step 9 (.step 63 (.step 11 (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 63)))) (.step 2 (.run (.close 7)))) (.step 63 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 2 (.step 68 (.run (.close 31))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 63 (.split 16 0 (.split 17 0 (.step 9 (.run (.close 11))) (.step 24 (.run (.close 11)))) (.step 24 (.run (.close 11)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part890.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part891
namespace Part892
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5789234136395753406671521056007779241891423355673473088456043642362961639013659499254307051536652726744961193101134460847328489369748910811536471344689570742501405120753010803908921705736133891332018280875331047380461027328⟩
def references : Fin 1 → Box := ![Part891.root]
def proof : Enumeration.Proof 1 := (.split 27 0 (.split 7 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 26 0 (.split 35 0 (.step 18 (.split 18 0 (.split 46 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 71 (.step 63 (.step 71 (.step 4 (.run (.close 2))))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 5))))) (.step 2 (.run (.close 7)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 23))))) (.step 2 (.step 4 (.run (.close 23))))) (.step 2 (.step 4 (.run (.close 23)))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 31 0 (.split 33 0 (.step 7 (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part891.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part892
namespace Part893
def root : Box := ⟨3351951985607397825209498480933058761663007760896696487095861511789597967143758483020234194662031959985999935706448443834845093598434618165897798143180800, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231016279241839348290219091472249369504048630538173409825336929147632429092799882638670284920546193190822959944094026950899344840568340480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 39 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 54 0 (.step 68 (.step 55 (.step 7 (.run (.close 23))))) (.step 71 (.run (.close 68)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 68 (.step 71 (.step 55 (.run (.close 2)))))) (.step 55 (.step 71 (.step 68 (.run (.close 3)))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.step 68 (.run (.close 7))))) (.step 2 (.run (.close 68)))) (.step 58 (.step 55 (.step 43 (.step 18 (.step 43 (.step 68 (.run (.close 3))))))))) (.step 2 (.run (.close 48)))) (.step 68 (.step 48 (.step 40 (.step 18 (.step 55 (.run (.close 3)))))))) (.step 2 (.step 24 (.step 43 (.run (.close 11)))))) (.step 2 (.run (.close 48)))) (.step 2 (.step 43 (.run (.close 18)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part893
namespace Part894
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486609512836890624, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231016279241839348290219091472249369504048630538173409825336929147632429092799882638670284920546193190822959944094026950899344840568340480⟩
def references : Fin 2 → Box := ![Part892.root, Part893.root]
def proof : Enumeration.Proof 2 := (.split 48 0 (.split 66 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 47 0 (.split 57 0 (.split 39 0 (.step 68 (.step 55 (.run (.close 7)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 55 (.step 71 (.step 68 (.run (.close 43)))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.step 68 (.run (.close 7))))) (.step 2 (.run (.close 68)))) (.step 58 (.step 55 (.step 43 (.step 68 (.run (.close 3))))))) (.step 2 (.run (.close 48)))) (.step 68 (.step 40 (.step 24 (.step 55 (.step 2 (.run (.close 68)))))))) (.step 2 (.step 24 (.step 43 (.run (.close 11)))))) (.step 2 (.run (.close 48)))) (.step 2 (.step 43 (.run (.close 18)))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part892.covered
  · exact Part893.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part894
namespace Part895
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360932430300464025890769090103534313140282909789149810903583200326610559280474659646339022848, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004635299768373932021760949449740583954455542865291599994011662882668679678941233220620693528601624066144947843608084480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 44 0 (.step 3 (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 31)))) (.step 31 (.step 68 (.run (.close 31))))) (.step 31 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 18)))) (.step 18 (.run (.close 68)))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 31 (.step 68 (.run (.close 3)))))) (.step 18 (.step 31 (.step 55 (.run (.close 3)))))) (.step 18 (.step 31 (.step 55 (.run (.close 3)))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 31)))) (.step 18 (.step 3 (.step 36 (.step 42 (.run (.close 2))))))) (.step 2 (.run (.close 18)))) (.step 18 (.step 3 (.step 40 (.run (.close 31)))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.step 18 (.run (.close 7))))) (.step 2 (.step 18 (.run (.close 31))))) (.step 3 (.step 31 (.step 23 (.step 18 (.run (.close 42))))))) (.step 3 (.step 31 (.split 10 0 (.step 22 (.step 53 (.step 2 (.run (.close 68))))) (.step 18 (.run (.close 2))))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 18 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part895
namespace Part896
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438471940926681771989787736014848, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004635299768373932021760949449740583954455542865291599994011662882668679678941233220620693529839564105430328118507208704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.split 17 0 (.step 68 (.run (.close 2))) (.step 24 (.run (.close 2)))))) (.step 31 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 2))) (.step 18 (.run (.close 68)))) (.step 18 (.run (.close 68)))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 31 (.step 51 (.run (.close 2)))))) (.step 18 (.step 31 (.step 51 (.step 2 (.run (.close 23))))))) (.step 18 (.step 31 (.step 51 (.split 18 0 (.step 55 (.run (.close 3))) (.step 2 (.run (.close 68)))))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 31)))) (.step 18 (.step 3 (.split 10 0 (.step 36 (.step 27 (.step 3 (.run (.close 61))))) (.step 18 (.run (.close 31))))))) (.step 2 (.run (.close 18)))) (.step 18 (.step 3 (.split 10 0 (.step 40 (.run (.close 31))) (.step 18 (.run (.close 43))))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.step 18 (.run (.close 7))))) (.step 2 (.step 18 (.run (.close 31))))) (.step 3 (.step 31 (.step 23 (.step 18 (.run (.close 42))))))) (.step 3 (.step 31 (.split 10 0 (.split 16 0 (.step 22 (.step 15 (.run (.close 2)))) (.step 55 (.run (.close 31)))) (.step 18 (.run (.close 2))))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 18 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part896
namespace Part897
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234131009374243490885467899096048133081606605402228047959227361767911715581267318828088567127199136530728432514728631355877113957297835940647156104360797703583899156482013408877188992904205330522604702496485091317907456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 72 0 (.split 74 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 31 0 (.split 23 0 (.split 18 0 (.step 54 (.split 41 0 (.step 54 (.step 2 (.run (.close 43)))) (.step 61 (.step 2 (.run (.close 40)))))) (.step 3 (.step 57 (.step 18 (.run (.close 2)))))) (.step 3 (.step 57 (.step 3 (.run (.close 18)))))) (.split 18 0 (.step 3 (.step 61 (.step 52 (.run (.close 2))))) (.step 3 (.run (.close 2))))) (.step 68 (.step 54 (.run (.close 70))))) (.split 22 0 (.split 36 0 (.step 68 (.step 61 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 31 (.step 63 (.run (.close 24))))))) (.split 22 0 (.split 36 0 (.step 68 (.step 61 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 31 (.step 63 (.step 24 (.run (.close 61)))))))) (.split 22 0 (.split 23 0 (.step 61 (.step 68 (.step 2 (.run (.close 24))))) (.step 55 (.step 3 (.step 2 (.run (.close 24)))))) (.step 68 (.step 31 (.run (.close 62)))))) (.step 68 (.step 57 (.split 23 0 (.step 70 (.step 2 (.run (.close 68)))) (.step 55 (.step 18 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part897
namespace Part898
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234131009374243490885467899096048133081610657663529557266338230582568343035409842689003158303204704980267834749165022398153360557100830383503838353083152572500468557613991914043590067580865301100299921427906587086815232⟩
def references : Fin 1 → Box := ![Part897.root]
def proof : Enumeration.Proof 1 := (.split 32 0 (.split 56 0 (.split 59 0 (.reuse 0) (.split 72 0 (.split 74 0 (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 22 0 (.split 23 0 (.split 24 0 (.step 54 (.split 26 0 (.step 54 (.step 2 (.run (.close 40)))) (.step 57 (.step 2 (.run (.close 40)))))) (.step 61 (.step 62 (.step 2 (.run (.close 43)))))) (.step 57 (.step 3 (.run (.close 62))))) (.step 62 (.run (.close 2)))) (.step 61 (.step 68 (.step 62 (.run (.close 31)))))) (.step 57 (.step 62 (.step 15 (.step 3 (.step 43 (.run (.close 53)))))))) (.step 61 (.step 62 (.step 68 (.step 2 (.run (.close 24))))))) (.step 57 (.step 62 (.step 46 (.step 9 (.run (.close 23))))))) (.step 61 (.run (.close 62)))) (.step 57 (.run (.close 62))))) (.split 14 0 (.split 22 0 (.step 57 (.step 54 (.run (.close 2)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 5))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 56 0 (.split 59 0 (.split 72 0 (.split 35 0 (.step 36 (.step 70 (.step 61 (.step 63 (.run (.close 2)))))) (.step 4 (.run (.close 3)))) (.step 71 (.step 4 (.run (.close 3))))) (.step 53 (.step 70 (.run (.close 44))))) (.step 55 (.run (.close 54)))) (.step 71 (.step 4 (.step 63 (.run (.close 2)))))) (.step 3 (.step 4 (.run (.close 71))))) (.step 3 (.step 4 (.run (.close 71))))) (.step 3 (.run (.close 4)))) (.step 3 (.run (.close 4)))) (.step 3 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part897.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part898
namespace Part899
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212287976531946931143970746921907018395230995216988959265342587323575327649363701663189709853625010831402231416716120056371779318317056⟩
def references : Fin 1 → Box := ![Part898.root]
def proof : Enumeration.Proof 1 := (.split 13 0 (.split 53 0 (.split 38 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 74 0 (.split 22 0 (.split 24 0 (.split 32 0 (.split 26 0 (.split 35 0 (.split 56 0 (.step 70 (.split 4 0 (.split 10 0 (.step 3 (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 57))))) (.step 76 (.run (.close 54)))) (.step 71 (.step 4 (.run (.close 18))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 58)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 2))))) (.split 38 0 (.split 56 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 61 (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 8 0 (.split 14 0 (.split 18 0 (.split 53 0 (.split 22 0 (.split 38 0 (.split 56 0 (.split 74 0 (.split 24 0 (.split 4 0 (.split 54 0 (.step 70 (.step 57 (.step 4 (.step 71 (.run (.close 2)))))) (.step 4 (.run (.close 57)))) (.step 18 (.step 54 (.step 2 (.run (.close 4)))))) (.step 5 (.step 4 (.run (.close 2))))) (.step 55 (.run (.close 70)))) (.step 72 (.run (.close 57)))) (.step 71 (.step 55 (.step 65 (.step 76 (.step 18 (.run (.close 2)))))))) (.step 55 (.run (.close 70)))) (.step 55 (.run (.close 54)))) (.step 3 (.step 76 (.step 65 (.step 57 (.step 2 (.run (.close 4)))))))) (.step 55 (.step 5 (.step 63 (.run (.close 4)))))) (.step 55 (.step 63 (.step 5 (.run (.close 48)))))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part898.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part899
namespace Part900
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212287976531946931143970746921907018395230995216988961162480177387763873469150720045532392121600439593257232639190357033641212750331904⟩
def references : Fin 1 → Box := ![Part899.root]
def proof : Enumeration.Proof 1 := (.split 7 0 (.split 27 0 (.reuse 0) (.split 18 0 (.split 19 0 (.split 23 0 (.split 6 0 (.split 12 0 (.split 13 0 (.split 26 0 (.split 31 0 (.split 38 0 (.split 56 0 (.split 35 0 (.split 36 0 (.split 54 0 (.split 72 0 (.step 44 (.split 4 0 (.step 44 (.step 2 (.run (.close 63)))) (.step 31 (.step 2 (.run (.close 5)))))) (.step 63 (.run (.close 70)))) (.step 4 (.run (.close 61)))) (.step 55 (.run (.close 54)))) (.step 71 (.step 63 (.step 4 (.run (.close 58)))))) (.step 55 (.run (.close 54)))) (.step 55 (.step 71 (.step 5 (.step 2 (.run (.close 4))))))) (.step 3 (.step 73 (.step 64 (.step 27 (.run (.close 2))))))) (.step 55 (.step 71 (.step 2 (.run (.close 4)))))) (.step 3 (.step 2 (.run (.close 4))))) (.step 3 (.step 4 (.run (.close 71))))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 18 0 (.split 19 0 (.split 53 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 36 0 (.split 23 0 (.split 38 0 (.split 24 0 (.split 27 0 (.split 39 0 (.split 26 0 (.step 54 (.step 70 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 5 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 5 (.run (.close 46)))) (.step 7 (.run (.close 2)))) (.step 3 (.run (.close 26)))) (.step 72 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 5)))) (.step 55 (.step 5 (.step 63 (.run (.close 4)))))) (.step 55 (.step 63 (.step 5 (.run (.close 48)))))) (.step 55 (.step 63 (.run (.close 54))))) (.step 3 (.step 76 (.run (.close 22))))) (.step 3 (.step 76 (.step 65 (.step 9 (.run (.close 2))))))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 3 (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part899.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part900
namespace Part901
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215286861860634976902233595013073645115023065505333248, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212287976531946931143970746921907018395230995216988961162480177387763873469150720047030431299864615084416009592724547128788543606882304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 38 0 (.split 36 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 53 0 (.split 17 0 (.split 73 0 (.split 22 0 (.split 50 0 (.split 27 0 (.step 54 (.step 2 (.run (.close 24)))) (.step 31 (.run (.close 2)))) (.step 53 (.run (.close 2)))) (.step 7 (.run (.close 70)))) (.step 65 (.run (.close 70)))) (.step 7 (.step 24 (.step 31 (.run (.close 42)))))) (.step 31 (.run (.close 54)))) (.split 4 0 (.split 17 0 (.step 3 (.run (.close 70))) (.step 23 (.run (.close 54)))) (.step 23 (.run (.close 70))))) (.split 4 0 (.split 10 0 (.step 3 (.step 54 (.run (.close 2)))) (.step 23 (.run (.close 54)))) (.step 23 (.run (.close 54))))) (.split 4 0 (.split 7 0 (.split 10 0 (.step 3 (.split 13 0 (.split 19 0 (.step 70 (.step 61 (.step 24 (.run (.close 2))))) (.step 18 (.run (.close 21)))) (.step 5 (.run (.close 2))))) (.step 23 (.step 24 (.run (.close 18))))) (.step 5 (.run (.close 2)))) (.step 23 (.step 24 (.run (.close 18)))))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 70)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 63))))) (.step 68 (.step 31 (.step 63 (.step 61 (.step 24 (.step 42 (.run (.close 62))))))))) (.step 68 (.step 31 (.step 63 (.step 61 (.run (.close 7))))))) (.step 68 (.run (.close 70)))) (.step 68 (.step 63 (.run (.close 58))))) (.step 68 (.run (.close 7))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part901
namespace Part902
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234131009374243490885467899096048133081610657667394094789359003703665681798515900766511215306238381929801205998373426160684791419753182727744402755350227489500652897224395509960907602740158918266191627877485524421705728⟩
def references : Fin 2 → Box := ![Part900.root, Part901.root]
def proof : Enumeration.Proof 2 := (.split 57 0 (.split 16 0 (.split 17 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 72 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 6 0 (.split 31 0 (.split 12 0 (.split 54 0 (.split 53 0 (.split 8 0 (.split 14 0 (.step 70 (.split 4 0 (.step 36 (.run (.close 54))) (.step 7 (.run (.close 2))))) (.step 31 (.run (.close 54)))) (.step 31 (.run (.close 54)))) (.step 31 (.run (.close 2)))) (.step 72 (.run (.close 61)))) (.step 54 (.step 24 (.run (.close 2))))) (.step 31 (.step 44 (.run (.close 54))))) (.step 7 (.step 5 (.step 3 (.run (.close 54)))))) (.split 31 0 (.step 54 (.step 3 (.step 5 (.run (.close 36))))) (.step 24 (.run (.close 3))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 2))))) (.reuse 1)) (.split 38 0 (.split 53 0 (.split 56 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 74 0 (.step 3 (.step 62 (.step 2 (.run (.close 4))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.run (.close 63))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part900.covered
  · exact Part901.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part902
namespace Part903
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234131009374243490885467899096048133081610657667394094789359003703665681798518952326211297982207664210876242996610456488573501055897468536196642751337442779341945577731712174914557908110870666187627779548963100193456128⟩
def references : Fin 1 → Box := ![Part902.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 6 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 3 (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 68 (.run (.close 3)))) (.step 68 (.step 3 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 36 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.step 3 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 55 (.step 68 (.run (.close 63))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part902.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part903
namespace Part904
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234136395753406676424723379602752013306946066372970974395682371918527090158011959910621892734471818560683123459210489247962728826199534053652011313461688898142391714476740450906486979942220728914388365242262052434608128⟩
def references : Fin 1 → Box := ![Part903.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.split 71 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 42 0 (.split 56 0 (.split 57 0 (.split 7 0 (.step 3 (.step 61 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.step 57 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))))) (.step 55 (.step 18 (.run (.close 3))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.step 43 (.run (.close 39)))))) (.step 68 (.step 63 (.run (.close 68))))) (.step 68 (.step 63 (.run (.close 68))))) (.step 68 (.step 63 (.step 43 (.run (.close 20))))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 36 0 (.split 38 0 (.split 26 0 (.split 56 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 70 (.step 3 (.run (.close 2)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 68)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.run (.close 68))))) (.step 55 (.step 68 (.run (.close 63))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 55 (.step 63 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part903.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part904
namespace Part905
def root : Box := ⟨4898883310661797945363497076419843873668423473372183956680011121698420115259362718051758874274289988507985600593650692529939174536316887597788915436385454014929038870792530229877420875072318716401156096, 5789234136395753406676424723384169648139344787960032346849242165387558721640870681812297020653327007996674837733975382981045136249112438174007689381912539738057722297913899570385198742392987430241823833261565451551509577728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 66 0 (.split 8 0 (.split 14 0 (.split 64 0 (.split 71 0 (.split 7 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.step 52 (.step 68 (.step 2 (.run (.close 24)))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 18 (.run (.close 3)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 52)))) (.step 55 (.step 68 (.run (.close 11))))) (.step 55 (.run (.close 68)))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 48))))) (.step 68 (.step 71 (.step 68 (.run (.close 55)))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.step 3 (.step 71 (.step 68 (.run (.close 43)))))))) (.step 68 (.step 63 (.step 68 (.run (.close 55)))))) (.step 68 (.step 63 (.step 68 (.run (.close 24)))))) (.step 68 (.step 63 (.step 77 (.step 68 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part905
namespace Part906
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913219022948441529864797483304376074816569778906170848451236913519109121582986747308779704753338278777371518824577120722014223688904511291694879080448, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847336645558389593904630900278783036605027387035407850370525416623983819443937617449339286178959653184776152541979311532414886882758885376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 38 0 (.split 46 0 (.split 73 0 (.step 3 (.split 4 0 (.split 35 0 (.step 68 (.step 3 (.run (.close 55)))) (.step 71 (.run (.close 3)))) (.step 68 (.step 3 (.run (.close 48)))))) (.step 55 (.run (.close 3)))) (.split 4 0 (.split 10 0 (.split 30 0 (.step 51 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.step 68 (.step 3 (.step 71 (.run (.close 2)))))) (.step 68 (.split 46 0 (.split 47 0 (.step 55 (.run (.close 3))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))))) (.step 68 (.step 55 (.run (.close 3))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 3 (.split 4 0 (.split 10 0 (.step 55 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))))) (.step 55 (.step 63 (.run (.close 68))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.split 46 0 (.split 47 0 (.step 22 (.step 55 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part906
namespace Part907
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847336645558389593904630900281131579187801220263297330967314753651359503677842604016963062356358569324108836864719281237244739836815867904⟩
def references : Fin 3 → Box := ![Part904.root, Part905.root, Part906.root]
def proof : Enumeration.Proof 3 := (.split 48 0 (.split 63 0 (.split 64 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 8 0 (.split 66 0 (.split 71 0 (.split 7 0 (.split 14 0 (.split 35 0 (.split 26 0 (.split 72 0 (.split 74 0 (.step 3 (.step 61 (.step 53 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 18 (.run (.close 3)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 55 (.step 68 (.run (.close 57))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 68 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.step 3 (.step 71 (.run (.close 68))))))) (.step 68 (.step 63 (.run (.close 68))))) (.step 68 (.step 63 (.step 68 (.run (.close 55)))))) (.step 68 (.step 63 (.step 77 (.step 68 (.run (.close 2)))))))) (.reuse 1)) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 6 0 (.split 7 0 (.split 8 0 (.reuse 2) (.step 55 (.step 63 (.step 68 (.run (.close 2)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.split 4 0 (.split 46 0 (.step 22 (.step 55 (.run (.close 9)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 68)))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part904.covered
  · exact Part905.covered
  · exact Part906.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part907
namespace Part908
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891216711779868486860697858560154870545895798997619546985669185819018092531803640195853278334150848284927287119928265406089556279110402048, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847339484772156373619047108574907599122739705946973035206698391193307521751378426080393981612007190148843036530218601342756556241056563200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 73 0 (.split 41 0 (.step 3 (.step 68 (.run (.close 48)))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 3 (.step 58 (.run (.close 55))))) (.split 4 0 (.split 10 0 (.split 30 0 (.step 51 (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.step 68 (.step 3 (.step 58 (.run (.close 2)))))) (.step 68 (.split 46 0 (.split 47 0 (.step 55 (.run (.close 3))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))))) (.step 68 (.step 55 (.split 46 0 (.split 47 0 (.step 27 (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 46 0 (.split 47 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 3 (.step 71 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part908
namespace Part909
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086056351442441850394496164688577034518575687224962187036869077247235813566820053543074922496, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847339484772156373619047108577256141705513539174864505096433367369018674579054384260961457114753609352577342453440752372022378928382410752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 58 0 (.split 70 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 36 0 (.split 10 0 (.split 30 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 55 (.step 31 (.step 53 (.step 23 (.step 18 (.run (.close 68))))))))) (.step 3 (.step 44 (.step 65 (.run (.close 2)))))) (.step 3 (.step 44 (.step 53 (.step 3 (.run (.close 2))))))) (.step 3 (.split 4 0 (.step 22 (.step 53 (.step 68 (.run (.close 2))))) (.step 18 (.run (.close 2)))))) (.step 68 (.step 3 (.step 31 (.step 2 (.run (.close 48))))))) (.step 3 (.step 44 (.step 53 (.step 36 (.run (.close 2))))))) (.step 55 (.step 18 (.step 3 (.step 22 (.step 40 (.step 57 (.step 68 (.run (.close 18)))))))))) (.step 3 (.step 44 (.step 65 (.run (.close 2)))))) (.step 3 (.step 44 (.step 65 (.run (.close 2)))))) (.step 55 (.step 18 (.step 3 (.split 44 0 (.split 48 0 (.step 55 (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))))))) (.step 3 (.step 44 (.step 53 (.step 36 (.run (.close 2))))))) (.step 55 (.step 3 (.step 31 (.split 4 0 (.step 36 (.step 61 (.step 31 (.step 2 (.run (.close 68)))))) (.step 68 (.run (.close 31)))))))) (.step 3 (.split 4 0 (.step 22 (.step 65 (.run (.close 2)))) (.step 2 (.run (.close 48))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part909
namespace Part910
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315391328240928832003409572790272, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847339484772156373619047108577256141705513539174864505096433367369018674579054384260961457114753609353906570449226878352490342839855611904⟩
def references : Fin 3 → Box := ![Part907.root, Part908.root, Part909.root]
def proof : Enumeration.Proof 3 := (.split 29 0 (.split 44 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.reuse 1) (.step 3 (.split 4 0 (.split 10 0 (.step 55 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))))) (.step 55 (.step 3 (.step 63 (.run (.close 11)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.split 46 0 (.split 47 0 (.step 9 (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))) (.step 55 (.step 3 (.step 63 (.run (.close 11)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.split 46 0 (.split 47 0 (.step 9 (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.step 31 (.run (.close 3))))))) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.reuse 2) (.step 3 (.split 4 0 (.step 22 (.step 53 (.step 26 (.run (.close 55))))) (.step 18 (.run (.close 2)))))) (.step 55 (.step 3 (.step 31 (.split 4 0 (.split 10 0 (.step 61 (.step 31 (.step 2 (.run (.close 68))))) (.step 55 (.run (.close 31)))) (.step 2 (.run (.close 7)))))))) (.step 3 (.split 4 0 (.step 22 (.step 65 (.run (.close 2)))) (.step 2 (.run (.close 48)))))) (.step 3 (.split 4 0 (.step 22 (.step 53 (.step 26 (.run (.close 9))))) (.step 2 (.run (.close 18)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part907.covered
  · exact Part908.covered
  · exact Part909.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part910
namespace Part911
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030308028183480086054362149496211247927543159584447235215285400358997645999315392566180968117383684471914496, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847339484772156373619047108577256141705513539174864505096433367369018674579054384260961457114753609353906570450463609464803186980973182976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 70 0 (.split 72 0 (.split 36 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.split 10 0 (.step 18 (.run (.close 2))) (.step 18 (.run (.close 42))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 3 (.step 44 (.step 36 (.run (.close 2)))))) (.step 3 (.step 44 (.step 52 (.step 36 (.run (.close 55))))))) (.step 68 (.step 18 (.step 55 (.step 2 (.run (.close 4))))))) (.step 3 (.split 4 0 (.step 22 (.step 26 (.run (.close 55)))) (.step 18 (.run (.close 2)))))) (.step 68 (.step 3 (.step 31 (.step 2 (.run (.close 48))))))) (.step 3 (.step 44 (.step 52 (.step 36 (.step 55 (.run (.close 2)))))))) (.step 68 (.step 18 (.step 3 (.run (.close 2)))))) (.step 55 (.step 3 (.split 4 0 (.step 18 (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 18))))))) (.step 55 (.step 18 (.step 3 (.split 4 0 (.step 22 (.step 15 (.step 57 (.step 18 (.run (.close 2)))))) (.step 2 (.run (.close 7)))))))) (.step 3 (.step 44 (.step 52 (.step 36 (.step 3 (.run (.close 2)))))))) (.step 55 (.step 3 (.step 31 (.split 4 0 (.step 36 (.step 27 (.step 61 (.step 31 (.run (.close 12)))))) (.step 55 (.run (.close 31)))))))) (.step 3 (.split 4 0 (.step 22 (.step 26 (.step 52 (.step 68 (.step 2 (.run (.close 68))))))) (.step 18 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part911
namespace Part912
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847339484772156373619047108577256141705513539174864505096433367369018674579054384260961457114753609353906570450464818391775723114754736128⟩
def references : Fin 6 → Box := ![Part885.root, Part894.root, Part895.root, Part896.root, Part910.root, Part911.root]
def proof : Enumeration.Proof 6 := (.split 67 0 (.split 4 0 (.reuse 0) (.split 9 0 (.split 29 0 (.split 44 0 (.reuse 1) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 73 0 (.split 49 0 (.split 50 0 (.split 59 0 (.step 3 (.step 31 (.run (.close 3)))) (.step 71 (.run (.close 68)))) (.step 68 (.step 71 (.run (.close 68))))) (.step 63 (.run (.close 68)))) (.step 2 (.run (.close 48)))) (.step 71 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 68 (.step 71 (.step 55 (.run (.close 2)))))) (.step 2 (.run (.close 48)))) (.step 55 (.step 71 (.step 68 (.run (.close 3)))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 68)))) (.step 55 (.step 63 (.step 43 (.run (.close 27)))))) (.step 2 (.run (.close 48)))) (.step 68 (.step 48 (.run (.close 9))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 9))))) (.reuse 2)) (.reuse 3))) (.split 9 0 (.reuse 4) (.split 6 0 (.split 8 0 (.reuse 5) (.step 55 (.step 3 (.step 31 (.split 4 0 (.split 10 0 (.step 36 (.step 61 (.step 31 (.step 2 (.run (.close 68)))))) (.step 55 (.run (.close 31)))) (.step 2 (.run (.close 7)))))))) (.step 3 (.split 4 0 (.step 22 (.step 26 (.step 52 (.step 68 (.run (.close 9)))))) (.step 2 (.run (.close 18))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part885.covered
  · exact Part894.covered
  · exact Part895.covered
  · exact Part896.covered
  · exact Part910.covered
  · exact Part911.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part912
namespace Part913
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408356095931599237832221556720617563649447119238640548905538075536786293719659907900213207334287568597025594568757326027858721242087424, 5789234131009374243485986584588438710047216197411217962417850698040560099452700988782651406771506361839022694542039612216553861198028403256653517446151565628536596950676090862023700079753060728025373410277453909707431346176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 22 0 (.split 14 0 (.split 12 0 (.split 30 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.split 35 0 (.split 72 0 (.split 56 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 4 (.step 2 (.run (.close 5))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 27 0 (.split 31 0 (.step 22 (.step 2 (.run (.close 58)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 5 (.step 31 (.step 3 (.step 4 (.run (.close 2)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 2))))) (.split 35 0 (.split 72 0 (.split 12 0 (.split 36 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.step 2 (.run (.close 5))))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part913
namespace Part914
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408356095931599237832221556720617563649447119238640548905538075536786293719659907900213207334287568597025594568757326027858721242087424, 5789234131009374243485986584588438710047216197411217962417850698040560099452700988782651406771506361839022694542039612216553861198028403256653517446151565628536596950676092360062878343928551886802328153393368671667462602752⟩
def references : Fin 1 → Box := ![Part913.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 8 0 (.split 17 0 (.reuse 0) (.split 35 0 (.split 72 0 (.split 36 0 (.split 6 0 (.split 14 0 (.split 74 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2)))))) (.split 38 0 (.split 14 0 (.split 17 0 (.split 56 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 5 (.step 31 (.step 3 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 5))))) (.split 36 0 (.split 35 0 (.split 72 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 12 0 (.split 17 0 (.step 2 (.run (.close 5))) (.step 63 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part913.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part914
namespace Part915
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408356095931599237832221556720617563649447119238640548905538075536786293719659907900213207334287568597025594568757326027858721242087424, 5789234131009374243485986584588438710047216197411217962417850698040560099452700988782651406771506361839022694542039612216553861198028403256653517446151565628536596950676092360062878343928551888069978753621598074263677435904⟩
def references : Fin 1 → Box := ![Part914.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 10 0 (.reuse 0) (.split 9 0 (.split 8 0 (.split 14 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 64 (.step 2 (.run (.close 4)))))) (.step 63 (.step 72 (.step 55 (.step 48 (.run (.close 2))))))) (.step 63 (.step 65 (.step 4 (.run (.close 2)))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 31 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))))) (.split 29 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 63 (.step 54 (.run (.close 2))))) (.step 54 (.run (.close 2)))) (.step 63 (.step 65 (.step 4 (.step 2 (.run (.close 4))))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 33)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part914.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part915
namespace Part916
def root : Box := ⟨4898883310657346788030287556357712069628819860448212997242721619736728722412481844852244030365602827247402036844362561690883362579263860878762381286192990643146663701882902515194011612373253717489614848, 5789234131009374243490885467899096052484164047812619602022372929823181965413934404333267727137822912084637106350848494426237613787753527177795495270655292703121639672054385137498690720061837764989366067868658088985025839104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 29 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 54 0 (.step 2 (.run (.close 5))) (.step 53 (.run (.close 2)))) (.step 54 (.step 2 (.run (.close 4))))) (.step 65 (.run (.close 2)))) (.step 54 (.run (.close 2)))) (.step 70 (.run (.close 2)))) (.step 54 (.run (.close 2)))) (.step 65 (.step 42 (.step 4 (.step 54 (.run (.close 2))))))) (.step 70 (.step 2 (.run (.close 4))))) (.step 70 (.step 2 (.run (.close 4))))) (.split 16 0 (.split 53 0 (.step 53 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 65))))) (.step 46 (.split 16 0 (.split 17 0 (.split 53 0 (.step 53 (.split 36 0 (.step 70 (.step 57 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 65)))))) (.split 26 0 (.split 72 0 (.split 36 0 (.split 38 0 (.step 53 (.split 42 0 (.split 16 0 (.split 17 0 (.step 5 (.step 2 (.run (.close 63)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 70)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 4 (.run (.close 70)))) (.step 4 (.step 71 (.run (.close 68)))))) (.split 23 0 (.split 31 0 (.split 33 0 (.step 53 (.run (.close 2))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part916
namespace Part917
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408356095931599237832221556720617563649447119238640548905538075536786293719659907900213207334287568597025594568757326027858721242087424, 5789234131009374243490885467899096052484164047812623466559895947081526660765825336320612026065152618519635763586099945945379903348178063371562077193233255166737671174231562502577351763049493507899277474988692166240739786752⟩
def references : Fin 2 → Box := ![Part915.root, Part916.root]
def proof : Enumeration.Proof 2 := (.split 57 0 (.split 67 0 (.reuse 0) (.split 9 0 (.reuse 1) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.step 64 (.split 24 0 (.step 54 (.step 70 (.step 18 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 63)))))) (.step 71 (.step 4 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 3 (.step 4 (.run (.close 15))))) (.step 2 (.run (.close 63)))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 54)))) (.step 2 (.step 4 (.run (.close 71))))))) (.split 12 0 (.split 54 0 (.split 8 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part915.covered
  · exact Part916.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part917
namespace Part918
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408356095931599237832221556720617563649447119238640548905538075536786293719659907900213207334287568597025594568757326027858721242087424, 5789234131009374243490885467899096052484164047812623466559895947081526660765825339372171726147828587801916838623098182975707792057814207657370529433229242382027512466912069819242305413354864219647198911140363643816511537152⟩
def references : Fin 1 → Box := ![Part917.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 54 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 35 0 (.split 72 0 (.split 57 0 (.step 65 (.split 16 0 (.step 65 (.step 55 (.step 53 (.run (.close 2))))) (.step 68 (.run (.close 55))))) (.step 2 (.run (.close 48)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 71))))) (.split 12 0 (.split 23 0 (.split 54 0 (.split 16 0 (.split 8 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.step 2 (.run (.close 48))))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 2 (.run (.close 48)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part917.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part918
namespace Part919
def root : Box := ⟨4784065733068162056019040113691253782879319801563701987073076494057106453662605337065045588760541596543736757642081878145750794778707264994115690496202247798948092164687583749055425916867896043110400, 5789234136395753406676424723379602756364389383221329043439502270449741522174184832379756136742580851956266645503560783008467181285584509722887984801791366628146312913048814847518297342426695569709925671726056942768752689152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 26 0 (.split 53 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 9 0 (.split 71 0 (.step 70 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 68)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 71)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part919
namespace Part920
def root : Box := ⟨4562444968704632373597244070806879402719575543257865999699600873995206766446509608062633428881020846897880950122499945386225491015095097906152874527056501756849020268929022276110732913488691200, 5789234136395753406676424723384165196982011578439970215045202561774634750681433392310335329260480127123475322890066695819784552685363152032461579209102055332867688351047067508838019556614947564384285936676139816960999292928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 27 0 (.split 32 0 (.split 4 0 (.split 10 0 (.split 30 0 (.split 67 0 (.split 8 0 (.split 69 0 (.step 31 (.split 70 0 (.split 14 0 (.split 66 0 (.step 53 (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 3))))) (.step 22 (.step 2 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 3 (.step 53 (.split 8 0 (.step 68 (.run (.close 2))) (.step 4 (.run (.close 63))))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 4 (.step 5 (.step 71 (.step 2 (.run (.close 71))))))) (.step 4 (.step 5 (.step 55 (.step 18 (.run (.close 2))))))) (.step 5 (.step 18 (.step 2 (.run (.close 55)))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part920
namespace Part921
def root : Box := ⟨4459859498083829974276734252779768573313079473415990927614598789192610143309445566980298043451567626834970929348501363926130731924128109070381821904328793390240433117937272268174028070453248, 5789234136395753406676424723384169652490427225114988419314348753465381716724897502232142535503173388134380800114076955500264354805870748362842022172390444677305892819248237677452589597839740779222835116622380132267827658752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 27 0 (.split 32 0 (.split 4 0 (.split 10 0 (.split 30 0 (.split 67 0 (.split 8 0 (.split 14 0 (.split 69 0 (.step 31 (.split 70 0 (.split 64 0 (.split 66 0 (.step 52 (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 3))))) (.step 22 (.step 2 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.split 8 0 (.split 12 0 (.split 18 0 (.step 31 (.step 68 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 68))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 3 (.step 2 (.run (.close 71))))) (.step 3 (.step 2 (.run (.close 71))))) (.step 4 (.step 5 (.step 71 (.step 2 (.run (.close 71))))))) (.step 4 (.step 5 (.step 55 (.step 18 (.step 2 (.run (.close 71)))))))) (.step 5 (.step 18 (.step 4 (.step 18 (.step 68 (.run (.close 2)))))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 4 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part921
namespace Part922
def root : Box := ⟨4351082437154956072465106588077826347036012427817670724348327313196467625387862469215706314418270097797508530909814356551913839966010963705178494114499718432217464205301707147006548377600, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692851495404769731610593280382704098407019777021607519801647544129264442926013125351301169423749424770862185845730564598059420553133948928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 24 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 31 0 (.split 63 0 (.split 33 0 (.split 41 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part922
namespace Part923
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408356095931599237832221556720617563649447119238640548905538075536786293719659907900213207334287568597025594568757326027858721242087424, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692851495404769731610593280382704098407019777021607519801647544129264442926013125351301169423749424770862185845730564598059420553133948928⟩
def references : Fin 5 → Box := ![Part918.root, Part919.root, Part920.root, Part921.root, Part922.root]
def proof : Enumeration.Proof 5 := (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 22 0 (.split 38 0 (.split 56 0 (.split 4 0 (.split 10 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 30 0 (.split 67 0 (.step 36 (.run (.close 2))) (.step 68 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 31)))) (.step 4 (.step 68 (.step 4 (.run (.close 2)))))) (.step 4 (.step 68 (.step 4 (.run (.close 2)))))) (.step 5 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 2)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part918.covered
  · exact Part919.covered
  · exact Part920.covered
  · exact Part921.covered
  · exact Part922.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part923
namespace Part924
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349393741037407567872, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696433002681809433932830490967924832028792904407586740714289470765479393947305413614220669163201895125984084372330905600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 35 0 (.split 50 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 43 (.step 4 (.step 2 (.run (.close 4)))))) (.step 43 (.step 4 (.split 14 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))))) (.split 7 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 53 0 (.step 55 (.split 54 0 (.step 2 (.run (.close 55))) (.step 4 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 23)))) (.step 4 (.step 63 (.run (.close 2)))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.step 24 (.step 18 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part924
namespace Part925
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349393741037407567872, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696433002681809433932830490967924832028794757081014537773416247901239532953831065935304547408011442320232018042685489152⟩
def references : Fin 1 → Box := ![Part924.root]
def proof : Enumeration.Proof 1 := (.split 12 0 (.split 26 0 (.reuse 0) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.split 18 0 (.step 24 (.split 35 0 (.step 2 (.run (.close 23))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 23))))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 74 0 (.split 18 0 (.step 68 (.split 19 0 (.step 24 (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part924.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part925
namespace Part926
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349393741037407567872, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696433002681809433932830490969961868005129243167282983461825626062291001347497002185940687857365823621148276253475733504⟩
def references : Fin 1 → Box := ![Part925.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 50 0 (.step 48 (.split 39 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 48))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 71 (.step 4 (.run (.close 48)))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 18 0 (.step 68 (.split 22 0 (.step 2 (.run (.close 24))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 15)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part925.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part926
namespace Part927
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349393741037407567872, 5789234136395753406676424723384169648139344787960032346849242165387558721637677133045323763439837400810310844811490691643616583080695085789147107067671010058046868347440585275360986005163814805351259779381305798924647268352⟩
def references : Fin 1 → Box := ![Part926.root]
def proof : Enumeration.Proof 1 := (.split 67 0 (.split 17 0 (.reuse 0) (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 50 0 (.split 59 0 (.split 30 0 (.split 42 0 (.step 2 (.run (.close 58))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 55 (.step 2 (.run (.close 5)))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 71 (.run (.close 63)))))) (.split 12 0 (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 17 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.step 71 (.run (.close 48)))))) (.step 68 (.step 3 (.step 2 (.run (.close 71)))))) (.step 68 (.step 4 (.step 71 (.run (.close 2)))))) (.step 68 (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part926.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part927
namespace Part928
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714737812568220577623142534110773248, 5789234136395753406676424723384169652490427225114988419314348753465381716721703953465169278289683780948016807191592264162835801637453395977981439858148914997295038868774923382428376860610568155598683722931064500862769430528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 14 0 (.split 39 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 63 (.run (.close 48)))) (.step 63 (.run (.close 2)))) (.step 55 (.step 48 (.run (.close 2))))) (.step 55 (.step 48 (.run (.close 2))))) (.step 63 (.step 55 (.step 2 (.run (.close 63)))))) (.step 68 (.step 63 (.run (.close 4))))) (.step 63 (.step 4 (.step 71 (.run (.close 24)))))) (.step 68 (.step 63 (.run (.close 4))))) (.step 71 (.step 68 (.step 63 (.run (.close 4)))))) (.step 71 (.step 63 (.step 4 (.step 71 (.run (.close 24))))))) (.step 71 (.step 4 (.step 63 (.step 4 (.step 2 (.run (.close 5)))))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 68 (.step 48 (.run (.close 2))))) (.step 3 (.step 24 (.step 48 (.run (.close 2)))))) (.step 68 (.step 55 (.step 4 (.step 63 (.step 2 (.run (.close 5)))))))) (.step 55 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 55 (.step 24 (.step 63 (.step 2 (.run (.close 4)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part928
namespace Part929
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981035118389856347444984945191048708096, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939160896039638078888537443622450026655705016410570752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 17 0 (.split 22 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 38 0 (.split 35 0 (.split 7 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 44 0 (.split 48 0 (.split 10 0 (.split 30 0 (.step 4 (.split 6 0 (.step 36 (.split 18 0 (.step 34 (.run (.close 3))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 3))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 63 (.step 18 (.step 4 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 18))))) (.step 4 (.step 58 (.run (.close 3))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 68 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 63 (.step 68 (.step 63 (.run (.close 52)))))) (.step 63 (.step 68 (.step 63 (.run (.close 2)))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 58 (.step 48 (.run (.close 2))))) (.step 63 (.step 58 (.step 48 (.run (.close 34)))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.step 68 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part929
namespace Part930
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922509426048258843617654748602453065676760693340110848, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409791455647307282742938724672343113728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 73 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 49 0 (.split 29 0 (.split 50 0 (.split 59 0 (.split 44 0 (.split 8 0 (.split 24 0 (.step 56 (.split 58 0 (.step 56 (.split 10 0 (.step 35 (.step 2 (.run (.close 71)))) (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2)))))) (.step 48 (.step 71 (.run (.close 2))))) (.step 8 (.run (.close 11)))) (.step 71 (.step 35 (.run (.close 8))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 35 (.step 71 (.step 3 (.run (.close 2)))))) (.step 48 (.step 2 (.run (.close 48))))) (.step 4 (.step 55 (.step 63 (.run (.close 2)))))) (.step 4 (.step 55 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.step 2 (.run (.close 5)))))) (.step 63 (.run (.close 2)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 40 (.step 24 (.run (.close 2))))) (.step 4 (.step 55 (.step 48 (.run (.close 2)))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 48 (.step 2 (.run (.close 5))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part930
namespace Part931
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349393741037407567872, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409791455647307282742938724672343113728⟩
def references : Fin 4 → Box := ![Part927.root, Part928.root, Part929.root, Part930.root]
def proof : Enumeration.Proof 4 := (.split 16 0 (.split 49 0 (.split 10 0 (.split 29 0 (.split 62 0 (.reuse 0) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 12 0 (.split 54 0 (.split 22 0 (.step 2 (.run (.close 48))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 4 (.run (.close 2))))) (.split 30 0 (.split 36 0 (.split 42 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 68 (.step 24 (.step 18 (.step 63 (.run (.close 2))))))) (.step 68 (.step 43 (.step 24 (.step 18 (.step 63 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 2 (.run (.close 4))))))) (.reuse 1)) (.reuse 2)) (.reuse 3))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part927.covered
  · exact Part928.covered
  · exact Part929.covered
  · exact Part930.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part931
namespace Part932
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349393742136919195648, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409791455648545222782224106046753865728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 9 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 14 0 (.split 74 0 (.split 38 0 (.split 24 0 (.split 39 0 (.split 49 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 55 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 63 (.step 55 (.step 63 (.run (.close 2)))))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 24)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 55 (.step 40 (.run (.close 7))))) (.step 55 (.step 48 (.run (.close 7))))) (.step 48 (.step 71 (.run (.close 5))))) (.step 71 (.step 55 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.step 71 (.step 4 (.run (.close 24)))))) (.step 2 (.run (.close 7)))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 2 (.step 71 (.run (.close 31))))) (.step 2 (.step 71 (.run (.close 24))))) (.step 2 (.step 71 (.run (.close 24))))) (.step 2 (.step 71 (.run (.close 31)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part932
namespace Part933
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349393741037407567872, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409791455648545222782224106046753865728⟩
def references : Fin 2 → Box := ![Part931.root, Part932.root]
def proof : Enumeration.Proof 2 := (.split 4 0 (.split 9 0 (.reuse 0) (.split 10 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 67 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 62 0 (.split 69 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 58))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 24 (.step 68 (.step 18 (.step 63 (.step 68 (.run (.close 3)))))))) (.step 24 (.step 68 (.step 43 (.step 18 (.step 63 (.step 68 (.run (.close 3))))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.run (.close 2)))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part931.covered
  · exact Part932.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part933
namespace Part934
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642487734313232105472, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696433002681809433932830490967924832028792904407586740714289470765479393947305413614219371088987261419078077648155443200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 35 0 (.split 50 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 43 (.step 4 (.step 2 (.run (.close 4)))))) (.step 43 (.step 4 (.split 14 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))))) (.split 7 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 53 0 (.step 55 (.split 54 0 (.step 2 (.run (.close 55))) (.step 4 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 23)))) (.step 4 (.step 63 (.run (.close 2)))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.step 24 (.step 18 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part934
namespace Part935
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642487734313232105472, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696433002681809433932830490967924832028794757081014537773416247901239532953831065935303249333796808613326011318510026752⟩
def references : Fin 1 → Box := ![Part934.root]
def proof : Enumeration.Proof 1 := (.split 12 0 (.split 26 0 (.reuse 0) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.split 18 0 (.step 24 (.split 35 0 (.step 2 (.run (.close 23))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 23))))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 74 0 (.split 18 0 (.step 68 (.split 19 0 (.step 24 (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part934.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part935
namespace Part936
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642487734313232105472, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696433002681809433932830490969961868005129243167282983461825626062291001347497002185939389783151189914242269529300271104⟩
def references : Fin 1 → Box := ![Part935.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 50 0 (.step 48 (.split 39 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 48))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 71 (.step 4 (.run (.close 48)))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 18 0 (.step 68 (.split 22 0 (.step 2 (.run (.close 24))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part935.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part936
namespace Part937
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642487734313232105472, 5789234136395753406676424723384169648139344787960032346849242165387558721637677133045323763439837400810310844811490691643616583080695085789147107067671010058046868347440585275360986005163813507277045145674399792200471805952⟩
def references : Fin 1 → Box := ![Part936.root]
def proof : Enumeration.Proof 1 := (.split 67 0 (.split 17 0 (.reuse 0) (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 50 0 (.split 59 0 (.split 30 0 (.split 42 0 (.step 2 (.run (.close 58))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 55 (.step 2 (.run (.close 5)))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 71 (.run (.close 63)))))) (.split 12 0 (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 17 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.step 71 (.run (.close 48)))))) (.step 68 (.step 3 (.step 2 (.run (.close 71)))))) (.step 68 (.step 4 (.step 71 (.run (.close 2)))))) (.step 68 (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part936.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part937
namespace Part938
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713439738353586870717135809935310848, 5789234136395753406676424723384169652490427225114988419314348753465381716721703953465169278289683780948016807191592264162835801637453395977981439858148914997295038868774923382428376860610566857524469089224158494138593968128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 24 0 (.split 31 0 (.split 33 0 (.step 7 (.run (.close 2))) (.step 55 (.step 48 (.run (.close 2))))) (.step 55 (.step 48 (.run (.close 2))))) (.step 63 (.step 55 (.step 2 (.run (.close 63)))))) (.step 68 (.run (.close 7)))) (.step 63 (.step 4 (.step 71 (.run (.close 24)))))) (.step 68 (.run (.close 7)))) (.step 68 (.run (.close 7)))) (.step 71 (.step 63 (.step 4 (.step 71 (.run (.close 24))))))) (.step 71 (.step 4 (.step 63 (.step 4 (.step 2 (.run (.close 5)))))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 68 (.step 48 (.run (.close 2))))) (.step 3 (.step 24 (.step 48 (.run (.close 2)))))) (.step 68 (.step 55 (.step 4 (.step 63 (.step 2 (.run (.close 5)))))))) (.step 55 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 55 (.step 24 (.step 63 (.step 2 (.run (.close 4)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part938
namespace Part939
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899047295640463577735175393938286432209398981033820315641713738078938466873245696, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939160896039638078887239369407816319749698292235108352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 17 0 (.split 22 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 38 0 (.split 35 0 (.split 7 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 44 0 (.split 48 0 (.split 10 0 (.split 30 0 (.step 4 (.split 6 0 (.step 36 (.split 18 0 (.step 34 (.step 3 (.step 2 (.run (.close 55))))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 3))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 63 (.step 18 (.step 4 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 9)))) (.step 68 (.step 4 (.run (.close 18))))) (.step 4 (.step 58 (.run (.close 3))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 9)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 63 (.step 68 (.step 63 (.run (.close 52)))))) (.step 63 (.step 68 (.step 63 (.run (.close 2)))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 58 (.step 48 (.run (.close 2))))) (.step 63 (.step 58 (.step 48 (.step 2 (.run (.close 4))))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.step 68 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part939
namespace Part940
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922509426048258843616356674387819358770753969164648448, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409790157573092649036032717948167651328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 13 0 (.split 73 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 49 0 (.split 29 0 (.split 50 0 (.split 59 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 62 0 (.step 11 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 71 (.step 55 (.run (.close 8))))) (.step 56 (.run (.close 2)))) (.step 71 (.step 35 (.run (.close 48))))) (.step 35 (.step 71 (.run (.close 8))))) (.step 71 (.step 35 (.run (.close 8))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 35 (.step 71 (.step 3 (.run (.close 2)))))) (.step 48 (.step 2 (.run (.close 48))))) (.step 55 (.step 71 (.run (.close 31))))) (.step 55 (.step 71 (.run (.close 31))))) (.step 71 (.step 55 (.step 2 (.run (.close 5)))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 40 (.step 24 (.run (.close 2))))) (.step 4 (.step 55 (.step 48 (.run (.close 2)))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 48 (.step 2 (.run (.close 5))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part940
namespace Part941
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642487734313232105472, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409790157573092649036032717948167651328⟩
def references : Fin 4 → Box := ![Part937.root, Part938.root, Part939.root, Part940.root]
def proof : Enumeration.Proof 4 := (.split 16 0 (.split 49 0 (.split 10 0 (.split 29 0 (.split 62 0 (.reuse 0) (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 12 0 (.split 54 0 (.split 22 0 (.step 2 (.run (.close 48))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 4 (.run (.close 2))))) (.split 30 0 (.split 36 0 (.split 42 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 68 (.step 24 (.step 18 (.step 63 (.run (.close 2))))))) (.step 68 (.step 43 (.step 24 (.step 18 (.step 63 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 2 (.run (.close 4))))))) (.reuse 1)) (.reuse 2)) (.reuse 3))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part937.covered
  · exact Part938.covered
  · exact Part939.covered
  · exact Part940.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part941
namespace Part942
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642487735412743733248, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409790157574330589075318099322578403328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 9 0 (.split 23 0 (.split 29 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 14 0 (.split 74 0 (.split 38 0 (.split 24 0 (.split 39 0 (.split 49 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 55 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 63 (.step 55 (.step 63 (.run (.close 2)))))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 24)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 40 (.run (.close 7)))) (.step 68 (.step 55 (.run (.close 7))))) (.step 48 (.step 71 (.run (.close 5))))) (.step 71 (.step 68 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.step 71 (.run (.close 9))))) (.step 2 (.run (.close 7)))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 2 (.step 71 (.run (.close 31))))) (.step 2 (.run (.close 9)))) (.step 2 (.step 71 (.run (.close 31)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part942
namespace Part943
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512714736544917620349394866937314410496, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409791455648545222782225231946660708352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 12 0 (.split 19 0 (.split 49 0 (.split 50 0 (.split 23 0 (.split 54 0 (.split 13 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 73 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 59 0 (.split 8 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 16 0 (.split 10 0 (.split 63 0 (.split 17 0 (.step 2 (.run (.close 71))) (.step 31 (.step 56 (.run (.close 2))))) (.step 48 (.step 2 (.run (.close 71))))) (.step 48 (.run (.close 2)))) (.step 35 (.step 56 (.step 11 (.run (.close 2)))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 56)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 8)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 48 (.step 2 (.run (.close 48)))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part943
namespace Part944
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642487734313232105472, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828660924732095933172704637820518700354992298232318311939162357541275409791455648545222782225231946660708352⟩
def references : Fin 3 → Box := ![Part941.root, Part942.root, Part943.root]
def proof : Enumeration.Proof 3 := (.split 11 0 (.split 4 0 (.split 9 0 (.reuse 0) (.split 10 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 67 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 62 0 (.split 69 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 58))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 24 (.step 68 (.step 18 (.step 63 (.step 68 (.run (.close 3)))))))) (.step 24 (.step 68 (.step 43 (.step 18 (.step 63 (.step 68 (.run (.close 3))))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.run (.close 2)))))) (.reuse 1)) (.reuse 2))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part941.covered
  · exact Part942.covered
  · exact Part943.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part944
namespace Part945
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960667312644746696187223091572042864535722476505309650863932023364101684932378624, 5789234136395753406671521056007779241891423355673473088456043642362961639010462825687223775409041999255148038143427527696250268823260995183834829073223426423641892138301665556209858690724098079451068776531113685963168022528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 53 0 (.split 70 0 (.split 57 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 54 0 (.split 58 0 (.split 69 0 (.split 12 0 (.split 63 0 (.split 4 0 (.step 15 (.step 57 (.step 18 (.run (.close 9))))) (.step 18 (.run (.close 7)))) (.step 43 (.step 57 (.run (.close 15))))) (.step 57 (.run (.close 15)))) (.step 57 (.run (.close 18)))) (.step 57 (.step 71 (.run (.close 43))))) (.step 57 (.step 43 (.step 2 (.run (.close 55)))))) (.split 24 0 (.step 43 (.split 6 0 (.split 12 0 (.step 43 (.run (.close 18))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68))))) (.step 68 (.run (.close 2))))) (.split 24 0 (.split 39 0 (.step 43 (.split 6 0 (.split 4 0 (.step 24 (.run (.close 18))) (.step 43 (.run (.close 2)))) (.step 71 (.run (.close 68))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 24 0 (.split 39 0 (.step 68 (.split 18 0 (.split 19 0 (.step 43 (.step 18 (.step 43 (.run (.close 40))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 31 (.step 71 (.step 40 (.step 68 (.step 48 (.run (.close 2))))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.split 16 0 (.split 17 0 (.step 3 (.step 58 (.step 55 (.step 43 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 23))))) (.step 55 (.step 40 (.split 24 0 (.split 39 0 (.step 68 (.step 58 (.step 3 (.step 71 (.step 2 (.run (.close 4))))))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part945
namespace Part946
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960667312644746696187223091572042864535722476505309650863932023364101684932378624, 5789234136395753406671521056007779241891423355673473088456043642362961639010462828738783475491717968537429113180425764726578159668884175390555260845831183997029667820705077572209851657296413376583884812362112875739641544704⟩
def references : Fin 1 → Box := ![Part945.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 46 0 (.split 27 0 (.split 47 0 (.split 32 0 (.reuse 0) (.step 40 (.step 55 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.step 58 (.step 55 (.split 56 0 (.step 4 (.run (.close 2))) (.step 71 (.run (.close 2))))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 23))))))) (.split 32 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 40 (.step 18 (.step 59 (.step 48 (.run (.close 2)))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 42 0 (.split 6 0 (.step 23 (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.run (.close 3)))) (.step 43 (.run (.close 7)))) (.step 4 (.run (.close 29))))) (.split 24 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 3 (.split 4 0 (.split 12 0 (.split 16 0 (.step 59 (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 48))))) (.step 55 (.step 40 (.run (.close 48)))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 23)))) (.step 71 (.run (.close 55)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 16 0 (.split 53 0 (.split 57 0 (.step 52 (.step 68 (.step 40 (.run (.close 43))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 68)))) (.step 68 (.step 43 (.run (.close 2))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 71 (.run (.close 68)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part945.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part946
namespace Part947
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960667312644746696187223091572042864535722476505309650863932023364101684932378624, 5789234136395753406671521056007779241891423355673473088456043642362961639010462828738783475491717971181652988341420160534239391799968334704173992702956061135624848918328242517455234958053256433519240045359687723086331772928⟩
def references : Fin 1 → Box := ![Part946.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 41 0 (.split 11 0 (.reuse 0) (.split 24 0 (.split 39 0 (.split 58 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 50 0 (.split 35 0 (.step 40 (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 4 (.run (.close 7)))) (.step 4 (.run (.close 43)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68))))) (.split 11 0 (.split 35 0 (.split 42 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 18 0 (.step 31 (.step 70 (.step 55 (.step 2 (.run (.close 40)))))) (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 40)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 23)))) (.step 43 (.step 55 (.step 2 (.run (.close 40)))))) (.step 4 (.step 71 (.step 43 (.run (.close 2)))))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 41 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 7 0 (.split 53 0 (.split 17 0 (.split 13 0 (.step 43 (.step 68 (.step 24 (.step 9 (.run (.close 4)))))) (.step 4 (.run (.close 55)))) (.step 68 (.step 43 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 71 (.step 4 (.step 68 (.run (.close 2)))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 5)))) (.step 68 (.run (.close 23)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part946.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part947
namespace Part948
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960667312644746696187223091572042864535722476505309650863932023364101684932378624, 5789234136395753406671525840073512305702396937558630707244719933604936855676440595746157124242075702187752221165452200458272286089606738145503232915675303056596123374110838506495699618576824095508420343459577858161039638528⟩
def references : Fin 1 → Box := ![Part947.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 66 0 (.reuse 0) (.split 8 0 (.split 24 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 69 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 54 0 (.step 43 (.step 31 (.run (.close 48)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 31)))) (.step 55 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 48))))) (.step 68 (.run (.close 40)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 68 (.run (.close 40)))) (.step 68 (.run (.close 40)))) (.step 58 (.step 63 (.step 55 (.run (.close 43))))))) (.split 24 0 (.split 39 0 (.split 58 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 11 0 (.split 50 0 (.split 35 0 (.step 55 (.step 40 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 71 (.step 4 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part947.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part948
namespace Part949
def root : Box := ⟨3351951982485649274893506249551461531869841455148100586362883263517663489333169539762368061540392522465255300961493082915262650063307946587614861955432448, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707440234307083784982014331757949056417138311482380314387230789641240443581596849644795210903285216114355455130515167358480659623368982528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 35 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 56 0 (.split 71 0 (.split 72 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.split 54 0 (.step 36 (.run (.close 2))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.run (.close 54)))) (.step 55 (.step 2 (.run (.close 43))))) (.step 68 (.step 2 (.run (.close 40))))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 55)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.step 43 (.step 2 (.run (.close 40))))))) (.step 4 (.step 71 (.step 43 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 23))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 23)))))) (.step 68 (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part949
namespace Part950
def root : Box := ⟨3351951982485649274896345463318241246286049751272663101887951450299836401133641883735296068406416052210035798327573115433281379463956500621654554469990400, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696430540054073618934850630393945499223403764212330992953816042605433203837077066753283426859115191835738212492906594304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 24 0 (.split 32 0 (.split 39 0 (.split 53 0 (.split 58 0 (.split 50 0 (.split 59 0 (.split 70 0 (.split 74 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 31))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 40)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.step 43 (.run (.close 3))))) (.step 63 (.run (.close 40)))) (.step 68 (.run (.close 43)))) (.step 71 (.step 68 (.run (.close 3))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 68 (.step 63 (.run (.close 55))))) (.step 68 (.run (.close 3)))) (.step 68 (.step 63 (.run (.close 40))))) (.step 71 (.step 68 (.run (.close 31))))) (.step 55 (.step 68 (.run (.close 40))))) (.step 58 (.step 63 (.step 55 (.run (.close 23)))))) (.step 68 (.step 4 (.step 71 (.run (.close 2)))))) (.step 55 (.step 40 (.run (.close 23))))) (.step 68 (.step 4 (.step 71 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part950
namespace Part951
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175634624659491331474419651533131627390460008275677978454443127913129789750382981020888816731291648, 5789234136395753406671525840073512305702396937558630707244719933604936855676443717494707443073520850564696430540054073618934850632479870338989917516551219377885019279522136838950995787404691246998001642793394999624705507328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 35 0 (.split 4 0 (.split 42 0 (.split 72 0 (.split 10 0 (.split 16 0 (.split 30 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 40))))) (.step 4 (.run (.close 40)))) (.step 43 (.run (.close 2)))) (.step 68 (.step 43 (.step 2 (.run (.close 40)))))) (.step 71 (.step 4 (.step 55 (.run (.close 43)))))) (.step 68 (.step 71 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 55 (.step 71 (.run (.close 23)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part951
namespace Part952
def root : Box := ⟨3351955179156164798469551184307024840072138541712598673106091018511378221341327864084741699380672628587821332198499944825691495802659118955305838573518848, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004632837140638117023781090959647065646298177102659372888212729059152617418658564873011628842940369888986203778346647552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 53 0 (.split 57 0 (.split 66 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 42 0 (.split 4 0 (.step 57 (.split 74 0 (.step 2 (.run (.close 43))) (.step 71 (.run (.close 52))))) (.step 58 (.run (.close 52)))) (.step 58 (.run (.close 52)))) (.step 71 (.run (.close 52)))) (.step 58 (.step 68 (.run (.close 23))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 52)))) (.step 55 (.run (.close 52)))) (.step 55 (.step 68 (.run (.close 24))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 55 (.run (.close 68)))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))) (.step 4 (.step 68 (.step 58 (.run (.close 2)))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 58 (.step 2 (.run (.close 4))))))) (.step 58 (.step 63 (.run (.close 3))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 4 (.step 68 (.step 58 (.run (.close 2)))))) (.step 4 (.step 68 (.step 58 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part952
namespace Part953
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564962519986072543755314000227332181871061374796259959899888563344708228295006617600, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004632837140638117023781090959647065646300029776087169947339506194912756425184217192766279091965001210330330388420886528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 31 0 (.split 32 0 (.split 33 0 (.split 41 0 (.split 53 0 (.split 70 0 (.split 39 0 (.split 58 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 69 0 (.split 22 0 (.split 35 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 43))) (.step 71 (.run (.close 29)))) (.step 71 (.run (.close 29)))) (.step 48 (.run (.close 29)))) (.step 48 (.run (.close 29)))) (.step 15 (.run (.close 2)))) (.step 15 (.run (.close 29)))) (.step 4 (.step 43 (.run (.close 23))))) (.step 71 (.run (.close 57)))) (.step 4 (.step 71 (.step 43 (.run (.close 23)))))) (.step 4 (.step 71 (.step 43 (.run (.close 23)))))) (.step 40 (.step 43 (.run (.close 24))))) (.step 40 (.step 43 (.run (.close 24))))) (.step 71 (.step 43 (.run (.close 23))))) (.step 71 (.step 43 (.run (.close 23))))) (.step 4 (.step 71 (.run (.close 31))))) (.step 4 (.step 71 (.run (.close 57))))) (.step 4 (.step 71 (.step 43 (.step 55 (.run (.close 43))))))) (.step 4 (.step 71 (.step 43 (.step 55 (.step 43 (.run (.close 2)))))))) (.step 4 (.step 71 (.run (.close 31))))) (.step 71 (.step 4 (.step 43 (.step 55 (.step 43 (.run (.close 2)))))))) (.step 4 (.step 71 (.run (.close 28)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part953
namespace Part954
def root : Box := ⟨3351951982485649274893506249551461531872304080535375239126399978740910540823484796349150786603969859909808222146441052168523042504862330591652099181772800, 5789234136395753406671525840073512305702396937558630707244719933604936855679640388010231019118455606128004635299766025391678731858399653324622162847259791574037756252963250521782794935768429492483605931517557880802670280704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 49 0 (.split 50 0 (.split 44 0 (.split 59 0 (.split 10 0 (.split 46 0 (.split 47 0 (.step 39 (.step 2 (.run (.close 71)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 28)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 41)))) (.step 43 (.run (.close 40)))) (.step 43 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 55 (.step 58 (.step 63 (.run (.close 2)))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 71 (.step 43 (.run (.close 2))))) (.step 58 (.run (.close 43)))) (.step 71 (.step 43 (.step 2 (.run (.close 4)))))) (.step 71 (.step 43 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.run (.close 43))))) (.step 71 (.step 55 (.step 58 (.step 63 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part954
namespace Part955
def root : Box := ⟨4898883310657342436947850401401639604522231782625217913215901199891213872566101707146281650264030310267928222263858572706938491816371821281229944469864820300348098609791186571489186309709496681179906048, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847339484772156373619047108574907601362484448124777245764140671763518648622798974341543299218607311901715369404231185803903275798917808128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 18 0 (.split 38 0 (.split 56 0 (.split 26 0 (.split 35 0 (.split 41 0 (.split 49 0 (.split 6 0 (.step 54 (.step 70 (.step 2 (.run (.close 40))))) (.step 7 (.run (.close 2)))) (.step 52 (.run (.close 2)))) (.step 70 (.run (.close 2)))) (.step 18 (.step 71 (.step 57 (.step 43 (.run (.close 15))))))) (.step 18 (.step 71 (.step 57 (.run (.close 7)))))) (.step 7 (.step 18 (.run (.close 2))))) (.step 18 (.step 7 (.step 18 (.step 58 (.run (.close 2))))))) (.step 18 (.split 4 0 (.step 26 (.step 54 (.step 18 (.run (.close 2))))) (.step 43 (.run (.close 18)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 24))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 71 (.run (.close 75))))) (.step 68 (.step 71 (.run (.close 39))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 71 (.step 3 (.step 71 (.run (.close 68))))))) (.step 68 (.step 71 (.step 3 (.step 71 (.run (.close 68))))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 7))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part955
namespace Part956
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408356095931599237832221556720619803394189297042851106347818643981064415365157142549748107323388532388896774729702706905351992849203200, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488676480120581703004883085445305527823094854966341976908392521004461394977957598956528096956487444526106834632704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 12 0 (.split 4 0 (.split 10 0 (.split 39 0 (.step 2 (.run (.close 4))) (.step 4 (.step 2 (.run (.close 5))))) (.step 58 (.run (.close 2)))) (.step 71 (.step 64 (.step 2 (.run (.close 5)))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 40))))) (.step 68 (.step 55 (.run (.close 48))))) (.step 68 (.step 55 (.step 71 (.run (.close 58)))))) (.step 68 (.run (.close 64)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 71)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 40))))) (.step 68 (.step 71 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part956
namespace Part957
def root : Box := ⟨3351951982485649274893506249551461531869841457496643166949465766624132161750004340020429245095542962279333836067931501619918094327631021748870387964313600, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828663164476838110974925902317160122230648890885228263228295432925793186138656807613100577617639658097737728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 18 0 (.split 62 0 (.split 63 0 (.split 64 0 (.split 49 0 (.split 10 0 (.split 56 0 (.split 19 0 (.split 23 0 (.step 39 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 59 (.run (.close 71)))) (.step 7 (.run (.close 39)))) (.step 18 (.step 7 (.run (.close 37))))) (.step 39 (.step 68 (.run (.close 2))))) (.step 39 (.run (.close 15)))) (.step 18 (.step 59 (.step 71 (.run (.close 2)))))) (.step 18 (.step 39 (.run (.close 2))))) (.step 39 (.step 31 (.split 46 0 (.step 75 (.step 22 (.run (.close 2)))) (.step 48 (.run (.close 2))))))) (.step 39 (.run (.close 2)))) (.split 18 0 (.step 39 (.step 31 (.split 46 0 (.split 7 0 (.step 39 (.step 48 (.run (.close 29)))) (.step 55 (.run (.close 2)))) (.step 48 (.run (.close 2)))))) (.step 68 (.run (.close 31))))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 39)))) (.step 43 (.run (.close 39)))) (.step 43 (.run (.close 39)))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 40 (.step 43 (.run (.close 4))))) (.step 43 (.step 40 (.step 68 (.run (.close 54)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 7 (.step 58 (.run (.close 43)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 40 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part957
namespace Part958
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538736640857906306459213368225179810374932444689138911867375071506771504661352151818434510848, 5653543574944809739115343129751252151564818225746450259442063143583815513308591211228695391721430429330846335624412911208827025315104611138896698281087572571896580403018098973144965851157087713078523463002553477163384832⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 13 0 (.split 62 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 58 0 (.split 70 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 18 0 (.split 6 0 (.split 12 0 (.split 19 0 (.step 33 (.step 43 (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 39)))) (.step 15 (.run (.close 18)))) (.step 15 (.step 18 (.step 57 (.run (.close 9)))))) (.step 38 (.step 22 (.split 4 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 18))))))) (.step 55 (.step 40 (.step 2 (.run (.close 55)))))) (.step 40 (.step 22 (.step 68 (.run (.close 2)))))) (.split 4 0 (.step 29 (.step 55 (.step 24 (.run (.close 2))))) (.step 2 (.run (.close 7))))) (.step 55 (.step 43 (.step 2 (.run (.close 40)))))) (.step 43 (.step 55 (.run (.close 22))))) (.step 43 (.step 55 (.step 40 (.step 2 (.run (.close 40))))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 18 (.step 55 (.step 3 (.run (.close 40)))))) (.step 18 (.step 55 (.step 3 (.run (.close 31)))))) (.step 18 (.step 68 (.step 3 (.run (.close 33)))))) (.step 18 (.step 68 (.step 3 (.run (.close 7)))))) (.step 18 (.step 68 (.step 31 (.run (.close 3)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 22 0 (.split 16 0 (.split 26 0 (.split 30 0 (.step 31 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 68))))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 55 (.step 3 (.run (.close 31))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part958
namespace Part959
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538736640857906306459213368225179810374932444689138911867375071506771504661352151818434510848, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828663164476838110976915195262799268799270419877815546588697257530376373583326827468228123817344943368699904⟩
def references : Fin 1 → Box := ![Part958.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 11 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 7 0 (.reuse 0) (.step 3 (.split 4 0 (.split 6 0 (.split 10 0 (.step 22 (.split 22 0 (.split 16 0 (.split 41 0 (.step 16 (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 68))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 7)))))) (.step 55 (.step 40 (.step 23 (.run (.close 2)))))) (.step 18 (.step 40 (.step 3 (.run (.close 2)))))) (.step 18 (.step 40 (.step 3 (.run (.close 31)))))) (.step 18 (.step 40 (.step 31 (.step 29 (.step 40 (.step 3 (.run (.close 2))))))))) (.step 55 (.step 40 (.step 23 (.run (.close 2)))))) (.step 55 (.step 40 (.step 23 (.run (.close 2)))))) (.step 18 (.step 43 (.step 31 (.step 71 (.run (.close 23))))))) (.step 68 (.step 43 (.step 24 (.step 3 (.step 2 (.run (.close 23)))))))) (.step 18 (.step 43 (.step 31 (.run (.close 33)))))) (.step 18 (.step 31 (.step 43 (.step 59 (.step 43 (.run (.close 2)))))))) (.step 68 (.step 43 (.step 24 (.step 3 (.step 2 (.run (.close 23)))))))) (.step 24 (.step 68 (.step 43 (.step 3 (.step 2 (.run (.close 23))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part958.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part959
namespace Part960
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960667312644746696187223091572042864535722476505309652101872062649481959831502848, 5653543574944809739115343129751252151564818225746450259442063143583815513308591211228695391721430429330846335624412911208827025315104611138896698281087572571896580403018098973144965851157087714316463502287933752062509056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 13 0 (.split 62 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 58 0 (.split 49 0 (.split 6 0 (.split 70 0 (.split 12 0 (.split 50 0 (.split 54 0 (.split 59 0 (.split 4 0 (.split 10 0 (.split 16 0 (.step 2 (.run (.close 23))) (.step 43 (.run (.close 2)))) (.split 18 0 (.step 39 (.split 16 0 (.step 2 (.run (.close 68))) (.step 68 (.run (.close 40))))) (.step 68 (.run (.close 2))))) (.split 23 0 (.split 29 0 (.step 39 (.step 18 (.run (.close 7)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 68))))) (.step 18 (.step 68 (.run (.close 2))))) (.split 69 0 (.step 40 (.step 15 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 18 (.step 55 (.run (.close 52))))) (.split 4 0 (.split 10 0 (.step 22 (.step 15 (.run (.close 2)))) (.step 68 (.run (.close 15)))) (.step 68 (.run (.close 52))))) (.step 18 (.step 68 (.step 18 (.run (.close 2)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 15 (.run (.close 2)))) (.step 68 (.run (.close 15)))) (.step 2 (.run (.close 15)))))) (.step 18 (.step 55 (.step 18 (.run (.close 2)))))) (.step 18 (.step 55 (.step 3 (.run (.close 40)))))) (.step 18 (.step 55 (.step 3 (.run (.close 52)))))) (.step 18 (.step 68 (.step 3 (.run (.close 64)))))) (.step 3 (.step 68 (.step 64 (.run (.close 2)))))) (.step 18 (.step 68 (.step 31 (.run (.close 3)))))) (.step 3 (.split 4 0 (.split 6 0 (.split 10 0 (.step 22 (.step 16 (.step 71 (.run (.close 31))))) (.step 71 (.step 2 (.run (.close 68))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 55 (.step 52 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part960
namespace Part961
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960667312644746696187223091572042864535722476505309652101872062649481959831502848, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828663164476838110976915195262799268799270419877815546588697257530376373583326828706168163102725218267824128⟩
def references : Fin 1 → Box := ![Part960.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 11 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 7 0 (.reuse 0) (.step 3 (.split 4 0 (.split 6 0 (.split 10 0 (.step 22 (.step 16 (.step 71 (.run (.close 31))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 7)))))) (.step 40 (.step 55 (.step 23 (.run (.close 2)))))) (.step 18 (.step 40 (.step 3 (.run (.close 2)))))) (.step 18 (.step 40 (.step 31 (.split 18 0 (.step 3 (.step 40 (.step 3 (.run (.close 2))))) (.step 68 (.run (.close 2)))))))) (.step 18 (.step 40 (.step 31 (.split 18 0 (.step 66 (.step 43 (.run (.close 2)))) (.step 68 (.run (.close 15)))))))) (.step 40 (.step 55 (.step 23 (.step 40 (.run (.close 2))))))) (.step 40 (.step 55 (.step 23 (.step 40 (.run (.close 2))))))) (.step 18 (.step 43 (.step 31 (.step 71 (.run (.close 23))))))) (.step 43 (.step 68 (.step 24 (.step 3 (.step 2 (.run (.close 23)))))))) (.step 18 (.step 31 (.step 43 (.split 18 0 (.step 3 (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 23)))))))) (.step 18 (.step 31 (.step 43 (.split 18 0 (.split 19 0 (.step 31 (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))))))) (.step 3 (.step 68 (.step 43 (.step 24 (.step 2 (.run (.close 23)))))))) (.step 3 (.step 68 (.step 43 (.step 24 (.step 2 (.run (.close 23))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part960.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part961
namespace Part962
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960667312644746696187223091572042864535722476505309650863932023364101684932378624, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828663164476838110976915195262799268799270419877815546588697257530376373583326828706168163102725218267824128⟩
def references : Fin 12 → Box := ![Part948.root, Part949.root, Part950.root, Part951.root, Part952.root, Part953.root, Part954.root, Part955.root, Part956.root, Part957.root, Part959.root, Part961.root]
def proof : Enumeration.Proof 12 := (.split 9 0 (.split 29 0 (.split 36 0 (.split 62 0 (.split 67 0 (.split 38 0 (.split 26 0 (.split 49 0 (.split 31 0 (.split 44 0 (.split 33 0 (.split 48 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 41 0 (.split 50 0 (.split 59 0 (.split 69 0 (.split 58 0 (.split 4 0 (.split 6 0 (.split 18 0 (.split 19 0 (.split 10 0 (.step 3 (.step 2 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 31)))) (.step 55 (.step 2 (.run (.close 31))))) (.step 55 (.step 2 (.run (.close 31))))) (.step 68 (.step 43 (.run (.close 3))))) (.step 68 (.run (.close 4)))) (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 48))))) (.step 68 (.run (.close 31)))) (.step 55 (.run (.close 2)))) (.step 68 (.run (.close 40)))) (.step 68 (.run (.close 40)))) (.step 71 (.step 68 (.run (.close 40))))) (.step 68 (.step 63 (.run (.close 40))))) (.step 58 (.step 63 (.step 55 (.run (.close 43)))))) (.step 58 (.step 63 (.step 55 (.run (.close 23))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)) (.reuse 7)) (.reuse 8)) (.split 8 0 (.split 14 0 (.reuse 9) (.step 40 (.step 43 (.run (.close 4))))) (.step 43 (.step 40 (.run (.close 7)))))) (.reuse 10)) (.reuse 11))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part948.covered
  · exact Part949.covered
  · exact Part950.covered
  · exact Part951.covered
  · exact Part952.covered
  · exact Part953.covered
  · exact Part954.covered
  · exact Part955.covered
  · exact Part956.covered
  · exact Part957.covered
  · exact Part959.covered
  · exact Part961.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part962
namespace Part963
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406671525840073512305702396937558630707244719933604936852403053109598565573060331153737097280786037414848285267174448667255298209017186568519222702771290089932394797241420551206864055370877894879517077405696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 39 0 (.split 58 0 (.split 74 0 (.split 59 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.split 16 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 38 0 (.split 42 0 (.split 46 0 (.step 18 (.run (.close 2))) (.step 58 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 58 (.run (.close 2))))) (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 54 0 (.split 72 0 (.split 5 0 (.split 11 0 (.split 32 0 (.split 53 0 (.step 68 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 5 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.step 68 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part963
namespace Part964
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406676424723384169648139344787960032346849242165387558718364286525149181893426647703982711692594846297057969019764173791176440186841692062440872523876997966007331352536069664567681556244122361880714617552896⟩
def references : Fin 1 → Box := ![Part963.root]
def proof : Enumeration.Proof 1 := (.split 67 0 (.split 24 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 7 0 (.step 43 (.step 5 (.run (.close 18)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 24 0 (.split 39 0 (.step 55 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 68)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 68 (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part963.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part964
namespace Part965
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406676424723384169648139344787960032346849242165387558718364286525149181893426647703982711692594846297057969019764173791176440186841692062440872523876997966007331353929866239475845503799030573535866386382848⟩
def references : Fin 1 → Box := ![Part964.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 14 0 (.reuse 0) (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 5 0 (.split 7 0 (.split 11 0 (.split 53 0 (.split 13 0 (.split 18 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 22 0 (.step 23 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 51)))) (.step 71 (.run (.close 23)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 68 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.step 63 (.step 4 (.run (.close 2)))))) (.step 4 (.step 68 (.step 2 (.run (.close 4))))))) (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 7 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 63 (.step 23 (.run (.close 24))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 58 (.step 4 (.run (.close 5))))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.step 58 (.run (.close 23))))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part964.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part965
namespace Part966
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406676424723384169648139344787960032346849242165387558718364286525149181893426647703982711692594846297057969019764175828212416521327778330886560933255159017475725019866116875616294858180330336872572569780224⟩
def references : Fin 1 → Box := ![Part965.root]
def proof : Enumeration.Proof 1 := (.split 30 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 12 0 (.split 18 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 71 (.step 4 (.step 2 (.run (.close 4)))))) (.step 71 (.step 4 (.step 2 (.run (.close 5)))))) (.step 71 (.step 4 (.step 68 (.step 2 (.run (.close 5))))))) (.step 68 (.step 71 (.step 4 (.step 2 (.run (.close 5))))))) (.step 68 (.step 71 (.run (.close 58))))) (.step 68 (.step 71 (.step 2 (.run (.close 5)))))) (.step 71 (.step 68 (.step 4 (.step 2 (.run (.close 4))))))) (.step 71 (.run (.close 58)))) (.step 71 (.run (.close 58)))) (.step 71 (.run (.close 58)))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 71 (.run (.close 2))))) (.step 55 (.step 71 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part965.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part966
namespace Part967
def root : Box := ⟨3351955179156164798469551184307024840072138541712596433361348840707167663899049104891857910800728887234927192957959188377330716275526854602562690609053696, 5789234136395753406676424723384169648139344787960032346849242165387558721640873803560847339484772156373619047108574907599122739705946973035206698393004325764834219030600190405079366771145267007357053453311321130054738509824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 7 0 (.step 3 (.split 8 0 (.split 13 0 (.split 73 0 (.split 44 0 (.split 48 0 (.split 63 0 (.step 3 (.step 57 (.step 55 (.run (.close 2))))) (.step 71 (.run (.close 3)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 4 (.run (.close 55)))))) (.step 58 (.step 4 (.run (.close 9))))) (.step 58 (.step 68 (.step 2 (.run (.close 4)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 63 (.step 2 (.run (.close 4)))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 48 (.run (.close 2))))) (.step 58 (.step 63 (.step 2 (.run (.close 4)))))) (.step 58 (.step 48 (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part967
namespace Part968
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488676480118341958262705281234748085544335662082553396964651168110322154437201150594480919223994862380362655334400⟩
def references : Fin 2 → Box := ![Part966.root, Part967.root]
def proof : Enumeration.Proof 2 := (.split 62 0 (.split 49 0 (.split 50 0 (.reuse 0) (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 5 (.split 8 0 (.split 14 0 (.step 22 (.split 7 0 (.split 24 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 55)))) (.step 4 (.run (.close 55))))) (.step 58 (.run (.close 3)))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 48)))) (.step 4 (.run (.close 48)))) (.step 4 (.run (.close 48)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.step 58 (.run (.close 2)))))) (.step 58 (.step 48 (.run (.close 2)))))) (.reuse 1)) (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 39 0 (.split 58 0 (.split 42 0 (.step 2 (.run (.close 58))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 5))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part966.covered
  · exact Part967.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part968
namespace Part969
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488676480118341958262705283224041031183482230704082389551934528512146757626592020357604477396861079831992860672000⟩
def references : Fin 1 → Box := ![Part968.root]
def proof : Enumeration.Proof 1 := (.split 10 0 (.split 29 0 (.reuse 0) (.split 30 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 12 0 (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 2)))))) (.split 29 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 49 0 (.split 54 0 (.step 2 (.run (.close 5))) (.step 58 (.run (.close 18)))) (.step 71 (.step 58 (.run (.close 4))))) (.step 58 (.run (.close 18)))) (.step 58 (.run (.close 18)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 7)))) (.step 58 (.step 68 (.run (.close 4))))) (.step 58 (.step 68 (.run (.close 4))))) (.step 58 (.step 68 (.run (.close 5))))) (.step 68 (.run (.close 7)))) (.step 68 (.run (.close 7)))) (.step 68 (.run (.close 7)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 55 (.step 71 (.step 43 (.step 2 (.run (.close 4))))))) (.step 55 (.step 71 (.step 43 (.step 2 (.run (.close 4))))))) (.step 18 (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part968.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part969
namespace Part970
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488676480118341958262705283224041031183482230704082389551934528512146757626592020357605715336900365213367271424000⟩
def references : Fin 1 → Box := ![Part969.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 9 0 (.reuse 0) (.split 10 0 (.split 30 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 12 0 (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 2)))))) (.split 9 0 (.split 29 0 (.split 41 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 5 0 (.split 6 0 (.split 8 0 (.split 12 0 (.split 18 0 (.split 11 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 10 0 (.split 16 0 (.split 35 0 (.split 72 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 7)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 55 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 31))))) (.step 2 (.run (.close 7)))) (.step 58 (.step 63 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 48)))) (.step 2 (.step 71 (.run (.close 43))))) (.step 58 (.step 68 (.run (.close 18))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 48)))) (.step 68 (.run (.close 7)))) (.step 2 (.run (.close 48)))) (.step 68 (.step 63 (.run (.close 7))))) (.step 68 (.step 63 (.run (.close 7))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 27)))) (.step 2 (.step 71 (.run (.close 18))))) (.step 2 (.step 71 (.run (.close 18))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part969.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part970
namespace Part971
def root : Box := ⟨3351951982485649274893506249551461531869841455148100584175632538734651564960669121896141029252776584868683625284282683848820051497745139888851808575029248, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828663164476838110976915195262801078050664752943369039885338018278936580926837229339981279627475341910474752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 38 0 (.split 44 0 (.split 46 0 (.split 62 0 (.split 47 0 (.split 69 0 (.split 9 0 (.split 56 0 (.step 29 (.run (.close 2))) (.step 59 (.run (.close 2)))) (.step 18 (.step 31 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 16 (.step 63 (.run (.close 28))))) (.step 71 (.run (.close 2)))) (.step 16 (.step 63 (.run (.close 28))))) (.step 63 (.step 16 (.run (.close 28))))) (.step 59 (.step 28 (.run (.close 71))))) (.step 71 (.step 2 (.run (.close 71))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 16)))) (.step 43 (.run (.close 7)))) (.step 5 (.step 43 (.run (.close 7))))) (.step 5 (.step 43 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 5 (.step 43 (.step 40 (.run (.close 2)))))) (.step 5 (.step 43 (.step 40 (.run (.close 2)))))) (.step 71 (.step 55 (.step 43 (.run (.close 2)))))) (.step 43 (.step 71 (.run (.close 2))))) (.step 71 (.step 55 (.step 43 (.run (.close 2)))))) (.step 71 (.step 43 (.step 5 (.step 2 (.run (.close 43))))))) (.step 43 (.step 71 (.step 5 (.step 2 (.run (.close 43))))))) (.step 71 (.step 55 (.step 58 (.step 43 (.step 2 (.run (.close 5))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part971
namespace Part972
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518388553451862907607279350219148725295181720056948871336799759011358536967913472, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828663164476838110976915195262801078050664752943369039885338018278936580926837229339981279627475341910474752⟩
def references : Fin 2 → Box := ![Part970.root, Part971.root]
def proof : Enumeration.Proof 2 := (.split 34 0 (.split 36 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 32 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 38 0 (.split 46 0 (.split 62 0 (.split 69 0 (.split 9 0 (.split 47 0 (.step 29 (.run (.close 2))) (.step 63 (.run (.close 28)))) (.step 18 (.run (.close 31)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 59 (.step 63 (.run (.close 2))))) (.step 59 (.step 28 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 71))))) (.step 58 (.run (.close 2)))) (.step 63 (.step 58 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 43 (.step 5 (.run (.close 2))))) (.step 43 (.step 5 (.run (.close 2))))) (.step 63 (.step 58 (.step 2 (.run (.close 4)))))) (.step 43 (.step 71 (.run (.close 2))))) (.step 63 (.step 58 (.step 4 (.run (.close 2)))))) (.step 71 (.step 43 (.step 5 (.run (.close 2)))))) (.step 43 (.step 71 (.step 5 (.run (.close 2))))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part970.covered
  · exact Part971.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part972
namespace Part973
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395753406676424723384169652490427225114988419314348753465381716724900623980692854334618536511325009488678828663164476838110976915195262801078050664752943369039885338018278936580926837229339981279627475341910474752⟩
def references : Fin 6 → Box := ![Part912.root, Part923.root, Part933.root, Part944.root, Part962.root, Part972.root]
def proof : Enumeration.Proof 6 := (.split 25 0 (.split 34 0 (.split 5 0 (.split 11 0 (.split 62 0 (.reuse 0) (.split 44 0 (.reuse 1) (.split 6 0 (.split 12 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 24 0 (.split 54 0 (.split 4 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 58 0 (.split 10 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 63)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 48 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 68))))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part912.covered
  · exact Part923.covered
  · exact Part933.covered
  · exact Part944.covered
  · exact Part962.covered
  · exact Part972.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part973
namespace Part974
def root : Box := ⟨4249103942534136789516705652423100970619230591091148891845104567135098320341966040257730908482764726358633022634172476697314360558144165879822781342846137286253636809169754165579087872, 5789234131009374243485986584588438705700382864198799891279783832873501548739201848343526146317261210524199692913074546190957865671630414032595721373852595275967709943418670527917468994628717704201297473553459811774361501696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 14 0 (.split 74 0 (.split 30 0 (.split 34 0 (.split 12 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.split 35 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 72 0 (.split 36 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 4 (.split 11 0 (.split 27 0 (.split 31 0 (.step 22 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 26 0 (.split 17 0 (.split 35 0 (.split 72 0 (.split 12 0 (.split 22 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 26 0 (.split 35 0 (.split 72 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 72 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 17 0 (.split 22 0 (.split 7 0 (.split 34 0 (.step 4 (.step 2 (.run (.close 5)))) (.step 71 (.step 4 (.step 71 (.run (.close 68)))))) (.step 5 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.split 17 0 (.split 22 0 (.split 74 0 (.split 7 0 (.split 34 0 (.step 4 (.step 2 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 15))))) (.step 5 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part974
namespace Part975
def root : Box := ⟨4249103942534136789516705652423100970619230591091148891845104567135098320341966040257730908482764726358633022634172476697314360558144165879822781342846137286253636809169754165579087872, 5789234131009374243485986584588438705700382864198799891279783832873501548739201848343526146317261210524199692913074546190957865671630414032595721373852595275967709943418670529378970631959620622404983515196715367564075597824⟩
def references : Fin 1 → Box := ![Part974.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 8 0 (.split 16 0 (.reuse 0) (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 12 0 (.split 17 0 (.step 2 (.run (.close 5))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 7 0 (.split 34 0 (.step 4 (.run (.close 2))) (.step 71 (.step 4 (.step 71 (.run (.close 68)))))) (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4)))))) (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 12 0 (.split 9 0 (.split 8 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 31 0 (.split 41 0 (.split 24 0 (.split 16 0 (.step 22 (.split 17 0 (.step 57 (.step 22 (.step 4 (.run (.close 2))))) (.step 71 (.run (.close 5))))) (.step 71 (.run (.close 5)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 4 (.run (.close 63))))) (.step 2 (.step 4 (.run (.close 63))))) (.step 2 (.run (.close 52)))) (.step 4 (.step 15 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part974.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part975
namespace Part976
def root : Box := ⟨4898883310657342441196954343935776394038937435044966931852646141707469258161654812749510129150848249941483498207888647500610847137899551282357081936436943315635157476132014206878891095515149161826615296, 5653543574944809739110559064018183993757903128166895795175892990981754768809801048008677475341051256135543909148114859174928009975912813423484310561107045676609474582676010138416436538247014919009265611812703260664397824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.split 24 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 54 (.run (.close 2)))) (.step 70 (.run (.close 2)))) (.step 76 (.step 65 (.step 2 (.run (.close 4)))))) (.step 54 (.run (.close 2)))) (.step 64 (.step 15 (.step 5 (.run (.close 2)))))) (.step 76 (.step 52 (.step 68 (.run (.close 70)))))) (.split 53 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 38 0 (.step 52 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 34 0 (.split 35 0 (.split 53 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 38 0 (.step 52 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 26 0 (.step 70 (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 70))))) (.split 26 0 (.step 72 (.step 54 (.step 2 (.run (.close 4))))) (.step 68 (.run (.close 2))))) (.split 26 0 (.step 65 (.split 35 0 (.step 65 (.step 54 (.split 72 0 (.split 6 0 (.split 12 0 (.split 10 0 (.split 34 0 (.step 2 (.run (.close 5))) (.step 68 (.run (.close 55)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 68 (.run (.close 55)))))) (.step 68 (.run (.close 55))))) (.step 68 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part976
namespace Part977
def root : Box := ⟨4898883310657342441196954343935776394038937435044966931852646141707469258161654812749510129150848249941483498207888647500610847137899551282357081936436943315635157476132014206878891095515149161826615296, 5789234131009374243490885467899096048137330714600201530884306064656123414700435260842582766600901791487533029684885191370313729551719393667929246958360335135262911372116455990149829357787535788844099993520333306206355456000⟩
def references : Fin 1 → Box := ![Part976.root]
def proof : Enumeration.Proof 1 := (.split 57 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.reuse 0) (.split 26 0 (.split 35 0 (.step 64 (.step 4 (.step 68 (.step 2 (.run (.close 48)))))) (.step 4 (.run (.close 55)))) (.step 2 (.run (.close 4))))) (.split 26 0 (.step 70 (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 70))))) (.split 34 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 11 0 (.step 52 (.run (.close 2))) (.step 4 (.run (.close 31)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 71))))) (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 14 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 11 0 (.step 52 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 4 (.run (.close 70)))) (.step 4 (.step 71 (.run (.close 68)))))) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 64 (.step 73 (.split 16 0 (.step 76 (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 55)))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part976.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part977
namespace Part978
def root : Box := ⟨4898883310657342441196954343935776394038937435044966931852646141707469258161654812749510129150848249941483498207888647500610847137899551282357081936436943315635157476132014206878891095515149161826615296, 5789234131009374243490885467899096048137330714600201530884306064656123414700435263894142466683577760769814104721883428400641618261355537953737699198356322350552752664796963306814783008092906500593259369711290164057026330624⟩
def references : Fin 1 → Box := ![Part977.root]
def proof : Enumeration.Proof 1 := (.split 9 0 (.split 46 0 (.split 47 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 65 (.step 64 (.step 55 (.split 16 0 (.step 3 (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2))))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.split 47 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 64 (.step 31 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 64))))) (.split 6 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 14 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 33 0 (.split 41 0 (.step 64 (.step 71 (.step 48 (.step 18 (.run (.close 2)))))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 54)))) (.step 2 (.step 71 (.run (.close 18))))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 54)))) (.step 2 (.step 71 (.run (.close 18))))) (.step 3 (.run (.close 63)))) (.step 3 (.run (.close 52)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 52)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part977.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part978
namespace Part979
def root : Box := ⟨4249103942534136789516705652423100970619230591091148891845104567135098320341966040257730908482764726358633022634172476697314360558144165879822781342846137286253636809169754165579087872, 5789234131009374243490885467899096048137330714600201530884306064656123414700435263894142466683577760769814104721883428400641618261355537953737699198356322350552752664796963306814783008092906500593259369711291289956933173248⟩
def references : Fin 2 → Box := ![Part975.root, Part978.root]
def proof : Enumeration.Proof 2 := (.split 5 0 (.split 67 0 (.split 10 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 47 0 (.split 57 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 64 (.run (.close 2)))) (.step 63 (.step 64 (.run (.close 18))))) (.step 63 (.step 72 (.step 64 (.run (.close 18)))))) (.step 63 (.step 65 (.step 64 (.run (.close 18)))))) (.step 31 (.step 16 (.run (.close 64))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2)))))) (.reuse 1)) (.split 12 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 54 0 (.split 14 0 (.split 74 0 (.split 42 0 (.split 16 0 (.split 39 0 (.step 2 (.run (.close 48))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.step 2 (.run (.close 23)))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part975.covered
  · exact Part978.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part979
namespace Part980
def root : Box := ⟨4249103942534136789516705652423100970619230591091148891845104567135098320341966040257730908482764726358633022634172476697314360558144165879822781342846137286253636809169754165579087872, 5789234131009374243490885467899096048137330714600201530884306064656123414700435263894142466683577760769814104721883428400641618261355537953737699198356322350552752664796963306814783008092906500593259369711291291056444801024⟩
def references : Fin 1 → Box := ![Part979.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.reuse 0) (.split 9 0 (.split 29 0 (.split 8 0 (.split 18 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 23 0 (.split 31 0 (.split 11 0 (.split 53 0 (.split 38 0 (.step 54 (.split 17 0 (.step 54 (.split 67 0 (.split 22 0 (.split 10 0 (.split 42 0 (.step 54 (.step 2 (.run (.close 4)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 54 (.step 70 (.step 52 (.step 2 (.run (.close 4)))))))) (.step 7 (.run (.close 54))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.step 31 (.run (.close 68))))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 18 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 31 (.step 7 (.run (.close 4))))) (.step 31 (.step 7 (.run (.close 4))))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.run (.close 7)))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.run (.close 13)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part979.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part980
namespace Part981
def root : Box := ⟨4355331541097490209254623293730246096054646051010936663741691484704841060700443538559476949465241072925900020173965508794416492294609121871122610447398729724410119407492711004473495912448, 5653543574944809739110559064018188344840340283122968260282481068804749852836624519413892407863400676122581326247924408722035276370365298773323703697681973018694254807457672806906313106844824192668225602835562642406375424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 10 0 (.split 34 0 (.split 36 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 65 (.run (.close 2)))) (.step 72 (.step 2 (.run (.close 4))))) (.step 64 (.run (.close 2)))) (.step 64 (.run (.close 2)))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.split 26 0 (.split 35 0 (.step 65 (.step 64 (.step 65 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63))))) (.split 26 0 (.split 35 0 (.step 72 (.step 64 (.step 65 (.step 64 (.step 2 (.run (.close 4))))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63))))) (.split 26 0 (.split 35 0 (.step 65 (.step 68 (.step 65 (.step 4 (.step 2 (.run (.close 5))))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part981
namespace Part982
def root : Box := ⟨4355331541097490209254623293730246096054646051010936663741691484704841060700443538559476949465241072925900020173965508794416492294609121871122610447398729724410119407492711004473495912448, 5789234131009374243490885467899096052488413151755157603349412652733946409784462084313987981533424140907520067101985000919860836818113846153279086351496910062604996152341237652818319234356133598117758953511357291488004276224⟩
def references : Fin 1 → Box := ![Part981.root]
def proof : Enumeration.Proof 1 := (.split 57 0 (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 74 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.split 6 0 (.split 10 0 (.step 5 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 64)))) (.step 2 (.run (.close 63)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 4 0 (.split 6 0 (.split 10 0 (.step 5 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 15)))) (.step 2 (.run (.close 63)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.step 2 (.step 63 (.run (.close 55))))) (.step 2 (.run (.close 63)))) (.step 2 (.step 63 (.run (.close 55))))) (.step 2 (.step 71 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part981.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part982
namespace Part983
def root : Box := ⟨4249103942534136789516705652423100970619230591091148891845104567135098320341966040257730908482764726358633022634172476697314360558144165879822781342846137286253636809169754165579087872, 5789234136395753406676419939313869692557664905278705561440342684860186054526843810314198743377818674055770641158415561028587331756245744777467301507339792387752522142695386692053846502904397286191305415997161581265444405248⟩
def references : Fin 2 → Box := ![Part980.root, Part982.root]
def proof : Enumeration.Proof 2 := (.split 71 0 (.split 62 0 (.split 25 0 (.reuse 0) (.split 34 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 74 0 (.split 16 0 (.split 35 0 (.split 17 0 (.split 22 0 (.split 58 0 (.split 12 0 (.split 72 0 (.step 2 (.run (.close 58))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.step 55 (.step 2 (.run (.close 23))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 58 (.step 2 (.run (.close 23)))))) (.reuse 1)) (.split 26 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 72 0 (.split 4 0 (.split 10 0 (.split 14 0 (.split 74 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 72))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.step 2 (.run (.close 48)))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 22))))) (.step 71 (.step 4 (.run (.close 22))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part980.covered
  · exact Part982.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part983
namespace Part984
def root : Box := ⟨4249103942534136789516705652423100970619230591091148891845104567135098320341966040257730908482764726358633022634172476697314360558144165879822781342846137286253636809169754165579087872, 5789234136395753406676424723379602756368638487163863180229018976102161271192821577321572392128176405061869873982447600952620226045884148218796541720059034308723796598477982681094311163427964948180485714097050590440245428224⟩
def references : Fin 1 → Box := ![Part983.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 6 0 (.split 12 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 35 0 (.split 71 0 (.split 9 0 (.split 72 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.run (.close 71)))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 63)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part983.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part984
namespace Part985
def root : Box := ⟨4455512664750617552341058662897343170067014083340512898355134538365578040575544352225720737533028990361056739075985922561821135518828759314334494392822567639352124802816755410069472407453696, 5789234136395753406676424723384169652494676329057522556103865459117801465743534247173958790888768941239984028592963773444417399566170386858750579090658112357883376504677405511028603418841010157693395158993373779939320397824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 12 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 64))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 63 (.step 40 (.step 5 (.step 71 (.step 2 (.run (.close 48)))))))) (.step 71 (.step 4 (.step 68 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 40 (.step 68 (.run (.close 63)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part985
namespace Part986
def root : Box := ⟨4249103942534136789516705652423100970622352339641464884076486164364891486647714638400395879633623883318258394372992242317434666661207657850982608273967543909149084784849042450885378048, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509106881000322837213821759269522042560064537321246015710204462396932123503496810780469002999763245772131564316290606969053068224626688000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 6 0 (.split 12 0 (.split 42 0 (.split 54 0 (.split 4 0 (.split 24 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 63))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part986
namespace Part987
def root : Box := ⟨4249103942534136789516705652423100970619230591091148891845104567135098320341966040257730908482764726358633022634172476697314360558144165879822781342846137286253636809169754165579087872, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509106881000322837213821759269522042560064537321246015710204462396932123503496810780469002999763245772131564316290606969053068224626688000⟩
def references : Fin 3 → Box := ![Part984.root, Part985.root, Part986.root]
def proof : Enumeration.Proof 3 := (.split 48 0 (.split 63 0 (.split 64 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 12 0 (.split 71 0 (.split 72 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 63 (.step 5 (.step 71 (.step 2 (.run (.close 48))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.step 2 (.run (.close 4)))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 40 (.step 68 (.run (.close 63)))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part984.covered
  · exact Part985.covered
  · exact Part986.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part987
namespace Part988
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608413325262848, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109720214089616928237967565646605077776856232811200546377436968022672875716003741106995933555096411059536044890631446310621094164299776⟩
def references : Fin 2 → Box := ![Part973.root, Part987.root]
def proof : Enumeration.Proof 2 := (.split 61 0 (.reuse 0) (.split 44 0 (.reuse 1) (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 12 0 (.split 42 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 24 0 (.split 10 0 (.split 35 0 (.split 72 0 (.split 30 0 (.split 49 0 (.step 2 (.run (.close 55))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 63)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 3 (.step 48 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 63))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part973.covered
  · exact Part987.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part988
namespace Part989
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211334161123099141995929982416070530017017988825597084267700865670365420929083186739934168155983808746197877039287748564257121958475876099553543187148570624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 38 0 (.split 56 0 (.split 73 0 (.split 46 0 (.split 47 0 (.split 41 0 (.split 23 0 (.split 57 0 (.split 17 0 (.step 27 (.step 2 (.run (.close 23)))) (.step 11 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.split 72 0 (.split 14 0 (.step 44 (.split 17 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2))))) (.step 23 (.step 5 (.run (.close 11))))) (.step 4 (.run (.close 55))))) (.split 23 0 (.step 27 (.step 44 (.run (.close 2)))) (.step 44 (.run (.close 68))))) (.split 16 0 (.split 17 0 (.split 41 0 (.step 18 (.split 74 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2))))) (.step 44 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4)))))) (.split 59 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 24))))) (.step 4 (.step 44 (.step 18 (.run (.close 2)))))) (.step 4 (.step 3 (.step 26 (.run (.close 44))))))) (.split 59 0 (.split 54 0 (.split 72 0 (.split 16 0 (.step 2 (.run (.close 24))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 4 (.step 24 (.step 55 (.run (.close 2))))))) (.split 14 0 (.split 59 0 (.split 54 0 (.split 72 0 (.step 2 (.run (.close 24))) (.step 58 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 4))))) (.step 5 (.step 71 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part989
namespace Part990
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211334161123099141995929982416070530017017988825599377766316855741877031749978488826874964720972977027321614628127136848262678127037799971605083039907971072⟩
def references : Fin 1 → Box := ![Part989.root]
def proof : Enumeration.Proof 1 := (.split 35 0 (.split 13 0 (.reuse 0) (.split 14 0 (.split 54 0 (.split 59 0 (.split 72 0 (.step 2 (.run (.close 24))) (.step 23 (.run (.close 2)))) (.split 24 0 (.step 3 (.run (.close 2))) (.step 5 (.run (.close 63))))) (.step 5 (.run (.close 2)))) (.split 27 0 (.split 32 0 (.step 5 (.split 16 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 13 0 (.split 27 0 (.split 32 0 (.split 38 0 (.split 14 0 (.split 16 0 (.split 72 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 4 (.run (.close 55)))) (.step 4 (.step 71 (.run (.close 11))))) (.step 40 (.run (.close 29)))) (.step 71 (.step 4 (.run (.close 11))))) (.step 23 (.run (.close 11)))) (.split 16 0 (.split 17 0 (.step 31 (.step 40 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 3 (.step 18 (.step 4 (.step 55 (.run (.close 2))))))) (.step 3 (.split 14 0 (.split 24 0 (.step 18 (.step 4 (.run (.close 47)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 14 0 (.split 17 0 (.split 22 0 (.split 24 0 (.step 3 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part989.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part990
namespace Part991
def root : Box := ⟨2772669694120814859578414184143083703436437075375818427843907377673748084941385762046500058423894228346415842282747698440122138624, 5789234136395748269820059484240009140673214437432980755741006239099211334161123099141995929982418778215265182847086906422868019085921014177331402037374492683245543720283985684907152764173978402182798164897403705325596442624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 13 0 (.split 31 0 (.split 33 0 (.split 16 0 (.split 41 0 (.split 35 0 (.split 42 0 (.step 47 (.run (.close 29))) (.step 29 (.run (.close 2)))) (.step 29 (.run (.close 2)))) (.step 40 (.run (.close 2)))) (.step 40 (.step 24 (.step 29 (.run (.close 2)))))) (.step 23 (.step 31 (.step 2 (.run (.close 23)))))) (.step 23 (.split 35 0 (.step 2 (.run (.close 23))) (.step 4 (.run (.close 40)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.step 40 (.step 15 (.step 2 (.run (.close 4)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 23 (.step 26 (.step 4 (.run (.close 2)))))) (.split 13 0 (.step 24 (.step 4 (.step 40 (.step 31 (.step 4 (.step 68 (.step 2 (.run (.close 4))))))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 24 0 (.split 38 0 (.step 40 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.split 24 0 (.step 47 (.run (.close 4))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part991
namespace Part992
def root : Box := ⟨3121748550315995004051291350608025884162782285748674587296232335441946909299346234741613908689115011134233035260984720286658937082860115354189824, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546245974647452127246811155131347975908981826892736188709605713239122527400220060266145245605812616099138734998957879268628497935288500224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 59 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.step 2 (.run (.close 23))) (.step 47 (.split 13 0 (.step 51 (.step 12 (.step 2 (.run (.close 23))))) (.step 71 (.run (.close 2)))))) (.step 47 (.split 32 0 (.step 51 (.split 35 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 4)))))) (.split 53 0 (.split 39 0 (.step 2 (.run (.close 4))) (.step 55 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4))))) (.step 47 (.split 19 0 (.split 33 0 (.split 23 0 (.step 51 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))) (.split 35 0 (.split 14 0 (.step 2 (.run (.close 23))) (.step 58 (.run (.close 18)))) (.step 55 (.run (.close 2))))) (.split 13 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 36 (.step 23 (.run (.close 11)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 4)))) (.step 55 (.run (.close 47)))) (.step 68 (.run (.close 4))))) (.split 35 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 24 (.step 2 (.run (.close 18))))) (.step 58 (.run (.close 11)))) (.step 55 (.step 4 (.run (.close 40)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 71 (.step 63 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 71 (.step 63 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part992
namespace Part993
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546245974650159812494976013392655021010684057071873334291027409113312448865664026387049176878312591105099808805693612873082993610902732800⟩
def references : Fin 3 → Box := ![Part990.root, Part991.root, Part992.root]
def proof : Enumeration.Proof 3 := (.split 48 0 (.split 26 0 (.split 42 0 (.reuse 0) (.split 38 0 (.split 13 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 14 0 (.split 70 0 (.split 16 0 (.split 17 0 (.step 43 (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.run (.close 24)))) (.step 24 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 11)))) (.step 40 (.step 29 (.run (.close 4))))) (.step 3 (.step 4 (.step 40 (.run (.close 2)))))) (.split 35 0 (.step 3 (.step 44 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 24 0 (.step 3 (.split 27 0 (.split 32 0 (.step 55 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 23))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 31 0 (.split 33 0 (.step 43 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 43)))))) (.reuse 1)) (.split 42 0 (.reuse 2) (.split 16 0 (.split 17 0 (.split 22 0 (.split 59 0 (.split 14 0 (.split 24 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 40)))) (.step 63 (.run (.close 47)))) (.step 63 (.step 58 (.run (.close 55))))) (.step 68 (.step 63 (.run (.close 55))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part990.covered
  · exact Part991.covered
  · exact Part992.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part993
namespace Part994
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406105468806093176126834307378890328244224, 5789234136390488133918511110732768150790334308767430415938183061724936651271185314665515958862076932813980930097089427004706924919285273266365138360458968806704564800399115814367738758309208344012570490917636473832895152128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 46 0 (.split 47 0 (.split 44 0 (.split 38 0 (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 54 0 (.split 22 0 (.split 74 0 (.split 19 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 55 (.run (.close 62)))) (.step 4 (.step 55 (.step 43 (.run (.close 23)))))) (.step 9 (.run (.close 23)))) (.step 4 (.step 55 (.step 24 (.run (.close 9)))))) (.step 4 (.step 55 (.step 24 (.run (.close 9)))))) (.split 48 0 (.split 66 0 (.split 63 0 (.step 4 (.step 27 (.run (.close 2)))) (.step 29 (.run (.close 27)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.split 31 0 (.split 33 0 (.split 41 0 (.step 63 (.step 23 (.step 4 (.step 24 (.run (.close 15)))))) (.step 55 (.run (.close 15)))) (.step 55 (.run (.close 27)))) (.step 55 (.run (.close 52))))) (.step 4 (.split 57 0 (.step 9 (.split 18 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 48))))))) (.split 14 0 (.split 16 0 (.step 29 (.run (.close 2))) (.step 68 (.run (.close 23)))) (.step 63 (.run (.close 23))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 31 (.split 38 0 (.split 56 0 (.step 55 (.split 24 0 (.step 21 (.run (.close 2))) (.step 4 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 31 (.split 47 0 (.split 56 0 (.step 55 (.split 39 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part994
namespace Part995
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406105468806093176126834307378890328244224, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221688779583528396375983438519127200383684402998237883219347687169812104441745357008530078553223244353540720689152⟩
def references : Fin 1 → Box := ![Part994.root]
def proof : Enumeration.Proof 1 := (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 13 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 46 0 (.step 9 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 24 0 (.step 3 (.split 31 0 (.split 33 0 (.split 39 0 (.step 4 (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 38 0 (.split 39 0 (.split 56 0 (.step 3 (.step 24 (.step 4 (.step 57 (.step 2 (.run (.close 4))))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.step 3 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.step 47 (.run (.close 2))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part994.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part995
namespace Part996
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221688779583528396375983438519127200383684402998237883219347687169812104441745357008530078553223244353540720689152⟩
def references : Fin 2 → Box := ![Part993.root, Part995.root]
def proof : Enumeration.Proof 2 := (.split 12 0 (.split 44 0 (.reuse 0) (.split 42 0 (.split 59 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 63 0 (.step 2 (.run (.close 23))) (.step 47 (.run (.close 2)))) (.split 35 0 (.split 54 0 (.step 2 (.run (.close 23))) (.step 71 (.step 68 (.run (.close 23))))) (.step 55 (.run (.close 2))))) (.split 26 0 (.split 35 0 (.split 54 0 (.split 14 0 (.step 2 (.run (.close 23))) (.step 58 (.run (.close 18)))) (.step 68 (.run (.close 11)))) (.step 55 (.run (.close 11)))) (.step 55 (.run (.close 11))))) (.split 35 0 (.split 14 0 (.split 54 0 (.split 17 0 (.step 2 (.run (.close 23))) (.step 24 (.step 2 (.run (.close 18))))) (.step 68 (.run (.close 11)))) (.step 58 (.run (.close 11)))) (.step 55 (.run (.close 11))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 71 (.step 63 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 55 (.run (.close 18))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 59 0 (.split 14 0 (.split 24 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 11)))) (.step 63 (.run (.close 47)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 63 (.run (.close 55))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part993.covered
  · exact Part995.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part996
namespace Part997
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210962556493334654746624, 5789234136395748269820059484240009140673214437432980755741006235584434932174254046819813039684190599350258518548316409973563103136998292698615322164322096621475216681249071038038867204268529475454208667489559118316310626304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 70 0 (.split 13 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 18 0 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 29 (.run (.close 2))) (.step 24 (.run (.close 27)))) (.step 24 (.run (.close 27)))) (.step 24 (.run (.close 27)))) (.split 19 0 (.split 23 0 (.step 11 (.run (.close 2))) (.step 15 (.run (.close 9)))) (.step 15 (.run (.close 9))))) (.step 11 (.run (.close 2)))) (.split 12 0 (.split 63 0 (.step 53 (.step 27 (.run (.close 23)))) (.step 55 (.run (.close 9)))) (.step 15 (.run (.close 9))))) (.step 23 (.step 29 (.run (.close 2))))) (.step 23 (.step 29 (.run (.close 2))))) (.step 23 (.step 29 (.run (.close 2))))) (.step 4 (.step 9 (.run (.close 2))))) (.step 4 (.step 9 (.run (.close 29))))) (.step 4 (.step 9 (.split 18 0 (.step 55 (.run (.close 2))) (.step 2 (.run (.close 4))))))) (.step 47 (.step 4 (.run (.close 2))))) (.step 47 (.step 4 (.run (.close 2))))) (.step 47 (.step 4 (.step 55 (.run (.close 2)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 46 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 12 0 (.step 40 (.run (.close 2))) (.step 4 (.run (.close 29)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part997
namespace Part998
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097392419887223186459222605824, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209389759063392308873445608543432260151337566200698594147466472579349404454493721808564327454684977989490909533180002304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 56 0 (.split 14 0 (.split 73 0 (.split 42 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 74 0 (.split 63 0 (.split 64 0 (.split 16 0 (.step 2 (.run (.close 24))) (.step 11 (.run (.close 2)))) (.step 11 (.run (.close 2)))) (.step 11 (.run (.close 2)))) (.step 11 (.run (.close 2)))) (.step 40 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 4 (.run (.close 11)))))) (.split 26 0 (.split 35 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.step 23 (.step 5 (.step 11 (.run (.close 2))))) (.step 55 (.run (.close 23)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 55 (.run (.close 23)))) (.step 55 (.run (.close 11)))) (.step 55 (.run (.close 11))))) (.split 26 0 (.split 35 0 (.split 72 0 (.split 16 0 (.split 24 0 (.step 47 (.step 5 (.step 11 (.run (.close 2))))) (.step 2 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 55 (.run (.close 11)))) (.step 55 (.run (.close 11)))) (.step 2 (.run (.close 11))))) (.step 40 (.step 11 (.run (.close 2))))) (.split 6 0 (.step 3 (.step 23 (.split 12 0 (.step 3 (.step 2 (.run (.close 24)))) (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 4))))) (.split 18 0 (.split 73 0 (.step 11 (.run (.close 2))) (.step 63 (.run (.close 11)))) (.step 63 (.step 23 (.run (.close 68)))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 27 0 (.split 32 0 (.step 63 (.split 35 0 (.split 54 0 (.split 14 0 (.step 3 (.step 2 (.run (.close 24)))) (.step 63 (.run (.close 11)))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 63 (.run (.close 5))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part998
namespace Part999
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221688779583528396375983438519127200383684402998237883219347687169812104441745357008530079762150216889674502242304⟩
def references : Fin 3 → Box := ![Part996.root, Part997.root, Part998.root]
def proof : Enumeration.Proof 3 := (.split 8 0 (.split 6 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 53 0 (.reuse 1) (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.step 47 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))) (.split 13 0 (.split 38 0 (.reuse 2) (.split 12 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 54 0 (.split 70 0 (.split 72 0 (.split 14 0 (.step 43 (.step 3 (.step 2 (.run (.close 24))))) (.step 63 (.run (.close 11)))) (.step 63 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 63 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 68 (.step 2 (.run (.close 4))))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.step 23 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 24))) (.step 71 (.run (.close 2)))) (.step 63 (.step 23 (.run (.close 71)))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part996.covered
  · exact Part997.covered
  · exact Part998.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part999
namespace Part1000
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391212141995192547459203072, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221688779583528396375983438519127200383684402998237883219347687169812103047948782100366132208422596855240144715776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 48))) (.split 6 0 (.step 47 (.run (.close 2))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.step 47 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 59 0 (.split 6 0 (.split 12 0 (.step 23 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.step 3 (.split 12 0 (.step 23 (.run (.close 2))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 35 0 (.split 54 0 (.split 13 0 (.step 3 (.run (.close 2))) (.step 5 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 32 0 (.split 35 0 (.split 53 0 (.split 54 0 (.split 13 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.step 3 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1000
namespace Part1001
def root : Box := ⟨2772669694120814859580762726725857536664326555972605912197855263163529627676332914011506615129254186540854909959788340533079834624, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221691128126111170209211327999723989720711778679101794872521477975577769943656253541094267192804492737065938583552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 14 0 (.split 53 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 59 0 (.step 2 (.run (.close 57))) (.split 31 0 (.step 57 (.run (.close 2))) (.step 55 (.run (.close 2))))) (.step 22 (.step 43 (.run (.close 23))))) (.split 7 0 (.split 38 0 (.split 42 0 (.step 43 (.step 55 (.step 57 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 7 0 (.split 38 0 (.split 42 0 (.step 43 (.step 40 (.step 57 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 38 0 (.step 3 (.step 2 (.run (.close 24)))) (.step 4 (.run (.close 2))))) (.step 3 (.split 59 0 (.step 2 (.run (.close 24))) (.step 4 (.run (.close 71)))))) (.split 12 0 (.split 35 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 29))))) (.split 44 0 (.split 46 0 (.split 47 0 (.step 5 (.step 55 (.step 63 (.run (.close 29))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.step 31 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 31))))) (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.step 31 (.step 40 (.step 11 (.step 4 (.step 63 (.run (.close 29))))))) (.step 4 (.run (.close 43)))) (.step 4 (.run (.close 43)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1001
namespace Part1002
def root : Box := ⟨2772669694120814859580762726725857536664326555972605912197855263163529627676332914011506615129254186540854909959788340533079834624, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221691128126111170209211327999723989720711778680786791539218394459322135013439568698769858629612910259439012937728⟩
def references : Fin 1 → Box := ![Part1001.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 22 0 (.split 8 0 (.reuse 0) (.split 7 0 (.split 13 0 (.split 18 0 (.split 27 0 (.split 19 0 (.split 23 0 (.step 63 (.step 5 (.step 11 (.step 4 (.step 63 (.run (.close 29))))))) (.step 4 (.step 63 (.run (.close 23))))) (.step 63 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 55 (.run (.close 40)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 55))))) (.split 44 0 (.split 48 0 (.split 66 0 (.split 46 0 (.split 53 0 (.split 6 0 (.split 47 0 (.step 40 (.step 4 (.step 68 (.run (.close 43))))) (.step 4 (.run (.close 2)))) (.step 55 (.run (.close 29)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))) (.split 44 0 (.split 48 0 (.split 66 0 (.split 46 0 (.split 64 0 (.split 27 0 (.split 7 0 (.split 13 0 (.step 40 (.step 43 (.step 68 (.step 74 (.step 2 (.run (.close 24))))))) (.step 4 (.run (.close 23)))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 68 (.run (.close 43))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1001.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1002
namespace Part1003
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221691128126111170209211327999723989720711778680786791539218394460783636650770471616973543462329193279094945480704⟩
def references : Fin 3 → Box := ![Part999.root, Part1000.root, Part1002.root]
def proof : Enumeration.Proof 3 := (.split 36 0 (.split 7 0 (.reuse 0) (.split 8 0 (.split 14 0 (.reuse 1) (.split 6 0 (.split 12 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 53 0 (.split 54 0 (.step 3 (.step 23 (.split 70 0 (.split 13 0 (.split 16 0 (.step 31 (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 48 (.step 24 (.run (.close 2))))) (.step 4 (.run (.close 2)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.step 23 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 24))) (.step 71 (.run (.close 2)))) (.step 63 (.step 23 (.run (.close 71)))))) (.step 63 (.run (.close 23)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 23)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))))) (.split 16 0 (.reuse 2) (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 18 0 (.step 43 (.split 38 0 (.split 46 0 (.step 23 (.step 11 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 23))))) (.step 43 (.run (.close 2)))) (.step 4 (.step 55 (.run (.close 68))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 43))))) (.step 68 (.run (.close 3)))) (.step 4 (.step 68 (.run (.close 43))))) (.step 4 (.step 68 (.run (.close 43))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part999.covered
  · exact Part1000.covered
  · exact Part1002.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1003
namespace Part1004
def root : Box := ⟨2772669694120814859578414184143083703436439064668762214317048202143613895088986024864577595495009339953298783599391621963550031872, 5789234136395748269820059484240009140673214433380719458005661553051938029775226659354954225139606433754952116337399336393008582427340388375432673364715105255708881460744702294070003472586687537265749331424374927390721179648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 8 0 (.split 23 0 (.step 55 (.step 2 (.run (.close 23)))) (.step 55 (.step 2 (.run (.close 4))))) (.step 40 (.run (.close 2)))) (.step 47 (.run (.close 32)))) (.step 47 (.step 32 (.run (.close 2))))) (.step 47 (.run (.close 2)))) (.split 47 0 (.split 23 0 (.step 23 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4))))) (.split 47 0 (.split 19 0 (.split 23 0 (.step 23 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4))))) (.split 18 0 (.split 19 0 (.split 48 0 (.split 44 0 (.step 31 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 8 0 (.step 32 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 8 0 (.step 32 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 8 0 (.step 32 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 7 0 (.split 38 0 (.split 47 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.step 69 (.step 11 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.step 40 (.run (.close 2)))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.step 4 (.step 40 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1004
namespace Part1005
def root : Box := ⟨2772669694120814859578414184143083703436439064668762214317048202143613895088986024864577595495009339953298783599391621963550031872, 5789234136395748269820059484240009140673214433380719458005661553051938029775226659354954225139609141440200281195662991980693058490747415001610886250290098656782360523872073655320561308938847097760758311222615046944328777728⟩
def references : Fin 1 → Box := ![Part1004.root]
def proof : Enumeration.Proof 1 := (.split 36 0 (.split 42 0 (.split 6 0 (.split 12 0 (.split 26 0 (.reuse 0) (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 47 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 44 0 (.step 40 (.step 2 (.run (.close 23)))) (.step 29 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 34 (.step 2 (.run (.close 23))))) (.step 40 (.run (.close 12)))) (.step 3 (.run (.close 2)))) (.step 40 (.step 2 (.run (.close 23))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 21 (.step 2 (.run (.close 23))))) (.step 40 (.step 2 (.run (.close 23))))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 8 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 39 0 (.split 35 0 (.split 42 0 (.step 2 (.run (.close 23))) (.step 43 (.run (.close 2)))) (.step 40 (.run (.close 31)))) (.step 40 (.run (.close 2)))) (.step 24 (.step 40 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1004.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1005
namespace Part1006
def root : Box := ⟨2772669694120814859578414184143083703436439064668762214317048202143613895088986024864577595495009339953298783599391621963550031872, 5789234136395748269820059484240009140673214433380719458005661553051938029775226659354954225139609141440200281195662991980693058490747415001610886250290098658467357190568990140526428016053065173640033371821495974344160968704⟩
def references : Fin 1 → Box := ![Part1005.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.split 36 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 36 0 (.split 42 0 (.split 14 0 (.split 22 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 26 0 (.split 6 0 (.split 7 0 (.split 12 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 23 (.run (.close 18)))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.step 2 (.run (.close 23)))))) (.step 40 (.step 24 (.step 23 (.run (.close 2)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 40 (.step 23 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1005.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1006
namespace Part1007
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578098629151000688952104947023872, 5789234136395748269820059484240009140673214433380719458005661553051938029775226659354954225139606433754952116337399336393008582427340388375432673364715105255708881460744702294070003472586687537266987271463660307665620303872⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 44 0 (.split 46 0 (.split 29 0 (.split 47 0 (.split 8 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 40 (.run (.close 2)))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2))))) (.split 47 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 8 0 (.step 47 (.step 40 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4))))) (.split 8 0 (.step 12 (.run (.close 4))) (.step 2 (.run (.close 4))))) (.split 46 0 (.split 29 0 (.split 47 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2))))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 23 (.step 2 (.run (.close 4)))))) (.split 8 0 (.step 32 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 3 (.run (.close 2))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 3 (.run (.close 2))))) (.split 8 0 (.split 29 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 40 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.step 4 (.step 40 (.run (.close 2))))))) (.split 35 0 (.step 2 (.run (.close 4))) (.step 3 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1007
namespace Part1008
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578098629151000688952104947023872, 5789234136395748269820059484240009140673214433380719458005661553051938029775226659354954225139609141440200281195662991980693058490747415001610886250290098658467357190568988642487249751877574014864317777670686207288203542528⟩
def references : Fin 1 → Box := ![Part1007.root]
def proof : Enumeration.Proof 1 := (.split 22 0 (.split 36 0 (.split 42 0 (.split 6 0 (.split 12 0 (.split 26 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 7 0 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 40 (.step 2 (.run (.close 23))))) (.step 3 (.run (.close 2))))) (.split 7 0 (.split 13 0 (.split 14 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 21 (.step 2 (.run (.close 23))))) (.step 40 (.step 2 (.run (.close 23))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 14 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 8 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 35 0 (.split 42 0 (.step 2 (.run (.close 23))) (.step 43 (.run (.close 2)))) (.step 40 (.run (.close 31)))) (.step 40 (.run (.close 2)))) (.step 24 (.step 40 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.run (.close 2)))))) (.split 36 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1007.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1008
namespace Part1009
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578098629151000688952104947023872, 5789234136395748269820059484240009140673214433380719458005661553051938029775226659354954225139609141440200281195662991980693058490747415001610886250290098658467357190568990140526428016053065173641271311860781354619060092928⟩
def references : Fin 1 → Box := ![Part1008.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.split 36 0 (.split 42 0 (.split 14 0 (.split 22 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 40 (.step 2 (.run (.close 23))))) (.step 23 (.step 2 (.run (.close 23))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 23 (.step 2 (.run (.close 23)))))) (.step 40 (.step 23 (.step 2 (.run (.close 23))))))) (.split 26 0 (.split 6 0 (.split 7 0 (.split 12 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 23 (.step 18 (.run (.close 2))))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.run (.close 18))))) (.step 40 (.step 24 (.step 2 (.run (.close 23)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 40 (.step 23 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1008.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1009
namespace Part1010
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221691128126111170209211329989016935359858347302315784126501754862608239840161341378830688975006466709503346737152⟩
def references : Fin 3 → Box := ![Part1003.root, Part1006.root, Part1009.root]
def proof : Enumeration.Proof 3 := (.split 9 0 (.split 29 0 (.reuse 0) (.split 59 0 (.reuse 1) (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 23))) (.step 55 (.step 2 (.run (.close 23))))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 2)))))) (.split 59 0 (.reuse 2) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.step 2 (.run (.close 23))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.step 15 (.step 2 (.run (.close 55)))))) (.step 55 (.step 2 (.run (.close 23))))) (.step 18 (.step 55 (.run (.close 2))))) (.step 18 (.step 11 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 4))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1003.covered
  · exact Part1006.covered
  · exact Part1009.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1010
namespace Part1011
def root : Box := ⟨2772669694120814859578414184143083703438474111352151061256748026303030685966677091433640342354775718546745592261166908536231297024, 5789234136395748269820054700174276076862240855547823136952329947857236117495145332134622281232061047209165950023057215041417898629512537252575285647768894890511586960962340525844350167749055546569401304831680193284200726528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 38 0 (.split 56 0 (.split 73 0 (.split 23 0 (.split 26 0 (.split 8 0 (.split 46 0 (.split 14 0 (.split 35 0 (.split 47 0 (.step 11 (.split 12 0 (.split 16 0 (.step 31 (.run (.close 2))) (.step 68 (.run (.close 31)))) (.step 43 (.run (.close 3))))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 71 (.step 43 (.step 68 (.run (.close 2)))))) (.step 63 (.run (.close 11)))) (.split 47 0 (.step 63 (.step 71 (.step 55 (.run (.close 2))))) (.step 58 (.run (.close 2))))) (.step 11 (.step 48 (.run (.close 68))))) (.step 11 (.step 71 (.step 24 (.step 71 (.run (.close 29))))))) (.split 46 0 (.split 47 0 (.split 57 0 (.split 53 0 (.step 24 (.step 3 (.step 55 (.run (.close 3))))) (.step 68 (.run (.close 3)))) (.step 71 (.run (.close 23)))) (.step 71 (.run (.close 23)))) (.step 71 (.step 68 (.run (.close 2)))))) (.split 63 0 (.step 3 (.step 63 (.step 4 (.step 71 (.run (.close 23)))))) (.step 4 (.run (.close 63))))) (.split 8 0 (.split 12 0 (.split 24 0 (.split 14 0 (.split 31 0 (.split 33 0 (.step 3 (.step 58 (.run (.close 2)))) (.step 71 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 4 (.run (.close 63)))) (.step 68 (.step 4 (.run (.close 23))))) (.step 71 (.run (.close 5)))) (.step 68 (.run (.close 4))))) (.split 8 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 14 0 (.split 27 0 (.split 39 0 (.split 58 0 (.step 3 (.step 58 (.step 40 (.run (.close 41))))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 42)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 71)))) (.step 68 (.step 4 (.run (.close 42))))) (.step 71 (.step 4 (.run (.close 18))))) (.step 68 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1011
namespace Part1012
def root : Box := ⟨2772669694120814859578414184143083703438474111352151061256748026303030685966677091433640342354775718546745592261166908536231297024, 5789234136395748269820054700174276076862240855547823136952329947857236117495145332134622281232061047209165950023057215041417898629512537252575285647768894890511586960962340525844350169110185014253155159866923165233291722752⟩
def references : Fin 1 → Box := ![Part1011.root]
def proof : Enumeration.Proof 1 := (.split 7 0 (.split 6 0 (.split 13 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 27 0 (.step 18 (.step 68 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 31)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 18 (.split 31 0 (.split 33 0 (.step 9 (.step 68 (.step 43 (.run (.close 24))))) (.step 4 (.step 43 (.run (.close 27))))) (.step 4 (.step 43 (.run (.close 27)))))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 71 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 48))))) (.step 71 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 3)))))) (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 31 0 (.split 27 0 (.split 33 0 (.split 59 0 (.step 28 (.step 63 (.step 18 (.run (.close 10))))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 18)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1011.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1012
namespace Part1013
def root : Box := ⟨2772669694120814859578414184143083703438474111352151061256748026303030685966677091433640342354775718546745592261166908536231297024, 5789234136395748269820054700174276076862240855547823136952329947857236117495145332134622281232061047209165950023057215041417898629512537252575285647768894890511586962533148455231886248927490717082222073076130765471483953152⟩
def references : Fin 1 → Box := ![Part1012.root]
def proof : Enumeration.Proof 1 := (.split 18 0 (.split 19 0 (.reuse 0) (.split 8 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 14 0 (.split 24 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 53 0 (.split 27 0 (.step 31 (.step 3 (.run (.close 9)))) (.step 4 (.step 2 (.run (.close 23))))) (.step 4 (.run (.close 31)))) (.step 68 (.step 2 (.run (.close 40))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 24)))) (.step 43 (.run (.close 3)))) (.step 68 (.step 55 (.run (.close 24))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 58 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.step 43 (.run (.close 2)))))) (.step 68 (.step 55 (.step 40 (.run (.close 29)))))) (.step 68 (.step 63 (.step 24 (.run (.close 9))))))) (.split 8 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 14 0 (.split 39 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 27 0 (.step 9 (.step 2 (.run (.close 23)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 23))))) (.step 40 (.step 43 (.run (.close 3))))) (.step 68 (.step 55 (.run (.close 42))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.step 2 (.run (.close 4)))))) (.step 68 (.step 55 (.step 43 (.run (.close 2)))))) (.step 68 (.step 40 (.step 55 (.run (.close 2)))))) (.step 68 (.step 63 (.step 24 (.run (.close 9)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1012.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1013
namespace Part1014
def root : Box := ⟨2772669694120814859578414184143083703438474111352151061256748026303030685966677091433640342354775718546745592261166908536231297024, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546245974650159812494976013395003563593457890301799850864151232226956577102981724418807936243510736382179785694297819151699062931591266304⟩
def references : Fin 1 → Box := ![Part1013.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.split 66 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 12 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 73 0 (.split 18 0 (.step 11 (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.step 40 (.run (.close 3))))))) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 73 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 24 0 (.split 39 0 (.step 55 (.run (.close 2))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 11)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 11))))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.step 40 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1013.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1014
namespace Part1015
def root : Box := ⟨2772669694120814859578414184143083703438474111352151061256748026303030685966677091433640342354775718546745592261166908536231297024, 5789234136395748269820059484240009140673214437432980755741006239099211334161126220890546248813863926592209392221691128126111170209213367024993269845944615748004193504662806331001905776411977519278805416266944665934631010304⟩
def references : Fin 1 → Box := ![Part1014.root]
def proof : Enumeration.Proof 1 := (.split 29 0 (.split 44 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 73 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 29 (.split 24 0 (.step 55 (.run (.close 2))) (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 11)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.step 55 (.step 40 (.run (.close 3))))))) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 31))) (.step 18 (.step 68 (.run (.close 23))))) (.step 18 (.step 43 (.step 2 (.run (.close 23)))))) (.step 18 (.step 40 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.step 42 (.run (.close 2)))))) (.step 3 (.step 23 (.run (.close 18))))) (.step 3 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 29 (.run (.close 2)))))) (.step 3 (.step 23 (.run (.close 11))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 29 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1014.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1015
namespace Part1016
def root : Box := ⟨3273390607896141870015962366521719967076220460227207873186727805171509612979845034463884713633709782773926658533664210587314647756846796625158575489024, 5789234136395748269820054700174276076862240855547819268640844502262573671188218249932858052188650520661094065455245515404768103444169222692812527314511290394083340765232182529298126286608121654471082950825204088512578584576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 70 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 13 0 (.split 42 0 (.split 59 0 (.step 27 (.run (.close 2))) (.step 62 (.run (.close 27)))) (.step 62 (.run (.close 27)))) (.step 3 (.step 53 (.run (.close 5))))) (.split 14 0 (.split 16 0 (.step 9 (.run (.close 27))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55))))) (.step 53 (.split 6 0 (.split 13 0 (.split 22 0 (.step 53 (.step 55 (.run (.close 9)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 29 (.run (.close 53)))))) (.split 14 0 (.split 6 0 (.split 12 0 (.split 13 0 (.step 53 (.step 9 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 58))))) (.step 15 (.run (.close 9)))) (.step 29 (.step 53 (.run (.close 9))))) (.step 68 (.run (.close 27))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 9 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 68 (.run (.close 29))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 53 (.split 13 0 (.split 18 0 (.split 19 0 (.step 11 (.run (.close 9))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 71 (.run (.close 2)))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 9 0 (.step 52 (.split 18 0 (.split 19 0 (.split 23 0 (.step 68 (.step 63 (.step 55 (.step 68 (.run (.close 11)))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 3 (.step 62 (.step 3 (.run (.close 27))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1016
namespace Part1017
def root : Box := ⟨3273390607896141870015962366521719967076220460227207873186727805171509612979845034463884713633709782773926658533664210587314647756846796625158575489024, 5789234136395748269820054700174276076862240855547819272414806930598891425416645004991860152235245068319485369967449572535012509842743226858425096391426004527858979293844598983517290897156643178498806754169399805218394210304⟩
def references : Fin 1 → Box := ![Part1016.root]
def proof : Enumeration.Proof 1 := (.split 32 0 (.split 8 0 (.split 38 0 (.split 56 0 (.split 53 0 (.reuse 0) (.split 13 0 (.step 3 (.split 36 0 (.step 27 (.step 55 (.step 3 (.run (.close 27))))) (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 63))))) (.split 53 0 (.split 36 0 (.split 13 0 (.split 63 0 (.step 55 (.step 3 (.step 9 (.run (.close 5))))) (.step 71 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 18))))) (.step 4 (.run (.close 68))))) (.split 36 0 (.split 53 0 (.split 13 0 (.split 42 0 (.split 56 0 (.split 63 0 (.step 55 (.step 3 (.step 53 (.run (.close 4))))) (.step 71 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 71 (.step 68 (.step 58 (.run (.close 2))))))) (.split 38 0 (.split 56 0 (.split 26 0 (.split 13 0 (.split 35 0 (.split 39 0 (.split 36 0 (.step 27 (.split 6 0 (.step 63 (.step 9 (.run (.close 67)))) (.step 4 (.run (.close 9))))) (.step 55 (.run (.close 68)))) (.step 42 (.run (.close 27)))) (.step 55 (.step 24 (.run (.close 11))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 55 (.run (.close 27)))) (.step 68 (.step 4 (.run (.close 55))))) (.step 68 (.step 4 (.run (.close 55)))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 6 0 (.split 12 0 (.step 27 (.split 16 0 (.split 17 0 (.split 53 0 (.step 53 (.step 3 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 31))))) (.step 3 (.run (.close 53)))) (.step 3 (.step 53 (.run (.close 2))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1016.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1017
namespace Part1018
def root : Box := ⟨3273390607896141870015962366521719967076220460227207873186727805171509612979845034463884713633709782773926658533664210587314647756846796625158575489024, 5789234136395748269820054700174276076862240855547819272414806930598891425416645004991860152235245068319485369967449572535012509842743226858426993529016068716404799080862981326199558872585405033500029228406377074651826225152⟩
def references : Fin 1 → Box := ![Part1017.root]
def proof : Enumeration.Proof 1 := (.split 7 0 (.split 27 0 (.reuse 0) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 6 0 (.split 12 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 18 0 (.split 19 0 (.split 39 0 (.split 23 0 (.step 63 (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 27)))) (.step 4 (.run (.close 27)))) (.step 5 (.run (.close 27)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 3 (.step 71 (.run (.close 5)))))) (.step 3 (.step 53 (.step 5 (.run (.close 9)))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 16 0 (.split 9 0 (.step 5 (.step 71 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 4 (.run (.close 7)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 5 (.run (.close 9)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 9)))) (.step 4 (.step 5 (.run (.close 23))))) (.step 4 (.step 5 (.run (.close 23))))) (.step 5 (.step 3 (.step 63 (.run (.close 4)))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1017.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1018
namespace Part1019
def root : Box := ⟨3273390607896141870015962366521719967076220460227207873186727805171509612979845034463884713633709782773926658533664210587314647756846796625158575489024, 5789234136395748269820059484240009140673214437432980755741006239099211337434513703986578099912932505760583260026733063978187693692806166493522815664313273100992105038822754680318684576096628438397882993587014780807442071552⟩
def references : Fin 1 → Box := ![Part1018.root]
def proof : Enumeration.Proof 1 := (.split 57 0 (.split 66 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 55 (.split 26 0 (.split 30 0 (.split 36 0 (.split 35 0 (.split 39 0 (.split 42 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 71 (.step 68 (.run (.close 55)))))) (.step 71 (.step 68 (.step 71 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 29))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 68 (.step 55 (.run (.close 68))))) (.step 63 (.step 68 (.step 71 (.step 55 (.run (.close 68))))))) (.step 55 (.run (.close 11)))) (.step 55 (.run (.close 11))))) (.split 36 0 (.split 38 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 42 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 55)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 31)))) (.step 4 (.run (.close 31)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.run (.close 55)))) (.step 63 (.run (.close 55)))) (.step 63 (.step 58 (.run (.close 2))))) (.step 4 (.step 71 (.step 63 (.step 68 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1018.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1019
namespace Part1020
def root : Box := ⟨3273390607896141870015962366521719967076220460227207873186727805171509612979845034463884713633709782773926658533664210587314647756846796625158575489024, 5789234136395748269820059484240009140673214437432980755741006239099211337434516828783710984573125050816404097912927783033945732360217915161377909420204181557789588743662246945231222488796237268269433612898607818397714481152⟩
def references : Fin 1 → Box := ![Part1019.root]
def proof : Enumeration.Proof 1 := (.split 47 0 (.split 48 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 6 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 24 0 (.split 26 0 (.step 32 (.run (.close 2))) (.step 71 (.step 63 (.run (.close 55))))) (.step 55 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 71 (.step 68 (.step 55 (.run (.close 3)))))) (.step 3 (.step 55 (.run (.close 9))))) (.step 63 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.step 71 (.step 55 (.run (.close 68))))))) (.step 55 (.run (.close 3)))) (.step 55 (.step 63 (.run (.close 11))))) (.step 55 (.step 63 (.run (.close 11)))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 27 0 (.split 32 0 (.split 74 0 (.split 6 0 (.split 12 0 (.split 24 0 (.step 32 (.split 26 0 (.step 18 (.run (.close 2))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.run (.close 31)))) (.step 4 (.step 71 (.step 68 (.run (.close 55)))))) (.step 63 (.step 71 (.step 68 (.step 4 (.run (.close 55))))))) (.step 63 (.run (.close 55)))) (.step 63 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1019.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1020
namespace Part1021
def root : Box := ⟨3273390607896141870015962366521719967076220460227207873186727805171509612979845034463884713633709782773926658533664210587314647756846796625158575489024, 5789234136395748269820059484240009140673214437432980755741006239099211337434516828786688118827053623419808544438333174169175959692504735121127066250619170631274285830566963481888589903972048528497299902191623099538057723904⟩
def references : Fin 1 → Box := ![Part1020.root]
def proof : Enumeration.Proof 1 := (.split 44 0 (.split 46 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 55))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 31)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 63 (.step 2 (.run (.close 4)))))) (.step 63 (.step 4 (.step 58 (.run (.close 2)))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 6 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 39 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 58 (.step 55 (.run (.close 3))))) (.step 3 (.step 29 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 71 (.step 68 (.step 58 (.run (.close 27)))))) (.step 58 (.step 55 (.run (.close 3))))) (.step 55 (.step 63 (.run (.close 11))))) (.step 55 (.step 63 (.run (.close 11))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1020.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1021
namespace Part1022
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395748269820059484240009140673214437432980755741006239099211337434516828786688118827053623419808544438333174169175959692504735121127066250619170631274285830566963481888589903972048528497299902191623099538057723904⟩
def references : Fin 3 → Box := ![Part1010.root, Part1015.root, Part1021.root]
def proof : Enumeration.Proof 3 := (.split 50 0 (.split 30 0 (.reuse 0) (.split 9 0 (.reuse 1) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 73 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.split 18 0 (.split 19 0 (.step 18 (.run (.close 2))) (.step 32 (.run (.close 2)))) (.step 32 (.run (.close 2))))) (.step 18 (.step 43 (.run (.close 2))))) (.step 18 (.step 43 (.step 2 (.run (.close 23)))))) (.step 18 (.step 40 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.step 11 (.run (.close 2)))))) (.step 3 (.step 23 (.run (.close 18))))) (.step 3 (.run (.close 2)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 29 (.run (.close 2)))))) (.step 3 (.step 23 (.step 18 (.run (.close 31)))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 29 (.run (.close 2)))))))) (.reuse 2))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1010.covered
  · exact Part1015.covered
  · exact Part1021.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1022
namespace Part1023
def root : Box := ⟨3196670515523576047707425257429017156664978682232014161916213802032197235721919575617814757342641401507637183572459959942329938056994775983689039872, 5789234136395748269820054700174276076862240855547819268640844505777350073178287094519114837363258603466353141425704449512822325005647109319068806661813266407751266363144909740203986985286324984006996963976305737194534862848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 53 0 (.split 70 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 59 0 (.split 72 0 (.split 13 0 (.split 73 0 (.step 27 (.run (.close 18))) (.step 3 (.run (.close 5)))) (.step 3 (.run (.close 52)))) (.step 62 (.step 52 (.run (.close 9))))) (.step 62 (.step 52 (.run (.close 9))))) (.split 16 0 (.step 9 (.run (.close 27))) (.step 68 (.run (.close 55))))) (.step 53 (.step 9 (.run (.close 27))))) (.split 12 0 (.split 59 0 (.split 22 0 (.step 9 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 62 (.run (.close 9)))) (.step 15 (.run (.close 9))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 9 0 (.step 9 (.run (.close 11))) (.step 55 (.run (.close 9)))) (.step 55 (.run (.close 9)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 55 (.run (.close 52))))) (.step 53 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 11 (.run (.close 9))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 71 (.run (.close 2)))))) (.step 52 (.split 31 0 (.split 33 0 (.split 41 0 (.step 29 (.split 64 0 (.step 3 (.run (.close 52))) (.step 68 (.run (.close 55))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))))) (.step 62 (.step 4 (.step 62 (.step 3 (.step 27 (.run (.close 4)))))))) (.split 73 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 26 0 (.split 35 0 (.split 36 0 (.step 3 (.step 61 (.step 4 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1023
namespace Part1024
def root : Box := ⟨3196670515523576047707425257429017156664978682232014161916213802032197235721919575617814757342641401507637183572459959942329938056994775983689039872, 5789234136395748269820054700174276076862240855547819272414806930598891425419841675507383728280179823882793572264536137033101438165235967664171394656955738353310058140677092405332183727583355738124018491698621371780773707776⟩
def references : Fin 1 → Box := ![Part1023.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 38 0 (.split 56 0 (.reuse 0) (.split 36 0 (.split 53 0 (.split 13 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 3 (.step 9 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 18)))))) (.split 36 0 (.split 42 0 (.split 53 0 (.split 70 0 (.split 13 0 (.split 56 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 3 (.step 9 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 18))))) (.step 71 (.step 68 (.step 58 (.run (.close 18))))))) (.split 38 0 (.split 56 0 (.split 26 0 (.split 35 0 (.split 13 0 (.split 18 0 (.step 27 (.split 6 0 (.step 63 (.step 52 (.step 24 (.run (.close 2))))) (.step 15 (.run (.close 9))))) (.step 55 (.run (.close 27)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 11))))) (.step 55 (.step 68 (.run (.close 11))))) (.step 68 (.step 4 (.run (.close 55))))) (.step 68 (.step 4 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1023.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1024
namespace Part1025
def root : Box := ⟨3196670515523576047707425257429017156664978682232014161916213802032197235721919575617814757342641401507637183572459959942329938056994775983689039872, 5789234136395748269820054700174276076862240855547819272414806930598891425419841675507383728280179823882793572264536137033101440301223003585083374189567508711407992530399997104667221650053725415344967954321376658088056061952⟩
def references : Fin 1 → Box := ![Part1024.root]
def proof : Enumeration.Proof 1 := (.split 27 0 (.split 32 0 (.split 8 0 (.reuse 0) (.split 38 0 (.split 56 0 (.split 26 0 (.split 35 0 (.split 13 0 (.split 39 0 (.split 58 0 (.split 36 0 (.step 27 (.split 6 0 (.split 9 0 (.step 63 (.step 9 (.run (.close 68)))) (.step 55 (.step 3 (.run (.close 52))))) (.step 5 (.run (.close 9))))) (.step 55 (.run (.close 68)))) (.step 61 (.run (.close 27)))) (.step 42 (.run (.close 27)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 11))))) (.step 55 (.step 43 (.run (.close 11))))) (.step 68 (.step 4 (.run (.close 55))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 6 0 (.split 12 0 (.step 27 (.split 16 0 (.split 17 0 (.split 53 0 (.step 53 (.step 3 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 48)))) (.step 71 (.run (.close 2))))) (.step 4 (.step 3 (.step 53 (.step 71 (.run (.close 5))))))) (.step 53 (.step 3 (.run (.close 27))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 6 0 (.split 12 0 (.split 24 0 (.split 18 0 (.split 64 0 (.split 19 0 (.split 36 0 (.step 27 (.run (.close 4))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.run (.close 3)))) (.step 71 (.run (.close 27)))) (.step 4 (.run (.close 3)))) (.step 27 (.run (.close 2)))) (.step 4 (.step 52 (.step 9 (.run (.close 5)))))) (.step 4 (.step 52 (.step 9 (.run (.close 5)))))) (.step 4 (.run (.close 63)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1024.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1025
namespace Part1026
def root : Box := ⟨3196670515523576047707425257429017156664978682232014161916213802032197235721919575617814757342641401507637183572459959942329938056994775983689039872, 5789234136395748269820059484240009140673214437432976891203483221840866642085819442514757377030537554888892805088568176957134334590861407026412614402286750632379266986182593093707686310577293077334148253601857287980268388352⟩
def references : Fin 1 → Box := ![Part1025.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.split 7 0 (.reuse 0) (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 6 0 (.split 12 0 (.split 39 0 (.split 18 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 16 0 (.split 9 0 (.split 19 0 (.split 41 0 (.step 71 (.run (.close 10))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 9)))) (.step 3 (.run (.close 2)))) (.step 4 (.run (.close 7)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 5 (.run (.close 9)))) (.step 5 (.step 63 (.run (.close 4))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 4 (.step 5 (.run (.close 23))))) (.step 5 (.run (.close 3)))) (.step 5 (.step 3 (.step 63 (.run (.close 4)))))) (.step 63 (.step 4 (.step 2 (.run (.close 5)))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 22 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 55 (.split 50 0 (.step 2 (.run (.close 23))) (.step 55 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.step 71 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.step 63 (.run (.close 3)))))) (.step 71 (.step 68 (.step 71 (.step 55 (.run (.close 40))))))) (.step 55 (.run (.close 29)))) (.step 63 (.step 55 (.run (.close 68))))) (.step 68 (.step 55 (.run (.close 68))))) (.step 58 (.step 55 (.run (.close 68))))) (.step 55 (.step 68 (.run (.close 11))))) (.step 55 (.step 63 (.run (.close 11))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1025.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1026
namespace Part1027
def root : Box := ⟨3196670515523576047707425257429017156664978682232014161916213802032197235721919575617814757342641401507637183572459959942329938056994775983689039872, 5789234136395748269820059484240009140673214437432980755741006239099211337437713496250651991950098642921121255490125377074419289122436802377138821696603532861615418794462833950757507180496070226865717168658285273246389501952⟩
def references : Fin 1 → Box := ![Part1026.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.split 57 0 (.reuse 0) (.split 36 0 (.split 38 0 (.split 8 0 (.split 14 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 26 0 (.split 35 0 (.step 55 (.split 50 0 (.step 2 (.run (.close 4))) (.step 55 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 18)))) (.step 4 (.run (.close 55)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 4 (.step 71 (.step 68 (.step 2 (.run (.close 48))))))) (.step 71 (.step 63 (.run (.close 62))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 4 (.step 71 (.step 63 (.step 58 (.run (.close 2)))))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 7 0 (.split 22 0 (.split 30 0 (.split 74 0 (.split 6 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 29 0 (.split 35 0 (.step 12 (.step 2 (.run (.close 23)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 32 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 55))))) (.step 55 (.step 2 (.run (.close 23))))) (.step 3 (.step 55 (.run (.close 9))))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 3 (.step 55 (.run (.close 9))))) (.step 63 (.run (.close 55)))) (.step 71 (.step 18 (.run (.close 2))))) (.step 68 (.step 71 (.step 55 (.run (.close 68)))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 63 (.step 68 (.step 71 (.step 55 (.run (.close 68))))))) (.step 58 (.step 55 (.run (.close 11))))) (.step 55 (.step 63 (.run (.close 11))))) (.step 55 (.step 63 (.run (.close 11))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1026.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1027
namespace Part1028
def root : Box := ⟨3196670515523576047707425257429017156664978682232014161916213802032197235721919575617814757342641401507637183572459959942329938056994775983689039872, 5789234136395748269820059484240009140673214437432980755741006239099211337437713499302211692032774612203402330527123614104747177832072946662947273936599520076905260087143341267422460830801440938613638604809956750822161252352⟩
def references : Fin 1 → Box := ![Part1027.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 36 0 (.split 38 0 (.split 16 0 (.split 17 0 (.split 7 0 (.split 22 0 (.split 30 0 (.split 42 0 (.split 32 0 (.split 74 0 (.split 6 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 39 0 (.step 18 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 31)))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 31)))) (.step 63 (.step 58 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 58 (.run (.close 31)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.step 58 (.step 2 (.run (.close 4))))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 8 0 (.split 14 0 (.split 36 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 42 0 (.split 50 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 55 (.step 2 (.run (.close 4))))) (.step 55 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 31)))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 58 (.run (.close 31)))) (.step 71 (.step 63 (.step 58 (.step 2 (.run (.close 4))))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1027.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1028
namespace Part1029
def root : Box := ⟨5136851466355833503165029182500125649951503713694505722166289944403058744430745763015071597648442050315534698607314977172445915123395291439666371233272533018157438090742475817499644029769870307157077364047872, 5789234131009374243485986584588438705696133760256265754490267127221078447768582614700875297345512806368904334415312755008776969024698626274426113251064102292849414155334111258378814466209119443479990163843776230392147738624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 72 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 2 (.run (.close 58))))) (.split 72 0 (.split 12 0 (.split 74 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 31)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 72 0 (.split 57 0 (.split 74 0 (.split 6 0 (.split 53 0 (.split 22 0 (.split 30 0 (.step 4 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 6 0 (.step 5 (.split 7 0 (.split 13 0 (.step 31 (.run (.close 2))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 2))))) (.step 4 (.run (.close 5))))) (.split 72 0 (.split 57 0 (.split 38 0 (.split 56 0 (.split 14 0 (.split 74 0 (.split 53 0 (.split 6 0 (.split 9 0 (.split 36 0 (.split 7 0 (.split 17 0 (.split 12 0 (.step 35 (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 68 (.run (.close 23)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 27)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1029
namespace Part1030
def root : Box := ⟨5136851466355833503165029182500125649951503713694505722166289944403058744430745763015071597648442050315534698607314977172445915123395291439666371233272533018157438090742475817499644029769870307157077364047872, 5789234131009374243485986584588438705696133760256265754490267127221078447768582617752434997428188775651185409452310994332603473724406282171055462645820458101763371393431502451639133155757120893961745510261164559332854988800⟩
def references : Fin 1 → Box := ![Part1029.root]
def proof : Enumeration.Proof 1 := (.split 26 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 8 0 (.reuse 0) (.split 6 0 (.step 5 (.split 7 0 (.step 31 (.split 13 0 (.split 18 0 (.split 19 0 (.step 5 (.run (.close 27))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 5))))) (.step 2 (.run (.close 27))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.split 36 0 (.split 12 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.run (.close 2))))) (.split 16 0 (.split 8 0 (.split 12 0 (.split 54 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 48))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 48)))) (.step 63 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 31 0 (.step 18 (.split 33 0 (.step 4 (.split 7 0 (.step 9 (.step 68 (.run (.close 9)))) (.step 4 (.run (.close 9))))) (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 55)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 31 0 (.step 18 (.split 33 0 (.step 4 (.split 7 0 (.step 9 (.step 5 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 71))))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1029.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1030
namespace Part1031
def root : Box := ⟨5136851466355833503165029182500125649951503713694505722166289944403058744430745763015071597648442050315534698607314977172445915123395291439666371233272533018157438090742475817499644029769870307157077364047872, 5789234136395753406671525840073507850193981290883612502975573741914186537684190670690598600540840314972743893719279507176680234351955226546146512421693271052603547277566500141234847299017204238698832535796940732477342744576⟩
def references : Fin 1 → Box := ![Part1030.root]
def proof : Enumeration.Proof 1 := (.split 64 0 (.split 66 0 (.split 71 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 36 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 42 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 2 (.run (.close 4)))))) (.split 8 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.run (.close 68))))) (.split 35 0 (.split 36 0 (.split 8 0 (.split 14 0 (.split 42 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1030.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1031
namespace Part1032
def root : Box := ⟨5136851466355833503165029182500125649951503713694505722166289944403058744430745763015071597648442050315534698607314977172445915123395291439666371233272533018157438090742475817499644029769870307157077364047872, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956122775764957580879164109595515455302701443613682033486580756720480162661872051870733801820577167173118860160277163718860336069477400576⟩
def references : Fin 1 → Box := ![Part1031.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.split 63 0 (.reuse 0) (.split 35 0 (.split 36 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 49 0 (.split 50 0 (.split 56 0 (.split 7 0 (.split 13 0 (.step 31 (.split 64 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2))))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2)))))) (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 39 0 (.split 54 0 (.split 58 0 (.split 72 0 (.split 74 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 57)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1031.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1032
namespace Part1033
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317891640017820413762525247218322753731291570712034091244831371794754369017812046831888877188196117888939015012352⟩
def references : Fin 3 → Box := ![Part1022.root, Part1028.root, Part1032.root]
def proof : Enumeration.Proof 3 := (.split 69 0 (.split 49 0 (.reuse 0) (.split 44 0 (.reuse 1) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 74 0 (.split 6 0 (.split 36 0 (.split 42 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 63 0 (.step 2 (.run (.close 23))) (.step 63 (.run (.close 12)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 23))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 55 (.step 63 (.run (.close 3))))) (.step 55 (.step 48 (.run (.close 3))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 58 (.step 18 (.run (.close 2))))) (.step 58 (.step 55 (.run (.close 68))))) (.step 58 (.step 55 (.run (.close 3))))) (.step 58 (.step 68 (.run (.close 27))))) (.step 55 (.step 11 (.run (.close 2))))) (.step 55 (.step 11 (.run (.close 2))))))) (.split 44 0 (.reuse 2) (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 24 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 39 0 (.split 54 0 (.split 58 0 (.split 72 0 (.split 74 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 2 (.step 4 (.run (.close 68)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1022.covered
  · exact Part1028.covered
  · exact Part1032.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1033
namespace Part1034
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671521056007779241891423355673469220144558200283072239468231497577859268106248948843829975008176350863377848617187842700315165990114230074919758963453181733770975872381494707199523555369658049150712807424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 18 0 (.split 36 0 (.split 73 0 (.split 42 0 (.split 35 0 (.split 14 0 (.step 31 (.step 27 (.split 63 0 (.split 64 0 (.step 27 (.step 18 (.step 2 (.run (.close 23))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))))) (.step 63 (.run (.close 11)))) (.split 16 0 (.split 17 0 (.step 68 (.step 31 (.run (.close 68)))) (.step 68 (.run (.close 4)))) (.step 68 (.run (.close 24))))) (.split 16 0 (.split 17 0 (.split 19 0 (.step 62 (.step 24 (.step 71 (.step 68 (.run (.close 43)))))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 24)))) (.step 68 (.run (.close 24))))) (.split 53 0 (.step 62 (.step 3 (.step 63 (.step 58 (.run (.close 5)))))) (.step 63 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.step 68 (.step 18 (.step 43 (.run (.close 2))))) (.step 68 (.run (.close 4)))) (.step 68 (.step 71 (.run (.close 24))))) (.step 43 (.step 68 (.run (.close 4))))) (.step 43 (.step 23 (.step 24 (.run (.close 5))))))) (.split 35 0 (.split 63 0 (.split 31 0 (.split 64 0 (.split 71 0 (.split 14 0 (.step 31 (.split 16 0 (.step 9 (.split 17 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 23))))) (.step 68 (.step 24 (.run (.close 2)))))) (.step 68 (.step 63 (.run (.close 24))))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 43 (.step 24 (.run (.close 2))))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 29)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1034
namespace Part1035
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013602055026618461039153860105339523073085759674266022120491103941474503048771181528895130632771561599631062430505918286445219016539085889077248⟩
def references : Fin 1 → Box := ![Part1034.root]
def proof : Enumeration.Proof 1 := (.split 56 0 (.split 47 0 (.split 57 0 (.reuse 0) (.split 18 0 (.split 19 0 (.split 23 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 49 0 (.step 68 (.step 71 (.run (.close 55)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 3)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 63 (.run (.close 3)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 18))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 57 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 49 0 (.step 68 (.step 71 (.run (.close 55)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 3)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 63 (.run (.close 3)))) (.step 58 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 18))))) (.split 24 0 (.split 35 0 (.split 14 0 (.split 39 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 49 0 (.split 58 0 (.split 74 0 (.split 50 0 (.step 58 (.step 40 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 4))))) (.step 71 (.run (.close 4)))) (.step 71 (.run (.close 5)))) (.step 63 (.step 58 (.run (.close 4))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 55 (.run (.close 2))))) (.step 4 (.step 68 (.step 55 (.run (.close 2)))))) (.step 58 (.run (.close 27)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 58 (.run (.close 27)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1034.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1035
namespace Part1036
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550135656632339658472189279397375266016927183020375092353133566210471454291700847920397672662362257229022201027049291776⟩
def references : Fin 1 → Box := ![Part1035.root]
def proof : Enumeration.Proof 1 := (.split 12 0 (.split 46 0 (.split 26 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 53 0 (.split 70 0 (.split 18 0 (.split 47 0 (.split 57 0 (.split 16 0 (.step 15 (.step 7 (.run (.close 29)))) (.step 68 (.run (.close 43)))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68)))) (.step 71 (.step 18 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 68 (.step 43 (.run (.close 31)))))) (.step 68 (.step 4 (.step 43 (.run (.close 31)))))) (.step 68 (.step 4 (.step 43 (.run (.close 31))))))) (.split 18 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 39 0 (.split 47 0 (.split 19 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 36 0 (.step 71 (.step 63 (.run (.close 2)))) (.step 55 (.run (.close 4)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.run (.close 64)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 31)))) (.step 71 (.step 68 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 58 (.run (.close 31)))) (.step 55 (.step 71 (.run (.close 2)))))) (.split 53 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 18 (.split 16 0 (.split 17 0 (.split 31 0 (.step 9 (.step 18 (.step 68 (.run (.close 15))))) (.step 18 (.run (.close 15)))) (.step 68 (.step 63 (.run (.close 24))))) (.step 68 (.step 63 (.run (.close 24)))))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5)))) (.step 71 (.step 58 (.run (.close 5))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 63 (.step 58 (.run (.close 5)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1035.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1036
namespace Part1037
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550138119257726933127142182824417445902872395525785665995664915683331576302081513537668708273728968176799774403385622528⟩
def references : Fin 1 → Box := ![Part1036.root]
def proof : Enumeration.Proof 1 := (.split 32 0 (.split 38 0 (.reuse 0) (.split 14 0 (.split 24 0 (.split 12 0 (.split 39 0 (.split 18 0 (.split 19 0 (.split 35 0 (.split 46 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 58 0 (.step 58 (.step 23 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.run (.close 58)))) (.step 71 (.run (.close 33)))) (.step 58 (.run (.close 68)))) (.step 55 (.run (.close 18)))) (.step 58 (.run (.close 2)))) (.step 71 (.run (.close 48)))) (.step 68 (.step 55 (.run (.close 18))))) (.step 55 (.step 71 (.step 2 (.run (.close 4)))))) (.step 58 (.run (.close 42)))) (.step 68 (.step 58 (.run (.close 5))))) (.step 58 (.step 68 (.run (.close 3))))) (.step 68 (.step 63 (.run (.close 13)))))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 46 0 (.split 47 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 24 0 (.split 38 0 (.split 31 0 (.split 33 0 (.split 57 0 (.split 39 0 (.step 4 (.step 31 (.step 23 (.run (.close 31))))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 3 (.run (.close 31)))) (.step 31 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 68 (.run (.close 31)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 8))))) (.step 68 (.step 63 (.run (.close 8))))) (.step 71 (.run (.close 63)))) (.step 71 (.run (.close 63)))) (.step 71 (.run (.close 63)))) (.step 40 (.step 23 (.run (.close 2))))) (.step 40 (.step 23 (.run (.close 2))))) (.step 71 (.step 4 (.step 63 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1036.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1037
namespace Part1038
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550138119257726933127142182824417445902872395525785665995664915683331576302081514898798175957482822031451125635065315328⟩
def references : Fin 1 → Box := ![Part1037.root]
def proof : Enumeration.Proof 1 := (.split 13 0 (.split 6 0 (.reuse 0) (.split 32 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 16 0 (.split 70 0 (.split 57 0 (.split 69 0 (.split 17 0 (.split 12 0 (.split 31 0 (.step 9 (.step 18 (.step 68 (.run (.close 9))))) (.step 18 (.run (.close 15)))) (.step 15 (.run (.close 2)))) (.step 68 (.step 24 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 46))))) (.step 71 (.run (.close 3)))) (.step 71 (.run (.close 27)))) (.step 68 (.step 24 (.run (.close 2))))) (.step 71 (.step 48 (.run (.close 3))))) (.step 58 (.run (.close 18)))) (.step 58 (.run (.close 18)))) (.step 71 (.step 48 (.run (.close 3)))))) (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 26 0 (.split 35 0 (.split 63 0 (.split 41 0 (.split 46 0 (.split 64 0 (.split 53 0 (.split 57 0 (.split 38 0 (.split 56 0 (.split 74 0 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 2))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.step 4 (.step 63 (.run (.close 2)))))) (.step 63 (.run (.close 4)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.step 71 (.run (.close 16))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 48)))) (.step 58 (.run (.close 2)))) (.step 4 (.step 40 (.step 24 (.run (.close 2)))))) (.step 71 (.run (.close 18)))) (.step 4 (.step 68 (.run (.close 18))))) (.step 71 (.run (.close 18)))) (.step 4 (.step 40 (.step 24 (.run (.close 2)))))) (.step 4 (.step 40 (.step 24 (.run (.close 2)))))) (.step 63 (.step 4 (.step 2 (.run (.close 5)))))) (.step 63 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1037.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1038
namespace Part1039
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550138119257726933127142182824417445902872395525785665995664915683331576302081514898798175957484032137862360981651324928⟩
def references : Fin 1 → Box := ![Part1038.root]
def proof : Enumeration.Proof 1 := (.split 7 0 (.split 8 0 (.reuse 0) (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 32 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 14 0 (.split 16 0 (.split 57 0 (.split 70 0 (.split 36 0 (.split 42 0 (.split 17 0 (.step 27 (.step 68 (.run (.close 24)))) (.step 24 (.run (.close 11)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 11)))) (.step 24 (.run (.close 11)))) (.step 11 (.run (.close 68)))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 7)))) (.step 63 (.run (.close 4)))) (.step 63 (.run (.close 4)))) (.step 63 (.step 4 (.run (.close 68))))) (.step 68 (.step 63 (.run (.close 7))))) (.step 23 (.step 24 (.run (.close 3))))) (.step 23 (.step 63 (.step 24 (.run (.close 40)))))) (.step 23 (.step 24 (.run (.close 3))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 14 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 46 0 (.split 18 0 (.step 7 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 5))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 18)))) (.step 71 (.run (.close 18)))) (.step 71 (.run (.close 18)))) (.step 40 (.step 4 (.step 24 (.run (.close 2)))))) (.step 40 (.step 4 (.step 24 (.run (.close 2)))))) (.step 40 (.step 4 (.step 24 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1038.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1039
namespace Part1040
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671525840073512305702396937558630707244719933604933503727654780612405806783533575983649370943289766857160036472462820887234009745835091775512759158484309908024814150851127692947886803294137018872473059328⟩
def references : Fin 1 → Box := ![Part1039.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.split 27 0 (.reuse 0) (.split 6 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 31 0 (.split 33 0 (.step 7 (.step 4 (.run (.close 2)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 40 (.step 4 (.step 23 (.run (.close 2)))))) (.step 40 (.step 4 (.step 23 (.run (.close 2)))))) (.step 40 (.step 4 (.step 23 (.run (.close 2)))))) (.step 71 (.step 48 (.run (.close 46)))))) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 18 (.split 46 0 (.step 55 (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 68))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 43 (.run (.close 11))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 55 (.step 43 (.run (.close 31))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 71 (.step 68 (.run (.close 43)))))) (.step 68 (.step 71 (.step 55 (.run (.close 3)))))) (.step 58 (.step 55 (.step 68 (.run (.close 11)))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 48 (.step 40 (.step 24 (.run (.close 15)))))) (.step 43 (.step 18 (.run (.close 11))))) (.step 63 (.step 58 (.step 68 (.step 2 (.run (.close 4))))))) (.step 68 (.step 48 (.step 40 (.step 18 (.run (.close 29))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1039.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1040
namespace Part1041
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956122775764957580879164109595515455302701443613680044193635117573911541132879464587373399995973977782249099570782251269816307157779349504⟩
def references : Fin 1 → Box := ![Part1040.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 39 0 (.split 46 0 (.split 47 0 (.step 68 (.step 55 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 48)))) (.step 71 (.run (.close 68)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 43 (.run (.close 11))))) (.step 43 (.step 18 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 55 (.step 43 (.run (.close 31))))) (.step 55 (.step 43 (.step 2 (.run (.close 55)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 71 (.step 68 (.run (.close 3)))))) (.step 68 (.step 71 (.step 55 (.run (.close 3)))))) (.step 55 (.step 43 (.run (.close 11))))) (.step 63 (.step 58 (.step 68 (.run (.close 2)))))) (.step 48 (.step 40 (.step 18 (.run (.close 29)))))) (.step 55 (.step 43 (.step 18 (.run (.close 11)))))) (.step 63 (.step 58 (.step 68 (.step 2 (.run (.close 4))))))) (.step 68 (.step 48 (.step 40 (.step 18 (.run (.close 29))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1040.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1041
namespace Part1042
def root : Box := ⟨2772669694120814859578414184143083703436439064668762214317048202143613895088986024864577595495009341220949383827621023460253237248, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317891640017820413762525247218322753731291570712034091244831371794754369017812046833155289847203317367938800943104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 53 0 (.split 57 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.step 31 (.step 2 (.run (.close 23))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 42 (.step 2 (.run (.close 55))))) (.step 68 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 11 (.step 68 (.run (.close 2)))))) (.step 31 (.step 11 (.step 18 (.run (.close 2)))))) (.step 18 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 3 (.step 11 (.step 2 (.run (.close 40))))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 18 (.step 3 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 18 (.step 3 (.step 40 (.run (.close 31)))))) (.step 18 (.step 3 (.step 11 (.step 2 (.run (.close 40))))))) (.step 3 (.step 31 (.step 23 (.run (.close 18)))))) (.step 3 (.step 31 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 3 (.step 31 (.split 16 0 (.step 29 (.run (.close 12))) (.step 68 (.run (.close 18))))))) (.step 3 (.step 31 (.step 23 (.run (.close 11))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1042
namespace Part1043
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189632973326751105024, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317891640017820413762525247218322753731291570712034091244831371794754369017812046833155289848385061910160819093504⟩
def references : Fin 2 → Box := ![Part1041.root, Part1042.root]
def proof : Enumeration.Proof 2 := (.split 29 0 (.split 44 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 49 0 (.split 50 0 (.split 58 0 (.step 18 (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68)))) (.step 68 (.step 71 (.run (.close 68))))) (.step 68 (.step 55 (.run (.close 8))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 43 (.step 18 (.run (.close 2))))) (.step 43 (.step 18 (.run (.close 2))))) (.step 55 (.step 43 (.run (.close 31))))) (.step 55 (.step 43 (.step 2 (.run (.close 55)))))) (.step 55 (.step 23 (.step 2 (.run (.close 55)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 24 (.run (.close 29))))) (.step 68 (.step 71 (.step 55 (.run (.close 3)))))) (.step 55 (.step 43 (.run (.close 11))))) (.step 63 (.step 58 (.step 68 (.run (.close 2)))))) (.step 48 (.step 40 (.step 18 (.run (.close 29)))))) (.step 55 (.step 63 (.step 43 (.run (.close 11)))))) (.step 63 (.step 58 (.step 68 (.step 2 (.run (.close 4))))))) (.step 68 (.step 48 (.step 40 (.step 18 (.run (.close 29)))))))) (.split 6 0 (.split 7 0 (.reuse 1) (.step 3 (.step 31 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 3 (.step 31 (.split 12 0 (.split 16 0 (.step 29 (.run (.close 2))) (.step 68 (.run (.close 18)))) (.step 29 (.run (.close 15))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1041.covered
  · exact Part1042.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1043
namespace Part1044
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579366279751228918353601650229248, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317891640017820413762525247218322753731291570712034091244831371794754369017812046833156527787242602748213700067328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 47 0 (.split 56 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.step 12 (.run (.close 68))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 3 (.step 11 (.step 18 (.run (.close 2))))))) (.step 18 (.step 31 (.step 11 (.step 18 (.run (.close 2))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 2))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 18 (.run (.close 31)))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 18 (.step 3 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 18 (.step 3 (.step 40 (.run (.close 31)))))) (.step 18 (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 18)))) (.step 18 (.run (.close 31)))) (.step 18 (.run (.close 31))))))) (.step 3 (.step 31 (.step 23 (.run (.close 18)))))) (.step 3 (.step 31 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 3 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.run (.close 9))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 31))))))) (.step 3 (.step 31 (.step 23 (.run (.close 11))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1044
namespace Part1045
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671521056007779241891423355673473084682081217541416934820122432616763267116254624561109707280426039412848026887248523179890200152688179753825631756740058486127054485857215459027051545392870624568618778624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 46 0 (.split 73 0 (.split 14 0 (.split 47 0 (.split 57 0 (.split 23 0 (.split 35 0 (.split 36 0 (.step 11 (.step 27 (.split 63 0 (.split 10 0 (.step 11 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 63 (.run (.close 68)))))) (.split 54 0 (.step 11 (.step 24 (.step 68 (.run (.close 27))))) (.step 68 (.run (.close 43))))) (.split 54 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 36 0 (.step 24 (.run (.close 27))) (.step 4 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 71 (.step 68 (.run (.close 43)))))) (.split 53 0 (.split 35 0 (.split 63 0 (.step 27 (.step 18 (.run (.close 7)))) (.step 68 (.run (.close 23)))) (.step 43 (.run (.close 18)))) (.step 2 (.step 71 (.run (.close 5)))))) (.step 11 (.step 18 (.run (.close 7))))) (.step 11 (.split 23 0 (.split 31 0 (.step 33 (.step 71 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))))) (.step 11 (.run (.close 27)))) (.split 31 0 (.split 33 0 (.split 23 0 (.split 35 0 (.split 47 0 (.split 63 0 (.split 64 0 (.step 62 (.step 63 (.step 18 (.run (.close 7))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 29)))) (.step 2 (.run (.close 9)))) (.step 2 (.step 71 (.run (.close 63))))) (.step 2 (.step 71 (.run (.close 63)))))) (.split 23 0 (.split 54 0 (.split 31 0 (.step 11 (.step 13 (.step 55 (.run (.close 4))))) (.step 2 (.run (.close 55)))) (.step 58 (.run (.close 5)))) (.step 2 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1045
namespace Part1046
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550135656632339658472189279397375266016927183020375092353133566208938958750834959062039325635211948045403463004377317376⟩
def references : Fin 1 → Box := ![Part1045.root]
def proof : Enumeration.Proof 1 := (.split 12 0 (.split 56 0 (.split 26 0 (.split 19 0 (.reuse 0) (.split 46 0 (.split 47 0 (.split 57 0 (.split 53 0 (.split 31 0 (.split 64 0 (.split 33 0 (.split 14 0 (.step 9 (.step 43 (.run (.close 2)))) (.step 68 (.run (.close 31)))) (.step 2 (.step 43 (.run (.close 24))))) (.step 68 (.run (.close 3)))) (.step 2 (.step 43 (.run (.close 24))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55))))) (.split 31 0 (.split 33 0 (.split 41 0 (.split 19 0 (.step 7 (.step 71 (.run (.close 29)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27))))) (.split 14 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 39 0 (.split 19 0 (.split 23 0 (.split 49 0 (.split 50 0 (.split 54 0 (.step 8 (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 55)))) (.step 58 (.run (.close 23)))) (.step 58 (.run (.close 7)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 58 (.run (.close 27)))) (.step 4 (.run (.close 29)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 63 (.run (.close 7)))))) (.split 46 0 (.split 47 0 (.split 31 0 (.split 33 0 (.split 53 0 (.split 70 0 (.split 73 0 (.split 57 0 (.step 9 (.run (.close 24))) (.step 71 (.run (.close 24)))) (.step 71 (.run (.close 9)))) (.step 71 (.run (.close 27)))) (.step 4 (.step 71 (.step 4 (.run (.close 63)))))) (.step 24 (.step 18 (.run (.close 9))))) (.step 24 (.step 18 (.step 24 (.run (.close 3)))))) (.step 71 (.step 58 (.run (.close 24))))) (.step 71 (.step 58 (.run (.close 24))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1045.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1046
namespace Part1047
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550138119257726933127140046837381524992790000504079496443550312978809219649311566496060886054003187536249752540810313728⟩
def references : Fin 1 → Box := ![Part1046.root]
def proof : Enumeration.Proof 1 := (.split 38 0 (.split 18 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 14 0 (.split 63 0 (.split 53 0 (.split 64 0 (.split 31 0 (.split 71 0 (.split 10 0 (.split 16 0 (.step 9 (.run (.close 2))) (.step 68 (.step 24 (.run (.close 2))))) (.step 18 (.run (.close 7)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 18)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 68 (.step 63 (.step 24 (.step 55 (.run (.close 27))))))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 31)))) (.step 68 (.step 40 (.run (.close 29))))) (.step 2 (.run (.close 29))))) (.split 14 0 (.split 24 0 (.split 31 0 (.split 12 0 (.split 18 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 58 0 (.step 58 (.run (.close 28))) (.step 71 (.run (.close 23)))) (.step 4 (.run (.close 58)))) (.step 58 (.run (.close 5)))) (.step 58 (.run (.close 68)))) (.step 58 (.run (.close 42)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 58 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 63 (.run (.close 7))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1046.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1047
namespace Part1048
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550138119257726933127142182824417445902872395525785665995664915683331576302081513537668708273728968177952697007504097280⟩
def references : Fin 1 → Box := ![Part1047.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 32 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 46 0 (.split 47 0 (.split 14 0 (.split 74 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 10 0 (.split 16 0 (.step 71 (.step 4 (.run (.close 30)))) (.step 63 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 7)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 71 (.step 48 (.run (.close 3)))))) (.split 32 0 (.split 53 0 (.split 70 0 (.split 12 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 73 0 (.split 69 0 (.split 18 0 (.split 19 0 (.split 31 0 (.split 23 0 (.split 10 0 (.step 18 (.step 29 (.run (.close 24)))) (.step 15 (.step 18 (.run (.close 7))))) (.step 2 (.run (.close 9)))) (.step 2 (.step 43 (.run (.close 24))))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.split 31 0 (.split 33 0 (.step 29 (.run (.close 9))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1047.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1048
namespace Part1049
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550138119257726933127142182824417445902872395525785665995664915683331576302081514898798175957484030957270741363751649280⟩
def references : Fin 1 → Box := ![Part1048.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 13 0 (.reuse 0) (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 18 0 (.split 19 0 (.split 46 0 (.split 6 0 (.split 12 0 (.split 23 0 (.split 54 0 (.split 10 0 (.split 16 0 (.step 71 (.step 10 (.run (.close 5)))) (.step 63 (.step 55 (.run (.close 2))))) (.step 7 (.run (.close 2)))) (.step 71 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 71 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 63 (.step 71 (.run (.close 4))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 63 (.step 71 (.run (.close 2)))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 11 (.step 48 (.step 68 (.run (.close 27))))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1048.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1049
namespace Part1050
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671521056007779241891423355673473088456043642362958287061677013605032158033175844977550138119257726933127142182824417445904769533115849854541484702701713918984349490327560030958706505194248010797183664128⟩
def references : Fin 1 → Box := ![Part1049.root]
def proof : Enumeration.Proof 1 := (.split 27 0 (.split 7 0 (.reuse 0) (.split 41 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 26 0 (.split 35 0 (.step 10 (.run (.close 7))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 71 (.step 63 (.step 71 (.step 4 (.run (.close 2))))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 5))))) (.step 2 (.run (.close 7)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 23)))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 31 0 (.split 33 0 (.step 7 (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 63))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))) (.step 2 (.step 71 (.run (.close 5))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1049.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1050
namespace Part1051
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956122775764957580879164109595515455302701443613680044193635117573911541132879464587373399995973977782249099570782251269816308257290977280⟩
def references : Fin 1 → Box := ![Part1050.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.split 66 0 (.reuse 0) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 26 0 (.split 32 0 (.split 35 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 11 (.step 55 (.run (.close 3)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 55 (.step 71 (.run (.close 29))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 29)))) (.step 58 (.step 55 (.run (.close 11))))) (.step 2 (.run (.close 48)))) (.step 68 (.step 40 (.step 24 (.run (.close 9)))))) (.step 2 (.run (.close 11)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 29))))) (.split 6 0 (.split 7 0 (.split 12 0 (.split 13 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 11 (.step 68 (.step 55 (.run (.close 3))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 48)))) (.step 55 (.step 71 (.run (.close 29))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 48)))) (.step 68 (.step 48 (.step 40 (.run (.close 29)))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 29)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1050.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1051
namespace Part1052
def root : Box := ⟨2772669694120814859578414184143083703436439064668762214317048202143613895088986024864577595495009339953298783599391623063061659648, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317891640017820413762525247218322753731291570712034091244831371794754369017812046833155289848385061911260330721280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 44 0 (.step 3 (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 31)))) (.step 31 (.step 68 (.run (.close 31))))) (.step 31 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 18)))) (.step 18 (.run (.close 68)))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 31 (.step 68 (.run (.close 3)))))) (.step 18 (.step 31 (.step 55 (.run (.close 3)))))) (.step 18 (.step 31 (.step 55 (.run (.close 3)))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 31)))) (.step 18 (.step 3 (.split 10 0 (.step 11 (.run (.close 2))) (.step 18 (.run (.close 31))))))) (.step 2 (.run (.close 18)))) (.step 18 (.step 3 (.step 40 (.run (.close 31)))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.step 18 (.run (.close 29))))) (.step 2 (.step 18 (.run (.close 31))))) (.step 3 (.step 31 (.step 23 (.run (.close 11)))))) (.step 3 (.step 31 (.split 10 0 (.split 16 0 (.step 29 (.run (.close 2))) (.step 68 (.run (.close 18)))) (.step 18 (.run (.close 2))))))) (.step 2 (.step 3 (.run (.close 11))))) (.step 2 (.step 18 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1052
namespace Part1053
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578098629151000688953204458651648, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317891640017820413762525247218322753731291570712034091244831371794754369017810717605160741663624470948341167947776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 18 (.step 31 (.step 11 (.step 18 (.run (.close 2))))))) (.step 31 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 2))) (.step 18 (.run (.close 68)))) (.step 18 (.run (.close 68)))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 31 (.split 18 0 (.step 55 (.run (.close 3))) (.step 2 (.run (.close 68))))))) (.step 18 (.step 31 (.split 10 0 (.step 55 (.run (.close 3))) (.step 18 (.run (.close 43))))))) (.step 18 (.step 31 (.split 10 0 (.step 11 (.run (.close 2))) (.step 18 (.run (.close 43))))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 31)))) (.step 18 (.step 3 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 18 (.run (.close 31)))) (.step 18 (.run (.close 31))))))) (.step 2 (.run (.close 18)))) (.step 18 (.step 3 (.split 10 0 (.step 40 (.run (.close 31))) (.step 18 (.run (.close 43))))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.step 18 (.run (.close 29))))) (.step 2 (.step 18 (.run (.close 31))))) (.step 3 (.step 31 (.step 23 (.run (.close 11))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1053
namespace Part1054
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403572929559527424, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317891640017820413762525247218322753731291570712034091244831371794754369017812046833156527788424347291535229845504⟩
def references : Fin 3 → Box := ![Part1051.root, Part1052.root, Part1053.root]
def proof : Enumeration.Proof 3 := (.split 9 0 (.split 29 0 (.split 44 0 (.reuse 0) (.split 6 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 73 0 (.split 49 0 (.split 58 0 (.split 74 0 (.split 16 0 (.step 18 (.run (.close 3))) (.step 55 (.run (.close 3)))) (.step 71 (.run (.close 11)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 68)))) (.step 2 (.run (.close 48)))) (.step 71 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 68 (.step 71 (.step 55 (.run (.close 2)))))) (.step 2 (.run (.close 48)))) (.step 55 (.step 71 (.run (.close 29))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 68)))) (.step 55 (.step 63 (.run (.close 11))))) (.step 2 (.run (.close 48)))) (.step 68 (.step 48 (.run (.close 9))))) (.step 2 (.run (.close 11)))) (.step 2 (.run (.close 29))))) (.reuse 1)) (.split 6 0 (.split 8 0 (.split 12 0 (.reuse 2) (.step 3 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.run (.close 9))) (.step 68 (.run (.close 9)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 31)))) (.step 18 (.run (.close 2))))))) (.step 2 (.step 3 (.run (.close 11))))) (.step 2 (.step 18 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1051.covered
  · exact Part1052.covered
  · exact Part1053.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1054
namespace Part1055
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234131009374243490885467899096048133081610657663529557266338230579216391052924193414109654826322937569212852872431108196804037645571543841719631757656095060465447801794750336701427617399182708062743599794847041722515456⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 56 0 (.split 59 0 (.split 72 0 (.split 74 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 31 0 (.split 41 0 (.step 9 (.step 2 (.run (.close 40)))) (.step 3 (.step 62 (.step 9 (.run (.close 31)))))) (.step 3 (.step 27 (.step 3 (.step 4 (.run (.close 43))))))) (.step 68 (.step 70 (.run (.close 2))))) (.split 36 0 (.step 68 (.step 27 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 36 0 (.step 68 (.step 27 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 22 0 (.split 23 0 (.step 27 (.step 68 (.run (.close 3)))) (.step 55 (.step 3 (.run (.close 27))))) (.step 68 (.run (.close 27))))) (.step 68 (.step 9 (.step 62 (.step 68 (.run (.close 70))))))) (.split 74 0 (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 26 0 (.split 19 0 (.split 35 0 (.step 70 (.run (.close 27))) (.step 62 (.step 18 (.run (.close 57))))) (.step 76 (.step 3 (.run (.close 9))))) (.step 62 (.step 75 (.step 2 (.run (.close 40)))))) (.step 9 (.run (.close 2)))) (.step 62 (.run (.close 2)))) (.step 62 (.run (.close 2)))) (.step 62 (.step 68 (.run (.close 27))))) (.step 62 (.step 9 (.run (.close 3))))) (.step 62 (.step 68 (.step 27 (.run (.close 2)))))) (.step 9 (.run (.close 27)))) (.step 62 (.run (.close 2))))) (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.step 54 (.step 70 (.step 9 (.step 54 (.step 2 (.run (.close 5))))))) (.step 4 (.run (.close 9)))) (.step 4 (.step 71 (.run (.close 9))))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1055
namespace Part1056
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234131009374243490885467899096048133081610657663529557266341745355618377925098264147318784499650179520088988870187992817048044070723623327563531013602687367728945650366304785281408241128074174351086585474905468968108032⟩
def references : Fin 1 → Box := ![Part1055.root]
def proof : Enumeration.Proof 1 := (.split 53 0 (.split 38 0 (.split 32 0 (.reuse 0) (.split 18 0 (.split 19 0 (.split 23 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 56 0 (.split 59 0 (.split 72 0 (.split 35 0 (.split 54 0 (.step 44 (.run (.close 27))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 71 (.step 4 (.run (.close 3))))) (.step 53 (.step 70 (.run (.close 44))))) (.step 4 (.step 55 (.step 5 (.run (.close 2)))))) (.step 71 (.step 4 (.run (.close 27))))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 4)))) (.step 3 (.run (.close 4)))) (.step 3 (.run (.close 4))))) (.split 8 0 (.split 14 0 (.split 74 0 (.split 22 0 (.split 24 0 (.split 32 0 (.split 26 0 (.split 35 0 (.split 56 0 (.step 70 (.split 4 0 (.split 10 0 (.step 3 (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 42))))) (.step 76 (.step 43 (.run (.close 28))))) (.step 71 (.step 4 (.run (.close 18))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 58)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 2))))) (.split 38 0 (.split 56 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 18 0 (.split 72 0 (.split 8 0 (.split 14 0 (.step 70 (.step 27 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 27)))) (.step 63 (.run (.close 27)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 5 (.step 2 (.run (.close 4)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1055.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1056
namespace Part1057
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234131009374243490885467899096048133081610657663529557266341745355618377925098264147318784499650179520088988870187992817048044070723623329460668603666875913548732668748647467549385031019396859327413495358983912061665280⟩
def references : Fin 1 → Box := ![Part1056.root]
def proof : Enumeration.Proof 1 := (.split 27 0 (.split 13 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 8 0 (.split 14 0 (.split 18 0 (.split 53 0 (.split 22 0 (.split 38 0 (.split 56 0 (.split 74 0 (.split 24 0 (.split 4 0 (.split 59 0 (.split 32 0 (.step 15 (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 2)))) (.step 76 (.run (.close 9)))) (.step 10 (.run (.close 9)))) (.step 5 (.run (.close 9)))) (.step 55 (.run (.close 70)))) (.step 55 (.step 72 (.step 58 (.run (.close 2)))))) (.step 71 (.step 55 (.step 65 (.step 76 (.step 18 (.run (.close 2)))))))) (.step 55 (.run (.close 70)))) (.step 55 (.step 4 (.step 63 (.step 2 (.run (.close 5))))))) (.step 3 (.step 76 (.step 65 (.step 9 (.run (.close 2))))))) (.step 55 (.step 5 (.run (.close 27))))) (.step 55 (.step 63 (.run (.close 46))))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 6 0 (.split 12 0 (.split 13 0 (.split 26 0 (.split 31 0 (.split 38 0 (.split 56 0 (.split 35 0 (.split 36 0 (.split 54 0 (.split 72 0 (.step 44 (.split 4 0 (.step 44 (.step 2 (.run (.close 63)))) (.step 31 (.run (.close 46))))) (.step 63 (.run (.close 46)))) (.step 4 (.step 3 (.run (.close 2))))) (.step 55 (.run (.close 46)))) (.step 71 (.step 63 (.run (.close 46))))) (.step 55 (.run (.close 46)))) (.step 55 (.step 71 (.run (.close 46))))) (.step 3 (.step 73 (.step 64 (.step 27 (.run (.close 2))))))) (.step 55 (.step 71 (.run (.close 46))))) (.step 3 (.run (.close 10)))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1056.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1057
namespace Part1058
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183919897053463409082013695591285166721561094501219434496, 5789234131009374243490885467899096048133081610657663529557266341745355618377925098264147318784499650179520088988870187992817048044070723623329460668603666875913548732668750144045226011875607637432596116149762732304396976128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 72 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 6 0 (.split 31 0 (.split 12 0 (.split 54 0 (.split 53 0 (.split 8 0 (.split 14 0 (.step 70 (.split 74 0 (.step 54 (.step 70 (.step 2 (.run (.close 31))))) (.step 31 (.run (.close 62))))) (.step 31 (.step 63 (.run (.close 11))))) (.step 31 (.run (.close 46)))) (.step 31 (.run (.close 2)))) (.step 72 (.run (.close 61)))) (.step 54 (.split 8 0 (.step 70 (.step 5 (.step 24 (.run (.close 2))))) (.step 63 (.run (.close 24)))))) (.step 31 (.step 44 (.step 54 (.step 31 (.run (.close 2))))))) (.step 7 (.step 5 (.run (.close 27))))) (.split 31 0 (.step 54 (.split 6 0 (.split 7 0 (.split 12 0 (.split 8 0 (.step 70 (.step 31 (.step 24 (.step 2 (.run (.close 24)))))) (.step 23 (.run (.close 46)))) (.step 18 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 24 (.run (.close 3))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 2))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1058
namespace Part1059
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918401937288419568328373221701297964031986482227970048, 5789234131009374243490885467899096048133081610657663529557266341745355618377925098264147318784499650179520088988870187992817048044070723623329460668603666875913548732668750145506727649206510555636280948866045751960329519104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 38 0 (.split 36 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 53 0 (.split 17 0 (.split 73 0 (.split 22 0 (.split 50 0 (.split 27 0 (.step 27 (.run (.close 2))) (.step 31 (.run (.close 2)))) (.step 53 (.run (.close 2)))) (.step 7 (.run (.close 70)))) (.step 65 (.run (.close 70)))) (.step 7 (.step 24 (.step 31 (.run (.close 42)))))) (.step 31 (.step 7 (.step 63 (.run (.close 72)))))) (.split 4 0 (.split 17 0 (.step 3 (.run (.close 70))) (.step 23 (.run (.close 70)))) (.step 23 (.run (.close 70))))) (.split 4 0 (.split 7 0 (.split 10 0 (.step 3 (.step 54 (.step 70 (.step 53 (.step 24 (.run (.close 2))))))) (.step 23 (.step 24 (.run (.close 18))))) (.step 5 (.run (.close 2)))) (.step 23 (.step 24 (.run (.close 18)))))) (.split 4 0 (.split 7 0 (.split 10 0 (.step 3 (.split 13 0 (.split 19 0 (.step 70 (.step 53 (.step 24 (.run (.close 2))))) (.step 18 (.run (.close 9)))) (.step 5 (.run (.close 2))))) (.step 23 (.step 24 (.run (.close 18))))) (.step 5 (.run (.close 2)))) (.step 23 (.step 24 (.run (.close 18)))))) (.step 68 (.step 2 (.run (.close 24))))) (.step 68 (.run (.close 70)))) (.step 68 (.step 55 (.run (.close 24))))) (.step 68 (.step 55 (.run (.close 63))))) (.step 68 (.step 31 (.step 63 (.run (.close 27)))))) (.step 68 (.step 31 (.step 63 (.run (.close 27)))))) (.step 68 (.run (.close 70)))) (.step 68 (.step 63 (.run (.close 58))))) (.step 68 (.run (.close 7))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1059
namespace Part1060
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234131009374243490885467899096048133081610657667394094789359003700313729816030251491617711829356614518746224121639511959337604495259817096042591181629339529580234845927510585388692194166298544954415946794448941144342528⟩
def references : Fin 3 → Box := ![Part1057.root, Part1058.root, Part1059.root]
def proof : Enumeration.Proof 3 := (.split 57 0 (.split 16 0 (.split 17 0 (.split 7 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 18 0 (.split 19 0 (.split 53 0 (.split 8 0 (.split 14 0 (.split 36 0 (.split 23 0 (.split 38 0 (.step 46 (.run (.close 71))) (.step 7 (.run (.close 2)))) (.step 3 (.run (.close 26)))) (.step 71 (.step 72 (.run (.close 46))))) (.step 55 (.step 5 (.run (.close 27))))) (.step 55 (.run (.close 46)))) (.step 55 (.step 63 (.run (.close 46))))) (.step 3 (.step 76 (.step 72 (.run (.close 18)))))) (.step 3 (.step 76 (.step 65 (.step 9 (.run (.close 2))))))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 3 (.step 2 (.run (.close 4)))))) (.reuse 1)) (.reuse 2)) (.split 38 0 (.split 53 0 (.split 56 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 74 0 (.step 3 (.step 62 (.step 2 (.run (.close 4))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.run (.close 63))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1057.covered
  · exact Part1058.covered
  · exact Part1059.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1060
namespace Part1061
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234131009374243490885467899096048133081610657667394094789359003700313729816033303051317794505325896799821261119876542287226314131404102904494831177616554819421527526434827250342342499537010292875852098465926516916092928⟩
def references : Fin 1 → Box := ![Part1060.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 6 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 3 (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 68 (.run (.close 3)))) (.step 68 (.step 3 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 36 0 (.step 3 (.step 2 (.run (.close 5)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.step 3 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 55 (.step 68 (.run (.close 63))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1060.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1061
namespace Part1062
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234136395753406676424723379602752013306946066372970974395682371915175138175526310635728389257590051149628141582476575046615541901706168421950199739740800938221973663179855526334271571368360355602612684159225469157244928⟩
def references : Fin 1 → Box := ![Part1061.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.split 71 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 46 0 (.split 53 0 (.split 47 0 (.split 42 0 (.split 56 0 (.split 57 0 (.split 7 0 (.step 3 (.step 27 (.step 3 (.split 59 0 (.step 71 (.run (.close 68))) (.step 62 (.step 71 (.run (.close 68)))))))) (.step 55 (.step 18 (.run (.close 3))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 63 (.run (.close 68))))) (.step 68 (.step 63 (.run (.close 68))))) (.step 68 (.step 63 (.run (.close 11)))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 36 0 (.split 38 0 (.split 26 0 (.split 56 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 70 (.step 3 (.run (.close 2)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.run (.close 68)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 68)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.run (.close 68))))) (.step 55 (.step 68 (.run (.close 63))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 55 (.step 63 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1061.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1062
namespace Part1063
def root : Box := ⟨4898883310661797945363497076419843873668423473368832004697525472423526611782480950640703892397556074306638413669157326898237362962595999637868497385088569090356823462218669856565645193989282133123792896, 5789234136395753406676424723384169648139344787960032346849242165387555369688888196163022127149850126229263782752098649066843789062187944808375987570338818850097801879862602685460626526984413569868512057580482414968232214528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 66 0 (.split 8 0 (.split 14 0 (.split 64 0 (.split 71 0 (.split 7 0 (.step 3 (.step 27 (.step 3 (.step 52 (.run (.close 29)))))) (.step 18 (.run (.close 3)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 52)))) (.step 55 (.step 68 (.run (.close 11))))) (.step 55 (.run (.close 68)))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 48))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 63 (.run (.close 11))))) (.step 68 (.step 63 (.run (.close 11))))) (.step 68 (.step 63 (.run (.close 11)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1063
namespace Part1064
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961236537299166636361320601536965019834693044991969501264312420153477419771413026420819784335286981892446946609168546861640911913223428255111601717248, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572443142081507826493575918402049122403680200110914484738823605050262931484017199398042401254387437776202292168668745958896007150674378752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 38 0 (.split 46 0 (.split 73 0 (.step 3 (.split 4 0 (.split 35 0 (.step 68 (.step 3 (.run (.close 55)))) (.step 71 (.run (.close 3)))) (.step 68 (.step 3 (.run (.close 48)))))) (.step 55 (.run (.close 3)))) (.split 4 0 (.split 10 0 (.split 30 0 (.step 69 (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.step 68 (.step 3 (.step 71 (.run (.close 2)))))) (.step 68 (.step 55 (.split 46 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 55))))))) (.step 68 (.step 55 (.run (.close 3))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 68 (.step 3 (.step 27 (.run (.close 2)))))) (.step 55 (.step 63 (.run (.close 68))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 55 (.step 63 (.run (.close 11))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.step 9 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1064
namespace Part1065
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572443142081507826493575918404397664986454033338803965335612942077638615717922185965666177431786353915534976491407505556161703253538504704⟩
def references : Fin 3 → Box := ![Part1062.root, Part1063.root, Part1064.root]
def proof : Enumeration.Proof 3 := (.split 48 0 (.split 63 0 (.split 64 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 8 0 (.split 66 0 (.split 71 0 (.split 7 0 (.step 3 (.step 27 (.step 3 (.step 53 (.step 71 (.run (.close 68))))))) (.step 55 (.step 18 (.run (.close 3))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 68)))) (.step 55 (.step 68 (.run (.close 42))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 63 (.run (.close 68))))) (.step 68 (.step 63 (.run (.close 11))))) (.step 68 (.step 63 (.run (.close 11)))))) (.reuse 1)) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.reuse 2) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1062.covered
  · exact Part1063.covered
  · exact Part1064.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1065
namespace Part1066
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616323208302986719449642876683420956344548612073126181353967374245297204571883222144556393409578632876353426746616489725006519695833038848, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126698173684921392519022479669574996579621353480856236392358680394188177893256096660053782444619795125859071819776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 41 0 (.step 3 (.run (.close 46))) (.step 55 (.run (.close 3)))) (.step 3 (.run (.close 47)))) (.split 4 0 (.split 10 0 (.split 30 0 (.step 69 (.run (.close 3))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.step 68 (.step 3 (.step 58 (.run (.close 2)))))) (.step 68 (.split 46 0 (.split 47 0 (.step 55 (.run (.close 3))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))))) (.step 68 (.split 46 0 (.split 47 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 46 0 (.split 47 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 68 (.run (.close 3)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23))))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 55 (.step 3 (.step 71 (.run (.close 68)))))) (.step 3 (.split 46 0 (.step 9 (.step 11 (.run (.close 2)))) (.step 2 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1066
namespace Part1067
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161562985810740038820775276728656616467278802300389971628295216873924037885737016959797559296, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250371139464731555795297786619133966209664572190181393945332710075915101489662764034560098304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 58 0 (.split 70 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 36 0 (.split 10 0 (.split 30 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 55 (.step 31 (.step 53 (.step 23 (.step 18 (.run (.close 68))))))))) (.step 3 (.step 44 (.step 65 (.run (.close 2)))))) (.step 3 (.step 44 (.step 53 (.step 3 (.run (.close 2))))))) (.step 3 (.split 4 0 (.step 26 (.step 53 (.step 68 (.run (.close 2))))) (.step 18 (.run (.close 2)))))) (.step 68 (.step 3 (.step 31 (.step 2 (.run (.close 48))))))) (.step 3 (.step 44 (.step 53 (.step 11 (.run (.close 2))))))) (.step 55 (.step 18 (.step 3 (.step 29 (.run (.close 2))))))) (.step 3 (.step 44 (.step 65 (.run (.close 2)))))) (.step 3 (.step 44 (.step 65 (.run (.close 2)))))) (.step 55 (.step 18 (.step 3 (.step 29 (.run (.close 2))))))) (.step 3 (.step 44 (.step 53 (.step 11 (.run (.close 2))))))) (.step 55 (.step 3 (.step 31 (.step 11 (.step 2 (.run (.close 31)))))))) (.step 3 (.split 4 0 (.step 26 (.step 65 (.run (.close 2)))) (.step 2 (.run (.close 48)))))) (.step 3 (.split 4 0 (.step 26 (.step 53 (.step 29 (.run (.close 2))))) (.step 18 (.run (.close 2)))))) (.step 55 (.step 3 (.step 31 (.step 11 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1067
namespace Part1068
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455019254405287034347101194551296, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250371139464731555795297786619133966209664572190181393944003482081366917910816343337415475200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 14 0 (.split 24 0 (.split 26 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 72 0 (.split 36 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.split 10 0 (.step 18 (.run (.close 2))) (.step 18 (.run (.close 42))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 18 (.run (.close 2))))) (.step 3 (.step 44 (.step 52 (.split 4 0 (.step 3 (.run (.close 2))) (.step 18 (.run (.close 2)))))))) (.step 68 (.step 18 (.step 55 (.step 2 (.run (.close 4))))))) (.step 3 (.split 4 0 (.step 26 (.step 52 (.step 3 (.run (.close 2))))) (.step 18 (.run (.close 2)))))) (.step 68 (.step 3 (.step 31 (.step 2 (.run (.close 48))))))) (.step 3 (.step 44 (.step 52 (.split 4 0 (.split 10 0 (.step 3 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 31)))))))) (.step 68 (.step 18 (.step 3 (.run (.close 2)))))) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 3 (.step 44 (.split 10 0 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2)))) (.step 18 (.run (.close 2))))))) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 3 (.step 44 (.step 52 (.split 4 0 (.split 10 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 3 (.run (.close 31)))) (.step 2 (.run (.close 31)))))))) (.step 55 (.step 3 (.step 31 (.step 27 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1068
namespace Part1069
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250371139464731555795297786619133966209664572190181393945332710077153042710692686531477372928⟩
def references : Fin 4 → Box := ![Part1065.root, Part1066.root, Part1067.root, Part1068.root]
def proof : Enumeration.Proof 4 := (.split 9 0 (.split 29 0 (.split 44 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.reuse 1) (.step 55 (.step 3 (.step 63 (.run (.close 11)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.split 46 0 (.step 9 (.run (.close 2))) (.step 71 (.run (.close 2)))))) (.step 55 (.step 3 (.step 63 (.run (.close 11)))))) (.step 55 (.step 3 (.step 2 (.run (.close 71)))))) (.step 3 (.split 46 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 71)))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.step 31 (.run (.close 3))))))) (.split 6 0 (.split 7 0 (.reuse 2) (.step 3 (.split 4 0 (.step 26 (.step 65 (.run (.close 2)))) (.step 2 (.run (.close 48)))))) (.step 3 (.split 4 0 (.step 26 (.step 53 (.step 29 (.run (.close 2))))) (.step 2 (.run (.close 18))))))) (.split 6 0 (.split 8 0 (.split 12 0 (.reuse 3) (.step 3 (.split 4 0 (.step 26 (.step 52 (.split 16 0 (.step 9 (.run (.close 2))) (.step 68 (.run (.close 2)))))) (.step 18 (.run (.close 2)))))) (.step 55 (.step 3 (.step 31 (.step 27 (.run (.close 2))))))) (.step 3 (.split 4 0 (.step 26 (.step 52 (.split 16 0 (.step 9 (.run (.close 2))) (.step 68 (.run (.close 9)))))) (.step 2 (.run (.close 18)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1065.covered
  · exact Part1066.covered
  · exact Part1067.covered
  · exact Part1068.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1069
namespace Part1070
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243485986584588438710047216197411217962417850698040556747500718503133376513268029480071611639560162878302352514011103909891021815634577844740576676532624793977099127864344486867652061634596370873124153982976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 22 0 (.split 14 0 (.split 6 0 (.split 12 0 (.split 30 0 (.split 39 0 (.split 58 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.split 35 0 (.split 72 0 (.split 56 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 4 (.step 2 (.run (.close 5))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 33 0 (.split 41 0 (.split 53 0 (.step 21 (.step 2 (.run (.close 58)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 74 0 (.split 31 0 (.split 32 0 (.split 7 0 (.step 4 (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 5 (.step 31 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 2))))) (.split 35 0 (.split 72 0 (.split 12 0 (.split 36 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.step 2 (.run (.close 5))))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1070
namespace Part1071
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243485986584588438710047216197411217962417850698040556747500718503133376513268029480071611639560162878302352514011103909891021815634577844740576676532624795475138306128519978026429016377712285635084185239552⟩
def references : Fin 1 → Box := ![Part1070.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 8 0 (.split 17 0 (.reuse 0) (.split 35 0 (.split 72 0 (.split 36 0 (.split 6 0 (.split 14 0 (.split 74 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2)))))) (.split 38 0 (.split 14 0 (.split 17 0 (.split 56 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 5 (.step 31 (.run (.close 27)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 5))))) (.split 36 0 (.split 35 0 (.split 72 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 12 0 (.split 17 0 (.step 2 (.run (.close 5))) (.step 63 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1070.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1071
namespace Part1072
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243485986584588438710047216197411217962417850698040556747500718503133376513268029480071611639560162878302352514011103909891021815634577844740576676532624795475138306128519978027696666977940515037680400072704⟩
def references : Fin 1 → Box := ![Part1071.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 10 0 (.reuse 0) (.split 9 0 (.split 8 0 (.split 14 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 64 (.step 2 (.run (.close 4)))))) (.step 63 (.step 72 (.step 55 (.step 48 (.run (.close 2))))))) (.step 63 (.step 65 (.step 4 (.run (.close 2)))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 31 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))))) (.split 29 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 5))))) (.step 63 (.step 10 (.step 48 (.run (.close 2)))))) (.step 63 (.step 10 (.step 48 (.run (.close 2)))))) (.step 63 (.step 65 (.step 4 (.step 2 (.run (.close 4))))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 33)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1071.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1072
namespace Part1073
def root : Box := ⟨4898883310657346788030287556357712069628819860444861045260235970461835218935600077441189048488868913046054849919869196059181551005542972918841963234896105718574448293309042141882235931290217134212251648, 5789234131009374243490885467899096052484164047812619602022372929823178613461951918683992833634346030317226051368971760512036266600829033812163793459081571815161719254003088252574118504653263904616054292187575052401748475904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 29 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 54 0 (.step 2 (.run (.close 5))) (.step 72 (.step 53 (.run (.close 2))))) (.step 70 (.run (.close 2)))) (.step 72 (.step 54 (.step 70 (.step 2 (.run (.close 4))))))) (.step 70 (.run (.close 2)))) (.step 72 (.step 54 (.step 70 (.step 2 (.run (.close 5))))))) (.step 65 (.step 42 (.step 4 (.step 70 (.run (.close 2))))))) (.step 70 (.step 2 (.run (.close 4))))) (.step 70 (.step 2 (.run (.close 4))))) (.split 16 0 (.split 53 0 (.step 53 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 65))))) (.step 46 (.step 4 (.step 55 (.step 53 (.run (.close 10))))))) (.split 26 0 (.split 72 0 (.split 36 0 (.split 38 0 (.step 53 (.split 42 0 (.split 16 0 (.split 17 0 (.step 5 (.step 2 (.run (.close 63)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 70)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 4 (.run (.close 70)))) (.step 4 (.run (.close 46))))) (.split 23 0 (.split 31 0 (.split 33 0 (.step 53 (.run (.close 2))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1073
namespace Part1074
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243490885467899096052484164047812623466559895947081523308813842850671337132561675736752224708604223212031178556161253570005930375381659534278777750756180265617652779547640919647525965699307609129657462423552⟩
def references : Fin 2 → Box := ![Part1072.root, Part1073.root]
def proof : Enumeration.Proof 2 := (.split 57 0 (.split 67 0 (.reuse 0) (.split 9 0 (.reuse 1) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.step 64 (.split 24 0 (.step 70 (.step 30 (.run (.close 18)))) (.step 2 (.run (.close 27))))) (.step 71 (.step 4 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 3 (.step 4 (.run (.close 15))))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))))) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 8 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 9 0 (.step 30 (.step 65 (.split 24 0 (.step 58 (.run (.close 2))) (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 48)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1072.covered
  · exact Part1073.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1074
namespace Part1075
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243490885467899096052484164047812623466559895947081523308813842853722896832644351706034505783641221449061506444870889714291738827621655521494067592048860772934317733197946290359273887135459280607233234173952⟩
def references : Fin 1 → Box := ![Part1074.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 54 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 35 0 (.split 72 0 (.step 65 (.step 30 (.step 58 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 71))))) (.split 12 0 (.split 23 0 (.split 54 0 (.split 16 0 (.split 8 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.step 2 (.run (.close 48))))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 2 (.run (.close 48)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1074.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1075
namespace Part1076
def root : Box := ⟨4784065733068162056019040113691253782879319798211750004587427219163602976780837926010063712026627395196549833148716246443939221057819305073697639199317323226732683590827210437279744833831312765747200, 5789234136395753406676424723379602756364389383221329043439502270449738170222202346730481243239103970188855590521684049094265834098660016357256282990217645740186392494997517962593725127018121709336613896044973906185475325952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 9 0 (.split 71 0 (.step 30 (.step 3 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 68)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 71)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1076
namespace Part1077
def root : Box := ⟨4562444968704632373597244070806879402716223591275380350424707370518324999035454626185899514679673659973387584490798133812504603055174679854855989602484286348275159895617246595027696330211328000, 5789234136395753406676424723384165196982011578439970215045202561774631398729450906661060435757003245356064267908189961905583205498438658666829877397528334444907767932995770623913447341206373704010974160995056780377721929728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 27 0 (.split 32 0 (.split 4 0 (.split 10 0 (.split 30 0 (.split 67 0 (.split 8 0 (.split 69 0 (.step 31 (.split 70 0 (.split 14 0 (.split 66 0 (.step 53 (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 3))))) (.split 12 0 (.step 31 (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 3 (.step 27 (.step 71 (.run (.close 2)))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 4 (.step 5 (.step 71 (.run (.close 10)))))) (.step 4 (.step 5 (.step 55 (.step 18 (.run (.close 2))))))) (.step 5 (.step 18 (.step 2 (.run (.close 55)))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1077
namespace Part1078
def root : Box := ⟨4459859498083829974276734252779768569961127490930341652721095312310842732254463690246383842104380702341605297646689790205242772003710057773496897332113384816380059806161591185137444793090048, 5789234136395753406676424723384169652490427225114988419314348753465378364772915016582867641999696506366969745132200221586063007618946254997210320360816723789345972401196940792528017382431166918849523340941297095684550295552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 27 0 (.split 32 0 (.split 4 0 (.split 10 0 (.split 30 0 (.split 67 0 (.split 8 0 (.split 69 0 (.step 31 (.split 70 0 (.split 64 0 (.split 66 0 (.step 52 (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 3))))) (.split 12 0 (.step 31 (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 3))))) (.step 71 (.run (.close 2)))) (.split 8 0 (.split 12 0 (.split 18 0 (.step 31 (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 9)))) (.step 71 (.run (.close 68))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 3 (.step 2 (.run (.close 71))))) (.step 3 (.step 2 (.run (.close 71))))) (.step 4 (.step 5 (.step 71 (.run (.close 10)))))) (.step 4 (.step 5 (.step 55 (.step 18 (.run (.close 10))))))) (.step 5 (.step 18 (.step 4 (.step 18 (.run (.close 9))))))) (.step 71 (.step 63 (.step 2 (.run (.close 4)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 4 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1078
namespace Part1079
def root : Box := ⟨4351082437154956072465106588077822995084029942168395830844850431429056570405985735301504967231345604431876829098240635663953919547959666820253921899091144571844152429620624110423271014400, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417957991927887964199538298505970184205672590097114154169945732555543554966092707300004284499177209362288325472418788916976383969856585728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 24 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 31 0 (.split 63 0 (.split 33 0 (.split 41 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1079
namespace Part1080
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417957991927887964199538298505970184205672590097114154169945732555543554966092707300004284499177209362288325472418788916976383969856585728⟩
def references : Fin 5 → Box := ![Part1075.root, Part1076.root, Part1077.root, Part1078.root, Part1079.root]
def proof : Enumeration.Proof 5 := (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.reuse 0) (.split 35 0 (.split 16 0 (.split 17 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 22 0 (.split 57 0 (.split 4 0 (.split 10 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 30 0 (.split 67 0 (.split 14 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 31)))) (.step 4 (.step 68 (.step 4 (.run (.close 2)))))) (.step 4 (.step 68 (.step 4 (.run (.close 2)))))) (.step 5 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 4 (.run (.close 2)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1075.covered
  · exact Part1076.covered
  · exact Part1077.covered
  · exact Part1078.covered
  · exact Part1079.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1080
namespace Part1081
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001216297201018813394233936839394197504⟩
def references : Fin 6 → Box := ![Part1033.root, Part1043.root, Part1044.root, Part1054.root, Part1069.root, Part1080.root]
def proof : Enumeration.Proof 6 := (.split 62 0 (.split 67 0 (.split 4 0 (.split 10 0 (.reuse 0) (.split 9 0 (.reuse 1) (.split 6 0 (.split 7 0 (.reuse 2) (.step 3 (.step 31 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2))))))) (.step 3 (.step 31 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.run (.close 9))) (.step 68 (.run (.close 9)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 31)))) (.step 15 (.run (.close 2))))))))) (.reuse 3)) (.reuse 4)) (.split 44 0 (.reuse 5) (.split 6 0 (.split 12 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 24 0 (.split 54 0 (.split 4 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 58 0 (.split 10 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 63)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 48 (.step 63 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 68)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1033.covered
  · exact Part1043.covered
  · exact Part1044.covered
  · exact Part1054.covered
  · exact Part1069.covered
  · exact Part1080.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1081
namespace Part1082
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304043431466397091092833865852754369052714182509022733198205646808789890119444901047789053542400⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 35 0 (.split 50 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 43 (.step 4 (.step 2 (.run (.close 4)))))) (.step 43 (.step 4 (.step 8 (.step 71 (.run (.close 2))))))) (.split 7 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 53 0 (.step 55 (.split 54 0 (.step 2 (.run (.close 55))) (.step 4 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 23)))) (.step 4 (.step 63 (.run (.close 2)))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.step 24 (.step 18 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1082
namespace Part1083
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304043431466397092945507293649813495829849942648029258850526730687034699666639148981459408125952⟩
def references : Fin 1 → Box := ![Part1082.root]
def proof : Enumeration.Proof 1 := (.split 12 0 (.split 26 0 (.reuse 0) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.split 18 0 (.step 24 (.step 47 (.run (.close 2)))) (.step 2 (.run (.close 23))))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 74 0 (.split 18 0 (.step 68 (.split 19 0 (.step 24 (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1082.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1083
namespace Part1084
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304045468502373427431593562095501905208010994116422924786777366827484054047940065239670198370304⟩
def references : Fin 1 → Box := ![Part1083.root]
def proof : Enumeration.Proof 1 := (.split 6 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 50 0 (.step 48 (.step 8 (.step 2 (.run (.close 4))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 48))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 71 (.step 4 (.run (.close 48)))))) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 18 0 (.step 68 (.split 22 0 (.step 2 (.run (.close 24))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 15)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1083.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1084
namespace Part1085
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406676424723384169648139344787960032346849242165387555369685694647396048869936360519042899789829613957729415235893770592423515405256097289170086947929389288390436413789755240944977948003700222762341369905152⟩
def references : Fin 1 → Box := ![Part1084.root]
def proof : Enumeration.Proof 1 := (.split 67 0 (.split 17 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 73 0 (.split 50 0 (.step 8 (.run (.close 11))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 63 (.step 2 (.run (.close 4)))))) (.step 4 (.step 63 (.step 2 (.run (.close 4)))))) (.step 4 (.step 71 (.run (.close 63)))))) (.split 12 0 (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 17 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.step 71 (.run (.close 48)))))) (.step 68 (.step 3 (.run (.close 8))))) (.step 68 (.step 4 (.step 71 (.run (.close 2)))))) (.step 68 (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1084.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1085
namespace Part1086
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140877439256444896540105950833410048, 5789234136395753406676424723384169652490427225114988419314348753465378364769721467815894384786206899180605752209715530248634454450528902612349738046575194109335118450723626497503804645201994295225371947249981464279492067328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 14 0 (.split 39 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 63 (.run (.close 48)))) (.step 63 (.run (.close 2)))) (.step 55 (.step 48 (.run (.close 2))))) (.step 55 (.step 48 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 11))))) (.step 68 (.step 63 (.run (.close 4))))) (.step 63 (.step 4 (.step 71 (.run (.close 24)))))) (.step 68 (.step 63 (.run (.close 4))))) (.step 71 (.step 68 (.step 63 (.run (.close 4)))))) (.step 71 (.step 63 (.step 4 (.step 71 (.run (.close 24))))))) (.step 71 (.step 4 (.step 63 (.step 4 (.step 2 (.run (.close 5)))))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 68 (.step 48 (.run (.close 2))))) (.step 3 (.step 24 (.step 48 (.run (.close 2)))))) (.step 68 (.step 55 (.step 4 (.step 63 (.step 2 (.run (.close 5)))))))) (.step 55 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 55 (.step 24 (.step 63 (.step 2 (.run (.close 4)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1086
namespace Part1087
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406676424723384169652490427225114988419314348753465378364769721467815894384786206899180605752209715530248634454450528902612349738046575194109335118450723626497503804645201994295225371947249981464279492067328⟩
def references : Fin 2 → Box := ![Part1085.root, Part1086.root]
def proof : Enumeration.Proof 2 := (.split 10 0 (.split 29 0 (.split 62 0 (.reuse 0) (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.step 30 (.step 4 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 48))))) (.step 2 (.run (.close 48)))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 2))))) (.split 30 0 (.split 36 0 (.split 42 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 68 (.step 24 (.step 18 (.step 63 (.run (.close 2))))))) (.step 68 (.step 43 (.step 24 (.step 18 (.step 63 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 2 (.run (.close 4))))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1085.covered
  · exact Part1086.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1087
namespace Part1088
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625624501476043435043794375290677384593724110062747648, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001217595273995507061855688089065750528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 36 0 (.split 42 0 (.split 13 0 (.split 73 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 49 0 (.split 27 0 (.split 32 0 (.split 50 0 (.step 8 (.step 11 (.run (.close 2)))) (.step 63 (.step 58 (.run (.close 31))))) (.step 35 (.run (.close 8)))) (.step 35 (.run (.close 8)))) (.step 48 (.step 2 (.run (.close 48))))) (.step 4 (.step 55 (.step 63 (.run (.close 2)))))) (.step 4 (.step 55 (.step 63 (.run (.close 2)))))) (.step 71 (.step 55 (.step 2 (.run (.close 5)))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 55 (.step 48 (.run (.close 2)))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 48 (.step 2 (.run (.close 5))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1088
namespace Part1089
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001217595273995507061855688089065750528⟩
def references : Fin 2 → Box := ![Part1087.root, Part1088.root]
def proof : Enumeration.Proof 2 := (.split 16 0 (.split 49 0 (.reuse 0) (.split 26 0 (.split 17 0 (.split 22 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 14 0 (.split 38 0 (.split 35 0 (.split 7 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 44 0 (.split 48 0 (.split 10 0 (.split 30 0 (.step 4 (.step 27 (.step 2 (.run (.close 23))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 63 (.step 18 (.step 4 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 4 (.step 71 (.step 68 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 18))))) (.step 4 (.step 68 (.step 58 (.run (.close 3)))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 68 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 27))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 58 (.step 48 (.run (.close 2))))) (.step 63 (.step 58 (.step 48 (.run (.close 27)))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.step 68 (.run (.close 2))))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1087.covered
  · exact Part1088.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1089
namespace Part1090
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310705553641832448, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001217595275233447101141069463476502528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 13 0 (.split 36 0 (.step 30 (.step 11 (.step 48 (.run (.close 2))))) (.step 8 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 63)))) (.step 55 (.step 48 (.run (.close 7))))) (.step 48 (.step 71 (.run (.close 5))))) (.step 71 (.step 55 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.step 71 (.run (.close 9))))) (.step 2 (.run (.close 7)))) (.step 71 (.step 63 (.run (.close 48))))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 48))))) (.step 71 (.step 63 (.run (.close 48))))) (.step 2 (.step 71 (.run (.close 31))))) (.step 2 (.step 71 (.run (.close 24))))) (.step 2 (.step 71 (.run (.close 24))))) (.step 2 (.step 71 (.run (.close 24))))) (.step 2 (.step 71 (.run (.close 31)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1090
namespace Part1091
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304043431466397092945507293649813495829849942648029258850525400160964700117059339167674952318976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 50 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 48))) (.step 43 (.step 4 (.step 2 (.run (.close 4)))))) (.step 43 (.step 4 (.step 8 (.step 71 (.run (.close 2))))))) (.split 7 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 53 0 (.step 55 (.split 54 0 (.step 2 (.run (.close 55))) (.step 4 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 71))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.step 2 (.run (.close 48))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 23)))) (.step 4 (.step 63 (.run (.close 2)))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.step 24 (.step 18 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.step 3 (.step 47 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1091
namespace Part1092
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304045468502373427431593562095501905208010994116422924786777365529409839414232006311441416060928⟩
def references : Fin 1 → Box := ![Part1091.root]
def proof : Enumeration.Proof 1 := (.split 30 0 (.split 12 0 (.reuse 0) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 74 0 (.split 18 0 (.step 68 (.split 19 0 (.step 24 (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 50 0 (.step 48 (.step 8 (.step 2 (.run (.close 4))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 48))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 68 (.step 4 (.step 63 (.run (.close 2)))))) (.step 71 (.step 4 (.run (.close 48))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1091.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1092
namespace Part1093
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304045468502373427431593562095501905208010995613000601413621953769983108115706971360620946915328⟩
def references : Fin 1 → Box := ![Part1092.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 6 0 (.reuse 0) (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 12 0 (.split 18 0 (.step 68 (.split 22 0 (.step 2 (.run (.close 24))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 73 0 (.split 50 0 (.step 8 (.run (.close 11))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 63))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 5))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.step 63 (.step 2 (.run (.close 4)))))) (.step 4 (.step 63 (.step 2 (.run (.close 4)))))) (.step 4 (.step 71 (.run (.close 63))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1092.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1093
namespace Part1094
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364769721467815894384786206899180605752209715530248634454450528900623056792407428625487806125863440266095679201455811123234027599140676858005925111267328⟩
def references : Fin 1 → Box := ![Part1093.root]
def proof : Enumeration.Proof 1 := (.split 62 0 (.split 67 0 (.reuse 0) (.split 12 0 (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 17 0 (.split 54 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.step 71 (.run (.close 48)))))) (.step 68 (.step 3 (.run (.close 8))))) (.step 68 (.step 4 (.step 71 (.run (.close 2)))))) (.step 68 (.step 3 (.run (.close 2)))))) (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.step 30 (.step 4 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 48))))) (.step 2 (.run (.close 48)))) (.step 68 (.step 4 (.run (.close 48))))) (.step 68 (.step 4 (.run (.close 48))))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1093.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1094
namespace Part1095
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139579365041811189634099226657947648, 5789234136395753406676424723384169652490427225114988419314348753465378364769721467815894384786206899180605752209715530248634454450528902612349738046575194109335118450723626497503804645201992997151157313543075457555316604928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 24 0 (.split 31 0 (.split 33 0 (.step 7 (.run (.close 2))) (.step 55 (.step 48 (.run (.close 2))))) (.step 55 (.step 48 (.run (.close 2))))) (.step 63 (.step 55 (.run (.close 11))))) (.step 68 (.run (.close 7)))) (.step 63 (.step 4 (.step 71 (.run (.close 24)))))) (.step 68 (.run (.close 7)))) (.step 68 (.run (.close 7)))) (.step 71 (.step 63 (.step 4 (.step 71 (.run (.close 24))))))) (.step 71 (.step 4 (.step 63 (.step 4 (.step 2 (.run (.close 5)))))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 68 (.step 48 (.run (.close 2))))) (.step 3 (.step 24 (.step 48 (.run (.close 2)))))) (.step 68 (.step 55 (.step 4 (.step 63 (.step 2 (.run (.close 5)))))))) (.step 55 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 55 (.step 24 (.step 63 (.step 2 (.run (.close 4)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1095
namespace Part1096
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642275971467422670313378996096040638666661708957745152⟩
def references : Fin 2 → Box := ![Part1094.root, Part1095.root]
def proof : Enumeration.Proof 2 := (.split 49 0 (.split 10 0 (.split 29 0 (.reuse 0) (.split 30 0 (.split 36 0 (.split 42 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 68 (.step 24 (.step 18 (.step 63 (.run (.close 2))))))) (.step 68 (.step 43 (.step 24 (.step 18 (.step 63 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 2 (.run (.close 4))))))) (.reuse 1)) (.split 17 0 (.split 22 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 38 0 (.split 35 0 (.split 7 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 44 0 (.split 48 0 (.step 27 (.step 9 (.step 2 (.run (.close 71))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 27))))) (.step 4 (.run (.close 9)))) (.step 68 (.step 4 (.run (.close 18))))) (.step 4 (.step 68 (.step 58 (.run (.close 3)))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 9)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 58 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 58 (.step 48 (.run (.close 2))))) (.step 58 (.step 48 (.run (.close 2))))) (.step 63 (.step 58 (.step 48 (.run (.close 27)))))) (.step 48 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1094.covered
  · exact Part1095.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1096
namespace Part1097
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001216297199780873354949681364890288128⟩
def references : Fin 1 → Box := ![Part1096.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 8 0 (.split 29 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 24 0 (.split 46 0 (.split 39 0 (.step 8 (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.run (.close 11)))) (.step 35 (.step 71 (.run (.close 8))))) (.step 48 (.step 58 (.run (.close 11))))) (.step 11 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 31))))) (.step 55 (.step 71 (.run (.close 31))))) (.step 71 (.step 55 (.run (.close 8))))) (.step 3 (.step 35 (.step 18 (.run (.close 42)))))) (.step 11 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 40 (.step 24 (.run (.close 2))))) (.step 4 (.step 55 (.step 48 (.run (.close 2)))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 63 (.step 24 (.step 2 (.run (.close 4))))))) (.step 4 (.step 71 (.step 63 (.step 55 (.step 48 (.run (.close 24)))))))) (.step 4 (.step 48 (.step 2 (.run (.close 5)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1096.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1097
namespace Part1098
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001216297201018813394235061639789412352⟩
def references : Fin 1 → Box := ![Part1097.root]
def proof : Enumeration.Proof 1 := (.split 9 0 (.reuse 0) (.split 10 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 67 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 62 0 (.split 69 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 58))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 24 (.step 68 (.step 18 (.step 63 (.step 68 (.run (.close 3)))))))) (.step 24 (.step 68 (.step 43 (.step 18 (.step 63 (.step 68 (.run (.close 3))))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1097.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1098
namespace Part1099
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001217595275233447101142195363383345152⟩
def references : Fin 1 → Box := ![Part1098.root]
def proof : Enumeration.Proof 1 := (.split 11 0 (.split 4 0 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 13 0 (.split 36 0 (.step 30 (.step 11 (.step 48 (.run (.close 2))))) (.step 8 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 63)))) (.step 68 (.step 55 (.run (.close 7))))) (.step 48 (.step 71 (.run (.close 5))))) (.step 71 (.step 68 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.step 71 (.run (.close 9))))) (.step 2 (.run (.close 7)))) (.step 71 (.step 63 (.run (.close 48))))) (.step 71 (.step 63 (.run (.close 48))))) (.step 71 (.step 63 (.run (.close 48))))) (.step 2 (.step 71 (.run (.close 31))))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.step 71 (.run (.close 31)))))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 49 0 (.split 50 0 (.split 23 0 (.split 54 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 36 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 59 0 (.step 2 (.run (.close 4))) (.step 4 (.step 2 (.run (.close 71))))) (.step 48 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 48 (.step 2 (.run (.close 48)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1098.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1099
namespace Part1100
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671521056007779241891423355673473088456043642362958287058480343086531450573526280946328027881439764239664297468584427250008678040823500396411449721691319800879434508125619464546137952826494421646943715328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 47 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 57 0 (.split 16 0 (.split 17 0 (.split 35 0 (.split 63 0 (.split 56 0 (.step 9 (.split 18 0 (.split 64 0 (.step 7 (.step 68 (.step 2 (.run (.close 40))))) (.step 71 (.run (.close 68)))) (.step 55 (.step 2 (.run (.close 40)))))) (.step 29 (.step 58 (.run (.close 2))))) (.step 29 (.run (.close 4)))) (.step 29 (.run (.close 4)))) (.split 24 0 (.split 39 0 (.step 43 (.step 29 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 24 0 (.split 39 0 (.step 68 (.split 18 0 (.split 19 0 (.step 43 (.step 18 (.step 43 (.run (.close 40))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 31 (.step 71 (.step 40 (.step 68 (.step 48 (.run (.close 2))))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.split 16 0 (.split 17 0 (.step 3 (.step 58 (.step 55 (.step 43 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 23))))) (.step 55 (.step 40 (.split 24 0 (.split 39 0 (.step 68 (.step 58 (.step 3 (.step 71 (.run (.close 28)))))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68))))))) (.step 40 (.step 55 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.step 58 (.step 55 (.split 56 0 (.step 4 (.run (.close 2))) (.step 71 (.run (.close 2))))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 23))))))) (.split 32 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 40 (.step 18 (.step 28 (.run (.close 31))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1100
namespace Part1101
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671521056007779241891423355673473088456043642362958287058480343089508581988241086770018058198549030812376812481959682024923559034257463109069747402653780687285279441887840814284787670387936971780446486528⟩
def references : Fin 1 → Box := ![Part1100.root]
def proof : Enumeration.Proof 1 := (.split 11 0 (.split 14 0 (.split 46 0 (.split 27 0 (.reuse 0) (.split 35 0 (.split 42 0 (.split 6 0 (.step 23 (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.run (.close 3)))) (.step 43 (.run (.close 7)))) (.step 4 (.run (.close 29))))) (.split 24 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 3 (.step 28 (.step 40 (.run (.close 29))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 23)))) (.step 71 (.run (.close 55)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 16 0 (.split 53 0 (.split 57 0 (.step 52 (.step 68 (.run (.close 29)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 68)))) (.step 68 (.step 43 (.run (.close 2))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 71 (.run (.close 68)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5))))) (.split 24 0 (.split 39 0 (.split 58 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 50 0 (.split 35 0 (.step 40 (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 4 (.run (.close 7)))) (.step 4 (.run (.close 43)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1100.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1101
namespace Part1102
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671521056007779241891423355673473088456043642362958287058480343089508581988241089414241933359543426620038044613043841338542290891382340247664928500276945632530662742644682573145928269678604686503054409728⟩
def references : Fin 1 → Box := ![Part1101.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 41 0 (.reuse 0) (.split 11 0 (.split 35 0 (.split 42 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 18 0 (.step 31 (.step 70 (.step 55 (.step 2 (.run (.close 40)))))) (.step 43 (.run (.close 2)))) (.step 4 (.run (.close 40)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 23)))) (.step 43 (.step 55 (.step 2 (.run (.close 40)))))) (.step 4 (.step 71 (.step 43 (.run (.close 2)))))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 32 0 (.split 41 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 7 0 (.split 11 0 (.split 53 0 (.step 29 (.step 43 (.step 63 (.run (.close 11))))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))) (.step 71 (.step 4 (.step 68 (.run (.close 2)))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 5)))) (.step 68 (.run (.close 23)))) (.step 4 (.run (.close 5)))) (.step 4 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1101.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1102
namespace Part1103
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671525840073512305702396937558630707244719933604933503724458110096882230738598820420341166183575466544070938902682244779871531104101582168636202956059541621571127403168250235135108567778494821577762275328⟩
def references : Fin 1 → Box := ![Part1102.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 66 0 (.reuse 0) (.split 8 0 (.split 24 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 69 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 54 0 (.step 43 (.step 31 (.run (.close 48)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 3)))) (.step 55 (.run (.close 31)))) (.step 55 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 48))))) (.step 68 (.run (.close 40)))) (.step 55 (.run (.close 29)))) (.step 68 (.run (.close 40)))) (.step 68 (.run (.close 40)))) (.step 58 (.step 63 (.step 55 (.run (.close 43))))))) (.split 24 0 (.split 39 0 (.split 58 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 11 0 (.split 50 0 (.split 35 0 (.step 55 (.step 40 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68)))) (.step 71 (.step 4 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1102.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1103
namespace Part1104
def root : Box := ⟨2772669694120814859578414186385015696339024297857631357966041480101619974471168370376389277674341402276751532265504578278678069248, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432546730830202017570959349881215142215791124557886948755528978067519555621676431593498325978713000705781594757203391677397623040091619328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 35 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 56 0 (.split 71 0 (.split 72 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.split 54 0 (.split 7 0 (.step 3 (.step 55 (.step 3 (.run (.close 27))))) (.step 4 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 40))))) (.step 55 (.step 2 (.run (.close 43))))) (.step 68 (.step 2 (.run (.close 40))))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 55)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.step 43 (.step 2 (.run (.close 40))))))) (.step 4 (.step 71 (.step 43 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 23))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 23)))))) (.step 68 (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1104
namespace Part1105
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285375558177339704733503443469452133591701952638610104993895624554136318912504851344709566485803416154655175909629231104⟩
def references : Fin 2 → Box := ![Part1103.root, Part1104.root]
def proof : Enumeration.Proof 2 := (.split 44 0 (.split 33 0 (.split 48 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 41 0 (.split 50 0 (.split 59 0 (.split 69 0 (.split 58 0 (.split 4 0 (.split 6 0 (.split 18 0 (.split 19 0 (.split 10 0 (.step 3 (.step 2 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 31)))) (.step 55 (.step 2 (.run (.close 31))))) (.step 55 (.step 2 (.run (.close 31))))) (.step 68 (.step 43 (.run (.close 3))))) (.step 68 (.run (.close 4)))) (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 48))))) (.step 68 (.run (.close 31)))) (.step 55 (.run (.close 2)))) (.step 68 (.run (.close 40)))) (.step 68 (.run (.close 40)))) (.step 71 (.step 68 (.run (.close 40))))) (.step 68 (.step 63 (.run (.close 40))))) (.step 58 (.step 63 (.step 55 (.run (.close 43)))))) (.step 58 (.step 63 (.step 55 (.run (.close 23))))))) (.reuse 1)) (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 24 0 (.split 32 0 (.split 39 0 (.split 53 0 (.split 58 0 (.split 50 0 (.split 59 0 (.split 70 0 (.split 10 0 (.split 69 0 (.step 29 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 68 (.step 43 (.run (.close 3))))) (.step 68 (.run (.close 43)))) (.step 71 (.run (.close 29)))) (.step 55 (.run (.close 29)))) (.step 68 (.step 63 (.run (.close 55))))) (.step 68 (.run (.close 3)))) (.step 68 (.step 63 (.run (.close 40))))) (.step 71 (.step 68 (.run (.close 31))))) (.step 55 (.step 68 (.run (.close 40))))) (.step 58 (.step 63 (.step 55 (.run (.close 23)))))) (.step 68 (.step 4 (.run (.close 28))))) (.step 55 (.run (.close 29)))) (.step 68 (.step 4 (.run (.close 28))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1103.covered
  · exact Part1104.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1105
namespace Part1106
def root : Box := ⟨3196670515523576047707425257429017156664978684471758904094018012589639516290363853739460254577290936407626284536251831122490883437872269255296155648, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593577855263904202822433904035153700014596365528938484928292311007855732494086349464437768469628594207903167195069284352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 53 0 (.split 57 0 (.split 66 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 27 0 (.step 9 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 52)))) (.step 58 (.run (.close 52)))) (.step 58 (.run (.close 52)))) (.step 71 (.run (.close 52)))) (.step 58 (.step 68 (.run (.close 23))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 52)))) (.step 55 (.run (.close 52)))) (.step 55 (.step 68 (.run (.close 24))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 23))))) (.step 55 (.run (.close 68)))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))) (.step 4 (.step 68 (.step 58 (.run (.close 2)))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 58 (.step 2 (.run (.close 4))))))) (.step 58 (.step 63 (.run (.close 3))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 4 (.step 68 (.step 58 (.run (.close 2)))))) (.step 4 (.step 68 (.step 58 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1106
namespace Part1107
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593577855263904202822433904035153700014596365528938484928292311007855732494086349464437768469628594207903167195069284352⟩
def references : Fin 2 → Box := ![Part1105.root, Part1106.root]
def proof : Enumeration.Proof 2 := (.split 49 0 (.split 31 0 (.reuse 0) (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 35 0 (.split 4 0 (.split 42 0 (.split 72 0 (.split 10 0 (.split 16 0 (.split 30 0 (.step 2 (.run (.close 23))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 40))))) (.step 4 (.run (.close 40)))) (.step 43 (.run (.close 2)))) (.step 68 (.step 43 (.step 2 (.run (.close 40)))))) (.step 71 (.step 4 (.step 55 (.run (.close 43)))))) (.step 68 (.step 71 (.run (.close 23))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 68 (.run (.close 29)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 68 (.step 55 (.step 71 (.run (.close 23)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 55 (.step 71 (.run (.close 23)))))) (.step 68 (.step 4 (.run (.close 2)))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1105.covered
  · exact Part1106.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1107
namespace Part1108
def root : Box := ⟨2772669694120817322203801461037779213054247544909121673222628262826683551808612923297574225643594662669193086649508615515904409600, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593580317889291477477384671475159958990461035686070686077835834911953636858222720359855632110294155836474844219392917504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 74 0 (.split 70 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 49 0 (.split 12 0 (.step 28 (.run (.close 29))) (.step 71 (.step 2 (.run (.close 63))))) (.step 71 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 28)))) (.step 43 (.run (.close 40)))) (.step 43 (.run (.close 28)))) (.step 71 (.run (.close 2)))) (.step 55 (.step 58 (.step 63 (.run (.close 2)))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 71 (.step 43 (.run (.close 2))))) (.step 58 (.run (.close 43)))) (.step 71 (.step 43 (.step 2 (.run (.close 4)))))) (.step 71 (.step 43 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.run (.close 43))))) (.step 71 (.step 55 (.step 58 (.step 63 (.run (.close 2))))))) (.step 71 (.step 63 (.step 55 (.step 58 (.step 2 (.run (.close 4))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1108
namespace Part1109
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296396066581035339365207075236680242650933321309526418567935375775883201217326198177410628626460097902542848, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126698173687161137261200283880132438860189797760662878556290246414294035096493141509030919410122820239215640444928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 18 0 (.split 38 0 (.split 56 0 (.split 26 0 (.split 35 0 (.split 41 0 (.split 49 0 (.split 6 0 (.step 70 (.step 46 (.step 4 (.step 3 (.run (.close 58)))))) (.step 7 (.run (.close 2)))) (.step 52 (.run (.close 2)))) (.step 70 (.run (.close 2)))) (.step 18 (.step 71 (.run (.close 9))))) (.step 18 (.step 71 (.run (.close 9))))) (.step 7 (.step 18 (.run (.close 2))))) (.step 18 (.step 7 (.step 18 (.step 58 (.run (.close 2))))))) (.step 18 (.split 4 0 (.step 3 (.split 7 0 (.step 70 (.run (.close 9))) (.step 18 (.step 2 (.run (.close 4)))))) (.step 43 (.run (.close 18)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.run (.close 58))))) (.step 68 (.step 55 (.run (.close 24))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 71 (.run (.close 75))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 7))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1109
namespace Part1110
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986705602047002372549485474646007070260176455444739091252863182751173123815036401417927025822315409571840000, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506799746206380355817958592079673826011521134078382056490341224119536822762549025096154785180806361489523557269504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 12 0 (.split 4 0 (.split 10 0 (.split 39 0 (.step 2 (.run (.close 4))) (.step 4 (.step 2 (.run (.close 5))))) (.step 58 (.run (.close 2)))) (.step 71 (.step 64 (.step 2 (.run (.close 5)))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 40))))) (.step 68 (.step 55 (.run (.close 48))))) (.step 68 (.step 55 (.step 71 (.run (.close 58)))))) (.step 68 (.run (.close 64)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 71)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 40))))) (.step 68 (.step 71 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1110
namespace Part1111
def root : Box := ⟨2772669694120814859580762728965602278842130766530048192766299541285175124910982448911495716093046057721015855340665833804686950400, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186481560270615348548509760930964810211931410508354971574139704598248879804746258226589204480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 7 0 (.split 13 0 (.split 63 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 18 0 (.split 19 0 (.split 42 0 (.step 29 (.run (.close 2))) (.step 39 (.step 18 (.run (.close 29))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 28 (.run (.close 71)))) (.step 28 (.run (.close 71)))) (.step 28 (.run (.close 71)))) (.step 29 (.run (.close 2)))) (.step 28 (.run (.close 71)))) (.step 28 (.run (.close 71)))) (.step 29 (.run (.close 2)))) (.step 29 (.run (.close 2)))) (.step 29 (.run (.close 2)))) (.step 29 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.step 2 (.run (.close 4))))) (.step 43 (.run (.close 39)))) (.step 43 (.step 40 (.step 29 (.run (.close 23)))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 43 (.step 40 (.run (.close 2))))) (.step 40 (.step 43 (.run (.close 4))))) (.step 43 (.step 40 (.step 68 (.run (.close 54)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 7 (.step 58 (.run (.close 43)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 40 (.run (.close 7))))) (.step 40 (.step 43 (.run (.close 4))))) (.step 43 (.step 40 (.run (.close 29)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1111
namespace Part1112
def root : Box := ⟨2772669694120814859578414186382828445614243275226204494885492480265259392323635559764566696458801211133459728980269115235157147648, 5789234136395753406676424723379602756364389383221325178901979249676617072883442359369394353930870115606569193950663864097730486757841454530434590767771514635729772548062472868216850503455903740191568283660968545577762553856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 71 0 (.split 74 0 (.split 7 0 (.split 24 0 (.split 13 0 (.split 62 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 58 0 (.split 70 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.step 29 (.split 66 0 (.split 38 0 (.split 56 0 (.split 6 0 (.step 68 (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 29)))) (.step 43 (.step 18 (.run (.close 2))))) (.step 43 (.step 18 (.run (.close 2))))) (.step 55 (.step 43 (.run (.close 2)))))) (.step 40 (.split 4 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 68)))))) (.step 29 (.step 2 (.run (.close 68))))) (.step 55 (.step 43 (.step 2 (.run (.close 40)))))) (.step 43 (.step 55 (.step 40 (.run (.close 3)))))) (.step 43 (.step 55 (.step 40 (.step 2 (.run (.close 40))))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 18 (.step 55 (.step 3 (.run (.close 40)))))) (.step 18 (.step 55 (.step 3 (.run (.close 31)))))) (.step 18 (.step 68 (.step 3 (.run (.close 33)))))) (.step 18 (.step 68 (.step 3 (.run (.close 7)))))) (.step 18 (.step 68 (.step 31 (.run (.close 3)))))) (.step 3 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 10 (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 68))))) (.step 2 (.run (.close 58)))))) (.step 3 (.step 55 (.step 3 (.run (.close 31)))))) (.step 3 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 10 (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 68))))) (.step 2 (.run (.close 58)))))) (.step 55 (.step 40 (.step 23 (.run (.close 2)))))) (.step 18 (.step 40 (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1112
namespace Part1113
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560987695078382459957397495291812332958160965009466454156452442734308360091336704⟩
def references : Fin 6 → Box := ![Part1107.root, Part1108.root, Part1109.root, Part1110.root, Part1111.root, Part1112.root]
def proof : Enumeration.Proof 6 := (.split 29 0 (.split 36 0 (.split 62 0 (.split 67 0 (.split 38 0 (.split 26 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 31 0 (.split 32 0 (.split 33 0 (.split 41 0 (.split 53 0 (.split 70 0 (.step 29 (.step 71 (.split 14 0 (.split 16 0 (.split 17 0 (.split 7 0 (.split 13 0 (.step 43 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 68)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.run (.close 43)))))) (.step 4 (.step 71 (.run (.close 31))))) (.step 4 (.step 71 (.run (.close 28))))) (.step 4 (.step 71 (.step 43 (.run (.close 29)))))) (.step 4 (.step 71 (.step 43 (.step 55 (.run (.close 29))))))) (.step 4 (.step 71 (.run (.close 31))))) (.step 71 (.step 4 (.step 43 (.step 55 (.step 43 (.run (.close 2)))))))) (.step 4 (.step 71 (.run (.close 15))))) (.step 4 (.step 71 (.run (.close 28)))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.split 5 0 (.split 11 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.reuse 5) (.step 18 (.step 40 (.step 3 (.run (.close 31)))))) (.step 18 (.step 40 (.step 31 (.run (.close 29)))))) (.step 55 (.step 40 (.step 23 (.run (.close 2)))))) (.step 55 (.step 40 (.step 23 (.run (.close 2)))))) (.step 18 (.step 43 (.step 31 (.run (.close 28)))))) (.step 68 (.step 43 (.step 24 (.step 3 (.step 2 (.run (.close 23)))))))) (.step 18 (.step 43 (.step 31 (.run (.close 28)))))) (.step 18 (.step 31 (.step 43 (.run (.close 28)))))) (.step 68 (.step 43 (.step 24 (.step 3 (.step 2 (.run (.close 23)))))))) (.step 24 (.step 68 (.step 43 (.step 3 (.step 2 (.run (.close 23)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1107.covered
  · exact Part1108.covered
  · exact Part1109.covered
  · exact Part1110.covered
  · exact Part1111.covered
  · exact Part1112.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1113
namespace Part1114
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449278790096381566445376554139648, 5653543574944809739115343129751252151564818225746450259442063143580463561326105561953801888244548661919791353747678997007479838390611245507194886707366684611976162351721214048572750442583227341004687821204897168785145856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 13 0 (.split 62 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 58 0 (.split 49 0 (.split 6 0 (.split 70 0 (.split 12 0 (.split 50 0 (.split 54 0 (.split 59 0 (.split 69 0 (.split 4 0 (.split 10 0 (.split 16 0 (.step 2 (.run (.close 23))) (.step 43 (.run (.close 2)))) (.split 18 0 (.split 19 0 (.step 3 (.run (.close 13))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 29 0 (.split 31 0 (.step 43 (.run (.close 2))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 40))))) (.step 18 (.step 2 (.run (.close 68))))) (.step 18 (.step 68 (.run (.close 2))))) (.split 69 0 (.step 40 (.step 15 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 18 (.step 55 (.run (.close 52))))) (.split 16 0 (.split 17 0 (.step 15 (.run (.close 2))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 18 (.step 68 (.step 18 (.run (.close 2)))))) (.step 3 (.split 16 0 (.split 17 0 (.step 15 (.run (.close 2))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))))) (.step 18 (.step 55 (.step 18 (.run (.close 2)))))) (.step 18 (.step 55 (.step 3 (.run (.close 40)))))) (.step 18 (.step 55 (.step 3 (.run (.close 52)))))) (.step 18 (.step 68 (.step 3 (.run (.close 64)))))) (.step 3 (.step 68 (.step 64 (.run (.close 2)))))) (.step 18 (.step 68 (.step 31 (.run (.close 3)))))) (.step 3 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 16 (.step 71 (.run (.close 28)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 68))))) (.step 2 (.run (.close 58)))))) (.step 3 (.step 55 (.step 52 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1114
namespace Part1115
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560987695078382459957397495291812332958160965009466455394392482019688634990460928⟩
def references : Fin 2 → Box := ![Part1113.root, Part1114.root]
def proof : Enumeration.Proof 2 := (.split 9 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 7 0 (.reuse 1) (.step 3 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 16 (.step 71 (.run (.close 28)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 58)))))) (.step 40 (.step 55 (.step 23 (.run (.close 2)))))) (.step 18 (.step 40 (.step 3 (.run (.close 2)))))) (.step 18 (.step 40 (.step 31 (.run (.close 29)))))) (.step 18 (.step 40 (.step 29 (.run (.close 2)))))) (.step 40 (.step 55 (.step 23 (.step 40 (.run (.close 2))))))) (.step 40 (.step 55 (.step 23 (.step 40 (.run (.close 2))))))) (.step 18 (.step 43 (.step 31 (.run (.close 28)))))) (.step 43 (.step 68 (.step 24 (.step 3 (.step 2 (.run (.close 23)))))))) (.step 18 (.step 31 (.step 43 (.run (.close 28)))))) (.step 18 (.step 31 (.step 43 (.step 28 (.run (.close 2))))))) (.step 3 (.step 68 (.step 43 (.step 24 (.step 2 (.run (.close 23)))))))) (.step 3 (.step 68 (.step 43 (.step 24 (.step 2 (.run (.close 23)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1113.covered
  · exact Part1114.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1115
namespace Part1116
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406671525840073512305702396937558630707244719933604933500451070623949290679556854271969686225804160680934083919987524173889666507205612847631262782353238793047470225026011977346490743595196811842933800042496⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 39 0 (.split 58 0 (.split 74 0 (.split 59 0 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 4))) (.split 16 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 38 0 (.split 42 0 (.split 46 0 (.step 18 (.run (.close 2))) (.step 58 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 58 (.run (.close 2))))) (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 54 0 (.split 72 0 (.split 5 0 (.split 11 0 (.split 32 0 (.split 53 0 (.step 68 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 6 0 (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 5 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.step 68 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1116
namespace Part1117
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169648139344787960032346849242165387555366412304039499906999923170822215300637612969563143767672577249297810808485030118341552912603458946669122406780320661090707308244468441278844131340189696⟩
def references : Fin 1 → Box := ![Part1116.root]
def proof : Enumeration.Proof 1 := (.split 67 0 (.split 24 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 7 0 (.step 43 (.step 5 (.run (.close 18)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.split 48 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 24 0 (.split 39 0 (.step 55 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 4 (.run (.close 68)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 4 (.step 71 (.run (.close 68))))) (.step 68 (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1116.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1117
namespace Part1118
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169648139344787960032346849242165387555366412304039499906999923170822215300637612969563143767672577249297810808485030118341552912603458946669122406781714457665615472192023349490499283109019648⟩
def references : Fin 1 → Box := ![Part1117.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 14 0 (.reuse 0) (.split 12 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 5 0 (.split 7 0 (.split 11 0 (.split 53 0 (.split 13 0 (.split 18 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 22 0 (.step 23 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 23)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 68 (.run (.close 2)))) (.step 4 (.step 71 (.step 2 (.run (.close 5)))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.step 63 (.step 4 (.run (.close 2)))))) (.step 4 (.step 68 (.step 2 (.run (.close 4))))))) (.split 12 0 (.split 54 0 (.split 72 0 (.split 7 0 (.split 32 0 (.split 70 0 (.split 13 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 47 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 63 (.step 23 (.run (.close 24))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 4 (.step 58 (.run (.close 23))))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))) (.step 4 (.step 68 (.step 2 (.run (.close 4)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1117.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1118
namespace Part1119
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169648139344787960032346849242165387555369685694647396048869936360519042899789829611609186832462060542702942918615920879164881871105163011877741687131778268372765138802950534646889317820006400⟩
def references : Fin 1 → Box := ![Part1118.root]
def proof : Enumeration.Proof 1 := (.split 50 0 (.split 30 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 12 0 (.split 18 0 (.split 74 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 71 (.step 4 (.step 2 (.run (.close 4)))))) (.step 71 (.step 4 (.step 2 (.run (.close 5)))))) (.step 71 (.step 4 (.step 68 (.step 2 (.run (.close 5))))))) (.step 68 (.step 71 (.step 4 (.step 2 (.run (.close 5))))))) (.step 68 (.step 71 (.run (.close 58))))) (.step 68 (.step 71 (.run (.close 8))))) (.step 71 (.step 68 (.step 4 (.step 2 (.run (.close 4))))))) (.step 71 (.run (.close 58)))) (.step 71 (.run (.close 58)))) (.step 71 (.run (.close 58)))) (.step 71 (.step 55 (.run (.close 2))))) (.step 55 (.step 71 (.run (.close 2))))) (.step 55 (.step 71 (.run (.close 2)))))) (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 5 (.step 9 (.step 55 (.run (.close 2))))) (.step 58 (.run (.close 3)))) (.step 68 (.step 2 (.run (.close 4))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 48)))) (.step 4 (.run (.close 48)))) (.step 4 (.run (.close 48)))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 58 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.step 58 (.run (.close 2)))))) (.step 58 (.step 48 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1118.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1119
namespace Part1120
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506799746204140611075780787869116383732761941194593476546599871225397582221792576734107607448313779343779377971200⟩
def references : Fin 1 → Box := ![Part1119.root]
def proof : Enumeration.Proof 1 := (.split 62 0 (.split 49 0 (.reuse 0) (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 7 0 (.step 3 (.step 9 (.step 27 (.run (.close 2))))) (.step 58 (.step 4 (.run (.close 9))))) (.step 58 (.step 68 (.run (.close 9))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 27))))) (.step 58 (.run (.close 27)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 48 (.run (.close 2))))) (.step 58 (.step 63 (.step 2 (.run (.close 4)))))) (.step 58 (.step 48 (.step 2 (.run (.close 4))))))) (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 74 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 24 0 (.split 39 0 (.step 10 (.step 4 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 65)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1119.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1120
namespace Part1121
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506799746204140611075780789858409329371908509816122469133883231627222185411183446497231165621179996795409583308800⟩
def references : Fin 1 → Box := ![Part1120.root]
def proof : Enumeration.Proof 1 := (.split 10 0 (.split 29 0 (.reuse 0) (.split 30 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 12 0 (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 2)))))) (.split 29 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 49 0 (.split 54 0 (.step 2 (.run (.close 5))) (.step 58 (.run (.close 18)))) (.step 71 (.step 58 (.run (.close 4))))) (.step 58 (.run (.close 18)))) (.step 58 (.run (.close 18)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 7)))) (.step 58 (.step 68 (.run (.close 4))))) (.step 58 (.step 68 (.run (.close 4))))) (.step 58 (.step 68 (.run (.close 5))))) (.step 68 (.run (.close 7)))) (.step 68 (.run (.close 7)))) (.step 68 (.run (.close 7)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 55 (.step 71 (.step 43 (.step 2 (.run (.close 4))))))) (.step 55 (.step 71 (.step 43 (.step 2 (.run (.close 4))))))) (.step 18 (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1120.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1121
namespace Part1122
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506799746204140611075780789858409329371908509816122469133883231627222185411183446497232403561219282176783994060800⟩
def references : Fin 1 → Box := ![Part1121.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 9 0 (.reuse 0) (.split 10 0 (.split 30 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 12 0 (.split 14 0 (.step 2 (.run (.close 4))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 2)))))) (.split 9 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 5 0 (.split 6 0 (.split 8 0 (.split 12 0 (.split 11 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 10 0 (.split 16 0 (.split 35 0 (.step 10 (.run (.close 7))) (.step 71 (.run (.close 2)))) (.step 55 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 58 (.step 68 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 5))))) (.step 2 (.run (.close 7)))) (.step 58 (.step 63 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 48)))) (.step 58 (.step 68 (.run (.close 18))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 48)))) (.step 68 (.run (.close 7)))) (.step 2 (.run (.close 48)))) (.step 68 (.step 63 (.run (.close 7))))) (.step 68 (.step 63 (.run (.close 7))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.step 71 (.run (.close 18))))) (.step 2 (.step 71 (.run (.close 18))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1121.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1122
namespace Part1123
def root : Box := ⟨2772669694120814859578414186382828445614241285933258857548175253069332358533571798700712067275274959678185969458805815225297666048, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560989504329776793022950988588453093706721172352976856028205598544438758633111552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 49 0 (.split 50 0 (.split 4 0 (.split 38 0 (.split 46 0 (.split 6 0 (.step 28 (.step 29 (.run (.close 2)))) (.step 71 (.run (.close 29)))) (.step 16 (.run (.close 28)))) (.step 16 (.run (.close 28)))) (.step 58 (.run (.close 28)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 16)))) (.step 71 (.step 43 (.run (.close 28))))) (.step 5 (.step 43 (.run (.close 28))))) (.step 5 (.step 43 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 5 (.step 43 (.step 40 (.run (.close 2)))))) (.step 5 (.step 43 (.run (.close 28))))) (.step 71 (.step 55 (.step 43 (.run (.close 2)))))) (.step 43 (.step 71 (.run (.close 2))))) (.step 71 (.step 55 (.step 43 (.run (.close 2)))))) (.step 71 (.step 43 (.step 5 (.step 2 (.run (.close 43))))))) (.step 43 (.step 71 (.step 5 (.step 2 (.run (.close 43))))))) (.step 71 (.step 55 (.step 58 (.step 43 (.step 2 (.run (.close 5))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1123
namespace Part1124
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560989504329776793022950988588453093706721172352976856028205598544438758633111552⟩
def references : Fin 2 → Box := ![Part1122.root, Part1123.root]
def proof : Enumeration.Proof 2 := (.split 34 0 (.split 36 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 49 0 (.split 50 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 6 0 (.step 28 (.step 29 (.run (.close 2)))) (.step 71 (.run (.close 29)))) (.step 28 (.run (.close 2)))) (.step 28 (.run (.close 2)))) (.step 28 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 71))))) (.step 58 (.run (.close 2)))) (.step 63 (.step 58 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.step 2 (.run (.close 4)))))) (.step 63 (.step 58 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 43 (.step 5 (.run (.close 2))))) (.step 43 (.step 5 (.run (.close 2))))) (.step 63 (.step 58 (.step 2 (.run (.close 4)))))) (.step 43 (.step 71 (.run (.close 2))))) (.step 63 (.step 58 (.step 4 (.run (.close 2)))))) (.step 71 (.step 43 (.step 5 (.run (.close 2)))))) (.step 43 (.step 71 (.step 5 (.run (.close 2))))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1122.covered
  · exact Part1123.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1124
namespace Part1125
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560989504329776793022950988588453093706721172352976856028205598544438758633111552⟩
def references : Fin 6 → Box := ![Part1081.root, Part1089.root, Part1090.root, Part1099.root, Part1115.root, Part1124.root]
def proof : Enumeration.Proof 6 := (.split 25 0 (.split 34 0 (.split 5 0 (.split 11 0 (.reuse 0) (.split 4 0 (.split 9 0 (.reuse 1) (.split 10 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 67 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 62 0 (.split 69 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 8 0 (.split 14 0 (.step 2 (.run (.close 58))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 24 (.step 68 (.step 18 (.step 63 (.step 68 (.run (.close 3)))))))) (.step 24 (.step 68 (.step 43 (.step 18 (.step 63 (.step 68 (.run (.close 3))))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.run (.close 2)))))) (.reuse 2))) (.reuse 3)) (.reuse 4)) (.reuse 5))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1081.covered
  · exact Part1089.covered
  · exact Part1090.covered
  · exact Part1099.covered
  · exact Part1115.covered
  · exact Part1124.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1125
namespace Part1126
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243485986584588438705700382864198799891279783832873498196787219362694251252813784328756788637931197812276756518484705920666964019562278874388007789525367373642992895385423568935664039351889984734668490014720⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 30 0 (.split 34 0 (.split 12 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.split 35 0 (.split 72 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 35 0 (.split 72 0 (.split 36 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 27 0 (.split 31 0 (.split 32 0 (.split 33 0 (.split 41 0 (.split 53 0 (.split 22 0 (.step 4 (.step 2 (.run (.close 71)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 26 0 (.split 17 0 (.split 35 0 (.split 72 0 (.split 12 0 (.split 22 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 26 0 (.split 35 0 (.split 72 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 72 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 17 0 (.split 22 0 (.split 7 0 (.split 34 0 (.step 4 (.step 2 (.run (.close 5)))) (.step 71 (.step 4 (.step 71 (.run (.close 68)))))) (.step 5 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1126
namespace Part1127
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243485986584588438705700382864198799891279783832873498196787219362694251252813784328756788637931197812276756518484705920666964019562278874388007789525367373644454398416551046762031671739514479409476191387648⟩
def references : Fin 1 → Box := ![Part1126.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 16 0 (.split 14 0 (.reuse 0) (.split 17 0 (.split 22 0 (.split 74 0 (.split 7 0 (.split 34 0 (.step 4 (.step 2 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 15))))) (.step 5 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 12 0 (.split 17 0 (.step 2 (.run (.close 5))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 7 0 (.split 34 0 (.step 4 (.run (.close 2))) (.step 71 (.step 4 (.step 71 (.run (.close 68)))))) (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1126.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1127
namespace Part1128
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272278180592461356316119079004930048, 5789234131009374243485986584588438705700382864198799891279783832873498196787219362694251252813784328756788637931197812276756518484705920666964019562278874388007789525367373644454398416551046763299322339743861732477501440000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 47 0 (.split 57 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 39 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 64 (.run (.close 2)))) (.step 63 (.step 64 (.run (.close 18))))) (.step 63 (.step 72 (.step 64 (.run (.close 18)))))) (.step 63 (.step 65 (.step 64 (.run (.close 18)))))) (.step 31 (.step 16 (.run (.close 64))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1128
namespace Part1129
def root : Box := ⟨4898883310657342441196954343935776394038937435041614979870160492432575754684773045338455147274114335740136311283395281868909035564178663322436663885140058391062942067558153833567115414432112578549252096, 5653543574944809739110559064018183993757903128166895795175892990978402816827315398733783971864169488724488927271380944973580823051419447791782498987386157716689056531379123752342583798770236342012657214446647021454491648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.split 10 0 (.step 2 (.run (.close 4))) (.step 64 (.run (.close 3)))) (.step 46 (.run (.close 2)))) (.step 70 (.run (.close 2)))) (.step 76 (.step 65 (.step 2 (.run (.close 4)))))) (.step 72 (.step 54 (.step 70 (.step 46 (.step 18 (.step 70 (.step 2 (.run (.close 4)))))))))) (.step 64 (.step 15 (.step 5 (.run (.close 2)))))) (.step 76 (.step 52 (.step 68 (.run (.close 70)))))) (.split 53 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 38 0 (.step 52 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 34 0 (.split 35 0 (.split 53 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 38 0 (.step 52 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 4 (.step 2 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 26 0 (.step 70 (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 70))))) (.split 26 0 (.step 72 (.step 54 (.step 70 (.step 4 (.step 2 (.run (.close 5))))))) (.step 68 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1129
namespace Part1130
def root : Box := ⟨4898883310657342441196954343935776394038937435041614979870160492432575754684773045338455147274114335740136311283395281868909035564178663322436663885140058391062942067558153833567115414432112578549252096, 5789234131009374243490885467899096048137330714600197666346783047397775367396561843205963574170095203285123317467757005936970092804370364108530963224208651783686959451887981740146596099391306185562114750758501572642263269376⟩
def references : Fin 1 → Box := ![Part1129.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 16 0 (.reuse 0) (.split 26 0 (.step 65 (.split 35 0 (.step 65 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 24 0 (.step 70 (.split 17 0 (.step 64 (.step 73 (.step 2 (.run (.close 4))))) (.step 63 (.step 23 (.step 2 (.run (.close 4))))))) (.step 63 (.run (.close 2)))) (.step 4 (.step 68 (.step 2 (.run (.close 5)))))) (.step 4 (.step 68 (.step 2 (.run (.close 5)))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 2 (.run (.close 5))))))) (.step 68 (.run (.close 55))))) (.step 68 (.run (.close 63))))) (.split 26 0 (.split 35 0 (.step 64 (.step 4 (.step 68 (.step 2 (.run (.close 48)))))) (.step 4 (.run (.close 55)))) (.step 2 (.run (.close 4))))) (.split 26 0 (.step 70 (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 46))))) (.split 34 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 11 0 (.step 52 (.run (.close 2))) (.step 4 (.run (.close 31)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 71))))) (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 14 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 11 0 (.step 52 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 4 (.run (.close 46)))) (.step 4 (.run (.close 46)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1129.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1130
namespace Part1131
def root : Box := ⟨4898883310657342441196954343935776394038937435041614979870160492432575754684773045338455147274114335740136311283395281868909035564178663322436663885140058391062942067558153833567115414432112578549252096, 5789234131009374243490885467899096048137330714600201530884306064656120062748452778244867573180100879002403049740006694486440271074431044588105997386782601462592832246745666421890210792684332640219947594030207127473748967424⟩
def references : Fin 1 → Box := ![Part1130.root]
def proof : Enumeration.Proof 1 := (.split 9 0 (.split 46 0 (.split 47 0 (.split 57 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 64 (.step 73 (.split 16 0 (.step 76 (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 55)))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 65 (.step 64 (.step 55 (.step 30 (.step 71 (.step 76 (.step 2 (.run (.close 4))))))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48))))) (.split 47 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 64 (.step 31 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 64))))) (.split 6 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 14 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 33 0 (.split 41 0 (.step 64 (.step 71 (.step 48 (.step 18 (.run (.close 2)))))) (.step 2 (.run (.close 70)))) (.step 2 (.step 4 (.run (.close 18))))) (.step 2 (.step 71 (.run (.close 18))))) (.step 2 (.run (.close 70)))) (.step 2 (.step 71 (.run (.close 18))))) (.step 2 (.step 71 (.run (.close 18))))) (.step 3 (.run (.close 63)))) (.step 3 (.run (.close 52)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 52)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1130.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1131
namespace Part1132
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243490885467899096048137330714600201530884306064656120062748452778244867573180100879002403049740006694486440271074431044588105997386782601462592832246745666421890210792684332640219947594030208253373655810048⟩
def references : Fin 3 → Box := ![Part1127.root, Part1128.root, Part1131.root]
def proof : Enumeration.Proof 3 := (.split 5 0 (.split 67 0 (.split 10 0 (.split 6 0 (.reuse 0) (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 9 0 (.split 8 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 24 0 (.split 16 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 7 0 (.split 17 0 (.split 22 0 (.step 15 (.step 2 (.run (.close 71)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 5)))) (.step 71 (.step 4 (.run (.close 63))))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 71 (.step 4 (.run (.close 63))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.reuse 1)) (.reuse 2)) (.split 6 0 (.split 12 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 54 0 (.split 38 0 (.split 7 0 (.split 49 0 (.split 9 0 (.split 18 0 (.split 19 0 (.step 30 (.split 24 0 (.step 48 (.run (.close 2))) (.step 2 (.run (.close 48))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.step 2 (.run (.close 23)))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 4 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1127.covered
  · exact Part1128.covered
  · exact Part1131.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1132
namespace Part1133
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243490885467899096048137330714600201530884306064656120062748452778244867573180100879002403049740006694486440271074431044588105997386782601462592832246745666421890210792684332640219947594030208254473167437824⟩
def references : Fin 1 → Box := ![Part1132.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.reuse 0) (.split 9 0 (.split 29 0 (.split 18 0 (.split 19 0 (.split 14 0 (.split 74 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 11 0 (.split 53 0 (.split 38 0 (.split 72 0 (.split 16 0 (.split 17 0 (.split 36 0 (.step 46 (.split 54 0 (.split 67 0 (.step 10 (.run (.close 27))) (.step 70 (.step 71 (.run (.close 52))))) (.step 71 (.step 18 (.run (.close 2)))))) (.step 72 (.step 7 (.run (.close 2))))) (.step 63 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 48)))) (.step 18 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.step 31 (.run (.close 68))))) (.step 2 (.step 31 (.run (.close 68))))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 18 (.step 7 (.run (.close 2))))) (.step 31 (.step 7 (.run (.close 4))))) (.step 31 (.step 7 (.run (.close 4))))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.run (.close 13)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1132.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1133
namespace Part1134
def root : Box := ⟨4355331541097490209254623293730242744102663565361661770238214602937430005718566804645275602278316579560268318362391787906456571876557824986198038231990155864036807631811627967890218549248, 5653543574944809739110559064018188344840340283126832797805498327146093252745070857483297831716225343710183579622642013662977649870408126908203814701923548674805338933338152960995140685926706728029917002501223039943835648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 10 0 (.split 34 0 (.split 36 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 65 (.run (.close 2)))) (.step 72 (.step 2 (.run (.close 4))))) (.step 64 (.run (.close 2)))) (.step 64 (.run (.close 2)))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.split 26 0 (.split 35 0 (.step 65 (.step 64 (.step 65 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63))))) (.split 26 0 (.split 35 0 (.step 72 (.step 64 (.step 65 (.step 64 (.step 2 (.run (.close 4))))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63))))) (.split 26 0 (.split 35 0 (.step 65 (.step 68 (.step 65 (.step 4 (.step 2 (.run (.close 5))))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1134
namespace Part1135
def root : Box := ⟨4355331541097490209254623293730242744102663565361661770238214602937430005718566804645275602278316579560268318362391787906456571876557824986198038231990155864036807631811627967890218549248, 5789234131009374243490885467899096052488413151755157603349412652733943057832479598664713088029947259140109012120108267005659489631189352787647384539923189174645075734289940767893747018947559737744447177830274254904726913024⟩
def references : Fin 1 → Box := ![Part1134.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 74 0 (.reuse 0) (.split 35 0 (.split 72 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 6 0 (.step 30 (.step 62 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 64)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 56 0 (.split 6 0 (.step 30 (.step 15 (.step 2 (.run (.close 63))))) (.step 2 (.run (.close 15)))) (.step 2 (.run (.close 5)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.step 2 (.step 63 (.run (.close 55))))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 46))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1134.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1135
namespace Part1136
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676419939313869692557664905278705561440342684860182702574861324664923849874341792288359586176538827114385984569321251411835599695766071499792601724644089807129274287495823425817993640316078544682167042048⟩
def references : Fin 2 → Box := ![Part1133.root, Part1135.root]
def proof : Enumeration.Proof 2 := (.split 71 0 (.split 62 0 (.split 25 0 (.reuse 0) (.split 34 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 74 0 (.split 16 0 (.split 35 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 72 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.step 55 (.step 2 (.run (.close 23))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 58 (.step 5 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 58 (.step 2 (.run (.close 23)))))) (.reuse 1)) (.split 26 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 72 0 (.split 4 0 (.split 10 0 (.split 14 0 (.split 74 0 (.split 30 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 72))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 63 (.step 71 (.step 2 (.run (.close 48)))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 4 (.step 2 (.run (.close 71)))))) (.step 71 (.step 4 (.step 2 (.run (.close 71)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1133.covered
  · exact Part1135.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1136
namespace Part1137
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676424723379602756368638487163863180229018976102157919240839091672297498624699523294458819000570867038418878858959654853164839908485313420763876180426685796169738948019391087807173938415967553856968065024⟩
def references : Fin 1 → Box := ![Part1136.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 6 0 (.split 12 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 26 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 35 0 (.split 71 0 (.step 30 (.split 9 0 (.step 70 (.run (.close 2))) (.step 2 (.run (.close 63))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 48)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.run (.close 71)))) (.step 71 (.step 68 (.step 2 (.run (.close 4)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 63)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1136.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1137
namespace Part1138
def root : Box := ⟨4455512664750617552341058662897343166715062100854863623461631061483810629520562475491806536185842065867691107374174348840933175598410708017449569820607159065491751491041074327032889130090496, 5789234136395753406676424723384169652494676329057522556103865459117798113791551761524683897385292059472572973611087039530216052379245893493118877279084391469923456086626108626104031203432436297320083383312290743356043034624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 12 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 64))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 63 (.step 40 (.step 5 (.step 71 (.step 2 (.run (.close 48)))))))) (.step 71 (.step 4 (.step 68 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 40 (.step 68 (.run (.close 63)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1138
namespace Part1139
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676424723384169652494676329057522556103865459117798113791551761524683897385292059472572973611087039530216052379245893493118877279084391469923456086626108626104031203432436297320083383312290743356043034624⟩
def references : Fin 2 → Box := ![Part1137.root, Part1138.root]
def proof : Enumeration.Proof 2 := (.split 63 0 (.split 64 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 12 0 (.split 71 0 (.split 72 0 (.split 14 0 (.split 74 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 4))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 2 (.run (.close 48)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 63 (.step 5 (.step 71 (.step 2 (.run (.close 48))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.step 2 (.run (.close 4)))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 4 (.step 71 (.step 40 (.step 68 (.run (.close 63)))))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1137.covered
  · exact Part1138.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1139
namespace Part1140
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234213377523441069802766777392788128358717350396752650078502650823211235543576392729172118075191030363557703942978831287970031641349324800⟩
def references : Fin 1 → Box := ![Part1139.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 6 0 (.split 12 0 (.split 42 0 (.split 54 0 (.split 4 0 (.split 24 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.run (.close 9)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 63))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1139.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1140
namespace Part1141
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5783586103091957808496987250214686792406378902833960374507899534368857180682313012842877255319085414405159289425956398490277498727068883741708383288422793979998999109642293688065072650838956544680975496183503555313778294784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 38 0 (.split 56 0 (.split 26 0 (.split 27 0 (.split 59 0 (.split 72 0 (.split 74 0 (.split 70 0 (.step 46 (.step 54 (.step 61 (.step 27 (.run (.close 4)))))) (.split 6 0 (.split 8 0 (.step 70 (.step 61 (.step 63 (.run (.close 4))))) (.step 63 (.run (.close 27)))) (.step 3 (.run (.close 7))))) (.split 22 0 (.split 41 0 (.step 62 (.step 68 (.run (.close 27)))) (.step 68 (.run (.close 62)))) (.step 68 (.run (.close 62))))) (.step 70 (.step 68 (.run (.close 9))))) (.step 62 (.split 6 0 (.split 8 0 (.step 54 (.step 61 (.step 62 (.run (.close 9))))) (.step 61 (.run (.close 46)))) (.step 57 (.run (.close 46)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 61 (.step 27 (.run (.close 11)))) (.step 71 (.step 55 (.run (.close 4))))) (.step 55 (.run (.close 46)))) (.step 71 (.step 4 (.step 63 (.run (.close 4)))))) (.step 55 (.run (.close 46))))) (.split 14 0 (.split 74 0 (.step 46 (.step 68 (.run (.close 9)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 8 0 (.split 14 0 (.split 16 0 (.step 54 (.step 68 (.step 4 (.run (.close 58))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 5))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 56 0 (.split 17 0 (.split 22 0 (.split 26 0 (.step 54 (.step 4 (.step 71 (.run (.close 5))))) (.step 71 (.run (.close 3)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 5 (.step 58 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1141
namespace Part1142
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5783586103091957808496987250214686792406378902833960374507899537883633582669185186913610464448758741647110163099328768100242789830066993641308281976982581392996796811511301761264020526052759209010745575044839049012319354880⟩
def references : Fin 1 → Box := ![Part1141.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 11 0 (.split 53 0 (.split 25 0 (.reuse 0) (.split 14 0 (.split 16 0 (.split 38 0 (.split 56 0 (.step 46 (.split 74 0 (.step 46 (.run (.close 4))) (.step 68 (.run (.close 4))))) (.step 5 (.step 58 (.run (.close 2))))) (.step 5 (.step 58 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.split 25 0 (.split 38 0 (.split 56 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 61 (.run (.close 2))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.split 25 0 (.split 38 0 (.split 56 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 16 0 (.split 17 0 (.step 61 (.step 31 (.run (.close 27)))) (.step 31 (.run (.close 54)))) (.step 31 (.step 7 (.step 63 (.run (.close 4)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 42 0 (.split 11 0 (.split 16 0 (.step 27 (.run (.close 2))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 27)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1141.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1142
namespace Part1143
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5783586103091957808496987250214686792406378902833960374507899537883633582669185186913610464448758741647110163099328768100242789830066993641308281976982581392996796811511301761264020526052759210278396175273068451608534188032⟩
def references : Fin 1 → Box := ![Part1142.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 10 0 (.reuse 0) (.split 5 0 (.split 8 0 (.split 25 0 (.split 26 0 (.split 11 0 (.split 38 0 (.split 14 0 (.split 35 0 (.split 67 0 (.split 22 0 (.step 54 (.step 46 (.split 12 0 (.split 17 0 (.step 61 (.step 31 (.run (.close 68)))) (.step 24 (.step 31 (.run (.close 11))))) (.step 43 (.step 24 (.run (.close 4))))))) (.step 7 (.step 54 (.step 48 (.run (.close 24)))))) (.step 54 (.step 70 (.step 61 (.step 7 (.run (.close 3))))))) (.step 7 (.step 52 (.step 68 (.step 54 (.step 4 (.run (.close 43)))))))) (.step 7 (.step 52 (.step 68 (.step 54 (.step 63 (.run (.close 11)))))))) (.step 7 (.step 64 (.split 14 0 (.step 54 (.step 55 (.step 54 (.step 33 (.step 71 (.run (.close 23))))))) (.step 68 (.run (.close 5))))))) (.step 7 (.step 64 (.split 38 0 (.split 35 0 (.split 72 0 (.split 14 0 (.step 48 (.step 54 (.run (.close 31)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 55))))))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 4)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31))))) (.split 5 0 (.split 8 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 11 0 (.step 54 (.split 67 0 (.split 41 0 (.step 7 (.run (.close 27))) (.step 9 (.step 31 (.run (.close 2))))) (.step 70 (.step 7 (.run (.close 27)))))) (.step 7 (.run (.close 27)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 4)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1142.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1143
namespace Part1144
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223674523533435127907585386672906575011573125160405941591560804154570333043065915249633846288711680⟩
def references : Fin 1 → Box := ![Part1143.root]
def proof : Enumeration.Proof 1 := (.split 73 0 (.split 33 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 56 0 (.split 5 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 53 0 (.split 72 0 (.split 54 0 (.split 4 0 (.step 36 (.run (.close 11))) (.step 27 (.run (.close 2)))) (.step 3 (.run (.close 23)))) (.step 68 (.run (.close 27)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 72 (.step 31 (.run (.close 2)))))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 3 (.run (.close 18))))) (.step 55 (.step 3 (.run (.close 29))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 46))))) (.split 5 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 16 0 (.split 22 0 (.split 25 0 (.split 38 0 (.split 59 0 (.split 72 0 (.step 54 (.step 70 (.step 46 (.step 54 (.run (.close 18)))))) (.step 71 (.run (.close 70)))) (.step 62 (.run (.close 2)))) (.step 58 (.step 65 (.step 54 (.step 5 (.step 2 (.run (.close 58)))))))) (.step 58 (.step 54 (.run (.close 46))))) (.step 55 (.step 62 (.run (.close 2))))) (.step 55 (.step 63 (.step 65 (.step 54 (.step 2 (.run (.close 23)))))))) (.step 55 (.step 63 (.step 5 (.run (.close 27)))))) (.step 55 (.step 3 (.run (.close 8))))) (.step 55 (.step 3 (.run (.close 8))))) (.step 55 (.step 3 (.run (.close 8))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1143.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1144
namespace Part1145
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521028977982484251848051457388609969372266496, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725561291506214810041864041055510282816691858155683370726404850705160470528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 31 0 (.split 33 0 (.split 25 0 (.split 41 0 (.split 24 0 (.split 26 0 (.split 49 0 (.split 35 0 (.split 6 0 (.step 54 (.step 46 (.split 67 0 (.step 71 (.run (.close 10))) (.step 70 (.run (.close 18)))))) (.step 3 (.step 71 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 58))))) (.step 52 (.run (.close 2)))) (.step 71 (.run (.close 46)))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 18)))) (.step 58 (.step 46 (.run (.close 2))))) (.step 3 (.run (.close 54)))) (.step 3 (.step 40 (.run (.close 2))))) (.step 55 (.step 5 (.run (.close 27))))) (.step 55 (.step 70 (.step 3 (.step 48 (.run (.close 4))))))) (.step 55 (.step 72 (.step 31 (.run (.close 54)))))) (.step 55 (.step 65 (.split 54 0 (.split 17 0 (.split 67 0 (.step 5 (.step 2 (.run (.close 63)))) (.step 54 (.step 70 (.run (.close 2))))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 9))))))) (.step 55 (.step 5 (.step 3 (.run (.close 63)))))) (.step 3 (.run (.close 54)))) (.step 55 (.step 3 (.step 8 (.run (.close 2)))))) (.step 55 (.step 5 (.step 3 (.run (.close 63)))))) (.step 3 (.run (.close 46))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1145
namespace Part1146
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725561291506214810041864041055510282816691858155683370726404850705160470528⟩
def references : Fin 2 → Box := ![Part1144.root, Part1145.root]
def proof : Enumeration.Proof 2 := (.split 13 0 (.split 31 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 54 0 (.split 56 0 (.split 72 0 (.split 73 0 (.split 5 0 (.split 11 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 53 0 (.split 4 0 (.step 36 (.run (.close 27))) (.step 27 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 68 (.step 31 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 54 (.step 31 (.run (.close 2)))))) (.step 68 (.step 31 (.run (.close 2))))) (.step 68 (.step 31 (.step 64 (.step 31 (.run (.close 2))))))) (.step 3 (.step 43 (.run (.close 23))))) (.step 68 (.step 3 (.run (.close 43))))) (.step 68 (.run (.close 54)))) (.step 3 (.run (.close 54)))) (.step 68 (.step 3 (.run (.close 18))))) (.step 55 (.step 3 (.run (.close 18))))) (.step 55 (.step 3 (.run (.close 29))))) (.step 3 (.run (.close 7)))) (.step 3 (.step 4 (.step 43 (.run (.close 24)))))) (.step 3 (.run (.close 46))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1144.covered
  · exact Part1145.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1146
namespace Part1147
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914681774625749731303494989693486596873216129345337240200528970873355370496, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725563016942801507682810899744475852073054970932926414503635262053627723776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 31 0 (.split 33 0 (.split 41 0 (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 38 0 (.split 56 0 (.split 74 0 (.split 32 0 (.split 39 0 (.split 4 0 (.split 10 0 (.step 62 (.step 3 (.step 57 (.run (.close 29))))) (.step 18 (.step 54 (.step 18 (.run (.close 2)))))) (.step 9 (.run (.close 2)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31)))) (.step 68 (.run (.close 62)))) (.step 18 (.run (.close 57)))) (.step 68 (.step 18 (.step 2 (.run (.close 4)))))) (.step 3 (.step 28 (.run (.close 9))))) (.step 68 (.step 54 (.step 70 (.step 4 (.run (.close 24))))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 54 (.step 70 (.step 18 (.run (.close 2))))))) (.step 68 (.run (.close 54)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 68 (.step 3 (.run (.close 11))))) (.step 68 (.step 3 (.step 48 (.run (.close 2)))))) (.step 68 (.step 3 (.run (.close 11))))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 70)))) (.step 3 (.run (.close 54)))) (.step 3 (.step 43 (.run (.close 23)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1147
namespace Part1148
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725563016942801507682810899744475852073054970932926414503635262053627723776⟩
def references : Fin 2 → Box := ![Part1146.root, Part1147.root]
def proof : Enumeration.Proof 2 := (.split 23 0 (.split 7 0 (.reuse 0) (.split 31 0 (.split 5 0 (.split 8 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 33 0 (.split 39 0 (.split 58 0 (.split 4 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 34 0 (.step 46 (.run (.close 2))) (.step 7 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 71))))) (.step 18 (.step 2 (.run (.close 71))))) (.step 7 (.run (.close 2)))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 46)))) (.step 55 (.step 5 (.run (.close 27))))) (.step 7 (.run (.close 46)))) (.step 72 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 46)))) (.step 55 (.step 5 (.step 63 (.step 5 (.run (.close 27))))))) (.step 55 (.step 3 (.run (.close 46))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 55 (.step 5 (.step 63 (.run (.close 46)))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 3 (.run (.close 46))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1146.covered
  · exact Part1147.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1148
namespace Part1149
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033664080626545386916475211363595244506787508919364483022848, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725563016942801509253618829132011931890360673761993327712842862291819954176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 31 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 4 0 (.step 22 (.split 10 0 (.split 30 0 (.step 9 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 9 (.run (.close 2)))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 54 (.step 18 (.run (.close 2)))))) (.split 4 0 (.split 6 0 (.split 7 0 (.split 10 0 (.split 12 0 (.split 13 0 (.step 3 (.run (.close 18))) (.step 2 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 24 (.run (.close 3))))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.step 24 (.run (.close 18)))))) (.step 68 (.step 3 (.run (.close 24))))) (.step 3 (.run (.close 54)))) (.step 3 (.step 43 (.run (.close 31))))) (.step 3 (.run (.close 7)))) (.step 55 (.step 3 (.step 31 (.run (.close 27)))))) (.step 3 (.step 40 (.run (.close 23))))) (.step 68 (.step 3 (.run (.close 31))))) (.step 3 (.step 40 (.run (.close 31))))) (.step 3 (.run (.close 7)))) (.step 68 (.step 3 (.step 31 (.run (.close 2)))))) (.step 55 (.step 3 (.step 61 (.run (.close 27)))))) (.step 68 (.step 3 (.step 65 (.step 2 (.run (.close 24)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1149
namespace Part1150
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408358868601293358647081135134801706733150555675715924722113246016366908340967713525836247308693672736603691959968287431430550216245248, 5789228615357111141503586739170888621570368439699510516910020032553785749215046980117447598480593637970170087425533354983191009596232063694882591751185029789971249375239096480599510171485022026676501256684682488613515034624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 54 0 (.split 58 0 (.step 2 (.run (.close 18))) (.step 53 (.run (.close 2)))) (.step 53 (.step 2 (.run (.close 4))))) (.step 54 (.step 70 (.step 2 (.run (.close 4)))))) (.step 65 (.step 2 (.run (.close 4))))) (.step 54 (.run (.close 2)))) (.step 64 (.split 6 0 (.split 38 0 (.step 54 (.step 2 (.run (.close 40)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 46)))))) (.step 65 (.step 10 (.run (.close 46))))) (.step 70 (.step 54 (.step 46 (.split 12 0 (.step 2 (.run (.close 5))) (.step 4 (.run (.close 63)))))))) (.step 54 (.run (.close 2)))) (.step 65 (.step 54 (.step 42 (.step 4 (.step 48 (.run (.close 2)))))))) (.step 65 (.step 64 (.split 17 0 (.split 36 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2))))))) (.step 65 (.step 46 (.step 2 (.run (.close 4)))))) (.step 70 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.step 53 (.split 16 0 (.step 54 (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 68 (.step 71 (.run (.close 58))))) (.step 71 (.step 68 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1150
namespace Part1151
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408358868601293358647081135134801706733150555675715924722113246016366908340967713525836247308693672736603691959968287431430550216245248, 5789234131009374243490885467899096052484164047812619602022372929823181965413934404333267727140595581778757921210426908612620442233367766474435808489056899334661979443304596534374799597946244260885857889470564497970562072576⟩
def references : Fin 1 → Box := ![Part1150.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.reuse 0) (.step 70 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.step 53 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 4))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 65)))) (.step 4 (.run (.close 55)))) (.step 4 (.run (.close 55)))))) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 25 0 (.step 53 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 48))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 46))))) (.split 74 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 46 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 46)))) (.step 68 (.run (.close 46)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 46))))) (.split 72 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 5 0 (.step 53 (.step 54 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 58))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1150.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1151
namespace Part1152
def root : Box := ⟨4249103942534136789516705652423100970619230591091148894617774261255913179920380224400814611919201801734449597804652057311935668363769788919797187446985715383644847770573325994553245696, 5789228615357111141503586739170888621574617543642044653699536738206205498233683725059263853866189191075773315904420172925104309614353897980233706387075001798094022009940318138514786331315154725492051906851365634365768859648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 54 0 (.split 58 0 (.step 2 (.run (.close 18))) (.step 52 (.run (.close 2)))) (.step 52 (.step 2 (.run (.close 4))))) (.step 54 (.step 70 (.step 2 (.run (.close 4)))))) (.step 65 (.step 64 (.run (.close 2))))) (.step 54 (.run (.close 2)))) (.step 64 (.step 9 (.step 54 (.run (.close 15)))))) (.step 64 (.step 10 (.run (.close 46))))) (.step 70 (.step 54 (.step 46 (.split 10 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))))))) (.step 54 (.run (.close 2)))) (.step 65 (.step 54 (.split 6 0 (.split 12 0 (.split 4 0 (.split 10 0 (.split 17 0 (.step 54 (.step 2 (.run (.close 23)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 64 (.run (.close 23))))) (.step 7 (.run (.close 2)))) (.step 64 (.step 4 (.run (.close 63))))) (.step 7 (.run (.close 2))))))) (.step 64 (.step 54 (.step 2 (.run (.close 4)))))) (.step 64 (.step 46 (.step 2 (.run (.close 4)))))) (.step 70 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.step 52 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 64)))) (.step 71 (.step 68 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1152
namespace Part1153
def root : Box := ⟨4249103942534136789516705652423100970619230591091148894617774261255913179920380224400814611919201801734449597804652057311935668363769788919797187446985715383644847770573325994553245696, 5789234131009374243490885467899096052488413151755153738811889635475601714432571149275083982526191134884361149689313726554533742251489600759786923124946871342784752078005818192290075757776376959701408539637247643722815897600⟩
def references : Fin 1 → Box := ![Part1152.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.reuse 0) (.step 70 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.step 52 (.split 34 0 (.step 54 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 54)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 63)))) (.step 68 (.step 63 (.run (.close 58))))) (.step 68 (.run (.close 64)))) (.step 68 (.run (.close 46)))))) (.split 74 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 25 0 (.step 52 (.step 54 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 53))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 46)))) (.step 4 (.step 71 (.run (.close 68)))))) (.split 74 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 46 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 46)))) (.step 68 (.run (.close 46)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 46))))) (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 5 0 (.step 52 (.run (.close 2))) (.step 63 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 52))))) (.step 71 (.step 68 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1152.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1153
namespace Part1154
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096052488413151755153738811889635475601714432571149275083982526191134884361149689313726554533742251489600759786923124946871342784752078005818192290075757776376959701409748563067258351990603776⟩
def references : Fin 4 → Box := ![Part1148.root, Part1149.root, Part1151.root, Part1153.root]
def proof : Enumeration.Proof 4 := (.split 61 0 (.split 62 0 (.split 18 0 (.split 19 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 58 0 (.split 31 0 (.split 4 0 (.step 22 (.split 10 0 (.step 9 (.run (.close 2))) (.step 18 (.run (.close 2))))) (.step 9 (.run (.close 2)))) (.step 9 (.split 4 0 (.step 22 (.run (.close 3))) (.step 2 (.run (.close 43)))))) (.step 3 (.run (.close 40)))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 7)))) (.step 68 (.step 3 (.run (.close 11))))) (.step 55 (.step 3 (.run (.close 27))))) (.step 3 (.run (.close 54)))) (.step 68 (.step 3 (.run (.close 31))))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 54)))) (.step 68 (.step 72 (.step 3 (.run (.close 31))))))) (.reuse 1)) (.split 8 0 (.reuse 2) (.split 35 0 (.split 72 0 (.split 14 0 (.step 46 (.split 34 0 (.step 30 (.step 4 (.run (.close 10)))) (.step 71 (.run (.close 46))))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 46)))) (.step 4 (.run (.close 53)))))) (.split 8 0 (.reuse 3) (.split 35 0 (.split 72 0 (.split 14 0 (.step 46 (.split 34 0 (.step 30 (.step 71 (.run (.close 10)))) (.step 68 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 46)))) (.step 4 (.run (.close 46))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1148.covered
  · exact Part1149.covered
  · exact Part1151.covered
  · exact Part1153.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1154
namespace Part1155
def root : Box := ⟨5386379163185534471414773640069251753523547958090930032126242996694364211649485655353416754303903258757464122391214009531929266140571550117757562374336689024016697170240048296165116704641640660089694470019739549696, 5789234136395753406676419939313869692557664905278705561440342684860186054526843807262639043297915374467610380980995738182402526750046035577741720203367716131548309570537144596604264069312296390683629678129620245110245556224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 25 0 (.split 38 0 (.split 56 0 (.split 57 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 18 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 19 0 (.split 23 0 (.split 31 0 (.step 54 (.step 46 (.step 54 (.split 4 0 (.step 57 (.run (.close 61))) (.step 18 (.run (.close 2))))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 3)))) (.step 18 (.run (.close 3)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 55 (.run (.close 57)))) (.step 55 (.step 18 (.run (.close 3))))) (.step 55 (.step 68 (.run (.close 48))))) (.step 3 (.run (.close 2)))) (.step 55 (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 68 (.run (.close 72)))) (.step 68 (.step 55 (.step 71 (.run (.close 57)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 68 (.step 63 (.step 68 (.run (.close 72)))))) (.step 68 (.step 63 (.step 68 (.step 55 (.step 63 (.run (.close 61)))))))) (.step 63 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 63 (.step 55 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1155
namespace Part1156
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676419939313869692557664905278705561440342684860186054526843807262639043297915374467610380980995738182402526750046035577741720203367716131548309570537144596604264069312296390683629678129620245110245556224⟩
def references : Fin 2 → Box := ![Part1154.root, Part1155.root]
def proof : Enumeration.Proof 2 := (.split 71 0 (.split 57 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 5 0 (.split 11 0 (.split 25 0 (.split 38 0 (.split 53 0 (.split 56 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 31 0 (.split 33 0 (.step 46 (.step 54 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 10)))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 58)))) (.step 68 (.step 3 (.run (.close 46))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 62)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 48))))) (.step 68 (.step 55 (.step 48 (.run (.close 2)))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 2)))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1154.covered
  · exact Part1155.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1156
namespace Part1157
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723379602756368638487163863180229018976102161271192821574270012692048273105473709613805027778106435421039684439019070960416086958052519584026319740585644728729835864052672809976229509254285046579200⟩
def references : Fin 1 → Box := ![Part1156.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 25 0 (.split 34 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 57 0 (.split 71 0 (.split 35 0 (.split 72 0 (.split 74 0 (.step 70 (.split 4 0 (.split 10 0 (.step 3 (.step 54 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 24))))) (.step 70 (.step 18 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 71))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.run (.close 27)))) (.step 55 (.run (.close 27)))) (.step 68 (.step 55 (.step 28 (.step 68 (.step 71 (.run (.close 7)))))))) (.step 55 (.step 68 (.step 58 (.run (.close 2)))))) (.step 68 (.run (.close 2)))) (.step 55 (.step 68 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 31))))) (.step 68 (.step 55 (.step 68 (.step 63 (.run (.close 7))))))) (.step 68 (.step 55 (.step 63 (.step 68 (.run (.close 31))))))) (.step 68 (.step 55 (.step 63 (.step 55 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1156.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1157
namespace Part1158
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723379602756368638487163863180229018976102161271192821577318595260716234268932300658524916748564050794735945328529966428800239046743696947425056169358586106815604351475921465147565423003590012698624⟩
def references : Fin 1 → Box := ![Part1157.root]
def proof : Enumeration.Proof 1 := (.split 47 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 5 0 (.split 74 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 53 0 (.split 56 0 (.split 30 0 (.step 2 (.run (.close 5))) (.step 18 (.step 2 (.run (.close 31))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 3 (.run (.close 48))))) (.step 3 (.step 2 (.run (.close 18))))) (.step 68 (.run (.close 2)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 48))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 68 (.step 2 (.run (.close 24))))) (.step 68 (.step 58 (.step 55 (.run (.close 28)))))) (.step 58 (.step 71 (.step 68 (.run (.close 2)))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 55 (.step 68 (.step 2 (.run (.close 48)))))) (.step 68 (.step 55 (.step 48 (.run (.close 2)))))) (.step 55 (.step 68 (.step 63 (.run (.close 2)))))) (.step 55 (.step 68 (.step 63 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1157.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1158
namespace Part1159
def root : Box := ⟨4562440617622195218641171605700291324896580459231045579854086026921496322861362087539475093804885993576009825956929369225368753910538471660800792324243241805105011242454462553973054434546024448, 5789234136395753406676424723384165196986260682382504351834719267427054499700070137252151584648848349923199366228531927948080681149099225614453007063393633972530800756998500563629404594329486759095091677331263606053064933376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 8 0 (.split 66 0 (.split 71 0 (.split 7 0 (.split 13 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 50 0 (.split 30 0 (.step 3 (.step 53 (.step 9 (.run (.close 2))))) (.step 31 (.run (.close 53)))) (.step 65 (.run (.close 53)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 68 (.run (.close 48))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 63 (.step 68 (.run (.close 57)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.step 68 (.step 2 (.run (.close 48))))))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 68 (.step 63 (.step 68 (.step 2 (.run (.close 48))))))) (.step 68 (.step 55 (.step 63 (.run (.close 11)))))) (.step 68 (.step 55 (.step 63 (.step 11 (.run (.close 2))))))) (.step 68 (.step 63 (.step 55 (.run (.close 2)))))) (.step 68 (.step 63 (.step 48 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1159
namespace Part1160
def root : Box := ⟨4455508415646675018204269146191690750317995446595571082099751715482166558161925043821962967316714304963846763777925203069393627367501863718299619091068841646231406643377550130495549127786496, 5789234136395753406676424723384169652494676329057522556103865459117801465743534247173958790891541610934104843452542187628560483269606821944833450026682023316969005225199670732243974635554278675859426223570595662835904151552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 66 0 (.split 8 0 (.split 14 0 (.split 64 0 (.split 71 0 (.split 7 0 (.split 13 0 (.split 18 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 19 0 (.split 23 0 (.split 31 0 (.step 54 (.step 46 (.step 54 (.step 64 (.step 31 (.run (.close 2))))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 3)))) (.step 18 (.run (.close 3)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 18 (.run (.close 3))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 55 (.run (.close 52)))) (.step 55 (.step 63 (.step 68 (.run (.close 11)))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 68 (.run (.close 2)))))) (.step 71 (.step 63 (.step 58 (.step 68 (.run (.close 2))))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.step 55 (.step 71 (.run (.close 68))))))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 68 (.step 63 (.step 55 (.step 68 (.run (.close 48))))))) (.step 68 (.step 55 (.step 63 (.run (.close 11)))))) (.step 68 (.step 55 (.step 63 (.step 11 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1160
namespace Part1161
def root : Box := ⟨3351951985607397825209501253602752882477867339310880630179564948226673342960333653499814809283339765611622975680854547974423190989645579569468527605710848, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509106883772992531334636618847936226703148240757681101793075398420843082589125531302734224215134462485401380556536305253182083745292746752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.step 54 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 54)))) (.step 55 (.step 18 (.split 6 0 (.step 68 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2))))))) (.step 55 (.step 18 (.step 2 (.run (.close 4)))))) (.step 55 (.split 4 0 (.step 18 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))))) (.step 55 (.split 4 0 (.split 10 0 (.step 18 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 18)))) (.step 2 (.run (.close 48)))))) (.step 68 (.run (.close 2)))) (.step 55 (.step 3 (.step 71 (.run (.close 68)))))) (.step 55 (.step 3 (.step 71 (.run (.close 29)))))) (.step 55 (.run (.close 27)))) (.step 55 (.step 3 (.step 63 (.run (.close 68)))))) (.step 55 (.step 3 (.step 63 (.run (.close 11)))))) (.step 3 (.step 68 (.run (.close 2))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 68 (.step 3 (.step 58 (.run (.close 2)))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 68 (.step 55 (.split 4 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 7))))))) (.step 68 (.step 3 (.step 58 (.run (.close 2)))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.step 31 (.run (.close 3)))))) (.step 68 (.step 55 (.split 46 0 (.step 11 (.run (.close 54))) (.step 71 (.run (.close 8))))))) (.step 68 (.step 3 (.step 48 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1161
namespace Part1162
def root : Box := ⟨3351951982485649274896348235987935367100909329686845005226912708932701219507936485770598561382226623186123938312878255780988296694222081147733111837032448, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049050364516324969743391216823546336499153936103157871182311940199464499953179017238196774915747247621637014078384766976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 42 0 (.split 53 0 (.split 56 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.step 46 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 18 (.split 6 0 (.step 68 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2)))))) (.step 18 (.step 2 (.run (.close 4))))) (.split 7 0 (.split 10 0 (.split 12 0 (.split 13 0 (.split 18 0 (.step 55 (.split 30 0 (.split 31 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 68)))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 71)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55))))) (.split 4 0 (.split 10 0 (.step 18 (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 18)))) (.step 2 (.run (.close 48))))) (.split 4 0 (.split 10 0 (.split 12 0 (.split 30 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 4))))) (.step 71 (.run (.close 18)))) (.step 2 (.run (.close 48))))) (.step 55 (.run (.close 9)))) (.step 55 (.step 3 (.split 46 0 (.step 71 (.run (.close 29))) (.step 71 (.run (.close 2))))))) (.step 55 (.step 3 (.split 46 0 (.step 71 (.run (.close 29))) (.step 2 (.run (.close 71))))))) (.step 55 (.run (.close 27)))) (.step 55 (.step 3 (.split 46 0 (.step 63 (.run (.close 11))) (.step 71 (.run (.close 55))))))) (.step 55 (.step 3 (.split 46 0 (.step 63 (.run (.close 11))) (.step 2 (.run (.close 55))))))) (.step 3 (.step 68 (.run (.close 2))))) (.step 3 (.step 68 (.run (.close 2))))) (.step 68 (.step 55 (.split 49 0 (.step 18 (.run (.close 3))) (.step 71 (.run (.close 68)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1162
namespace Part1163
def root : Box := ⟨3351951982485649274896348235987935367100909329686845005226912708932701219507936485770598561382226623186123938312878255780988296694222081147733111837032448, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669246286629248372991933631961344724263372217148926313124329352285136329730440762514737201152⟩
def references : Fin 1 → Box := ![Part1162.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.reuse 0) (.step 3 (.split 46 0 (.split 47 0 (.step 68 (.run (.close 2))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))))) (.step 68 (.step 55 (.split 49 0 (.step 18 (.run (.close 3))) (.step 71 (.run (.close 68))))))) (.step 68 (.step 55 (.split 4 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 71 (.run (.close 68)))) (.step 68 (.run (.close 7))))))) (.step 68 (.step 3 (.split 48 0 (.step 58 (.run (.close 2))) (.step 2 (.run (.close 71))))))) (.step 68 (.step 55 (.split 8 0 (.split 14 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))))) (.step 68 (.step 55 (.split 4 0 (.split 8 0 (.split 14 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 31))))))) (.step 68 (.step 55 (.split 4 0 (.split 8 0 (.split 10 0 (.split 30 0 (.split 49 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 31)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 7))))))) (.step 68 (.step 3 (.split 48 0 (.step 48 (.run (.close 2))) (.step 2 (.run (.close 71))))))) (.step 68 (.step 3 (.split 48 0 (.step 48 (.run (.close 2))) (.step 2 (.run (.close 71)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1162.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1163
namespace Part1164
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669246286629248372991933631961344724263372217148926313124329352285136329730440762514737201152⟩
def references : Fin 5 → Box := ![Part1158.root, Part1159.root, Part1160.root, Part1161.root, Part1163.root]
def proof : Enumeration.Proof 5 := (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 46 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 6 0 (.split 74 0 (.split 42 0 (.split 72 0 (.split 66 0 (.split 71 0 (.split 12 0 (.split 24 0 (.split 39 0 (.step 2 (.run (.close 4))) (.step 68 (.step 5 (.step 2 (.run (.close 18)))))) (.step 68 (.step 5 (.step 2 (.run (.close 31)))))) (.step 68 (.step 3 (.run (.close 48))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 18 (.run (.close 2))))) (.step 58 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 55 (.step 68 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 58 (.step 71 (.step 68 (.run (.close 2)))))) (.step 68 (.step 58 (.step 55 (.run (.close 28)))))) (.step 58 (.step 71 (.step 68 (.run (.close 2)))))) (.step 55 (.step 68 (.run (.close 2))))) (.step 68 (.step 55 (.step 48 (.run (.close 2)))))) (.step 68 (.step 55 (.step 48 (.run (.close 2)))))) (.step 55 (.step 68 (.step 63 (.run (.close 48)))))) (.step 55 (.step 48 (.step 68 (.run (.close 2))))))) (.reuse 1)) (.split 5 0 (.split 11 0 (.reuse 2) (.step 68 (.step 63 (.step 55 (.run (.close 2)))))) (.step 68 (.step 63 (.step 48 (.run (.close 55))))))) (.split 5 0 (.reuse 3) (.step 68 (.step 3 (.step 48 (.run (.close 2))))))) (.reuse 4))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1158.covered
  · exact Part1159.covered
  · exact Part1160.covered
  · exact Part1161.covered
  · exact Part1163.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1164
namespace Part1165
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797369505676280601061248670718155620945908532829124217007722778424001770241878230375801552896, 5789234136395753406676424723384169652494676329053565265906329759105480036621690010392138759305285726456335576155750595912645652967667723700927161585366581452058192255740169623756856595961623453201361609856034751432909389824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 70 0 (.split 72 0 (.split 73 0 (.split 74 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 30 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.step 18 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 33 (.step 68 (.step 54 (.run (.close 18))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 18 (.step 3 (.step 18 (.run (.close 68)))))) (.step 18 (.run (.close 54)))) (.step 18 (.step 3 (.step 18 (.run (.close 68)))))) (.step 18 (.step 3 (.step 18 (.run (.close 68)))))) (.step 18 (.run (.close 54)))) (.step 65 (.step 53 (.step 22 (.step 68 (.run (.close 2)))))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 33 (.split 10 0 (.step 68 (.run (.close 7))) (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 55 (.step 31 (.step 27 (.run (.close 2)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 65 (.step 2 (.run (.close 4))))) (.step 3 (.step 18 (.run (.close 68))))) (.step 2 (.run (.close 7)))))) (.step 55 (.step 18 (.step 9 (.run (.close 2)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 65 (.step 2 (.run (.close 4))))) (.step 3 (.step 18 (.step 68 (.run (.close 2)))))) (.step 2 (.run (.close 7))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1165
namespace Part1166
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797369505676280601061248670718155620945908532829124217007722778424001770241878230375801552896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529501152739120387289288827554160485704138752⟩
def references : Fin 1 → Box := ![Part1165.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.reuse 0) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 53 (.step 27 (.run (.close 2))))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 54)))))) (.step 68 (.step 18 (.step 3 (.step 10 (.step 68 (.run (.close 18)))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 54)))))) (.step 68 (.step 3 (.step 31 (.step 65 (.step 2 (.run (.close 48)))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 53 (.step 27 (.run (.close 2))))) (.step 3 (.step 53 (.run (.close 31))))) (.step 3 (.step 53 (.run (.close 7))))))) (.step 68 (.step 18 (.step 3 (.step 10 (.step 68 (.run (.close 18)))))))) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 65 (.step 2 (.run (.close 4))))) (.step 3 (.step 65 (.run (.close 31))))) (.step 2 (.run (.close 7)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 65 (.step 2 (.run (.close 4))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 18 (.step 68 (.step 3 (.step 10 (.step 68 (.run (.close 18)))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 53 (.step 27 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 55 (.step 31 (.step 27 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1165.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1166
namespace Part1167
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136390493270774876349876928662611796200388014926103506585245981755718621278237841678483172059920057987704523612943789474749954704268676977781503453637287540374890214400085728151363431789444715227178048838456072732672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 72 0 (.split 73 0 (.split 74 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 55))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.step 18 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 13 (.run (.close 2))) (.step 68 (.step 18 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 13))))) (.step 18 (.run (.close 54)))) (.step 18 (.step 3 (.run (.close 13))))) (.step 18 (.step 3 (.run (.close 13))))) (.step 18 (.step 3 (.run (.close 13))))) (.step 18 (.step 54 (.run (.close 2))))) (.split 16 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 18)))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 13 (.split 16 0 (.split 17 0 (.step 18 (.step 54 (.run (.close 18)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 48))))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 55 (.step 31 (.step 27 (.split 4 0 (.step 36 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2)))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 64 (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 13)))) (.step 2 (.run (.close 7)))))) (.step 55 (.step 18 (.step 9 (.split 4 0 (.step 22 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1167
namespace Part1168
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220858423682212355010212625042285856935432206865187842370473053842868890457098565791521345624891981824⟩
def references : Fin 1 → Box := ![Part1167.root]
def proof : Enumeration.Proof 1 := (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 70 0 (.reuse 0) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 64 (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 13)))) (.step 2 (.run (.close 7)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 27))))) (.step 3 (.run (.close 13)))) (.step 3 (.run (.close 54)))))) (.step 68 (.step 18 (.step 3 (.split 44 0 (.step 64 (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 71)))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 27))))) (.step 3 (.run (.close 13)))) (.step 3 (.run (.close 54)))))) (.step 68 (.step 3 (.step 31 (.step 30 (.split 44 0 (.split 46 0 (.step 68 (.run (.close 31))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71))))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.step 3 (.run (.close 2))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 3))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 31))))) (.step 3 (.step 52 (.run (.close 31))))) (.step 3 (.step 52 (.run (.close 7))))))) (.step 68 (.step 18 (.step 3 (.step 10 (.split 44 0 (.step 64 (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 71))))))))) (.step 55 (.step 18 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1167.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1168
namespace Part1169
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502513868588072281082720337970487676108800⟩
def references : Fin 1 → Box := ![Part1168.root]
def proof : Enumeration.Proof 1 := (.split 13 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.reuse 0) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 64 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2)))))) (.step 3 (.step 64 (.run (.close 31))))) (.step 2 (.run (.close 7)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.step 64 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2)))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 18 (.step 55 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 18 (.step 68 (.step 3 (.step 10 (.split 44 0 (.step 64 (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 71))))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 36 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2)))) (.step 3 (.run (.close 31)))) (.step 68 (.run (.close 27))))) (.step 2 (.run (.close 3)))) (.step 31 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 55 (.step 31 (.step 27 (.split 4 0 (.step 36 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 2))))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 64 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2)))))) (.step 3 (.step 64 (.run (.close 18))))) (.step 2 (.run (.close 7))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1168.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1169
namespace Part1170
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 1 → Box := ![Part1169.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.reuse 0) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 15)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 3 (.step 52 (.run (.close 18))))) (.step 3 (.step 52 (.run (.close 13))))))) (.step 3 (.step 68 (.step 31 (.step 30 (.split 44 0 (.split 46 0 (.step 68 (.run (.close 31))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71))))))))) (.step 3 (.step 55 (.step 31 (.step 27 (.split 4 0 (.step 36 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 68))))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 64 (.split 16 0 (.step 2 (.run (.close 4))) (.step 68 (.run (.close 2)))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 12 0 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 15)))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 68 (.run (.close 27)))) (.step 9 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 68 (.step 31 (.step 30 (.split 44 0 (.split 46 0 (.step 68 (.run (.close 31))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1169.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1170
namespace Part1171
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 3 → Box := ![Part1164.root, Part1166.root, Part1170.root]
def proof : Enumeration.Proof 3 := (.split 9 0 (.split 29 0 (.reuse 0) (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.reuse 1) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 65 (.step 2 (.run (.close 4))))) (.step 3 (.step 65 (.run (.close 18))))) (.step 2 (.run (.close 7)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.step 53 (.run (.close 18))))) (.step 3 (.step 53 (.run (.close 9))))))) (.step 3 (.step 68 (.step 31 (.step 30 (.step 68 (.run (.close 31)))))))) (.step 3 (.step 55 (.step 31 (.step 27 (.run (.close 2))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 65 (.step 2 (.run (.close 4))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 3 (.step 68 (.step 31 (.step 30 (.step 68 (.run (.close 31))))))))) (.reuse 2))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1164.covered
  · exact Part1166.covered
  · exact Part1170.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1171
namespace Part1172
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 3 → Box := ![Part1125.root, Part1140.root, Part1171.root]
def proof : Enumeration.Proof 3 := (.split 51 0 (.split 61 0 (.reuse 0) (.split 44 0 (.reuse 1) (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 12 0 (.split 42 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 24 0 (.split 10 0 (.split 35 0 (.split 72 0 (.split 30 0 (.split 49 0 (.step 2 (.run (.close 55))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 48)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 63)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 3 (.step 48 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 68 (.step 71 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 63 (.step 71 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 63))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))))) (.reuse 2))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part1125.covered
  · exact Part1140.covered
  · exact Part1171.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1172
namespace Part1173
def root : Box := ⟨1073741824, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 7 → Box := ![Part620.root, Part739.root, Part757.root, Part759.root, Part825.root, Part988.root, Part1172.root]
def proof : Enumeration.Proof 7 := (.split 43 0 (.split 51 0 (.split 25 0 (.split 34 0 (.reuse 0) (.split 36 0 (.reuse 1) (.split 9 0 (.reuse 2) (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.reuse 3) (.step 43 (.step 31 (.step 3 (.step 2 (.run (.close 4))))))) (.step 31 (.step 40 (.step 3 (.step 66 (.run (.close 2))))))) (.step 31 (.split 4 0 (.split 10 0 (.step 22 (.step 2 (.run (.close 4)))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 4)))))) (.step 31 (.split 4 0 (.split 10 0 (.step 22 (.split 12 0 (.split 16 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.step 2 (.run (.close 40))) (.step 31 (.run (.close 71)))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 15)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 15 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 18)))))) (.step 31 (.step 43 (.step 3 (.step 2 (.run (.close 4)))))))))) (.reuse 4)) (.reuse 5)) (.reuse 6))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part620.covered
  · exact Part739.covered
  · exact Part757.covered
  · exact Part759.covered
  · exact Part825.covered
  · exact Part988.covered
  · exact Part1172.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part1173
end FiveColour.Packed.EnumerationChunks.Case51
