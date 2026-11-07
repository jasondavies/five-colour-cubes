module
public import FiveColour.EnumerationChunks.Case39.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case39
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part770
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616323208302986719449642876683420956344548612073126181353967374245297204571883222144556393409578632876353426746616489725006519695833038848, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250369150171785916648729165090141378926304170365578204554462948220007530033419256123076116480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 41 0 (.step 3 (.run (.close 46))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 68 (.step 3 (.step 58 (.run (.close 2)))))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 68 (.step 55 (.step 2 (.run (.close 48)))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 46 0 (.split 47 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3))))))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 55)))) (.step 3 (.split 4 0 (.step 68 (.run (.close 10))) (.step 2 (.run (.close 28)))))) (.step 3 (.split 46 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 55)))))) (.step 2 (.run (.close 55)))) (.step 2 (.step 55 (.run (.close 3))))) (.step 2 (.run (.close 9)))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.step 2 (.run (.close 48))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part770
namespace Part771
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161562985810740038820775276728656616467278802300389971628295216873924037885737016959797559296, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250371139464731555795297786619133966209664572190181393945332710075915102670254384751971401728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 70 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 36 0 (.split 10 0 (.split 30 0 (.split 42 0 (.step 2 (.run (.close 3))) (.step 18 (.run (.close 26)))) (.step 18 (.run (.close 32)))) (.step 18 (.step 2 (.run (.close 3))))) (.step 18 (.step 2 (.run (.close 3))))) (.step 2 (.run (.close 3)))) (.step 55 (.step 18 (.step 2 (.run (.close 4)))))) (.step 55 (.step 18 (.step 2 (.run (.close 4)))))) (.step 55 (.step 31 (.step 53 (.step 23 (.run (.close 2))))))) (.step 2 (.run (.close 70)))) (.step 2 (.step 3 (.run (.close 31))))) (.step 68 (.step 18 (.step 55 (.step 68 (.step 18 (.run (.close 3)))))))) (.step 3 (.split 4 0 (.step 26 (.step 53 (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 18)))))) (.step 2 (.step 68 (.step 18 (.run (.close 4)))))) (.step 2 (.step 3 (.run (.close 31))))) (.step 68 (.step 18 (.step 3 (.step 10 (.run (.close 2))))))) (.step 55 (.step 18 (.step 3 (.step 29 (.step 68 (.run (.close 3)))))))) (.step 2 (.step 3 (.run (.close 48))))) (.step 2 (.step 3 (.run (.close 48))))) (.step 2 (.step 68 (.run (.close 9))))) (.step 2 (.step 3 (.run (.close 31))))) (.step 2 (.step 68 (.run (.close 27))))) (.step 3 (.split 4 0 (.step 26 (.step 65 (.step 10 (.run (.close 2))))) (.step 18 (.run (.close 3)))))) (.step 3 (.split 4 0 (.step 26 (.step 53 (.step 29 (.run (.close 2))))) (.step 18 (.run (.close 3)))))) (.step 2 (.step 68 (.run (.close 27))))) (.step 2 (.step 3 (.run (.close 18)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455019254405287034347101194551296, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250371139464731555795297786619133966209664572190181393945332710077153041528948144309459222528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 70 0 (.split 72 0 (.split 36 0 (.split 42 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 3))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.run (.close 12)))) (.step 2 (.run (.close 18)))) (.step 55 (.step 18 (.step 2 (.run (.close 3)))))) (.step 55 (.step 18 (.step 2 (.run (.close 3)))))) (.step 55 (.step 18 (.step 2 (.run (.close 3)))))) (.step 2 (.run (.close 70)))) (.step 2 (.step 3 (.run (.close 31))))) (.step 68 (.step 18 (.step 55 (.step 18 (.step 68 (.run (.close 3)))))))) (.step 3 (.split 4 0 (.step 26 (.step 52 (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 18)))))) (.step 2 (.step 68 (.step 18 (.run (.close 4)))))) (.step 2 (.step 3 (.run (.close 31))))) (.step 68 (.step 18 (.step 3 (.step 10 (.run (.close 2))))))) (.step 55 (.step 18 (.step 3 (.step 9 (.run (.close 2))))))) (.step 2 (.step 68 (.run (.close 9))))) (.step 2 (.step 3 (.run (.close 31))))) (.step 2 (.step 68 (.run (.close 27))))) (.step 3 (.split 4 0 (.step 26 (.split 10 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 3)))))) (.step 3 (.split 4 0 (.step 26 (.step 52 (.split 10 0 (.split 16 0 (.step 9 (.run (.close 2))) (.step 68 (.run (.close 23)))) (.step 18 (.run (.close 2)))))) (.step 18 (.run (.close 3)))))) (.step 2 (.step 68 (.run (.close 27)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part772
namespace Part773
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296393826836293161560996517794399674206655199664029183918400475786782237425455018016465247748966826295427072, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250371139464731555795297786619133966209664572190181393945332710077153042710692686531477372928⟩
def references : Fin 4 → Box := ![Part769.root, Part770.root, Part771.root, Part772.root]
def proof : Enumeration.Proof 4 := (.split 9 0 (.split 29 0 (.split 44 0 (.split 48 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 6 0 (.split 7 0 (.split 12 0 (.split 13 0 (.split 24 0 (.split 27 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 38 0 (.split 46 0 (.split 73 0 (.step 3 (.split 35 0 (.step 2 (.run (.close 48))) (.step 71 (.step 2 (.run (.close 68)))))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 68 (.step 3 (.step 71 (.run (.close 55)))))) (.step 2 (.run (.close 24)))) (.step 68 (.step 55 (.run (.close 3))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))))) (.step 68 (.step 55 (.split 31 0 (.split 33 0 (.split 41 0 (.split 39 0 (.split 46 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3))))))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 3 (.split 4 0 (.step 68 (.run (.close 10))) (.step 2 (.run (.close 28)))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 2 (.step 55 (.run (.close 3))))) (.step 2 (.run (.close 9)))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.step 2 (.run (.close 48))))))) (.reuse 1)) (.split 6 0 (.reuse 2) (.step 2 (.step 3 (.run (.close 18)))))) (.split 6 0 (.split 7 0 (.reuse 3) (.step 2 (.step 3 (.run (.close 18))))) (.step 2 (.step 3 (.run (.close 18))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part769.covered
  · exact Part770.covered
  · exact Part771.covered
  · exact Part772.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part773
namespace Part774
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126700522227504166352250371139464731555795297786619133966209664572190181393945332710077153042710692686531477372928⟩
def references : Fin 7 → Box := ![Part747.root, Part754.root, Part755.root, Part756.root, Part757.root, Part760.root, Part773.root]
def proof : Enumeration.Proof 7 := (.split 67 0 (.split 4 0 (.split 10 0 (.reuse 0) (.split 9 0 (.split 29 0 (.split 44 0 (.split 48 0 (.reuse 1) (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 32 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 54 0 (.split 39 0 (.split 46 0 (.split 47 0 (.step 68 (.step 55 (.run (.close 3)))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 23)))) (.step 71 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.step 55 (.step 2 (.run (.close 48)))))) (.step 68 (.step 55 (.step 43 (.step 18 (.run (.close 71))))))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 63 (.step 58 (.step 68 (.step 55 (.run (.close 2))))))) (.step 48 (.step 40 (.step 18 (.run (.close 29)))))) (.step 2 (.run (.close 24)))) (.step 2 (.step 71 (.run (.close 28))))) (.step 2 (.run (.close 29))))) (.reuse 2)) (.reuse 3)) (.reuse 4))) (.split 9 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 27 0 (.split 7 0 (.reuse 5) (.step 2 (.step 28 (.step 18 (.run (.close 16)))))) (.step 2 (.step 7 (.run (.close 3))))) (.step 2 (.step 43 (.step 18 (.run (.close 71)))))) (.step 2 (.step 43 (.step 18 (.run (.close 71)))))) (.step 2 (.step 43 (.step 18 (.run (.close 71)))))) (.step 2 (.step 18 (.step 9 (.run (.close 18)))))) (.step 2 (.step 18 (.step 9 (.run (.close 18))))))) (.reuse 6))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part747.covered
  · exact Part754.covered
  · exact Part755.covered
  · exact Part756.covered
  · exact Part757.covered
  · exact Part760.covered
  · exact Part773.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part774
namespace Part775
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243485986584588438710047216197411217962417850698040556747500718503133376513268029480071611639560162878302352514011103909891021815634577844738891679865927878989932438027609185042385793762204040131027977371648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 12 0 (.split 53 0 (.split 24 0 (.split 30 0 (.split 39 0 (.split 58 0 (.split 74 0 (.step 10 (.split 26 0 (.split 27 0 (.split 9 0 (.step 3 (.step 9 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 4 (.run (.close 9))))) (.step 4 (.step 3 (.step 5 (.run (.close 2)))))) (.step 4 (.step 3 (.step 5 (.run (.close 2)))))) (.step 4 (.split 9 0 (.step 3 (.run (.close 65))) (.step 2 (.run (.close 3)))))) (.split 26 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 74 0 (.split 36 0 (.step 3 (.split 54 0 (.step 65 (.run (.close 2))) (.step 4 (.run (.close 53))))) (.step 71 (.run (.close 3)))) (.step 71 (.step 63 (.run (.close 2))))) (.step 71 (.run (.close 65)))) (.step 71 (.run (.close 65)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.split 7 0 (.step 4 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 5 (.run (.close 2))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 40))))) (.step 5 (.run (.close 71)))) (.step 5 (.run (.close 43))))) (.step 2 (.step 5 (.run (.close 71)))))) (.split 35 0 (.split 72 0 (.split 36 0 (.split 38 0 (.step 30 (.step 3 (.step 72 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 4 (.run (.close 68)))) (.step 4 (.run (.close 68))))) (.split 24 0 (.split 58 0 (.split 74 0 (.split 27 0 (.split 31 0 (.split 53 0 (.step 21 (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 10)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part775
namespace Part776
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243485986584588438710047216197411217962417850698040556747500718503133376513268029480071611639560162878302352514011103909891021815634577844740576676532624795473676804491189075108225330336070183000799077990400⟩
def references : Fin 1 → Box := ![Part775.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 22 0 (.split 14 0 (.split 6 0 (.reuse 0) (.split 31 0 (.split 32 0 (.split 7 0 (.step 4 (.step 9 (.run (.close 2)))) (.step 2 (.step 9 (.run (.close 71))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 7 0 (.split 13 0 (.split 38 0 (.split 56 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 5 (.step 31 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 5))))) (.step 71 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 5 (.run (.close 43)))) (.step 2 (.step 71 (.run (.close 4)))))) (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 36 0 (.split 38 0 (.split 14 0 (.split 74 0 (.split 30 0 (.step 30 (.step 68 (.run (.close 5)))) (.step 63 (.run (.close 65)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 4 (.step 71 (.step 2 (.run (.close 4)))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 4 (.step 71 (.step 2 (.run (.close 4)))))) (.step 4 (.step 71 (.step 2 (.run (.close 4))))))) (.split 35 0 (.split 72 0 (.split 36 0 (.split 6 0 (.split 38 0 (.split 14 0 (.split 74 0 (.split 56 0 (.split 53 0 (.split 22 0 (.split 30 0 (.step 3 (.step 4 (.step 30 (.run (.close 5))))) (.step 63 (.run (.close 3)))) (.step 63 (.step 55 (.run (.close 31))))) (.step 63 (.run (.close 72)))) (.step 71 (.run (.close 72)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 4 (.step 71 (.step 2 (.run (.close 4)))))) (.step 68 (.run (.close 55)))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part775.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part776
namespace Part777
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023166488907581873174223634667929600, 5789234131009374243485986584588438710047216197411217962417850698040556747500718503133376513268029480071611639560162878302352514011103909891021815634577844740576676532624795475138306128519978027696666977940515036580888444928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 9 0 (.split 29 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 6 0 (.split 12 0 (.split 54 0 (.split 24 0 (.step 65 (.split 7 0 (.split 13 0 (.split 39 0 (.step 65 (.step 3 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.run (.close 3)))) (.step 16 (.step 18 (.run (.close 3)))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 9))))) (.step 63 (.step 4 (.run (.close 16))))) (.step 63 (.step 4 (.run (.close 9))))) (.step 71 (.run (.close 10)))) (.step 71 (.step 55 (.run (.close 10))))) (.step 64 (.step 63 (.step 55 (.run (.close 23)))))) (.step 63 (.step 72 (.step 55 (.step 48 (.step 55 (.run (.close 23)))))))) (.step 63 (.step 65 (.step 4 (.run (.close 23)))))) (.step 63 (.step 71 (.step 4 (.run (.close 2)))))) (.step 71 (.step 63 (.step 4 (.run (.close 71)))))) (.step 71 (.step 63 (.step 4 (.run (.close 71)))))) (.step 71 (.step 63 (.step 4 (.run (.close 71)))))) (.step 63 (.step 71 (.step 4 (.run (.close 2)))))) (.step 63 (.step 71 (.step 4 (.run (.close 2)))))) (.step 18 (.step 31 (.step 65 (.step 18 (.run (.close 2))))))) (.step 31 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 18))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part777
namespace Part778
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243485986584588438710047216197411217962417850698040556747500718503133376513268029480071611639560162878302352514011103909891021815634577844740576676532624795475138306128519978027696666977940515036580888444928⟩
def references : Fin 2 → Box := ![Part776.root, Part777.root]
def proof : Enumeration.Proof 2 := (.split 10 0 (.split 16 0 (.split 8 0 (.reuse 0) (.split 7 0 (.split 13 0 (.split 38 0 (.split 14 0 (.split 17 0 (.split 56 0 (.split 73 0 (.split 18 0 (.split 19 0 (.step 5 (.step 31 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 5)))) (.step 4 (.step 68 (.run (.close 5))))) (.step 71 (.run (.close 5)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 4 (.step 71 (.step 68 (.run (.close 2)))))) (.step 5 (.run (.close 43)))) (.step 2 (.step 71 (.run (.close 5)))))) (.split 36 0 (.split 38 0 (.split 56 0 (.split 6 0 (.split 9 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 8 0 (.split 42 0 (.split 14 0 (.split 74 0 (.split 12 0 (.split 17 0 (.split 7 0 (.step 35 (.step 42 (.step 65 (.run (.close 4))))) (.step 5 (.run (.close 65)))) (.step 63 (.run (.close 65)))) (.step 4 (.run (.close 42)))) (.step 63 (.run (.close 31)))) (.step 63 (.run (.close 31)))) (.step 68 (.run (.close 23)))) (.step 63 (.run (.close 31)))) (.step 4 (.run (.close 31)))) (.step 4 (.run (.close 31)))) (.step 4 (.run (.close 2)))) (.step 68 (.step 18 (.step 3 (.step 63 (.step 18 (.run (.close 3)))))))) (.step 4 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part776.covered
  · exact Part777.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part778
namespace Part779
def root : Box := ⟨4898883310657346788030287556357712069628819860444861045260235970461835218935600077441189048488868913046054849919869196059181551005542972918841963234896105718574448293309042141882235931290217134212251648, 5789234131009374243490885467899096052484164047812619602022372929823178613461951918683992833634346030317226051368971760512036266600829031822870847819935003193632726666719727850749513921465819234596199164641375347116477513728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 54 0 (.split 4 0 (.split 10 0 (.split 6 0 (.split 12 0 (.split 24 0 (.split 39 0 (.step 65 (.split 58 0 (.step 76 (.step 3 (.run (.close 53)))) (.step 4 (.run (.close 2))))) (.step 3 (.run (.close 65)))) (.step 3 (.step 2 (.run (.close 5))))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 9)))) (.step 64 (.step 70 (.step 46 (.step 4 (.run (.close 71))))))) (.step 30 (.step 18 (.step 9 (.run (.close 7)))))) (.step 53 (.step 4 (.run (.close 9))))) (.step 72 (.step 65 (.step 4 (.run (.close 2)))))) (.step 70 (.run (.close 10)))) (.step 65 (.run (.close 9)))) (.step 72 (.step 54 (.step 70 (.step 46 (.step 5 (.step 71 (.run (.close 2))))))))) (.step 70 (.step 4 (.step 2 (.run (.close 23)))))) (.step 72 (.step 54 (.step 70 (.step 46 (.step 4 (.run (.close 7)))))))) (.step 65 (.step 42 (.step 70 (.run (.close 4)))))) (.step 70 (.step 4 (.run (.close 2))))) (.step 70 (.step 4 (.run (.close 76))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.step 53 (.run (.close 10))) (.step 4 (.run (.close 55)))) (.step 71 (.run (.close 70)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 65))))) (.step 46 (.step 4 (.step 55 (.step 53 (.run (.close 10)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part779
namespace Part780
def root : Box := ⟨4898883310657346788030287556357712069628819860444861045260235970461835218935600077441189048488868913046054849919869196059181551005542972918841963234896105718574448293309042141882235931290217134212251648, 5789234131009374243490885467899096052484164047812619602022372929823178613461951918683992833634346030317226051368971760512036266600829033812163793459081571815161719254003088252574118504653263904617292232226860432676647600128⟩
def references : Fin 1 → Box := ![Part779.root]
def proof : Enumeration.Proof 1 := (.split 9 0 (.split 29 0 (.split 8 0 (.split 14 0 (.reuse 0) (.split 26 0 (.split 72 0 (.split 36 0 (.split 38 0 (.step 53 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.step 5 (.step 73 (.step 5 (.run (.close 2))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 70)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 71)))) (.step 4 (.run (.close 70)))) (.step 4 (.run (.close 46))))) (.step 46 (.step 5 (.step 30 (.step 68 (.run (.close 63))))))) (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.step 53 (.run (.close 65))) (.step 2 (.step 4 (.run (.close 30))))) (.step 2 (.step 4 (.run (.close 30))))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 33 0 (.split 41 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 14 0 (.step 64 (.split 24 0 (.step 70 (.step 30 (.run (.close 18)))) (.step 2 (.run (.close 18))))) (.step 2 (.step 71 (.run (.close 48))))) (.step 3 (.run (.close 18)))) (.step 3 (.step 71 (.run (.close 18))))) (.step 2 (.step 71 (.run (.close 30))))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 46)))) (.step 2 (.run (.close 70)))) (.step 2 (.step 4 (.run (.close 30))))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part779.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part780
namespace Part781
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243490885467899096052484164047812623466559895947081523308813842850671337132561675736752224708604223212031178556161253570005930375381659534278777750756180265617652779547640919647525965699307609129657462423552⟩
def references : Fin 2 → Box := ![Part778.root, Part780.root]
def proof : Enumeration.Proof 2 := (.split 57 0 (.split 67 0 (.split 4 0 (.reuse 0) (.split 9 0 (.split 29 0 (.split 8 0 (.split 14 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 42 0 (.split 38 0 (.split 56 0 (.split 6 0 (.step 30 (.run (.close 9))) (.step 2 (.run (.close 9)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 65)))) (.step 71 (.run (.close 10)))) (.step 72 (.step 71 (.run (.close 28))))) (.step 63 (.step 10 (.step 48 (.run (.close 2)))))) (.step 63 (.step 10 (.step 48 (.run (.close 2)))))) (.step 63 (.step 65 (.step 68 (.step 4 (.run (.close 2))))))) (.step 2 (.step 63 (.step 71 (.run (.close 4)))))) (.step 71 (.step 63 (.step 71 (.run (.close 18)))))) (.step 71 (.step 63 (.step 71 (.run (.close 18)))))) (.step 2 (.step 63 (.step 71 (.run (.close 4)))))) (.step 2 (.step 63 (.step 71 (.run (.close 4)))))) (.step 2 (.step 18 (.run (.close 3))))) (.step 2 (.step 18 (.run (.close 3)))))) (.reuse 1)) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 9 0 (.step 30 (.step 65 (.split 24 0 (.step 58 (.run (.close 55))) (.step 2 (.run (.close 23)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 18 (.step 2 (.run (.close 3)))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 71 (.step 68 (.step 3 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 3))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part778.covered
  · exact Part780.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part781
namespace Part782
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986703362302260194745274917203726501815898333799241856603328282762072160023165221256981644944822137964724224, 5789234131009374243490885467899096052484164047812623466559895947081523308813842853722896832644351706034505783641221449061506444870889714291738827621655521494067592048860772934317733197946290359273887135459280607233234173952⟩
def references : Fin 1 → Box := ![Part781.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 54 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 35 0 (.split 72 0 (.step 65 (.step 30 (.step 58 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 58)))) (.step 68 (.step 18 (.step 2 (.run (.close 3)))))) (.step 68 (.step 3 (.run (.close 2))))) (.step 18 (.step 68 (.step 3 (.run (.close 2)))))) (.step 71 (.step 68 (.step 3 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 3)))))) (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 16 0 (.split 8 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 42 0 (.step 30 (.step 55 (.step 2 (.run (.close 71))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 55))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.step 71 (.run (.close 55)))))) (.step 2 (.run (.close 58)))) (.step 63 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 18 (.step 2 (.run (.close 3)))))) (.step 18 (.step 68 (.step 3 (.run (.close 2)))))) (.step 18 (.step 68 (.step 3 (.run (.close 2)))))) (.step 71 (.step 68 (.step 3 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 3))))))
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
def root : Box := ⟨4784065733068162056019040113691253782879319798211750004587427219163602976780837926010063712026627395196549833148716246443939221057819305073697639199317323226732683590827210437279744833831312765747200, 5789234136395753406676424723379602756364389383221329043439502270449738170222202346730481243239103970188855590521684049094265834098660016357256282990217645740186392494997517962593725127018121709336613896044973906185475325952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 24 0 (.split 26 0 (.split 53 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 35 0 (.split 47 0 (.split 57 0 (.split 9 0 (.split 71 0 (.step 30 (.step 3 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 32 (.step 3 (.run (.close 2))))) (.step 32 (.step 76 (.step 68 (.step 2 (.run (.close 48))))))) (.step 32 (.step 76 (.step 68 (.step 3 (.run (.close 2))))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 3)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 58 (.run (.close 28))))) (.step 68 (.step 71 (.run (.close 28))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 30))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 8)))))) (.step 71 (.step 68 (.step 63 (.step 3 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 9)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part783
namespace Part784
def root : Box := ⟨4562444968704632373597244070806879402716223591275380350424707370518324999035454626185899514679673659973387584490798133812504603055174679854855989602484286348275159895617246595027696330211328000, 5789234136395753406676424723384165196982011578439970215045202561774631398729450906661060435757003245356064267908189961905583205498438658666829877397528334444907767932995770623913447341206373704010974160995056780377721929728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 7 0 (.split 56 0 (.split 13 0 (.split 73 0 (.split 4 0 (.split 10 0 (.split 30 0 (.split 67 0 (.split 69 0 (.step 2 (.run (.close 55))) (.split 12 0 (.step 2 (.run (.close 55))) (.step 71 (.step 2 (.run (.close 3)))))) (.step 3 (.step 53 (.step 27 (.step 71 (.run (.close 3))))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 2 (.run (.close 71)))) (.step 4 (.step 5 (.step 18 (.run (.close 3)))))) (.step 4 (.step 5 (.step 18 (.step 68 (.run (.close 3))))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 65)))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 65)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 63 (.step 2 (.run (.close 55)))))) (.step 2 (.step 71 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part784
namespace Part785
def root : Box := ⟨4459859498083829974276734252779768569961127490930341652721095312310842732254463690246383842104380702341605297646689790205242772003710057773496897332113384816380059806161591185137444793090048, 5789234136395753406676424723384169652490427225114988419314348753465378364772915016582867641999696506366969745132200221586063007618946254997210320360816723789345972401196940792528017382431166918849523340941297095684550295552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 35 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 7 0 (.split 56 0 (.split 13 0 (.split 73 0 (.split 10 0 (.split 30 0 (.split 67 0 (.split 69 0 (.step 2 (.run (.close 55))) (.split 12 0 (.step 2 (.run (.close 55))) (.step 71 (.run (.close 64))))) (.split 12 0 (.split 18 0 (.step 2 (.run (.close 55))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 9))))) (.step 71 (.run (.close 31)))) (.step 71 (.run (.close 31)))) (.step 4 (.step 5 (.step 71 (.step 18 (.run (.close 3))))))) (.step 4 (.step 5 (.step 18 (.step 68 (.run (.close 3))))))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 63 (.step 2 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part785
namespace Part786
def root : Box := ⟨4351082437154956072465106588077822995084029942168395830844850431429056570405985735301504967231345604431876829098240635663953919547959666820253921899091144571844152429620624110423271014400, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417957991927887964199538298505970184205672590097114154169945732555543554966092707300004284499177209362288325472418788916976383969856585728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 24 0 (.split 26 0 (.split 53 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 2))))) (.split 4 0 (.step 32 (.split 10 0 (.step 2 (.run (.close 55))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71))))) (.split 4 0 (.step 32 (.split 10 0 (.split 13 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 10)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71))))) (.step 32 (.split 4 0 (.split 10 0 (.step 21 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 3)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 58 (.step 18 (.step 2 (.run (.close 55))))))) (.step 71 (.step 68 (.step 63 (.run (.close 28)))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 8)))))) (.step 71 (.step 68 (.step 63 (.step 3 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 9)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part786
namespace Part787
def root : Box := ⟨4351082437154956072465106588077822995084026820419845517691832816611541193447976111265880014579106310459753376701072906447706018434817241321216553922798951136949857006122202375007502336000, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001216297201018813394233936839394197504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 16 0 (.split 8 0 (.split 14 0 (.split 17 0 (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 24 0 (.split 26 0 (.split 53 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 63 (.run (.close 2))))) (.split 4 0 (.step 32 (.split 10 0 (.step 2 (.run (.close 55))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71))))) (.split 4 0 (.step 32 (.split 10 0 (.split 13 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 10)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71))))) (.step 32 (.split 10 0 (.split 27 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))))) (.step 68 (.step 58 (.run (.close 10))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 3)))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 68 (.step 58 (.run (.close 10))))) (.step 68 (.step 71 (.step 63 (.run (.close 10)))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.step 68 (.step 63 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.step 2 (.run (.close 23))))))) (.step 68 (.step 48 (.step 63 (.step 3 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 9)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part787
namespace Part788
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304043431466397092945507293649813495829849942648029258850526730687034699666639148981459408125952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 12 0 (.split 26 0 (.split 35 0 (.split 50 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.split 7 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 13 0 (.split 24 0 (.split 38 0 (.split 39 0 (.step 68 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 53 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.step 24 (.step 18 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 40)))) (.split 7 0 (.split 13 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 18 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part788
namespace Part789
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304045468502373427431593562095501905208010995613000601413621955068057322749413877367345122377728⟩
def references : Fin 1 → Box := ![Part788.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 6 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 50 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.step 4 (.step 2 (.run (.close 68))))))) (.step 68 (.step 63 (.step 4 (.step 55 (.run (.close 2))))))) (.step 68 (.step 63 (.step 4 (.step 55 (.run (.close 18))))))) (.step 4 (.step 71 (.run (.close 31)))))) (.step 2 (.step 4 (.run (.close 71))))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 13 0 (.split 73 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 8)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 63 (.step 55 (.run (.close 2)))))) (.step 63 (.step 4 (.step 55 (.run (.close 8)))))) (.step 63 (.step 4 (.step 55 (.step 68 (.run (.close 2))))))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part788.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part789
namespace Part790
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406676424723384169652490427225114988419314348753465378364769721467815894384786206899180605752209715530248634454450528902612349738046575194109335118450723626497503804645201994293957721347021752062782788861952⟩
def references : Fin 1 → Box := ![Part789.root]
def proof : Enumeration.Proof 1 := (.split 29 0 (.split 62 0 (.split 67 0 (.reuse 0) (.split 26 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 35 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 55 (.split 17 0 (.split 54 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 55 (.step 31 (.run (.close 30)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 3 (.run (.close 30))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.run (.close 68))))) (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.step 30 (.step 4 (.step 63 (.step 55 (.step 4 (.run (.close 31))))))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 65)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 55)))) (.step 4 (.step 68 (.run (.close 2)))))) (.step 2 (.step 18 (.run (.close 3)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part789.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part790
namespace Part791
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406676424723384169652490427225114988419314348753465378364769721467815894384786206899180605752209715530248634454450528902612349738046575194109335118450723626497503804645201994295225371947249981464279492067328⟩
def references : Fin 1 → Box := ![Part790.root]
def proof : Enumeration.Proof 1 := (.split 10 0 (.reuse 0) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 8 0 (.split 14 0 (.split 39 0 (.split 36 0 (.split 42 0 (.split 38 0 (.step 55 (.run (.close 30))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 5)))) (.step 68 (.step 63 (.run (.close 4))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 4))))) (.step 2 (.run (.close 71)))) (.step 71 (.step 63 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 18)))) (.step 55 (.step 63 (.step 24 (.step 4 (.step 23 (.run (.close 40)))))))) (.step 55 (.step 63 (.step 24 (.step 23 (.run (.close 3))))))) (.step 24 (.step 63 (.step 23 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part790.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part791
namespace Part792
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642275971467422670314677070310674345572668433133207552⟩
def references : Fin 1 → Box := ![Part791.root]
def proof : Enumeration.Proof 1 := (.split 49 0 (.reuse 0) (.split 26 0 (.split 17 0 (.split 22 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 38 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 44 0 (.split 48 0 (.split 10 0 (.split 30 0 (.step 4 (.step 27 (.step 12 (.step 4 (.run (.close 2)))))) (.step 63 (.run (.close 27)))) (.step 63 (.run (.close 52)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 18))))) (.step 4 (.step 58 (.run (.close 3))))) (.step 4 (.step 71 (.run (.close 9))))) (.step 68 (.step 4 (.run (.close 5))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 63 (.step 58 (.step 48 (.run (.close 27)))))) (.step 48 (.step 4 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 71))))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704454130204672, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001217595275233447101141069463476502528⟩
def references : Fin 1 → Box := ![Part792.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 9 0 (.split 16 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 13 0 (.split 73 0 (.split 35 0 (.split 72 0 (.split 49 0 (.step 2 (.run (.close 48))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 24))))) (.step 71 (.step 63 (.step 2 (.run (.close 24)))))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.step 24 (.run (.close 23))))) (.step 24 (.run (.close 8)))) (.step 4 (.step 55 (.run (.close 2))))) (.step 24 (.step 4 (.run (.close 23))))) (.step 4 (.step 55 (.step 48 (.run (.close 8)))))) (.step 4 (.step 63 (.step 2 (.run (.close 24)))))) (.step 63 (.step 24 (.step 4 (.run (.close 23)))))) (.step 63 (.step 24 (.step 4 (.run (.close 23)))))) (.step 63 (.step 24 (.step 4 (.step 23 (.run (.close 2))))))) (.step 4 (.step 63 (.step 2 (.run (.close 24))))))) (.step 2 (.step 3 (.run (.close 31))))) (.step 2 (.split 10 0 (.split 16 0 (.split 12 0 (.step 55 (.step 7 (.run (.close 4)))) (.step 71 (.run (.close 18)))) (.step 4 (.step 55 (.run (.close 31))))) (.step 7 (.run (.close 68))))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304043431466397092945507293649813495829849942648029258850526729388960485032932242974735232663552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 12 0 (.split 26 0 (.split 35 0 (.split 50 0 (.split 54 0 (.split 72 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 4))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.split 7 0 (.split 8 0 (.step 3 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 13 0 (.split 24 0 (.split 38 0 (.split 39 0 (.step 68 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2))))) (.split 22 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 53 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.step 3 (.step 24 (.step 18 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 40)))) (.split 7 0 (.split 13 0 (.split 24 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 73 0 (.split 18 0 (.step 68 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 40)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part794
namespace Part795
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285378020805075519731483304045468502373427431593562095501905208010995613000601413621953769983108115706971360620946915328⟩
def references : Fin 1 → Box := ![Part794.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 6 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 50 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 4))))) (.step 68 (.step 63 (.step 4 (.run (.close 10)))))) (.step 68 (.step 63 (.step 4 (.run (.close 10)))))) (.step 68 (.step 63 (.step 4 (.run (.close 10)))))) (.step 4 (.step 71 (.run (.close 31)))))) (.step 2 (.run (.close 9)))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 13 0 (.split 73 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 8)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 63 (.step 55 (.run (.close 2)))))) (.step 63 (.step 4 (.step 55 (.run (.close 8)))))) (.step 63 (.step 4 (.step 55 (.step 68 (.run (.close 2))))))) (.step 4 (.run (.close 2)))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364769721467815894384786206899180605752209715530248634454450528902612349738046575194109335118450723626497503804645201992995883506713314846056058613399552⟩
def references : Fin 1 → Box := ![Part795.root]
def proof : Enumeration.Proof 1 := (.split 29 0 (.split 62 0 (.split 67 0 (.reuse 0) (.split 26 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 35 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 55 (.split 17 0 (.split 54 0 (.step 55 (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 55 (.step 31 (.run (.close 30)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 3 (.run (.close 30))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.run (.close 68))))) (.split 35 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.step 30 (.step 4 (.step 63 (.step 55 (.step 4 (.run (.close 31))))))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 65)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 4 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 55)))) (.step 4 (.step 68 (.run (.close 2)))))) (.step 2 (.step 18 (.run (.close 3)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part795.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part796
namespace Part797
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642275971467422670313378996096040638666661708957745152⟩
def references : Fin 1 → Box := ![Part796.root]
def proof : Enumeration.Proof 1 := (.split 49 0 (.split 10 0 (.reuse 0) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 31 0 (.split 33 0 (.step 7 (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 68 (.run (.close 7)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 68 (.run (.close 7)))) (.step 2 (.run (.close 71)))) (.step 71 (.step 63 (.step 4 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 18)))) (.step 55 (.step 63 (.step 24 (.step 4 (.step 23 (.run (.close 40)))))))) (.step 55 (.step 63 (.step 24 (.step 23 (.run (.close 3))))))) (.step 24 (.step 63 (.step 23 (.run (.close 3))))))) (.split 17 0 (.split 22 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 38 0 (.split 35 0 (.split 7 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 44 0 (.split 48 0 (.step 27 (.step 9 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 9)))) (.step 68 (.step 4 (.run (.close 18))))) (.step 4 (.step 68 (.step 58 (.run (.close 3)))))) (.step 2 (.step 4 (.run (.close 5))))) (.step 4 (.run (.close 9)))) (.step 68 (.step 4 (.run (.close 5))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 63 (.step 58 (.step 48 (.run (.close 27)))))) (.step 48 (.step 4 (.run (.close 2))))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961404697729954742272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094746723384909008679339006118707126634104338311900260642277432969060001217595275233447101142195363383345152⟩
def references : Fin 1 → Box := ![Part797.root]
def proof : Enumeration.Proof 1 := (.split 11 0 (.split 4 0 (.split 9 0 (.split 16 0 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 29 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 39 0 (.step 8 (.run (.close 2))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 63 (.step 2 (.run (.close 24))))) (.step 71 (.step 63 (.step 2 (.run (.close 24)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 63 (.step 24 (.run (.close 23))))) (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 8)))) (.step 4 (.step 55 (.run (.close 2))))) (.step 24 (.step 4 (.run (.close 23))))) (.step 4 (.step 55 (.step 48 (.run (.close 8)))))) (.step 4 (.step 63 (.step 2 (.run (.close 24)))))) (.step 63 (.step 24 (.step 4 (.run (.close 23)))))) (.step 63 (.step 24 (.step 4 (.run (.close 23)))))) (.step 63 (.step 24 (.step 4 (.step 23 (.run (.close 2))))))) (.step 4 (.step 63 (.step 2 (.run (.close 24))))))) (.step 2 (.step 3 (.run (.close 31))))) (.step 2 (.step 7 (.run (.close 18))))) (.step 2 (.step 4 (.step 48 (.step 24 (.run (.close 23)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part797.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part798
namespace Part799
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671521056007779241891423355673473088456043642362958287058480343086531450573526280946328027881439764239664297468584427250008678040823500396411449721691319800879434508125619464546137952826494421646943715328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 47 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 57 0 (.split 16 0 (.split 17 0 (.split 35 0 (.split 63 0 (.split 56 0 (.step 9 (.split 18 0 (.split 64 0 (.step 7 (.step 68 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 68)))) (.step 55 (.step 18 (.run (.close 2)))))) (.step 29 (.step 58 (.run (.close 18))))) (.step 29 (.run (.close 2)))) (.step 29 (.run (.close 2)))) (.split 24 0 (.split 39 0 (.step 29 (.step 68 (.run (.close 40)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 24 0 (.split 39 0 (.step 68 (.split 18 0 (.split 19 0 (.step 43 (.step 18 (.step 43 (.run (.close 40))))) (.step 68 (.run (.close 4)))) (.step 68 (.run (.close 4))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 31 (.step 71 (.step 40 (.step 68 (.step 48 (.run (.close 28))))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 55))))) (.split 16 0 (.split 17 0 (.step 3 (.step 58 (.step 55 (.step 43 (.run (.close 4)))))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 55))))) (.step 55 (.step 40 (.split 24 0 (.split 39 0 (.step 68 (.step 58 (.step 3 (.step 71 (.run (.close 28)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))))) (.step 40 (.step 55 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.step 58 (.step 55 (.split 56 0 (.step 4 (.step 43 (.run (.close 4)))) (.step 43 (.run (.close 2))))))) (.step 68 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 55))))))) (.split 32 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 40 (.step 18 (.step 28 (.run (.close 31))))) (.step 68 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))) (.step 4 (.run (.close 23)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part799
namespace Part800
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671521056007779241891423355673473088456043642362958287058480343089508581988241086770018058198549030812376812481959682024923559034257463109069747402653780687285279441887840814284787670387936971780446486528⟩
def references : Fin 1 → Box := ![Part799.root]
def proof : Enumeration.Proof 1 := (.split 11 0 (.split 14 0 (.split 46 0 (.split 27 0 (.reuse 0) (.split 47 0 (.split 35 0 (.split 42 0 (.split 6 0 (.step 23 (.step 4 (.step 43 (.run (.close 10))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 43 (.run (.close 7)))) (.step 4 (.run (.close 29)))) (.step 4 (.run (.close 23))))) (.split 24 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.step 3 (.step 28 (.step 40 (.run (.close 29))))) (.step 4 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 71 (.run (.close 55)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24))))) (.split 27 0 (.split 32 0 (.split 70 0 (.split 46 0 (.split 47 0 (.split 16 0 (.split 53 0 (.split 57 0 (.step 52 (.step 68 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 4)))) (.step 68 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 24 0 (.split 39 0 (.split 58 0 (.split 64 0 (.split 71 0 (.split 6 0 (.split 50 0 (.split 35 0 (.step 55 (.step 40 (.step 4 (.step 23 (.run (.close 40)))))) (.step 4 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part799.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part800
namespace Part801
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671525840073512305702396937558630707244719933604933503724458110096882230738598820420341166183575466544070938902682244779871531104101582168636202956059541621571127403168250235135108567778493695677855432704⟩
def references : Fin 1 → Box := ![Part800.root]
def proof : Enumeration.Proof 1 := (.split 66 0 (.split 8 0 (.split 41 0 (.reuse 0) (.split 11 0 (.split 35 0 (.split 42 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 18 0 (.step 31 (.step 70 (.step 55 (.step 3 (.run (.close 2)))))) (.step 40 (.run (.close 3)))) (.step 4 (.run (.close 40)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 68)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 43 (.step 55 (.step 43 (.step 71 (.run (.close 2))))))) (.step 4 (.step 71 (.step 43 (.run (.close 2)))))) (.step 2 (.run (.close 24))))) (.split 27 0 (.split 32 0 (.split 41 0 (.split 70 0 (.split 47 0 (.split 57 0 (.split 7 0 (.split 11 0 (.split 53 0 (.step 29 (.step 43 (.step 63 (.run (.close 11))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 8 0 (.split 24 0 (.split 39 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 69 0 (.split 6 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 12 0 (.split 54 0 (.step 43 (.step 31 (.run (.close 2)))) (.step 68 (.run (.close 31)))) (.step 68 (.run (.close 31)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 55 (.run (.close 3)))) (.step 2 (.run (.close 29)))) (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 55 (.run (.close 29)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part800.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part801
namespace Part802
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432546730830202017570959349881215142213603873833103936831156475840401934256323262162605113542287230099371641758004015754174109863068565504⟩
def references : Fin 1 → Box := ![Part801.root]
def proof : Enumeration.Proof 1 := (.split 48 0 (.split 5 0 (.reuse 0) (.split 24 0 (.split 39 0 (.split 58 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 6 0 (.split 11 0 (.split 50 0 (.split 35 0 (.step 55 (.step 40 (.step 4 (.step 23 (.run (.close 40)))))) (.step 4 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 24 0 (.split 39 0 (.split 41 0 (.split 50 0 (.split 59 0 (.split 69 0 (.split 53 0 (.split 70 0 (.split 4 0 (.split 6 0 (.split 18 0 (.split 19 0 (.split 10 0 (.step 3 (.step 2 (.run (.close 63)))) (.step 68 (.run (.close 3)))) (.step 55 (.run (.close 31)))) (.step 55 (.run (.close 31)))) (.step 2 (.run (.close 29)))) (.step 2 (.step 68 (.run (.close 4))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 68 (.run (.close 3)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))))
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
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671525840073512305702396937558630707244719933604933503724461231845432549570043968797285375558177339704733503443469452133591701952638610104993895624554136318912504851344709566485803416154655175909629231104⟩
def references : Fin 1 → Box := ![Part802.root]
def proof : Enumeration.Proof 1 := (.split 44 0 (.split 33 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 47 0 (.split 53 0 (.split 35 0 (.split 42 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 56 0 (.split 71 0 (.split 72 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.split 54 0 (.split 7 0 (.step 3 (.step 55 (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 40)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 40)))) (.step 4 (.run (.close 40)))) (.step 2 (.run (.close 23)))) (.step 4 (.run (.close 43)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 43 (.step 40 (.run (.close 2))))) (.step 4 (.step 71 (.step 43 (.run (.close 2)))))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24))))) (.split 5 0 (.split 11 0 (.split 24 0 (.split 32 0 (.split 39 0 (.split 53 0 (.split 58 0 (.split 50 0 (.split 59 0 (.split 70 0 (.split 74 0 (.split 4 0 (.split 10 0 (.split 69 0 (.step 29 (.step 43 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 2 (.step 68 (.run (.close 4))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 55 (.run (.close 29)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))))
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
def root : Box := ⟨3196670515523576047707425257429017156664978684471758904094018012589639516290363853739460254577290936407626284536251831122490883437872269255296155648, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593577855263904202822433904035153700014596365528938484928292311007855732494086349464437768469628594207903167195069284352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 53 0 (.split 57 0 (.split 66 0 (.split 71 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 42 0 (.split 4 0 (.split 13 0 (.split 27 0 (.step 9 (.run (.close 2))) (.step 4 (.run (.close 71)))) (.step 71 (.run (.close 16)))) (.step 58 (.run (.close 52)))) (.step 58 (.step 68 (.run (.close 52))))) (.step 71 (.run (.close 9)))) (.step 58 (.step 68 (.run (.close 23))))) (.step 55 (.run (.close 68)))) (.step 55 (.step 68 (.run (.close 58))))) (.step 55 (.run (.close 52)))) (.step 68 (.step 55 (.run (.close 52))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.step 55 (.run (.close 2)))))) (.step 71 (.step 68 (.step 58 (.run (.close 2)))))) (.step 4 (.step 68 (.step 58 (.run (.close 2)))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 58 (.step 4 (.run (.close 55))))))) (.step 58 (.step 63 (.run (.close 3))))) (.step 55 (.step 71 (.run (.close 68))))) (.step 4 (.step 68 (.step 58 (.run (.close 2)))))) (.step 4 (.step 68 (.step 58 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part804
namespace Part805
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406671525840073512305702396937558630707244719933604933503727657902360956125614978724360593577855263904202822433904035153700014598218202366281987419088143615871500612001784192418718653225529247293805143523328⟩
def references : Fin 2 → Box := ![Part803.root, Part804.root]
def proof : Enumeration.Proof 2 := (.split 26 0 (.split 49 0 (.split 31 0 (.reuse 0) (.split 14 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 35 0 (.split 4 0 (.split 42 0 (.split 56 0 (.split 10 0 (.split 16 0 (.split 30 0 (.split 24 0 (.split 27 0 (.split 32 0 (.step 24 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 3)))) (.step 43 (.run (.close 2)))) (.step 68 (.step 55 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 4 (.step 68 (.step 2 (.run (.close 43)))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 43)))) (.step 71 (.step 4 (.step 55 (.run (.close 43)))))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24))))) (.reuse 1)) (.split 5 0 (.split 11 0 (.split 31 0 (.split 32 0 (.split 33 0 (.split 41 0 (.split 53 0 (.split 70 0 (.step 29 (.step 71 (.split 14 0 (.split 16 0 (.split 17 0 (.split 7 0 (.split 13 0 (.step 43 (.step 18 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 58)))) (.step 4 (.run (.close 68)))) (.step 4 (.step 71 (.run (.close 68))))) (.step 2 (.run (.close 43)))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.step 4 (.run (.close 43))))) (.step 2 (.step 4 (.run (.close 43))))) (.step 2 (.run (.close 71)))) (.step 2 (.step 4 (.run (.close 43))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part803.covered
  · exact Part804.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part805
namespace Part806
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320369089219939735226668387296396066581035339365207075236680242650933321309526418567935375775883201217326198177410628626460097902542848, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126698173687161137261200283880132438860189797760662878556290246414294035096493141509030919410122820239215640444928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 18 0 (.split 38 0 (.split 56 0 (.split 26 0 (.split 35 0 (.split 41 0 (.split 49 0 (.split 6 0 (.step 70 (.step 46 (.step 4 (.step 3 (.run (.close 58)))))) (.step 7 (.step 3 (.run (.close 76))))) (.step 52 (.run (.close 2)))) (.step 70 (.run (.close 2)))) (.step 18 (.step 71 (.run (.close 9))))) (.step 18 (.step 71 (.run (.close 9))))) (.step 7 (.step 18 (.run (.close 2))))) (.step 18 (.step 7 (.step 18 (.step 58 (.run (.close 40))))))) (.step 18 (.split 4 0 (.step 3 (.step 26 (.split 7 0 (.step 70 (.run (.close 9))) (.step 18 (.run (.close 9)))))) (.step 43 (.run (.close 18)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 55 (.run (.close 58))))) (.step 68 (.step 55 (.run (.close 24))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 71 (.run (.close 75))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 71 (.run (.close 29))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 55 (.run (.close 68)))) (.step 55 (.run (.close 7))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part806
namespace Part807
def root : Box := ⟨4351082437154956072465106588077822995084026820419845514852619049831826777239679986705602047002372549485474646007070260176455444739091252863182751173123815036401417927025822315409571840000, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506799746206380355817958592079673826011521134078382056490341224119536822762549025096154785180806361489523557269504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 4 0 (.split 10 0 (.split 24 0 (.split 39 0 (.step 10 (.run (.close 4))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 5)))) (.step 58 (.run (.close 16)))) (.step 64 (.step 58 (.run (.close 10))))) (.step 71 (.step 4 (.run (.close 15))))) (.step 71 (.step 4 (.run (.close 9))))) (.step 71 (.run (.close 4)))) (.step 71 (.run (.close 4)))) (.step 71 (.run (.close 18)))) (.step 68 (.step 63 (.run (.close 55))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 55 (.run (.close 48))))) (.step 68 (.step 55 (.step 71 (.run (.close 58)))))) (.step 68 (.run (.close 64)))) (.step 68 (.step 63 (.step 55 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 71 (.step 68 (.run (.close 55))))) (.step 68 (.run (.close 71)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 55)))))) (.step 71 (.step 68 (.step 63 (.run (.close 55)))))) (.step 68 (.step 71 (.run (.close 40))))) (.step 68 (.step 71 (.run (.close 7)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part807
namespace Part808
def root : Box := ⟨2772669694120814859580762728965602278842130766530048192766299541285175124910982448911495716093046057721015855340665833804686950400, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186481560270615348548509760930964810211931410508354971574139704598248879804746258226589204480⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 74 0 (.split 27 0 (.split 32 0 (.split 70 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 7 0 (.split 13 0 (.split 54 0 (.split 63 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 18 0 (.split 19 0 (.split 42 0 (.step 18 (.step 29 (.run (.close 2)))) (.step 39 (.step 18 (.run (.close 29))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 28 (.run (.close 48)))) (.step 28 (.run (.close 48)))) (.step 28 (.run (.close 71)))) (.step 29 (.run (.close 55)))) (.step 18 (.step 29 (.run (.close 48))))) (.step 18 (.step 28 (.run (.close 2))))) (.step 28 (.run (.close 71)))) (.step 29 (.run (.close 58)))) (.step 29 (.run (.close 58)))) (.step 29 (.run (.close 58)))) (.step 29 (.run (.close 58)))) (.step 43 (.run (.close 39)))) (.step 43 (.step 40 (.run (.close 4))))) (.step 43 (.run (.close 39)))) (.step 43 (.step 40 (.step 29 (.run (.close 23)))))) (.step 43 (.step 40 (.run (.close 4))))) (.step 43 (.step 40 (.run (.close 4))))) (.step 43 (.step 40 (.run (.close 4))))) (.step 43 (.step 40 (.run (.close 4))))) (.step 43 (.step 40 (.run (.close 4))))) (.step 40 (.step 43 (.run (.close 4))))) (.step 43 (.step 40 (.step 68 (.run (.close 54)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 7 (.step 58 (.run (.close 43)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 40 (.step 18 (.run (.close 31)))))) (.step 43 (.step 40 (.run (.close 7))))) (.step 40 (.step 43 (.run (.close 4))))) (.step 43 (.step 40 (.run (.close 29)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part808
namespace Part809
def root : Box := ⟨2772669694120814859578414186382828445614243275226204494885492480265259392323635559764566696458801211133459728980269115235157147648, 5789234136395753406676424723384169652490427225114984554776825732692257267434155029221780752691462651784683348561180036589527660278127693170388628138370592684889352454261895698151142758868948949704478937483111349706012229632⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.split 7 0 (.split 24 0 (.split 13 0 (.split 62 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 58 0 (.split 70 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.step 29 (.split 66 0 (.split 38 0 (.split 56 0 (.split 6 0 (.step 68 (.step 18 (.run (.close 3)))) (.step 2 (.step 18 (.run (.close 3))))) (.step 43 (.step 18 (.run (.close 31))))) (.step 43 (.step 18 (.run (.close 31))))) (.step 2 (.step 43 (.step 68 (.run (.close 63))))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 55 (.step 43 (.run (.close 3)))))) (.step 2 (.step 55 (.step 43 (.run (.close 3)))))) (.step 2 (.step 55 (.step 43 (.run (.close 3)))))) (.step 2 (.step 68 (.step 43 (.run (.close 3)))))) (.step 2 (.step 55 (.step 43 (.run (.close 3)))))) (.step 2 (.step 55 (.step 43 (.run (.close 3)))))) (.step 2 (.step 68 (.step 43 (.run (.close 3)))))) (.step 2 (.step 68 (.step 43 (.run (.close 3)))))) (.step 18 (.step 68 (.step 31 (.run (.close 3)))))) (.step 3 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 10 (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 43)))) (.step 4 (.step 63 (.step 3 (.run (.close 31)))))) (.step 68 (.step 43 (.run (.close 18))))) (.step 2 (.step 3 (.run (.close 31))))))) (.step 2 (.step 55 (.step 43 (.run (.close 3)))))) (.step 2 (.step 18 (.step 16 (.step 28 (.run (.close 3))))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part809
namespace Part810
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449277552156342281065101655015424, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560987695078382459957397495291812332958160965009466454156452442734308360091336704⟩
def references : Fin 5 → Box := ![Part805.root, Part806.root, Part807.root, Part808.root, Part809.root]
def proof : Enumeration.Proof 5 := (.split 29 0 (.split 36 0 (.split 62 0 (.split 67 0 (.split 38 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 74 0 (.split 32 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 53 0 (.split 49 0 (.split 7 0 (.split 13 0 (.split 46 0 (.split 47 0 (.split 12 0 (.step 28 (.run (.close 29))) (.step 71 (.run (.close 29)))) (.step 48 (.run (.close 28)))) (.step 48 (.run (.close 16)))) (.step 18 (.run (.close 28)))) (.step 18 (.run (.close 28)))) (.step 58 (.run (.close 48)))) (.step 43 (.run (.close 40)))) (.step 43 (.run (.close 28)))) (.step 43 (.run (.close 28)))) (.step 43 (.run (.close 40)))) (.step 43 (.run (.close 28)))) (.step 71 (.step 55 (.run (.close 28))))) (.step 55 (.step 58 (.step 63 (.run (.close 28)))))) (.step 58 (.run (.close 43)))) (.step 71 (.step 43 (.run (.close 2))))) (.step 58 (.run (.close 43)))) (.step 43 (.step 71 (.run (.close 2))))) (.step 43 (.step 71 (.run (.close 2))))) (.step 63 (.step 58 (.run (.close 43))))) (.step 71 (.step 55 (.step 58 (.step 63 (.run (.close 16))))))) (.step 71 (.step 55 (.step 58 (.step 63 (.run (.close 28)))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.split 5 0 (.split 11 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 14 0 (.reuse 4) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 68 (.run (.close 43))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part805.covered
  · exact Part806.covered
  · exact Part807.covered
  · exact Part808.covered
  · exact Part809.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part810
namespace Part811
def root : Box := ⟨2772669694120814859578414186382828445614241285933258855738923858736266805040275157939963507067931449278790096381566445376554139648, 5789234131009374243490890251964829116295137629697777220811049217550377428141060633369183592086475582458318619894233303989003991819709555906246375611928632310582246557708323828981323234907640052119259761214449636075221549056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 7 0 (.split 24 0 (.split 13 0 (.split 62 0 (.split 27 0 (.split 32 0 (.split 39 0 (.split 58 0 (.split 49 0 (.split 6 0 (.split 70 0 (.split 12 0 (.split 50 0 (.split 54 0 (.split 59 0 (.split 69 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.step 43 (.run (.close 31)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.split 18 0 (.split 19 0 (.step 3 (.run (.close 13))) (.step 43 (.run (.close 18)))) (.step 43 (.run (.close 18))))) (.step 2 (.step 43 (.run (.close 18))))) (.step 18 (.step 68 (.run (.close 3))))) (.step 18 (.step 68 (.run (.close 3))))) (.split 69 0 (.step 40 (.step 15 (.run (.close 2)))) (.step 4 (.step 68 (.run (.close 18)))))) (.step 18 (.step 55 (.run (.close 52))))) (.split 10 0 (.split 16 0 (.split 17 0 (.step 15 (.step 71 (.run (.close 31)))) (.step 55 (.run (.close 40)))) (.step 55 (.run (.close 40)))) (.step 68 (.run (.close 15))))) (.step 2 (.step 68 (.run (.close 3))))) (.step 2 (.step 18 (.run (.close 15))))) (.step 18 (.step 55 (.step 18 (.run (.close 3)))))) (.step 2 (.step 55 (.run (.close 15))))) (.step 2 (.step 55 (.run (.close 15))))) (.step 2 (.step 68 (.step 43 (.run (.close 3)))))) (.step 2 (.step 68 (.step 43 (.run (.close 3)))))) (.step 18 (.step 68 (.step 31 (.run (.close 3)))))) (.step 3 (.split 6 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 16 (.step 71 (.run (.close 28)))) (.step 68 (.run (.close 43)))) (.step 68 (.run (.close 43)))) (.step 4 (.step 63 (.step 3 (.run (.close 31)))))) (.step 2 (.step 3 (.run (.close 31))))))) (.step 2 (.step 55 (.step 43 (.run (.close 3)))))) (.step 2 (.step 16 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 43)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part811
namespace Part812
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560987695078382459957397495291812332958160965009466455394392482019688634990460928⟩
def references : Fin 11 → Box := ![Part774.root, Part782.root, Part783.root, Part784.root, Part785.root, Part786.root, Part787.root, Part793.root, Part798.root, Part810.root, Part811.root]
def proof : Enumeration.Proof 11 := (.split 34 0 (.split 5 0 (.split 11 0 (.split 62 0 (.reuse 0) (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.reuse 1) (.split 26 0 (.split 35 0 (.split 16 0 (.split 17 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 22 0 (.split 38 0 (.split 56 0 (.split 4 0 (.split 10 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 30 0 (.split 67 0 (.step 2 (.run (.close 3))) (.step 68 (.step 3 (.run (.close 2))))) (.step 71 (.run (.close 31)))) (.step 4 (.step 68 (.step 4 (.run (.close 3)))))) (.step 4 (.step 68 (.step 4 (.run (.close 3)))))) (.step 2 (.run (.close 3)))) (.step 63 (.run (.close 3)))) (.step 2 (.run (.close 18)))) (.step 71 (.run (.close 2)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.run (.close 68)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 63))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 2 (.step 71 (.run (.close 68)))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6))) (.reuse 7)) (.reuse 8)) (.split 9 0 (.reuse 9) (.split 5 0 (.split 11 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 71 0 (.reuse 10) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 68 (.run (.close 43)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part774.covered
  · exact Part782.covered
  · exact Part783.covered
  · exact Part784.covered
  · exact Part785.covered
  · exact Part786.covered
  · exact Part787.covered
  · exact Part793.covered
  · exact Part798.covered
  · exact Part810.covered
  · exact Part811.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part812
namespace Part813
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5653548961323972919750931238434441558824122030381352534198420605895191149122179565906764098749063582650755611763994948295200554449842633257863547676460830041078101741932143713378876600033065001127934550796037314729476096⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 69 0 (.split 16 0 (.split 17 0 (.split 38 0 (.step 2 (.run (.close 4))) (.step 28 (.run (.close 2)))) (.step 24 (.step 59 (.step 2 (.run (.close 4)))))) (.step 24 (.step 47 (.step 43 (.run (.close 2)))))) (.split 31 0 (.split 33 0 (.split 41 0 (.step 28 (.step 68 (.run (.close 10)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40))))) (.split 5 0 (.split 16 0 (.split 11 0 (.split 17 0 (.split 22 0 (.split 27 0 (.split 63 0 (.split 64 0 (.split 31 0 (.split 33 0 (.step 31 (.step 48 (.run (.close 28)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 63)))) (.step 71 (.run (.close 63)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 5)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 28)))) (.split 5 0 (.split 11 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 69 0 (.split 46 0 (.split 7 0 (.split 47 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 63)))) (.step 71 (.run (.close 10)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 2 (.step 58 (.run (.close 28)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part813
namespace Part814
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169648139344787960032346849242165387555366412304039499906999923170822215300637612969563143767672577249297810808485030118341552912603458946669122406781714457665615472192023349490499283109019648⟩
def references : Fin 1 → Box := ![Part813.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 14 0 (.split 67 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 59 0 (.reuse 0) (.split 38 0 (.split 42 0 (.split 46 0 (.step 18 (.split 5 0 (.split 11 0 (.split 47 0 (.split 53 0 (.step 3 (.step 5 (.step 29 (.run (.close 10))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 48)))) (.step 4 (.run (.close 29)))) (.step 58 (.step 43 (.run (.close 28)))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 24 0 (.split 27 0 (.split 39 0 (.step 55 (.step 18 (.run (.close 10)))) (.step 2 (.step 4 (.run (.close 43))))) (.step 2 (.step 4 (.run (.close 40))))) (.step 2 (.step 4 (.run (.close 43))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71)))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169648139344787960032346849242165387555366412304039499906999923170822215300637612969563143767672577251334846784819516204609998601012837107720590800447650708301755921546404649253835989292417024⟩
def references : Fin 1 → Box := ![Part814.root]
def proof : Enumeration.Proof 1 := (.split 30 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 71 0 (.split 5 0 (.split 6 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 12 0 (.split 18 0 (.split 74 0 (.split 35 0 (.split 54 0 (.split 16 0 (.split 7 0 (.split 13 0 (.split 59 0 (.step 40 (.run (.close 28))) (.step 4 (.run (.close 71)))) (.step 55 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 55 (.run (.close 2)))) (.step 71 (.run (.close 58)))) (.step 71 (.run (.close 58)))) (.step 2 (.run (.close 55)))) (.step 55 (.run (.close 28)))) (.step 71 (.step 58 (.run (.close 4))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.step 71 (.run (.close 29))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.step 4 (.run (.close 40))))) (.step 2 (.step 4 (.run (.close 40))))) (.step 2 (.step 4 (.run (.close 40))))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169648139344787960032346849242165387555369688891317911572445981295274606207992126698173684921392519022479669574996581430604876874298612548893520154794555736693146983741677630238093471461146624⟩
def references : Fin 1 → Box := ![Part815.root]
def proof : Enumeration.Proof 1 := (.split 49 0 (.split 50 0 (.reuse 0) (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 5 (.step 9 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 5))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 55)))) (.step 58 (.step 68 (.step 4 (.run (.close 10)))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 71 (.step 63 (.step 55 (.run (.close 18)))))) (.step 58 (.step 48 (.step 43 (.run (.close 21))))))) (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 7 0 (.step 3 (.step 9 (.step 2 (.run (.close 3))))) (.step 2 (.run (.close 9)))) (.step 58 (.step 2 (.run (.close 18))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 27))))) (.step 58 (.run (.close 27)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 55)))) (.step 58 (.step 68 (.step 4 (.step 58 (.run (.close 9))))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 58 (.step 63 (.step 55 (.run (.close 9)))))) (.step 58 (.step 5 (.step 48 (.run (.close 9)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part815.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part816
namespace Part817
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483089765675624306157723450393755648, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506799746204140611075780789858409329371908509816122469133883231627222185411183446497231165621179996795409583308800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.split 48 0 (.split 66 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 6 0 (.split 12 0 (.split 49 0 (.split 54 0 (.split 50 0 (.split 7 0 (.split 18 0 (.split 19 0 (.step 7 (.run (.close 2))) (.step 55 (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 58 (.run (.close 4)))) (.step 71 (.step 58 (.run (.close 4))))) (.step 71 (.step 58 (.run (.close 4))))) (.step 58 (.run (.close 18)))) (.step 58 (.run (.close 18)))) (.step 2 (.step 68 (.run (.close 58))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.step 68 (.run (.close 18))))) (.step 2 (.run (.close 7)))) (.step 2 (.step 68 (.run (.close 58))))) (.step 2 (.run (.close 7)))) (.step 2 (.step 71 (.run (.close 55))))) (.step 2 (.step 71 (.run (.close 55))))) (.step 2 (.step 71 (.run (.close 55))))) (.step 2 (.step 68 (.step 43 (.run (.close 40)))))) (.step 2 (.step 68 (.step 43 (.run (.close 40)))))) (.step 2 (.step 68 (.step 43 (.run (.close 40)))))) (.step 2 (.step 18 (.run (.close 58)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part817
namespace Part818
def root : Box := ⟨2772669694120814859578414184143083703436437075375816576979730974947686861298922263800722966311483088498025024077928321953690550272, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506799746204140611075780789858409329371908509816122469133883231627222185411183446497232403561219282176783994060800⟩
def references : Fin 2 → Box := ![Part816.root, Part817.root]
def proof : Enumeration.Proof 2 := (.split 4 0 (.split 9 0 (.split 10 0 (.split 29 0 (.split 62 0 (.reuse 0) (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.split 74 0 (.split 47 0 (.split 57 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 24 0 (.split 39 0 (.step 10 (.step 4 (.run (.close 71)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 55)))) (.step 71 (.step 68 (.run (.close 40))))) (.step 68 (.step 55 (.run (.close 2))))) (.step 68 (.run (.close 65)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68)))))) (.step 2 (.split 12 0 (.step 18 (.run (.close 10))) (.step 3 (.run (.close 31)))))) (.reuse 1)) (.step 2 (.split 12 0 (.step 18 (.run (.close 10))) (.step 3 (.run (.close 31)))))) (.step 2 (.step 7 (.run (.close 71)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part816.covered
  · exact Part817.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part818
namespace Part819
def root : Box := ⟨2772669694120814859578414186382828445614241285933258857548175253069332358533571798700712067275274959678185969458805815225297666048, 5789234136395753406676424723384169652490427225114988419314348753465378364772918138331417960831141654743913954506802094748963129651186483549563560989504329776793022950988588453093706721172352976856028205598544438758633111552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 49 0 (.split 50 0 (.split 6 0 (.step 28 (.step 29 (.run (.close 2)))) (.step 2 (.run (.close 28)))) (.step 58 (.step 18 (.run (.close 28))))) (.step 18 (.step 58 (.run (.close 2))))) (.step 2 (.step 58 (.run (.close 40))))) (.step 2 (.step 58 (.run (.close 40))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 2 (.step 43 (.run (.close 28))))) (.step 2 (.step 43 (.run (.close 28))))) (.step 2 (.step 58 (.run (.close 40))))) (.step 2 (.step 71 (.step 43 (.run (.close 40)))))) (.step 2 (.step 58 (.run (.close 40))))) (.step 2 (.step 71 (.step 43 (.run (.close 40)))))) (.step 2 (.step 71 (.step 43 (.run (.close 40))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part819
namespace Part820
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5653543574944809734211675753360841556810052726769120728176678466701232207484834887021462615553294960389809390712187282520261761207134759691062070402896038227464254615068528188813236898165332613000701943067719142387744768⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 22 0 (.split 26 0 (.split 36 0 (.split 42 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 7 0 (.split 13 0 (.split 46 0 (.split 35 0 (.split 54 0 (.split 72 0 (.split 49 0 (.step 2 (.run (.close 58))) (.split 9 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 2))))) (.step 68 (.step 4 (.run (.close 9))))) (.step 10 (.step 2 (.run (.close 3))))) (.step 68 (.step 4 (.run (.close 9))))) (.split 47 0 (.split 53 0 (.step 12 (.run (.close 10))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 68))))) (.step 10 (.run (.close 2)))) (.step 10 (.run (.close 2)))) (.step 4 (.step 30 (.step 3 (.run (.close 2)))))) (.step 4 (.step 30 (.step 12 (.step 3 (.step 2 (.run (.close 4)))))))) (.step 4 (.step 30 (.step 10 (.run (.close 2)))))) (.split 72 0 (.split 24 0 (.step 10 (.run (.close 2))) (.step 71 (.step 4 (.run (.close 76))))) (.step 71 (.run (.close 2))))) (.split 72 0 (.split 42 0 (.split 24 0 (.step 10 (.run (.close 2))) (.step 71 (.step 4 (.run (.close 57))))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 2))))) (.step 4 (.step 10 (.step 68 (.step 10 (.step 2 (.run (.close 71)))))))) (.split 35 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 36 0 (.split 38 0 (.step 30 (.step 68 (.run (.close 5)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part820
namespace Part821
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5653543574944809734211675753360841556810052726769120728176678466701232207484834887021462615553294960389809390712187284760006503384938970248504350971340316349109751849719559666478964707875970436429898377568279773281517568⟩
def references : Fin 1 → Box := ![Part820.root]
def proof : Enumeration.Proof 1 := (.split 34 0 (.split 12 0 (.split 11 0 (.split 17 0 (.reuse 0) (.split 35 0 (.split 72 0 (.split 47 0 (.split 57 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 22 0 (.step 30 (.step 68 (.run (.close 5)))) (.step 63 (.step 2 (.run (.close 68))))) (.step 71 (.run (.close 72)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 18))))) (.split 35 0 (.split 72 0 (.split 36 0 (.split 38 0 (.step 30 (.step 4 (.step 30 (.run (.close 10))))) (.step 68 (.run (.close 64)))) (.step 68 (.run (.close 55)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 11 0 (.split 27 0 (.split 31 0 (.split 32 0 (.split 33 0 (.split 41 0 (.split 53 0 (.split 22 0 (.step 4 (.step 16 (.step 9 (.run (.close 48))))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 9 0 (.split 26 0 (.split 11 0 (.split 17 0 (.split 35 0 (.split 72 0 (.split 22 0 (.split 36 0 (.split 24 0 (.step 10 (.run (.close 2))) (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 10)))) (.step 68 (.run (.close 40)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 18)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 71 (.run (.close 10)))) (.step 18 (.step 68 (.step 18 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part820.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part821
namespace Part822
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243485986584588438705700382864198799891279783832873498196787219362694251252813784328756788637931197812276756518484705920666964019562278874388007789525367373642992896779220143843827985697872376775191084138496⟩
def references : Fin 1 → Box := ![Part821.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 74 0 (.split 30 0 (.reuse 0) (.split 9 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 11 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 24 0 (.split 36 0 (.split 29 0 (.split 39 0 (.split 58 0 (.split 12 0 (.split 18 0 (.step 65 (.step 64 (.run (.close 10)))) (.step 18 (.step 3 (.run (.close 62))))) (.step 4 (.run (.close 64)))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 18 (.run (.close 3)))) (.step 71 (.run (.close 10)))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 55 (.run (.close 10))))) (.step 63 (.step 55 (.run (.close 2))))) (.step 72 (.step 63 (.step 55 (.run (.close 2)))))) (.step 63 (.step 55 (.run (.close 8))))) (.step 71 (.step 55 (.run (.close 2))))) (.step 71 (.run (.close 65)))) (.step 71 (.step 55 (.run (.close 2))))) (.step 71 (.run (.close 18)))) (.step 71 (.run (.close 18)))) (.step 71 (.run (.close 18)))) (.step 18 (.step 64 (.step 18 (.run (.close 2))))))) (.split 17 0 (.split 22 0 (.split 7 0 (.split 34 0 (.step 4 (.split 13 0 (.step 31 (.step 30 (.step 68 (.run (.close 2))))) (.step 4 (.step 71 (.step 68 (.run (.close 5))))))) (.step 71 (.step 4 (.step 71 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 4))))) (.step 71 (.step 63 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2)))))) (.split 17 0 (.split 22 0 (.split 74 0 (.split 7 0 (.split 34 0 (.step 4 (.split 13 0 (.step 31 (.step 30 (.step 68 (.run (.close 2))))) (.step 4 (.step 71 (.run (.close 15)))))) (.step 71 (.step 4 (.run (.close 15))))) (.step 2 (.step 71 (.run (.close 4))))) (.step 2 (.run (.close 5)))) (.step 68 (.step 63 (.run (.close 31))))) (.step 63 (.step 4 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part821.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part822
namespace Part823
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243485986584588438705700382864198799891279783832873498196787219362694251252813784328756788637931197812276756518484705920666964019562278874388007789525367373644454398416551046762031671739514479409476191387648⟩
def references : Fin 1 → Box := ![Part822.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 16 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 9 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 14 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 74 0 (.split 11 0 (.split 12 0 (.split 17 0 (.split 7 0 (.step 35 (.split 29 0 (.split 22 0 (.step 4 (.step 35 (.step 2 (.run (.close 4))))) (.step 63 (.run (.close 23)))) (.step 18 (.run (.close 3))))) (.step 5 (.run (.close 30)))) (.step 63 (.run (.close 30)))) (.step 4 (.run (.close 34)))) (.step 63 (.run (.close 8)))) (.step 63 (.run (.close 31)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 63 (.run (.close 31)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.step 31 (.run (.close 3))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 71 (.step 4 (.step 2 (.run (.close 23)))))) (.step 71 (.step 4 (.step 2 (.run (.close 23)))))) (.step 71 (.step 4 (.run (.close 2)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 7 0 (.split 34 0 (.step 4 (.split 13 0 (.step 31 (.step 30 (.step 68 (.run (.close 2))))) (.step 4 (.run (.close 10))))) (.step 71 (.step 4 (.step 71 (.run (.close 2)))))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 5)))) (.step 68 (.step 63 (.run (.close 31))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 5)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part822.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part823
namespace Part824
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272278180592461356316119079004930048, 5789234131009374243485986584588438705700382864198799891279783832873498196787219362694251252813784328756788637931197812276756518484705920666964019562278874388007789525367373644454398416551046763299322339743861732477501440000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 9 0 (.split 29 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 6 0 (.split 24 0 (.split 39 0 (.split 58 0 (.step 64 (.run (.close 52))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 71 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 9)))) (.step 71 (.run (.close 64)))) (.step 71 (.step 40 (.run (.close 18))))) (.step 58 (.run (.close 16)))) (.step 64 (.run (.close 2)))) (.step 63 (.step 64 (.run (.close 4))))) (.step 72 (.step 64 (.step 4 (.run (.close 68)))))) (.step 63 (.step 64 (.step 4 (.run (.close 68)))))) (.step 31 (.step 16 (.run (.close 64))))) (.step 71 (.step 63 (.step 55 (.run (.close 2)))))) (.step 71 (.step 63 (.step 55 (.run (.close 2)))))) (.step 71 (.step 63 (.run (.close 64))))) (.step 63 (.step 71 (.step 4 (.run (.close 2)))))) (.step 71 (.step 63 (.step 4 (.run (.close 71)))))) (.step 71 (.step 63 (.step 4 (.run (.close 71)))))) (.step 71 (.step 63 (.step 4 (.run (.close 71)))))) (.step 63 (.step 71 (.step 4 (.run (.close 2)))))) (.step 63 (.step 71 (.step 4 (.run (.close 2)))))) (.step 18 (.step 31 (.step 65 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 18)))))))) (.step 18 (.step 31 (.step 64 (.step 18 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part824
namespace Part825
def root : Box := ⟨4898883310657342441196954343935776394038937435041614979870160492432575754684773045338455147274114335740136311283395281868909035564178663322436663885140058391062942067558153833567115414432112578549252096, 5653543574944809739110559064018183993757903128166895795175892990978402816827315398733783971864169488724488927271380944973580823051419447791782498987386156031692389834462640007977514015455078666422429331848739277554843648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.split 53 0 (.split 24 0 (.split 29 0 (.split 10 0 (.split 39 0 (.split 58 0 (.split 12 0 (.split 54 0 (.split 7 0 (.split 13 0 (.step 73 (.step 3 (.run (.close 52)))) (.step 3 (.run (.close 10)))) (.step 76 (.run (.close 10)))) (.step 4 (.run (.close 9)))) (.step 4 (.run (.close 15)))) (.step 3 (.run (.close 30)))) (.step 3 (.step 2 (.run (.close 5))))) (.step 64 (.run (.close 4)))) (.step 3 (.step 76 (.step 2 (.run (.close 58)))))) (.step 5 (.step 73 (.step 3 (.run (.close 2)))))) (.step 73 (.step 3 (.step 31 (.run (.close 2)))))) (.step 46 (.step 3 (.run (.close 15))))) (.step 70 (.step 68 (.step 3 (.run (.close 15)))))) (.step 76 (.step 65 (.step 64 (.step 55 (.run (.close 10))))))) (.step 72 (.step 54 (.step 70 (.step 46 (.step 18 (.step 70 (.step 4 (.step 18 (.run (.close 2))))))))))) (.step 64 (.step 15 (.step 5 (.step 3 (.run (.close 58))))))) (.step 76 (.step 52 (.step 68 (.run (.close 70)))))) (.split 53 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 38 0 (.step 52 (.step 3 (.step 4 (.run (.close 9))))) (.step 58 (.run (.close 18)))) (.step 71 (.run (.close 3)))) (.step 71 (.run (.close 3)))) (.step 71 (.run (.close 3)))) (.step 71 (.run (.close 3)))) (.step 4 (.run (.close 55))))) (.split 34 0 (.split 35 0 (.split 53 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 38 0 (.step 52 (.step 3 (.run (.close 46)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 18)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part825
namespace Part826
def root : Box := ⟨4898883310657342441196954343935776394038937435041614979870160492432575754684773045338455147274114335740136311283395281868909035564178663322436663885140058391062942067558153833567115414432112578549252096, 5789234131009374243490885467899096048137330714600197666346783047397775367396561843205963574170095203285123317467757005936970092804370364108530963224208651783686959451887981740146596099391306185562113541832681958013088563200⟩
def references : Fin 1 → Box := ![Part825.root]
def proof : Enumeration.Proof 1 := (.split 14 0 (.split 74 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.split 26 0 (.step 70 (.step 68 (.step 55 (.step 3 (.step 4 (.step 2 (.run (.close 23)))))))) (.step 71 (.run (.close 70))))) (.split 26 0 (.step 72 (.step 54 (.step 70 (.step 4 (.step 55 (.step 73 (.step 2 (.run (.close 4))))))))) (.step 71 (.step 4 (.step 2 (.run (.close 23))))))) (.split 26 0 (.step 65 (.split 35 0 (.step 65 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 24 0 (.step 70 (.split 17 0 (.step 64 (.step 55 (.step 73 (.step 4 (.run (.close 30)))))) (.step 23 (.step 63 (.run (.close 2)))))) (.step 63 (.run (.close 46)))) (.step 4 (.step 68 (.step 73 (.step 24 (.run (.close 2))))))) (.step 4 (.step 68 (.step 73 (.step 18 (.run (.close 3))))))) (.step 71 (.step 4 (.step 63 (.run (.close 2)))))) (.step 71 (.step 4 (.step 2 (.run (.close 23))))))) (.step 68 (.run (.close 55))))) (.step 68 (.run (.close 63))))) (.split 26 0 (.split 35 0 (.step 64 (.step 68 (.step 3 (.run (.close 2))))) (.step 68 (.run (.close 55)))) (.step 2 (.step 4 (.run (.close 71)))))) (.split 26 0 (.step 70 (.step 4 (.step 55 (.run (.close 2))))) (.step 4 (.run (.close 46))))) (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 11 0 (.step 52 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 71)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part825.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part826
namespace Part827
def root : Box := ⟨4898883310657342441196954343935776394038937435041614979870160492432575754684773045338455147274114335740136311283395281868909035564178663322436663885140058391062942067558153833567115414432112578549252096, 5789234131009374243490885467899096048137330714600201530884306064656120062748452778244867573180100879002403049740006694486440271074431044588105997386782601462592832246745666421890210792684332640218709653990921747198849843200⟩
def references : Fin 1 → Box := ![Part826.root]
def proof : Enumeration.Proof 1 := (.split 46 0 (.split 47 0 (.split 57 0 (.split 8 0 (.reuse 0) (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 11 0 (.step 52 (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 5)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 71))))) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 64 (.step 73 (.split 16 0 (.step 76 (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 55)))))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68)))) (.step 2 (.step 68 (.run (.close 4))))) (.step 2 (.step 68 (.run (.close 4)))))) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 65 (.step 64 (.step 55 (.step 30 (.step 71 (.step 76 (.step 55 (.run (.close 3))))))))) (.step 71 (.run (.close 55)))) (.step 71 (.run (.close 68)))) (.step 71 (.run (.close 68)))) (.step 2 (.step 68 (.run (.close 4))))) (.step 2 (.step 68 (.run (.close 4)))))) (.split 38 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 64 (.step 31 (.run (.close 2)))) (.step 71 (.run (.close 55)))) (.step 71 (.run (.close 55)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 63)))) (.step 2 (.run (.close 63)))) (.step 58 (.run (.close 55)))))
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
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243490885467899096048137330714600201530884306064656120062748452778244867573180100879002403049740006694486440271074431044588105997386782601462592832246745666421890210792684332640219947594030207127473748967424⟩
def references : Fin 3 → Box := ![Part823.root, Part824.root, Part827.root]
def proof : Enumeration.Proof 3 := (.split 67 0 (.split 10 0 (.split 6 0 (.reuse 0) (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 12 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 33 0 (.split 41 0 (.split 24 0 (.split 16 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 7 0 (.split 17 0 (.split 22 0 (.step 15 (.run (.close 9))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 10 (.run (.close 71)))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 71 (.run (.close 5)))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 3))))) (.step 2 (.step 68 (.run (.close 3))))) (.step 2 (.step 68 (.run (.close 3))))) (.step 4 (.step 15 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71))))) (.step 2 (.step 4 (.run (.close 71)))))) (.reuse 1)) (.split 9 0 (.reuse 2) (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 33 0 (.split 41 0 (.step 64 (.step 71 (.step 48 (.step 18 (.run (.close 2)))))) (.step 2 (.run (.close 70)))) (.step 2 (.step 4 (.run (.close 18))))) (.step 2 (.step 18 (.run (.close 3))))) (.step 3 (.run (.close 18)))) (.step 3 (.step 76 (.run (.close 10))))) (.step 3 (.step 76 (.run (.close 10))))) (.step 2 (.run (.close 52)))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 52)))) (.step 2 (.run (.close 64)))) (.step 2 (.run (.close 52)))) (.step 3 (.run (.close 64)))) (.step 3 (.run (.close 52))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part823.covered
  · exact Part824.covered
  · exact Part827.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part828
namespace Part829
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086718681813352448, 5789234131009374243490885467899096048137330714600201530884306064656120062748452778244867573180100879002403049740006694486440271074431044588105997386782601462592832246745666421890210792684332640219947594030208254473167437824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 9 0 (.split 29 0 (.split 8 0 (.split 18 0 (.split 19 0 (.split 14 0 (.split 74 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 11 0 (.split 53 0 (.split 38 0 (.split 72 0 (.split 16 0 (.split 17 0 (.split 36 0 (.step 46 (.split 54 0 (.split 67 0 (.step 10 (.run (.close 27))) (.step 70 (.step 71 (.run (.close 52))))) (.step 71 (.step 18 (.run (.close 4)))))) (.step 72 (.step 7 (.run (.close 2))))) (.step 72 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 48)))) (.step 18 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 10)))) (.step 2 (.step 72 (.step 31 (.run (.close 40)))))) (.step 2 (.step 7 (.run (.close 5))))) (.step 2 (.step 72 (.run (.close 7))))) (.step 2 (.step 18 (.step 64 (.run (.close 4)))))) (.step 18 (.step 70 (.split 6 0 (.step 30 (.step 5 (.run (.close 18)))) (.step 2 (.run (.close 18))))))) (.step 2 (.step 58 (.run (.close 55))))) (.step 2 (.step 58 (.run (.close 55))))) (.step 2 (.run (.close 13)))) (.step 18 (.step 7 (.run (.close 2))))) (.step 2 (.step 7 (.run (.close 4))))) (.step 2 (.run (.close 13)))) (.step 18 (.step 54 (.split 6 0 (.step 30 (.step 9 (.run (.close 7)))) (.step 2 (.run (.close 9))))))) (.step 18 (.split 10 0 (.step 65 (.split 14 0 (.split 16 0 (.split 17 0 (.step 10 (.run (.close 2))) (.step 68 (.step 63 (.run (.close 23))))) (.step 68 (.step 63 (.run (.close 23))))) (.step 71 (.step 4 (.run (.close 63)))))) (.step 18 (.run (.close 7)))))) (.step 2 (.step 7 (.run (.close 4))))) (.step 2 (.step 18 (.step 65 (.run (.close 10)))))) (.step 2 (.step 18 (.step 64 (.run (.close 18))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part829
namespace Part830
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234131009374243490885467899096048137330714600201530884306064656120062748452778244867573180100879002403049740006694486440271074431044588105997388591852856925897800238963062650959352891676150620581407146733004596810088448⟩
def references : Fin 2 → Box := ![Part828.root, Part829.root]
def proof : Enumeration.Proof 2 := (.split 25 0 (.split 4 0 (.split 5 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 35 0 (.split 72 0 (.split 34 0 (.split 36 0 (.split 54 0 (.step 30 (.split 38 0 (.split 7 0 (.split 49 0 (.split 9 0 (.split 18 0 (.split 19 0 (.step 30 (.split 24 0 (.step 55 (.step 48 (.run (.close 8)))) (.step 2 (.run (.close 48))))) (.step 4 (.step 68 (.run (.close 23))))) (.step 4 (.step 68 (.run (.close 30))))) (.step 2 (.run (.close 64)))) (.step 4 (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 35 (.step 68 (.step 55 (.run (.close 2))))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 63 (.step 68 (.step 55 (.run (.close 2)))))) (.step 68 (.step 63 (.step 55 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 4 (.step 68 (.step 4 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 2))))) (.step 2 (.step 4 (.run (.close 71)))))) (.reuse 1)) (.split 34 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 74 0 (.split 11 0 (.split 16 0 (.split 35 0 (.split 17 0 (.step 10 (.split 22 0 (.split 6 0 (.split 12 0 (.split 72 0 (.split 49 0 (.step 10 (.split 69 0 (.step 2 (.run (.close 71))) (.step 72 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 64)))) (.step 2 (.run (.close 58)))) (.step 68 (.run (.close 55))))) (.step 68 (.step 71 (.step 55 (.run (.close 2)))))) (.step 71 (.run (.close 10)))) (.step 68 (.step 18 (.step 55 (.run (.close 2)))))) (.step 2 (.step 58 (.run (.close 55))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 68 (.step 71 (.run (.close 9)))))) (.step 2 (.step 68 (.step 71 (.run (.close 9)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 58 (.step 18 (.step 55 (.step 16 (.run (.close 28))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part828.covered
  · exact Part829.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part830
namespace Part831
def root : Box := ⟨4355331541097490209254623293730242744102663565361661770238214602937430005718566804645275602278316579560268318362391787906456571876557824986198038231990155864036807631811627967890218549248, 5653543574944809739110559064018188344840340283126832797805494812369691265872893735190388619366928819478234869252035373369797837236153941499852887955400313035235231180202918651975468259880063245911788214046333013430632448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 26 0 (.split 35 0 (.split 72 0 (.split 10 0 (.split 34 0 (.split 69 0 (.split 36 0 (.split 30 0 (.split 38 0 (.split 18 0 (.split 27 0 (.split 29 0 (.split 6 0 (.split 12 0 (.split 24 0 (.split 9 0 (.split 19 0 (.step 65 (.step 64 (.run (.close 10)))) (.step 72 (.step 65 (.run (.close 10))))) (.step 3 (.run (.close 64)))) (.step 30 (.run (.close 5)))) (.step 5 (.run (.close 64)))) (.step 10 (.run (.close 2)))) (.step 65 (.run (.close 2)))) (.step 65 (.step 64 (.step 5 (.step 2 (.run (.close 4))))))) (.step 65 (.run (.close 3)))) (.step 65 (.run (.close 2)))) (.step 65 (.run (.close 2)))) (.step 72 (.step 65 (.step 64 (.step 2 (.run (.close 58))))))) (.step 72 (.step 65 (.step 64 (.run (.close 2)))))) (.step 64 (.step 4 (.step 18 (.run (.close 2)))))) (.step 64 (.run (.close 2)))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.step 5 (.step 3 (.step 76 (.run (.close 10))))) (.step 4 (.run (.close 10)))) (.step 71 (.run (.close 64)))) (.step 4 (.step 71 (.run (.close 9))))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 76)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 64))))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.step 5 (.step 3 (.step 65 (.run (.close 10))))) (.step 4 (.run (.close 10)))) (.step 71 (.run (.close 64)))) (.step 4 (.run (.close 21)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 64))))) (.step 10 (.step 53 (.step 71 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part831
namespace Part832
def root : Box := ⟨4355331541097490209254623293730242744102663565361661770238214602937430005718566804645275602278316579560268318362391787906456571876557824986198038231990155864036807631811627967890218549248, 5789234131009374243490885467899096052488413151755157603349412652733943057832479595613153387947271289857827937083110029975331600921553208501838932299927201959355234441609433451228791974845612819758363553063482863653197185024⟩
def references : Fin 1 → Box := ![Part831.root]
def proof : Enumeration.Proof 1 := (.split 74 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.reuse 0) (.split 26 0 (.split 35 0 (.step 72 (.step 65 (.step 64 (.step 10 (.run (.close 2)))))) (.step 68 (.step 4 (.run (.close 63))))) (.step 2 (.run (.close 10))))) (.split 26 0 (.split 35 0 (.step 65 (.step 64 (.step 65 (.step 30 (.step 55 (.run (.close 5))))))) (.step 4 (.step 71 (.run (.close 30))))) (.step 4 (.run (.close 30))))) (.split 26 0 (.split 35 0 (.step 72 (.step 64 (.step 65 (.step 64 (.step 30 (.step 55 (.run (.close 18)))))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 4 (.run (.close 30))))) (.split 26 0 (.split 35 0 (.step 65 (.step 68 (.step 65 (.step 4 (.step 68 (.step 2 (.run (.close 4)))))))) (.step 68 (.run (.close 65)))) (.step 68 (.run (.close 65))))) (.split 35 0 (.split 72 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 6 0 (.step 30 (.step 62 (.step 63 (.run (.close 5))))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 73)))) (.step 63 (.run (.close 30)))) (.step 63 (.run (.close 65)))) (.step 71 (.run (.close 30)))) (.step 71 (.run (.close 30)))) (.step 71 (.run (.close 65)))) (.step 71 (.run (.close 30)))) (.step 71 (.run (.close 64)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))))
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
def root : Box := ⟨4355331541097490209254623293730242744102663565361661770238214602937430005718566804645275602278316579560268318362391787906456571876557824986198038231990155864036807631811627967890218549248, 5789234131009374243490885467899096052488413151755157603349412652733943057832479598661735956615232453316418981802999000432946974617814098012734400684079290650532597840345862224170171454410676449245180913014516526633921282048⟩
def references : Fin 1 → Box := ![Part832.root]
def proof : Enumeration.Proof 1 := (.split 47 0 (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 6 0 (.step 30 (.run (.close 52))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 30)))) (.step 71 (.run (.close 65)))) (.step 71 (.run (.close 30)))) (.step 71 (.run (.close 64)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 5)))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 71 (.step 63 (.run (.close 30))))) (.step 71 (.step 63 (.run (.close 30))))) (.step 63 (.run (.close 65))))) (.split 26 0 (.split 35 0 (.split 72 0 (.split 14 0 (.step 65 (.step 64 (.run (.close 30)))) (.step 2 (.run (.close 64)))) (.step 68 (.run (.close 64)))) (.step 68 (.run (.close 64)))) (.step 2 (.step 4 (.run (.close 71)))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 10 (.step 31 (.step 53 (.split 72 0 (.step 31 (.run (.close 2))) (.step 4 (.run (.close 2))))))) (.step 71 (.run (.close 30)))) (.step 63 (.run (.close 30)))) (.step 63 (.run (.close 65)))) (.step 2 (.run (.close 52))))) (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.step 30 (.step 65 (.step 55 (.step 64 (.step 4 (.run (.close 68))))))) (.step 4 (.run (.close 64)))) (.step 2 (.step 4 (.run (.close 71))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.step 63 (.run (.close 2)))))) (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 65 (.step 68 (.step 65 (.run (.close 3))))) (.step 71 (.run (.close 65)))) (.step 71 (.run (.close 65)))) (.step 2 (.run (.close 58)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part832.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part833
namespace Part834
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676419939313869692557664905278705561440342684860182702574861324664923849874341792288359586176538827114385984569321251411835599695766071499792601724644089807129274287495823425817993640316078544682167042048⟩
def references : Fin 2 → Box := ![Part830.root, Part833.root]
def proof : Enumeration.Proof 2 := (.split 71 0 (.split 62 0 (.reuse 0) (.split 46 0 (.reuse 1) (.split 6 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 64 (.step 68 (.step 65 (.run (.close 64))))) (.step 71 (.run (.close 64)))) (.step 71 (.run (.close 64)))) (.step 2 (.run (.close 58)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.run (.close 10)))))) (.split 26 0 (.split 35 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 72 0 (.split 4 0 (.split 10 0 (.split 14 0 (.split 74 0 (.split 69 0 (.split 30 0 (.split 49 0 (.split 50 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 72 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 3)))) (.step 2 (.run (.close 18)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 72)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 71 (.step 68 (.run (.close 72))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 58)))) (.step 71 (.step 4 (.step 68 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part830.covered
  · exact Part833.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part834
namespace Part835
def root : Box := ⟨4784065733063815222685827691755578192996894394965684614511949189904138725953805823276162497272050089278011196674802056171423779693509708668398289443269995715226457839938902122159227975726757102747648, 5789234136395753406676424723379602756368638487163863180229018976102157919240839091672297498624699523294458819000570867038418878858959654853164839908485313420763876180426684298130560683843898630956005770518964148002122366976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 6 0 (.split 12 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 35 0 (.split 71 0 (.step 30 (.split 9 0 (.step 70 (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 3))))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 71)))) (.split 4 0 (.split 24 0 (.split 26 0 (.step 12 (.step 68 (.step 2 (.run (.close 48))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 71))))) (.split 4 0 (.split 13 0 (.split 24 0 (.split 26 0 (.step 12 (.step 76 (.step 2 (.run (.close 48))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 28))))) (.split 4 0 (.split 10 0 (.split 13 0 (.split 24 0 (.split 26 0 (.step 12 (.step 76 (.step 68 (.step 2 (.run (.close 48)))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 3)))) (.step 2 (.run (.close 10))))) (.step 68 (.step 58 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 28))))) (.step 68 (.step 58 (.run (.close 28))))) (.step 71 (.step 68 (.step 63 (.step 3 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 3))))) (.step 68 (.step 71 (.run (.close 28))))) (.step 68 (.step 63 (.step 71 (.run (.close 28)))))) (.step 2 (.step 68 (.run (.close 55))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part835
namespace Part836
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676424723384165196986260682382504351834719267427051147748087651602876691142598798461667496387076779849736250258738297162738434315796002125485251618424938457489461162207643082481534203366050428049214668800⟩
def references : Fin 2 → Box := ![Part834.root, Part835.root]
def proof : Enumeration.Proof 2 := (.split 64 0 (.split 66 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.reuse 1) (.step 71 (.step 68 (.step 63 (.run (.close 8)))))) (.step 71 (.step 68 (.step 63 (.run (.close 8)))))) (.step 2 (.step 68 (.run (.close 55))))) (.step 2 (.step 68 (.run (.close 55)))))) (.split 26 0 (.split 35 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 8 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 53 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.split 18 0 (.split 71 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 30 0 (.split 57 0 (.split 49 0 (.step 3 (.run (.close 2))) (.step 71 (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 4 (.step 18 (.step 9 (.run (.close 2)))))) (.step 63 (.step 4 (.run (.close 3))))) (.step 63 (.run (.close 3)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 4)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 71 (.step 68 (.step 71 (.run (.close 55)))))) (.step 71 (.step 68 (.run (.close 65))))) (.step 2 (.step 4 (.run (.close 55))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.run (.close 65)))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.step 2 (.run (.close 55)))))) (.step 2 (.run (.close 58)))) (.step 71 (.step 63 (.step 55 (.run (.close 2)))))) (.step 2 (.step 71 (.run (.close 68))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part834.covered
  · exact Part835.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part836
namespace Part837
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676424723384169652494676329057522556103865459117798113791551761524683897385292059472572973611087039530216052379245893493118877279084391469923456086626108626104031203432436297320083383312290743356043034624⟩
def references : Fin 1 → Box := ![Part836.root]
def proof : Enumeration.Proof 1 := (.split 63 0 (.reuse 0) (.split 26 0 (.split 35 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 8 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 42 0 (.split 53 0 (.split 4 0 (.split 6 0 (.split 10 0 (.split 12 0 (.split 18 0 (.split 64 0 (.split 71 0 (.split 72 0 (.split 14 0 (.split 74 0 (.split 46 0 (.split 47 0 (.split 30 0 (.split 57 0 (.split 49 0 (.step 3 (.run (.close 2))) (.step 71 (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 4 (.step 18 (.step 9 (.run (.close 2)))))) (.step 63 (.step 4 (.run (.close 3))))) (.step 63 (.run (.close 3)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 4)))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.run (.close 64))))) (.step 71 (.step 68 (.run (.close 64))))) (.step 71 (.step 68 (.run (.close 64))))) (.step 2 (.run (.close 64)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.step 4 (.run (.close 68))))) (.step 71 (.step 68 (.run (.close 2))))) (.step 68 (.step 71 (.step 2 (.run (.close 55)))))) (.step 2 (.run (.close 58)))) (.step 71 (.step 63 (.step 55 (.step 40 (.step 71 (.run (.close 3)))))))) (.step 2 (.step 71 (.run (.close 68))))))
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
def root : Box := ⟨4249103942534136789516705652419749018639866690366571380599604396953836504770980724199048692709130517686556582799271354357514248609910772926410392865393683535837309103766005867608014848, 5789234136395753406676424723384169652494676329057522552329903030781480359563128128214232113330926185726163297406925075408190092282224953568640362653650941993165992463404804137398158420742309428190765661321844875112422047744⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 24 0 (.split 7 0 (.split 35 0 (.split 72 0 (.split 39 0 (.split 31 0 (.split 63 0 (.split 33 0 (.split 64 0 (.split 46 0 (.step 30 (.step 12 (.step 3 (.step 72 (.step 55 (.run (.close 52))))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 71)))) (.step 71 (.step 63 (.step 68 (.run (.close 3)))))) (.split 4 0 (.split 24 0 (.split 26 0 (.step 12 (.split 30 0 (.split 62 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 71))))) (.split 4 0 (.split 13 0 (.split 24 0 (.split 26 0 (.step 12 (.split 30 0 (.split 62 0 (.split 67 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 10)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 28))))) (.split 4 0 (.split 10 0 (.split 13 0 (.split 24 0 (.split 26 0 (.step 12 (.split 27 0 (.split 30 0 (.split 32 0 (.split 62 0 (.split 67 0 (.step 22 (.step 2 (.run (.close 55)))) (.step 68 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 18 (.run (.close 3))))) (.step 2 (.run (.close 10)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part838
namespace Part839
def root : Box := ⟨4249103942534136789516705652419749018636744941816258227581989579438459546761356688574096040469836545563104185631542138109613135467485273889042416573200248641541885605344270451839336448, 5789234136395753406676424723384169652494676329057522556103865455603021711804682709202501007087063880607566309312314194536088619990904514244160545321047945803895512953511825367493394155096327058075595330134061996409748455424⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 4 0 (.split 24 0 (.split 10 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 48))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 71)))) (.step 71 (.step 63 (.step 68 (.run (.close 3)))))) (.split 4 0 (.split 13 0 (.split 24 0 (.split 26 0 (.step 12 (.split 30 0 (.split 62 0 (.step 2 (.run (.close 55))) (.step 68 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 71))))) (.split 4 0 (.split 13 0 (.split 24 0 (.split 26 0 (.step 12 (.split 27 0 (.split 30 0 (.split 32 0 (.split 62 0 (.step 9 (.run (.close 2))) (.step 68 (.run (.close 10)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 28))))) (.split 4 0 (.split 10 0 (.split 13 0 (.split 24 0 (.split 26 0 (.step 12 (.split 27 0 (.split 30 0 (.split 32 0 (.split 62 0 (.step 9 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 4)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 18 (.run (.close 3))))) (.step 2 (.run (.close 28))))) (.step 68 (.step 58 (.run (.close 10))))) (.step 71 (.step 63 (.run (.close 10))))) (.step 68 (.step 58 (.run (.close 10))))) (.step 3 (.step 48 (.step 63 (.run (.close 10)))))) (.step 2 (.step 71 (.run (.close 3)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part839
namespace Part840
def root : Box := ⟨4249103942534136789516705652419749018636744941816255388368222799724043338465232126056383721558271360726931211060451588737393942506847280955250565934272276912941861128086717582301724672, 5789234136395753406676424723384169652494676329057522556103865459117798113791554883273234216216737207849517182985688912690876429669308317834914675625394301784915795585689810111008982881002485675671578855765227584510886936576⟩
def references : Fin 3 → Box := ![Part837.root, Part838.root, Part839.root]
def proof : Enumeration.Proof 3 := (.split 44 0 (.split 48 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 6 0 (.split 12 0 (.split 38 0 (.split 42 0 (.split 56 0 (.reuse 1) (.step 68 (.step 58 (.step 18 (.run (.close 2)))))) (.step 71 (.step 63 (.step 68 (.run (.close 55)))))) (.step 68 (.step 58 (.step 18 (.step 3 (.run (.close 2))))))) (.step 71 (.step 68 (.step 63 (.step 3 (.run (.close 2))))))) (.step 2 (.step 71 (.run (.close 3))))) (.step 71 (.step 68 (.step 63 (.step 55 (.run (.close 2))))))) (.step 68 (.step 63 (.step 71 (.step 55 (.run (.close 28))))))) (.step 2 (.step 68 (.run (.close 55))))) (.step 2 (.step 4 (.run (.close 68))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.step 68 (.run (.close 55))))))) (.step 71 (.step 68 (.step 63 (.step 55 (.run (.close 2))))))) (.step 2 (.step 68 (.run (.close 55))))) (.step 2 (.step 68 (.run (.close 55)))))) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 8 0 (.split 14 0 (.split 22 0 (.split 53 0 (.split 34 0 (.split 36 0 (.reuse 2) (.step 68 (.step 71 (.step 63 (.run (.close 10)))))) (.step 68 (.step 71 (.step 28 (.run (.close 2)))))) (.step 2 (.run (.close 10)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 71 (.step 68 (.step 63 (.run (.close 30)))))) (.step 68 (.step 63 (.step 18 (.step 31 (.run (.close 30))))))) (.step 2 (.step 68 (.run (.close 55))))) (.step 2 (.step 68 (.run (.close 55))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part837.covered
  · exact Part838.covered
  · exact Part839.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part840
namespace Part841
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5783586103091957808496987250214686792406378902833960374507899534368857180682313012842877255319085414405159289425956398490277498727068883741708383288422793979998999109642293688065072650838956544680975496183503555313778294784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 38 0 (.split 56 0 (.split 26 0 (.split 27 0 (.split 59 0 (.split 72 0 (.split 74 0 (.split 70 0 (.step 46 (.step 54 (.step 61 (.step 27 (.run (.close 4)))))) (.split 6 0 (.split 8 0 (.step 70 (.step 61 (.step 63 (.run (.close 4))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 22 0 (.split 41 0 (.step 62 (.step 68 (.run (.close 27)))) (.step 2 (.run (.close 24)))) (.step 68 (.run (.close 62))))) (.step 68 (.step 54 (.step 70 (.step 68 (.run (.close 2))))))) (.step 62 (.split 6 0 (.split 8 0 (.step 54 (.step 61 (.step 62 (.run (.close 9))))) (.step 61 (.run (.close 46)))) (.step 57 (.run (.close 46)))))) (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 61 (.step 27 (.run (.close 11)))) (.step 71 (.step 4 (.step 55 (.run (.close 2)))))) (.step 55 (.run (.close 46)))) (.step 71 (.step 4 (.step 63 (.run (.close 2)))))) (.step 55 (.run (.close 46))))) (.split 14 0 (.split 74 0 (.step 46 (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68))))) (.split 8 0 (.split 14 0 (.split 16 0 (.step 54 (.step 68 (.step 4 (.run (.close 58))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 5))))) (.split 8 0 (.split 14 0 (.split 16 0 (.split 56 0 (.split 17 0 (.split 22 0 (.split 26 0 (.step 54 (.step 4 (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 55 (.step 5 (.step 58 (.run (.close 2)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 5)))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part841
namespace Part842
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5783586103091957808496987250214686792406378902833960374507899537883633582669185186913610464448758741647110163099328768100242789830066993641308281976982581392996796811511301761264020526052759209010745575044839049012319354880⟩
def references : Fin 1 → Box := ![Part841.root]
def proof : Enumeration.Proof 1 := (.split 5 0 (.split 11 0 (.split 53 0 (.split 25 0 (.reuse 0) (.split 14 0 (.split 16 0 (.split 38 0 (.split 56 0 (.split 74 0 (.step 46 (.run (.close 4))) (.step 2 (.run (.close 43)))) (.step 55 (.step 5 (.step 58 (.run (.close 2)))))) (.step 55 (.step 5 (.step 58 (.run (.close 2)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.split 25 0 (.split 38 0 (.split 56 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 61 (.run (.close 2))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 23)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.split 25 0 (.split 38 0 (.split 56 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 16 0 (.split 17 0 (.step 61 (.run (.close 2))) (.step 31 (.run (.close 54)))) (.step 31 (.step 7 (.step 63 (.run (.close 4)))))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 71)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55))))) (.split 25 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 42 0 (.split 11 0 (.split 16 0 (.step 27 (.run (.close 2))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 48)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 68 (.run (.close 55)))) (.step 2 (.run (.close 7)))) (.step 68 (.run (.close 55)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part841.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part842
namespace Part843
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5783586103091957808496987250214686792406378902833960374507899537883633582669185186913610464448758741647110163099328768100242789830066993641308281976982581392996796811511301761264020526052759210278396175273068451608534188032⟩
def references : Fin 1 → Box := ![Part842.root]
def proof : Enumeration.Proof 1 := (.split 4 0 (.split 10 0 (.reuse 0) (.split 5 0 (.split 8 0 (.split 25 0 (.split 26 0 (.split 11 0 (.split 38 0 (.split 14 0 (.split 35 0 (.split 67 0 (.split 22 0 (.step 54 (.step 46 (.split 12 0 (.split 17 0 (.step 61 (.step 2 (.run (.close 24)))) (.step 24 (.step 31 (.run (.close 11))))) (.step 43 (.step 2 (.run (.close 23))))))) (.step 7 (.step 54 (.step 48 (.run (.close 24)))))) (.step 54 (.step 70 (.step 61 (.step 2 (.run (.close 24))))))) (.step 7 (.step 52 (.step 68 (.step 54 (.step 4 (.run (.close 43)))))))) (.step 7 (.step 52 (.step 68 (.step 54 (.step 68 (.run (.close 11)))))))) (.step 7 (.step 64 (.split 14 0 (.step 54 (.step 55 (.step 54 (.step 33 (.step 71 (.run (.close 23))))))) (.step 68 (.run (.close 5))))))) (.step 7 (.step 64 (.split 38 0 (.split 35 0 (.split 72 0 (.split 14 0 (.step 48 (.step 54 (.run (.close 31)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 48)))) (.step 68 (.run (.close 55))))))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))) (.split 5 0 (.split 8 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 11 0 (.step 54 (.split 67 0 (.split 41 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 43)))) (.step 70 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 58)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
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
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223674523533435127907585386672906575011573125160405941591560804154570333043065915249633846288711680⟩
def references : Fin 1 → Box := ![Part843.root]
def proof : Enumeration.Proof 1 := (.split 73 0 (.split 33 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 56 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 54 0 (.split 4 0 (.step 36 (.run (.close 2))) (.step 2 (.run (.close 11)))) (.step 3 (.run (.close 23)))) (.step 68 (.run (.close 27)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 3 (.run (.close 18))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 54)))) (.step 2 (.run (.close 54))))) (.split 5 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 16 0 (.split 22 0 (.split 25 0 (.split 38 0 (.split 59 0 (.split 72 0 (.step 54 (.step 70 (.step 46 (.step 54 (.run (.close 18)))))) (.step 71 (.run (.close 70)))) (.step 62 (.run (.close 18)))) (.step 58 (.step 65 (.step 54 (.step 5 (.step 76 (.run (.close 28)))))))) (.step 58 (.step 54 (.run (.close 46))))) (.step 55 (.step 62 (.run (.close 2))))) (.step 55 (.step 63 (.step 65 (.step 54 (.step 4 (.run (.close 23)))))))) (.step 55 (.step 63 (.step 5 (.run (.close 27)))))) (.step 55 (.step 3 (.run (.close 8))))) (.step 55 (.step 3 (.run (.close 8))))) (.step 55 (.step 3 (.run (.close 8))))))
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
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521028977982484251848051457388609969372266496, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725561291506214810041864041055510282816691858155683370726404850705160470528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 31 0 (.split 33 0 (.split 25 0 (.split 41 0 (.split 24 0 (.split 26 0 (.split 49 0 (.split 35 0 (.split 6 0 (.step 54 (.step 46 (.split 67 0 (.step 71 (.run (.close 10))) (.step 70 (.run (.close 18)))))) (.step 3 (.step 58 (.run (.close 18))))) (.step 71 (.step 4 (.run (.close 71))))) (.step 64 (.step 52 (.run (.close 71))))) (.step 71 (.run (.close 46)))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 18)))) (.step 58 (.step 46 (.run (.close 58))))) (.step 3 (.run (.close 54)))) (.step 3 (.step 40 (.run (.close 5))))) (.step 55 (.step 5 (.run (.close 27))))) (.step 55 (.step 70 (.step 3 (.step 48 (.run (.close 2))))))) (.step 55 (.step 72 (.step 31 (.run (.close 54)))))) (.step 55 (.step 65 (.split 54 0 (.split 17 0 (.split 67 0 (.step 5 (.step 2 (.run (.close 5)))) (.step 70 (.step 2 (.run (.close 4))))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 9))))))) (.step 55 (.step 5 (.step 3 (.run (.close 63)))))) (.step 3 (.run (.close 54)))) (.step 55 (.step 3 (.step 8 (.run (.close 5)))))) (.step 55 (.step 5 (.step 3 (.run (.close 63)))))) (.step 3 (.run (.close 46))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part845
namespace Part846
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725561291506214810041864041055510282816691858155683371906996471422571773952⟩
def references : Fin 2 → Box := ![Part844.root, Part845.root]
def proof : Enumeration.Proof 2 := (.split 7 0 (.split 13 0 (.split 31 0 (.reuse 0) (.split 6 0 (.split 12 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 54 0 (.split 56 0 (.split 72 0 (.split 73 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 4 0 (.step 36 (.run (.close 2))) (.step 2 (.run (.close 11)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 54 (.step 2 (.run (.close 40)))))) (.step 3 (.step 43 (.run (.close 23))))) (.step 68 (.step 3 (.run (.close 43))))) (.step 68 (.run (.close 54)))) (.step 3 (.run (.close 54)))) (.step 68 (.step 3 (.run (.close 18))))) (.step 55 (.step 3 (.run (.close 18))))) (.step 2 (.step 71 (.run (.close 7))))) (.step 2 (.step 68 (.step 58 (.run (.close 40)))))) (.step 3 (.step 4 (.step 43 (.run (.close 24)))))) (.step 3 (.run (.close 46))))) (.reuse 1)) (.split 31 0 (.split 8 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 33 0 (.split 4 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 34 0 (.step 46 (.run (.close 58))) (.step 7 (.run (.close 46)))) (.step 18 (.run (.close 46)))) (.step 18 (.step 4 (.run (.close 9))))) (.step 2 (.step 71 (.run (.close 76))))) (.step 2 (.step 28 (.run (.close 9))))) (.step 3 (.run (.close 46)))) (.step 2 (.step 55 (.run (.close 5))))) (.step 7 (.run (.close 46)))) (.step 72 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 46)))) (.step 2 (.step 55 (.run (.close 46))))) (.step 2 (.step 55 (.run (.close 46))))) (.step 2 (.step 55 (.run (.close 46))))) (.step 2 (.step 55 (.run (.close 46))))) (.step 3 (.run (.close 46)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part844.covered
  · exact Part845.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part846
namespace Part847
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725563016942801507682810899744475852073054970932926414503635262053627723776⟩
def references : Fin 1 → Box := ![Part846.root]
def proof : Enumeration.Proof 1 := (.split 23 0 (.reuse 0) (.split 31 0 (.split 33 0 (.split 41 0 (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 24 0 (.split 27 0 (.split 53 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 38 0 (.split 56 0 (.split 74 0 (.split 32 0 (.split 39 0 (.split 4 0 (.split 10 0 (.step 62 (.step 3 (.step 57 (.run (.close 29))))) (.step 18 (.step 54 (.step 18 (.run (.close 9)))))) (.step 9 (.run (.close 18)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31)))) (.step 68 (.run (.close 62)))) (.step 18 (.run (.close 57)))) (.step 68 (.step 18 (.step 4 (.run (.close 9)))))) (.step 3 (.step 28 (.run (.close 9))))) (.step 68 (.step 54 (.step 70 (.step 4 (.run (.close 2))))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 54 (.step 70 (.step 18 (.run (.close 2))))))) (.step 68 (.run (.close 54)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 68 (.step 3 (.run (.close 11))))) (.step 68 (.step 3 (.step 48 (.run (.close 2)))))) (.step 68 (.step 3 (.run (.close 11))))) (.step 3 (.run (.close 46)))) (.step 3 (.run (.close 70)))) (.step 3 (.run (.close 54)))) (.step 3 (.step 43 (.run (.close 23))))))
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
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033664080626545386916475211363595244506787508919364483022848, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725563016942801509253618829132011931890360673761993327712842862291819954176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 8 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 31 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 33 0 (.split 41 0 (.split 4 0 (.step 22 (.split 10 0 (.split 6 0 (.split 30 0 (.step 9 (.run (.close 18))) (.step 18 (.run (.close 76)))) (.step 53 (.run (.close 9)))) (.step 18 (.run (.close 9))))) (.step 9 (.run (.close 7)))) (.step 3 (.run (.close 40)))) (.step 9 (.step 3 (.run (.close 2))))) (.step 68 (.step 18 (.step 3 (.run (.close 9)))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 54 (.step 18 (.run (.close 4)))))) (.split 4 0 (.split 6 0 (.split 7 0 (.split 10 0 (.split 12 0 (.split 13 0 (.step 3 (.run (.close 18))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 24 (.step 18 (.run (.close 3))))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 24 (.step 18 (.run (.close 3)))))) (.step 68 (.step 3 (.run (.close 24))))) (.step 3 (.run (.close 54)))) (.step 3 (.step 43 (.run (.close 31))))) (.step 3 (.run (.close 7)))) (.step 55 (.step 3 (.step 5 (.run (.close 27)))))) (.step 3 (.step 40 (.run (.close 23))))) (.step 68 (.step 3 (.run (.close 31))))) (.step 3 (.step 40 (.run (.close 31))))) (.step 3 (.run (.close 7)))) (.step 68 (.step 3 (.step 31 (.run (.close 2)))))) (.step 55 (.step 3 (.step 61 (.run (.close 27)))))) (.step 68 (.step 3 (.step 65 (.step 31 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part848
namespace Part849
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234131009374243490885467899096048133081610657663529557266341745358970329907583913422212290749201641051958830325336093401223676609458274894421337725563016942801509253618829132011931890360673761993327712842862291819954176⟩
def references : Fin 2 → Box := ![Part847.root, Part848.root]
def proof : Enumeration.Proof 2 := (.split 18 0 (.split 19 0 (.reuse 0) (.split 5 0 (.split 11 0 (.split 27 0 (.split 32 0 (.split 53 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 24 0 (.split 39 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 58 0 (.split 31 0 (.split 4 0 (.step 22 (.split 10 0 (.step 9 (.run (.close 18))) (.step 18 (.run (.close 76))))) (.step 9 (.step 18 (.run (.close 16))))) (.split 4 0 (.step 22 (.run (.close 3))) (.step 2 (.run (.close 54))))) (.step 3 (.run (.close 40)))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 68 (.run (.close 54)))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 7)))) (.step 68 (.step 3 (.run (.close 11))))) (.step 55 (.step 3 (.run (.close 27))))) (.step 3 (.run (.close 54)))) (.step 68 (.step 3 (.run (.close 31))))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 54)))) (.step 68 (.step 72 (.step 3 (.run (.close 31))))))) (.reuse 1))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part847.covered
  · exact Part848.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part849
namespace Part850
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408358868601293358647081135134801706733150555675715924722113246016366908340967713525836247308693672736603691959968287431430550216245248, 5648027922681707751811830335810757426795628227479746358412878146988784635312452310217808282362604173771258885047729991194497614913119034143411025963764164000978979882493865666759687019965201898246184472029370424489934848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 54 0 (.split 58 0 (.split 4 0 (.split 10 0 (.split 19 0 (.split 7 0 (.split 6 0 (.split 13 0 (.split 27 0 (.step 54 (.split 67 0 (.step 4 (.step 2 (.run (.close 4)))) (.step 73 (.step 54 (.step 53 (.run (.close 4))))))) (.step 65 (.run (.close 30)))) (.step 65 (.step 4 (.run (.close 2))))) (.step 3 (.step 4 (.run (.close 9))))) (.step 65 (.step 3 (.run (.close 10))))) (.step 72 (.step 3 (.run (.close 9))))) (.step 64 (.step 54 (.step 46 (.step 65 (.run (.close 4))))))) (.step 46 (.step 10 (.run (.close 2))))) (.step 72 (.step 53 (.step 4 (.step 3 (.run (.close 2))))))) (.step 72 (.step 53 (.step 4 (.run (.close 57)))))) (.step 70 (.step 54 (.step 46 (.step 10 (.run (.close 4))))))) (.step 65 (.step 4 (.run (.close 10))))) (.step 72 (.step 54 (.run (.close 10))))) (.step 64 (.split 6 0 (.split 38 0 (.step 54 (.step 46 (.step 10 (.run (.close 4))))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 46)))))) (.step 65 (.step 10 (.run (.close 46))))) (.step 70 (.step 54 (.step 46 (.split 12 0 (.step 30 (.run (.close 5))) (.step 4 (.run (.close 63)))))))) (.step 72 (.step 54 (.run (.close 10))))) (.step 65 (.step 54 (.step 42 (.step 4 (.step 48 (.run (.close 23)))))))) (.step 65 (.step 64 (.split 69 0 (.split 17 0 (.split 36 0 (.step 30 (.step 4 (.run (.close 68)))) (.step 68 (.run (.close 55)))) (.step 63 (.run (.close 30)))) (.step 72 (.step 30 (.run (.close 4)))))))) (.step 46 (.step 55 (.run (.close 30)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part850
namespace Part851
def root : Box := ⟨4351082437154956072465106588077826347036009306069120408358868601293358647081135134801706733150555675715924722113246016366908340967713525836247308693672736603691959968287431430550216245248, 5789234131009374243490885467899096052484164047812619602022372929823181965413934404333267727140595581778757921210426908612620442233367766474435808489056899334661979443304596534374798204149669352721911543488172457447967948800⟩
def references : Fin 1 → Box := ![Part850.root]
def proof : Enumeration.Proof 1 := (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.reuse 0) (.step 70 (.split 25 0 (.split 34 0 (.split 38 0 (.split 42 0 (.split 56 0 (.step 53 (.split 16 0 (.step 54 (.split 17 0 (.step 2 (.run (.close 4))) (.step 63 (.run (.close 2))))) (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 71)))) (.step 68 (.step 71 (.run (.close 58))))) (.step 2 (.run (.close 71)))))) (.step 70 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.step 53 (.split 34 0 (.split 36 0 (.split 27 0 (.step 57 (.step 5 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 4 (.run (.close 55)))) (.step 71 (.step 4 (.run (.close 63))))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 65)))) (.step 4 (.run (.close 55)))) (.step 4 (.run (.close 55)))))) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 42 0 (.split 25 0 (.step 53 (.step 18 (.run (.close 10)))) (.step 71 (.run (.close 10)))) (.step 71 (.run (.close 10)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 48))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 46))))) (.split 11 0 (.split 17 0 (.split 35 0 (.step 46 (.step 68 (.run (.close 10)))) (.step 4 (.step 71 (.run (.close 76))))) (.step 68 (.run (.close 46)))) (.step 2 (.step 4 (.run (.close 71))))))
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
def root : Box := ⟨4249103942534136789516705652423100970619230591091148894617774261255913179920380224400814611919201801734449597804652057311935668363769788919797187446985715383644847770573325994553245696, 5648027922681707751811830335810757431044732170013883147929583799408533653949197252034063667958157279374487363934547933107797633034953319494525661853736172123751614583715523582035846850097900713796834638712516176743759872⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 54 0 (.split 58 0 (.split 4 0 (.split 10 0 (.split 19 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 32 0 (.step 54 (.split 67 0 (.split 6 0 (.split 12 0 (.step 3 (.run (.close 2))) (.step 4 (.run (.close 76)))) (.step 4 (.run (.close 62)))) (.step 54 (.step 70 (.step 4 (.run (.close 52))))))) (.step 64 (.step 30 (.run (.close 4))))) (.step 64 (.step 10 (.run (.close 2))))) (.step 52 (.step 3 (.run (.close 2))))) (.step 64 (.step 10 (.run (.close 2))))) (.step 72 (.step 3 (.run (.close 10))))) (.step 64 (.run (.close 52)))) (.step 46 (.step 10 (.run (.close 30))))) (.step 54 (.run (.close 2)))) (.step 54 (.run (.close 2)))) (.step 70 (.step 54 (.step 46 (.step 10 (.run (.close 4))))))) (.step 65 (.step 64 (.step 10 (.run (.close 2)))))) (.step 72 (.step 54 (.run (.close 10))))) (.step 64 (.step 9 (.step 54 (.run (.close 15)))))) (.step 64 (.step 10 (.run (.close 46))))) (.step 70 (.step 54 (.step 46 (.split 10 0 (.step 30 (.run (.close 5))) (.step 63 (.run (.close 64)))))))) (.step 72 (.step 54 (.step 55 (.run (.close 2)))))) (.step 65 (.step 54 (.split 12 0 (.split 18 0 (.split 4 0 (.split 10 0 (.split 17 0 (.step 54 (.step 46 (.split 67 0 (.step 55 (.step 31 (.run (.close 30)))) (.step 73 (.step 55 (.run (.close 30))))))) (.step 63 (.run (.close 54)))) (.step 63 (.step 64 (.run (.close 4))))) (.step 7 (.run (.close 30)))) (.step 68 (.step 30 (.step 5 (.run (.close 24)))))) (.step 64 (.step 4 (.run (.close 63)))))))) (.step 64 (.step 54 (.step 68 (.run (.close 27)))))) (.step 64 (.step 46 (.step 55 (.run (.close 30))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part852
namespace Part853
def root : Box := ⟨4249103942534136789516705652423100970619230591091148894617774261255913179920380224400814611919201801734449597804652057311935668363769788919797187446985715383644847770573325994553245696, 5789234131009374243490885467899096052488413151755153738811889635475601714432571149275083982526191134884361149689313726554533742251489600759786921272273443545725625300870058053283548711660047401288437562333511476590147534848⟩
def references : Fin 1 → Box := ![Part852.root]
def proof : Enumeration.Proof 1 := (.split 35 0 (.split 72 0 (.split 74 0 (.reuse 0) (.step 70 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.step 52 (.split 16 0 (.split 17 0 (.split 6 0 (.split 12 0 (.step 30 (.run (.close 5))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 71)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 64)))) (.step 2 (.run (.close 46)))))) (.step 70 (.split 5 0 (.split 11 0 (.split 16 0 (.split 22 0 (.split 53 0 (.step 52 (.split 34 0 (.split 36 0 (.step 54 (.step 10 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 68 (.step 63 (.run (.close 58))))) (.step 68 (.run (.close 64)))) (.step 68 (.run (.close 46)))))) (.split 74 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 25 0 (.step 52 (.step 54 (.step 46 (.step 10 (.run (.close 4)))))) (.step 71 (.run (.close 10)))) (.step 4 (.step 71 (.run (.close 76))))) (.step 71 (.step 4 (.run (.close 18))))) (.step 71 (.run (.close 22)))) (.step 71 (.run (.close 64)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 53))))) (.step 68 (.step 63 (.run (.close 2))))) (.step 68 (.run (.close 46)))) (.step 4 (.step 71 (.run (.close 68))))))
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
def root : Box := ⟨4249103942534136789516705652423100970619230591091148894617774261255913179920380224400814611919201801734449597804652057311935668363769788919797187446985715383644847770573325994553245696, 5789234131009374243490885467899096052488413151755153738811889635475601714432571149275083982526191134884361149689313726554533742251489600759786923124946871342784752078005818192290075757776376959701409748563067258351990603776⟩
def references : Fin 1 → Box := ![Part853.root]
def proof : Enumeration.Proof 1 := (.split 8 0 (.split 14 0 (.split 26 0 (.reuse 0) (.split 74 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.step 46 (.run (.close 10))) (.step 4 (.step 71 (.run (.close 53))))) (.step 68 (.run (.close 30)))) (.step 68 (.run (.close 46)))) (.step 68 (.run (.close 46)))) (.step 2 (.step 4 (.run (.close 46))))) (.step 4 (.run (.close 46))))) (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 5 0 (.step 52 (.run (.close 30))) (.step 2 (.run (.close 46)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 63 (.run (.close 36)))) (.step 63 (.step 4 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 52))))) (.step 2 (.run (.close 46))))) (.split 35 0 (.split 72 0 (.split 14 0 (.step 46 (.split 34 0 (.step 30 (.step 68 (.run (.close 5)))) (.step 71 (.run (.close 46))))) (.step 2 (.run (.close 52)))) (.step 4 (.run (.close 46)))) (.step 4 (.run (.close 46)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part853.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part854
namespace Part855
def root : Box := ⟨3864537523017258348047303873417636619192436351927590651341936285013801629804154221903710149916884492642512805194535839725496083182070604508759476767664684638877223114244096, 5789234131009374243490885467899096052488413151755157603349412652733946409784462081262428281453520841319359806924565178073676031811914136953553505047524833806400783580182995557368736800764032702610083215643815955332805427200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 35 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 5 0 (.split 11 0 (.split 25 0 (.split 38 0 (.split 53 0 (.split 56 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 31 0 (.split 33 0 (.step 46 (.step 54 (.step 10 (.step 2 (.run (.close 71)))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 68 (.run (.close 10)))) (.step 68 (.run (.close 10)))) (.step 68 (.step 58 (.run (.close 10))))) (.step 68 (.step 58 (.run (.close 55))))) (.step 2 (.run (.close 54)))) (.step 68 (.step 58 (.run (.close 55))))) (.step 68 (.step 58 (.run (.close 55))))) (.step 2 (.step 58 (.run (.close 55))))) (.step 2 (.step 58 (.run (.close 55))))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.step 18 (.run (.close 3))))) (.step 3 (.run (.close 71)))) (.step 2 (.step 18 (.run (.close 10))))) (.step 68 (.run (.close 10)))) (.step 68 (.run (.close 10)))) (.step 2 (.step 68 (.run (.close 48))))) (.step 68 (.step 55 (.run (.close 71))))) (.step 68 (.step 55 (.run (.close 48))))) (.step 55 (.step 68 (.step 55 (.step 48 (.run (.close 73))))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 2 (.step 68 (.run (.close 48)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part855
namespace Part856
def root : Box := ⟨5386379163185534471414773640069251753523547958090930032126242996694364211649485655353416754303903258757464122391214009531929266140571550117757562374336689024016697170240048296165116704641640660089694470019739549696, 5789234136395753406676419939313869692557664905278705561440342684860186054526843807262639043297915374467610380980995738182402526750046035577741720203367716131548309570537144596604264069312296390683629678129620245110245556224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 25 0 (.split 38 0 (.split 56 0 (.split 57 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 7 0 (.split 8 0 (.split 13 0 (.split 14 0 (.split 18 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 19 0 (.split 23 0 (.split 31 0 (.step 54 (.step 46 (.step 54 (.split 4 0 (.step 57 (.run (.close 61))) (.step 2 (.run (.close 71))))))) (.step 2 (.run (.close 61)))) (.step 18 (.run (.close 3)))) (.step 18 (.run (.close 3)))) (.step 2 (.run (.close 61)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 2 (.run (.close 57)))) (.step 55 (.step 18 (.run (.close 3))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 3 (.run (.close 71)))) (.step 2 (.step 4 (.run (.close 61))))) (.step 2 (.run (.close 22)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 72)))) (.step 68 (.step 55 (.step 71 (.run (.close 57)))))) (.step 2 (.run (.close 18)))) (.step 71 (.step 68 (.run (.close 72))))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 68 (.step 71 (.run (.close 55))))) (.step 68 (.step 63 (.step 68 (.run (.close 72)))))) (.step 68 (.step 63 (.step 68 (.step 55 (.step 63 (.run (.close 61)))))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 2 (.step 68 (.run (.close 48)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part856
namespace Part857
def root : Box := ⟨4784065733063810973581885157618788676291241978568617960252656648542259379952161751917525065602206520408883435770957712575174633921970160437489445144120044985688140420678557274495703779189417100443648, 5789234136395753406676424723379602756368638487163863180229018976102161271192821574270012692048273105473709613805027778106435421039684439019070960416086958052519584026319740585644728729835864052672809976229509254285046579200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 0 (.split 25 0 (.split 34 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 36 0 (.split 38 0 (.split 56 0 (.split 57 0 (.split 71 0 (.step 70 (.split 35 0 (.split 72 0 (.split 74 0 (.step 70 (.split 4 0 (.split 10 0 (.step 3 (.step 54 (.step 70 (.run (.close 3))))) (.step 18 (.step 3 (.run (.close 71))))) (.step 2 (.step 18 (.run (.close 71)))))) (.step 2 (.run (.close 9)))) (.step 68 (.run (.close 10)))) (.step 68 (.run (.close 10))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 68 (.run (.close 10)))) (.step 68 (.run (.close 10)))) (.step 68 (.step 71 (.run (.close 55))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 63))))) (.step 2 (.step 68 (.run (.close 63))))) (.step 68 (.step 55 (.step 28 (.step 68 (.step 71 (.run (.close 7)))))))) (.step 2 (.step 68 (.run (.close 46))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 55 (.step 68 (.run (.close 71))))) (.step 68 (.step 55 (.run (.close 31))))) (.step 68 (.step 55 (.step 68 (.step 63 (.run (.close 7))))))) (.step 2 (.step 68 (.step 55 (.run (.close 71)))))) (.step 2 (.step 68 (.run (.close 46)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part857
namespace Part858
def root : Box := ⟨3351951982488697857462176983384614243729420922532740102888290058257027278803346066768740366526432398976903945899113385340439816749368939803929547265540096, 5789234136395753406676424723379602756368638487163863180229018976102161271192821577318595260716234268932300658524916748564050794735945328529966428800239046743696947425056169358586106815604351475921465147565423003590012698624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 5 0 (.split 74 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 6 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 38 0 (.split 25 0 (.split 53 0 (.split 56 0 (.split 62 0 (.split 30 0 (.step 3 (.step 2 (.run (.close 48)))) (.step 31 (.run (.close 65)))) (.step 65 (.run (.close 2)))) (.step 68 (.run (.close 10)))) (.step 2 (.run (.close 30)))) (.step 68 (.step 58 (.run (.close 55))))) (.step 68 (.run (.close 65)))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.step 3 (.run (.close 71))))) (.step 2 (.step 18 (.run (.close 10))))) (.step 71 (.step 68 (.run (.close 10))))) (.step 68 (.step 58 (.run (.close 55))))) (.step 68 (.step 58 (.run (.close 55))))) (.step 71 (.step 68 (.run (.close 10))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 2 (.step 68 (.run (.close 46))))) (.step 68 (.step 58 (.step 55 (.run (.close 28)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 55 (.step 68 (.step 55 (.run (.close 71)))))) (.step 55 (.step 68 (.step 55 (.run (.close 48)))))) (.step 68 (.step 55 (.step 48 (.run (.close 8)))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 2 (.step 68 (.run (.close 48)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part858
namespace Part859
def root : Box := ⟨3351951982485652252024923737026979342715018142828855200029607172622291296318817758578573301640927606626674728096592153736305067360462419647908513105051648, 5789234136395753406676424723379602756368638487163863180229018976102161271192821577321572392130949074755990688842026015136763309749320583304879412656082945267809425319000247902309682380141234764420731412381180731860818329600⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 6 0 (.split 74 0 (.split 42 0 (.split 72 0 (.split 66 0 (.split 71 0 (.split 57 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 24 0 (.split 33 0 (.split 39 0 (.step 64 (.step 3 (.step 55 (.step 2 (.run (.close 48)))))) (.step 2 (.step 71 (.run (.close 4))))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 46)))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.step 18 (.run (.close 3))))) (.step 68 (.step 18 (.run (.close 3))))) (.step 3 (.run (.close 71)))) (.step 2 (.step 68 (.step 58 (.run (.close 55)))))) (.step 2 (.run (.close 18)))) (.step 2 (.step 68 (.run (.close 48))))) (.step 58 (.step 68 (.run (.close 10))))) (.step 68 (.step 58 (.run (.close 55))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 2 (.step 18 (.run (.close 10))))) (.step 68 (.step 58 (.step 55 (.run (.close 2)))))) (.step 58 (.step 71 (.step 68 (.run (.close 10)))))) (.step 68 (.step 55 (.step 58 (.run (.close 28)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 55 (.step 68 (.step 55 (.run (.close 71)))))) (.step 68 (.step 55 (.step 48 (.run (.close 8)))))) (.step 68 (.step 55 (.step 48 (.run (.close 8)))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 2 (.step 68 (.run (.close 48)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part859
namespace Part860
def root : Box := ⟨4562440617622195218641171605700291324896580459231045579854086026921496322861362087539475093804885993576009825956929369225368753910538471660800792324243241805105011242454462553973054434546024448, 5789234136395753406676424723384165196986260682382504351834719267427054499700070137252151584648848349923199366228531927948080681149099225614453007063393633972530800756998500563629404594329486759095091677331263606053064933376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 46 0 (.split 47 0 (.split 56 0 (.split 57 0 (.split 8 0 (.split 66 0 (.split 71 0 (.split 7 0 (.split 13 0 (.split 14 0 (.split 18 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 19 0 (.split 23 0 (.split 50 0 (.split 30 0 (.step 3 (.step 2 (.run (.close 48)))) (.step 31 (.run (.close 53)))) (.step 65 (.run (.close 2)))) (.step 18 (.run (.close 3)))) (.step 18 (.run (.close 3)))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 55 (.step 18 (.run (.close 3))))) (.step 2 (.step 71 (.run (.close 68))))) (.step 3 (.run (.close 71)))) (.step 2 (.step 18 (.run (.close 9))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 4 (.step 71 (.run (.close 68)))))) (.step 2 (.run (.close 18)))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 68 (.step 71 (.step 68 (.step 71 (.run (.close 2))))))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 68 (.step 63 (.step 68 (.step 71 (.run (.close 55))))))) (.step 68 (.step 55 (.step 63 (.run (.close 11)))))) (.step 68 (.step 55 (.step 63 (.step 11 (.run (.close 2))))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 2 (.step 68 (.run (.close 48)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part860
namespace Part861
def root : Box := ⟨4455508415646675018204269146191690750317995446595571082099751715482166558161925043821962967316714304963846763777925203069393627367501863718299619091068841646231406643377550130495549127786496, 5789234136395753406676424723384169652494676329057522556103865459117801465743534247173958790891541610934104843452542187628560483269606821944833450026682023316969005225199670732243974635554279973933640857277502795459986456576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 66 0 (.split 8 0 (.split 14 0 (.split 64 0 (.split 71 0 (.split 7 0 (.split 13 0 (.split 18 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 74 0 (.split 19 0 (.split 23 0 (.split 31 0 (.step 54 (.step 46 (.step 54 (.step 64 (.step 31 (.run (.close 2))))))) (.step 2 (.run (.close 64)))) (.step 18 (.run (.close 3)))) (.step 18 (.run (.close 3)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 68 (.run (.close 63)))) (.step 68 (.run (.close 63)))) (.step 2 (.step 71 (.run (.close 68))))) (.step 55 (.step 18 (.run (.close 3))))) (.step 3 (.run (.close 71)))) (.step 2 (.step 18 (.run (.close 9))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 4 (.step 71 (.run (.close 68)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 71 (.step 68 (.step 71 (.run (.close 2)))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 68 (.step 55 (.step 71 (.run (.close 29)))))) (.step 71 (.step 68 (.step 58 (.run (.close 55)))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 68 (.step 55 (.step 71 (.step 29 (.run (.close 2))))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 68 (.step 63 (.step 55 (.step 68 (.run (.close 71))))))) (.step 68 (.step 55 (.step 63 (.run (.close 11)))))) (.step 68 (.step 55 (.step 63 (.step 11 (.run (.close 2))))))) (.step 2 (.step 68 (.run (.close 48)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part861
namespace Part862
def root : Box := ⟨3351951985607397825209501253602752882477867339310880630179564948226673342960333653499814809283339765611622975680854547974423190989645579569468527605710848, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509106883772992531334636618847936226703148240757681101793075398420843082589125531302734224215134462485401380556536305253183209645199589376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 56 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.step 54 (.step 3 (.run (.close 68)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 68 (.run (.close 10)))) (.step 55 (.step 3 (.step 71 (.run (.close 68)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 68 (.step 55 (.step 18 (.run (.close 2)))))) (.step 68 (.step 3 (.step 58 (.run (.close 55)))))) (.step 68 (.step 55 (.step 18 (.run (.close 3)))))) (.step 68 (.step 55 (.split 4 0 (.step 18 (.run (.close 3))) (.step 68 (.run (.close 7))))))) (.step 2 (.step 68 (.run (.close 46))))) (.step 68 (.step 55 (.step 31 (.run (.close 2)))))) (.step 68 (.step 55 (.step 31 (.run (.close 2)))))) (.step 68 (.step 55 (.split 46 0 (.step 11 (.run (.close 54))) (.step 2 (.run (.close 55))))))) (.step 2 (.step 68 (.run (.close 54))))) (.step 2 (.step 68 (.run (.close 46)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part862
namespace Part863
def root : Box := ⟨3351951982485649274896348235987935367100909329686845005226912708932701219507936485770598561382226623186123938312878255780988296694222081147733111837032448, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669246286629248372991933631961344724263370719109748048948836895433968161833437356659891503104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 22 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 53 0 (.split 56 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 71 0 (.step 46 (.run (.close 3))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 46)))) (.step 2 (.run (.close 46)))) (.step 55 (.run (.close 9)))) (.step 55 (.split 46 0 (.step 71 (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 71)))))) (.step 2 (.step 68 (.run (.close 71))))) (.step 2 (.step 68 (.run (.close 63))))) (.step 2 (.step 68 (.run (.close 63))))) (.step 2 (.step 68 (.run (.close 63))))) (.step 3 (.step 68 (.run (.close 10))))) (.step 2 (.step 68 (.run (.close 48))))) (.step 68 (.step 55 (.split 35 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 68))))))) (.step 3 (.split 46 0 (.split 47 0 (.step 68 (.run (.close 10))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 68)))))) (.step 68 (.step 55 (.split 4 0 (.split 10 0 (.split 30 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 2)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 18))))))) (.step 68 (.step 55 (.split 4 0 (.split 10 0 (.split 30 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 71 (.run (.close 68)))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 18)))) (.step 68 (.run (.close 7))))))) (.step 2 (.step 68 (.run (.close 46))))) (.step 68 (.step 55 (.split 49 0 (.step 2 (.run (.close 71))) (.step 68 (.run (.close 71)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part863
namespace Part864
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669246286629248372991933631961344724263372217148926313124329352285136329730440762514737201152⟩
def references : Fin 12 → Box := ![Part849.root, Part851.root, Part854.root, Part855.root, Part856.root, Part857.root, Part858.root, Part859.root, Part860.root, Part861.root, Part862.root, Part863.root]
def proof : Enumeration.Proof 12 := (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 46 0 (.split 47 0 (.split 66 0 (.split 71 0 (.split 57 0 (.split 61 0 (.split 62 0 (.reuse 0) (.split 8 0 (.split 14 0 (.reuse 1) (.split 72 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 56 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 74 0 (.split 5 0 (.step 53 (.step 54 (.step 46 (.step 30 (.run (.close 5)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 63)))) (.step 63 (.run (.close 30)))) (.step 63 (.run (.close 30)))) (.step 63 (.run (.close 65)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 71 (.run (.close 2))))) (.step 68 (.run (.close 65)))) (.step 68 (.run (.close 54)))) (.step 68 (.step 55 (.run (.close 58))))) (.step 2 (.run (.close 46)))) (.step 4 (.step 71 (.run (.close 68)))))) (.split 35 0 (.split 72 0 (.split 14 0 (.step 46 (.split 34 0 (.step 30 (.step 71 (.run (.close 5)))) (.step 71 (.run (.close 46))))) (.step 2 (.run (.close 46)))) (.step 4 (.run (.close 46)))) (.step 4 (.run (.close 53)))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)) (.reuse 7)) (.reuse 8)) (.split 5 0 (.reuse 9) (.step 2 (.step 68 (.run (.close 48)))))) (.reuse 10)) (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.reuse 11) (.step 68 (.step 55 (.split 4 0 (.split 8 0 (.split 14 0 (.split 49 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 71)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48)))) (.step 2 (.run (.close 48))))))) (.step 68 (.step 55 (.split 4 0 (.split 10 0 (.split 30 0 (.split 49 0 (.step 2 (.run (.close 71))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 71)))) (.step 68 (.run (.close 31)))) (.step 2 (.run (.close 7))))))) (.step 2 (.step 68 (.run (.close 46))))) (.step 2 (.step 68 (.run (.close 46))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part849.covered
  · exact Part851.covered
  · exact Part854.covered
  · exact Part855.covered
  · exact Part856.covered
  · exact Part857.covered
  · exact Part858.covered
  · exact Part859.covered
  · exact Part860.covered
  · exact Part861.covered
  · exact Part862.covered
  · exact Part863.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part864
namespace Part865
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797369505676280601061248670718155620945908532829124217007722778424001770241878230375801552896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049050364518671221067291666170694485213454505471640656280026291815726339424022948344329588579411625426455304810056908800⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 39 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 70 0 (.split 72 0 (.split 73 0 (.split 74 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 32 (.run (.close 2))) (.step 18 (.step 68 (.run (.close 3))))) (.step 18 (.step 68 (.run (.close 3))))) (.step 18 (.step 68 (.run (.close 3))))) (.step 18 (.step 68 (.run (.close 3))))) (.step 68 (.step 18 (.step 68 (.run (.close 3)))))) (.step 68 (.step 18 (.step 68 (.run (.close 3)))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 33 (.step 68 (.step 54 (.run (.close 18))))) (.step 2 (.run (.close 46)))) (.step 2 (.step 18 (.run (.close 68))))) (.step 2 (.run (.close 54)))) (.step 2 (.step 18 (.run (.close 68))))) (.step 18 (.step 3 (.step 18 (.run (.close 68)))))) (.step 18 (.run (.close 54)))) (.step 65 (.step 53 (.step 22 (.step 68 (.run (.close 2)))))))) (.step 2 (.step 54 (.step 33 (.step 18 (.step 70 (.run (.close 18)))))))) (.step 2 (.step 68 (.step 3 (.run (.close 31)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 65 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 68))))) (.step 3 (.step 18 (.run (.close 68))))))) (.step 55 (.step 18 (.step 9 (.step 68 (.run (.close 18))))))) (.step 2 (.step 3 (.step 18 (.step 68 (.run (.close 31))))))) (.step 2 (.run (.close 54)))) (.step 68 (.step 18 (.step 3 (.step 10 (.step 68 (.run (.close 18)))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.run (.close 54)))) (.step 3 (.run (.close 54)))))) (.step 2 (.run (.close 54)))) (.step 2 (.step 3 (.run (.close 33)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part865
namespace Part866
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016568094197603890180242299420672, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114141043902368428812648239333376⟩
def references : Fin 2 → Box := ![Part864.root, Part865.root]
def proof : Enumeration.Proof 2 := (.split 29 0 (.reuse 0) (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.reuse 1) (.step 68 (.step 18 (.step 3 (.step 10 (.step 68 (.run (.close 18)))))))) (.step 55 (.step 18 (.step 3 (.step 9 (.step 68 (.run (.close 18)))))))) (.step 2 (.step 3 (.run (.close 33))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 68 (.step 18 (.run (.close 9)))))) (.step 2 (.step 68 (.step 18 (.run (.close 10)))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 68 (.step 3 (.run (.close 31)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 65 (.step 10 (.run (.close 2))))) (.step 3 (.step 65 (.run (.close 18))))) (.step 3 (.step 65 (.run (.close 10))))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 53 (.step 9 (.run (.close 2))))) (.step 3 (.step 53 (.run (.close 18))))) (.step 3 (.step 53 (.run (.close 9))))))) (.step 2 (.step 68 (.step 3 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 46))))) (.step 2 (.step 3 (.step 65 (.step 18 (.run (.close 58))))))) (.step 2 (.step 3 (.step 53 (.step 18 (.run (.close 71))))))) (.step 2 (.step 68 (.run (.close 46))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part864.covered
  · exact Part865.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part866
namespace Part867
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103861856471989429199558946420969751807826336311401013429443251759974325234541638204033775482858911736342825515933636364076349245245896824245664092014681883711583027200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 56 0 (.split 58 0 (.split 70 0 (.split 72 0 (.split 73 0 (.split 74 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 3))) (.step 18 (.step 68 (.run (.close 3))))) (.step 18 (.step 68 (.run (.close 3))))) (.step 18 (.step 68 (.run (.close 3))))) (.step 18 (.step 3 (.run (.close 2))))) (.step 18 (.step 68 (.run (.close 3))))) (.step 22 (.split 22 0 (.step 10 (.step 2 (.run (.close 3)))) (.step 18 (.run (.close 3)))))) (.step 68 (.step 18 (.step 68 (.run (.close 3)))))) (.step 68 (.step 18 (.step 68 (.run (.close 3)))))) (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 41 0 (.split 44 0 (.step 13 (.run (.close 2))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 2 (.run (.close 13)))) (.step 18 (.step 3 (.run (.close 13))))) (.step 18 (.step 54 (.run (.close 2))))) (.split 16 0 (.step 18 (.run (.close 12))) (.step 24 (.run (.close 18)))))) (.step 2 (.step 54 (.step 13 (.step 18 (.step 70 (.run (.close 18)))))))) (.step 2 (.step 68 (.step 3 (.run (.close 31)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 64 (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 13)))) (.step 3 (.step 18 (.run (.close 68))))))) (.step 55 (.step 18 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 71))))))))) (.step 2 (.step 3 (.step 18 (.step 68 (.run (.close 31))))))) (.step 2 (.run (.close 54)))) (.step 68 (.step 18 (.step 3 (.step 10 (.split 44 0 (.step 64 (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 71)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part867
namespace Part868
def root : Box := ⟨3351951982485649274893509022221155652684701033562282487514593797367516383334961914680049189163033662548131004521027616853016569332137643175560517198544896, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502513868588072281082720337970487676108800⟩
def references : Fin 1 → Box := ![Part867.root]
def proof : Enumeration.Proof 1 := (.split 13 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 53 0 (.split 54 0 (.reuse 0) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.step 3 (.run (.close 2))) (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 27))))) (.step 3 (.run (.close 13)))) (.step 3 (.run (.close 54)))))) (.step 2 (.run (.close 54)))) (.step 2 (.step 3 (.step 18 (.step 68 (.run (.close 31))))))) (.step 68 (.step 18 (.step 3 (.step 10 (.split 44 0 (.step 64 (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 71))))))))) (.step 55 (.step 18 (.step 3 (.step 9 (.split 4 0 (.step 22 (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 71))))))))) (.step 2 (.step 3 (.step 18 (.step 68 (.run (.close 31))))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 68 (.step 18 (.run (.close 9)))))) (.step 2 (.step 68 (.step 18 (.run (.close 10)))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.step 68 (.step 3 (.run (.close 31)))))) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.step 64 (.split 16 0 (.step 10 (.run (.close 2))) (.step 68 (.run (.close 3)))))) (.step 3 (.step 64 (.run (.close 18))))) (.step 3 (.step 64 (.run (.close 13)))))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571830047899648, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 6 → Box := ![Part812.root, Part818.root, Part819.root, Part840.root, Part866.root, Part868.root]
def proof : Enumeration.Proof 6 := (.split 51 0 (.split 61 0 (.split 25 0 (.reuse 0) (.split 34 0 (.split 36 0 (.reuse 1) (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 70 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 49 0 (.split 50 0 (.split 6 0 (.step 28 (.step 29 (.run (.close 2)))) (.step 2 (.run (.close 28)))) (.step 58 (.step 48 (.run (.close 18))))) (.step 58 (.step 48 (.run (.close 18))))) (.step 2 (.step 58 (.run (.close 4))))) (.step 2 (.step 58 (.run (.close 4))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 43 (.run (.close 7)))) (.step 2 (.step 55 (.run (.close 28))))) (.step 2 (.step 55 (.run (.close 28))))) (.step 2 (.step 71 (.run (.close 43))))) (.step 2 (.step 43 (.run (.close 40))))) (.step 2 (.step 71 (.run (.close 43))))) (.step 2 (.step 43 (.run (.close 40))))) (.step 2 (.step 43 (.run (.close 40)))))) (.reuse 2))) (.reuse 3)) (.split 9 0 (.reuse 4) (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.reuse 5) (.step 3 (.split 4 0 (.split 10 0 (.step 22 (.split 16 0 (.split 18 0 (.step 52 (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.step 2 (.run (.close 71))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 3))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 3))))) (.step 3 (.step 52 (.run (.close 18))))) (.step 3 (.step 52 (.run (.close 13))))))) (.step 2 (.step 68 (.step 3 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 46))))) (.step 2 (.step 3 (.step 64 (.step 18 (.run (.close 58))))))) (.step 2 (.step 3 (.step 52 (.step 18 (.run (.close 71))))))) (.step 2 (.step 68 (.run (.close 46)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part812.covered
  · exact Part818.covered
  · exact Part819.covered
  · exact Part840.covered
  · exact Part866.covered
  · exact Part868.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part869
namespace Part870
def root : Box := ⟨1073741824, 5789234136395753406676424723384169652494676329057522556103865459117801465743537368922509109722986759311049052827144060789220860559669248275922194012138502253490337311546732618973529502515199114142281842407714192923138457600⟩
def references : Fin 18 → Box := ![Part416.root, Part480.root, Part490.root, Part491.root, Part492.root, Part493.root, Part494.root, Part495.root, Part501.root, Part507.root, Part526.root, Part567.root, Part658.root, Part672.root, Part673.root, Part682.root, Part710.root, Part869.root]
def proof : Enumeration.Proof 18 := (.split 43 0 (.split 51 0 (.split 25 0 (.split 34 0 (.reuse 0) (.split 36 0 (.split 5 0 (.split 11 0 (.split 38 0 (.reuse 1) (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.split 41 0 (.split 58 0 (.reuse 2) (.split 49 0 (.split 50 0 (.split 16 0 (.split 17 0 (.split 59 0 (.split 22 0 (.split 53 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 10 0 (.split 7 0 (.split 13 0 (.split 73 0 (.split 30 0 (.step 2 (.run (.close 31))) (.step 4 (.run (.close 2)))) (.step 63 (.step 4 (.run (.close 31))))) (.step 63 (.step 18 (.run (.close 31))))) (.step 2 (.run (.close 31)))) (.step 4 (.step 2 (.run (.close 3))))) (.step 71 (.run (.close 2)))) (.step 63 (.run (.close 18)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 43)))) (.step 58 (.step 48 (.run (.close 2))))) (.step 58 (.step 55 (.run (.close 43))))) (.step 4 (.step 58 (.step 48 (.run (.close 2)))))) (.step 4 (.step 58 (.step 48 (.step 2 (.run (.close 5))))))) (.step 58 (.step 43 (.run (.close 2))))) (.step 58 (.step 43 (.run (.close 2)))))) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)) (.reuse 7))) (.reuse 8)) (.reuse 9)) (.reuse 10))) (.reuse 11)) (.split 61 0 (.split 25 0 (.split 34 0 (.reuse 12) (.split 9 0 (.reuse 13) (.split 5 0 (.split 11 0 (.split 46 0 (.split 47 0 (.split 53 0 (.split 57 0 (.split 8 0 (.split 14 0 (.split 63 0 (.split 64 0 (.reuse 14) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 43 (.step 68 (.run (.close 31)))))) (.step 2 (.step 68 (.run (.close 43))))) (.step 2 (.step 68 (.run (.close 43))))))) (.reuse 15)) (.reuse 16))) (.reuse 17))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part416.covered
  · exact Part480.covered
  · exact Part490.covered
  · exact Part491.covered
  · exact Part492.covered
  · exact Part493.covered
  · exact Part494.covered
  · exact Part495.covered
  · exact Part501.covered
  · exact Part507.covered
  · exact Part526.covered
  · exact Part567.covered
  · exact Part658.covered
  · exact Part672.covered
  · exact Part673.covered
  · exact Part682.covered
  · exact Part710.covered
  · exact Part869.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part870
end FiveColour.Packed.EnumerationChunks.Case39
