module
public import FiveColour.EnumerationChunks.Case132.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case132
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part769
def root : Box := ⟨1393796574908163946345982392040524741607425, 11572820244868825110612595243234989860555963036094477429256650891953478352115558975733472184928657876277139003958900405450867617575065498126849446040467470734944444072776215767605123533326938940736603256758519429857313554434⟩
def references : Fin 1 → Box := ![Part768.root]
def proof : Enumeration.Proof 1 := (.split 36 0 (.split 42 0 (.split 35 0 (.reuse 0) (.step 3 (.step 18 (.step 47 (.step 51 (.step 69 (.split 63 0 (.split 64 0 (.split 71 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 2 (.run (.close 69))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 18)))) (.step 5 (.run (.close 18)))) (.step 40 (.step 74 (.step 29 (.step 11 (.step 18 (.step 2 (.run (.close 69))))))))) (.step 40 (.step 74 (.step 67 (.step 29 (.step 11 (.run (.close 32)))))))) (.step 40 (.step 74 (.step 67 (.step 29 (.step 11 (.step 66 (.step 77 (.run (.close 12)))))))))))))))) (.step 31 (.step 18 (.step 51 (.step 69 (.step 3 (.split 63 0 (.split 42 1 (.step 18 (.run (.close 2))) (.step 40 (.run (.close 3)))) (.step 40 (.step 74 (.step 66 (.step 11 (.run (.close 18))))))))))))) (.step 31 (.step 3 (.step 51 (.step 69 (.split 35 0 (.step 3 (.split 63 0 (.split 36 1 (.split 42 0 (.step 18 (.run (.close 2))) (.step 40 (.run (.close 3)))) (.step 40 (.run (.close 3)))) (.step 40 (.step 74 (.step 66 (.step 67 (.run (.close 18)))))))) (.step 40 (.step 74 (.step 29 (.run (.close 3)))))))))))
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
def root : Box := ⟨1684996666696914987166688442938726917102321526408785780071123124225, 11572820244868825110612595243234989860555963036094477429256650891953478352115558975733472184928657876277139003958900405450867617575065498126849446040467470738314437406170045741938497631611242958613353617611306908950076588034⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 2 (.run (.close 69))) (.step 18 (.step 2 (.run (.close 8))))) (.step 18 (.step 31 (.step 2 (.run (.close 8)))))) (.step 31 (.step 47 (.step 51 (.split 15 0 (.split 22 1 (.split 24 0 (.split 27 0 (.split 32 0 (.split 39 0 (.step 69 (.step 2 (.step 60 (.run (.close 2))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 2 (.run (.close 18)))))))) (.step 3 (.step 51 (.step 69 (.split 46 0 (.split 22 1 (.step 31 (.run (.close 2))) (.step 24 (.run (.close 3)))) (.step 43 (.step 60 (.step 49 (.run (.close 31)))))))))) (.step 31 (.step 18 (.run (.close 2))))) (.step 18 (.step 31 (.step 18 (.step 2 (.run (.close 11))))))) (.step 18 (.step 31 (.step 47 (.step 51 (.step 69 (.step 49 (.split 38 0 (.step 18 (.run (.close 2))) (.step 50 (.step 49 (.run (.close 18)))))))))))) (.step 3 (.step 18 (.step 31 (.step 47 (.step 51 (.step 69 (.split 63 0 (.step 2 (.run (.close 31))) (.step 40 (.step 74 (.run (.close 31)))))))))))) (.step 3 (.step 18 (.step 51 (.step 69 (.split 63 0 (.split 22 1 (.step 31 (.run (.close 2))) (.step 23 (.run (.close 3)))) (.step 40 (.step 74 (.step 66 (.step 67 (.run (.close 31)))))))))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part770
namespace Part771
def root : Box := ⟨2147483649, 11572820244868825110612595243234989860555963036094477429256650891953478352115558975733472184928657876277139003958900405450867617575065498126849446040467470738314437406170045741938500419204392774941246309576090989995264835586⟩
def references : Fin 4 → Box := ![Part765.root, Part766.root, Part769.root, Part770.root]
def proof : Enumeration.Proof 4 := (.split 22 0 (.split 14 0 (.split 74 0 (.reuse 0) (.split 36 0 (.split 42 0 (.split 35 0 (.reuse 1) (.step 3 (.step 18 (.step 47 (.step 51 (.step 69 (.split 45 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 24 0 (.split 31 0 (.split 33 0 (.split 39 0 (.step 75 (.split 63 0 (.step 32 (.step 40 (.step 29 (.step 2 (.run (.close 32)))))) (.step 74 (.step 40 (.step 66 (.step 67 (.step 29 (.step 2 (.run (.close 69)))))))))) (.step 42 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 40)))) (.step 27 (.run (.close 29)))) (.step 4 (.step 5 (.run (.close 18))))) (.step 4 (.step 5 (.run (.close 18))))) (.step 71 (.step 43 (.step 63 (.step 66 (.step 4 (.run (.close 18)))))))) (.step 2 (.run (.close 23)))))))))) (.step 31 (.step 3 (.step 18 (.step 47 (.step 51 (.step 69 (.step 3 (.split 63 0 (.step 2 (.run (.close 18))) (.step 40 (.step 74 (.run (.close 18))))))))))))) (.step 31 (.step 3 (.step 51 (.step 69 (.split 35 0 (.step 3 (.split 63 0 (.step 18 (.run (.close 2))) (.step 40 (.step 74 (.run (.close 18)))))) (.step 40 (.step 74 (.step 29 (.run (.close 3)))))))))))) (.reuse 2)) (.split 14 0 (.reuse 3) (.step 3 (.step 18 (.step 69 (.split 44 0 (.split 46 0 (.step 18 (.split 48 0 (.split 63 0 (.split 64 0 (.step 31 (.step 2 (.run (.close 69)))) (.step 3 (.run (.close 18)))) (.step 3 (.step 11 (.step 18 (.run (.close 74)))))) (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 18)))) (.step 3 (.step 8 (.step 11 (.run (.close 2)))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part765.covered
  · exact Part766.covered
  · exact Part769.covered
  · exact Part770.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
def root : Box := ⟨2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493273754599425, 11572820244868825110612595243234989860555963036094477429256650891953478352115558975733472184928652460906642674242373094279978154932607053295607908535801228086529023828656122367250414253069825152801169335132167447781186732034⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 22 0 (.split 46 0 (.split 47 0 (.split 57 0 (.split 38 0 (.split 56 0 (.split 35 0 (.split 72 0 (.split 14 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 2 (.run (.close 69))) (.step 18 (.step 2 (.run (.close 29))))) (.step 18 (.step 31 (.step 2 (.run (.close 29)))))) (.step 18 (.step 47 (.step 51 (.step 69 (.split 13 0 (.split 34 1 (.split 73 0 (.split 74 0 (.step 2 (.run (.close 74))) (.step 40 (.step 74 (.run (.close 18))))) (.step 2 (.run (.close 66)))) (.step 3 (.run (.close 31)))) (.step 2 (.run (.close 66))))))))) (.step 3 (.step 47 (.step 51 (.step 69 (.split 63 0 (.split 34 1 (.step 18 (.run (.close 2))) (.step 40 (.run (.close 3)))) (.step 40 (.step 66 (.run (.close 2)))))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 31 (.step 3 (.split 44 0 (.split 48 0 (.split 63 0 (.step 2 (.run (.close 31))) (.step 29 (.step 15 (.run (.close 66))))) (.step 31 (.run (.close 2)))) (.step 29 (.run (.close 2))))))) (.step 18 (.step 31 (.run (.close 2))))) (.step 3 (.step 18 (.split 35 0 (.step 31 (.run (.close 2))) (.step 29 (.run (.close 31))))))) (.step 31 (.step 18 (.step 31 (.run (.close 2)))))) (.step 31 (.step 51 (.step 69 (.split 38 0 (.step 31 (.step 18 (.step 31 (.run (.close 2))))) (.step 3 (.run (.close 31)))))))) (.step 31 (.step 47 (.step 51 (.step 69 (.split 14 0 (.split 38 0 (.split 56 0 (.step 31 (.step 18 (.step 31 (.step 2 (.run (.close 60)))))) (.step 3 (.run (.close 31)))) (.step 3 (.step 28 (.step 31 (.run (.close 60)))))) (.step 5 (.step 8 (.step 71 (.step 43 (.step 48 (.step 49 (.run (.close 18)))))))))))))) (.step 3 (.step 18 (.step 31 (.step 3 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part772
namespace Part773
def root : Box := ⟨1496577676626844588240573268701473812127677071491073, 11572820244868825110612595243234989860555963036094477429256650891953478352115558975733472184928657876277139003958900405455347107059421106547964330601604359291187735067245517830560452201350549347915569858503114590705187553282⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 2 (.run (.close 51))) (.step 18 (.step 2 (.run (.close 8))))) (.step 18 (.step 31 (.step 2 (.run (.close 8)))))) (.step 31 (.step 47 (.step 69 (.split 15 0 (.split 17 1 (.split 24 0 (.split 27 0 (.split 32 0 (.split 39 0 (.step 51 (.step 2 (.step 60 (.run (.close 31))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 2 (.run (.close 18)))))))) (.step 3 (.step 51 (.step 69 (.split 46 0 (.split 17 1 (.step 31 (.run (.close 2))) (.step 24 (.run (.close 3)))) (.step 43 (.step 60 (.step 49 (.step 28 (.run (.close 31))))))))))) (.step 31 (.step 18 (.run (.close 2))))) (.step 18 (.step 31 (.step 18 (.step 2 (.run (.close 11))))))) (.step 18 (.step 31 (.step 47 (.step 51 (.step 49 (.step 69 (.split 38 0 (.step 18 (.run (.close 2))) (.step 60 (.step 50 (.run (.close 18)))))))))))) (.step 3 (.step 18 (.step 31 (.step 47 (.step 51 (.step 69 (.split 63 0 (.step 2 (.run (.close 31))) (.step 40 (.step 74 (.run (.close 31)))))))))))) (.step 3 (.step 18 (.step 51 (.step 69 (.split 63 0 (.split 17 1 (.step 31 (.run (.close 2))) (.step 23 (.run (.close 3)))) (.step 40 (.step 74 (.step 66 (.run (.close 31))))))))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.step 31 (.step 47 (.step 43 (.step 51 (.step 69 (.step 3 (.run (.close 7))))))))))) (.step 3 (.step 18 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part773
namespace Part774
def root : Box := ⟨3514776401986872174070733209129673327241950873673372369609965291102998109899599898686750536018664732148375711432438199315006457855854921632037902485053056745473, 11572809213564298906637997785778574998728371819868259251484020254801156019208419313466760564034152786940487892341667351196012156060798542424381215587483584181234406994014403995688272477153636559798306436949702814113592246274⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 17 0 (.split 22 0 (.split 14 0 (.split 74 0 (.split 0 1 (.split 49 0 (.split 50 0 (.split 59 0 (.split 8 0 (.split 12 0 (.split 13 0 (.split 25 0 (.split 26 0 (.split 64 0 (.split 44 0 (.split 47 0 (.split 48 0 (.split 63 0 (.step 2 (.run (.close 60))) (.step 18 (.run (.close 2)))) (.step 51 (.run (.close 2)))) (.step 18 (.step 51 (.step 2 (.step 60 (.step 2 (.run (.close 49)))))))) (.step 8 (.step 51 (.step 69 (.split 29 0 (.split 63 0 (.step 2 (.step 27 (.step 48 (.step 11 (.run (.close 18)))))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 18)))))))) (.step 18 (.step 31 (.step 51 (.step 2 (.run (.close 74))))))) (.step 2 (.step 18 (.run (.close 31))))) (.step 2 (.step 60 (.step 50 (.step 49 (.step 18 (.run (.close 8)))))))) (.step 2 (.step 60 (.step 50 (.step 49 (.step 63 (.step 48 (.run (.close 51))))))))) (.step 2 (.step 31 (.step 60 (.step 50 (.step 49 (.run (.close 8)))))))) (.step 2 (.run (.close 18)))) (.step 2 (.step 18 (.step 30 (.step 60 (.run (.close 50))))))) (.step 2 (.step 50 (.step 18 (.step 30 (.run (.close 73))))))) (.step 2 (.step 49 (.step 18 (.step 30 (.run (.close 73))))))) (.step 3 (.step 18 (.split 47 0 (.split 46 0 (.step 2 (.run (.close 51))) (.step 47 (.step 51 (.step 2 (.step 73 (.step 60 (.step 2 (.run (.close 49))))))))) (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 2 (.run (.close 60))) (.step 8 (.step 51 (.step 2 (.run (.close 60))))))))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 12 (.step 18 (.step 2 (.run (.close 11))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 3 (.step 51 (.step 2 (.run (.close 77)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part774
namespace Part775
def root : Box := ⟨3514776401986872174070733209129673327241950873673372369609965291102998109899599898686750536018664732148375711432438199315006457855854921632037902485053056745473, 11572820244868825110612595243234989860555963036094477429256650898983031156089303323874938603188004530761040751305645144670798199781061717926049243413968542775643901702921471599970252302906484967797626976599520215446931374082⟩
def references : Fin 1 → Box := ![Part774.root]
def proof : Enumeration.Proof 1 := (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.reuse 0) (.step 3 (.step 51 (.step 18 (.step 2 (.run (.close 8))))))) (.step 18 (.step 3 (.step 47 (.step 51 (.step 69 (.split 60 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 27 0 (.split 31 0 (.split 32 0 (.split 33 0 (.step 59 (.split 46 0 (.step 32 (.step 43 (.step 28 (.step 2 (.run (.close 32)))))) (.step 60 (.step 50 (.step 43 (.step 49 (.step 8 (.step 2 (.run (.close 51)))))))))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 28)))) (.step 4 (.step 5 (.run (.close 18))))) (.step 4 (.step 5 (.run (.close 18))))) (.step 48 (.step 58 (.step 40 (.step 50 (.step 49 (.step 4 (.run (.close 18))))))))) (.step 2 (.run (.close 24)))))))))) (.step 3 (.step 18 (.step 31 (.step 18 (.run (.close 2))))))) (.step 3 (.step 18 (.step 3 (.step 51 (.step 69 (.step 32 (.step 31 (.step 18 (.run (.close 2))))))))))) (.step 3 (.step 31 (.step 3 (.step 18 (.step 47 (.step 51 (.step 69 (.split 38 0 (.step 3 (.split 46 0 (.step 2 (.run (.close 18))) (.step 43 (.step 60 (.run (.close 18)))))) (.step 28 (.run (.close 3)))))))))))) (.step 3 (.step 31 (.step 51 (.step 69 (.split 38 0 (.step 3 (.split 46 0 (.step 18 (.run (.close 2))) (.step 43 (.step 60 (.step 50 (.run (.close 18))))))) (.step 28 (.run (.close 3)))))))))
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
def root : Box := ⟨2147483649, 11572820244868825110612595243234989860555963036094477429256650898983031156089303323874938603188004530761040751305645144675277689265417326347164127975105431331887192697390770669770230504834068710157948867361275201990145605634⟩
def references : Fin 4 → Box := ![Part771.root, Part772.root, Part773.root, Part775.root]
def proof : Enumeration.Proof 4 := (.split 53 0 (.split 17 0 (.split 34 0 (.reuse 0) (.split 36 0 (.split 42 0 (.reuse 1) (.step 31 (.split 14 0 (.step 3 (.split 35 0 (.split 38 0 (.step 31 (.run (.close 2))) (.step 28 (.run (.close 31)))) (.step 29 (.step 31 (.run (.close 38)))))) (.step 40 (.run (.close 3)))))) (.step 31 (.split 35 0 (.split 38 0 (.step 3 (.split 56 0 (.step 31 (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 28 (.run (.close 31)))))) (.step 31 (.step 7 (.step 28 (.step 59 (.run (.close 41))))))) (.step 31 (.step 29 (.step 7 (.step 75 (.step 41 (.run (.close 38))))))))))) (.split 22 0 (.split 14 0 (.reuse 2) (.step 3 (.step 18 (.step 51 (.split 44 0 (.split 46 0 (.step 18 (.split 66 0 (.split 63 0 (.split 64 0 (.step 31 (.step 2 (.step 61 (.step 74 (.run (.close 2)))))) (.step 3 (.run (.close 18)))) (.step 3 (.step 18 (.run (.close 74))))) (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 18)))) (.step 3 (.step 8 (.step 11 (.run (.close 2)))))))))) (.step 18 (.split 34 0 (.step 3 (.step 18 (.step 3 (.step 18 (.run (.close 2)))))) (.step 7 (.run (.close 3))))))) (.split 34 0 (.reuse 3) (.step 3 (.step 31 (.step 47 (.step 51 (.step 69 (.split 17 0 (.split 38 0 (.split 56 0 (.split 6 0 (.step 3 (.step 18 (.split 46 0 (.step 31 (.step 2 (.run (.close 60)))) (.step 43 (.run (.close 49)))))) (.step 2 (.run (.close 24)))) (.step 28 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 3)))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part771.covered
  · exact Part772.covered
  · exact Part773.covered
  · exact Part775.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part776
namespace Part777
def root : Box := ⟨1461501637330902918203684832716283019658080026625, 11572820244868825110612595243234989860555963036094477429256650891953478352115558975733472184928657876277139003958900405455347107059421106547964330601604359291187735067245514840328102222323178703176402120988056374667204624386⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 56 0 (.step 2 (.step 8 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 8))))) (.step 18 (.step 31 (.step 2 (.run (.close 8)))))) (.step 31 (.step 47 (.step 51 (.step 69 (.split 16 1 (.split 56 0 (.step 2 (.run (.close 60))) (.step 43 (.step 60 (.run (.close 31))))) (.step 3 (.run (.close 18))))))))) (.step 3 (.step 51 (.step 69 (.split 46 0 (.split 16 1 (.step 31 (.run (.close 2))) (.step 24 (.run (.close 3)))) (.step 43 (.step 60 (.step 50 (.run (.close 31)))))))))) (.step 31 (.step 18 (.run (.close 2))))) (.step 18 (.step 31 (.step 18 (.step 2 (.run (.close 11))))))) (.step 18 (.step 31 (.step 47 (.step 51 (.step 69 (.split 38 0 (.step 31 (.step 18 (.step 2 (.run (.close 74))))) (.step 40 (.step 60 (.step 49 (.run (.close 18)))))))))))) (.step 3 (.step 18 (.step 31 (.step 47 (.step 51 (.step 69 (.split 63 0 (.step 2 (.run (.close 31))) (.step 40 (.step 74 (.run (.close 31)))))))))))) (.step 3 (.step 18 (.step 51 (.step 69 (.split 63 0 (.split 16 1 (.step 31 (.run (.close 2))) (.step 23 (.run (.close 3)))) (.step 40 (.step 74 (.step 67 (.run (.close 31))))))))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.step 31 (.step 47 (.step 43 (.step 51 (.step 69 (.step 3 (.run (.close 7))))))))))) (.step 3 (.step 18 (.run (.close 2)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part777
namespace Part778
def root : Box := ⟨2147483649, 11572820244868825110612595243234989860555963036094477429256650898983031156089303323874938603188004530761040751305645144675277689265417326347164127975105431331887192697390770672693233779495874546565318532793841241302010691586⟩
def references : Fin 2 → Box := ![Part776.root, Part777.root]
def proof : Enumeration.Proof 2 := (.split 16 0 (.reuse 0) (.split 17 0 (.split 22 0 (.split 53 0 (.split 14 0 (.reuse 1) (.step 3 (.split 44 0 (.split 46 0 (.step 18 (.split 48 0 (.split 66 0 (.split 63 0 (.split 64 0 (.step 31 (.step 2 (.run (.close 74)))) (.step 3 (.run (.close 18)))) (.step 3 (.step 11 (.step 18 (.run (.close 74)))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 18)))) (.step 3 (.step 8 (.step 11 (.run (.close 2)))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.split 14 0 (.split 34 0 (.step 3 (.step 18 (.step 3 (.step 18 (.run (.close 2)))))) (.step 7 (.run (.close 3)))) (.step 3 (.step 11 (.run (.close 18))))))) (.step 18 (.split 14 0 (.split 22 0 (.split 34 0 (.step 3 (.step 18 (.step 3 (.step 18 (.run (.close 2)))))) (.step 7 (.run (.close 3)))) (.step 7 (.step 3 (.step 18 (.run (.close 8)))))) (.step 18 (.step 11 (.step 7 (.step 77 (.run (.close 17))))))))))
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
def root : Box := ⟨1298074214633706907132626229788673, 5648038695440039134447968108419270441226196924197710380805945987562090048950257852300983637690719347690235260696101212019132098160653102902854137041052929293866203301195772667415466941199208915795465025802506588670394370⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 18 (.split 0 1 (.split 49 0 (.split 50 0 (.split 59 0 (.split 12 0 (.split 25 0 (.split 26 0 (.split 44 0 (.split 46 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 47 0 (.step 2 (.run (.close 51))) (.step 18 (.step 51 (.step 2 (.step 60 (.step 2 (.run (.close 50)))))))) (.step 18 (.step 2 (.run (.close 18))))) (.step 18 (.step 31 (.step 18 (.run (.close 2)))))) (.step 18 (.step 31 (.step 18 (.step 51 (.step 69 (.step 12 (.split 53 0 (.step 2 (.run (.close 74))) (.step 48 (.step 58 (.run (.close 66)))))))))))) (.step 12 (.step 2 (.step 60 (.run (.close 2)))))) (.step 8 (.step 51 (.step 69 (.step 12 (.split 22 0 (.split 64 0 (.split 29 0 (.split 47 0 (.split 18 0 (.step 11 (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 11)))) (.step 8 (.step 2 (.run (.close 74))))) (.step 2 (.run (.close 18)))) (.step 11 (.step 18 (.run (.close 2))))) (.step 8 (.step 11 (.run (.close 2)))))))))) (.step 2 (.step 31 (.step 47 (.step 49 (.run (.close 18))))))) (.step 2 (.step 60 (.step 50 (.step 49 (.step 18 (.step 8 (.run (.close 51))))))))) (.step 2 (.step 63 (.step 47 (.step 48 (.step 60 (.step 50 (.step 49 (.run (.close 14)))))))))) (.step 2 (.step 18 (.step 30 (.step 60 (.step 50 (.run (.close 34)))))))) (.step 2 (.step 18 (.step 30 (.step 50 (.step 73 (.run (.close 49)))))))) (.step 2 (.run (.close 12)))) (.step 18 (.step 3 (.step 12 (.split 44 0 (.split 47 0 (.step 2 (.run (.close 51))) (.step 51 (.step 69 (.step 2 (.step 51 (.step 2 (.run (.close 60)))))))) (.step 8 (.step 51 (.step 2 (.step 47 (.step 2 (.run (.close 8)))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part779
namespace Part780
def root : Box := ⟨1298074214633706907132626229788673, 11572809213564298906637997785778574998728371819868259259031945104444238723691528475443298345867995227773368749094079951687260480845096246596634665942801119264171157055542093798152445011665030257476973872661475205972412596226⟩
def references : Fin 1 → Box := ![Part779.root]
def proof : Enumeration.Proof 1 := (.split 56 0 (.split 14 0 (.split 74 0 (.split 16 0 (.split 17 0 (.reuse 0) (.split 22 0 (.step 18 (.step 3 (.split 44 0 (.split 46 0 (.step 18 (.run (.close 2))) (.step 8 (.step 18 (.run (.close 60))))) (.step 8 (.run (.close 2)))))) (.step 18 (.run (.close 2))))) (.split 17 0 (.split 22 0 (.step 18 (.step 3 (.split 44 0 (.split 46 0 (.step 18 (.run (.close 2))) (.step 8 (.step 18 (.run (.close 60))))) (.step 8 (.run (.close 2)))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 8 (.run (.close 7)))))) (.step 3 (.split 16 0 (.split 17 0 (.step 18 (.step 12 (.step 18 (.step 2 (.run (.close 8)))))) (.step 8 (.run (.close 18)))) (.step 8 (.step 18 (.step 56 (.run (.close 14)))))))) (.step 3 (.split 16 0 (.split 17 0 (.step 12 (.step 18 (.step 2 (.run (.close 56))))) (.step 18 (.run (.close 14)))) (.step 48 (.step 8 (.step 18 (.step 77 (.run (.close 14))))))))) (.step 3 (.step 18 (.step 47 (.step 51 (.step 69 (.split 46 0 (.split 47 0 (.split 16 0 (.split 17 0 (.step 3 (.split 63 0 (.split 64 0 (.split 71 0 (.step 2 (.run (.close 51))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 18)))) (.step 48 (.step 23 (.step 60 (.run (.close 18))))))) (.step 8 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 50 (.step 8 (.step 24 (.step 28 (.step 60 (.step 3 (.run (.close 51)))))))))) (.step 43 (.step 60 (.step 8 (.step 49 (.step 28 (.step 3 (.run (.close 12)))))))))))))))
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
def root : Box := ⟨1298074214633706907132626229788673, 11572820244868825110612595243234989860555963036094477429256650898983031156089303323874938603188004530761040751305640447585632652114605938964855664739913791410546085063180057020950191159518064183466498511449130982600897200130⟩
def references : Fin 1 → Box := ![Part780.root]
def proof : Enumeration.Proof 1 := (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.reuse 0) (.step 3 (.step 18 (.step 47 (.step 51 (.step 69 (.split 46 0 (.split 47 0 (.split 16 0 (.split 17 0 (.step 3 (.split 53 0 (.split 63 0 (.split 64 0 (.split 71 0 (.step 2 (.step 43 (.step 60 (.step 2 (.run (.close 8)))))) (.step 4 (.run (.close 18)))) (.step 4 (.run (.close 18)))) (.step 48 (.step 58 (.step 40 (.step 60 (.run (.close 18))))))) (.step 8 (.step 4 (.step 24 (.step 60 (.step 2 (.run (.close 51))))))))) (.step 8 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 60 (.step 50 (.step 8 (.step 28 (.step 3 (.run (.close 32))))))))) (.step 43 (.step 60 (.step 50 (.step 8 (.step 49 (.step 24 (.step 28 (.step 59 (.step 56 (.step 18 (.run (.close 51))))))))))))))))))) (.step 3 (.step 31 (.step 18 (.step 51 (.step 69 (.step 12 (.step 18 (.step 31 (.run (.close 2))))))))))) (.step 3 (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 18 (.step 31 (.split 53 0 (.step 3 (.step 32 (.step 31 (.step 2 (.step 4 (.run (.close 2))))))) (.step 4 (.step 18 (.run (.close 74))))))) (.step 43 (.step 48 (.step 66 (.step 18 (.run (.close 50)))))))))))) (.step 3 (.step 31 (.step 51 (.step 69 (.split 16 0 (.split 38 0 (.step 3 (.split 46 0 (.split 42 1 (.step 18 (.run (.close 2))) (.step 43 (.run (.close 3)))) (.step 43 (.step 60 (.step 49 (.run (.close 18))))))) (.step 28 (.run (.close 3)))) (.step 7 (.step 3 (.run (.close 2))))))))))
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
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727074585042721378292777435812376133285876920625254286345394998395011073, 5648038695440039144245734729733955315121897727000997137775252166335722480781902788604987944819606187898173209232501452014281390792397836192188402832378928882077570976893818585655400318310512600280752771149689220520476674⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 38 0 (.split 56 0 (.split 0 1 (.split 67 1 (.split 69 0 (.split 46 0 (.split 63 0 (.split 47 0 (.split 64 0 (.step 2 (.run (.close 18))) (.step 18 (.step 2 (.run (.close 69))))) (.step 18 (.step 2 (.run (.close 69))))) (.step 18 (.step 69 (.split 64 0 (.step 2 (.run (.close 74))) (.step 47 (.step 2 (.step 57 (.step 61 (.step 74 (.step 2 (.run (.close 66)))))))))))) (.step 18 (.step 69 (.split 47 0 (.step 2 (.run (.close 60))) (.step 47 (.step 51 (.step 2 (.run (.close 60))))))))) (.step 2 (.step 63 (.step 47 (.step 48 (.step 60 (.run (.close 69)))))))) (.step 3 (.step 69 (.run (.close 2))))) (.step 3 (.step 69 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.step 2 (.run (.close 63))) (.step 69 (.split 57 0 (.step 2 (.run (.close 74))) (.step 63 (.run (.close 2)))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.step 68 (.step 60 (.run (.close 49))))))) (.step 69 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.step 2 (.run (.close 74))) (.step 30 (.step 10 (.run (.close 63))))) (.step 68 (.step 48 (.step 63 (.step 66 (.step 67 (.run (.close 74)))))))) (.step 18 (.step 2 (.run (.close 60))))) (.step 30 (.step 10 (.step 18 (.step 50 (.step 49 (.run (.close 60))))))))))))) (.step 3 (.step 31 (.step 69 (.split 44 0 (.split 46 0 (.step 2 (.run (.close 60))) (.step 10 (.step 43 (.step 60 (.step 50 (.step 2 (.run (.close 76)))))))) (.step 30 (.run (.close 10)))))))) (.step 3 (.step 31 (.step 69 (.split 44 0 (.split 46 0 (.step 32 (.step 2 (.run (.close 51)))) (.step 68 (.step 60 (.step 50 (.step 49 (.step 28 (.run (.close 51)))))))) (.step 30 (.run (.close 10))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part782
namespace Part783
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727074585042721378292777435812376133285876920625254286345394998395011073, 11572820244868825110622393009856304545429858736897280708465695362548274888011770154976171243920637631252269574923262909094645194444867574189448083624112885481057278140147356224641855257100643060147628643347780257230805270530⟩
def references : Fin 1 → Box := ![Part782.root]
def proof : Enumeration.Proof 1 := (.split 17 0 (.split 22 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 74 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.reuse 0) (.step 3 (.step 31 (.step 69 (.run (.close 2)))))) (.step 3 (.step 31 (.step 69 (.split 44 0 (.split 48 0 (.split 63 0 (.step 2 (.run (.close 74))) (.step 55 (.step 74 (.step 66 (.run (.close 67)))))) (.step 55 (.step 57 (.step 66 (.step 2 (.run (.close 21))))))) (.step 27 (.run (.close 9)))))))) (.step 3 (.step 31 (.step 18 (.run (.close 2)))))) (.step 3 (.step 31 (.step 18 (.run (.close 2)))))) (.step 31 (.split 35 0 (.step 3 (.split 38 0 (.step 18 (.run (.close 2))) (.step 7 (.run (.close 18))))) (.step 7 (.run (.close 18)))))) (.step 3 (.step 18 (.step 69 (.run (.close 2)))))) (.step 3 (.step 18 (.step 69 (.split 44 0 (.split 48 0 (.split 63 0 (.step 2 (.run (.close 74))) (.step 55 (.step 74 (.run (.close 34))))) (.step 55 (.step 61 (.step 66 (.step 2 (.run (.close 69))))))) (.step 27 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 69 (.split 44 0 (.split 47 0 (.step 2 (.run (.close 60))) (.step 30 (.step 43 (.step 60 (.step 2 (.run (.close 51))))))) (.step 30 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 69 (.split 44 0 (.split 46 0 (.split 47 0 (.step 2 (.run (.close 60))) (.step 68 (.step 60 (.step 50 (.run (.close 51)))))) (.step 68 (.step 60 (.step 50 (.run (.close 12)))))) (.step 30 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 31 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))))))) (.step 3 (.step 18 (.step 31 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 18))))))))
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
def root : Box := ⟨2147483649, 11572820244868825110622393009856304545429858736897280708465695362548274888011770154976171243920637631252269574923262909094645194444867574189448083624112885481057278140147356227564858531762448896554998308780346296542670356482⟩
def references : Fin 3 → Box := ![Part778.root, Part781.root, Part783.root]
def proof : Enumeration.Proof 3 := (.split 67 0 (.split 11 0 (.reuse 0) (.split 34 0 (.split 36 0 (.reuse 1) (.step 3 (.step 31 (.step 51 (.step 69 (.split 16 0 (.split 38 0 (.step 3 (.split 46 0 (.split 36 1 (.split 42 0 (.step 18 (.run (.close 2))) (.step 43 (.run (.close 3)))) (.step 43 (.run (.close 3)))) (.step 43 (.step 60 (.step 50 (.step 49 (.step 8 (.run (.close 18))))))))) (.step 28 (.run (.close 3)))) (.step 7 (.step 3 (.run (.close 2)))))))))) (.step 3 (.step 31 (.step 51 (.step 69 (.split 16 0 (.split 17 0 (.split 38 0 (.split 56 0 (.split 46 0 (.split 6 0 (.step 3 (.split 34 1 (.split 36 0 (.split 42 0 (.step 18 (.run (.close 2))) (.step 43 (.run (.close 3)))) (.step 43 (.run (.close 3)))) (.step 43 (.run (.close 3))))) (.step 2 (.run (.close 24)))) (.step 43 (.step 24 (.step 49 (.run (.close 4)))))) (.step 28 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 7 (.step 3 (.run (.close 2))))))))))) (.split 16 0 (.reuse 2) (.step 3 (.step 18 (.split 11 0 (.split 14 0 (.step 31 (.split 17 0 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 18)))) (.step 3 (.run (.close 7))))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part778.covered
  · exact Part781.covered
  · exact Part783.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part784
namespace Part785
def root : Box := ⟨4671939192445127903888559724237098316690665991422525368913093138328857771221685643782054718788988313373329725003360673086145233634688448510210725191395547328770042546544911308884863172862669750273, 5648038695440039134447977452297655331482000649055861119657886292067961257769807589763372303680369764243309938304052883493344978588823498285507868810475564930130975379936758168741792709399082558218866653314663014222266369⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 6 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 39 0 (.split 54 0 (.split 58 0 (.split 46 0 (.split 63 0 (.split 47 0 (.split 64 0 (.split 9 0 (.split 13 0 (.split 29 0 (.split 32 0 (.split 7 0 (.split 18 0 (.step 69 (.step 2 (.run (.close 18)))) (.step 2 (.step 10 (.run (.close 57))))) (.step 2 (.step 10 (.run (.close 57))))) (.step 2 (.step 30 (.run (.close 61))))) (.step 2 (.step 18 (.run (.close 47))))) (.step 2 (.step 10 (.run (.close 57))))) (.step 2 (.step 18 (.run (.close 47))))) (.step 18 (.step 47 (.step 2 (.step 57 (.step 61 (.step 63 (.step 67 (.run (.close 51)))))))))) (.step 18 (.step 47 (.step 51 (.step 2 (.run (.close 60))))))) (.step 18 (.step 47 (.step 51 (.step 69 (.step 2 (.step 63 (.step 12 (.step 74 (.step 2 (.run (.close 66)))))))))))) (.step 18 (.step 47 (.step 51 (.step 69 (.step 2 (.step 12 (.step 60 (.step 2 (.run (.close 49))))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 27 (.step 63 (.run (.close 61))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 9 (.step 63 (.run (.close 57))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 27 (.step 63 (.run (.close 61))))))))) (.step 2 (.step 55 (.step 18 (.step 9 (.run (.close 57))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 63 (.run (.close 61)))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 9 (.step 63 (.run (.close 57))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 63 (.run (.close 57))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part785
namespace Part786
def root : Box := ⟨4671939192445127903888559724237098316690665991422525368913093138328857771221685643782054718788988313373329725003360673086145233634688448510210725191395547328770042546544911308884863172862669750273, 5648038695440039144245744073612340205377705504120445611971885547667705325832640614791264602537856316517625631605594619915128943036678679649187888592856082079969041321521443726638049967481234999738809123473719991650484226⟩
def references : Fin 1 → Box := ![Part785.root]
def proof : Enumeration.Proof 1 := (.split 0 1 (.split 4 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 28 0 (.split 38 0 (.split 56 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 67 0 (.reuse 0) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 48 (.step 63 (.run (.close 66)))) (.step 63 (.step 50 (.step 49 (.run (.close 60)))))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 63 (.step 74 (.step 66 (.run (.close 67)))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 63 (.step 66 (.run (.close 67))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 63 (.step 74 (.run (.close 66))))))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.step 31 (.step 47 (.step 51 (.step 69 (.step 10 (.step 2 (.step 60 (.step 2 (.run (.close 76))))))))))))) (.step 71 (.step 3 (.step 31 (.step 68 (.step 47 (.step 51 (.step 69 (.step 10 (.step 32 (.step 2 (.step 60 (.step 2 (.run (.close 76))))))))))))))) (.step 2 (.step 3 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 2 (.step 3 (.run (.close 18))))) (.step 2 (.step 3 (.run (.close 18))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.split 47 0 (.step 63 (.step 74 (.run (.close 66)))) (.step 63 (.step 50 (.run (.close 48))))) (.step 18 (.step 60 (.run (.close 49)))))))))))
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
def root : Box := ⟨3432398830065304857490950399540696608634717650071652704697231729592771591698828026061279820330727277488648155695740429018560993999858321906287014147705012225, 5648038695440039144245744073612340205377705504120438064047035911449798502854088353235383567776808700906199254085524988751366083044505172841667950430471829938843374537535939655861503889473455214030028857319632755643908097⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 34 0 (.split 36 0 (.split 42 0 (.split 61 0 (.split 65 0 (.split 67 0 (.split 69 0 (.split 49 0 (.split 52 1 (.split 63 0 (.split 46 0 (.split 9 0 (.split 47 0 (.split 64 0 (.step 2 (.run (.close 18))) (.step 18 (.step 2 (.step 27 (.step 9 (.step 63 (.step 67 (.run (.close 74))))))))) (.step 18 (.step 2 (.step 30 (.step 10 (.step 48 (.run (.close 50)))))))) (.step 2 (.step 47 (.step 18 (.run (.close 51)))))) (.step 18 (.step 47 (.step 51 (.step 2 (.step 60 (.step 2 (.run (.close 49))))))))) (.step 18 (.step 47 (.step 51 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))))) (.step 3 (.step 55 (.step 47 (.step 51 (.step 69 (.split 46 0 (.split 63 0 (.step 50 (.step 48 (.run (.close 67)))) (.step 48 (.step 63 (.step 74 (.run (.close 66)))))) (.step 18 (.step 60 (.run (.close 49))))))))))) (.step 2 (.step 48 (.step 55 (.step 47 (.step 63 (.step 74 (.run (.close 66))))))))) (.step 2 (.step 63 (.step 68 (.step 47 (.step 48 (.step 60 (.step 50 (.run (.close 49)))))))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 48 (.step 63 (.run (.close 66)))) (.step 63 (.step 50 (.step 49 (.run (.close 60)))))))))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.split 47 0 (.step 63 (.step 74 (.run (.close 66)))) (.step 63 (.step 50 (.run (.close 48))))) (.step 18 (.step 60 (.run (.close 49))))))))))) (.step 2 (.step 63 (.step 68 (.step 47 (.step 48 (.step 50 (.run (.close 49))))))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part787
namespace Part788
def root : Box := ⟨3432398830065304857490950399540696608634717650071652704697231729592771591698828026061279820330727277488648155695740429018560993999858321906287014147705012225, 11572820244868825110622393019200182930320114544674400156939891995936471668516951502517339421377434566912910297787515652082016284650712567379567085848525912389410633048849186436541567340225437901765262509763765743154997755906⟩
def references : Fin 1 → Box := ![Part787.root]
def proof : Enumeration.Proof 1 := (.step 31 (.split 11 0 (.split 53 0 (.split 38 0 (.split 56 0 (.split 14 0 (.split 74 0 (.split 0 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 35 0 (.split 72 0 (.reuse 0) (.step 3 (.step 55 (.step 31 (.step 47 (.step 51 (.step 69 (.step 9 (.step 2 (.step 57 (.step 2 (.run (.close 74))))))))))))) (.step 58 (.step 3 (.step 31 (.step 55 (.step 47 (.step 51 (.step 69 (.step 9 (.step 32 (.step 2 (.step 57 (.step 2 (.run (.close 74))))))))))))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.split 47 0 (.step 63 (.step 74 (.run (.close 66)))) (.step 63 (.step 50 (.run (.close 48))))) (.step 18 (.step 60 (.run (.close 49))))))))))) (.step 3 (.step 55 (.step 18 (.step 47 (.step 51 (.step 69 (.step 27 (.step 23 (.step 2 (.step 61 (.step 2 (.run (.close 74)))))))))))))) (.step 3 (.step 48 (.step 18 (.step 55 (.step 47 (.step 51 (.step 69 (.step 27 (.step 23 (.step 12 (.step 2 (.step 61 (.step 2 (.run (.close 74)))))))))))))))) (.step 3 (.step 68 (.step 31 (.step 10 (.step 51 (.step 2 (.run (.close 76))))))))) (.step 3 (.step 31 (.step 68 (.step 47 (.step 51 (.step 69 (.step 10 (.step 43 (.step 60 (.step 50 (.step 49 (.step 2 (.run (.close 76))))))))))))))) (.step 3 (.step 68 (.step 18 (.step 30 (.step 51 (.step 2 (.run (.close 73))))))))) (.step 3 (.step 18 (.step 68 (.step 47 (.step 51 (.step 69 (.step 30 (.step 24 (.step 60 (.step 50 (.step 49 (.step 2 (.run (.close 73))))))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part787.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part788
namespace Part789
def root : Box := ⟨2147483649, 11572820244868825110622393019200182930320114544674400156939891995936471668516951502517339421377434566912910297787515652082016284650712567379567085848525912391095629715546102921747434047339655977644537570362646670554829946882⟩
def references : Fin 3 → Box := ![Part784.root, Part786.root, Part788.root]
def proof : Enumeration.Proof 3 := (.split 52 0 (.split 65 0 (.reuse 0) (.step 18 (.step 31 (.split 14 0 (.split 74 0 (.split 35 0 (.split 72 0 (.split 11 0 (.split 53 0 (.reuse 1) (.step 3 (.step 68 (.step 18 (.step 47 (.step 51 (.step 69 (.step 30 (.step 24 (.step 2 (.step 60 (.step 2 (.run (.close 73)))))))))))))) (.step 3 (.step 63 (.step 18 (.step 68 (.step 47 (.step 51 (.step 69 (.step 30 (.step 24 (.step 12 (.step 2 (.step 60 (.step 2 (.run (.close 73)))))))))))))))) (.step 3 (.step 55 (.step 31 (.step 9 (.step 51 (.step 67 (.step 2 (.run (.close 69)))))))))) (.step 3 (.step 31 (.step 55 (.step 47 (.step 51 (.step 69 (.step 9 (.step 40 (.step 74 (.step 66 (.step 67 (.step 2 (.run (.close 57))))))))))))))) (.step 3 (.step 55 (.step 18 (.step 27 (.step 51 (.step 66 (.step 2 (.run (.close 69)))))))))) (.step 3 (.step 18 (.step 55 (.step 47 (.step 51 (.step 69 (.step 27 (.step 23 (.step 74 (.step 66 (.step 67 (.step 2 (.run (.close 61)))))))))))))))))) (.step 18 (.reuse 2)))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part784.covered
  · exact Part786.covered
  · exact Part788.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part789
namespace Part790
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608414399004673, 5648038695440039134447977452297655331482004701317158855002572346212770484352228550552529847640103447492950461114401176148501878731287375837095761441408735781843600268534643569308709653461024883825115585885301937398611969⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 49 0 (.split 50 0 (.split 51 1 (.split 52 0 (.split 65 0 (.split 6 0 (.split 46 0 (.split 63 0 (.split 47 0 (.split 64 0 (.step 2 (.run (.close 18))) (.step 18 (.step 2 (.run (.close 51))))) (.step 18 (.step 2 (.run (.close 51))))) (.step 18 (.step 51 (.split 64 0 (.step 2 (.run (.close 74))) (.step 47 (.step 51 (.step 2 (.run (.close 74))))))))) (.step 18 (.step 51 (.step 12 (.split 47 0 (.step 2 (.run (.close 60))) (.step 47 (.step 2 (.step 73 (.step 60 (.step 2 (.run (.close 49)))))))))))) (.step 2 (.step 48 (.step 47 (.step 63 (.run (.close 57))))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 48 (.step 63 (.run (.close 66)))) (.step 63 (.step 50 (.step 49 (.run (.close 60)))))))))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 48 (.step 63 (.run (.close 66)))) (.step 63 (.step 50 (.step 49 (.run (.close 60)))))))))))) (.step 3 (.step 51 (.run (.close 2))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 63 (.step 66 (.run (.close 67))))))))) (.step 2 (.step 48 (.step 68 (.step 47 (.step 63 (.step 74 (.run (.close 66)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part790
namespace Part791
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608414399004673, 5659069999966243109045434908712517159073220927535336627633216528087907365236238958730569001491847268045809425092194655414035083350071298620008149063255886434629303644901317651266737333893175243467545997457689813951971330⟩
def references : Fin 1 → Box := ![Part790.root]
def proof : Enumeration.Proof 1 := (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 0 1 (.reuse 0) (.step 3 (.step 51 (.split 44 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 2 (.step 68 (.step 74 (.run (.close 66))))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.step 73 (.step 76 (.step 60 (.run (.close 49)))))))) (.step 51 (.split 46 0 (.split 47 0 (.split 57 0 (.split 63 0 (.step 2 (.run (.close 74))) (.step 27 (.step 9 (.step 66 (.run (.close 67)))))) (.step 30 (.step 10 (.run (.close 18))))) (.step 18 (.step 2 (.run (.close 60))))) (.step 30 (.step 10 (.step 18 (.step 50 (.step 49 (.run (.close 60))))))))))))) (.step 3 (.step 31 (.step 51 (.run (.close 2)))))) (.step 3 (.step 31 (.step 51 (.split 44 0 (.split 46 0 (.step 32 (.step 2 (.run (.close 76)))) (.step 68 (.step 60 (.step 50 (.step 49 (.run (.close 51))))))) (.step 30 (.run (.close 10)))))))) (.step 3 (.step 31 (.step 51 (.split 44 0 (.split 63 0 (.step 2 (.run (.close 57))) (.step 9 (.step 40 (.step 74 (.step 2 (.run (.close 69))))))) (.step 27 (.run (.close 9)))))))) (.step 3 (.step 31 (.step 51 (.split 44 0 (.split 63 0 (.step 32 (.step 2 (.run (.close 69)))) (.step 55 (.step 74 (.step 66 (.step 67 (.run (.close 69))))))) (.step 27 (.run (.close 9)))))))) (.step 3 (.step 31 (.step 18 (.run (.close 2)))))) (.step 3 (.step 31 (.step 18 (.run (.close 2)))))) (.step 31 (.split 35 0 (.step 3 (.split 38 0 (.step 18 (.run (.close 2))) (.step 7 (.run (.close 18))))) (.step 7 (.run (.close 18))))))
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
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608414399004673, 11572820244868825110612595252578868245446218843871596877730847532371234640498449642714656567657300569344745213852808183859337641251984180419298166973006859179074627724503362382804902538098511100744693035074929097386837934082⟩
def references : Fin 1 → Box := ![Part791.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 74 0 (.reuse 0) (.step 3 (.step 18 (.step 51 (.split 44 0 (.split 64 0 (.step 2 (.run (.close 61))) (.step 42 (.step 40 (.step 74 (.step 66 (.step 2 (.run (.close 61)))))))) (.step 27 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 51 (.split 44 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 61))) (.step 42 (.step 40 (.step 11 (.step 55 (.step 74 (.step 67 (.run (.close 61))))))))) (.step 55 (.step 74 (.step 66 (.run (.close 34)))))) (.step 27 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 51 (.run (.close 2)))))) (.step 3 (.step 18 (.step 51 (.split 44 0 (.split 46 0 (.split 47 0 (.step 2 (.run (.close 60))) (.step 68 (.step 60 (.step 2 (.run (.close 51)))))) (.step 68 (.step 60 (.step 50 (.run (.close 12)))))) (.step 30 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 31 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))))))) (.step 3 (.step 18 (.step 31 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 18)))))))) (.step 3 (.step 18 (.split 11 0 (.split 14 0 (.step 31 (.split 17 0 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 18)))) (.step 3 (.run (.close 7))))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571831121641473, 5659069999966243109045434908712517159073220927535336627633216528081203461271267660180781994532668362727369744811411060165667118188399672243507294801912753112814564527538558336400962681258170666507098630751881095517569026⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 72 0 (.split 38 0 (.split 56 0 (.split 0 1 (.split 43 1 (.split 52 0 (.split 65 0 (.split 46 0 (.split 63 0 (.split 47 0 (.split 64 0 (.step 2 (.run (.close 18))) (.step 18 (.step 2 (.run (.close 47))))) (.step 18 (.step 2 (.run (.close 47))))) (.step 18 (.step 47 (.split 64 0 (.step 2 (.run (.close 74))) (.step 47 (.step 2 (.step 74 (.step 2 (.run (.close 66)))))))))) (.step 18 (.step 47 (.split 47 0 (.step 2 (.run (.close 60))) (.step 47 (.step 2 (.step 60 (.step 2 (.run (.close 49)))))))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 48 (.step 63 (.run (.close 66)))) (.step 63 (.step 50 (.step 49 (.run (.close 60)))))))))))) (.step 3 (.step 68 (.step 47 (.step 51 (.step 69 (.split 46 0 (.step 48 (.step 63 (.run (.close 66)))) (.step 63 (.step 50 (.step 49 (.run (.close 60)))))))))))) (.step 3 (.step 47 (.run (.close 2))))) (.step 3 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.step 2 (.run (.close 74))) (.step 18 (.run (.close 2)))) (.split 57 0 (.split 63 0 (.step 2 (.run (.close 74))) (.step 68 (.step 66 (.run (.close 67))))) (.step 68 (.run (.close 18))))) (.step 18 (.step 2 (.run (.close 60))))) (.step 18 (.step 12 (.step 68 (.step 60 (.run (.close 50))))))) (.step 47 (.split 18 0 (.step 68 (.run (.close 47))) (.step 2 (.run (.close 9)))))))) (.step 3 (.step 28 (.step 18 (.step 47 (.step 2 (.step 68 (.run (.close 28))))))))) (.step 3 (.step 28 (.step 18 (.split 48 0 (.step 2 (.run (.close 47))) (.step 68 (.step 10 (.run (.close 28))))))))) (.step 3 (.step 29 (.step 18 (.step 47 (.step 2 (.step 55 (.run (.close 29)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part793
namespace Part794
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571831121641473, 11572820244868825110612595252578868245446218843871596877730847532371227936594484671416106780650346805809923103889054716030934946878135193688034763349859417403154786888400768612955758107281363379998069483712763024220283207682⟩
def references : Fin 1 → Box := ![Part793.root]
def proof : Enumeration.Proof 1 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 74 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.reuse 0) (.step 3 (.step 29 (.step 18 (.split 48 0 (.step 2 (.run (.close 47))) (.step 55 (.step 9 (.run (.close 29))))))))) (.step 18 (.step 3 (.step 29 (.step 28 (.step 3 (.step 68 (.run (.close 18))))))))) (.step 3 (.step 31 (.step 18 (.run (.close 2)))))) (.step 3 (.step 31 (.split 35 0 (.split 38 0 (.step 18 (.run (.close 2))) (.step 10 (.step 43 (.run (.close 28))))) (.step 9 (.step 43 (.run (.close 29)))))))) (.step 3 (.step 11 (.step 18 (.step 47 (.step 2 (.step 55 (.run (.close 11))))))))) (.step 3 (.step 11 (.step 18 (.step 47 (.split 48 0 (.step 2 (.run (.close 27))) (.step 55 (.run (.close 11))))))))) (.step 3 (.step 8 (.step 18 (.step 47 (.step 2 (.step 68 (.run (.close 8))))))))) (.step 3 (.step 8 (.step 18 (.step 47 (.split 48 0 (.step 2 (.run (.close 30))) (.step 68 (.run (.close 8))))))))) (.step 3 (.step 18 (.step 31 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))))))) (.step 3 (.step 18 (.step 31 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 18)))))))) (.step 3 (.step 18 (.split 11 0 (.split 14 0 (.step 31 (.split 17 0 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 68 (.run (.close 3)))) (.step 43 (.run (.close 18)))) (.step 3 (.run (.close 7))))) (.step 43 (.step 27 (.step 11 (.run (.close 23)))))) (.step 43 (.step 30 (.step 8 (.run (.close 23)))))))))
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
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571831121641473, 11572820244868825110622393019200182930320114544674400156939891995936478372420916473815889208395479009224215667189582776646991313838307302412333755772355272489473955782871199183756476102573362010780725965570427031037281304578⟩
def references : Fin 1 → Box := ![Part794.root]
def proof : Enumeration.Proof 1 := (.split 51 0 (.split 67 0 (.reuse 0) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 18 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.step 68 (.run (.close 2))) (.step 3 (.step 2 (.run (.close 74))))) (.step 10 (.step 30 (.step 63 (.step 2 (.step 68 (.run (.close 2)))))))) (.step 3 (.step 69 (.split 57 0 (.step 2 (.run (.close 74))) (.step 30 (.step 10 (.run (.close 63)))))))) (.step 3 (.step 18 (.step 2 (.run (.close 60)))))) (.step 10 (.step 30 (.step 3 (.step 18 (.step 50 (.run (.close 69)))))))) (.step 3 (.step 47 (.step 69 (.split 18 0 (.step 68 (.run (.close 18))) (.step 2 (.run (.close 9))))))))) (.step 68 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 7))))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 18 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.step 68 (.step 2 (.run (.close 9)))) (.step 3 (.step 2 (.run (.close 74))))) (.step 10 (.step 30 (.step 3 (.run (.close 63)))))) (.step 3 (.step 51 (.run (.close 2))))) (.step 3 (.step 18 (.step 2 (.run (.close 60)))))) (.step 10 (.step 30 (.step 3 (.step 18 (.step 50 (.run (.close 51)))))))) (.step 3 (.step 47 (.step 51 (.split 18 0 (.step 68 (.run (.close 18))) (.step 2 (.run (.close 9))))))))) (.step 68 (.step 2 (.run (.close 7))))) (.step 68 (.step 7 (.step 2 (.run (.close 7)))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 7))))) (.step 68 (.step 7 (.step 2 (.run (.close 7))))))))
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
def root : Box := ⟨2037035976334486086268445688409378161051468393665936250636140449354381299763336708330881025, 11572820244868825110612595247906929053001090939983037153493749215677129546341893997645522691916402998591361112737771516168963234368343897014176298059484481678283187241412246953648850135123947127749856528165766327656756805634⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 34 0 (.split 17 0 (.split 22 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 74 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 0 1 (.split 4 0 (.split 30 1 (.step 32 (.split 52 0 (.split 65 0 (.split 46 0 (.split 63 0 (.step 2 (.run (.close 18))) (.step 18 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))) (.step 18 (.step 2 (.step 60 (.step 2 (.run (.close 49))))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18)))))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 18)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 31 (.step 32 (.step 2 (.run (.close 50)))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 32 (.step 2 (.run (.close 67)))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.split 44 0 (.split 48 0 (.split 63 0 (.step 2 (.run (.close 67))) (.step 11 (.step 18 (.run (.close 74))))) (.step 18 (.run (.close 2)))) (.step 11 (.run (.close 2))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.split 44 0 (.split 46 0 (.step 18 (.run (.close 2))) (.step 8 (.step 18 (.run (.close 60))))) (.step 8 (.run (.close 2))))))) (.step 3 (.step 18 (.step 3 (.run (.close 2)))))) (.step 3 (.step 18 (.split 22 0 (.step 3 (.run (.close 2))) (.step 7 (.run (.close 3))))))) (.step 3 (.step 31 (.split 22 0 (.split 36 0 (.step 3 (.run (.close 2))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part796
namespace Part797
def root : Box := ⟨2037035976334486086268445688409378161051468393665936250636140449354381299763336708330881025, 11572820244868825110622393019200182930320114544674400156939891995936478372420916473815889208395479009224215667189582776646991313838311376484286424744527809380850774539193302120543807975074634291679434728169953704449648099330⟩
def references : Fin 1 → Box := ![Part796.root]
def proof : Enumeration.Proof 1 := (.step 3 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.reuse 0) (.step 3 (.step 18 (.split 17 0 (.split 22 0 (.split 34 0 (.step 3 (.run (.close 2))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 7))))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 7 (.run (.close 18)))) (.step 43 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 18 (.step 2 (.run (.close 68)))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 18 (.step 68 (.step 2 (.run (.close 68))))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))))
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
def root : Box := ⟨1267650600228229401498850689025, 11572820244868825110612595247906929053001090939983037153493749215677129546341893997645522691916402998591361112737771516168963234368339822942223629087311944786906368485090144016861518262622674849386448966022698457237796421634⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 34 0 (.split 17 0 (.split 22 0 (.split 11 0 (.split 53 0 (.split 14 0 (.split 74 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 0 1 (.split 4 0 (.split 10 1 (.step 12 (.split 52 0 (.split 65 0 (.split 64 0 (.split 47 0 (.step 2 (.run (.close 18))) (.step 18 (.step 2 (.step 60 (.step 2 (.run (.close 50))))))) (.step 18 (.step 2 (.step 74 (.step 2 (.run (.close 67))))))) (.step 3 (.step 68 (.run (.close 18))))) (.step 3 (.step 68 (.run (.close 18)))))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 18)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.split 44 0 (.split 46 0 (.step 31 (.run (.close 2))) (.step 28 (.step 31 (.run (.close 60))))) (.step 28 (.run (.close 2))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.split 44 0 (.split 48 0 (.split 63 0 (.step 2 (.run (.close 31))) (.step 29 (.step 31 (.run (.close 74))))) (.step 31 (.run (.close 2)))) (.step 29 (.run (.close 2))))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 31 (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 12 (.step 2 (.run (.close 66)))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 12 (.step 2 (.run (.close 49)))))) (.step 3 (.step 18 (.step 3 (.run (.close 2)))))) (.step 3 (.step 18 (.split 22 0 (.step 3 (.run (.close 2))) (.step 7 (.run (.close 3))))))) (.step 3 (.step 31 (.split 22 0 (.split 36 0 (.step 3 (.run (.close 2))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part798
namespace Part799
def root : Box := ⟨1267650600228229401498850689025, 11572820244868825110622393019200182930320114544674400156939891995936478372420916473815889208395479009224215667189582776646991313838311376484286424744527809380850774539193302120543807975074634294214735928626412507443054510082⟩
def references : Fin 1 → Box := ![Part798.root]
def proof : Enumeration.Proof 1 := (.step 3 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.reuse 0) (.step 3 (.step 18 (.split 17 0 (.split 22 0 (.split 34 0 (.step 3 (.run (.close 2))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 7))))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 18 (.run (.close 2))) (.step 7 (.run (.close 18)))) (.step 43 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 18 (.step 2 (.run (.close 68)))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 18 (.step 68 (.step 2 (.run (.close 68))))) (.step 7 (.run (.close 18)))) (.step 7 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 3 (.run (.close 2))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part798.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part799
namespace Part800
def root : Box := ⟨2148532225, 5648038695440039134447968108419270441226192871936412645461252910735978412719069763577095645964827320872022374194615305516718231929373493506830588745737366472695861782005282021481221914159470601266944591942098734282702849⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 2 1 (.split 46 0 (.split 63 0 (.split 9 0 (.split 44 0 (.split 47 0 (.step 2 (.run (.close 18))) (.step 18 (.run (.close 2)))) (.split 12 0 (.step 8 (.split 64 0 (.step 2 (.step 29 (.step 2 (.run (.close 8))))) (.step 27 (.step 29 (.step 2 (.run (.close 50))))))) (.step 2 (.step 9 (.run (.close 10)))))) (.step 2 (.step 18 (.step 29 (.step 8 (.run (.close 11))))))) (.step 18 (.step 12 (.split 64 0 (.step 2 (.run (.close 11))) (.step 63 (.step 29 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))))))) (.step 18 (.step 12 (.split 47 0 (.step 2 (.run (.close 8))) (.step 48 (.step 58 (.step 50 (.step 49 (.run (.close 8)))))))))) (.step 3 (.split 46 0 (.split 63 0 (.split 9 0 (.split 47 0 (.split 64 0 (.split 29 0 (.split 23 0 (.split 31 0 (.step 5 (.step 30 (.step 9 (.step 29 (.run (.close 60)))))) (.step 2 (.step 30 (.run (.close 61))))) (.step 2 (.step 9 (.run (.close 57))))) (.step 2 (.step 29 (.run (.close 51))))) (.step 29 (.step 18 (.step 2 (.step 74 (.step 2 (.run (.close 67)))))))) (.step 8 (.step 18 (.step 2 (.step 60 (.step 2 (.run (.close 8)))))))) (.step 2 (.step 47 (.step 51 (.step 18 (.run (.close 69))))))) (.step 29 (.step 18 (.split 64 0 (.step 2 (.step 74 (.step 2 (.run (.close 66))))) (.step 63 (.step 40 (.step 74 (.step 66 (.step 67 (.run (.close 29))))))))))) (.step 8 (.step 18 (.split 47 0 (.step 2 (.step 60 (.step 2 (.run (.close 8))))) (.step 48 (.step 58 (.step 60 (.step 50 (.step 49 (.run (.close 8)))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part800
namespace Part801
def root : Box := ⟨2148532225, 5648038695440039139346856091015805323301951214159081770351337077815598724121646657847649815926452613504967466596434059117907768491956345276974330952446432460537960650107745674451657434022319439597844249106318293335015425⟩
def references : Fin 1 → Box := ![Part800.root]
def proof : Enumeration.Proof 1 := (.split 56 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 52 0 (.split 59 0 (.split 65 0 (.split 67 0 (.reuse 0) (.step 3 (.step 69 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.step 2 (.run (.close 48))) (.step 57 (.step 48 (.step 2 (.run (.close 63)))))) (.step 48 (.step 2 (.step 48 (.run (.close 2)))))) (.step 48 (.step 18 (.run (.close 2))))) (.step 30 (.run (.close 9))))))) (.step 3 (.step 68 (.step 47 (.step 48 (.run (.close 63))))))) (.step 2 (.step 48 (.step 27 (.run (.close 63)))))) (.step 3 (.step 68 (.step 47 (.step 48 (.run (.close 63))))))) (.step 3 (.step 51 (.split 44 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 2 (.run (.close 63))) (.step 48 (.step 2 (.run (.close 57))))) (.step 48 (.step 2 (.step 73 (.step 2 (.run (.close 57))))))) (.step 48 (.step 18 (.run (.close 2))))) (.step 30 (.run (.close 9))))))) (.step 2 (.step 48 (.step 63 (.run (.close 68)))))) (.step 2 (.step 48 (.step 63 (.run (.close 68)))))) (.step 3 (.step 29 (.split 9 0 (.step 68 (.step 48 (.run (.close 27)))) (.step 2 (.step 48 (.run (.close 27)))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.step 31 (.split 46 0 (.split 47 0 (.split 29 0 (.split 9 0 (.split 18 0 (.step 8 (.step 2 (.run (.close 51)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 59)))) (.step 2 (.run (.close 59)))) (.step 48 (.step 43 (.step 60 (.step 50 (.step 8 (.run (.close 59)))))))) (.step 48 (.step 43 (.step 60 (.step 48 (.step 49 (.step 28 (.run (.close 59)))))))))))))
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
def root : Box := ⟨2148532225, 5648038695440039139346856091015805323301951214159081770351337077815598724121646657847649815926452613504972391847208608427809303374005899205034452006123689699774165741667715195072445064421039698434807589316012124384788482⟩
def references : Fin 1 → Box := ![Part801.root]
def proof : Enumeration.Proof 1 := (.split 0 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.reuse 0) (.step 3 (.step 18 (.step 31 (.step 32 (.split 2 1 (.step 31 (.split 44 0 (.split 46 0 (.step 2 (.run (.close 51))) (.step 48 (.step 58 (.step 49 (.step 28 (.run (.close 51))))))) (.step 30 (.run (.close 28))))) (.step 8 (.step 5 (.step 48 (.step 60 (.step 58 (.step 8 (.step 49 (.run (.close 5))))))))))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.split 46 0 (.split 63 0 (.split 47 0 (.split 64 0 (.split 57 0 (.step 2 (.run (.close 11))) (.step 18 (.step 2 (.run (.close 8))))) (.step 18 (.step 32 (.step 51 (.step 2 (.run (.close 11))))))) (.step 18 (.step 32 (.step 51 (.step 2 (.run (.close 8))))))) (.step 18 (.step 12 (.step 51 (.step 69 (.split 48 0 (.step 2 (.run (.close 11))) (.step 47 (.step 2 (.step 57 (.step 61 (.run (.close 67)))))))))))) (.step 18 (.step 12 (.step 51 (.step 69 (.split 48 0 (.step 2 (.run (.close 8))) (.step 47 (.step 2 (.step 60 (.step 2 (.run (.close 8))))))))))))))
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
def root : Box := ⟨2148532225, 11572820244868825110617494131217586395438038790384438793098271440430201960281365550703947487532392407823478297042605561264282466560140277558148035068671656843773543201752105299420422188431717680205992814906591793745007476738⟩
def references : Fin 1 → Box := ![Part802.root]
def proof : Enumeration.Proof 1 := (.split 72 0 (.split 14 0 (.split 74 0 (.reuse 0) (.step 3 (.step 31 (.split 38 0 (.split 56 0 (.step 18 (.split 63 0 (.split 9 0 (.split 64 0 (.split 29 0 (.split 7 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 11 (.step 2 (.run (.close 69)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 11)))) (.step 2 (.run (.close 77)))) (.step 63 (.step 40 (.step 74 (.step 67 (.run (.close 11))))))) (.step 2 (.step 74 (.step 67 (.run (.close 77)))))) (.step 63 (.step 40 (.step 74 (.step 63 (.step 66 (.step 67 (.step 11 (.run (.close 69))))))))))) (.step 40 (.step 48 (.step 60 (.run (.close 18)))))) (.step 5 (.step 40 (.step 48 (.step 67 (.step 29 (.run (.close 18))))))))))) (.step 3 (.step 18 (.step 31 (.split 38 0 (.split 56 0 (.step 12 (.split 2 1 (.step 18 (.split 13 0 (.split 44 0 (.split 48 0 (.step 2 (.run (.close 69))) (.step 40 (.step 74 (.step 63 (.step 11 (.step 67 (.run (.close 51)))))))) (.step 9 (.run (.close 11)))) (.step 2 (.run (.close 23))))) (.step 29 (.step 5 (.step 63 (.step 74 (.step 40 (.step 67 (.step 29 (.run (.close 18))))))))))) (.step 5 (.step 40 (.step 48 (.step 49 (.step 29 (.run (.close 18)))))))) (.step 5 (.step 40 (.step 48 (.step 74 (.step 49 (.step 67 (.step 5 (.run (.close 29)))))))))))))) (.step 3 (.step 31 (.split 63 0 (.split 9 0 (.split 64 0 (.step 2 (.run (.close 29))) (.step 63 (.step 40 (.step 67 (.run (.close 29)))))) (.step 2 (.step 74 (.run (.close 75))))) (.step 63 (.step 40 (.step 74 (.step 63 (.step 66 (.step 29 (.run (.close 67))))))))))))
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
def root : Box := ⟨2147483649, 11572820244868825110622393019200182930320114544674400156939891995936478372420916473815889208395479009224215667189582776646991313838311376484286424744527809380850774539193302120543807975074634294214735928626412507443056607234⟩
def references : Fin 6 → Box := ![Part789.root, Part792.root, Part795.root, Part797.root, Part799.root, Part803.root]
def proof : Enumeration.Proof 6 := (.split 2 0 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.reuse 0) (.split 67 0 (.reuse 1) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 18 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.step 68 (.run (.close 2))) (.step 3 (.step 2 (.run (.close 74))))) (.step 18 (.run (.close 2)))) (.step 3 (.step 51 (.run (.close 2))))) (.step 3 (.step 18 (.step 2 (.run (.close 60)))))) (.step 3 (.step 18 (.step 51 (.step 2 (.run (.close 60))))))) (.step 3 (.step 51 (.step 69 (.split 46 0 (.split 47 0 (.split 57 0 (.step 2 (.run (.close 74))) (.step 30 (.step 10 (.run (.close 63))))) (.step 30 (.step 10 (.run (.close 18))))) (.step 30 (.step 10 (.step 63 (.step 50 (.step 49 (.run (.close 60))))))))))))) (.step 68 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 7)))))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.step 3 (.step 31 (.split 11 0 (.split 53 0 (.split 35 0 (.reuse 5) (.step 31 (.step 3 (.step 32 (.split 44 0 (.split 48 0 (.step 2 (.run (.close 69))) (.step 40 (.step 74 (.step 63 (.step 29 (.step 66 (.run (.close 51)))))))) (.step 27 (.run (.close 29)))))))) (.step 3 (.step 18 (.split 47 0 (.split 46 0 (.step 2 (.run (.close 8))) (.step 48 (.step 43 (.step 60 (.step 49 (.step 2 (.run (.close 8)))))))) (.step 43 (.step 60 (.step 50 (.step 48 (.step 8 (.run (.close 49))))))))))) (.step 3 (.step 18 (.step 12 (.split 44 0 (.split 47 0 (.step 2 (.run (.close 51))) (.step 48 (.step 58 (.step 50 (.step 8 (.run (.close 51))))))) (.step 10 (.run (.close 8)))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part789.covered
  · exact Part792.covered
  · exact Part795.covered
  · exact Part797.covered
  · exact Part799.covered
  · exact Part803.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part804
namespace Part805
def root : Box := ⟨2147484673, 5648038695440039134447968108419270441226192871936412645461252910735978412719069763577095645964827320872022374194615305516718231929373493506830588745737366472695861782005282021481221914159470601266944591942098734280607745⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 1 1 (.split 46 0 (.split 63 0 (.split 9 0 (.split 44 0 (.split 47 0 (.step 2 (.run (.close 18))) (.step 18 (.run (.close 2)))) (.split 12 0 (.step 8 (.split 64 0 (.step 2 (.step 29 (.step 2 (.run (.close 8))))) (.step 27 (.step 29 (.step 2 (.run (.close 50))))))) (.step 2 (.step 9 (.run (.close 10)))))) (.step 2 (.step 18 (.step 29 (.step 8 (.run (.close 11))))))) (.step 18 (.step 12 (.split 64 0 (.step 2 (.run (.close 11))) (.step 63 (.step 29 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))))))) (.step 18 (.step 12 (.split 47 0 (.step 2 (.run (.close 8))) (.step 48 (.step 58 (.step 50 (.step 49 (.run (.close 8)))))))))) (.step 3 (.split 46 0 (.split 63 0 (.split 9 0 (.split 47 0 (.split 64 0 (.split 29 0 (.split 23 0 (.split 31 0 (.step 4 (.step 30 (.step 9 (.step 29 (.run (.close 60)))))) (.step 2 (.step 30 (.run (.close 61))))) (.step 2 (.step 9 (.run (.close 57))))) (.step 2 (.step 29 (.run (.close 51))))) (.step 29 (.step 18 (.step 2 (.step 74 (.step 2 (.run (.close 67)))))))) (.step 8 (.step 18 (.step 2 (.step 60 (.step 2 (.run (.close 8)))))))) (.step 2 (.step 47 (.step 51 (.step 18 (.run (.close 69))))))) (.step 29 (.step 18 (.split 64 0 (.step 2 (.step 74 (.step 2 (.run (.close 66))))) (.step 63 (.step 40 (.step 66 (.step 67 (.run (.close 29)))))))))) (.step 8 (.step 18 (.split 47 0 (.step 2 (.step 60 (.step 2 (.run (.close 8))))) (.step 48 (.step 58 (.step 50 (.step 49 (.run (.close 8))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part805
namespace Part806
def root : Box := ⟨2147484673, 5659069999966243113944313547430667150893167440377244447132281973525326638787333112950125302087899397799778283970936239731216278322634510488163141857913251657016144419650300493128384428470228939884512310899695191926507521⟩
def references : Fin 1 → Box := ![Part805.root]
def proof : Enumeration.Proof 1 := (.split 72 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 52 0 (.split 59 0 (.split 65 0 (.split 67 0 (.reuse 0) (.step 3 (.step 69 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.step 2 (.run (.close 48))) (.step 57 (.step 48 (.step 2 (.run (.close 63)))))) (.step 48 (.step 2 (.step 48 (.run (.close 2)))))) (.step 48 (.step 18 (.run (.close 2))))) (.step 30 (.run (.close 9))))))) (.step 3 (.step 68 (.step 47 (.step 48 (.run (.close 63))))))) (.step 2 (.step 48 (.step 27 (.run (.close 63)))))) (.step 3 (.step 68 (.step 47 (.step 48 (.run (.close 63))))))) (.step 3 (.step 51 (.split 44 0 (.split 46 0 (.split 47 0 (.split 57 0 (.step 2 (.run (.close 63))) (.step 48 (.step 2 (.run (.close 57))))) (.step 48 (.step 2 (.step 73 (.step 2 (.run (.close 57))))))) (.step 48 (.step 18 (.run (.close 2))))) (.step 30 (.run (.close 9))))))) (.step 2 (.step 48 (.step 63 (.run (.close 68)))))) (.step 2 (.step 48 (.step 63 (.run (.close 68)))))) (.step 3 (.step 29 (.split 9 0 (.step 68 (.step 48 (.run (.close 27)))) (.step 2 (.step 48 (.run (.close 27)))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.step 31 (.split 63 0 (.split 64 0 (.split 29 0 (.split 9 0 (.split 18 0 (.step 11 (.step 2 (.run (.close 69)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 75)))) (.step 2 (.run (.close 75)))) (.step 63 (.step 40 (.step 74 (.step 63 (.step 67 (.step 29 (.run (.close 4))))))))) (.step 63 (.step 40 (.step 74 (.step 63 (.step 66 (.step 67 (.step 29 (.run (.close 69))))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part805.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part806
namespace Part807
def root : Box := ⟨2147484673, 5659069999966243113944313547430667150893167440377244447132281973525326638787333112950125302087899397799778283970940826728448258467694768106288232118063293845397192536782214476206508753294699385055755073760508445851650049⟩
def references : Fin 1 → Box := ![Part806.root]
def proof : Enumeration.Proof 1 := (.split 2 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.reuse 0) (.step 3 (.step 18 (.step 31 (.step 32 (.split 1 1 (.step 31 (.split 44 0 (.split 48 0 (.step 2 (.run (.close 69))) (.step 40 (.step 74 (.step 63 (.step 29 (.step 66 (.run (.close 51)))))))) (.step 27 (.run (.close 29))))) (.step 29 (.step 4 (.step 63 (.step 74 (.step 40 (.step 66 (.step 29 (.run (.close 18))))))))))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.split 46 0 (.split 63 0 (.split 47 0 (.split 64 0 (.split 9 0 (.step 51 (.step 2 (.run (.close 8)))) (.step 2 (.step 29 (.run (.close 51))))) (.step 29 (.step 18 (.step 2 (.step 74 (.step 2 (.run (.close 67)))))))) (.step 8 (.step 18 (.step 2 (.step 60 (.step 2 (.run (.close 8)))))))) (.step 29 (.step 18 (.step 12 (.step 63 (.step 74 (.step 40 (.step 66 (.run (.close 67)))))))))) (.step 8 (.step 18 (.step 12 (.step 48 (.step 60 (.step 58 (.step 50 (.run (.close 49))))))))))))
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
def root : Box := ⟨2147484673, 5659069999966243113944313547430667150893167440377244447132289003078130612531681254416543561434553881701525630715680046659030464463914567306085605619135331174861489288205079352605138766210411094899019149565478547670173698⟩
def references : Fin 1 → Box := ![Part807.root]
def proof : Enumeration.Proof 1 := (.split 53 0 (.split 0 1 (.reuse 0) (.step 3 (.split 46 0 (.split 63 0 (.split 47 0 (.split 64 0 (.split 57 0 (.step 2 (.run (.close 11))) (.step 18 (.step 2 (.run (.close 8))))) (.step 18 (.step 32 (.step 51 (.step 2 (.run (.close 11))))))) (.step 18 (.step 32 (.step 51 (.step 2 (.run (.close 8))))))) (.step 18 (.step 12 (.step 51 (.step 69 (.split 48 0 (.step 2 (.run (.close 11))) (.step 47 (.step 2 (.step 57 (.step 61 (.run (.close 67)))))))))))) (.step 18 (.step 12 (.step 51 (.step 69 (.split 48 0 (.step 2 (.run (.close 8))) (.step 47 (.step 2 (.step 60 (.step 2 (.run (.close 8)))))))))))))) (.step 3 (.step 31 (.split 35 0 (.split 72 0 (.step 18 (.split 46 0 (.split 9 0 (.split 47 0 (.split 29 0 (.split 6 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.step 2 (.run (.close 51)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 24)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 56)))) (.step 48 (.step 58 (.step 60 (.step 50 (.run (.close 8))))))) (.step 2 (.step 60 (.step 50 (.run (.close 56)))))) (.step 48 (.step 43 (.step 60 (.step 50 (.step 48 (.step 49 (.step 8 (.run (.close 51))))))))))) (.step 43 (.step 63 (.step 74 (.run (.close 18)))))) (.step 4 (.step 43 (.step 63 (.step 50 (.step 11 (.run (.close 18)))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part807.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part808
namespace Part809
def root : Box := ⟨2147483649, 11572820244868825110622393019200182930320114544674400156939891995936478372420916473815889208395479009224215667189582776646991313838311376484286424744527809380850774539193302120543807975074634294214735928626412507443056609282⟩
def references : Fin 2 → Box := ![Part804.root, Part808.root]
def proof : Enumeration.Proof 2 := (.split 1 0 (.reuse 0) (.step 3 (.step 31 (.split 14 0 (.split 74 0 (.split 38 0 (.split 56 0 (.split 11 0 (.reuse 1) (.step 3 (.step 18 (.step 31 (.split 35 0 (.split 72 0 (.step 12 (.split 1 1 (.step 18 (.split 44 0 (.split 47 0 (.step 2 (.run (.close 51))) (.step 48 (.step 58 (.step 50 (.step 8 (.run (.close 51))))))) (.step 10 (.run (.close 8))))) (.step 8 (.step 4 (.step 48 (.step 60 (.step 50 (.step 58 (.step 8 (.run (.close 18))))))))))) (.step 4 (.step 43 (.step 63 (.step 66 (.step 11 (.run (.close 18)))))))) (.step 4 (.step 43 (.step 63 (.step 60 (.step 50 (.step 66 (.step 4 (.run (.close 11)))))))))))))) (.step 3 (.step 31 (.split 46 0 (.split 9 0 (.split 47 0 (.step 2 (.run (.close 8))) (.step 48 (.step 60 (.step 50 (.step 2 (.run (.close 8))))))) (.step 2 (.step 60 (.run (.close 59))))) (.step 48 (.step 43 (.step 60 (.step 49 (.step 48 (.step 8 (.run (.close 59)))))))))))) (.step 31 (.step 3 (.step 32 (.step 43 (.split 44 0 (.split 46 0 (.step 2 (.run (.close 51))) (.step 48 (.step 60 (.step 49 (.step 28 (.run (.close 51))))))) (.step 30 (.run (.close 28))))))))) (.step 3 (.step 18 (.split 64 0 (.split 63 0 (.step 2 (.run (.close 29))) (.step 40 (.step 74 (.step 63 (.step 66 (.run (.close 11))))))) (.step 40 (.step 74 (.step 63 (.step 67 (.step 29 (.run (.close 77))))))))))) (.step 3 (.step 18 (.step 12 (.split 44 0 (.split 48 0 (.step 2 (.run (.close 69))) (.step 40 (.step 74 (.step 63 (.step 11 (.step 67 (.run (.close 51)))))))) (.step 9 (.run (.close 11)))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part804.covered
  · exact Part808.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part809
namespace Part810
def root : Box := ⟨2147483648, 11572820244868825110622393019200182930320114544674400156939891995936478372420916473815889208395479009224215667189582776646991313838311376484286424744527809380850774539193302120543807975074634294214735928626412507443056609282⟩
def references : Fin 7 → Box := ![Part615.root, Part674.root, Part677.root, Part680.root, Part683.root, Part758.root, Part809.root]
def proof : Enumeration.Proof 7 := (.split 0 0 (.split 1 0 (.split 2 0 (.reuse 0) (.split 10 0 (.split 30 0 (.split 43 0 (.reuse 1) (.split 51 0 (.reuse 2) (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.step 27 (.step 9 (.step 63 (.run (.close 3))))) (.step 30 (.step 9 (.step 48 (.run (.close 2)))))) (.step 48 (.step 63 (.step 3 (.step 2 (.run (.close 57))))))) (.step 30 (.step 10 (.step 48 (.run (.close 10)))))) (.step 30 (.step 10 (.step 48 (.run (.close 10)))))) (.step 30 (.step 9 (.run (.close 68))))) (.step 9 (.step 10 (.run (.close 2))))) (.step 9 (.step 10 (.run (.close 2))))) (.step 9 (.step 10 (.step 43 (.run (.close 3)))))) (.step 27 (.step 43 (.step 30 (.step 27 (.step 43 (.run (.close 3)))))))) (.step 27 (.step 43 (.step 30 (.step 27 (.step 43 (.run (.close 3)))))))) (.step 43 (.step 27 (.step 68 (.step 30 (.run (.close 8)))))))))) (.reuse 3)) (.reuse 4))) (.reuse 5)) (.reuse 6))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part615.covered
  · exact Part674.covered
  · exact Part677.covered
  · exact Part680.covered
  · exact Part683.covered
  · exact Part758.covered
  · exact Part809.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part810
end FiveColour.Packed.EnumerationChunks.Case132
