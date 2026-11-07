module
public import FiveColour.EnumerationChunks.Case142.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case142
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part768
def root : Box := ⟨1427247692705959881058285969449495138530230272, 5794887679965438090546899933839123354270966216145824413436713630539886635343492249294806971927603135232667249977419685089297836993597707059548158981730208973714652073556831231108938347063923413624347666233923215667070239745⟩
def references : Fin 3 → Box := ![Part763.root, Part765.root, Part767.root]
def proof : Enumeration.Proof 3 := (.split 43 0 (.split 22 0 (.reuse 0) (.step 18 (.split 36 0 (.split 42 0 (.reuse 1) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 38 0 (.step 3 (.step 31 (.run (.close 2)))) (.step 60 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 24 (.step 23 (.run (.close 26))))) (.step 55 (.run (.close 31)))))) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 38 0 (.split 42 0 (.step 3 (.step 31 (.run (.close 2)))) (.step 7 (.step 3 (.run (.close 43))))) (.step 3 (.run (.close 7)))) (.step 74 (.step 7 (.step 3 (.run (.close 2)))))) (.step 24 (.step 23 (.step 4 (.step 10 (.step 76 (.step 3 (.run (.close 7))))))))) (.step 3 (.run (.close 18)))))))) (.step 18 (.split 51 0 (.reuse 2) (.split 12 0 (.split 13 0 (.step 3 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 36 0 (.step 18 (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.step 2 (.step 7 (.run (.close 3)))) (.step 30 (.step 7 (.step 3 (.step 72 (.run (.close 64))))))) (.step 27 (.step 7 (.step 3 (.step 72 (.step 64 (.step 65 (.run (.close 70))))))))) (.step 27 (.step 7 (.step 3 (.step 62 (.step 65 (.step 53 (.step 72 (.step 53 (.run (.close 64))))))))))) (.step 27 (.step 7 (.step 3 (.step 62 (.step 53 (.step 64 (.step 70 (.step 52 (.step 72 (.step 53 (.run (.close 52)))))))))))))) (.step 68 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 43 (.step 30 (.step 27 (.step 68 (.run (.close 3))))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))) (.step 10 (.run (.close 3)))) (.step 9 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part763.covered
  · exact Part765.covered
  · exact Part767.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part768
namespace Part769
def root : Box := ⟨1645504557321206043582216875263310386041021835083075001878839296, 5794876648660911876534490572845813839137229519343124090519969671310278603664786823839005956539787130148073118771822910386704324320115964274461065175492692677398900059856291030150202720007758032506353605677078682040521458689⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 74 0 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 21 1 (.split 23 0 (.split 43 0 (.split 51 0 (.split 54 0 (.step 2 (.run (.close 73))) (.step 5 (.step 2 (.run (.close 63))))) (.step 3 (.run (.close 2)))) (.step 30 (.step 2 (.run (.close 48))))) (.split 61 0 (.split 62 0 (.split 69 0 (.step 2 (.run (.close 30))) (.step 73 (.step 2 (.run (.close 3))))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 73)))))) (.step 18 (.step 24 (.run (.close 2))))) (.step 22 (.step 26 (.split 61 0 (.split 62 0 (.split 43 0 (.split 51 0 (.step 2 (.run (.close 3))) (.step 61 (.step 2 (.run (.close 3))))) (.step 9 (.step 10 (.step 24 (.step 2 (.run (.close 30))))))) (.step 24 (.step 3 (.run (.close 2))))) (.step 24 (.step 3 (.step 2 (.step 73 (.step 2 (.run (.close 76))))))))))) (.step 21 (.step 22 (.step 26 (.split 61 0 (.split 69 0 (.split 43 0 (.split 51 0 (.split 73 0 (.step 2 (.run (.close 61))) (.step 3 (.run (.close 2)))) (.step 24 (.step 23 (.run (.close 3))))) (.step 24 (.step 23 (.run (.close 3))))) (.step 24 (.step 3 (.step 2 (.run (.close 73)))))) (.step 24 (.step 3 (.step 43 (.step 18 (.step 24 (.step 10 (.step 76 (.step 35 (.run (.close 21))))))))))))))) (.step 3 (.step 21 (.step 22 (.step 26 (.step 12 (.split 62 0 (.step 2 (.step 73 (.step 2 (.run (.close 76))))) (.step 5 (.step 10 (.step 76 (.step 43 (.step 24 (.run (.close 72)))))))))))))) (.step 3 (.step 31 (.step 21 (.step 2 (.step 9 (.step 61 (.step 74 (.step 4 (.step 15 (.run (.close 22)))))))))))) (.step 2 (.step 63 (.step 24 (.step 4 (.step 57 (.run (.close 15))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part769
namespace Part770
def root : Box := ⟨1645504557321206043582216875263310386041021835083075001878839296, 5794876648660911881550947082958932494571828338482925641025109898990105749763183079679082155361612309181008432441558452032600872011646535180469617658752697102596249437581445397056147870044359917578777433574159256437748925441⟩
def references : Fin 1 → Box := ![Part769.root]
def proof : Enumeration.Proof 1 := (.split 50 0 (.split 59 0 (.split 15 1 (.split 22 0 (.split 36 0 (.split 42 0 (.split 55 0 (.split 68 0 (.reuse 0) (.step 63 (.step 18 (.step 24 (.step 21 (.step 4 (.run (.close 2)))))))) (.step 63 (.step 18 (.step 24 (.step 21 (.step 4 (.run (.close 2)))))))) (.step 68 (.step 18 (.step 24 (.run (.close 3)))))) (.step 68 (.step 18 (.step 24 (.run (.close 3)))))) (.step 18 (.step 24 (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.step 3 (.run (.close 2))))))))))) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.step 2 (.run (.close 76))) (.step 5 (.step 2 (.run (.close 7))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 24 (.step 21 (.step 2 (.run (.close 3))))))) (.step 3 (.step 18 (.step 24 (.step 21 (.step 2 (.step 10 (.step 16 (.run (.close 22)))))))))) (.step 3 (.step 18 (.step 24 (.step 21 (.step 2 (.step 9 (.step 15 (.run (.close 22)))))))))))) (.step 3 (.step 18 (.step 23 (.step 21 (.step 27 (.step 23 (.step 9 (.step 61 (.run (.close 26))))))))))) (.step 3 (.step 18 (.step 23 (.step 21 (.step 22 (.step 26 (.step 27 (.step 40 (.step 15 (.step 2 (.step 57 (.step 2 (.run (.close 61)))))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part769.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part770
namespace Part771
def root : Box := ⟨1427247692705959881058285969449495138530230272, 5794887679965438090546899933839123354270966216145824413436713630539886635343492249294806971927603135232667249977419685089297836993597707059548158981730208973717943082671473643193248285429038114634313137965190375393767457793⟩
def references : Fin 2 → Box := ![Part768.root, Part770.root]
def proof : Enumeration.Proof 2 := (.split 21 0 (.reuse 0) (.step 3 (.step 18 (.step 31 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 49 0 (.reuse 1) (.step 3 (.step 26 (.split 12 0 (.split 18 0 (.split 19 0 (.split 54 0 (.split 15 1 (.split 21 1 (.step 2 (.step 48 (.run (.close 2)))) (.step 23 (.run (.close 18)))) (.step 18 (.run (.close 2)))) (.step 55 (.step 23 (.step 2 (.step 57 (.step 2 (.run (.close 18)))))))) (.step 18 (.step 27 (.step 61 (.step 2 (.run (.close 22))))))) (.step 18 (.step 23 (.step 9 (.step 42 (.step 21 (.run (.close 61)))))))) (.step 4 (.step 55 (.step 23 (.step 57 (.step 18 (.step 15 (.run (.close 12)))))))))))) (.step 68 (.step 3 (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.split 13 0 (.step 2 (.step 43 (.run (.close 2)))) (.step 49 (.step 76 (.step 43 (.run (.close 2)))))))))))))) (.step 3 (.step 18 (.step 31 (.step 24 (.step 21 (.step 22 (.step 26 (.step 32 (.step 43 (.split 13 0 (.step 2 (.run (.close 60))) (.step 76 (.step 43 (.step 16 (.step 2 (.run (.close 60))))))))))))))))) (.step 68 (.step 55 (.step 18 (.step 3 (.step 21 (.step 22 (.step 2 (.run (.close 26)))))))))) (.step 55 (.step 18 (.step 31 (.step 43 (.step 31 (.step 21 (.step 22 (.step 26 (.split 12 0 (.step 2 (.run (.close 57))) (.step 40 (.step 57 (.step 2 (.step 15 (.step 2 (.run (.close 74)))))))))))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part768.covered
  · exact Part770.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
def root : Box := ⟨2239744742177804210557442280568444278121645497234649534901416348656497831061219231350326988410137346048, 5794876648660911881546048199648275152134880488081524001420587667207480531849967178479190941486270830094493171073452351957224618249072625537880978400569612929364340219764056142962917072066786360601306345822612429311958844417⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 50 0 (.split 54 0 (.split 59 0 (.split 13 0 (.split 61 0 (.split 62 0 (.split 69 0 (.split 73 0 (.split 15 1 (.step 2 (.step 21 (.step 2 (.run (.close 4))))) (.step 18 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 31))))) (.step 3 (.step 2 (.run (.close 3))))) (.step 3 (.step 31 (.step 2 (.run (.close 3)))))) (.step 3 (.step 21 (.step 22 (.step 26 (.split 5 0 (.split 11 0 (.split 34 1 (.split 37 0 (.split 45 0 (.split 53 0 (.step 3 (.step 18 (.step 68 (.run (.close 3))))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 68)))) (.step 2 (.run (.close 43)))) (.step 43 (.run (.close 18)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 10))))))))) (.step 3 (.step 21 (.step 22 (.step 26 (.split 61 0 (.split 34 1 (.split 69 0 (.step 2 (.run (.close 76))) (.step 43 (.step 68 (.run (.close 16))))) (.step 18 (.run (.close 2)))) (.step 43 (.step 49 (.run (.close 16)))))))))) (.step 18 (.step 3 (.step 2 (.run (.close 3)))))) (.step 31 (.step 3 (.step 31 (.run (.close 2)))))) (.step 3 (.step 18 (.step 31 (.step 2 (.run (.close 3)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part772
namespace Part773
def root : Box := ⟨2239744742177804210557442280568444278121645497234649534901416348656497831061219231350326988410137346048, 5794876648660911881555845966269589837008776188884327288177556980415813672165901483886558303160660324856524625439722970428993338317374866038497815649826842249855888690447459316320078694355948632383061038405465689513538880513⟩
def references : Fin 1 → Box := ![Part772.root]
def proof : Enumeration.Proof 1 := (.split 56 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 12 0 (.split 49 0 (.reuse 0) (.step 3 (.step 18 (.step 31 (.step 21 (.step 22 (.step 26 (.split 4 0 (.split 7 0 (.split 8 0 (.split 14 0 (.split 25 0 (.split 34 1 (.step 3 (.split 40 0 (.split 57 0 (.split 60 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 74 0 (.step 3 (.step 55 (.run (.close 52)))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 15)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 40))))) (.step 40 (.run (.close 18)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 18))))))))))) (.step 3 (.step 21 (.step 22 (.step 26 (.split 13 0 (.split 61 0 (.step 31 (.split 49 0 (.split 34 1 (.split 62 0 (.step 3 (.split 59 0 (.step 2 (.run (.close 3))) (.step 40 (.step 55 (.run (.close 15)))))) (.step 58 (.run (.close 31)))) (.step 18 (.run (.close 31)))) (.step 40 (.step 29 (.step 55 (.step 9 (.step 15 (.run (.close 7))))))))) (.step 58 (.step 55 (.step 5 (.step 16 (.step 15 (.run (.close 71)))))))) (.step 3 (.run (.close 31))))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.step 21 (.step 68 (.step 22 (.step 3 (.run (.close 7))))))))) (.step 3 (.step 18 (.step 21 (.step 68 (.step 9 (.step 10 (.step 18 (.run (.close 2)))))))))) (.step 18 (.step 31 (.step 3 (.step 18 (.step 31 (.run (.close 2))))))))
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
def root : Box := ⟨2239744742177804210557442280568444278121645497234649534901416348656497831061219231350326988410137346048, 5794887679965438085530443423726004698836367405110545458402262774954606104563676332318198560480669627844196627651283466327365509586884558406718814446939514399600810031479252513451201728086436392577228730010693026279974765569⟩
def references : Fin 1 → Box := ![Part773.root]
def proof : Enumeration.Proof 1 := (.split 42 0 (.split 22 0 (.split 35 0 (.split 72 0 (.split 38 0 (.reuse 0) (.step 31 (.step 21 (.step 18 (.step 31 (.split 13 0 (.split 19 0 (.split 23 0 (.split 73 0 (.step 3 (.step 2 (.run (.close 7)))) (.step 18 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 31))))) (.step 31 (.run (.close 2)))) (.step 18 (.step 28 (.run (.close 31)))))))))) (.step 18 (.step 31 (.step 3 (.step 18 (.step 31 (.run (.close 2)))))))) (.step 31 (.step 21 (.step 18 (.step 31 (.split 12 0 (.split 19 0 (.split 23 0 (.split 54 0 (.step 3 (.step 29 (.run (.close 31)))) (.step 18 (.run (.close 31)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 18 (.step 29 (.run (.close 31)))))))))) (.split 12 0 (.split 13 0 (.split 35 0 (.split 38 0 (.step 3 (.step 31 (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 24 (.run (.close 7)))) (.step 24 (.run (.close 3))))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 31)))) (.step 55 (.run (.close 31))))) (.step 31 (.step 26 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 35 0 (.split 38 0 (.split 43 0 (.step 18 (.split 49 0 (.step 31 (.step 2 (.run (.close 76)))) (.step 40 (.run (.close 18))))) (.step 43 (.step 7 (.run (.close 2))))) (.step 18 (.step 28 (.run (.close 31))))) (.step 18 (.step 29 (.step 31 (.run (.close 38)))))) (.step 40 (.run (.close 18)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 18 (.run (.close 31)))) (.step 18 (.run (.close 31)))))))
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
def root : Box := ⟨2037035976334486086268445688409378161051468395093183943342100330412667269212831844713627648, 5794887679965438085530443423726004698836367405110545458402262774954599400659711361019648773462625185532891258249216341757910990914938289024789928934145802636356011726006960118429513343426418897979427206640684352666675971073⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 67 0 (.split 22 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 12 0 (.split 13 0 (.split 54 0 (.split 49 0 (.split 56 0 (.split 50 0 (.split 59 0 (.split 61 0 (.split 62 0 (.step 3 (.split 4 0 (.step 32 (.split 15 1 (.split 21 0 (.split 55 0 (.step 2 (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 4))))) (.step 3 (.step 18 (.run (.close 2)))))) (.step 2 (.run (.close 3))))) (.step 3 (.step 2 (.run (.close 3))))) (.step 3 (.split 18 0 (.split 19 0 (.step 2 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.step 2 (.run (.close 3)))))) (.step 3 (.step 18 (.step 2 (.run (.close 31)))))) (.step 3 (.step 31 (.step 3 (.run (.close 2)))))) (.split 49 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 2))))) (.step 3 (.split 61 0 (.split 62 0 (.step 31 (.step 22 (.step 26 (.split 69 0 (.step 2 (.run (.close 31))) (.step 3 (.run (.close 2))))))) (.step 3 (.run (.close 18)))) (.step 3 (.step 76 (.step 16 (.run (.close 18)))))))) (.split 49 0 (.split 50 0 (.step 3 (.step 2 (.step 57 (.step 2 (.run (.close 15)))))) (.step 3 (.run (.close 2)))) (.step 3 (.step 9 (.run (.close 53)))))) (.step 3 (.step 32 (.step 18 (.run (.close 2)))))) (.step 3 (.step 18 (.step 31 (.run (.close 2)))))) (.step 3 (.step 31 (.step 32 (.step 18 (.run (.close 2))))))) (.step 3 (.step 18 (.step 31 (.step 3 (.run (.close 2))))))) (.step 18 (.step 3 (.step 31 (.run (.close 2)))))) (.step 3 (.step 18 (.step 3 (.run (.close 2))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part775
namespace Part776
def root : Box := ⟨1427247692705959881058285969449495138530230272, 5794887679965438090546899933839123354270966216145824413436713630539886635343492249294806971927603135232667249977419685093777326477957389552615712515039634421338052833462875649780558359857894137893343791326472035349348484097⟩
def references : Fin 3 → Box := ![Part771.root, Part774.root, Part775.root]
def proof : Enumeration.Proof 3 := (.split 30 0 (.split 34 0 (.reuse 0) (.step 18 (.split 36 0 (.reuse 1) (.step 31 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 35 0 (.split 38 0 (.split 42 0 (.split 43 0 (.step 18 (.split 49 0 (.step 31 (.step 2 (.run (.close 76)))) (.step 40 (.run (.close 18))))) (.step 10 (.step 43 (.step 29 (.run (.close 7)))))) (.step 7 (.step 18 (.step 31 (.run (.close 28)))))) (.step 31 (.step 7 (.step 28 (.step 59 (.run (.close 41))))))) (.step 31 (.step 29 (.step 7 (.step 75 (.step 41 (.run (.close 38)))))))) (.step 31 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 18 (.run (.close 31)))) (.step 18 (.run (.close 31)))))))) (.step 18 (.split 43 0 (.split 34 0 (.split 36 0 (.split 51 0 (.reuse 2) (.split 18 0 (.split 19 0 (.step 18 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))) (.step 3 (.step 18 (.step 31 (.step 3 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))))))) (.step 3 (.step 18 (.step 31 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))))) (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part771.covered
  · exact Part774.covered
  · exact Part775.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part776
namespace Part777
def root : Box := ⟨1606938044258991702789654798301043660808172443277931365531648, 5794876648660901607848014371291926155802800256036645319508435919003399526997488309798583696364941228138853749621174972207752881389359196397140652045518938645038142373393501622925007056355715832523283623902829083354117178369⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 55 0 (.split 68 0 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 20 1 (.split 23 0 (.split 43 0 (.split 49 0 (.step 2 (.run (.close 4))) (.step 63 (.step 3 (.run (.close 2))))) (.step 27 (.step 2 (.run (.close 48))))) (.step 26 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 57))))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 26 (.split 49 0 (.split 50 0 (.split 59 0 (.split 43 0 (.step 2 (.run (.close 3))) (.step 9 (.step 2 (.run (.close 3))))) (.step 3 (.run (.close 2)))) (.step 61 (.step 23 (.step 3 (.run (.close 2)))))) (.step 61 (.step 23 (.step 3 (.step 2 (.step 61 (.step 2 (.run (.close 22))))))))))) (.step 21 (.step 22 (.step 26 (.split 49 0 (.split 59 0 (.split 43 0 (.split 51 0 (.split 54 0 (.step 2 (.run (.close 73))) (.step 3 (.run (.close 2)))) (.step 24 (.step 23 (.run (.close 3))))) (.step 24 (.step 23 (.run (.close 3))))) (.step 23 (.step 3 (.step 2 (.run (.close 57)))))) (.step 23 (.step 3 (.step 40 (.step 18 (.step 23 (.step 9 (.step 57 (.step 42 (.run (.close 21))))))))))))))) (.step 3 (.step 31 (.step 21 (.step 2 (.step 10 (.step 60 (.step 73 (.step 5 (.step 16 (.run (.close 22)))))))))))) (.step 3 (.step 21 (.step 22 (.step 26 (.step 12 (.split 50 0 (.step 2 (.step 61 (.step 2 (.run (.close 57))))) (.step 4 (.step 9 (.step 57 (.step 40 (.step 23 (.run (.close 62)))))))))))))) (.step 48 (.step 5 (.step 18 (.step 24 (.step 21 (.step 4 (.run (.close 2))))))))) (.step 48 (.step 5 (.step 18 (.step 24 (.step 21 (.step 4 (.run (.close 2)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part777
namespace Part778
def root : Box := ⟨1606938044258991702789654798301043660808172443277931365531648, 5794876648660911881550947082958932494563330130597857367446076487685266251732302930826496796680290714096418380077957945147191877634542261309613926474730345800165503651967501953392972257276790627087291222652970188940636062721⟩
def references : Fin 1 → Box := ![Part777.root]
def proof : Enumeration.Proof 1 := (.split 62 0 (.split 69 0 (.split 15 1 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 53 0 (.reuse 0) (.step 2 (.step 48 (.step 23 (.step 5 (.step 76 (.run (.close 16)))))))) (.step 55 (.step 18 (.step 24 (.run (.close 3)))))) (.step 55 (.step 18 (.step 24 (.run (.close 3)))))) (.step 55 (.step 18 (.step 24 (.run (.close 3)))))) (.step 3 (.step 2 (.step 24 (.run (.close 18)))))) (.step 18 (.step 23 (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.step 3 (.run (.close 2))))))))))) (.step 18 (.step 23 (.step 21 (.step 22 (.step 26 (.split 12 0 (.step 4 (.step 2 (.run (.close 76)))) (.step 5 (.step 2 (.step 4 (.run (.close 2)))))))))))) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 49 0 (.step 2 (.run (.close 57))) (.step 63 (.step 2 (.run (.close 18))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 24 (.step 21 (.step 2 (.run (.close 3))))))) (.step 3 (.step 18 (.step 24 (.step 21 (.step 2 (.step 10 (.step 16 (.run (.close 22)))))))))) (.step 3 (.step 18 (.step 24 (.step 21 (.step 2 (.step 9 (.step 15 (.run (.close 22)))))))))))) (.step 3 (.step 18 (.step 24 (.step 21 (.step 30 (.step 24 (.step 10 (.step 73 (.run (.close 22))))))))))) (.step 3 (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.step 30 (.step 43 (.step 16 (.step 2 (.step 73 (.step 2 (.run (.close 76)))))))))))))))
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
def root : Box := ⟨1427247692705959881058285969449495138530230272, 5794887679965438090546899933839123354270966216145824413436713630539886635343492249294806971927603135232667249977419685093777326477957389552615712515039634421338056047338964167761109443782078820218548835732459600935019086849⟩
def references : Fin 2 → Box := ![Part776.root, Part778.root]
def proof : Enumeration.Proof 2 := (.split 20 0 (.reuse 0) (.step 3 (.step 18 (.step 31 (.split 38 0 (.split 56 0 (.split 35 0 (.split 72 0 (.split 61 0 (.reuse 1) (.step 3 (.step 26 (.split 13 0 (.split 18 0 (.split 19 0 (.split 73 0 (.split 15 1 (.split 20 1 (.split 21 0 (.step 2 (.step 63 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 18 (.run (.close 2)))) (.step 63 (.step 68 (.step 73 (.step 24 (.step 2 (.run (.close 76)))))))) (.step 18 (.step 24 (.step 76 (.step 2 (.run (.close 22))))))) (.step 18 (.step 24 (.step 10 (.step 35 (.step 76 (.step 21 (.run (.close 73))))))))) (.step 5 (.step 68 (.step 24 (.step 76 (.step 18 (.step 16 (.run (.close 12)))))))))))) (.step 55 (.step 3 (.step 18 (.step 23 (.step 21 (.step 22 (.step 26 (.split 12 0 (.step 2 (.step 40 (.run (.close 2)))) (.step 40 (.step 2 (.run (.close 57))))))))))))) (.step 3 (.step 18 (.step 31 (.step 23 (.step 21 (.step 22 (.step 26 (.step 32 (.step 40 (.split 12 0 (.step 2 (.run (.close 57))) (.step 57 (.step 40 (.step 15 (.step 2 (.run (.close 74))))))))))))))))) (.step 68 (.step 55 (.step 18 (.step 3 (.step 21 (.step 22 (.step 2 (.run (.close 60)))))))))) (.step 68 (.step 18 (.step 31 (.step 40 (.step 18 (.step 31 (.step 21 (.step 22 (.step 26 (.split 13 0 (.step 2 (.run (.close 60))) (.step 49 (.step 76 (.step 2 (.step 43 (.step 16 (.step 2 (.run (.close 60)))))))))))))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part776.covered
  · exact Part778.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part779
namespace Part780
def root : Box := ⟨1496579103874537294200454326987443261622813454237696, 5794876648660911881546048199648275152126382272091933132370864883808094418494113349732090643340190759924070187630338351691952726324962782378984173539167173302638467039156517263541023442796170070097244493561759987101852500993⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 62 0 (.split 69 0 (.split 15 1 (.split 17 1 (.split 20 0 (.split 21 0 (.split 55 0 (.split 68 0 (.split 13 0 (.split 12 0 (.step 2 (.run (.close 3))) (.step 3 (.step 2 (.run (.close 22))))) (.step 3 (.step 2 (.run (.close 22))))) (.step 18 (.step 22 (.split 12 0 (.split 13 0 (.step 2 (.run (.close 4))) (.step 5 (.step 2 (.step 60 (.step 2 (.run (.close 4))))))) (.step 27 (.step 40 (.run (.close 4)))))))) (.step 18 (.step 22 (.split 12 0 (.split 13 0 (.step 2 (.run (.close 4))) (.step 5 (.step 2 (.step 60 (.step 2 (.run (.close 4))))))) (.step 27 (.step 40 (.run (.close 4)))))))) (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.step 3 (.run (.close 2))))))))) (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.step 3 (.run (.close 2))))))))) (.step 18 (.step 22 (.run (.close 2))))) (.step 18 (.step 22 (.split 12 0 (.split 13 0 (.step 2 (.run (.close 3))) (.step 3 (.step 2 (.step 10 (.step 60 (.step 73 (.step 16 (.run (.close 21))))))))) (.step 3 (.step 2 (.step 9 (.step 24 (.step 15 (.run (.close 21))))))))))) (.step 3 (.step 18 (.step 22 (.run (.close 2)))))) (.step 3 (.step 18 (.step 22 (.split 13 0 (.split 18 0 (.step 2 (.run (.close 73))) (.step 24 (.run (.close 21)))) (.step 24 (.step 10 (.step 16 (.run (.close 65))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part780
namespace Part781
def root : Box := ⟨1496579103874537294200454326987443261622813454237696, 5794876648660911881555845966269589837008776188884327280629632130772730967682792321910020521321272544635402138968153541564979356641848679294377847583031459449446606625777266453044611216021769291014228148006129510156268995585⟩
def references : Fin 1 → Box := ![Part780.root]
def proof : Enumeration.Proof 1 := (.split 51 0 (.split 67 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.reuse 0) (.step 3 (.step 22 (.split 13 0 (.split 18 0 (.split 23 0 (.split 73 0 (.split 15 1 (.split 17 1 (.split 20 0 (.step 2 (.step 63 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 24 (.step 2 (.run (.close 61))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 76))))) (.step 18 (.step 73 (.step 2 (.run (.close 22)))))) (.step 18 (.step 24 (.step 10 (.step 35 (.step 21 (.run (.close 73)))))))) (.step 30 (.step 24 (.step 76 (.step 18 (.step 16 (.run (.close 12))))))))))) (.step 18 (.step 3 (.step 18 (.step 22 (.split 12 0 (.step 2 (.run (.close 57))) (.step 27 (.step 40 (.step 57 (.step 2 (.run (.close 26)))))))))))) (.step 3 (.step 31 (.step 18 (.step 22 (.split 12 0 (.split 18 0 (.step 2 (.run (.close 57))) (.step 23 (.run (.close 21)))) (.step 23 (.step 57 (.step 15 (.run (.close 53))))))))))) (.step 3 (.step 31 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.step 31 (.split 15 1 (.split 17 1 (.step 2 (.step 48 (.run (.close 2)))) (.step 23 (.step 2 (.run (.close 60))))) (.step 18 (.run (.close 2))))) (.step 27 (.step 23 (.step 4 (.step 2 (.run (.close 18))))))) (.step 18 (.step 2 (.run (.close 26))))) (.step 18 (.step 23 (.run (.close 22))))) (.step 18 (.step 23 (.step 42 (.step 9 (.step 21 (.step 57 (.run (.close 22))))))))) (.step 27 (.step 23 (.step 9 (.step 57 (.step 18 (.run (.close 12))))))))))) (.step 3 (.step 18 (.step 31 (.run (.close 2)))))) (.step 3 (.step 18 (.step 31 (.step 22 (.step 36 (.step 18 (.run (.close 7)))))))))
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
def root : Box := ⟨1496579103874537294200454326987443261622813454237696, 5794887679965438085530443423726004698836367405110545458402262774954606104563676332318198560480669627844196627651283466322886020102528949985603929885802625839987527310554170721463475435932667638321403711581984517741492569089⟩
def references : Fin 1 → Box := ![Part781.root]
def proof : Enumeration.Proof 1 := (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 43 0 (.reuse 0) (.step 3 (.step 30 (.step 27 (.step 18 (.step 31 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 68 (.step 18 (.step 22 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 68 (.step 18 (.step 31 (.step 22 (.split 13 0 (.split 18 0 (.step 2 (.run (.close 60))) (.step 24 (.run (.close 21)))) (.step 24 (.step 10 (.step 16 (.step 28 (.run (.close 41)))))))))))))) (.step 18 (.step 55 (.step 3 (.step 18 (.step 22 (.split 12 0 (.step 2 (.run (.close 57))) (.step 40 (.step 66 (.step 57 (.step 2 (.run (.close 26))))))))))))) (.step 18 (.step 55 (.step 3 (.step 18 (.step 31 (.step 22 (.split 12 0 (.split 18 0 (.step 2 (.run (.close 57))) (.step 23 (.run (.close 21)))) (.step 23 (.step 9 (.step 57 (.step 15 (.run (.close 38)))))))))))))) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 38 0 (.step 3 (.step 31 (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 24 (.run (.close 7)))) (.step 24 (.run (.close 3))))))) (.step 60 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 24 (.step 23 (.step 4 (.step 10 (.step 3 (.run (.close 60)))))))) (.step 55 (.run (.close 31))))))
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
def root : Box := ⟨1496579103874537294200454326987443261622813454237696, 5794887679965438085530443423726004698836367405110545458402262774954606104563676332318198560480669627844196627651288163412531057253344411439865062093166802652705453701086987309993849928411752878467361762940035715103137465345⟩
def references : Fin 1 → Box := ![Part782.root]
def proof : Enumeration.Proof 1 := (.split 30 0 (.split 34 0 (.split 36 0 (.reuse 0) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 38 0 (.split 42 0 (.step 3 (.step 31 (.step 18 (.split 18 0 (.step 36 (.split 19 0 (.step 18 (.run (.close 7))) (.step 24 (.run (.close 7))))) (.step 24 (.run (.close 3))))))) (.step 7 (.step 3 (.run (.close 43))))) (.step 3 (.run (.close 7)))) (.step 74 (.step 7 (.step 3 (.run (.close 2)))))) (.step 24 (.step 23 (.run (.close 22))))) (.step 24 (.step 23 (.run (.close 22))))))) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.step 31 (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 24 (.run (.close 7)))) (.step 24 (.run (.close 3))))))) (.step 7 (.step 3 (.run (.close 43))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 49 (.step 7 (.step 24 (.step 23 (.step 4 (.step 10 (.step 76 (.run (.close 31)))))))))) (.step 66 (.step 7 (.step 24 (.step 23 (.step 4 (.step 9 (.step 3 (.run (.close 57)))))))))))) (.step 18 (.step 3 (.step 31 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))))))
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
def root : Box := ⟨1462928885023608878084743118685732514794462773248, 5794876648660911881546048199648275152126382272091933132370864883808094418494113349732090643340190759924070187630338351691952726324962782378984173539167173302638467039156514273308673463768799425358076756046701771063869572097⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 62 0 (.split 69 0 (.split 15 1 (.split 16 1 (.split 20 0 (.split 21 0 (.split 55 0 (.split 68 0 (.split 13 0 (.split 12 0 (.step 2 (.run (.close 3))) (.step 3 (.step 2 (.run (.close 21))))) (.step 3 (.step 2 (.run (.close 21))))) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.step 2 (.run (.close 60))) (.step 4 (.step 2 (.run (.close 21))))) (.step 30 (.step 43 (.step 10 (.step 4 (.step 60 (.run (.close 21)))))))) (.step 27 (.step 40 (.step 4 (.run (.close 2)))))))) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.step 2 (.run (.close 60))) (.step 4 (.step 2 (.run (.close 21))))) (.step 30 (.step 43 (.step 10 (.step 4 (.step 60 (.run (.close 21)))))))) (.step 27 (.step 40 (.step 4 (.run (.close 2)))))))) (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.step 3 (.run (.close 2))))))))) (.step 18 (.step 24 (.step 21 (.step 22 (.step 26 (.step 3 (.run (.close 2))))))))) (.step 18 (.step 21 (.run (.close 2))))) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.step 2 (.run (.close 4))) (.step 21 (.run (.close 2)))) (.step 3 (.step 21 (.step 2 (.step 10 (.step 60 (.step 73 (.step 16 (.run (.close 21)))))))))) (.step 3 (.step 21 (.step 2 (.step 9 (.step 61 (.step 74 (.step 15 (.run (.close 21)))))))))))) (.step 3 (.step 18 (.step 21 (.split 13 0 (.step 2 (.run (.close 73))) (.step 30 (.step 43 (.step 76 (.step 2 (.run (.close 22))))))))))) (.step 3 (.step 18 (.step 21 (.step 2 (.run (.close 73)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part784
namespace Part785
def root : Box := ⟨1462928885023608878084743118685732514794462773248, 5794876648660911881555845966269589837008776188884327288177556980415813672165901483886558303160660324856524625439722970424513848833019257617382931088689953693612599302916204508433379309052263067592711335279270525075025036289⟩
def references : Fin 1 → Box := ![Part784.root]
def proof : Enumeration.Proof 1 := (.split 56 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.reuse 0) (.step 3 (.step 21 (.split 13 0 (.split 19 0 (.split 23 0 (.split 73 0 (.split 15 1 (.split 16 1 (.split 20 0 (.step 2 (.step 63 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 24 (.step 2 (.run (.close 74))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 76))))) (.step 18 (.step 73 (.step 2 (.run (.close 21)))))) (.step 18 (.step 21 (.step 2 (.run (.close 73)))))) (.step 18 (.step 21 (.run (.close 12)))))))) (.step 18 (.step 3 (.step 18 (.step 21 (.split 12 0 (.step 2 (.run (.close 57))) (.step 27 (.step 40 (.step 57 (.step 2 (.run (.close 26)))))))))))) (.step 3 (.step 31 (.step 18 (.step 21 (.step 2 (.run (.close 61)))))))) (.step 3 (.step 31 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.step 31 (.split 15 1 (.split 16 1 (.step 2 (.step 48 (.run (.close 2)))) (.step 23 (.step 2 (.run (.close 60))))) (.step 18 (.run (.close 2))))) (.step 27 (.step 23 (.step 4 (.step 2 (.run (.close 18))))))) (.step 18 (.step 2 (.run (.close 21))))) (.step 18 (.step 23 (.step 61 (.step 2 (.run (.close 21))))))) (.step 18 (.step 23 (.run (.close 21))))) (.step 18 (.step 21 (.run (.close 12)))))))) (.step 3 (.step 18 (.step 31 (.run (.close 2)))))) (.step 3 (.step 36 (.step 31 (.step 18 (.split 49 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 7))))))))) (.step 3 (.step 30 (.step 27 (.step 18 (.step 31 (.run (.close 2)))))))) (.step 3 (.step 18 (.step 68 (.step 18 (.step 21 (.split 13 0 (.step 2 (.run (.close 60))) (.step 43 (.step 49 (.step 76 (.step 2 (.run (.close 22)))))))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part784.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part785
namespace Part786
def root : Box := ⟨1462928885023608878084743118685732514794462773248, 5794887679965438085530443423726004698836367405110545458402262774954606104563676332318198560480669627844196627651288163408051567768984728946797508559857377205085343950295582313174189874955526210469163372063695839109573510145⟩
def references : Fin 1 → Box := ![Part785.root]
def proof : Enumeration.Proof 1 := (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.reuse 0) (.step 3 (.step 18 (.step 68 (.step 18 (.step 31 (.step 21 (.step 2 (.run (.close 60)))))))))) (.step 18 (.step 55 (.step 3 (.step 18 (.step 21 (.split 12 0 (.step 2 (.run (.close 57))) (.step 40 (.step 66 (.step 57 (.step 2 (.run (.close 26))))))))))))) (.step 18 (.step 55 (.step 3 (.step 18 (.step 31 (.step 21 (.step 2 (.run (.close 74)))))))))) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 38 0 (.step 3 (.step 31 (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 24 (.run (.close 7)))) (.step 24 (.run (.close 3))))))) (.step 60 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 24 (.step 23 (.step 4 (.step 10 (.step 3 (.run (.close 60)))))))) (.step 55 (.run (.close 31)))))) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 38 0 (.split 42 0 (.step 3 (.step 31 (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 24 (.run (.close 7)))) (.step 24 (.run (.close 3))))))) (.step 7 (.step 3 (.run (.close 43))))) (.step 3 (.run (.close 7)))) (.step 74 (.step 7 (.step 3 (.run (.close 2)))))) (.step 24 (.step 23 (.step 4 (.step 10 (.step 76 (.step 3 (.run (.close 7))))))))) (.step 3 (.run (.close 18))))))
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
def root : Box := ⟨1462928885023608878084743118685732514794462773248, 5794887679965438085530443423726004698836367405110545458402262774954606104563676332318198560480669627844196627651288163412531057253344411439865062093166802656075447034480814294094876835261836067932837078242549059203105817601⟩
def references : Fin 1 → Box := ![Part786.root]
def proof : Enumeration.Proof 1 := (.split 22 0 (.split 30 0 (.split 34 0 (.reuse 0) (.step 18 (.split 12 0 (.split 13 0 (.split 35 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 3 (.step 31 (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 24 (.run (.close 7)))) (.step 24 (.run (.close 3))))))) (.step 7 (.step 3 (.run (.close 43))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 49 (.step 7 (.step 24 (.step 23 (.step 4 (.step 10 (.step 76 (.run (.close 31)))))))))) (.step 66 (.step 7 (.step 24 (.step 23 (.step 4 (.step 9 (.step 3 (.run (.close 57)))))))))))) (.step 18 (.step 3 (.step 31 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))))) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 31 (.split 49 0 (.step 18 (.step 24 (.split 61 0 (.step 18 (.run (.close 2))) (.step 18 (.run (.close 2)))))) (.step 18 (.run (.close 2))))) (.step 30 (.step 73 (.step 11 (.step 8 (.step 11 (.step 2 (.run (.close 7))))))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 18 (.step 7 (.run (.close 2))))) (.step 24 (.step 23 (.step 3 (.step 2 (.run (.close 3))))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 21 (.run (.close 2))))) (.step 3 (.step 18 (.step 21 (.step 2 (.run (.close 26))))))) (.step 3 (.step 18 (.step 21 (.step 2 (.run (.close 26)))))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part786.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part787
namespace Part788
def root : Box := ⟨1462928885023608878084743118685732514794462773248, 5794887679965438090546899933839123354270966216145824413436713630539886635343492249294806971927603135232667249977419685093777326477957389552615712515039634421338056047338967163839465972133061137772455904112649895596732187649⟩
def references : Fin 1 → Box := ![Part787.root]
def proof : Enumeration.Proof 1 := (.step 18 (.split 17 0 (.reuse 0) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 31 (.split 49 0 (.step 18 (.step 24 (.split 61 0 (.step 18 (.run (.close 2))) (.step 18 (.run (.close 2)))))) (.step 18 (.run (.close 2))))) (.step 27 (.step 61 (.step 8 (.step 11 (.step 8 (.step 2 (.run (.close 7))))))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 18 (.step 7 (.run (.close 2))))) (.step 24 (.step 23 (.step 3 (.step 2 (.run (.close 3))))))) (.step 7 (.step 18 (.step 25 (.step 2 (.run (.close 7))))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 21 (.run (.close 2))))) (.step 3 (.step 18 (.step 21 (.step 2 (.run (.close 22))))))) (.step 3 (.step 18 (.step 21 (.step 2 (.run (.close 22))))))))))
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
def root : Box := ⟨1427247692705961148708886197678896635233435648, 5794887679965438085530443423726004698836367405110545458402262774954606104563676332318198560475124288455954997932126637954599852695656075834852296735461666682128278028336746456561550255912665837720028139985583481865053930497⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 51 0 (.split 67 0 (.split 22 0 (.split 42 0 (.split 35 0 (.split 72 0 (.split 38 0 (.split 56 0 (.split 12 0 (.split 13 0 (.split 54 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 61 0 (.split 62 0 (.step 3 (.split 4 0 (.step 12 (.split 15 1 (.split 20 0 (.split 21 0 (.split 55 0 (.step 2 (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 4))))) (.step 3 (.step 2 (.step 24 (.run (.close 4)))))) (.step 3 (.step 18 (.run (.close 2)))))) (.step 2 (.run (.close 3))))) (.step 3 (.step 2 (.run (.close 3))))) (.step 3 (.step 12 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.step 2 (.run (.close 3)))))) (.step 3 (.step 31 (.run (.close 12))))) (.split 49 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 2))))) (.step 3 (.step 12 (.run (.close 16))))) (.step 3 (.step 12 (.run (.close 15))))) (.step 3 (.step 18 (.step 31 (.run (.close 2)))))) (.step 3 (.split 61 0 (.step 18 (.split 13 0 (.step 3 (.step 31 (.run (.close 2)))) (.step 28 (.run (.close 31))))) (.step 3 (.run (.close 18)))))) (.step 3 (.step 18 (.step 31 (.run (.close 2)))))) (.step 3 (.split 49 0 (.step 18 (.split 12 0 (.step 3 (.step 31 (.run (.close 2)))) (.step 29 (.run (.close 31))))) (.step 3 (.run (.close 18)))))) (.step 3 (.step 18 (.step 31 (.step 3 (.run (.close 2))))))) (.step 18 (.step 3 (.step 31 (.run (.close 2)))))) (.step 3 (.step 18 (.step 3 (.run (.close 2)))))) (.step 18 (.step 3 (.split 18 0 (.split 19 0 (.split 22 0 (.step 18 (.step 52 (.step 18 (.step 64 (.step 3 (.run (.close 2))))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part789
namespace Part790
def root : Box := ⟨1427247692705961148708886197678896635233435648, 5794887679965438090546899933839123354270966216145824413436713630539886635343492249294806971927603135232667249977419685093777326477957389552615712515039634421338056047338967163839465972133061140307757104569108698590138598401⟩
def references : Fin 1 → Box := ![Part789.root]
def proof : Enumeration.Proof 1 := (.step 18 (.split 16 0 (.split 17 0 (.split 30 0 (.split 43 0 (.split 34 0 (.split 36 0 (.reuse 0) (.step 3 (.step 18 (.step 31 (.step 3 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))))))) (.step 3 (.step 18 (.step 31 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))))) (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))) (.step 18 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))) (.step 18 (.step 3 (.step 31 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 18 (.step 7 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 24))))))))) (.step 18 (.step 3 (.step 31 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 18 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 18 (.step 7 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 24))))) (.step 18 (.step 7 (.run (.close 2))))))))))
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
def root : Box := ⟨2147483648, 5794887679965438090546899933839123354270966216145824413436713630539886635343492249294806971927603135232667249977419685093777326477957389552615712515039634421338056047338967163839465972133061140307757104569108698590138598401⟩
def references : Fin 5 → Box := ![Part733.root, Part779.root, Part783.root, Part788.root, Part790.root]
def proof : Enumeration.Proof 5 := (.split 15 0 (.reuse 0) (.split 10 0 (.split 16 0 (.split 17 0 (.reuse 1) (.step 18 (.split 22 0 (.reuse 2) (.step 18 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 31 (.split 49 0 (.step 18 (.step 24 (.split 61 0 (.step 18 (.run (.close 2))) (.step 18 (.run (.close 2)))))) (.step 18 (.run (.close 2))))) (.step 27 (.step 61 (.step 73 (.step 8 (.step 11 (.step 2 (.run (.close 7))))))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 18 (.step 7 (.run (.close 2))))) (.step 24 (.step 23 (.step 3 (.step 2 (.run (.close 3))))))) (.step 18 (.step 2 (.run (.close 4))))) (.step 18 (.step 22 (.step 2 (.run (.close 4)))))) (.step 3 (.step 18 (.step 22 (.step 2 (.run (.close 76))))))) (.step 3 (.step 18 (.step 22 (.step 2 (.run (.close 57))))))))))) (.reuse 3)) (.reuse 4)))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part733.covered
  · exact Part779.covered
  · exact Part783.covered
  · exact Part788.covered
  · exact Part790.covered
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part791
end FiveColour.Packed.EnumerationChunks.Case142
