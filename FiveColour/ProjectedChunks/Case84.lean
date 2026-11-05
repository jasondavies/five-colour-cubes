module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case84
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405634970392459735496868692530956040756468332803841040762245551796284960602347012096⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593704327342179793651, 5789228615357111146520043253955950924962759905236944250816662429627930946143174768881773115736627492968050798482740711356931196351281104609431181736320982633118032348601960626826787145704805298534408245321323047477072364544, 0⟩]
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925664188033770695627336559962463655613398901129254453295620147697437467558653698612971399368019147644861899733919523139269273813194857771368479871065440391258781711600713728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 74 (.split 72 1 (.split 74 1 (.split 2 0 (.split 8 0 (.split 14 0 (.step 3 (.step 31 (.close 3))) (.step 3 (.step 18 (.step 5 (.step 29 (.step 5 (.close 12))))))) (.step 3 (.step 18 (.step 5 (.step 29 (.step 5 (.close 31))))))) (.step 3 (.step 31 (.step 18 (.step 23 (.step 11 (.step 3 (.close 5)))))))) (.split 71 1 (.split 2 0 (.split 16 0 (.step 69 (.step 3 (.step 11 (.step 18 (.step 5 (.close 17)))))) (.step 11 (.step 3 (.close 18)))) (.step 11 (.step 3 (.step 23 (.step 31 (.step 5 (.close 12))))))) (.step 11 (.step 69 (.step 31 (.close 74)))))) (.step 29 (.step 69 (.split 71 1 (.step 75 (.step 3 (.close 5))) (.step 69 (.step 31 (.step 3 (.step 11 (.close 18)))))))))) (.step 3 (.step 69 (.step 3 (.close 7))))) (.step 3 (.step 63 (.step 74 (.split 72 1 (.step 18 (.step 3 (.close 15))) (.step 3 (.step 26 (.step 15 (.close 21))))))))) (.step 3 (.step 67 (.step 69 (.step 67 (.step 75 (.split 65 1 (.split 74 1 (.step 31 (.close 3)) (.step 11 (.step 3 (.step 23 (.step 31 (.close 18)))))) (.step 3 (.step 18 (.step 21 (.step 3 (.step 5 (.step 3 (.close 22)))))))))))))) (.step 66 (.step 3 (.step 69 (.step 66 (.split 65 1 (.step 75 (.step 77 (.step 3 (.step 31 (.step 11 (.step 3 (.step 5 (.step 3 (.step 12 (.close 18)))))))))) (.step 3 (.step 18 (.step 23 (.step 3 (.step 22 (.step 26 (.step 22 (.close 28)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978176018699776613985412130863684895550982818540136923979883584233863197908406122866581925743593805673340220844071190528⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 3 (.step 74 (.split 63 1 (.split 64 1 (.step 3 (.split 65 1 (.step 75 (.split 74 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 8 0 (.split 10 0 (.step 28 (.split 14 0 (.step 59 (.close 3)) (.step 3 (.step 5 (.step 3 (.step 12 (.close 31))))))) (.step 3 (.step 28 (.step 12 (.close 31))))) (.step 3 (.step 5 (.step 3 (.step 28 (.close 31)))))) (.step 5 (.step 3 (.step 28 (.close 31))))) (.step 29 (.step 31 (.close 3)))) (.step 22 (.step 31 (.step 5 (.close 8))))) (.step 5 (.step 8 (.step 12 (.close 18)))))) (.step 5 (.step 10 (.step 18 (.step 22 (.step 28 (.step 15 (.step 26 (.step 15 (.close 31))))))))))) (.step 18 (.step 31 (.step 18 (.step 63 (.step 5 (.step 11 (.close 12)))))))) (.step 18 (.step 31 (.step 12 (.step 63 (.close 66)))))))))) (.run (.step 3 (.step 51 (.step 3 (.close 7)))))) (.run (.step 3 (.step 9 (.step 10 (.step 27 (.step 47 (.step 3 (.close 7))))))))) (.run (.step 7 (.step 31 (.step 75 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.split 71 1 (.step 31 (.step 7 (.step 22 (.close 28)))) (.step 29 (.step 31 (.close 11)))) (.step 29 (.step 31 (.step 11 (.close 67)))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 3 (.step 26 (.close 45)))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943950551163295313665743697413502708453507545732160717077770538728623627560017908352526875666287795321672569978880⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.reuse 0) (.run (.step 3 (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 3 (.split 65 1 (.step 75 (.split 71 1 (.split 74 1 (.split 72 1 (.split 2 0 (.split 8 0 (.split 10 0 (.step 28 (.split 14 0 (.step 41 (.close 3)) (.step 3 (.step 5 (.step 3 (.step 12 (.close 31))))))) (.step 3 (.step 28 (.step 12 (.close 31))))) (.step 3 (.step 5 (.step 3 (.step 28 (.close 31)))))) (.step 5 (.step 3 (.step 28 (.close 31))))) (.step 29 (.step 31 (.close 3)))) (.step 5 (.step 8 (.close 12)))) (.step 31 (.step 5 (.step 8 (.step 11 (.step 12 (.close 18)))))))) (.step 5 (.step 10 (.step 18 (.step 21 (.step 28 (.close 31)))))))) (.step 18 (.step 21 (.step 31 (.close 67))))) (.step 18 (.step 31 (.step 12 (.step 63 (.close 66)))))) (.step 5 (.step 10 (.step 28 (.split 63 1 (.split 64 1 (.step 59 (.step 3 (.step 5 (.step 59 (.step 68 (.step 41 (.step 22 (.step 31 (.close 5))))))))) (.step 5 (.step 18 (.step 21 (.step 31 (.step 5 (.step 41 (.step 5 (.step 12 (.close 67)))))))))) (.step 5 (.step 18 (.step 31 (.step 49 (.step 63 (.close 66))))))))))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 41 (.close 3))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252835458093312342499596338077731736178690388512054074200785744370751913889746383419204321671079330006958080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 38 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 38 1 (.step 75 (.split 42 1 (.split 56 1 (.split 65 1 (.split 74 1 (.split 51 1 (.step 29 (.split 67 1 (.split 2 0 (.split 8 0 (.split 10 0 (.split 16 0 (.split 51 0 (.step 67 (.step 38 (.step 66 (.step 31 (.step 3 (.close 18)))))) (.step 21 (.step 3 (.step 15 (.step 22 (.step 15 (.close 26))))))) (.step 21 (.step 38 (.close 18)))) (.step 31 (.step 38 (.close 3)))) (.step 9 (.step 66 (.step 38 (.step 32 (.step 67 (.step 38 (.step 3 (.close 11))))))))) (.step 31 (.step 32 (.step 3 (.close 11))))) (.step 3 (.close 21)))) (.step 3 (.close 21))) (.step 3 (.step 29 (.step 40 (.step 66 (.step 67 (.step 69 (.step 11 (.step 31 (.step 74 (.step 3 (.step 5 (.close 17))))))))))))) (.step 3 (.step 21 (.step 29 (.close 31))))) (.step 3 (.step 5 (.step 29 (.step 31 (.step 3 (.step 22 (.close 38)))))))) (.step 3 (.step 29 (.step 31 (.step 3 (.step 38 (.close 3)))))))) (.step 3 (.step 5 (.step 31 (.step 28 (.close 38)))))) (.step 3 (.step 29 (.step 31 (.step 38 (.step 3 (.step 22 (.close 39)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405631265045604138008621804865602792331680826342745769642449857682952739285587984384⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 74 (.step 75 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.step 31 (.step 7 (.step 22 (.close 28)))) (.step 29 (.step 31 (.step 11 (.close 67)))))) (.step 3 (.step 29 (.step 31 (.step 11 (.close 66)))))) (.step 3 (.step 5 (.step 22 (.step 28 (.step 31 (.step 3 (.close 39)))))))) (.step 7 (.step 31 (.close 39)))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 39)))))))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.step 38 (.step 66 (.step 75 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 64 1 (.step 7 (.split 71 1 (.step 31 (.step 7 (.step 29 (.step 3 (.step 22 (.close 37)))))) (.step 29 (.step 31 (.step 11 (.close 17)))))) (.step 3 (.step 29 (.step 31 (.step 11 (.step 66 (.step 11 (.close 17)))))))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 37)))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 37)))))) (.step 7 (.step 31 (.close 37))))))))))) (.run (.step 3 (.step 7 (.step 18 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.step 29 (.close 31))))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 29 (.close 31)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405634970392459735496868692530956037833462270548885385491679576090836807993535758336⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 28 (.step 29 (.step 66 (.step 67 (.step 74 (.split 65 1 (.step 29 (.split 74 1 (.split 30 1 (.split 51 1 (.step 29 (.step 3 (.step 47 (.step 3 (.close 18))))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.close 29))) (.step 3 (.step 27 (.step 29 (.step 11 (.step 18 (.step 29 (.step 66 (.step 18 (.close 67))))))))))) (.step 3 (.step 28 (.close 29))))))))))))) (.run (.step 7 (.step 18 (.step 77 (.split 26 1 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.step 29 (.close 67))))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 11 (.step 18 (.step 29 (.step 38 (.step 66 (.step 38 (.close 67))))))))) (.step 3 (.step 18 (.step 29 (.close 66)))))))))) (.run (.step 7 (.step 18 (.step 74 (.step 77 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.split 72 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 11 (.step 18 (.close 29))))))) (.step 3 (.step 11 (.step 18 (.step 29 (.close 66)))))) (.step 3 (.step 11 (.step 18 (.step 29 (.step 38 (.close 66))))))) (.step 3 (.step 18 (.step 29 (.close 66))))) (.step 7 (.step 18 (.step 7 (.close 11)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758320032835933598087636165669219771963862058316698165659873414211687740726299878212593272693004555098185983651641021011292834151649775432561913487667910792091161784954783290943253981865497262554430440332350380479348736⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.step 77 (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.step 27 (.split 36 1 (.split 42 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 74 1 (.split 2 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 11 (.step 3 (.step 5 (.close 17)))) (.step 3 (.step 5 (.step 11 (.close 17))))) (.step 3 (.close 11))) (.step 3 (.step 11 (.step 3 (.step 12 (.step 3 (.close 17))))))) (.step 11 (.step 3 (.step 17 (.close 3))))) (.step 11 (.step 3 (.step 17 (.step 3 (.close 5)))))) (.step 11 (.close 17))) (.step 11 (.step 17 (.step 74 (.close 3))))) (.step 3 (.close 11))) (.step 11 (.step 17 (.step 3 (.step 67 (.close 3)))))) (.step 11 (.step 12 (.step 17 (.step 34 (.close 66)))))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 5 (.step 11 (.step 17 (.step 29 (.step 31 (.close 17)))))))) (.step 3 (.step 5 (.step 11 (.step 17 (.step 29 (.step 31 (.close 17))))))))) (.step 3 (.step 5 (.step 17 (.step 29 (.step 11 (.step 17 (.close 31)))))))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 31 (.step 66 (.step 67 (.step 69 (.step 29 (.step 11 (.step 23 (.step 74 (.step 3 (.step 31 (.close 17))))))))))))) (.step 3 (.step 11 (.step 17 (.step 18 (.step 12 (.step 17 (.step 12 (.close 34)))))))))) (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 31 (.step 5 (.step 11 (.step 12 (.close 17))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405634970392459735496868692530956040756468332803841038226941933488186928350589091840⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 38 1 (.reuse 0) (.run (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 31 (.step 5 (.step 11 (.step 12 (.close 17)))))))))))) (.run (.step 3 (.step 5 (.step 17 (.step 31 (.step 38 (.step 66 (.step 67 (.step 74 (.step 75 (.split 2 0 (.split 16 0 (.step 29 (.step 40 (.step 77 (.split 10 0 (.split 34 0 (.step 11 (.step 38 (.step 3 (.close 17)))) (.step 3 (.step 5 (.step 11 (.step 17 (.close 31)))))) (.step 3 (.step 11 (.close 17))))))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 5 (.step 11 (.step 12 (.close 17))))))))))))))))) (.run (.step 3 (.step 5 (.step 17 (.step 27 (.step 29 (.step 47 (.step 29 (.close 17)))))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.close 3)))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 3 (.close 17))))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 3 (.step 17 (.step 3 (.close 19))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2417851639229261570637824, 11567177732598406499846312727330591355628391050586285927614052719007414723160991772070982803074461970758699362368416790578324682387712717632645108675907238891746777703797704323285805172305532918499587582859835977262317961216⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 10 1 (.step 47 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.step 11 (.step 27 (.split 36 1 (.split 42 1 (.split 51 1 (.split 63 1 (.split 64 1 (.step 3 (.split 71 1 (.split 10 0 (.step 11 (.step 3 (.close 5))) (.step 3 (.close 11))) (.step 11 (.step 3 (.step 5 (.close 29)))))) (.step 11 (.step 3 (.step 5 (.step 29 (.close 31)))))) (.step 11 (.step 9 (.step 29 (.step 5 (.close 31)))))) (.step 3 (.close 11))) (.step 3 (.step 5 (.step 11 (.step 29 (.close 31)))))) (.step 3 (.step 5 (.step 11 (.step 29 (.close 31)))))))) (.step 3 (.step 5 (.step 11 (.step 29 (.step 11 (.close 31))))))) (.step 3 (.close 11))) (.step 3 (.step 8 (.close 11)))) (.step 3 (.step 8 (.close 11)))) (.step 3 (.step 8 (.close 11)))) (.step 11 (.close 5)))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 11 (.step 29 (.step 31 (.step 66 (.step 67 (.step 69 (.step 11 (.step 3 (.step 5 (.close 31))))))))))))) (.step 3 (.step 11 (.step 5 (.close 18))))) (.step 3 (.step 5 (.step 8 (.step 18 (.step 31 (.step 5 (.close 11)))))))) (.step 3 (.step 5 (.step 8 (.step 18 (.step 31 (.step 5 (.close 11)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405634970392459735496868692530956040756468332803841040762245551796284960602344914944⟩
def references : Fin 3 → Box := ![Part5.root, Part7.root, Part8.root]
def proof : Chunks.Proof 3 := (.split 8 1 (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 67 (.step 77 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 29)))))) (.step 3 (.step 11 (.step 18 (.step 29 (.close 66)))))) (.step 3 (.step 11 (.step 18 (.step 29 (.step 38 (.close 66))))))) (.step 3 (.step 18 (.step 29 (.close 66))))) (.step 7 (.step 18 (.step 7 (.close 11))))) (.step 7 (.step 18 (.step 7 (.close 19))))))))))) (.reuse 1)) (.run (.step 3 (.step 7 (.step 18 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.step 7 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 29)))) (.step 3 (.step 18 (.step 29 (.close 31)))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 29 (.close 31)))) (.step 3 (.close 29))) (.step 3 (.step 11 (.close 17))))))))) (.step 3 (.step 11 (.step 31 (.step 47 (.step 66 (.step 67 (.step 74 (.split 35 1 (.reuse 2) (.run (.step 3 (.step 5 (.step 9 (.step 11 (.step 29 (.step 31 (.step 38 (.step 66 (.step 67 (.step 74 (.split 10 0 (.split 30 0 (.split 63 0 (.split 64 0 (.step 11 (.step 3 (.close 5))) (.step 11 (.close 5))) (.step 11 (.step 5 (.close 31)))) (.step 3 (.close 11))) (.step 3 (.close 11)))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405634970392459735496868692530956040756468332803841040762245551796284960602347012096⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 11 (.step 18 (.step 29 (.step 31 (.split 14 1 (.split 35 1 (.split 38 1 (.step 11 (.step 74 (.split 56 1 (.step 63 (.step 66 (.step 67 (.step 75 (.step 77 (.split 26 1 (.split 63 1 (.split 72 1 (.step 5 (.step 23 (.split 16 0 (.step 5 (.step 11 (.step 3 (.step 31 (.step 5 (.close 12)))))) (.step 3 (.step 8 (.step 11 (.step 12 (.close 18)))))))) (.step 3 (.step 5 (.step 29 (.step 5 (.close 31)))))) (.step 11 (.step 12 (.step 23 (.step 66 (.step 3 (.close 5))))))) (.step 3 (.step 5 (.step 28 (.step 11 (.close 29))))))))))) (.step 5 (.step 18 (.step 5 (.close 66))))))) (.step 5 (.step 18 (.step 5 (.close 66))))) (.step 3 (.step 5 (.step 29 (.step 31 (.step 11 (.step 32 (.step 38 (.close 5))))))))) (.step 5 (.step 11 (.step 12 (.close 17))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case84
