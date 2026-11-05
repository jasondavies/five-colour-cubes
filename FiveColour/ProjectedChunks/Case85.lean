module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case85
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629417799930527318685021603565546019137056466607621217069470404367987255528128512⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593704327342213348339, 5789228615357111146520048038021683988773733487122101869605338720869906162805958987122173504434281850008071622175991935381017825153590590481063666660227604324706233660950604329370748855691173985301545264301300140783538537472, 0⟩]
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925664188033770695627336559962463655613398901129254453295620147697437467558653698612971399368017296780685497007858299496805775567417765658957340022673413260619790595994419200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.split 72 1 (.split 74 1 (.split 71 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 3 (.step 15 (.close 28))) (.step 3 (.step 18 (.step 5 (.close 12))))) (.step 3 (.close 12))) (.step 3 (.step 5 (.step 3 (.close 28))))) (.step 31 (.step 18 (.close 74)))) (.step 74 (.split 2 0 (.step 69 (.split 16 0 (.step 31 (.step 11 (.step 18 (.step 3 (.close 5))))) (.step 11 (.step 18 (.close 3))))) (.step 11 (.step 23 (.step 31 (.step 5 (.step 18 (.close 5))))))))) (.step 29 (.step 69 (.step 74 (.step 75 (.step 3 (.close 31))))))) (.step 3 (.close 7))) (.step 3 (.step 74 (.step 3 (.step 63 (.step 74 (.step 18 (.step 23 (.step 3 (.step 29 (.step 15 (.step 26 (.step 15 (.close 31)))))))))))))) (.step 3 (.step 67 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.step 31 (.step 18 (.close 67))) (.step 11 (.step 67 (.close 3)))) (.step 29 (.step 67 (.close 3)))) (.step 63 (.step 3 (.close 67)))))))) (.step 66 (.step 3 (.step 66 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.step 31 (.step 18 (.close 66))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.close 3)))) (.step 63 (.step 3 (.close 66))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978176018699776613985412130863684895550980967675960521253822360591399699662629030754170785895201778542701229728464896000⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 3 (.split 63 1 (.split 64 1 (.split 65 1 (.step 18 (.step 74 (.step 75 (.split 74 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 10 0 (.step 28 (.split 14 0 (.step 59 (.close 3)) (.step 3 (.step 5 (.step 3 (.step 12 (.close 31))))))) (.step 3 (.step 28 (.step 12 (.close 31))))) (.step 5 (.step 3 (.step 28 (.close 31))))) (.step 28 (.step 31 (.close 3)))) (.step 22 (.step 31 (.close 5)))) (.step 5 (.step 12 (.close 18))))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 22 (.step 28 (.step 15 (.step 26 (.step 15 (.close 31))))))))))) (.step 18 (.step 31 (.step 63 (.close 67))))) (.step 18 (.step 31 (.step 12 (.step 63 (.close 66))))))))) (.run (.step 3 (.step 51 (.step 3 (.close 7)))))) (.run (.step 3 (.step 9 (.step 10 (.step 27 (.step 47 (.step 3 (.step 7 (.step 3 (.close 10))))))))))) (.run (.step 7 (.step 31 (.step 75 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.step 31 (.step 7 (.step 22 (.close 28)))) (.step 29 (.step 31 (.close 67))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 3 (.step 5 (.step 28 (.step 5 (.step 31 (.step 3 (.step 26 (.close 45))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943950551163295313665743697413502706602643369329434655854128075230377850467905497212678483639157156330556963684352⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.reuse 0) (.run (.step 3 (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 3 (.step 75 (.split 74 1 (.split 72 1 (.split 2 0 (.split 10 0 (.step 28 (.split 14 0 (.step 41 (.close 3)) (.step 3 (.step 5 (.step 3 (.step 12 (.close 31))))))) (.step 3 (.step 28 (.step 12 (.close 31))))) (.step 5 (.step 3 (.step 28 (.close 31))))) (.step 28 (.step 31 (.close 3)))) (.step 5 (.close 12))))) (.step 18 (.step 31 (.step 18 (.close 5))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 21 (.step 28 (.close 31)))))))) (.step 18 (.step 21 (.step 31 (.close 67))))) (.step 18 (.step 31 (.step 12 (.step 63 (.close 66)))))) (.step 5 (.step 10 (.step 28 (.step 59 (.split 63 1 (.split 64 1 (.step 59 (.step 3 (.step 5 (.step 41 (.step 18 (.step 22 (.step 5 (.step 12 (.close 31))))))))) (.step 5 (.step 18 (.step 21 (.step 31 (.step 5 (.step 41 (.step 5 (.step 12 (.close 67)))))))))) (.step 5 (.step 18 (.step 31 (.step 49 (.step 41 (.step 22 (.step 59 (.close 66)))))))))))))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 41 (.close 3))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252835458093312342499596338075880872002287662450830431737287498593659801478606535027177191032088214400663552⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 74 (.step 75 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.step 7 (.split 64 1 (.step 31 (.step 7 (.step 22 (.close 28)))) (.step 29 (.step 31 (.close 67))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 3 (.step 5 (.step 22 (.step 28 (.step 5 (.step 31 (.step 3 (.close 39))))))))) (.step 7 (.step 31 (.close 39)))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 39)))))))))))) (.run (.step 3 (.step 9 (.step 38 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.step 75 (.split 65 1 (.split 74 1 (.split 51 1 (.step 29 (.split 67 1 (.split 2 0 (.split 10 0 (.split 16 0 (.split 51 0 (.step 67 (.step 38 (.step 66 (.step 31 (.step 3 (.close 18)))))) (.step 21 (.step 3 (.step 15 (.step 22 (.step 15 (.close 26))))))) (.step 21 (.step 38 (.close 18)))) (.step 31 (.step 38 (.close 3)))) (.step 31 (.step 3 (.step 12 (.step 3 (.step 21 (.close 32))))))) (.step 3 (.close 21)))) (.step 3 (.close 21))) (.step 3 (.step 29 (.step 40 (.step 66 (.step 67 (.step 69 (.step 31 (.step 74 (.step 3 (.step 5 (.close 17)))))))))))) (.step 3 (.step 21 (.step 29 (.close 31)))))) (.step 3 (.step 5 (.step 29 (.step 31 (.step 3 (.close 38))))))) (.step 3 (.step 29 (.step 31 (.step 38 (.close 3)))))) (.step 3 (.step 5 (.step 31 (.step 28 (.close 38)))))) (.step 3 (.step 29 (.step 31 (.step 38 (.step 3 (.step 22 (.close 39))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629417799930523948691688209732575607400854645021650595325456785363248417266991104⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 38 (.step 66 (.step 75 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 64 1 (.step 7 (.split 71 1 (.step 31 (.step 7 (.step 29 (.step 3 (.step 22 (.close 37)))))) (.step 29 (.step 31 (.close 17))))) (.step 3 (.step 29 (.step 31 (.step 17 (.close 66)))))) (.step 3 (.step 5 (.step 28 (.step 5 (.step 31 (.close 37))))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 37)))))) (.step 7 (.step 31 (.close 37))))))))))) (.run (.step 3 (.step 7 (.step 18 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 31)))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.close 31)))))))) (.run (.step 3 (.step 18 (.step 28 (.step 29 (.split 63 1 (.split 64 1 (.split 65 1 (.step 29 (.split 71 1 (.split 74 1 (.step 28 (.step 3 (.step 29 (.split 2 0 (.split 10 0 (.step 28 (.close 3)) (.step 3 (.close 12))) (.step 5 (.step 3 (.close 28))))))) (.step 3 (.step 5 (.step 18 (.step 5 (.close 28)))))) (.step 18 (.step 29 (.step 63 (.close 74)))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 28 (.step 18 (.step 28 (.step 21 (.close 29)))))))))) (.step 18 (.step 29 (.step 63 (.close 67))))) (.step 18 (.step 29 (.step 49 (.step 63 (.step 66 (.close 5)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758320032835933598087636165669219771963862058316698165659873414211687740726299878212593272693004555098190908902420157318426349174685515026076305383284698042972875228007572459563493281219981968328030194304180592030253056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 25 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 65 1 (.split 72 1 (.split 74 1 (.split 34 1 (.step 27 (.split 36 1 (.split 30 1 (.split 42 1 (.split 51 1 (.split 63 1 (.step 3 (.split 64 1 (.split 2 0 (.split 16 0 (.step 31 (.step 11 (.step 18 (.step 23 (.close 5))))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 23 (.step 17 (.close 5))))) (.step 11 (.step 67 (.close 3))))) (.step 11 (.step 12 (.step 34 (.step 17 (.close 66)))))) (.step 3 (.close 17))) (.step 3 (.step 5 (.step 31 (.close 17))))) (.step 3 (.close 17))) (.step 3 (.step 5 (.step 31 (.close 17)))))) (.step 3 (.step 5 (.step 17 (.close 31))))) (.step 11 (.step 17 (.step 3 (.step 31 (.step 17 (.close 3))))))) (.step 3 (.step 17 (.step 29 (.step 31 (.step 40 (.step 66 (.step 67 (.step 69 (.step 74 (.step 3 (.step 31 (.close 17))))))))))))) (.step 3 (.step 17 (.step 18 (.step 12 (.step 17 (.step 12 (.close 34)))))))) (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 31 (.step 5 (.step 12 (.close 17)))))))))) (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 31 (.step 5 (.step 12 (.close 17)))))))))) (.step 3 (.step 5 (.step 17 (.step 29 (.step 31 (.step 38 (.step 40 (.step 66 (.step 67 (.step 74 (.step 77 (.split 2 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.step 5 (.close 12)))))))))))))))) (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 28 (.step 29 (.step 5 (.step 12 (.close 17))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629417799930527318685021603565546019137056466607618681768269947909184262119620608⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 77 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 67)))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 18 (.step 38 (.step 66 (.step 38 (.close 67)))))))))))) (.run (.step 7 (.step 18 (.step 74 (.step 77 (.split 22 1 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.step 18 (.step 3 (.close 7))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 18 (.step 38 (.close 66))))) (.step 7 (.step 18 (.step 3 (.close 7))))))))))) (.run (.step 7 (.step 18 (.step 67 (.step 77 (.split 17 1 (.split 22 1 (.split 35 1 (.split 63 1 (.step 7 (.step 67 (.step 18 (.step 3 (.close 7))))) (.step 3 (.step 11 (.step 18 (.step 38 (.close 66)))))) (.step 3 (.step 18 (.step 38 (.close 66))))) (.step 7 (.step 18 (.step 3 (.close 7))))) (.step 7 (.step 18 (.step 7 (.step 11 (.close 19)))))))))))) (.step 3 (.step 31 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.close 3)))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 3 (.close 17))))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 17 (.step 3 (.close 19))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629417799930527318685021603565546019137056466607621217069470404367987255528128512⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.split 10 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.split 14 1 (.split 35 1 (.split 63 1 (.step 7 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 31))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.close 31))) (.step 3 (.close 17)))))))) (.run (.step 3 (.step 18 (.step 28 (.step 31 (.split 14 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.step 5 (.step 74 (.step 5 (.step 3 (.step 23 (.step 5 (.step 31 (.step 5 (.step 12 (.close 18)))))))))) (.step 3 (.close 5))) (.step 5 (.step 11 (.step 23 (.step 32 (.step 63 (.step 67 (.close 5)))))))) (.step 11 (.step 12 (.step 63 (.step 66 (.close 5)))))) (.step 5 (.step 18 (.step 5 (.close 66))))) (.step 5 (.step 24 (.step 28 (.step 18 (.step 5 (.close 66))))))) (.step 3 (.step 5 (.step 29 (.step 31 (.step 32 (.step 38 (.close 5)))))))) (.step 5 (.step 12 (.close 17))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case85
