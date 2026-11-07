module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case132
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3, 10772758326371078510970147200012526354604737634583951647284399502621932439294850254393591254141823556597649460084701075384149029362889777997765031562067818873446862015111366371654301004092814533792443451687449919491⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨35316146901545158704630, 5653543574944814755571853247436803716454724612791659711089705579306986522117889612360021199005891927787012395663881876145364984991659977283795580425489459579195031692141033330803301315732180305291384498095632819925550081, 0⟩]
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
def root : Box := ⟨3, 10772758326371073726904414136201552772719580015795275356042424285955951550538926289651002141538494530607311671562521141619824273911692708017367275900848935247718321850365196592911898276078081512404062658346765778947⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 47 (.split 41 1 (.split 23 0 (.split 41 0 (.split 18 0 (.split 46 1 (.split 47 1 (.split 57 1 (.step 18 (.step 66 (.close 18))) (.split 63 1 (.step 18 (.step 50 (.step 18 (.close 49)))) (.step 49 (.close 66)))) (.step 50 (.split 63 1 (.step 18 (.step 50 (.close 18))) (.step 49 (.close 66))))) (.step 49 (.split 63 1 (.step 18 (.step 50 (.step 18 (.close 49)))) (.step 49 (.close 66))))) (.step 55 (.split 46 1 (.split 47 1 (.split 57 1 (.step 18 (.close 67)) (.step 18 (.step 45 (.close 66)))) (.step 50 (.step 18 (.close 39)))) (.step 49 (.step 18 (.step 45 (.close 66))))))) (.step 55 (.step 69 (.split 46 1 (.split 47 1 (.step 18 (.step 66 (.close 18))) (.step 50 (.step 18 (.close 50)))) (.step 49 (.step 18 (.close 49))))))) (.step 55 (.step 69 (.split 46 1 (.split 47 1 (.step 18 (.step 66 (.close 18))) (.step 50 (.step 18 (.close 50)))) (.step 49 (.step 18 (.close 49))))))) (.step 55 (.step 69 (.split 46 1 (.split 47 1 (.split 57 1 (.step 18 (.close 66)) (.step 18 (.close 8))) (.step 18 (.close 49))) (.step 18 (.close 49))))))))
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
def root : Box := ⟨3, 10772758326371078510970147200012526354604737634583951647284399502621932439294850254393591254141823556597649460084698888131338319521905946104052455208805683180604149977659917041931944653491273238428443330099904774147⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 51 (.step 69 (.split 19 0 (.split 33 0 (.reuse 0) (.run (.step 51 (.step 55 (.step 47 (.split 41 1 (.split 46 1 (.split 47 1 (.split 57 1 (.split 3 0 (.step 18 (.close 74)) (.step 18 (.close 66))) (.split 63 1 (.step 18 (.close 60)) (.step 18 (.close 66)))) (.step 50 (.split 63 1 (.step 18 (.close 50)) (.step 18 (.close 50))))) (.step 49 (.split 63 1 (.step 18 (.close 49)) (.step 12 (.close 49))))) (.step 69 (.split 46 1 (.split 47 1 (.split 57 1 (.step 18 (.close 66)) (.step 18 (.close 8))) (.step 18 (.close 44))) (.step 18 (.close 44)))))))))) (.run (.step 51 (.step 55 (.step 47 (.split 46 1 (.split 47 1 (.split 57 1 (.split 3 0 (.step 18 (.close 74)) (.step 18 (.close 67))) (.split 63 1 (.step 18 (.close 60)) (.step 18 (.close 66)))) (.step 50 (.split 63 1 (.step 18 (.close 50)) (.step 18 (.close 50))))) (.step 49 (.split 63 1 (.step 18 (.close 49)) (.step 12 (.close 49))))))))))))
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
def root : Box := ⟨4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826051, 10772758326371078510970147200012526354604737634583951647284399502621932439294850254393591254141823556597649460084701075384149027373596832358618461215102239586951746825210261533189762426629359065309323630408726740995⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 33 1 (.split 44 1 (.split 46 1 (.split 47 1 (.split 48 1 (.split 57 1 (.split 63 1 (.split 64 1 (.split 66 1 (.split 71 1 (.split 18 0 (.step 55 (.split 41 1 (.split 46 0 (.split 47 0 (.step 18 (.close 34)) (.step 18 (.close 8))) (.step 12 (.step 18 (.close 8)))) (.step 44 (.close 12)))) (.step 55 (.close 22))) (.step 18 (.step 34 (.step 36 (.step 17 (.close 40)))))) (.step 55 (.close 69))) (.step 18 (.step 32 (.step 55 (.step 17 (.step 34 (.step 61 (.close 69)))))))) (.step 18 (.step 55 (.step 66 (.close 34))))) (.step 18 (.step 43 (.step 34 (.close 44))))) (.step 51 (.close 34))) (.step 18 (.step 32 (.step 51 (.step 55 (.step 44 (.close 49))))))) (.step 12 (.step 18 (.step 51 (.step 55 (.step 44 (.close 49))))))) (.step 55 (.close 47))) (.step 34 (.split 44 1 (.split 46 1 (.split 47 1 (.split 48 1 (.split 57 1 (.split 63 1 (.split 64 1 (.split 66 1 (.split 71 1 (.step 36 (.close 12)) (.step 18 (.close 34))) (.step 51 (.close 69))) (.step 18 (.step 36 (.close 66)))) (.step 18 (.step 34 (.close 66)))) (.step 18 (.step 34 (.close 44)))) (.step 36 (.close 51))) (.step 18 (.step 32 (.step 35 (.step 14 (.step 43 (.step 44 (.close 51)))))))) (.step 18 (.step 34 (.close 49)))) (.step 55 (.close 47))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3, 10772758326371078510970147200012526354604737634583951647284399502621932439294850254393591254141823556597649460084701075384149029362889777997765031562067818871876054085723830291836995301262509680543950471173284823043⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 23 1 (.split 29 1 (.split 31 1 (.split 33 1 (.reuse 0) (.run (.split 44 1 (.split 46 1 (.split 47 1 (.split 48 1 (.split 57 1 (.split 63 1 (.split 64 1 (.split 66 1 (.split 71 1 (.split 18 0 (.step 51 (.step 44 (.step 55 (.step 18 (.close 36))))) (.step 55 (.close 22))) (.step 18 (.step 36 (.close 40)))) (.step 55 (.close 69))) (.step 18 (.step 32 (.step 51 (.step 40 (.step 36 (.close 67))))))) (.step 12 (.step 18 (.step 51 (.step 55 (.step 36 (.step 32 (.close 66)))))))) (.step 18 (.step 43 (.step 36 (.close 44))))) (.step 51 (.close 22))) (.step 18 (.step 32 (.step 51 (.step 43 (.close 44)))))) (.step 12 (.step 18 (.step 51 (.step 44 (.step 50 (.step 43 (.close 44)))))))) (.step 55 (.close 47))))) (.reuse 1)) (.run (.step 32 (.step 51 (.step 69 (.split 19 0 (.split 33 0 (.step 47 (.split 46 1 (.split 57 1 (.step 32 (.step 18 (.close 32))) (.step 18 (.close 32))) (.step 18 (.close 32)))) (.step 32 (.close 18))) (.step 32 (.close 18)))))))) (.run (.step 32 (.split 31 1 (.split 33 1 (.split 41 1 (.step 51 (.step 55 (.step 47 (.step 69 (.split 46 1 (.split 47 1 (.split 57 1 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.close 22)) (.step 18 (.close 22))) (.step 18 (.close 67))) (.step 18 (.close 66))) (.step 18 (.close 26))) (.step 18 (.close 50))) (.step 18 (.close 49))))))) (.step 55 (.close 22))) (.step 36 (.step 55 (.close 22)))) (.step 34 (.step 55 (.close 22)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3064991081731777716716694054300618367237478244367204355, 10772758326371078510970147200012526354604737634583951647284399502621932439294850254393591254141823556597649460084701075384149029362889777997765031562067818873446862015111366371654301004091576593753158071412550795267⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 6 (.step 32 (.split 19 1 (.split 31 1 (.split 33 1 (.split 41 1 (.split 44 1 (.split 46 1 (.split 47 1 (.split 48 1 (.split 57 1 (.split 63 1 (.split 64 1 (.split 66 1 (.split 71 1 (.split 23 1 (.step 55 (.split 46 0 (.split 47 0 (.step 18 (.close 21)) (.step 18 (.close 10))) (.step 12 (.step 18 (.close 10))))) (.step 26 (.close 12))) (.step 18 (.step 21 (.step 22 (.step 23 (.close 9)))))) (.step 55 (.close 69))) (.step 18 (.step 32 (.step 55 (.step 21 (.close 67)))))) (.step 18 (.step 55 (.step 38 (.step 66 (.close 69)))))) (.step 18 (.step 24 (.step 21 (.close 26))))) (.step 51 (.close 21))) (.step 18 (.step 32 (.step 51 (.step 55 (.step 26 (.close 50))))))) (.step 12 (.step 18 (.step 51 (.step 55 (.step 26 (.close 50))))))) (.step 55 (.close 47))) (.step 21 (.step 55 (.close 21)))) (.step 21 (.step 36 (.step 55 (.close 21))))) (.step 21 (.step 34 (.step 55 (.close 21))))) (.step 21 (.split 44 1 (.split 46 1 (.split 47 1 (.split 48 1 (.split 57 1 (.split 63 1 (.split 64 1 (.split 66 1 (.split 71 1 (.step 22 (.close 12)) (.step 18 (.close 21))) (.step 51 (.close 69))) (.step 18 (.step 22 (.close 67)))) (.step 18 (.step 22 (.step 21 (.close 66))))) (.step 18 (.step 21 (.close 26)))) (.step 22 (.close 51))) (.step 18 (.step 21 (.close 50)))) (.step 18 (.step 24 (.step 41 (.step 49 (.step 21 (.close 51))))))) (.step 55 (.close 47))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3, 10772758326371078510970147200012526354604737634583951647284399502621932439294850254393591254141823556597649460084701075384149029362889777997765031562067818873446862015111366371654301004092814533792443451687449919491⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 9 1 (.split 18 1 (.split 3 1 (.split 19 1 (.reuse 0) (.run (.step 32 (.split 31 1 (.split 33 1 (.split 41 1 (.split 44 1 (.split 46 1 (.split 47 1 (.split 48 1 (.split 57 1 (.split 63 1 (.split 64 1 (.split 66 1 (.split 71 1 (.split 23 1 (.step 51 (.step 55 (.step 18 (.close 22)))) (.step 22 (.close 12))) (.step 18 (.step 22 (.close 23)))) (.step 55 (.close 69))) (.step 18 (.step 32 (.step 51 (.step 23 (.step 22 (.close 67))))))) (.step 12 (.step 18 (.step 51 (.step 55 (.step 22 (.step 32 (.step 26 (.close 66))))))))) (.step 18 (.step 24 (.step 22 (.close 26))))) (.step 51 (.close 22))) (.step 18 (.step 32 (.step 51 (.step 24 (.close 26)))))) (.step 12 (.step 18 (.step 51 (.step 26 (.step 50 (.step 24 (.close 26)))))))) (.step 55 (.close 47))) (.step 22 (.step 55 (.close 22)))) (.step 22 (.step 36 (.step 51 (.close 22))))) (.step 22 (.step 34 (.step 55 (.close 22)))))))) (.run (.step 6 (.step 51 (.step 69 (.split 19 0 (.split 33 0 (.step 47 (.split 46 1 (.split 47 1 (.split 57 1 (.split 63 1 (.split 64 1 (.step 6 (.step 18 (.close 6))) (.step 18 (.close 6))) (.step 18 (.step 6 (.close 66)))) (.step 18 (.close 6))) (.step 18 (.close 6))) (.step 18 (.step 6 (.close 49))))) (.step 6 (.step 18 (.step 8 (.close 11))))) (.step 6 (.step 18 (.step 28 (.close 29)))))))))) (.reuse 1)) (.run (.step 12 (.step 51 (.step 69 (.split 19 0 (.split 33 0 (.step 47 (.split 47 1 (.split 57 1 (.step 12 (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 18 (.close 12)))) (.step 12 (.close 18))) (.step 12 (.close 18))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case132
