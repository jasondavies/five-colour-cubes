module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case95
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853697380090703193104493962814292945836591488466277962268620177260150784⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩]
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689606849435006565578796138799127648221478143495396993374276725291398493649195930352295802655321387768084711609160032618827066167930676661739403152583058075778730164224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.split 56 1 (.split 59 1 (.split 67 1 (.step 75 (.split 55 1 (.split 72 1 (.split 21 0 (.split 34 0 (.step 7 (.step 3 (.step 18 (.step 9 (.step 12 (.close 21)))))) (.step 31 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 4))))) (.step 29 (.step 75 (.step 3 (.step 9 (.close 12)))))) (.step 31 (.step 48 (.step 9 (.step 3 (.step 12 (.close 21)))))))) (.step 3 (.close 7))) (.step 26 (.split 67 1 (.split 55 1 (.split 21 0 (.split 25 0 (.split 34 0 (.split 12 0 (.step 7 (.step 18 (.step 3 (.step 9 (.step 21 (.close 22)))))) (.step 9 (.step 3 (.step 18 (.step 12 (.step 21 (.close 22))))))) (.step 9 (.step 7 (.step 15 (.step 16 (.step 21 (.close 22))))))) (.step 3 (.step 9 (.step 26 (.step 28 (.close 12)))))) (.step 3 (.step 9 (.step 4 (.step 17 (.close 18)))))) (.step 48 (.step 31 (.step 9 (.step 26 (.step 3 (.step 12 (.close 21)))))))) (.step 3 (.close 7))))) (.step 3 (.step 58 (.step 75 (.split 59 1 (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 28 (.step 3 (.step 22 (.step 16 (.close 21))))) (.step 3 (.close 21))) (.step 10 (.step 22 (.step 28 (.step 3 (.step 12 (.step 15 (.close 21)))))))) (.step 3 (.step 12 (.close 15)))) (.step 10 (.step 3 (.step 15 (.step 21 (.close 22)))))) (.step 29 (.step 31 (.close 3)))) (.step 3 (.step 9 (.step 22 (.step 26 (.step 28 (.step 31 (.close 12))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545143754822751573472831330831589048320557084074783133113336629601807170942703256664697145419586139205569961724799301934347994824631263106783522456600576⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 54 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 58 (.step 75 (.split 56 1 (.split 59 1 (.step 31 (.step 57 (.close 3))) (.step 26 (.step 57 (.close 3)))) (.step 22 (.step 31 (.step 3 (.close 57))))))))))) (.run (.step 3 (.step 7 (.step 26 (.step 44 (.close 54))))))) (.run (.step 57 (.step 58 (.step 62 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 25 0 (.split 34 0 (.step 53 (.close 3)) (.step 9 (.step 7 (.step 15 (.step 16 (.close 21)))))) (.step 3 (.step 9 (.step 21 (.step 28 (.close 12)))))) (.step 3 (.step 9 (.step 4 (.step 17 (.close 18)))))) (.step 53 (.close 3))) (.step 3 (.step 9 (.step 21 (.step 22 (.step 31 (.close 12))))))) (.step 48 (.step 53 (.step 3 (.step 9 (.step 21 (.step 22 (.step 28 (.close 31))))))))) (.step 9 (.step 21 (.step 53 (.step 3 (.step 31 (.step 18 (.step 3 (.step 12 (.close 26)))))))))) (.step 9 (.step 21 (.step 26 (.step 18 (.step 29 (.step 31 (.step 3 (.close 12))))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 7 (.step 53 (.close 7))))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926745682103906354870414032147597141660462029411235337174700503848381049100824488372976999166446854267879484507377096335487687196672⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 57 (.step 58 (.step 62 (.split 50 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 25 0 (.split 34 0 (.split 12 0 (.step 7 (.step 18 (.step 3 (.step 9 (.step 21 (.close 22)))))) (.step 9 (.step 3 (.step 18 (.close 12))))) (.step 9 (.step 7 (.step 15 (.close 16))))) (.step 3 (.step 9 (.step 16 (.close 28))))) (.step 3 (.step 9 (.step 4 (.step 17 (.close 18)))))) (.step 52 (.close 3))) (.step 3 (.step 9 (.step 16 (.step 22 (.step 31 (.close 21))))))) (.step 48 (.step 52 (.step 3 (.close 22))))) (.step 9 (.step 52 (.step 31 (.step 57 (.close 3)))))) (.step 9 (.step 26 (.step 29 (.step 31 (.step 40 (.step 31 (.step 52 (.step 57 (.step 18 (.step 12 (.close 16)))))))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 52)))))) (.step 3 (.step 7 (.step 52 (.close 7))))) (.step 52 (.split 72 1 (.split 56 1 (.step 52 (.close 3)) (.step 3 (.step 9 (.step 16 (.step 21 (.step 22 (.step 31 (.close 52)))))))) (.step 9 (.step 21 (.step 26 (.step 29 (.step 31 (.step 40 (.close 52))))))))))))))) (.run (.step 3 (.step 46 (.step 9 (.step 27 (.step 46 (.close 52))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512187420787110447655700316220349906201416292499492770526602971766237220553610102842276237835200460427667414450176⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.step 7 (.step 28 (.step 3 (.step 26 (.close 45)))))) (.step 9 (.step 26 (.step 29 (.close 31))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 29 (.step 31 (.close 53)))))))) (.step 9 (.step 18 (.step 26 (.step 31 (.close 52))))))))))) (.run (.step 3 (.step 21 (.step 58 (.split 42 1 (.split 49 1 (.split 54 1 (.split 59 1 (.step 41 (.split 72 1 (.split 55 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 28 (.step 41 (.step 3 (.step 21 (.step 16 (.close 22)))))) (.step 3 (.step 21 (.close 28)))) (.step 10 (.step 21 (.step 28 (.step 31 (.close 3)))))) (.step 3 (.step 12 (.step 15 (.step 22 (.close 28)))))) (.step 10 (.step 3 (.step 21 (.step 22 (.step 3 (.step 15 (.close 26)))))))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 9 (.close 12))))))) (.step 29 (.step 31 (.step 3 (.step 38 (.step 3 (.step 22 (.step 39 (.close 41)))))))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 28 (.step 31 (.step 12 (.close 41))))))))) (.step 10 (.step 21 (.step 31 (.step 41 (.step 3 (.step 41 (.close 57)))))))) (.step 3 (.step 9 (.step 16 (.step 21 (.step 31 (.step 41 (.step 52 (.step 28 (.step 52 (.step 41 (.close 58)))))))))))) (.step 31 (.step 28 (.step 41 (.close 3))))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122459273227302299118403185275479644925457720565502906633823357963745506084236132781373234336185324851429376⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 57 (.step 75 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 22 (.step 28 (.step 3 (.step 22 (.close 39))))))) (.step 9 (.step 18 (.step 21 (.step 22 (.step 29 (.step 31 (.close 53)))))))) (.step 9 (.step 18 (.step 22 (.step 31 (.close 52)))))) (.step 31 (.close 39))) (.step 21 (.step 31 (.step 28 (.close 39))))))))))) (.run (.step 3 (.step 9 (.step 21 (.step 38 (.step 57 (.step 3 (.split 36 1 (.split 38 1 (.step 75 (.step 58 (.split 42 1 (.split 56 1 (.split 49 1 (.step 29 (.split 59 1 (.split 55 1 (.split 16 0 (.split 54 1 (.step 38 (.step 3 (.close 9))) (.step 9 (.step 21 (.step 31 (.step 4 (.close 17)))))) (.step 3 (.step 18 (.step 9 (.step 3 (.step 15 (.close 21))))))) (.step 18 (.step 31 (.step 9 (.close 12))))) (.step 9 (.step 21 (.step 26 (.step 18 (.step 31 (.close 12)))))))) (.step 9 (.step 21 (.step 29 (.step 40 (.step 52 (.step 57 (.step 31 (.step 26 (.step 18 (.step 31 (.close 12)))))))))))) (.step 29 (.step 31 (.step 3 (.step 22 (.close 38)))))) (.step 29 (.step 31 (.step 3 (.step 38 (.close 3)))))))) (.step 29 (.step 31 (.close 38)))) (.step 29 (.step 31 (.step 38 (.step 3 (.step 22 (.close 39)))))))))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853697376799694078459085800147826227081114397722705646238905665669038080⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 38 (.step 75 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 37)) (.step 9 (.step 15 (.step 29 (.close 31))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 29 (.step 31 (.close 52)))))))) (.step 9 (.step 15 (.step 16 (.step 18 (.step 31 (.close 52))))))) (.step 31 (.close 37))) (.step 16 (.step 21 (.step 28 (.step 31 (.close 37)))))) (.step 31 (.close 37))))))))) (.run (.step 3 (.step 7 (.split 35 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.step 9 (.close 31)))))))) (.run (.step 3 (.step 29 (.step 58 (.split 34 1 (.split 36 1 (.split 42 1 (.split 38 1 (.step 29 (.split 49 1 (.split 50 1 (.step 28 (.step 29 (.split 54 1 (.split 59 1 (.step 28 (.split 6 0 (.step 3 (.close 28)) (.step 10 (.close 3)))) (.step 3 (.step 9 (.close 28)))) (.step 10 (.step 29 (.step 3 (.step 28 (.close 57)))))))) (.step 3 (.step 9 (.step 21 (.step 29 (.step 53 (.step 28 (.step 57 (.step 16 (.step 28 (.step 16 (.close 53)))))))))))) (.step 3 (.step 9 (.step 31 (.step 52 (.step 16 (.step 52 (.step 28 (.step 57 (.step 28 (.step 21 (.step 52 (.close 28)))))))))))))) (.step 21 (.step 28 (.step 58 (.step 28 (.step 3 (.step 9 (.step 12 (.close 21))))))))) (.step 28 (.step 29 (.close 3)))) (.step 28 (.step 29 (.close 3)))) (.step 16 (.step 28 (.step 29 (.close 3)))))))))) (.run (.step 7 (.step 18 (.step 26 (.step 18 (.close 7)))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853697380090703193104493962814292943178132961595245757696360054079356928⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 58 (.split 25 1 (.split 35 1 (.split 38 1 (.step 57 (.split 49 1 (.split 50 1 (.split 59 1 (.split 72 1 (.step 3 (.split 55 1 (.split 56 1 (.step 4 (.step 18 (.step 4 (.step 3 (.close 9))))) (.step 3 (.step 4 (.step 10 (.step 18 (.close 4)))))) (.step 3 (.step 4 (.close 5))))) (.step 4 (.step 9 (.step 3 (.step 18 (.step 15 (.close 24))))))) (.step 3 (.step 4 (.step 9 (.close 18))))) (.step 3 (.step 4 (.step 9 (.step 18 (.step 34 (.close 53))))))) (.step 3 (.step 9 (.step 18 (.step 34 (.step 4 (.step 48 (.close 52))))))))) (.step 3 (.step 4 (.step 5 (.step 10 (.step 21 (.step 28 (.step 4 (.step 22 (.step 3 (.close 4))))))))))) (.step 4 (.step 9 (.step 18 (.step 31 (.close 38)))))) (.step 3 (.step 4 (.step 5 (.step 10 (.step 28 (.step 3 (.step 18 (.close 4))))))))))))))) (.run (.step 7 (.step 18 (.step 22 (.step 18 (.split 22 1 (.step 22 (.step 18 (.close 7))) (.step 7 (.close 18))))))))) (.run (.step 7 (.step 18 (.step 21 (.split 17 1 (.step 21 (.step 18 (.split 22 1 (.step 21 (.step 18 (.close 7))) (.step 7 (.close 18))))) (.step 7 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853697380090703193104493962814292945836591488466277959962777168046456832⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 9 (.step 15 (.step 21 (.step 22 (.step 26 (.step 31 (.split 21 1 (.split 25 1 (.step 57 (.split 35 1 (.step 3 (.split 49 1 (.split 50 1 (.split 55 1 (.split 38 1 (.step 9 (.step 31 (.step 75 (.split 56 1 (.split 59 1 (.step 31 (.step 15 (.close 3))) (.step 15 (.close 3))) (.step 15 (.step 16 (.step 22 (.step 15 (.step 31 (.step 3 (.close 15))))))))))) (.step 10 (.step 15 (.step 16 (.step 21 (.step 31 (.step 3 (.step 15 (.close 3))))))))) (.step 9 (.step 12 (.step 15 (.step 31 (.step 48 (.step 58 (.close 15)))))))) (.step 9 (.step 15 (.step 21 (.step 15 (.step 3 (.step 12 (.step 3 (.step 26 (.step 3 (.step 32 (.step 48 (.close 53))))))))))))) (.step 9 (.step 12 (.step 15 (.step 3 (.step 21 (.step 3 (.step 26 (.step 3 (.step 34 (.close 52)))))))))))) (.step 9 (.step 15 (.step 3 (.step 21 (.step 29 (.step 31 (.step 4 (.close 18)))))))))) (.step 3 (.step 10 (.step 12 (.step 15 (.step 16 (.step 28 (.step 29 (.step 15 (.step 21 (.close 28))))))))))) (.step 3 (.step 4 (.step 9 (.step 15 (.close 3)))))))))))))))) (.run (.step 3 (.step 7 (.step 15 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 9))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 9 (.close 15)))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853697380090703193104493962814292945836591488466277962268620177260150784⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 10 (.step 18 (.step 9 (.step 3 (.step 10 (.step 18 (.step 9 (.step 10 (.step 3 (.step 15 (.step 22 (.step 26 (.close 31)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case95
