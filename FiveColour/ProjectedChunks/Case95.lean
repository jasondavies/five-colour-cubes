module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545143754822751573472831330831589048320557084074783133113336629601807170942703256664697145419586139205569961724799301934347994824631263106783522456600576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.step 58 (.split 56 1 (.split 59 1 (.split 67 1 (.split 55 1 (.split 72 1 (.split 34 0 (.step 7 (.step 3 (.step 18 (.close 31)))) (.step 31 (.close 3))) (.step 29 (.step 75 (.step 3 (.close 31))))) (.step 31 (.close 58))) (.step 3 (.close 7))) (.step 26 (.split 67 1 (.split 55 1 (.split 25 0 (.split 34 0 (.split 12 0 (.step 18 (.close 62)) (.step 9 (.step 3 (.close 62)))) (.step 9 (.close 31))) (.step 3 (.close 58))) (.step 48 (.step 31 (.close 62)))) (.step 3 (.close 7))))) (.step 3 (.step 75 (.split 59 1 (.split 72 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 28 (.step 3 (.close 31))) (.step 3 (.close 21))) (.step 22 (.step 28 (.step 3 (.close 31))))) (.step 3 (.close 15))) (.step 10 (.close 31))) (.step 29 (.step 31 (.close 3)))) (.step 3 (.close 58))))))) (.step 3 (.step 9 (.step 58 (.step 75 (.split 59 1 (.step 31 (.step 57 (.close 3))) (.step 26 (.step 57 (.close 3))))))))) (.step 3 (.close 54))) (.step 57 (.step 58 (.step 62 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 25 0 (.split 34 0 (.step 53 (.close 3)) (.step 9 (.close 31))) (.step 3 (.close 58))) (.step 3 (.close 18))) (.step 53 (.close 3))) (.step 3 (.close 58))) (.step 48 (.step 53 (.close 58)))) (.step 9 (.step 21 (.step 53 (.step 3 (.close 57)))))) (.step 9 (.step 21 (.step 26 (.step 31 (.close 53)))))) (.step 3 (.close 70))) (.step 3 (.close 54))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512187420787110447655700316220349906201416292499492770526602971766237220553610102842276237835200460427667414450176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 58 (.step 62 (.split 50 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 25 0 (.split 34 0 (.split 12 0 (.step 18 (.step 3 (.close 31))) (.step 9 (.step 3 (.step 18 (.close 12))))) (.step 9 (.close 31))) (.step 3 (.close 58))) (.step 52 (.close 3))) (.step 3 (.close 58))) (.step 48 (.step 52 (.close 31)))) (.step 52 (.step 57 (.close 3)))) (.step 9 (.step 26 (.step 40 (.step 31 (.step 52 (.step 57 (.close 31)))))))) (.step 3 (.close 70))) (.step 3 (.close 54))) (.step 52 (.split 72 1 (.split 56 1 (.step 52 (.close 3)) (.step 31 (.close 52))) (.step 26 (.step 29 (.step 31 (.close 52))))))))))) (.run (.step 3 (.step 46 (.step 9 (.step 27 (.step 46 (.close 52)))))))) (.run (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.step 7 (.close 45))) (.step 9 (.close 31))) (.step 31 (.close 53))) (.step 31 (.close 52))))) (.run (.step 3 (.step 21 (.step 58 (.split 42 1 (.split 49 1 (.split 54 1 (.split 59 1 (.step 41 (.split 72 1 (.split 55 1 (.split 6 0 (.split 10 0 (.split 12 0 (.split 16 0 (.step 28 (.step 41 (.step 3 (.close 31)))) (.step 3 (.close 41))) (.step 21 (.step 31 (.close 3)))) (.step 3 (.close 41))) (.step 10 (.close 31))) (.step 3 (.step 5 (.close 41)))) (.step 31 (.step 38 (.step 3 (.close 41)))))) (.step 3 (.step 9 (.step 21 (.step 31 (.close 41)))))) (.step 31 (.close 57))) (.step 3 (.step 16 (.step 31 (.step 52 (.close 58)))))) (.step 31 (.close 45))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853694006806360684629111466770940349627280193079652828667345527717756928⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 25 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 57 (.split 49 1 (.split 50 1 (.step 31 (.close 39)) (.step 31 (.close 53))) (.step 31 (.close 52))))))) (.run (.step 3 (.step 21 (.step 38 (.step 57 (.step 3 (.split 36 1 (.split 38 1 (.step 75 (.step 58 (.split 42 1 (.split 56 1 (.split 49 1 (.step 29 (.split 59 1 (.split 55 1 (.split 54 1 (.step 38 (.close 31)) (.step 9 (.step 21 (.step 31 (.close 18))))) (.step 18 (.close 38))) (.step 9 (.step 21 (.step 26 (.step 18 (.step 31 (.close 12)))))))) (.step 9 (.step 21 (.step 40 (.step 52 (.step 57 (.step 31 (.step 26 (.step 31 (.close 12)))))))))) (.step 29 (.step 31 (.step 3 (.close 38))))) (.step 31 (.close 45))))) (.step 29 (.step 31 (.close 38)))) (.step 31 (.close 39)))))))))) (.run (.step 7 (.split 38 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 37)) (.step 15 (.close 31))) (.step 9 (.step 15 (.step 31 (.close 52))))) (.step 31 (.close 52))) (.step 16 (.step 21 (.step 28 (.step 31 (.close 37))))))))) (.run (.split 35 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.close 31))))) (.run (.step 3 (.split 38 1 (.split 49 1 (.split 50 1 (.step 28 (.step 29 (.split 54 1 (.split 59 1 (.step 28 (.split 6 0 (.step 3 (.close 28)) (.step 10 (.close 3)))) (.step 3 (.step 9 (.close 28)))) (.step 29 (.close 57))))) (.step 3 (.step 9 (.step 29 (.step 53 (.close 58)))))) (.step 3 (.step 9 (.step 31 (.step 52 (.close 58)))))) (.step 58 (.step 28 (.step 3 (.close 58))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853697380090703193104493962814292945836588953165077503503974174640046080⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 26 (.step 18 (.close 7)))))) (.run (.step 18 (.step 31 (.split 25 1 (.split 35 1 (.split 38 1 (.step 57 (.split 49 1 (.split 50 1 (.split 59 1 (.split 72 1 (.step 3 (.split 56 1 (.step 18 (.step 4 (.step 3 (.close 9)))) (.step 4 (.step 10 (.step 18 (.close 4)))))) (.step 18 (.close 31))) (.step 3 (.step 4 (.step 9 (.close 18))))) (.step 3 (.step 18 (.close 53)))) (.step 9 (.step 18 (.step 48 (.close 52)))))) (.step 3 (.step 4 (.step 21 (.step 28 (.step 4 (.step 22 (.close 41)))))))) (.step 18 (.step 31 (.close 38)))) (.step 4 (.step 10 (.step 28 (.step 3 (.step 18 (.close 4))))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.step 22 (.step 18 (.close 7))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.step 18 (.close 7))) (.step 7 (.close 18))) (.step 7 (.close 18))))))) (.run (.step 18 (.step 21 (.step 22 (.step 26 (.split 21 1 (.split 25 1 (.step 57 (.split 35 1 (.step 3 (.split 49 1 (.split 50 1 (.split 55 1 (.split 38 1 (.step 9 (.step 75 (.split 56 1 (.split 59 1 (.step 31 (.step 15 (.close 3))) (.step 15 (.close 3))) (.step 31 (.close 15))))) (.step 31 (.step 15 (.close 3)))) (.step 9 (.step 31 (.step 48 (.step 58 (.close 15)))))) (.step 21 (.step 15 (.close 53)))) (.step 12 (.step 15 (.close 52))))) (.step 15 (.close 38)))) (.step 3 (.step 28 (.step 29 (.step 15 (.step 21 (.close 28))))))) (.step 4 (.step 15 (.close 3))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829016572853697380090703193104493962814292945836591488466277962268620177260150784⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.split 10 1 (.reuse 0) (.run (.step 7 (.step 15 (.split 35 1 (.split 49 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 9))) (.step 3 (.close 18))) (.step 3 (.close 31))))))) (.run (.step 9 (.step 18 (.step 9 (.step 10 (.step 18 (.step 9 (.close 31)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part4.excludes
end FiveColour.Packed.ProjectedChunks.Case95
