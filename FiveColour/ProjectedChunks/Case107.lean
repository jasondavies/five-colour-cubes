module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case107
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829011145099514380894042713214571680568612323806060286564838609235605292511657984⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908284911715939576823, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857309521993999462306427087381105369261884265993783467999530422928012791073057088273642977565022587162213165827073, 0⟩]
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545143754822751573472831330831589048320557084074783133113336629601807170942701447413302812354032645908929200976239094590837594190818145429111894207102976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.step 58 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.step 18 (.step 3 (.close 31)))) (.step 29 (.step 75 (.step 18 (.close 31))))) (.step 3 (.close 7))) (.step 26 (.split 67 1 (.split 21 0 (.split 34 0 (.split 16 0 (.step 62 (.close 3)) (.step 18 (.close 3))) (.step 9 (.close 31))) (.step 3 (.close 18))) (.step 3 (.close 70))))) (.step 3 (.step 58 (.step 75 (.split 59 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.step 59 (.close 3))) (.step 3 (.close 22))) (.step 3 (.close 21))) (.step 31 (.close 3))) (.step 3 (.close 15))) (.step 31 (.step 3 (.close 38)))) (.step 3 (.close 58)))))))) (.step 3 (.step 9 (.split 55 1 (.split 59 1 (.split 72 1 (.step 31 (.close 57)) (.step 57 (.close 3))) (.step 26 (.step 57 (.close 3)))) (.step 48 (.step 57 (.close 58))))))) (.step 3 (.close 54))) (.step 58 (.step 62 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 34 0 (.split 12 0 (.step 18 (.close 53)) (.step 21 (.step 3 (.step 18 (.close 31))))) (.step 9 (.close 31))) (.step 53 (.close 3))) (.step 3 (.close 58))) (.step 48 (.step 53 (.close 58)))) (.step 21 (.step 53 (.step 57 (.close 3))))) (.step 9 (.step 21 (.step 26 (.step 40 (.step 31 (.step 53 (.step 57 (.close 31))))))))) (.step 3 (.close 70))) (.step 3 (.close 54)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512187420787110447655700316220349906199607041105159704973109675125476471993402759331875604022082782756039164952576⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 58 (.step 62 (.split 50 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 34 0 (.split 12 0 (.step 18 (.step 3 (.close 31))) (.step 9 (.step 31 (.step 34 (.close 52))))) (.step 9 (.close 31))) (.step 52 (.close 3))) (.step 3 (.close 58))) (.step 48 (.step 52 (.close 31)))) (.step 52 (.step 57 (.close 18)))) (.step 9 (.step 26 (.step 40 (.step 57 (.step 75 (.close 31))))))) (.step 3 (.close 70))) (.step 3 (.close 54))) (.split 72 1 (.split 56 1 (.step 52 (.close 3)) (.step 31 (.close 52))) (.step 21 (.step 31 (.close 52))))))))) (.run (.step 3 (.step 46 (.step 52 (.step 53 (.step 7 (.step 9 (.step 27 (.close 46)))))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 45)) (.step 31 (.close 57))) (.step 31 (.close 53))) (.step 31 (.close 52)))))) (.run (.step 3 (.step 21 (.step 58 (.split 42 1 (.split 49 1 (.split 54 1 (.split 59 1 (.step 59 (.split 72 1 (.split 55 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.step 41 (.split 21 0 (.step 41 (.close 3)) (.step 3 (.close 22))))) (.step 3 (.close 39))) (.step 3 (.close 41))) (.step 21 (.step 31 (.close 3)))) (.step 3 (.close 41))) (.step 3 (.step 5 (.close 41)))) (.step 31 (.step 38 (.step 3 (.close 41)))))) (.step 3 (.step 31 (.close 58)))) (.step 31 (.close 57))) (.step 3 (.step 31 (.step 52 (.close 58))))) (.step 31 (.close 45))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829011145099514377603033598569163517902145605050583195821266295511733790134239232⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 57 (.split 49 1 (.split 50 1 (.step 31 (.close 39)) (.step 31 (.close 53))) (.step 31 (.close 52))))))) (.run (.step 3 (.step 9 (.step 21 (.step 38 (.step 57 (.step 3 (.split 36 1 (.split 38 1 (.step 75 (.step 58 (.split 42 1 (.split 49 1 (.step 29 (.split 56 1 (.split 59 1 (.split 17 0 (.split 21 0 (.step 38 (.close 3)) (.step 18 (.close 38))) (.step 18 (.close 38))) (.step 21 (.step 26 (.step 40 (.step 57 (.step 31 (.close 12))))))) (.step 31 (.step 38 (.close 3))))) (.step 9 (.step 21 (.step 52 (.step 40 (.step 57 (.step 58 (.split 34 0 (.step 62 (.split 36 0 (.split 38 0 (.step 52 (.close 12)) (.step 12 (.close 31))) (.step 31 (.close 26)))) (.step 15 (.step 31 (.close 26))))))))))) (.step 31 (.close 45))))) (.step 31 (.close 41))) (.step 31 (.close 39))))))))))) (.run (.step 7 (.step 75 (.split 38 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.step 37 (.close 7))) (.step 15 (.close 31))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.step 37 (.close 3)))))))) (.run (.split 35 1 (.step 3 (.step 7 (.close 52))) (.step 3 (.close 31))))) (.run (.step 7 (.step 26 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 26))) (.step 18 (.close 52))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829011145099514380894042713214571680568612321147601759693806406969188178544558080⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 35 1 (.split 38 1 (.step 57 (.split 49 1 (.split 50 1 (.split 59 1 (.split 72 1 (.step 3 (.split 56 1 (.step 18 (.step 4 (.step 3 (.close 57)))) (.step 4 (.step 18 (.close 4))))) (.step 18 (.close 31))) (.step 3 (.step 4 (.step 18 (.close 34))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 18 (.close 52))))) (.step 3 (.step 4 (.step 5 (.step 31 (.step 22 (.close 41))))))) (.step 18 (.step 31 (.close 38)))))))) (.run (.step 7 (.step 18 (.split 22 1 (.step 22 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 22))) (.step 18 (.close 52))))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 21))) (.step 18 (.close 52))))) (.step 7 (.close 18))) (.step 7 (.close 18)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252829011145099514380894042713214571680568612323806060286564838609235605292511657984⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 21 1 (.split 35 1 (.split 38 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.step 21 (.step 22 (.step 26 (.step 9 (.split 55 1 (.split 56 1 (.split 59 1 (.split 72 1 (.step 31 (.step 15 (.close 3))) (.step 15 (.close 31))) (.step 15 (.close 18))) (.step 31 (.close 15))) (.step 12 (.step 48 (.step 15 (.step 31 (.close 58))))))))))) (.step 21 (.step 15 (.step 3 (.step 4 (.close 15)))))) (.step 21 (.step 22 (.step 15 (.close 53))))) (.step 12 (.step 21 (.step 15 (.step 26 (.close 52)))))) (.step 3 (.step 16 (.step 21 (.step 31 (.step 15 (.close 59))))))) (.step 21 (.step 15 (.close 38)))) (.step 4 (.step 15 (.step 3 (.step 18 (.close 15)))))))))) (.run (.split 35 1 (.split 49 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 15))) (.step 18 (.close 52))) (.step 3 (.close 31)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part4.excludes
end FiveColour.Packed.ProjectedChunks.Case107
