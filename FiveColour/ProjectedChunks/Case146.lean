module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case146
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686465314963165146820842286981650510269619360326650879354991314816729869574801059769041884766471428885447232557582473825883143056870817655214082533393246144821475232903593984⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
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
def root : Box := ⟨4294967296, 11031304526203979496340767072204264539074732142412851534956501608025710084481509692846403711945387603264584046484810526375325986300065434754055115263912606837801201120430714496250290951780093664031356205762311339638784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.step 31 (.step 18 (.step 3 (.step 26 (.step 3 (.close 12)))))) (.step 26 (.split 16 0 (.split 17 0 (.step 26 (.step 3 (.step 26 (.step 3 (.close 31))))) (.step 3 (.close 18))) (.step 3 (.close 18))))) (.step 31 (.step 3 (.close 12)))) (.split 56 1 (.split 16 0 (.split 17 0 (.step 62 (.split 21 0 (.split 22 0 (.step 9 (.step 21 (.step 31 (.close 3)))) (.step 3 (.close 26))) (.step 3 (.close 40)))) (.step 3 (.close 53))) (.step 18 (.close 21))) (.step 3 (.close 58)))) (.split 56 1 (.split 16 0 (.split 17 0 (.split 54 1 (.split 21 0 (.split 22 0 (.step 52 (.step 12 (.step 26 (.close 52)))) (.step 3 (.close 26))) (.step 3 (.close 40))) (.step 12 (.step 52 (.step 31 (.close 57))))) (.step 3 (.step 12 (.close 52)))) (.step 3 (.step 12 (.step 18 (.close 21))))) (.step 31 (.close 52)))) (.step 31 (.close 12))) (.step 31 (.step 3 (.step 21 (.close 57))))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 18 (.close 12))) (.step 12 (.step 21 (.step 22 (.step 26 (.step 57 (.split 38 1 (.split 50 1 (.split 59 1 (.step 31 (.step 12 (.step 3 (.step 15 (.close 3))))) (.step 15 (.close 3))) (.step 12 (.step 15 (.close 3)))) (.step 21 (.step 15 (.step 31 (.close 3))))))))))) (.step 31 (.close 12))))
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
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284818158823375278551857746471140503401077625136286468690110927404584493540839407166326609879634836315882805063891138855479254072802206490651442261963209911261410710159097856⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 59 2 (.split 72 2 (.step 3 (.split 55 1 (.split 21 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.step 18 (.step 21 (.step 29 (.step 31 (.step 38 (.split 12 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.step 21 (.step 31 (.step 12 (.step 26 (.close 31)))))) (.step 18 (.close 38))) (.step 18 (.close 38))) (.step 18 (.close 21))) (.step 15 (.close 3)))))))))) (.run (.step 31 (.close 12)))) (.run (.step 18 (.step 31 (.split 38 1 (.step 18 (.step 57 (.step 3 (.step 4 (.step 15 (.step 18 (.close 15))))))) (.step 3 (.close 4))))))) (.run (.step 18 (.step 31 (.split 12 1 (.step 58 (.split 21 1 (.split 16 0 (.step 58 (.step 48 (.step 52 (.step 9 (.step 53 (.step 31 (.step 57 (.close 58)))))))) (.step 3 (.close 48))) (.step 4 (.close 5)))) (.step 9 (.step 12 (.step 48 (.step 15 (.close 58))))))))))) (.run (.step 29 (.step 31 (.step 38 (.split 55 1 (.split 12 1 (.step 3 (.step 18 (.step 75 (.step 18 (.close 12))))) (.step 15 (.close 75))) (.step 18 (.close 75)))))))) (.run (.step 26 (.split 12 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 18 (.split 56 1 (.split 16 0 (.split 17 0 (.step 62 (.close 31)) (.step 3 (.close 62))) (.step 3 (.close 62))) (.step 3 (.close 58)))) (.step 57 (.close 62))) (.step 53 (.close 31))) (.step 52 (.close 3))) (.step 31 (.close 62))) (.step 3 (.step 31 (.close 62)))) (.step 31 (.close 62))) (.step 15 (.step 31 (.close 52)))) (.step 18 (.close 21))) (.step 15 (.close 62))))))
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
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284825706755423183705837890574015133834897056332312472158555179714238279834922098175841354993188466080293879912265725648496988819536854686067516698847218171728988928173146112⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 50 2 (.split 54 2 (.split 56 2 (.reuse 0) (.run (.step 31 (.step 58 (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 21 1 (.step 31 (.step 3 (.step 5 (.close 58)))) (.step 3 (.close 59))) (.step 5 (.close 18))) (.step 5 (.close 18))) (.step 5 (.close 18))) (.step 4 (.step 31 (.step 15 (.step 3 (.close 58)))))))))) (.run (.step 21 (.step 22 (.step 26 (.step 32 (.step 57 (.step 31 (.close 57))))))))) (.run (.step 21 (.step 57 (.step 58 (.step 53 (.split 72 2 (.split 12 1 (.split 16 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 54 1 (.split 56 1 (.step 62 (.step 18 (.split 72 1 (.split 17 0 (.split 21 0 (.step 53 (.close 21)) (.step 3 (.close 53))) (.step 3 (.close 53))) (.step 21 (.step 26 (.step 18 (.close 53))))))) (.step 31 (.close 53))) (.step 26 (.step 32 (.step 53 (.close 31))))) (.step 52 (.close 3))) (.step 31 (.close 53))) (.step 31 (.close 53))) (.step 15 (.step 31 (.close 52)))) (.step 18 (.close 21))) (.step 15 (.close 53))) (.step 9 (.step 15 (.step 32 (.step 40 (.step 53 (.step 57 (.step 75 (.close 12)))))))))))))))
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
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284825706755423183705837896967356164882049146201823598774964699138141825322684550015407326257675422150582678099486118259204076470083846774034707172006532977366498063954214912⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 38 2 (.split 49 2 (.reuse 0) (.run (.step 12 (.step 57 (.step 58 (.step 52 (.split 72 2 (.split 16 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 50 1 (.split 54 1 (.split 56 1 (.step 62 (.step 18 (.split 72 1 (.split 16 0 (.split 17 0 (.step 52 (.close 31)) (.step 3 (.close 52))) (.step 3 (.close 52))) (.step 12 (.step 26 (.step 18 (.close 52))))))) (.step 31 (.close 52))) (.step 52 (.close 57))) (.step 52 (.close 3))) (.step 31 (.close 52))) (.step 3 (.step 31 (.close 52)))) (.step 31 (.close 52))) (.step 9 (.step 12 (.step 21 (.step 31 (.step 32 (.step 52 (.step 40 (.step 52 (.step 26 (.step 38 (.close 3)))))))))))) (.step 31 (.close 52))) (.step 18 (.close 21))) (.step 9 (.step 12 (.step 31 (.step 40 (.step 52 (.step 57 (.close 75)))))))))))))) (.run (.step 21 (.step 41 (.step 58 (.split 54 2 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 49 1 (.step 41 (.step 31 (.step 3 (.step 5 (.close 58))))) (.step 31 (.close 58))) (.step 5 (.close 18))) (.step 3 (.step 5 (.step 18 (.step 31 (.step 22 (.close 41))))))) (.step 5 (.close 18))) (.step 5 (.close 18))) (.step 3 (.step 10 (.step 12 (.step 21 (.step 31 (.step 15 (.step 41 (.close 15))))))))) (.step 31 (.close 57))))))))
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
def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686465314963165146820842286981650510269619360326650879354991314816729869574801059769041884766471428885447232557582473825883143056870817655214082533393246144821475232903593984⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.step 3 (.split 12 2 (.step 18 (.step 58 (.split 21 2 (.split 35 2 (.reuse 0) (.run (.step 21 (.step 29 (.step 31 (.step 38 (.step 57 (.split 49 2 (.split 59 2 (.split 55 1 (.split 12 1 (.step 3 (.step 18 (.step 38 (.step 18 (.step 12 (.step 3 (.close 18))))))) (.step 15 (.close 38))) (.step 31 (.close 38))) (.step 3 (.step 26 (.step 40 (.step 52 (.step 38 (.close 62))))))) (.step 12 (.step 40 (.step 52 (.step 57 (.step 38 (.close 3)))))))))))))) (.run (.step 3 (.step 31 (.step 57 (.split 35 2 (.split 49 2 (.split 50 2 (.split 59 2 (.step 24 (.step 57 (.split 72 2 (.split 35 1 (.split 38 2 (.split 56 2 (.split 12 1 (.step 3 (.step 4 (.step 24 (.step 18 (.step 12 (.close 52)))))) (.step 4 (.close 15))) (.step 4 (.close 59))) (.step 24 (.close 41))) (.step 4 (.step 18 (.close 38)))) (.step 18 (.step 31 (.close 75)))))) (.step 4 (.step 15 (.step 18 (.step 52 (.step 53 (.step 24 (.close 62)))))))) (.step 4 (.step 15 (.step 18 (.step 53 (.close 24)))))) (.step 4 (.step 12 (.step 18 (.close 52))))) (.step 15 (.step 18 (.step 31 (.step 38 (.close 24))))))))))))) (.run (.step 15 (.step 18 (.step 21 (.step 15 (.step 3 (.step 22 (.step 24 (.step 26 (.step 31 (.step 58 (.split 38 2 (.split 38 1 (.step 15 (.step 4 (.step 31 (.step 15 (.close 58))))) (.step 31 (.step 15 (.close 41)))) (.step 4 (.step 31 (.step 15 (.step 41 (.close 15)))))))))))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case146
