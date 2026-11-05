module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
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
def root : Box := ⟨4294967296, 11031304526203979496340767072204264539074732142412851534956501608025710084481509692846403709237702355099725780480680259125429351383958659753685186322626043577195338801916037430219902529343200531151165794902513448648704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 1 (.split 22 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.step 31 (.step 9 (.step 18 (.step 3 (.step 18 (.step 26 (.step 3 (.close 12)))))))) (.step 26 (.split 16 0 (.split 17 0 (.step 26 (.step 3 (.step 26 (.step 3 (.close 31))))) (.step 3 (.step 4 (.close 18)))) (.step 3 (.close 18))))) (.step 31 (.step 3 (.close 12)))) (.split 56 1 (.split 16 0 (.split 17 0 (.step 62 (.split 21 0 (.split 22 0 (.step 9 (.step 21 (.step 18 (.step 31 (.close 3))))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 4 (.step 18 (.close 12)))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 12))))))) (.split 56 1 (.split 16 0 (.split 17 0 (.step 62 (.split 54 1 (.split 21 0 (.split 22 0 (.step 52 (.step 9 (.step 12 (.step 18 (.step 26 (.step 3 (.step 16 (.close 21)))))))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 4 (.step 12 (.step 4 (.close 18)))))) (.step 9 (.step 12 (.step 52 (.step 18 (.step 31 (.step 3 (.step 18 (.step 26 (.step 3 (.close 21)))))))))))) (.step 3 (.step 12 (.step 18 (.step 21 (.close 26)))))) (.step 3 (.step 12 (.step 18 (.close 21))))) (.step 3 (.step 12 (.step 16 (.step 22 (.step 31 (.step 21 (.close 52))))))))) (.step 31 (.close 12))) (.step 21 (.step 31 (.step 3 (.step 12 (.step 21 (.step 12 (.close 52)))))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 12)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 11031304526203979496340767072204264539074732142412851534956501608025710084481509692846403709237702355099725782831518580259994828589260634880604869083383280765685282603687001447523329101408013416350018430681193335750656⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 3 (.step 18 (.close 12))))) (.run (.step 12 (.step 21 (.step 22 (.step 26 (.step 9 (.step 57 (.step 31 (.split 38 1 (.split 50 1 (.split 59 1 (.step 31 (.step 12 (.step 3 (.step 15 (.close 3))))) (.step 12 (.step 15 (.close 3)))) (.step 12 (.step 15 (.close 3)))) (.step 12 (.step 21 (.step 15 (.step 31 (.close 3))))))))))))))) (.run (.step 3 (.step 31 (.close 12))))) (.run (.step 18 (.step 21 (.step 29 (.step 31 (.step 38 (.split 12 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 32 (.step 21 (.step 31 (.step 12 (.step 26 (.step 3 (.close 31))))))) (.step 3 (.step 18 (.step 21 (.step 26 (.close 3)))))) (.step 3 (.step 18 (.step 21 (.step 31 (.close 12)))))) (.step 3 (.step 18 (.step 21 (.step 22 (.step 3 (.close 12))))))) (.step 3 (.step 18 (.close 21)))) (.step 12 (.step 15 (.close 3))))))))))) (.run (.step 3 (.step 31 (.close 12))))) (.run (.step 18 (.step 31 (.split 38 1 (.step 18 (.step 4 (.step 57 (.step 3 (.step 4 (.step 15 (.step 18 (.close 15)))))))) (.step 3 (.close 4)))))))
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
def root : Box := ⟨12156783893206034058141819913157698684606776071022764355456027333078084408436254335155391744962218147328704745931545280807798294166245435472324828615568252989437056064657154899968, 22062609052407958992681534144408529078149464284818158823375278551857746471140503401077625133578783441946069140928903616618601581495773143981522845872922927893355629218496928780921495783888831602831927544653059905814528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 26 (.step 58 (.split 12 1 (.split 16 1 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 18 (.step 62 (.split 56 1 (.split 16 0 (.split 17 0 (.step 62 (.step 3 (.close 15))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 22 (.step 26 (.step 31 (.step 12 (.close 21))))))))) (.step 9 (.step 22 (.step 26 (.step 57 (.step 3 (.step 18 (.step 12 (.step 21 (.step 32 (.close 48))))))))))) (.step 53 (.step 3 (.close 21)))) (.step 52 (.close 3))) (.step 3 (.step 26 (.step 31 (.step 12 (.step 52 (.step 12 (.close 53)))))))) (.step 3 (.step 21 (.step 26 (.step 31 (.step 52 (.step 57 (.step 12 (.step 57 (.step 12 (.step 41 (.close 58)))))))))))) (.step 3 (.step 22 (.step 26 (.step 31 (.step 12 (.step 52 (.step 12 (.close 53))))))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 31 (.step 32 (.step 40 (.step 52 (.step 31 (.step 57 (.step 12 (.step 18 (.step 31 (.close 12))))))))))))))) (.step 3 (.step 15 (.step 26 (.step 31 (.close 52)))))) (.step 3 (.step 18 (.step 48 (.step 12 (.step 52 (.step 12 (.close 53)))))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 9 (.step 12 (.step 15 (.step 18 (.step 21 (.step 3 (.step 26 (.step 3 (.step 32 (.step 48 (.close 53))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284818158823375278551857746471140503401077625133578783441946069140928903616618601581495773143981522845872922927893355629218496928780921495783888831602831927544653059905814528⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 59 2 (.split 72 2 (.step 3 (.split 55 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 12 1 (.step 58 (.split 21 1 (.step 58 (.split 16 0 (.step 58 (.step 48 (.step 52 (.step 9 (.step 53 (.step 31 (.step 57 (.step 18 (.step 12 (.close 21)))))))))) (.step 3 (.step 4 (.step 18 (.step 12 (.close 21))))))) (.step 3 (.step 4 (.close 5))))) (.step 4 (.step 9 (.step 12 (.step 15 (.step 48 (.step 15 (.step 31 (.step 53 (.step 15 (.close 31)))))))))))))))) (.run (.step 9 (.step 26 (.step 29 (.step 31 (.step 38 (.split 55 1 (.split 12 1 (.step 3 (.step 18 (.step 75 (.step 18 (.close 12))))) (.step 12 (.step 15 (.step 18 (.step 26 (.step 3 (.step 21 (.close 22)))))))) (.step 3 (.step 4 (.step 18 (.step 31 (.step 15 (.step 26 (.step 52 (.step 53 (.step 57 (.step 12 (.close 21))))))))))))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨9820171823688425610039569090482797456649926138129194368449874104288401389214023664649810276977712471452660052382680213027651769637656179159989877735424, 22062609052407958992681534144408529078149464284825706755423183705837890574015133834897056329604786910390321450582689910701292591010518257535152610283997776267942422236231675515569691199963268486840188012231277919862784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 21 (.step 53 (.step 57 (.step 58 (.step 53 (.split 72 2 (.split 12 1 (.split 16 1 (.split 21 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 54 1 (.split 55 1 (.split 56 1 (.step 62 (.step 18 (.split 72 1 (.split 16 0 (.split 17 0 (.split 21 0 (.step 53 (.step 3 (.step 15 (.step 16 (.close 21))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.close 12)))) (.step 9 (.step 21 (.step 26 (.step 18 (.step 31 (.close 3))))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 12 (.close 53))))))) (.step 18 (.step 32 (.step 48 (.close 53))))) (.step 9 (.step 21 (.step 22 (.step 26 (.step 32 (.step 53 (.step 3 (.step 15 (.step 22 (.step 15 (.close 26)))))))))))) (.step 52 (.close 3))) (.step 3 (.step 21 (.step 26 (.step 31 (.step 12 (.step 52 (.step 12 (.close 53))))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 12 (.step 52 (.step 12 (.close 53))))))))) (.step 3 (.step 15 (.step 21 (.step 31 (.close 52)))))) (.step 3 (.step 18 (.step 48 (.step 12 (.step 52 (.step 12 (.close 53)))))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 9 (.step 12 (.step 15 (.step 18 (.step 21 (.step 3 (.step 26 (.step 3 (.step 32 (.step 48 (.close 53)))))))))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 31 (.step 32 (.step 40 (.step 52 (.step 53 (.step 57 (.step 75 (.close 12)))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨9590011546570728134804266689924606891259693494266791375439330179969141981654319985009580348611047335402988332404961145534816181286773612465218387968, 22062609052407958992681534144408529078149464284825706755423183705837896967356164882049146199115913526794915623711686088562209550563971570296473713163987782654841496267788610841124627840726958364294379194639585202143232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 12 (.step 52 (.step 57 (.step 58 (.step 52 (.split 72 2 (.split 16 1 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.step 62 (.step 18 (.split 72 1 (.split 16 0 (.split 17 0 (.step 52 (.step 3 (.close 12))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 12 (.close 18)))) (.step 9 (.step 12 (.step 26 (.step 18 (.step 31 (.close 3))))))))) (.step 3 (.step 12 (.step 16 (.step 22 (.step 31 (.step 21 (.close 52)))))))) (.step 12 (.step 18 (.step 48 (.close 52))))) (.step 9 (.step 12 (.step 22 (.step 26 (.step 52 (.step 18 (.step 22 (.step 26 (.step 22 (.close 31))))))))))) (.step 52 (.close 3))) (.step 3 (.step 26 (.step 31 (.step 12 (.close 52)))))) (.step 3 (.step 12 (.step 21 (.step 16 (.step 31 (.close 52))))))) (.step 3 (.step 22 (.step 31 (.step 12 (.close 52)))))) (.step 9 (.step 12 (.step 18 (.step 21 (.step 31 (.step 32 (.step 52 (.step 40 (.step 52 (.step 26 (.step 31 (.step 38 (.close 3)))))))))))))) (.step 3 (.step 15 (.step 16 (.step 31 (.close 52)))))) (.step 3 (.step 12 (.step 18 (.step 4 (.step 48 (.close 52))))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 9 (.step 12 (.step 18 (.step 26 (.step 31 (.step 38 (.step 40 (.step 52 (.step 57 (.close 75))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284825706755423183705837896967356164882049146199115913526794915623711686088562209550563971570296473713163987782654841496267788610841124627840726958364294379194639585202143232⟩
def references : Fin 3 → Box := ![Part3.root, Part4.root, Part5.root]
def proof : Chunks.Proof 3 := (.split 49 2 (.split 50 2 (.split 54 2 (.split 56 2 (.reuse 0) (.run (.step 3 (.step 31 (.step 58 (.split 12 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 49 1 (.split 50 1 (.split 21 1 (.step 31 (.step 3 (.step 5 (.step 57 (.step 12 (.step 21 (.step 12 (.close 41)))))))) (.step 3 (.step 4 (.step 5 (.step 22 (.step 4 (.step 21 (.step 3 (.close 4))))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 53)))))) (.step 3 (.step 12 (.step 16 (.step 22 (.step 31 (.step 52 (.step 21 (.step 57 (.step 41 (.close 58))))))))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 4 (.step 10 (.step 12 (.step 22 (.step 31 (.step 15 (.step 3 (.step 15 (.step 21 (.close 41))))))))))))))))) (.run (.step 9 (.step 12 (.step 21 (.step 15 (.step 22 (.step 26 (.step 32 (.step 57 (.step 31 (.step 41 (.close 57))))))))))))) (.reuse 1)) (.reuse 2))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284825706755423183705837896967356164882049146199115913526799840874490822395695724573599711163812712854454389093466671595190794503741335624919330711262295030755960665074040832⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 35 2 (.split 38 2 (.reuse 0) (.run (.step 3 (.step 21 (.step 31 (.step 41 (.step 58 (.split 54 2 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 49 1 (.step 41 (.step 31 (.step 3 (.step 5 (.step 21 (.step 41 (.close 12))))))) (.step 3 (.step 12 (.step 16 (.step 21 (.step 31 (.step 41 (.step 52 (.close 57))))))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 4 (.step 5 (.step 18 (.step 21 (.step 31 (.step 22 (.step 32 (.close 41)))))))))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 5 (.close 18)))) (.step 3 (.step 4 (.step 10 (.step 12 (.step 21 (.step 31 (.step 15 (.step 41 (.close 15)))))))))) (.step 3 (.step 4 (.step 9 (.step 15 (.step 21 (.step 31 (.step 41 (.step 48 (.close 57))))))))))))))))) (.run (.step 9 (.step 21 (.step 29 (.step 31 (.step 38 (.step 57 (.split 49 2 (.split 59 2 (.split 55 1 (.split 12 1 (.step 3 (.step 18 (.step 38 (.step 18 (.step 12 (.step 3 (.close 18))))))) (.step 12 (.step 15 (.step 18 (.step 21 (.close 31)))))) (.step 3 (.step 4 (.step 18 (.step 31 (.step 15 (.step 21 (.close 38)))))))) (.step 3 (.step 15 (.step 18 (.step 21 (.step 26 (.step 32 (.step 40 (.step 52 (.step 38 (.step 57 (.step 18 (.step 12 (.step 38 (.close 58))))))))))))))) (.step 3 (.step 12 (.step 18 (.step 21 (.step 32 (.step 40 (.step 52 (.step 57 (.step 38 (.close 3)))))))))))))))))))
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
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284825710440933364195624373765749310378405484985171792839729946710629787479313070659682574529170842910761780958969557397730009078850192656913037905738602997068790021729812480⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.step 18 (.step 58 (.split 21 2 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 57 (.split 35 2 (.split 49 2 (.split 50 2 (.split 59 2 (.step 24 (.step 57 (.step 58 (.split 72 2 (.split 35 1 (.split 38 2 (.split 56 2 (.step 4 (.split 12 1 (.step 3 (.step 4 (.step 18 (.step 24 (.step 18 (.step 12 (.close 52))))))) (.step 4 (.step 9 (.step 12 (.close 15)))))) (.step 3 (.step 4 (.step 5 (.step 3 (.step 22 (.close 31))))))) (.step 3 (.step 4 (.step 5 (.step 8 (.step 21 (.step 24 (.step 4 (.step 22 (.step 4 (.step 32 (.close 41)))))))))))) (.step 4 (.step 9 (.step 15 (.step 18 (.step 15 (.close 24))))))) (.step 4 (.step 9 (.step 15 (.step 18 (.step 24 (.step 26 (.step 31 (.step 38 (.close 57))))))))))))) (.step 3 (.step 4 (.step 15 (.step 18 (.step 52 (.step 53 (.step 12 (.step 24 (.step 12 (.close 57))))))))))) (.step 3 (.step 4 (.step 15 (.step 18 (.step 52 (.step 53 (.close 24)))))))) (.step 3 (.step 4 (.step 12 (.step 18 (.close 52)))))) (.step 4 (.step 9 (.step 15 (.step 18 (.step 31 (.step 38 (.close 24))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686465314963165146820842286981650510269619360326650879354991314816729869574801059769041884766471428885447232557582473825883143056870817655214082533393246144821475232903593984⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.split 12 2 (.reuse 0) (.run (.step 9 (.step 12 (.step 15 (.step 18 (.step 9 (.step 21 (.step 15 (.step 3 (.step 22 (.step 24 (.step 26 (.step 31 (.step 58 (.split 38 2 (.split 38 1 (.step 15 (.step 4 (.step 22 (.step 15 (.step 31 (.step 15 (.close 58))))))) (.step 4 (.step 21 (.step 15 (.step 22 (.step 15 (.step 31 (.step 15 (.close 41))))))))) (.step 4 (.step 21 (.step 31 (.step 15 (.step 41 (.close 15))))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part9.excludes
end FiveColour.Packed.ProjectedChunks.Case146
