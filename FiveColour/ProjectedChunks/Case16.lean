module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case16
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721538116913463296⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37630511536740859966407, 5789234131004108975754332037409142809267054969284561340134967070491198656929520178649377157723386516549331769084384324871873123416508784820466354286493168996104550163977995004790153775060025742547153916698520434934706865153, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075743702186563710326317312853837380693889657622864945658497925949331159554953215521879914385740714553999325662524165221874186812510581983176867703288015945958686720⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 55 1 (.split 52 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 3 (.close 7)) (.step 7 (.close 21))) (.step 7 (.close 31))) (.step 7 (.close 31))) (.step 7 (.close 48))) (.step 7 (.step 3 (.close 17)))) (.split 11 0 (.step 7 (.step 3 (.close 8))) (.split 16 0 (.split 25 0 (.split 4 0 (.split 10 0 (.step 8 (.close 3)) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 4))) (.step 7 (.close 8))))) (.step 7 (.close 3))) (.step 55 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 48 (.step 7 (.step 58 (.close 45)))) (.step 7 (.close 3))) (.step 3 (.step 27 (.close 48)))) (.step 7 (.close 3))) (.step 7 (.close 3))))) (.step 3 (.close 60))) (.split 57 1 (.split 59 1 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 28 (.step 3 (.split 16 0 (.step 55 (.close 7)) (.step 3 (.close 4))))) (.step 3 (.close 7))) (.step 3 (.close 59))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 5 (.close 58))) (.step 28 (.step 3 (.close 60))))) (.step 55 (.step 3 (.step 48 (.step 3 (.close 16)))))) (.step 58 (.step 5 (.close 28)))))
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320922571584929003810029806465188704760677128061677323842636205361652263093392555032085063365525799315256511304250891752885526058032269070162737647058944⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 53 1 (.reuse 0) (.run (.split 52 1 (.split 55 1 (.split 67 1 (.split 4 0 (.split 56 1 (.split 57 1 (.split 59 1 (.split 10 0 (.split 11 0 (.split 25 0 (.step 8 (.step 7 (.close 55))) (.step 3 (.close 8))) (.step 8 (.step 56 (.close 3)))) (.step 3 (.close 7))) (.step 4 (.close 48))) (.step 8 (.step 51 (.close 60)))) (.step 3 (.step 24 (.step 43 (.close 51))))) (.step 3 (.step 48 (.step 7 (.step 3 (.close 8)))))) (.step 3 (.step 7 (.close 8)))) (.step 5 (.step 18 (.step 8 (.close 58))))) (.step 3 (.step 8 (.close 48)))))) (.run (.step 7 (.step 3 (.close 54))))) (.run (.step 58 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.step 55 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 48 (.step 7 (.step 50 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.step 27 (.close 48)))) (.step 7 (.close 3))) (.step 7 (.close 3)))) (.split 5 0 (.split 11 0 (.step 53 (.step 55 (.step 7 (.close 53)))) (.step 48 (.close 7))) (.step 9 (.step 27 (.close 48))))) (.step 48 (.close 3))) (.step 5 (.step 48 (.close 58)))) (.step 4 (.step 35 (.close 48)))) (.step 3 (.step 7 (.step 48 (.close 53))))))))
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
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496087086157417190034294038011212863205740661804321282664727926293102459295356400268016838351643920678665443979118918195516332844467059949568⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 46 1 (.split 47 1 (.split 49 1 (.reuse 0) (.run (.split 50 1 (.step 58 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.step 55 (.split 67 1 (.split 4 0 (.split 5 0 (.split 10 0 (.step 48 (.step 7 (.step 49 (.close 7)))) (.step 7 (.close 3))) (.step 3 (.step 27 (.close 48)))) (.step 7 (.close 3))) (.step 7 (.close 3)))) (.split 5 0 (.split 11 0 (.step 52 (.step 55 (.step 7 (.close 52)))) (.step 48 (.close 7))) (.step 9 (.step 27 (.close 48))))) (.step 48 (.close 3))) (.step 5 (.step 16 (.close 58)))) (.step 4 (.step 48 (.close 8)))) (.step 3 (.step 7 (.step 48 (.close 52)))))) (.step 55 (.split 56 1 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 53 1 (.split 5 0 (.split 11 0 (.step 52 (.close 3)) (.step 27 (.step 48 (.close 7)))) (.step 9 (.close 52))) (.step 27 (.close 48))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 48 (.close 7)))) (.step 27 (.step 48 (.close 7)))) (.step 52 (.step 55 (.close 7)))) (.step 9 (.close 58))))))) (.run (.step 3 (.split 55 1 (.split 4 0 (.step 50 (.split 10 0 (.step 49 (.step 50 (.step 3 (.step 50 (.close 16))))) (.step 48 (.step 3 (.close 49))))) (.step 48 (.step 3 (.close 50)))) (.step 50 (.close 58)))))) (.run (.step 3 (.split 4 0 (.split 10 0 (.step 50 (.step 60 (.step 49 (.step 3 (.close 49))))) (.step 3 (.close 49))) (.step 3 (.step 49 (.close 3)))))))
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
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100830646272000, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070819612416902153342427555758679335880405010435516860832613450894501111135101152600792412192768⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 51 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 16 0 (.split 50 1 (.step 59 (.split 55 1 (.split 57 1 (.split 53 1 (.split 5 0 (.step 28 (.step 3 (.step 58 (.step 55 (.close 7))))) (.step 10 (.close 41))) (.step 3 (.step 8 (.step 24 (.close 41))))) (.step 28 (.step 3 (.close 60)))) (.step 5 (.step 28 (.close 58))))) (.step 5 (.step 21 (.close 31)))) (.step 5 (.step 41 (.step 43 (.step 50 (.step 3 (.close 41))))))) (.step 58 (.split 53 1 (.split 57 1 (.step 3 (.step 7 (.close 41))) (.step 28 (.step 3 (.close 16)))) (.step 3 (.close 41))))) (.step 58 (.split 53 1 (.split 57 1 (.step 3 (.step 7 (.close 41))) (.step 28 (.step 3 (.close 16)))) (.step 3 (.close 41))))) (.step 3 (.step 7 (.close 58)))) (.step 3 (.step 7 (.close 54)))) (.step 48 (.step 5 (.step 48 (.step 9 (.close 58)))))) (.step 21 (.step 28 (.step 41 (.step 50 (.close 3)))))) (.step 28 (.step 3 (.step 49 (.close 48))))) (.step 31 (.step 48 (.step 4 (.close 21))))) (.step 10 (.close 46))) (.step 7 (.step 28 (.step 38 (.step 41 (.step 7 (.close 31))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070819612416902153342427555758679335880405010435516860832613450894501111135101152600792412192768⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 38 1 (.split 42 1 (.split 43 1 (.split 45 1 (.reuse 0) (.run (.split 46 1 (.split 47 1 (.split 49 1 (.step 48 (.step 31 (.step 3 (.step 4 (.step 8 (.close 3)))))) (.step 48 (.close 52))) (.step 48 (.close 50))) (.step 48 (.close 49))))) (.run (.step 3 (.split 45 1 (.split 53 1 (.split 56 1 (.split 5 0 (.step 54 (.split 11 0 (.split 25 0 (.step 70 (.step 7 (.close 58))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.step 7 (.close 27)))) (.step 3 (.step 7 (.step 27 (.close 46)))))))) (.run (.step 7 (.step 31 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.close 7))) (.step 7 (.close 37))) (.step 7 (.close 45))) (.step 31 (.close 60))) (.step 7 (.step 28 (.step 31 (.close 16))))) (.step 4 (.step 7 (.step 8 (.step 28 (.close 37)))))) (.step 7 (.step 28 (.step 21 (.close 58))))) (.step 7 (.step 16 (.step 28 (.close 58))))) (.step 28 (.step 31 (.step 50 (.close 45))))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 31)))))))))) (.reuse 1))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872270360586904047501897498942679454931441228244200275717726488393041638565502944574834099537369495444127744⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.close 7))) (.step 7 (.close 37))) (.step 7 (.close 39))) (.step 28 (.step 31 (.step 3 (.close 37))))) (.step 7 (.step 28 (.step 31 (.close 16))))) (.step 4 (.step 7 (.close 56)))) (.step 3 (.step 28 (.step 31 (.close 16))))) (.step 7 (.step 22 (.close 58)))) (.step 7 (.step 22 (.close 58)))) (.step 28 (.step 31 (.step 50 (.close 39))))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 22)))))) (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.step 45 (.step 3 (.close 31))) (.step 4 (.close 39))) (.step 7 (.step 22 (.step 21 (.close 58))))) (.step 29 (.step 31 (.close 39)))) (.step 31 (.step 39 (.close 37)))) (.step 31 (.step 39 (.close 49))))) (.step 28 (.step 38 (.step 41 (.step 7 (.close 31))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719446109644165038299075671418729782048078852993514574090160780178199473234640896⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 7 (.close 31)) (.step 28 (.close 7))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 28 (.step 31 (.step 3 (.close 37))))) (.step 7 (.step 28 (.step 31 (.close 16))))) (.step 7 (.step 28 (.close 37)))) (.step 7 (.step 28 (.step 21 (.close 58))))) (.step 7 (.step 16 (.close 31)))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 50)))))) (.step 28 (.step 31 (.close 49)))) (.split 46 1 (.split 47 1 (.split 53 1 (.step 37 (.step 7 (.close 31))) (.step 7 (.close 37))) (.step 31 (.step 37 (.close 3)))) (.step 31 (.close 49)))) (.step 28 (.step 37 (.step 38 (.step 41 (.step 7 (.close 16))))))) (.split 46 1 (.split 47 1 (.split 53 1 (.step 37 (.step 7 (.close 31))) (.step 7 (.close 37))) (.step 31 (.step 37 (.close 3)))) (.step 31 (.step 37 (.close 8))))))))) (.run (.step 18 (.split 38 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 41)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895559371364629164715370542796639060337024974723973896702949596877291520⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 25 1 (.reuse 0) (.run (.split 30 1 (.split 38 1 (.split 43 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 51 1 (.step 28 (.split 52 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 50 1 (.split 53 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 5 0 (.step 28 (.close 3)) (.step 10 (.close 28))) (.step 5 (.close 28))) (.step 28 (.close 60))) (.step 5 (.step 28 (.close 48)))) (.step 5 (.step 24 (.step 43 (.close 56))))) (.step 5 (.step 28 (.close 48)))) (.step 28 (.step 3 (.close 7)))) (.step 28 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 28)))) (.step 3 (.step 28 (.close 48))))) (.step 3 (.step 7 (.close 54)))) (.step 48 (.step 5 (.step 9 (.step 16 (.step 48 (.close 58))))))) (.step 3 (.step 28 (.close 50)))) (.step 28 (.step 3 (.close 49)))) (.step 28 (.step 48 (.step 4 (.close 21))))) (.step 9 (.step 10 (.close 7)))) (.step 28 (.close 21))) (.step 28 (.step 3 (.close 7))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631854287161708843652182650314201779300857340776939520⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 22 1 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.step 8 (.step 18 (.close 3)))) (.step 8 (.step 18 (.step 3 (.close 19))))) (.step 5 (.step 7 (.close 59)))) (.step 8 (.step 36 (.step 51 (.step 7 (.close 51)))))) (.step 7 (.step 11 (.step 17 (.close 48))))) (.step 18 (.step 50 (.close 3)))) (.step 8 (.step 49 (.step 18 (.step 3 (.close 49)))))) (.step 4 (.step 18 (.close 48)))) (.step 4 (.step 5 (.step 8 (.step 28 (.step 41 (.step 7 (.step 19 (.close 20))))))))) (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 19 (.close 51)))))))) (.step 20 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 20 (.step 7 (.step 18 (.close 3)))) (.step 7 (.step 11 (.step 18 (.close 17))))) (.step 7 (.step 11 (.step 17 (.step 18 (.close 19)))))) (.step 18 (.step 19 (.close 20)))) (.step 18 (.step 20 (.close 49)))) (.step 18 (.close 20))) (.step 7 (.step 19 (.step 20 (.close 28))))) (.step 7 (.step 28 (.close 25)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174555100853999034495583876996709482496⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.step 8 (.step 18 (.close 3)))) (.step 18 (.step 3 (.close 19)))) (.step 7 (.close 19))) (.step 56 (.close 7))) (.step 3 (.step 18 (.close 19)))) (.step 7 (.step 8 (.step 18 (.close 17))))) (.step 7 (.step 18 (.close 19)))) (.step 18 (.close 50))) (.step 8 (.step 49 (.step 18 (.step 3 (.close 19)))))) (.step 4 (.step 7 (.step 18 (.close 19))))) (.step 4 (.step 5 (.step 28 (.step 41 (.close 19)))))) (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 19 (.close 49)))))))) (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 11 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.step 19 (.close 49)))) (.step 18 (.close 19))) (.step 7 (.step 19 (.close 28)))) (.step 7 (.step 19 (.close 28))))) (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.step 19 (.step 7 (.close 18))) (.step 11 (.step 18 (.close 19)))) (.step 18 (.close 19))) (.step 18 (.step 19 (.close 49)))) (.step 18 (.close 19))) (.step 7 (.step 19 (.close 28)))) (.step 7 (.step 19 (.close 28))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2596148429267413814265250312093696, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486909523727777813070819612416902153342427555758679335880405010435516860832613452192575325768808059733416494497792⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 30 0 (.split 45 1 (.split 50 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 25 0 (.step 8 (.step 3 (.step 55 (.close 3)))) (.step 3 (.step 14 (.close 3)))) (.step 4 (.close 48))) (.step 8 (.close 60))) (.step 3 (.step 24 (.step 43 (.close 59))))) (.step 8 (.step 14 (.close 3)))) (.step 4 (.step 34 (.step 14 (.close 48))))) (.step 4 (.step 8 (.step 14 (.close 48))))) (.step 3 (.step 48 (.step 8 (.step 7 (.close 14)))))) (.step 3 (.step 48 (.step 14 (.step 7 (.step 3 (.close 8))))))) (.step 48 (.split 56 1 (.split 57 1 (.step 3 (.step 7 (.close 14))) (.step 3 (.close 14))) (.step 3 (.close 14))))) (.step 3 (.step 7 (.close 48)))) (.step 5 (.step 18 (.step 30 (.step 8 (.close 58)))))) (.step 3 (.step 8 (.step 14 (.close 48))))) (.step 3 (.step 7 (.close 48)))) (.step 4 (.step 34 (.step 48 (.step 49 (.step 27 (.close 34))))))) (.step 8 (.step 14 (.step 49 (.step 50 (.close 3)))))) (.step 8 (.step 14 (.step 34 (.step 49 (.close 3)))))) (.step 8 (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 14 (.step 7 (.step 28 (.step 37 (.close 39)))))))))) (.step 4 (.step 43 (.step 24 (.step 49 (.step 50 (.step 59 (.step 60 (.split 42 1 (.step 24 (.step 8 (.step 3 (.close 14)))) (.step 3 (.close 41))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556398928213668202491009620791787520⟩
def references : Fin 4 → Box := ![Part7.root, Part8.root, Part9.root, Part10.root]
def proof : Chunks.Proof 4 := (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 25 1 (.split 38 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 7 (.step 8 (.step 18 (.close 3)))) (.step 18 (.close 60))) (.step 5 (.step 7 (.close 59)))) (.step 56 (.close 7))) (.step 3 (.step 8 (.step 18 (.close 19))))) (.step 7 (.step 8 (.step 18 (.close 17))))) (.step 7 (.step 11 (.step 17 (.close 48))))) (.step 18 (.step 50 (.close 3)))) (.step 8 (.step 49 (.step 18 (.step 3 (.close 49)))))) (.step 4 (.step 8 (.step 18 (.close 25))))) (.step 4 (.step 5 (.step 8 (.step 28 (.step 41 (.step 7 (.step 19 (.close 20))))))))) (.step 4 (.step 5 (.step 8 (.step 24 (.step 28 (.step 25 (.close 49)))))))))))) (.reuse 1)) (.reuse 2)) (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 3) (.run (.step 5 (.step 4 (.step 7 (.step 28 (.step 14 (.step 24 (.step 8 (.step 7 (.step 37 (.close 56)))))))))))) (.run (.step 3 (.step 5 (.step 4 (.step 7 (.step 14 (.step 28 (.step 37 (.step 14 (.close 37))))))))))) (.run (.step 3 (.step 31 (.step 7 (.close 14)))))) (.run (.step 5 (.step 28 (.step 24 (.step 43 (.step 24 (.step 8 (.step 14 (.step 28 (.close 14))))))))))) (.run (.step 7 (.step 8 (.step 17 (.step 14 (.step 7 (.step 18 (.close 3))))))))) (.run (.step 7 (.step 8 (.step 17 (.step 14 (.step 7 (.step 18 (.close 14))))))))) (.run (.step 7 (.step 8 (.step 17 (.step 14 (.step 7 (.step 18 (.step 19 (.close 3)))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2251801961168896, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721537017401835520⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 1 (.split 25 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 51 1 (.step 8 (.split 52 1 (.split 55 1 (.split 67 1 (.split 4 0 (.split 10 0 (.split 45 1 (.split 50 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 25 0 (.step 8 (.close 3)) (.step 3 (.close 47))) (.step 4 (.close 8))) (.step 8 (.close 60))) (.step 3 (.step 24 (.step 10 (.step 8 (.close 59)))))) (.step 4 (.step 8 (.close 48)))) (.step 8 (.close 48))) (.step 8 (.step 3 (.close 7)))) (.step 8 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 8)))) (.step 5 (.step 18 (.step 30 (.close 58))))) (.step 3 (.step 8 (.close 48))))) (.step 3 (.step 7 (.close 48)))) (.step 4 (.step 48 (.step 8 (.close 44))))) (.step 3 (.step 8 (.close 50)))) (.step 8 (.step 3 (.close 49)))) (.step 8 (.step 3 (.step 7 (.close 27))))) (.step 3 (.step 4 (.step 7 (.step 8 (.step 28 (.step 45 (.close 49)))))))) (.step 3 (.step 8 (.step 43 (.step 24 (.step 10 (.step 8 (.close 41)))))))) (.step 5 (.step 4 (.step 8 (.step 28 (.step 24 (.step 8 (.step 3 (.step 41 (.step 39 (.step 45 (.close 49)))))))))))) (.step 3 (.step 5 (.step 4 (.step 7 (.step 28 (.step 41 (.step 24 (.step 8 (.step 37 (.close 49))))))))))) (.step 8 (.step 3 (.close 7)))) (.step 5 (.step 8 (.step 28 (.step 24 (.step 10 (.step 8 (.close 28)))))))) (.step 8 (.step 7 (.close 34)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨2147483648, 9797766621314684873895708907333611310075747216966320925768258496089993515089749841225217486911872272600331646227343144032719447918895561056361295861631855748663346174556400195864268430721538116913463296⟩
def references : Fin 2 → Box := ![Part11.root, Part12.root]
def proof : Chunks.Proof 2 := (.split 4 1 (.split 5 1 (.split 10 1 (.reuse 0) (.run (.step 18 (.step 31 (.split 11 1 (.split 25 1 (.split 38 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 41)))) (.step 28 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 14)))))))) (.reuse 1)) (.run (.step 18 (.step 31 (.split 5 1 (.split 11 1 (.split 25 1 (.split 38 1 (.step 3 (.step 7 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 41)))) (.step 28 (.step 3 (.close 7)))) (.step 3 (.step 7 (.close 14)))) (.step 8 (.step 3 (.close 7))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part13.excludes
end FiveColour.Packed.ProjectedChunks.Case16
