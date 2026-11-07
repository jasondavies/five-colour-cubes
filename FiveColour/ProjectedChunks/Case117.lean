module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case117
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848990635548761507172873080143725624441185932164455731511631966480970596411198406656⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908392998381874375671, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859361899508584915508177230179531154389992449, 0⟩]
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128988695900350277731064209002701788242648331369876354823354484790699718829960818484103785166563613095512676814996086566935602539806631619203841392640000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.step 18 (.close 21))) (.split 34 0 (.split 36 0 (.step 26 (.step 3 (.close 18))) (.step 3 (.close 26))) (.step 29 (.step 75 (.close 3))))) (.step 3 (.close 7))) (.step 26 (.split 67 1 (.split 16 0 (.split 12 0 (.split 21 0 (.step 62 (.close 7)) (.step 3 (.close 18))) (.step 26 (.step 3 (.close 62)))) (.step 18 (.close 62))) (.step 26 (.close 70))))) (.step 9 (.split 59 1 (.split 72 1 (.step 3 (.split 42 0 (.step 57 (.close 18)) (.step 26 (.close 31)))) (.step 57 (.close 3))) (.step 26 (.step 57 (.close 3)))))) (.step 57 (.step 3 (.close 54)))) (.split 51 1 (.split 67 1 (.split 72 1 (.split 59 1 (.split 10 0 (.split 54 1 (.split 12 0 (.step 53 (.close 7)) (.step 21 (.step 3 (.step 15 (.step 18 (.close 26)))))) (.step 21 (.step 57 (.close 3)))) (.split 54 1 (.step 18 (.close 53)) (.step 3 (.close 53)))) (.step 53 (.close 7))) (.step 9 (.step 21 (.step 26 (.step 40 (.step 53 (.step 57 (.close 53)))))))) (.step 3 (.step 53 (.close 7)))) (.step 3 (.step 53 (.close 54))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188638416187803805131271556139646498065454463049500650281600760180153731293638219987598547951287284563915571200⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.split 51 1 (.split 67 1 (.split 72 1 (.split 50 1 (.split 59 1 (.split 54 1 (.split 12 0 (.split 21 0 (.split 34 0 (.split 35 0 (.step 7 (.close 52)) (.step 3 (.step 18 (.close 21)))) (.step 9 (.close 31))) (.step 3 (.close 18))) (.split 35 0 (.step 3 (.step 18 (.close 31))) (.step 15 (.step 21 (.step 3 (.step 18 (.close 26))))))) (.step 57 (.close 52))) (.step 52 (.close 7))) (.step 52 (.close 7))) (.step 9 (.step 26 (.step 52 (.step 40 (.step 52 (.step 57 (.close 52)))))))) (.step 3 (.step 52 (.close 7)))) (.step 3 (.step 52 (.close 54)))))) (.run (.step 9 (.step 3 (.step 46 (.step 52 (.step 53 (.step 62 (.split 49 1 (.step 7 (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46)))))))))))) (.run (.step 7 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 7)) (.step 31 (.close 57))) (.step 31 (.close 53))) (.step 31 (.close 52))))))) (.run (.step 7 (.step 75 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.close 7)) (.step 31 (.close 57))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 39)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848990635548761507169582071029080216278519465445700254420888394167246724908820987904⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.step 9 (.step 21 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 54 1 (.step 3 (.split 72 1 (.split 21 0 (.split 34 0 (.split 36 0 (.split 12 0 (.step 3 (.close 18)) (.step 21 (.step 3 (.close 17)))) (.step 3 (.close 38))) (.step 29 (.step 38 (.close 3)))) (.step 18 (.close 38))) (.step 29 (.close 38)))) (.step 38 (.step 57 (.close 3)))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 40 (.step 31 (.step 57 (.close 38))))))))) (.step 3 (.step 9 (.step 21 (.step 57 (.step 62 (.step 40 (.step 75 (.split 36 0 (.step 52 (.close 26)) (.step 31 (.close 38))))))))))) (.step 31 (.step 3 (.close 38)))) (.step 31 (.step 3 (.close 39))))))))) (.run (.step 7 (.step 38 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.step 7 (.close 37))) (.step 15 (.step 31 (.close 52)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.close 37)))))))) (.run (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 31))) (.step 3 (.close 18))) (.step 18 (.close 52))) (.step 3 (.close 31))))) (.run (.step 7 (.step 26 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 26))) (.step 18 (.close 52)))) (.step 18 (.close 26)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848990635548761507172873080143725624441185932164455731511631966480970596411198406656⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.step 57 (.split 59 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 3 (.step 18 (.close 31))) (.step 3 (.step 18 (.close 34)))) (.step 18 (.close 52))) (.step 18 (.close 38))) (.step 18 (.close 62))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.step 22 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 22))) (.step 18 (.close 52)))) (.step 18 (.close 22)))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 21))) (.step 18 (.close 52)))) (.step 18 (.close 21)))) (.step 7 (.close 18))) (.step 18 (.close 19))))))) (.run (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.split 72 1 (.step 3 (.step 18 (.step 9 (.step 15 (.step 3 (.close 15)))))) (.step 21 (.step 22 (.step 15 (.close 18)))))) (.step 21 (.step 22 (.step 15 (.close 62))))) (.step 21 (.step 15 (.step 3 (.step 15 (.close 18)))))) (.step 21 (.step 15 (.close 53)))) (.step 21 (.step 22 (.step 15 (.step 26 (.close 52)))))) (.step 21 (.step 15 (.close 38))))))) (.run (.split 12 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 15))) (.step 3 (.close 18))) (.step 18 (.close 52))) (.step 3 (.close 31))) (.step 3 (.close 15)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part3.excludes
end FiveColour.Packed.ProjectedChunks.Case117
