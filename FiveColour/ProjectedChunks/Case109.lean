module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case109
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848990635548761507172873080143725624441185932164455731511631966484429360925018947584⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908392998381874375607, 5789234131009374243490890256636772759901851996560544808214778193549775928795277575978058672488451386148482820637016487820419584261128081612316866307095117301248629629600134054099986201414770618195247788012495054996921910273, 0⟩]
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678183941331022256138675492594946067824010703097951684010540186178237089313243409003100671149955670668662458548224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.close 18))) (.step 29 (.step 75 (.close 18)))) (.step 3 (.close 7))) (.step 26 (.split 67 1 (.split 12 0 (.split 21 0 (.step 62 (.close 7)) (.step 9 (.close 18))) (.step 9 (.step 3 (.close 62)))) (.step 3 (.close 70))))) (.step 9 (.step 3 (.step 57 (.step 18 (.close 26)))))) (.step 57 (.step 3 (.close 54)))) (.step 53 (.step 57 (.split 72 1 (.split 54 1 (.split 12 0 (.step 53 (.step 3 (.close 7))) (.step 9 (.step 3 (.step 15 (.close 53))))) (.step 9 (.step 21 (.step 3 (.close 57))))) (.step 9 (.step 26 (.step 3 (.step 40 (.step 53 (.close 15)))))))))) (.step 52 (.split 72 1 (.split 51 1 (.split 67 1 (.split 54 1 (.split 12 0 (.split 21 0 (.split 34 0 (.split 35 0 (.step 7 (.close 9)) (.step 9 (.close 18))) (.step 9 (.close 31))) (.step 9 (.close 18))) (.step 9 (.step 3 (.step 15 (.step 18 (.close 21)))))) (.step 57 (.close 3))) (.step 3 (.close 70))) (.step 52 (.close 7))) (.step 3 (.step 9 (.step 26 (.step 40 (.step 52 (.close 57))))))))) (.step 9 (.step 3 (.step 46 (.step 52 (.step 53 (.step 7 (.step 9 (.step 27 (.close 46)))))))))) (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 7)) (.step 31 (.close 57))) (.step 31 (.close 53))) (.step 31 (.close 52)))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848990635548761507172873080143722628362829403810814955430853865899666806140125052928⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.close 7)) (.step 9 (.close 31))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 39))))))) (.run (.step 3 (.step 9 (.step 21 (.step 38 (.step 57 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 51 1 (.step 75 (.split 54 1 (.split 12 0 (.step 3 (.close 38)) (.step 9 (.step 3 (.close 38)))) (.step 9 (.step 21 (.step 31 (.close 57)))))) (.step 3 (.close 9))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 40 (.step 31 (.close 57)))))))) (.step 3 (.step 9 (.step 21 (.step 52 (.step 40 (.step 57 (.step 38 (.step 26 (.close 52)))))))))) (.step 31 (.close 45))) (.step 31 (.close 39)))))))))) (.run (.step 7 (.step 38 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.close 7)) (.step 9 (.step 15 (.close 31)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 37))) (.step 31 (.close 37)))))))) (.run (.split 35 1 (.split 49 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 9))) (.step 18 (.close 52))) (.step 3 (.close 31))))) (.run (.step 7 (.step 26 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 26))) (.step 18 (.close 52)))) (.step 18 (.close 9))))))) (.run (.step 3 (.step 18 (.step 31 (.step 9 (.step 57 (.split 35 1 (.split 72 1 (.step 3 (.step 18 (.step 52 (.close 53)))) (.step 18 (.close 31))) (.step 18 (.close 38))))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848990635548761507172873080143725624441185932164455731511631966484429360925018947584⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 22 (.split 22 1 (.step 22 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 22))) (.step 18 (.close 52)))) (.step 18 (.close 9)))) (.step 7 (.close 18))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.step 21 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.close 18)) (.step 18 (.close 21))) (.step 18 (.close 52)))) (.step 18 (.close 9)))) (.step 7 (.close 18))) (.step 7 (.close 18))))))) (.run (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.step 21 (.step 9 (.step 3 (.step 18 (.step 15 (.step 3 (.step 15 (.close 3))))))))) (.step 21 (.step 15 (.close 62)))) (.step 15 (.close 18))) (.step 21 (.step 15 (.close 53)))) (.step 21 (.step 15 (.step 26 (.close 52))))) (.step 21 (.step 15 (.close 38))))))) (.run (.split 12 1 (.split 35 1 (.split 49 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 9))) (.step 18 (.close 52))) (.step 3 (.close 31))) (.step 3 (.close 15))))) (.run (.step 9 (.step 11 (.step 9 (.step 18 (.step 9 (.close 31))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part2.excludes
end FiveColour.Packed.ProjectedChunks.Case109
