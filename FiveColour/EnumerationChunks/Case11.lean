module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case11
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409449891788137011620874289152⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨8697816018884211022451, 5789228615357111146515144370645293582521562950893008474422619893061853696606201481707084707191459675456370831556440846149949944370837561739506646933964126675846887447766945946864215253787366754672169104713068902630525239296, 0⟩]
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
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843445759100917919003786254359394883714925394579685376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 42 0 (.split 36 0 (.split 14 0 (.split 34 0 (.step 5 (.close 52)) (.step 5 (.step 10 (.close 13)))) (.step 5 (.step 11 (.step 27 (.close 34))))) (.step 54 (.step 5 (.step 10 (.close 13))))) (.split 43 0 (.step 58 (.step 5 (.step 13 (.step 5 (.close 17))))) (.step 70 (.step 58 (.step 5 (.step 13 (.step 5 (.close 11)))))))) (.split 42 0 (.split 36 0 (.step 53 (.step 5 (.close 13))) (.step 54 (.step 33 (.close 5)))) (.step 70 (.split 14 0 (.step 33 (.step 58 (.close 10))) (.step 13 (.step 53 (.step 5 (.close 11)))))))) (.split 30 0 (.split 42 0 (.split 43 0 (.step 5 (.step 31 (.close 17))) (.step 70 (.step 5 (.close 11)))) (.step 55 (.step 62 (.step 5 (.step 13 (.step 5 (.close 11))))))) (.step 70 (.step 5 (.step 31 (.step 13 (.step 5 (.close 11)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 42 0 (.split 43 0 (.step 5 (.step 13 (.close 17))) (.step 54 (.step 5 (.close 11)))) (.step 54 (.close 5))) (.step 55 (.step 52 (.step 5 (.step 15 (.step 5 (.close 11))))))) (.step 54 (.step 33 (.step 63 (.step 25 (.step 5 (.close 10))))))) (.step 70 (.split 14 0 (.step 70 (.step 54 (.step 5 (.close 11)))) (.step 63 (.step 11 (.step 17 (.step 5 (.close 19))))))))))
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
def root : Box := ⟨1267650600228229401497776947200, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220601161453331797561748481845835306024621309952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.step 52 (.step 64 (.step 5 (.close 10)))) (.step 54 (.step 13 (.step 5 (.close 10))))) (.split 36 0 (.split 56 0 (.step 52 (.step 33 (.step 5 (.step 13 (.close 5))))) (.step 13 (.step 33 (.close 5)))) (.step 13 (.step 33 (.step 5 (.close 10)))))) (.step 70 (.step 13 (.close 5)))) (.split 30 0 (.step 54 (.split 22 0 (.step 52 (.step 5 (.step 13 (.close 5)))) (.step 70 (.step 5 (.close 11))))) (.step 13 (.step 33 (.step 54 (.close 5)))))) (.split 17 0 (.split 22 0 (.split 36 0 (.split 56 0 (.split 58 0 (.split 42 0 (.step 52 (.step 63 (.close 10))) (.step 13 (.step 5 (.step 25 (.step 5 (.step 10 (.close 15))))))) (.step 52 (.step 42 (.close 5)))) (.step 13 (.step 54 (.step 5 (.close 10))))) (.step 13 (.step 54 (.step 5 (.step 25 (.step 5 (.step 10 (.close 15)))))))) (.step 70 (.step 13 (.split 38 0 (.step 70 (.step 5 (.step 11 (.close 14)))) (.step 14 (.step 5 (.step 19 (.close 5)))))))) (.split 22 0 (.split 30 0 (.step 54 (.split 34 0 (.step 63 (.step 13 (.close 5))) (.step 13 (.step 5 (.step 14 (.close 11)))))) (.step 13 (.step 33 (.step 20 (.step 5 (.close 14)))))) (.split 30 0 (.step 70 (.step 19 (.step 13 (.step 19 (.step 5 (.close 11)))))) (.step 13 (.step 19 (.step 20 (.close 5)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602555249906705725694827828227346547215433728⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 14 0 (.step 5 (.step 11 (.step 13 (.close 27)))) (.step 63 (.close 11))) (.step 54 (.step 5 (.close 11)))) (.step 55 (.step 52 (.step 5 (.step 15 (.step 5 (.close 11))))))) (.step 53 (.step 65 (.close 11)))) (.step 70 (.split 14 0 (.step 70 (.step 63 (.close 20))) (.step 63 (.step 11 (.step 17 (.step 5 (.close 19)))))))) (.split 14 0 (.split 30 0 (.split 34 0 (.split 42 0 (.split 43 0 (.step 63 (.step 20 (.close 5))) (.step 54 (.step 48 (.close 5)))) (.step 23 (.step 24 (.step 13 (.step 19 (.step 5 (.close 20))))))) (.step 23 (.step 24 (.step 54 (.step 5 (.step 13 (.step 14 (.close 16)))))))) (.step 33 (.step 53 (.step 23 (.step 20 (.step 23 (.close 11))))))) (.split 22 0 (.step 63 (.step 19 (.step 11 (.step 5 (.close 17))))) (.split 30 0 (.step 63 (.step 19 (.step 11 (.step 5 (.close 17))))) (.step 13 (.step 19 (.step 20 (.step 5 (.close 11))))))))))) (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.split 36 0 (.step 63 (.close 13)) (.step 13 (.step 5 (.close 13))))) (.step 13 (.step 5 (.close 11)))) (.step 13 (.step 20 (.step 13 (.close 5))))) (.step 13 (.step 53 (.step 14 (.step 11 (.close 5)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409448681681725776274288279552⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.reuse 0) (.run (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 38 0 (.step 52 (.step 5 (.close 10))) (.step 55 (.step 65 (.step 10 (.step 5 (.close 13)))))) (.step 52 (.step 10 (.close 13)))) (.split 34 0 (.split 36 0 (.step 65 (.step 52 (.close 5))) (.step 13 (.step 54 (.step 5 (.step 10 (.close 16)))))) (.step 13 (.step 52 (.step 10 (.close 16)))))) (.step 55 (.step 70 (.step 5 (.close 11))))) (.split 14 0 (.step 55 (.step 72 (.step 5 (.step 11 (.close 13))))) (.step 24 (.step 13 (.step 5 (.close 11)))))) (.split 14 0 (.split 17 0 (.step 55 (.step 65 (.close 5))) (.step 24 (.step 13 (.step 23 (.step 54 (.step 5 (.step 10 (.close 17)))))))) (.step 24 (.step 63 (.step 5 (.step 13 (.step 5 (.close 17)))))))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 52 (.step 5 (.close 10))) (.step 13 (.step 15 (.close 10)))) (.step 13 (.step 54 (.step 5 (.step 10 (.close 13)))))) (.step 13 (.step 52 (.step 10 (.close 13))))) (.step 13 (.step 5 (.step 10 (.close 18))))) (.step 13 (.close 5))) (.step 13 (.step 54 (.step 5 (.close 11))))) (.step 13 (.step 55 (.step 13 (.close 5))))) (.step 13 (.step 31 (.step 63 (.step 13 (.close 5)))))))))
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

namespace Part4
def root : Box := ⟨1180591620718485045248, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409448682862317396991699582976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 13 0 (.split 51 0 (.split 38 0 (.split 42 0 (.step 5 (.close 7)) (.step 55 (.step 7 (.close 5)))) (.step 55 (.step 10 (.close 5)))) (.step 46 (.split 36 0 (.split 56 0 (.step 5 (.close 7)) (.step 7 (.step 5 (.close 10)))) (.step 7 (.close 5))))) (.split 38 0 (.split 42 0 (.step 52 (.step 10 (.close 5))) (.step 55 (.step 76 (.step 7 (.close 5))))) (.split 34 0 (.step 55 (.step 10 (.close 5))) (.step 7 (.close 5))))) (.step 7 (.step 46 (.step 5 (.close 10))))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 72 (.step 5 (.close 7))))) (.step 7 (.step 15 (.step 5 (.step 10 (.close 30)))))) (.step 7 (.step 65 (.step 5 (.close 7))))) (.step 7 (.split 34 0 (.split 13 0 (.split 16 0 (.split 17 0 (.step 55 (.step 5 (.close 7))) (.step 5 (.close 7))) (.step 7 (.close 5))) (.split 16 0 (.split 43 0 (.split 51 0 (.step 5 (.close 7)) (.step 5 (.close 7))) (.step 5 (.close 7))) (.step 5 (.step 7 (.close 5))))) (.step 7 (.close 5))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5789228615351851005602038365663647631691737414976494313896709961700895180786636570403427415128915098895626337085519943934161329303696328371865771017798781382148815513257843447220602556611036173409449891788137011620874289152⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 7 0 (.split 8 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 13 0 (.split 39 0 (.step 5 (.step 10 (.close 27))) (.step 5 (.step 27 (.step 5 (.close 35))))) (.step 5 (.close 7))) (.step 52 (.step 40 (.step 5 (.close 7))))) (.step 7 (.step 18 (.step 11 (.close 13))))) (.step 7 (.step 48 (.close 5)))) (.step 7 (.step 18 (.step 11 (.close 13))))) (.step 7 (.step 63 (.step 7 (.step 5 (.step 11 (.close 13))))))) (.step 7 (.step 68 (.step 63 (.close 7))))) (.step 7 (.split 16 0 (.split 13 0 (.step 63 (.step 7 (.close 5))) (.step 63 (.close 5))) (.step 7 (.close 5))))))) (.split 8 0 (.reuse 1) (.run (.split 14 0 (.step 7 (.split 34 0 (.split 13 0 (.split 16 0 (.split 17 0 (.step 55 (.step 5 (.close 7))) (.step 5 (.close 7))) (.step 7 (.close 5))) (.split 16 0 (.split 43 0 (.split 51 0 (.step 5 (.close 7)) (.step 5 (.close 7))) (.step 5 (.close 7))) (.step 5 (.step 7 (.close 5))))) (.step 7 (.close 5)))) (.split 10 0 (.split 13 0 (.step 7 (.split 16 0 (.step 63 (.close 5)) (.step 7 (.close 5)))) (.step 5 (.step 23 (.step 5 (.close 7))))) (.step 5 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part5.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case11

namespace FiveColour.Packed.EnumerationChunks.Projected.Case11
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 255 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 255 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 255 0).upper i := by decide +kernel
lemma budget_model : (⟨8697816018884211022451, 5789228615357111146515144370645293582521562950893008474422619893061853696606201481707084707191459675456370831556440846149949944370837561739506646933964126675846887447766945946864215253787366754672169104713068902630525239296, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 255), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨8697816018884211022451, 5789228615357111146515144370645293582521562950893008474422619893061853696606201481707084707191459675456370831556440846149949944370837561739506646933964126675846887447766945946864215253787366754672169104713068902630525239296, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 255) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 255 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 255 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 255) (Archive.root 255) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 255 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 255 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case11

namespace FiveColour.Packed.EnumerationChunks.Case11
def root : Box := Archive.root 255
def families : Fin 78 → List Cut := Enumeration.families 255
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case11.original_covered points
end FiveColour.Packed.EnumerationChunks.Case11
