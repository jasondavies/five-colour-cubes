module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case19
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774538572461504338143573274126223462950690675705247977443137688163756565230079967232⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨11593704327342146239203, 5789228615351851010618494880448709935079879776571393911013839255768432665236909366211952458869579070868465007734427163889986087675088308450524617271906414823344187018214989624687995923638293252931585195508460550071695442944, 0⟩]
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774538572461504338143573274126223462950690675705247977443136479237936950600905261056⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 4 0 (.split 16 0 (.split 14 0 (.split 63 0 (.split 17 0 (.split 22 0 (.step 29 (.close 3)) (.step 45 (.step 3 (.close 4)))) (.step 39 (.step 4 (.step 7 (.close 11))))) (.step 37 (.step 29 (.step 7 (.step 3 (.step 11 (.step 19 (.close 20)))))))) (.step 37 (.step 5 (.step 7 (.step 11 (.step 19 (.close 20))))))) (.split 14 0 (.split 17 0 (.split 63 0 (.split 22 0 (.step 38 (.step 3 (.step 4 (.close 7)))) (.step 7 (.step 25 (.step 4 (.step 11 (.close 19)))))) (.step 37 (.step 29 (.step 5 (.step 11 (.close 19)))))) (.step 7 (.step 39 (.step 4 (.step 11 (.step 15 (.close 19))))))) (.step 7 (.split 17 0 (.step 37 (.step 5 (.step 11 (.close 19)))) (.step 13 (.step 19 (.close 20))))))) (.split 14 0 (.split 25 0 (.step 7 (.step 3 (.close 28))) (.step 7 (.close 28))) (.step 7 (.close 3)))) (.split 14 0 (.split 16 0 (.split 17 0 (.split 51 0 (.split 63 0 (.step 7 (.split 22 0 (.step 29 (.close 3)) (.step 7 (.step 4 (.step 11 (.close 15)))))) (.step 29 (.step 37 (.step 7 (.step 3 (.step 11 (.close 13))))))) (.step 7 (.step 39 (.step 13 (.step 3 (.step 4 (.close 11))))))) (.step 7 (.step 39 (.step 4 (.step 11 (.step 13 (.close 15))))))) (.step 7 (.split 35 0 (.step 13 (.split 38 0 (.split 36 0 (.step 17 (.step 3 (.step 11 (.close 19)))) (.step 20 (.step 11 (.close 15)))) (.step 33 (.step 5 (.close 14))))) (.step 33 (.step 13 (.step 17 (.step 4 (.step 11 (.close 19))))))))) (.step 7 (.step 13 (.close 3))))))
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
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748833008221223422239590226486830063807184255482746434307083199263698824324214225571002359774538572461504338143573274126223462950690675705247977443137688163756565230079967232⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.reuse 0) (.run (.split 14 0 (.split 25 0 (.split 26 0 (.step 7 (.step 3 (.close 5))) (.step 7 (.step 5 (.close 28)))) (.step 7 (.step 5 (.close 28)))) (.step 7 (.split 25 0 (.split 16 0 (.step 7 (.step 5 (.step 7 (.close 11)))) (.step 7 (.close 11))) (.step 5 (.step 3 (.close 4))))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case19

namespace FiveColour.Packed.EnumerationChunks.Projected.Case19
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 263 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 263 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 263 0).upper i := by decide +kernel
lemma budget_model : (⟨11593704327342146239203, 5789228615351851010618494880448709935079879776571393911013839255768432665236909366211952458869579070868465007734427163889986087675088308450524617271906414823344187018214989624687995923638293252931585195508460550071695442944, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 263), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11593704327342146239203, 5789228615351851010618494880448709935079879776571393911013839255768432665236909366211952458869579070868465007734427163889986087675088308450524617271906414823344187018214989624687995923638293252931585195508460550071695442944, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 263) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 263 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 263 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 263) (Archive.root 263) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 263 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 263 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case19

namespace FiveColour.Packed.EnumerationChunks.Case19
def root : Box := Archive.root 263
def families : Fin 78 → List Cut := Enumeration.families 263
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case19.original_covered points
end FiveColour.Packed.EnumerationChunks.Case19
