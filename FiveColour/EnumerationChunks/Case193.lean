module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case193
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5521038642265172833200147547967109093502561454181064050036358039072371390093391687922924278807897719249905207065419940049129307126026975365791764392541059237187957285564389525571243956334985412480090948773421734952962⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨30666541081021128896446, 5653548961323972924649819221030976445153133834664318320894055915633373970312978309199083541659665574237124037639541146111563493128984644470311576664498607971097082070547331612438551329471180924412418929488251918999356417, 0⟩]
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
def root : Box := ⟨2, 5521038642265172833200147547967109093502561454181064050036358039072371390093391687922924278807897719249905207065419940049129307126026975365791764392541059237187957285564389525571243956334985412480090948773421734952962⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 40 1 (.step 68 (.step 15 (.step 31 (.step 21 (.close 33))))) (.step 4 (.step 24 (.step 7 (.step 15 (.close 19)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case193

namespace FiveColour.Packed.EnumerationChunks.Projected.Case193
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 80 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 80 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 80 0).upper i := by decide +kernel
lemma budget_model : (⟨30666541081021128896446, 5653548961323972924649819221030976445153133834664318320894055915633373970312978309199083541659665574237124037639541146111563493128984644470311576664498607971097082070547331612438551329471180924412418929488251918999356417, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 80), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨30666541081021128896446, 5653548961323972924649819221030976445153133834664318320894055915633373970312978309199083541659665574237124037639541146111563493128984644470311576664498607971097082070547331612438551329471180924412418929488251918999356417, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 80) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 80 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 80 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 80) (Archive.root 80) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 80 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 80 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case193

namespace FiveColour.Packed.EnumerationChunks.Case193
def root : Box := Archive.root 80
def families : Fin 78 → List Cut := Enumeration.families 80
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case193.original_covered points
end FiveColour.Packed.EnumerationChunks.Case193
