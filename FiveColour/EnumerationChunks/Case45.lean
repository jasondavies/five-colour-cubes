module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case45
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772022452223414230330376331696413793774961053209756195714202226062881002554841756544659090282998731189681632781772299293014141111432660525349210247919217617187001487910240256⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772022452223414230330376331696413793774961053209756195714202226062881002554841756544659090282998731189681632781772299293014141111432660525349210247919217617187001487910240256⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 12 0 (.step 7 (.step 43 (.step 9 (.step 33 (.close 37))))) (.step 9 (.step 15 (.step 7 (.step 13 (.step 33 (.close 38))))))) (.step 7 (.step 43 (.step 39 (.close 9))))) (.split 17 0 (.step 7 (.step 38 (.step 43 (.close 9)))) (.split 26 0 (.split 30 0 (.step 24 (.step 38 (.step 9 (.step 13 (.step 15 (.close 17)))))) (.step 7 (.close 24))) (.step 7 (.close 17))))) (.step 7 (.step 13 (.split 35 0 (.split 50 0 (.split 17 0 (.step 43 (.step 15 (.close 17))) (.step 39 (.close 15))) (.step 33 (.step 43 (.close 9)))) (.step 33 (.step 52 (.step 38 (.step 9 (.close 20))))))))) (.split 16 0 (.split 17 0 (.split 26 0 (.step 7 (.close 9)) (.split 34 0 (.step 9 (.close 7)) (.step 15 (.step 7 (.close 9))))) (.step 7 (.close 9))) (.split 17 0 (.step 7 (.close 9)) (.step 7 (.close 9))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case45

namespace FiveColour.Packed.EnumerationChunks.Projected.Case45
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 289 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 289 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 289 0).upper i := by decide +kernel
lemma budget_model : (⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 289), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 289) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 289 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 289 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 289) (Archive.root 289) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 289 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 289 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case45

namespace FiveColour.Packed.EnumerationChunks.Case45
def root : Box := Archive.root 289
def families : Fin 78 → List Cut := Enumeration.families 289
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case45.original_covered points
end FiveColour.Packed.EnumerationChunks.Case45
