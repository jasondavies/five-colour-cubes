module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case91
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5260135901548373507240989882880128665554204340346194632619378241831841263937196316689854567294266855479896558852888901455290301000121374319688502565501857074588549035545263362308577757041801694903573774799470593⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨36598186871210186373086, 5653548961318841089639973500642015693236235224231190043906103201777981023951928279572763835464728950349135465840953962536991606646746825747881197814404025084909808628036390642683365795134764479495963128771311687678559233, 0⟩]
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
def root : Box := ⟨1, 5260135901548373507240989882880128665554204340346194632619378241831841263937196316689854567294266855479896558852888901455290301000121374319688502565501857074588549035545263362308577757041801694903573774799470593⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 34 (.close 6)))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case91

namespace FiveColour.Packed.EnumerationChunks.Projected.Case91
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 335 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 335 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 335 0).upper i := by decide +kernel
lemma budget_model : (⟨36598186871210186373086, 5653548961318841089639973500642015693236235224231190043906103201777981023951928279572763835464728950349135465840953962536991606646746825747881197814404025084909808628036390642683365795134764479495963128771311687678559233, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 335), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨36598186871210186373086, 5653548961318841089639973500642015693236235224231190043906103201777981023951928279572763835464728950349135465840953962536991606646746825747881197814404025084909808628036390642683365795134764479495963128771311687678559233, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 335) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 335 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 335 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 335) (Archive.root 335) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 335 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 335 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case91

namespace FiveColour.Packed.EnumerationChunks.Case91
def root : Box := Archive.root 335
def families : Fin 78 → List Cut := Enumeration.families 335
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case91.original_covered points
end FiveColour.Packed.EnumerationChunks.Case91
