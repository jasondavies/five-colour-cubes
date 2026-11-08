module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case93
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5648027917416434993898217684409255726706857339275904353810758349475126415318925473216880205817354431797774533970661368371276286328121750006487368109364869522170973728614246461580741026079684992555377705351212133615927297⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨28332829588240734347134, 5653548961323977936207446023492293789637427680963569422727051963205498374293613300750817692265347568044813268093686906541296848761506679246043077888340581153728623135459825353848098381261863991956758680015453701907939329, 0⟩]
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
def root : Box := ⟨1, 5648027917416434993898217684409255726706857339275904353810758349475126415318925473216880205817354431797774533970661368371276286328121750006487368109364869522170973728614246461580741026079684992555377705351212133615927297⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 31 0 (.step 23 (.step 6 (.close 16))) (.step 16 (.step 5 (.close 6)))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case93

namespace FiveColour.Packed.EnumerationChunks.Projected.Case93
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 337 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 337 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 337 0).upper i := by decide +kernel
lemma budget_model : (⟨28332829588240734347134, 5653548961323977936207446023492293789637427680963569422727051963205498374293613300750817692265347568044813268093686906541296848761506679246043077888340581153728623135459825353848098381261863991956758680015453701907939329, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 337), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨28332829588240734347134, 5653548961323977936207446023492293789637427680963569422727051963205498374293613300750817692265347568044813268093686906541296848761506679246043077888340581153728623135459825353848098381261863991956758680015453701907939329, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 337) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 337 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 337 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 337) (Archive.root 337) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 337 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 337 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case93

namespace FiveColour.Packed.EnumerationChunks.Case93
def root : Box := Archive.root 337
def families : Fin 78 → List Cut := Enumeration.families 337
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case93.original_covered points
end FiveColour.Packed.EnumerationChunks.Case93
