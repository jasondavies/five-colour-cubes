module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case72
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510724716875129052021434112103325415711342535343422895103095152999653711524920626245062089790517323846554997974339651190569672959175364774507990560770158804315967325971939328⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨32908989162382482537463, 5789234131009374248507346766749891419687533244750779835710650130547166070169190972551199135583887163440067555744480064067624080828260535803883819067065712488494011642056487991334880784408697916612570372223033612482063107073, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510724716875129052021434112103325415711342535343422895103095152999653711524920626245062089790517323846554997974339651190569672959175364774507990560770158804315967325971939328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 0 (.split 17 0 (.step 45 (.step 17 (.close 38))) (.split 34 0 (.step 20 (.step 24 (.close 39))) (.split 42 0 (.step 20 (.step 17 (.close 39))) (.step 39 (.step 17 (.step 24 (.close 25))))))) (.step 33 (.split 17 0 (.step 45 (.close 15)) (.step 39 (.step 15 (.step 17 (.close 19)))))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 10 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case72

namespace FiveColour.Packed.EnumerationChunks.Projected.Case72
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 316 0 10 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 316 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 316 0).upper i := by decide +kernel
lemma budget_model : (⟨32908989162382482537463, 5789234131009374248507346766749891419687533244750779835710650130547166070169190972551199135583887163440067555744480064067624080828260535803883819067065712488494011642056487991334880784408697916612570372223033612482063107073, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 316), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908989162382482537463, 5789234131009374248507346766749891419687533244750779835710650130547166070169190972551199135583887163440067555744480064067624080828260535803883819067065712488494011642056487991334880784408697916612570372223033612482063107073, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 316) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 316 0 10).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 10)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 10 families = caseProblem 316 0 10 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 316) (Archive.root 316) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 316 0 10 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 316 0 10).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case72

namespace FiveColour.Packed.EnumerationChunks.Case72
def root : Box := Archive.root 316
def families : Fin 78 → List Cut := Enumeration.families 316
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case72.original_covered points
end FiveColour.Packed.EnumerationChunks.Case72
