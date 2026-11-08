module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case190
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5653543569679536981196946412616686640498315936812243935685725083698590658270650634706916204403427661912866746291945337247102666105685933582966387019461497053753410440467153841998707561271549610527107888750601742428667906⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨23611742337562385305406, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340647030340707156299050781889704801152725612693487204679141161216171784460345221283290785923672815928606721, 0⟩]
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
def root : Box := ⟨2, 5653543569679536981196946412616686640498315936812243935685725083698590658270650634706916204403427661912866746291945337247102666105685933582966387019461497053753410440467153841998707561271549610527107888750601742428667906⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.split 7 0 (.step 18 (.close 7)) (.split 12 0 (.step 18 (.step 7 (.close 10))) (.step 18 (.step 6 (.step 10 (.close 12)))))) (.split 7 0 (.split 13 0 (.step 18 (.step 7 (.close 9))) (.step 18 (.step 6 (.step 9 (.close 12))))) (.step 6 (.close 7)))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case190

namespace FiveColour.Packed.EnumerationChunks.Projected.Case190
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 77 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 77 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 77 0).upper i := by decide +kernel
lemma budget_model : (⟨23611742337562385305406, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340647030340707156299050781889704801152725612693487204679141161216171784460345221283290785923672815928606721, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 77), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨23611742337562385305406, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340647030340707156299050781889704801152725612693487204679141161216171784460345221283290785923672815928606721, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 77) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 77 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 77 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 77) (Archive.root 77) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 77 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 77 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case190

namespace FiveColour.Packed.EnumerationChunks.Case190
def root : Box := Archive.root 77
def families : Fin 78 → List Cut := Enumeration.families 77
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case190.original_covered points
end FiveColour.Packed.EnumerationChunks.Case190
