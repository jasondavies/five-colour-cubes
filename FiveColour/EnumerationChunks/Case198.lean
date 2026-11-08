module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case198
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 8299031137761985917024815727382322302024892470299583597066504420315676327613638987917529186770768885411344702863770575488882822647868912535110081969254807365878058141456049899569154⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37777778898337257226238, 5653548961323977941106329334149636230834382024899345816765989398247113357360444305729838074397400656298373192651830057026261434151992145403009949318848438682146707620919927162966295129934908516482828496311092367326184449, 0⟩]
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
def root : Box := ⟨2, 8299031137761985917024815727382322302024892470299583597066504420315676327613638987917529186770768885411344702863770575488882822647868912535110081969254807365878058141456049899569154⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 4 (.close 31)))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case198

namespace FiveColour.Packed.EnumerationChunks.Projected.Case198
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 85 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 85 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 85 0).upper i := by decide +kernel
lemma budget_model : (⟨37777778898337257226238, 5653548961323977941106329334149636230834382024899345816765989398247113357360444305729838074397400656298373192651830057026261434151992145403009949318848438682146707620919927162966295129934908516482828496311092367326184449, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 85), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨37777778898337257226238, 5653548961323977941106329334149636230834382024899345816765989398247113357360444305729838074397400656298373192651830057026261434151992145403009949318848438682146707620919927162966295129934908516482828496311092367326184449, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 85) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 85 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 85 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 85) (Archive.root 85) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 85 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 85 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case198

namespace FiveColour.Packed.EnumerationChunks.Case198
def root : Box := Archive.root 85
def families : Fin 78 → List Cut := Enumeration.families 85
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case198.original_covered points
end FiveColour.Packed.EnumerationChunks.Case198
