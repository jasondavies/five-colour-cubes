module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case69
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520661873432413930091811010963534734505009995389894990493733299354520747423412594371113130017162316079069306338423024812671756013854899244834558871948243410636471935794751266782969856⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨18741817655939057892339, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475069125776341470636776399003572424092354108296175801265491834031787454638626179529899799972324883525318738944, 0⟩]
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
def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520661873432413930091811010963534734505009995389894990493733299354520747423412594371113130017162316079069306338423024812671756013854899244834558871948243410636471935794751266782969856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 38 0 (.split 16 0 (.split 22 0 (.step 39 (.step 14 (.close 45))) (.step 45 (.step 20 (.step 14 (.step 23 (.close 25)))))) (.split 22 0 (.split 17 0 (.step 43 (.step 39 (.close 41))) (.split 36 0 (.split 51 0 (.step 14 (.step 17 (.close 20))) (.step 20 (.step 14 (.step 23 (.close 25))))) (.step 20 (.close 25)))) (.split 36 0 (.split 17 0 (.step 25 (.close 14)) (.step 20 (.step 17 (.close 25)))) (.step 20 (.step 17 (.close 25)))))) (.step 33 (.split 22 0 (.split 17 0 (.step 54 (.step 5 (.close 14))) (.step 39 (.step 5 (.close 14)))) (.step 45 (.step 23 (.split 34 0 (.step 20 (.close 19)) (.step 14 (.close 16)))))))) (.step 13 (.split 38 0 (.split 16 0 (.step 43 (.split 22 0 (.step 20 (.step 23 (.close 37))) (.step 43 (.step 11 (.step 5 (.step 17 (.close 20))))))) (.split 22 0 (.step 43 (.step 11 (.step 5 (.step 17 (.close 20))))) (.step 25 (.step 20 (.close 5))))) (.step 33 (.split 16 0 (.step 23 (.step 5 (.close 16))) (.split 43 0 (.step 5 (.close 19)) (.step 23 (.close 11)))))))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case69

namespace FiveColour.Packed.EnumerationChunks.Projected.Case69
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 313 0 10 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 313 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 313 0).upper i := by decide +kernel
lemma budget_model : (⟨18741817655939057892339, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475069125776341470636776399003572424092354108296175801265491834031787454638626179529899799972324883525318738944, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 313), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨18741817655939057892339, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475069125776341470636776399003572424092354108296175801265491834031787454638626179529899799972324883525318738944, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 313) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 313 0 10).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 10)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 10 families = caseProblem 313 0 10 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 313) (Archive.root 313) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 313 0 10 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 313 0 10).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case69

namespace FiveColour.Packed.EnumerationChunks.Case69
def root : Box := Archive.root 313
def families : Fin 78 → List Cut := Enumeration.families 313
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case69.original_covered points
end FiveColour.Packed.EnumerationChunks.Case69
