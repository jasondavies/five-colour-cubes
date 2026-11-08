module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case169
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346508060100310038720657802945771935416622282658564044340506066347242599290074050567531007167894303490965504⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨37630669409018456112119, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639180033369853557824749914671530180203279448118754128379673028050877429417560652570824680124548036304556207899649, 0⟩]
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
def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861724080608471001193524593889459337845033577446486715613065811222753756626059547199875318874125810401653251899951155939087010181939200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 55 1 (.step 7 (.split 49 1 (.split 56 1 (.split 67 1 (.step 7 (.step 9 (.step 58 (.close 7)))) (.split 38 0 (.step 7 (.step 53 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 21 (.close 26)))))) (.split 67 1 (.split 34 0 (.split 50 1 (.step 7 (.step 9 (.step 7 (.close 21)))) (.step 48 (.step 21 (.step 7 (.step 9 (.step 7 (.step 22 (.step 7 (.close 26))))))))) (.step 7 (.step 16 (.step 21 (.close 22))))) (.step 7 (.step 9 (.step 21 (.close 26)))))) (.split 50 1 (.split 56 1 (.split 67 1 (.step 7 (.step 9 (.close 52))) (.step 52 (.step 7 (.step 9 (.close 21))))) (.step 48 (.step 16 (.step 57 (.step 9 (.step 7 (.step 26 (.step 7 (.close 21))))))))) (.step 52 (.split 56 1 (.step 7 (.step 9 (.close 52))) (.step 9 (.step 21 (.step 5 (.step 7 (.step 16 (.step 7 (.step 22 (.step 7 (.close 26)))))))))))))) (.step 18 (.step 58 (.step 18 (.step 52 (.step 7 (.step 53 (.step 7 (.close 62))))))))) (.step 7 (.step 54 (.split 49 1 (.split 55 1 (.split 56 1 (.split 38 0 (.step 7 (.step 53 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 7 (.step 9 (.step 21 (.step 26 (.step 21 (.close 53))))))) (.step 7 (.step 53 (.close 54)))) (.step 52 (.step 7 (.step 9 (.step 21 (.close 26))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346505820355567860916447245503491366972342476016400112774485960491434521280126991131525027409473632051658752⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 7 (.step 54 (.split 49 1 (.split 55 1 (.split 56 1 (.step 70 (.split 38 0 (.step 7 (.step 9 (.step 7 (.step 27 (.close 46))))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 46 (.close 53))))) (.step 9 (.step 27 (.step 9 (.step 46 (.step 7 (.close 52))))))))))) (.run (.step 7 (.step 45 (.step 38 (.step 58 (.close 52))))))) (.run (.step 7 (.split 42 1 (.step 58 (.split 43 1 (.split 51 1 (.split 67 1 (.split 34 0 (.split 49 1 (.split 50 1 (.step 58 (.step 7 (.step 10 (.step 7 (.close 21))))) (.step 21 (.step 5 (.step 58 (.close 9))))) (.step 42 (.step 58 (.step 9 (.close 26))))) (.step 7 (.step 16 (.step 21 (.close 22))))) (.step 7 (.step 9 (.step 26 (.step 21 (.close 54)))))) (.step 7 (.step 54 (.step 21 (.close 52))))) (.step 7 (.step 9 (.close 10))))) (.step 7 (.step 38 (.step 41 (.step 16 (.close 45))))))))) (.run (.step 7 (.split 38 1 (.step 7 (.step 58 (.split 49 1 (.step 39 (.step 22 (.step 38 (.step 45 (.step 52 (.step 53 (.close 57))))))) (.step 22 (.step 57 (.step 45 (.step 38 (.close 52)))))))) (.step 38 (.step 45 (.step 7 (.step 38 (.step 41 (.step 16 (.step 22 (.step 45 (.close 52)))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 9797766621314684873895708907325882235029705663859328588111430561827861726855985850370175705061346508060100310038720657802945771935416622282658564044340506066347242599290074050567531007167894303490965504⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 36 1 (.split 38 1 (.step 7 (.step 37 (.step 38 (.step 58 (.close 52))))) (.step 16 (.step 38 (.step 28 (.step 37 (.step 7 (.step 37 (.step 21 (.close 41))))))))) (.split 49 1 (.step 45 (.split 50 1 (.step 37 (.step 7 (.step 16 (.step 21 (.close 22))))) (.step 7 (.step 22 (.step 37 (.step 21 (.step 38 (.step 52 (.step 45 (.step 22 (.close 53))))))))))) (.step 7 (.step 16 (.step 37 (.close 52))))))))) (.run (.step 7 (.step 18 (.close 52))))) (.run (.step 7 (.step 18 (.step 52 (.close 53)))))) (.run (.step 7 (.step 18 (.split 38 1 (.step 7 (.step 19 (.step 25 (.step 52 (.step 53 (.close 19)))))) (.step 4 (.step 5 (.close 19))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part2.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case169

namespace FiveColour.Packed.EnumerationChunks.Projected.Case169
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 56 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 56 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 56 0).upper i := by decide +kernel
lemma budget_model : (⟨37630669409018456112119, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639180033369853557824749914671530180203279448118754128379673028050877429417560652570824680124548036304556207899649, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 56), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨37630669409018456112119, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639180033369853557824749914671530180203279448118754128379673028050877429417560652570824680124548036304556207899649, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 56) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 56 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 56 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 56) (Archive.root 56) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 56 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 56 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case169

namespace FiveColour.Packed.EnumerationChunks.Case169
def root : Box := Archive.root 56
def families : Fin 78 → List Cut := Enumeration.families 56
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case169.original_covered points
end FiveColour.Packed.EnumerationChunks.Case169
