module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case22
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714807338531950044380334832772606038667612822783043417733974197376314982795397038080⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32016031753816107707303, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697928522998852134929247591988189268012958721, 0⟩]
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
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714807338531950044380334832772606038667612822783043417733974197375162061290790191104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 0 (.split 16 0 (.split 22 0 (.split 42 0 (.split 26 0 (.split 17 0 (.split 30 0 (.step 9 (.step 18 (.step 13 (.close 15)))) (.step 53 (.step 7 (.step 9 (.step 13 (.close 15)))))) (.step 54 (.step 4 (.close 7)))) (.step 46 (.step 71 (.close 7)))) (.step 70 (.split 17 0 (.step 62 (.step 7 (.step 9 (.step 13 (.close 15))))) (.step 7 (.step 43 (.close 4)))))) (.split 42 0 (.split 17 0 (.step 70 (.step 62 (.step 7 (.close 4)))) (.step 7 (.step 54 (.step 4 (.step 9 (.close 13)))))) (.step 7 (.step 68 (.close 70))))) (.split 17 0 (.split 22 0 (.split 42 0 (.step 53 (.step 9 (.step 4 (.close 7)))) (.step 7 (.step 53 (.step 4 (.step 9 (.close 13)))))) (.step 7 (.step 70 (.step 24 (.close 4))))) (.step 7 (.step 54 (.step 24 (.step 18 (.step 13 (.step 4 (.close 18))))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 52 (.split 30 0 (.split 34 0 (.step 52 (.step 7 (.step 9 (.step 13 (.close 18))))) (.step 7 (.close 15))) (.step 7 (.step 33 (.step 13 (.close 9)))))) (.step 7 (.step 13 (.step 70 (.step 13 (.step 4 (.close 9))))))) (.step 7 (.step 13 (.step 54 (.step 13 (.step 4 (.step 9 (.close 14)))))))) (.step 7 (.step 13 (.split 12 0 (.step 13 (.split 35 0 (.split 50 0 (.split 62 0 (.step 39 (.step 4 (.step 9 (.close 15)))) (.step 23 (.step 4 (.close 16)))) (.step 33 (.step 24 (.step 4 (.close 9))))) (.step 24 (.step 33 (.step 4 (.step 9 (.close 15))))))) (.step 13 (.close 4))))))))
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
def root : Box := ⟨1073741824, 5515652268238843663967872367942735257503789912183210560402466295286724304382214181162031642034816500226667523172814242883942965536945714807338531950044380334832772606038667612822783043417733974197376314982795397038080⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.reuse 0) (.run (.split 16 0 (.split 26 0 (.split 22 0 (.split 4 0 (.split 42 0 (.step 46 (.split 10 0 (.split 34 0 (.step 9 (.close 4)) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 4))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 53 (.step 7 (.close 4)))))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case22

namespace FiveColour.Packed.EnumerationChunks.Projected.Case22
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 266 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 266 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 266 0).upper i := by decide +kernel
lemma budget_model : (⟨32016031753816107707303, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697928522998852134929247591988189268012958721, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 266), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32016031753816107707303, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697928522998852134929247591988189268012958721, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 266) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 266 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 266 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 266) (Archive.root 266) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 266 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 266 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case22

namespace FiveColour.Packed.EnumerationChunks.Case22
def root : Box := Archive.root 266
def families : Fin 78 → List Cut := Enumeration.families 266
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case22.original_covered points
end FiveColour.Packed.EnumerationChunks.Case22
