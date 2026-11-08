module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case48
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813225706412971961174873176746754048⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨37630511536740859966423, 5789234131009369111655880410916383799149935097950111679937790244350696937832588910803674238545500183085609357535611307840729301634221804252716538090356296810875202044827950228461282219658217406305038239415791728186442646529, 0⟩]
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253811926364547738026037213156054401024⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.step 7 (.split 22 0 (.split 30 0 (.step 55 (.step 4 (.step 8 (.close 16)))) (.step 33 (.step 23 (.step 17 (.close 37))))) (.split 34 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 19)))) (.split 38 0 (.step 20 (.step 4 (.step 8 (.close 19)))) (.step 19 (.step 5 (.close 20))))) (.split 38 0 (.split 47 0 (.step 23 (.close 24)) (.step 19 (.close 23))) (.step 19 (.close 23)))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 55 (.step 4 (.close 7))) (.step 7 (.step 19 (.close 4)))) (.step 7 (.split 38 0 (.step 20 (.close 4)) (.step 19 (.close 5))))) (.step 7 (.split 36 0 (.split 38 0 (.step 23 (.step 17 (.close 19))) (.step 19 (.close 5))) (.step 20 (.step 4 (.step 8 (.close 17))))))) (.step 7 (.step 33 (.split 34 0 (.step 20 (.step 55 (.step 19 (.step 20 (.step 4 (.close 8)))))) (.step 33 (.step 20 (.step 23 (.step 17 (.close 20)))))))))))
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
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813224438762371732944345780136706048⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 11 0 (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.step 28 (.step 48 (.close 16))) (.split 34 0 (.step 55 (.close 28)) (.step 33 (.step 55 (.close 33))))) (.step 7 (.close 28))) (.step 7 (.split 30 0 (.step 55 (.step 4 (.step 8 (.close 16)))) (.step 33 (.step 23 (.step 17 (.close 37))))))) (.step 7 (.split 22 0 (.split 30 0 (.step 55 (.step 4 (.step 8 (.close 16)))) (.step 33 (.step 23 (.step 17 (.close 37))))) (.split 34 0 (.split 36 0 (.step 55 (.step 4 (.step 8 (.close 19)))) (.step 39 (.step 4 (.step 8 (.close 20))))) (.step 39 (.split 38 0 (.step 23 (.step 17 (.close 20))) (.step 19 (.close 23))))))))) (.reuse 0)) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 30 0 (.split 43 0 (.step 16 (.step 4 (.close 14))) (.step 28 (.step 13 (.close 8)))) (.step 13 (.step 33 (.step 23 (.close 15))))) (.step 7 (.step 28 (.close 4)))) (.step 7 (.step 13 (.step 40 (.step 8 (.step 4 (.step 14 (.step 19 (.close 20))))))))) (.split 22 0 (.step 7 (.step 13 (.step 40 (.step 8 (.step 4 (.step 14 (.step 19 (.close 20)))))))) (.step 13 (.step 7 (.step 20 (.step 8 (.step 4 (.close 14)))))))) (.split 17 0 (.split 22 0 (.step 7 (.step 13 (.step 40 (.step 8 (.step 4 (.step 14 (.close 19))))))) (.step 13 (.step 7 (.step 19 (.step 23 (.step 4 (.step 8 (.close 20)))))))) (.split 25 0 (.step 19 (.step 13 (.step 20 (.step 4 (.close 8))))) (.step 7 (.step 19 (.close 4))))))))
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
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813225706412971961173747276839911424⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.reuse 0) (.run (.step 7 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.step 55 (.close 13)) (.step 33 (.step 16 (.step 13 (.close 4))))) (.step 13 (.step 33 (.step 4 (.step 14 (.close 16)))))) (.step 13 (.split 38 0 (.step 55 (.step 33 (.step 14 (.step 17 (.close 39))))) (.step 33 (.step 5 (.step 8 (.close 14))))))) (.step 13 (.split 38 0 (.split 47 0 (.split 50 0 (.step 20 (.step 14 (.step 17 (.close 39)))) (.step 33 (.step 20 (.step 14 (.close 15))))) (.step 33 (.step 23 (.step 17 (.step 4 (.step 8 (.close 20))))))) (.step 33 (.step 20 (.step 4 (.step 5 (.close 14)))))))) (.split 17 0 (.step 13 (.split 38 0 (.split 47 0 (.split 50 0 (.step 40 (.step 14 (.step 17 (.step 20 (.close 38))))) (.step 33 (.step 24 (.close 15)))) (.step 33 (.step 23 (.step 17 (.step 4 (.step 8 (.close 19))))))) (.step 33 (.step 23 (.close 5))))) (.split 30 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 55 (.step 19 (.step 13 (.step 4 (.close 8))))) (.step 13 (.close 19))) (.step 13 (.close 20))) (.step 13 (.step 14 (.step 15 (.close 17))))) (.step 13 (.step 33 (.step 20 (.step 25 (.step 4 (.close 8))))))))) (.step 13 (.step 16 (.close 13)))))))
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

namespace Part3
def root : Box := ⟨1073741824, 4898883310657342436947854453666805651352363424560975156020431245054782664320940005102763692316592448381902181992067844711047607045138012867784568757882690690803978253813225706412971961174873176746754048⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.reuse 0) (.run (.split 11 0 (.step 7 (.split 16 0 (.step 7 (.split 34 0 (.split 36 0 (.step 7 (.step 4 (.close 8))) (.step 7 (.close 5))) (.step 7 (.step 28 (.step 4 (.close 5)))))) (.step 7 (.close 8)))) (.split 16 0 (.split 17 0 (.split 25 0 (.step 7 (.split 34 0 (.step 7 (.close 8)) (.step 7 (.close 8)))) (.split 34 0 (.split 36 0 (.split 43 0 (.split 49 0 (.split 30 0 (.step 8 (.close 4)) (.step 4 (.step 7 (.close 8)))) (.step 4 (.close 5))) (.step 8 (.step 4 (.close 7)))) (.step 4 (.step 7 (.close 8)))) (.step 28 (.step 4 (.close 7))))) (.step 7 (.close 8))) (.split 17 0 (.step 7 (.close 8)) (.step 7 (.close 8)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part3.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case48

namespace FiveColour.Packed.EnumerationChunks.Projected.Case48
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 292 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 292 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 292 0).upper i := by decide +kernel
lemma budget_model : (⟨37630511536740859966423, 5789234131009369111655880410916383799149935097950111679937790244350696937832588910803674238545500183085609357535611307840729301634221804252716538090356296810875202044827950228461282219658217406305038239415791728186442646529, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 292), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨37630511536740859966423, 5789234131009369111655880410916383799149935097950111679937790244350696937832588910803674238545500183085609357535611307840729301634221804252716538090356296810875202044827950228461282219658217406305038239415791728186442646529, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 292) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 292 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 292 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 292) (Archive.root 292) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 292 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 292 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case48

namespace FiveColour.Packed.EnumerationChunks.Case48
def root : Box := Archive.root 292
def families : Fin 78 → List Cut := Enumeration.families 292
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case48.original_covered points
end FiveColour.Packed.EnumerationChunks.Case48
