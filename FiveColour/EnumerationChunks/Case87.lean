module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case87
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1, 5653548956058700166731417831957222835792060869588458894420752633442121112516058933536319246290492648189535944136999435573090003575782175849212904177256684980701058685762056803967313027059914440807907888584654501214945281⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨21221736057412879896382, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340644790595964978494840224447424232708447491047989970029606261225677024092266535310765487517604899868114945, 0⟩]
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
def root : Box := ⟨1, 5653548956058700166731417831957222835792060869588458894420752633442121112516058933536319246290492648189535944136999435573090003575782175849212904177256684980701058685762056803967313025730686445022992014527925936327753729⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 7 0 (.split 18 0 (.split 23 0 (.split 25 0 (.split 13 0 (.split 63 0 (.step 31 (.step 5 (.step 31 (.close 38)))) (.step 37 (.step 5 (.step 22 (.step 21 (.step 31 (.close 38))))))) (.step 31 (.step 37 (.step 22 (.step 21 (.close 38)))))) (.step 29 (.split 13 0 (.split 60 0 (.step 48 (.step 37 (.step 22 (.step 5 (.close 31))))) (.step 5 (.step 31 (.step 37 (.close 38))))) (.step 31 (.step 37 (.step 22 (.step 21 (.close 38)))))))) (.step 75 (.step 31 (.close 28)))) (.split 13 0 (.split 23 0 (.step 31 (.step 38 (.step 31 (.close 28)))) (.step 75 (.step 31 (.close 21)))) (.split 19 0 (.step 71 (.step 38 (.step 31 (.step 16 (.close 21))))) (.split 25 0 (.step 71 (.step 15 (.step 21 (.step 22 (.step 16 (.close 21)))))) (.step 16 (.step 37 (.step 21 (.step 22 (.step 21 (.close 5)))))))))) (.split 25 0 (.split 34 0 (.step 71 (.step 29 (.step 63 (.step 21 (.close 22))))) (.split 13 0 (.step 31 (.step 29 (.step 63 (.step 21 (.close 22))))) (.step 37 (.step 10 (.close 16))))) (.step 29 (.step 6 (.close 16))))))
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
def root : Box := ⟨1152921504606846977, 5653548956058700166731417831957222835792060869588458894420752633442121112516058933536319246290492648189535944136999435573090003575782175849212904177256684980701058685762056803967313027059914440807907888584654501214945281⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 7 0 (.split 12 0 (.split 18 0 (.split 23 0 (.split 25 0 (.split 38 0 (.split 73 0 (.step 31 (.step 11 (.close 15))) (.step 31 (.step 6 (.close 10)))) (.step 28 (.step 31 (.step 38 (.step 31 (.close 5)))))) (.step 28 (.step 9 (.step 12 (.step 15 (.close 16)))))) (.step 31 (.step 63 (.step 75 (.step 31 (.step 9 (.close 10))))))) (.split 13 0 (.step 38 (.step 31 (.step 63 (.step 31 (.step 9 (.step 10 (.close 21))))))) (.step 15 (.step 31 (.step 10 (.step 21 (.step 31 (.step 16 (.step 9 (.close 21)))))))))) (.split 13 0 (.split 23 0 (.split 25 0 (.split 18 0 (.split 38 0 (.step 15 (.step 31 (.close 11))) (.step 28 (.step 15 (.step 31 (.close 5))))) (.step 15 (.step 31 (.step 21 (.step 10 (.step 21 (.close 22))))))) (.step 9 (.close 28))) (.step 9 (.step 15 (.step 75 (.step 31 (.close 10)))))) (.step 9 (.step 15 (.close 6))))) (.split 13 0 (.split 18 0 (.step 29 (.step 31 (.step 63 (.split 34 0 (.step 9 (.step 15 (.close 21))) (.step 15 (.step 9 (.close 21))))))) (.step 9 (.step 29 (.step 21 (.step 6 (.step 9 (.close 15))))))) (.step 9 (.step 15 (.step 29 (.step 16 (.step 6 (.step 9 (.close 10))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1, 5653548956058700166731417831957222835792060869588458894420752633442121112516058933536319246290492648189535944136999435573090003575782175849212904177256684980701058685762056803967313027059914440807907888584654501214945281⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 6 0 (.split 12 0 (.reuse 0) (.run (.split 13 0 (.split 7 0 (.split 23 0 (.split 25 0 (.split 18 0 (.step 31 (.step 37 (.step 22 (.close 5)))) (.step 31 (.step 38 (.step 15 (.step 21 (.close 22)))))) (.step 29 (.step 31 (.step 37 (.step 31 (.step 22 (.close 5))))))) (.step 75 (.step 31 (.step 15 (.close 21))))) (.step 29 (.step 31 (.step 63 (.step 15 (.step 21 (.close 22))))))) (.split 25 0 (.split 26 0 (.step 15 (.step 31 (.step 16 (.close 12)))) (.step 63 (.split 7 0 (.step 31 (.split 18 0 (.split 34 0 (.step 15 (.step 21 (.close 31))) (.step 15 (.step 16 (.close 31)))) (.step 15 (.close 21)))) (.step 10 (.step 5 (.close 15)))))) (.step 9 (.step 31 (.step 15 (.close 16)))))))) (.reuse 1))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part2.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case87

namespace FiveColour.Packed.EnumerationChunks.Projected.Case87
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 331 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 331 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 331 0).upper i := by decide +kernel
lemma budget_model : (⟨21221736057412879896382, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340644790595964978494840224447424232708447491047989970029606261225677024092266535310765487517604899868114945, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 331), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨21221736057412879896382, 5653548961323972919750935910373634003956179490728538149207183478557268316910687518202790982855978902426053129357340644790595964978494840224447424232708447491047989970029606261225677024092266535310765487517604899868114945, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 331) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 331 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 331 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 331) (Archive.root 331) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 331 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 331 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case87

namespace FiveColour.Packed.EnumerationChunks.Case87
def root : Box := Archive.root 331
def families : Fin 78 → List Cut := Enumeration.families 331
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case87.original_covered points
end FiveColour.Packed.EnumerationChunks.Case87
