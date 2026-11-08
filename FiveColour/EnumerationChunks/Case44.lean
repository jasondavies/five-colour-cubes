module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case44
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584875467977175614502853182733307993850916913393916352603581152291217965611745280⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584875467977175614502853182733307993850916913393915084952980922908894964301692928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 17 0 (.split 12 0 (.split 22 0 (.step 58 (.step 9 (.step 33 (.close 37)))) (.step 7 (.step 43 (.step 4 (.close 5))))) (.split 22 0 (.split 25 0 (.step 29 (.step 15 (.step 37 (.step 18 (.close 33))))) (.step 29 (.step 7 (.close 9)))) (.step 37 (.step 7 (.step 18 (.step 9 (.step 33 (.close 38)))))))) (.split 22 0 (.split 12 0 (.step 7 (.step 39 (.step 4 (.step 9 (.close 5))))) (.step 37 (.step 7 (.step 18 (.step 9 (.step 33 (.close 38))))))) (.step 7 (.split 12 0 (.step 39 (.step 23 (.step 9 (.close 17)))) (.step 13 (.step 24 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20))))))))))) (.split 17 0 (.split 22 0 (.split 12 0 (.step 7 (.step 38 (.step 4 (.step 9 (.close 5))))) (.step 37 (.step 7 (.step 18 (.step 9 (.step 33 (.close 38))))))) (.step 7 (.split 12 0 (.step 45 (.step 23 (.step 9 (.step 17 (.close 19))))) (.step 13 (.step 24 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20)))))))))) (.split 22 0 (.step 7 (.split 12 0 (.step 39 (.step 23 (.step 9 (.close 17)))) (.step 13 (.step 24 (.step 37 (.step 4 (.step 9 (.step 19 (.close 20))))))))) (.split 30 0 (.step 24 (.step 7 (.step 19 (.step 4 (.step 5 (.close 20)))))) (.step 7 (.step 24 (.step 20 (.close 4)))))))))
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584875467977175614502853182733307993850916913393916352603581152291217965611745280⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.split 10 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 12 0 (.step 7 (.step 52 (.step 58 (.step 9 (.close 33))))) (.step 37 (.step 7 (.step 13 (.close 15))))) (.step 7 (.split 12 0 (.step 45 (.step 13 (.step 15 (.step 4 (.close 9))))) (.step 13 (.close 4))))) (.step 7 (.split 12 0 (.split 22 0 (.step 39 (.step 13 (.step 4 (.step 9 (.close 5))))) (.step 13 (.step 24 (.step 39 (.step 4 (.close 5)))))) (.step 13 (.close 4))))) (.step 7 (.split 12 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 43 (.step 4 (.close 5))) (.step 13 (.step 33 (.close 38)))) (.step 13 (.step 24 (.step 45 (.step 4 (.close 5)))))) (.step 13 (.split 35 0 (.split 38 0 (.step 24 (.step 14 (.close 20))) (.step 23 (.step 14 (.close 19)))) (.step 24 (.step 4 (.close 5)))))) (.step 13 (.close 4))))))) (.run (.split 16 0 (.split 25 0 (.split 34 0 (.step 7 (.close 9)) (.split 49 0 (.split 50 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.split 34 0 (.split 35 0 (.step 7 (.close 9)) (.step 29 (.close 4))) (.step 29 (.close 7)))) (.step 7 (.step 29 (.step 7 (.close 9)))))))
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

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part1.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case44

namespace FiveColour.Packed.EnumerationChunks.Projected.Case44
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 288 0 12 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 288 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 288 0).upper i := by decide +kernel
lemma budget_model : (⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 288), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 288) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 288 0 12).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 12)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 12 families = caseProblem 288 0 12 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 288) (Archive.root 288) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 288 0 12 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 288 0 12).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case44

namespace FiveColour.Packed.EnumerationChunks.Case44
def root : Box := Archive.root 288
def families : Fin 78 → List Cut := Enumeration.families 288
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case44.original_covered points
end FiveColour.Packed.EnumerationChunks.Case44
