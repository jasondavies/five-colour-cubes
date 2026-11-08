module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case25
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385586728141404972673629630318493447000376569233148566601628212473635345675197612032⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908284911715838913447, 5789234131004114107589341883129531770018971867894994468411955019690277647889009051559687699629171582451667236722394843212749036780556536815853887133914354043305755671668584339630966863574716854696998678016360900365014533121, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385586728141404972673629630318493447000376569233148566601628212473635345675197612032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.split 10 0 (.split 16 0 (.split 22 0 (.split 12 0 (.split 49 0 (.step 7 (.split 17 0 (.step 29 (.step 7 (.step 9 (.close 18)))) (.step 7 (.step 39 (.close 4))))) (.step 37 (.step 7 (.step 43 (.step 9 (.step 18 (.step 7 (.close 21)))))))) (.step 29 (.step 37 (.step 7 (.step 9 (.step 18 (.close 33))))))) (.step 7 (.step 45 (.step 7 (.close 43))))) (.step 7 (.split 17 0 (.split 22 0 (.step 38 (.step 7 (.step 4 (.close 9)))) (.step 7 (.step 24 (.step 38 (.step 23 (.step 9 (.close 13))))))) (.step 7 (.step 39 (.step 24 (.step 38 (.step 4 (.close 9))))))))) (.step 7 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.step 7 (.step 15 (.step 13 (.step 9 (.close 18))))) (.step 7 (.close 15))) (.step 7 (.step 13 (.step 43 (.step 4 (.close 5)))))) (.step 7 (.step 13 (.step 39 (.step 4 (.step 9 (.close 5))))))) (.step 7 (.step 13 (.split 35 0 (.split 38 0 (.step 43 (.step 14 (.step 17 (.close 20)))) (.step 23 (.step 5 (.step 4 (.close 15))))) (.step 33 (.step 24 (.step 4 (.step 9 (.close 15))))))))))) (.split 16 0 (.split 25 0 (.split 26 0 (.step 7 (.close 9)) (.split 34 0 (.step 7 (.close 9)) (.step 29 (.close 7)))) (.split 26 0 (.split 34 0 (.step 7 (.close 9)) (.step 29 (.close 7))) (.step 29 (.close 4)))) (.step 7 (.step 29 (.close 7))))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case25

namespace FiveColour.Packed.EnumerationChunks.Projected.Case25
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 269 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 269 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 269 0).upper i := by decide +kernel
lemma budget_model : (⟨32908284911715838913447, 5789234131004114107589341883129531770018971867894994468411955019690277647889009051559687699629171582451667236722394843212749036780556536815853887133914354043305755671668584339630966863574716854696998678016360900365014533121, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 269), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908284911715838913447, 5789234131004114107589341883129531770018971867894994468411955019690277647889009051559687699629171582451667236722394843212749036780556536815853887133914354043305755671668584339630966863574716854696998678016360900365014533121, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 269) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 269 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 269 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 269) (Archive.root 269) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 269 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 269 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case25

namespace FiveColour.Packed.EnumerationChunks.Case25
def root : Box := Archive.root 269
def families : Fin 78 → List Cut := Enumeration.families 269
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case25.original_covered points
end FiveColour.Packed.EnumerationChunks.Case25
