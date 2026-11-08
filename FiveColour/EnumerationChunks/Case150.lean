module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case150
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 10273712730478288321023642923791353606196196407812131726871936621419135109769172305990500435502698646277160710723671530593951730670736222394774007769655957198336352452447008444936506055575773247186529945649152⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨37033564156298044177383, 5789234131004114112605798393242650429804653116085229495907826956687667789266125362145452370754004878501022282187955398943580153440264784719876785736443695986532384820264588047565369260442422522659787644311954017558436250625, 0⟩]
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
def root : Box := ⟨2147483648, 10273712730478288321023642923791353606196196407812131726871936621419135109769172305990500435502698646277160710723671530593951730670736222394774007769655957198336352452447008444936506055575773247186529945649152⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 16 1 (.split 17 1 (.step 7 (.split 34 1 (.split 36 1 (.step 7 (.step 54 (.step 70 (.split 17 0 (.split 36 0 (.step 46 (.split 22 0 (.split 42 0 (.split 49 1 (.split 50 1 (.split 59 1 (.step 64 (.step 7 (.step 65 (.close 7)))) (.step 62 (.step 7 (.step 52 (.step 53 (.step 64 (.step 7 (.step 27 (.close 65))))))))) (.step 53 (.close 7))) (.step 52 (.close 7))) (.step 7 (.step 52 (.step 10 (.step 53 (.step 22 (.step 26 (.close 52)))))))) (.step 7 (.step 52 (.step 30 (.step 53 (.step 36 (.step 44 (.close 52))))))))) (.step 7 (.step 46 (.step 52 (.step 10 (.step 53 (.step 22 (.step 26 (.close 52))))))))) (.step 7 (.step 46 (.step 52 (.step 30 (.step 53 (.step 36 (.step 44 (.close 52)))))))))))) (.step 7 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52))))) (.step 7 (.split 49 1 (.split 50 1 (.step 7 (.step 37 (.close 64))) (.step 7 (.close 37))) (.step 7 (.step 37 (.close 52))))))) (.step 7 (.split 49 1 (.step 7 (.close 64)) (.step 7 (.close 52))))) (.step 7 (.split 49 1 (.split 50 1 (.step 7 (.step 19 (.close 64))) (.step 7 (.close 19))) (.step 7 (.step 19 (.close 52))))))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case150

namespace FiveColour.Packed.EnumerationChunks.Projected.Case150
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 37 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 37 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 37 0).upper i := by decide +kernel
lemma budget_model : (⟨37033564156298044177383, 5789234131004114112605798393242650429804653116085229495907826956687667789266125362145452370754004878501022282187955398943580153440264784719876785736443695986532384820264588047565369260442422522659787644311954017558436250625, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 37), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨37033564156298044177383, 5789234131004114112605798393242650429804653116085229495907826956687667789266125362145452370754004878501022282187955398943580153440264784719876785736443695986532384820264588047565369260442422522659787644311954017558436250625, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 37) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 37 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 37 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 37) (Archive.root 37) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 37 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 37 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case150

namespace FiveColour.Packed.EnumerationChunks.Case150
def root : Box := Archive.root 37
def families : Fin 78 → List Cut := Enumeration.families 37
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case150.original_covered points
end FiveColour.Packed.EnumerationChunks.Case150
