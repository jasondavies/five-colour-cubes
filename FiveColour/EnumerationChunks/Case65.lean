module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case65
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 4898883310657342436947854453662941113829342651439877817257322135417574524641937045872157746694534288946432808933277465536114757720652315297179625524486576508989969954327617120681802983943955045261770752⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨37630669409018422557687, 5789234131009374248507346766749891419687533244750779835710650130547166070165997423784225875531183789473991668342093468871764627366270137944873799542728008123750934930136012272409766640092332188979741397452445100402566759425, 0⟩]
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
def root : Box := ⟨1073741824, 4898883310657342436947854453662941113829342651439877817257322135417574524641937045872157746694534288946432808933277465536114757720652315297179625524486576508989969954327617120681802983943955045261770752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 49 0 (.split 38 0 (.split 50 0 (.split 22 0 (.step 39 (.step 14 (.close 38))) (.split 34 0 (.step 20 (.step 23 (.close 39))) (.split 36 0 (.step 25 (.step 14 (.close 43))) (.step 45 (.step 14 (.step 17 (.close 20))))))) (.step 33 (.step 43 (.step 45 (.step 17 (.close 19)))))) (.step 33 (.step 55 (.close 16)))) (.step 13 (.split 38 0 (.split 50 0 (.step 43 (.step 45 (.step 17 (.close 20)))) (.step 33 (.step 43 (.step 45 (.step 17 (.close 24)))))) (.step 33 (.step 43 (.close 16))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part0.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case65

namespace FiveColour.Packed.EnumerationChunks.Projected.Case65
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 309 0 11 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 309 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 309 0).upper i := by decide +kernel
lemma budget_model : (⟨37630669409018422557687, 5789234131009374248507346766749891419687533244750779835710650130547166070165997423784225875531183789473991668342093468871764627366270137944873799542728008123750934930136012272409766640092332188979741397452445100402566759425, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 309), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨37630669409018422557687, 5789234131009374248507346766749891419687533244750779835710650130547166070165997423784225875531183789473991668342093468871764627366270137944873799542728008123750934930136012272409766640092332188979741397452445100402566759425, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 309) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 309 0 11).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 11)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 11 families = caseProblem 309 0 11 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 309) (Archive.root 309) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 309 0 11 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 309 0 11).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case65

namespace FiveColour.Packed.EnumerationChunks.Case65
def root : Box := Archive.root 309
def families : Fin 78 → List Cut := Enumeration.families 309
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case65.original_covered points
end FiveColour.Packed.EnumerationChunks.Case65
