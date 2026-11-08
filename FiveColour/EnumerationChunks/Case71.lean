module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case71
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510728490837553873562786353657906403980233452264643311543525991831341231804033785833920434893103466315599146474004651586992199080845060955209186264820709222895434779542421504⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨32908917104513633811447, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910783464123183971966183505480246655101777156571565223628287311696793642513456346367764851812016709392942153860097, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743458514510728490837553873562786353657906403980233452264643311543525991831341231804033785833920434893103466315599146474004651586992199080845060955209186264820709222895434779542421504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 0 (.split 38 0 (.split 17 0 (.split 22 0 (.step 54 (.close 38)) (.step 45 (.step 14 (.step 17 (.step 20 (.close 39)))))) (.split 34 0 (.split 42 0 (.step 20 (.step 23 (.close 39))) (.split 22 0 (.step 39 (.close 23)) (.step 25 (.close 20)))) (.split 42 0 (.split 51 0 (.step 20 (.step 17 (.close 39))) (.step 39 (.close 20))) (.step 39 (.step 25 (.close 45)))))) (.step 33 (.split 17 0 (.split 51 0 (.step 45 (.close 5)) (.step 39 (.step 45 (.close 5)))) (.step 39 (.step 23 (.close 5)))))) (.step 33 (.split 17 0 (.split 51 0 (.step 45 (.close 4)) (.step 39 (.step 45 (.close 4)))) (.step 39 (.step 24 (.close 4)))))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case71

namespace FiveColour.Packed.EnumerationChunks.Projected.Case71
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 315 0 10 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 315 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 315 0).upper i := by decide +kernel
lemma budget_model : (⟨32908917104513633811447, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910783464123183971966183505480246655101777156571565223628287311696793642513456346367764851812016709392942153860097, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 315), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908917104513633811447, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910783464123183971966183505480246655101777156571565223628287311696793642513456346367764851812016709392942153860097, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 315) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 315 0 10).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 10)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 10 families = caseProblem 315 0 10 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 315) (Archive.root 315) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 315 0 10 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 315 0 10).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case71

namespace FiveColour.Packed.EnumerationChunks.Case71
def root : Box := Archive.root 315
def families : Fin 78 → List Cut := Enumeration.families 315
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case71.original_covered points
end FiveColour.Packed.EnumerationChunks.Case71
