module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case68
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055221114677693970840402853060144478704032022528⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
  else if r.val = 2 then [⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩]
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
def root : Box := ⟨1461501637330902918203684832716283019657006284800, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055219720881119061408805906849523036684734693376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 29 (.step 38 (.step 24 (.step 15 (.close 37))))) (.step 38 (.close 11))) (.split 30 0 (.step 45 (.split 34 0 (.step 11 (.step 19 (.close 20))) (.step 24 (.step 19 (.step 33 (.step 37 (.close 45))))))) (.step 33 (.step 25 (.step 24 (.step 25 (.step 11 (.close 15)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 11 (.step 20 (.step 24 (.close 25)))) (.step 19 (.step 24 (.step 19 (.step 25 (.close 33)))))) (.split 35 0 (.split 43 0 (.step 24 (.step 25 (.step 37 (.close 66)))) (.step 11 (.close 20))) (.step 24 (.step 33 (.step 25 (.close 37)))))) (.step 33 (.step 38 (.close 20)))) (.split 34 0 (.split 30 0 (.split 35 0 (.step 20 (.step 11 (.step 20 (.step 19 (.close 25))))) (.step 19 (.close 25))) (.step 19 (.step 20 (.step 11 (.close 24))))) (.split 35 0 (.split 30 0 (.split 36 0 (.step 25 (.step 11 (.close 19))) (.step 20 (.step 25 (.close 66)))) (.step 20 (.step 19 (.step 24 (.close 25))))) (.step 24 (.step 38 (.close 19))))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1461501637330902919471335432944512421153709490176, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055219720881119062676456507077752438181437898752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 24 (.step 20 (.close 38)))))) (.step 33 (.step 13 (.step 24 (.close 29))))) (.split 35 0 (.split 30 0 (.step 17 (.step 37 (.step 17 (.step 20 (.close 39))))) (.step 13 (.step 33 (.step 38 (.close 39))))) (.step 17 (.step 33 (.step 15 (.step 37 (.step 15 (.close 39)))))))) (.split 35 0 (.step 13 (.split 64 0 (.split 42 0 (.split 67 0 (.step 17 (.step 11 (.close 20))) (.step 25 (.step 17 (.close 20)))) (.step 25 (.close 20))) (.step 17 (.step 19 (.close 24))))) (.step 17 (.step 19 (.step 13 (.step 19 (.close 24))))))) (.split 22 0 (.split 35 0 (.step 13 (.split 64 0 (.split 36 0 (.split 42 0 (.step 17 (.step 11 (.close 20))) (.step 25 (.step 11 (.step 15 (.close 17))))) (.step 20 (.step 17 (.step 24 (.close 25))))) (.step 17 (.step 19 (.step 20 (.close 11)))))) (.step 17 (.step 19 (.step 13 (.step 19 (.close 24)))))) (.split 30 0 (.split 35 0 (.step 20 (.step 13 (.step 17 (.step 11 (.close 19))))) (.step 17 (.close 19))) (.step 19 (.step 13 (.step 20 (.close 25))))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1267650600228229401497776947200, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055219720881119062676456507077752438181437898752⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.run (.split 17 0 (.split 22 0 (.split 30 0 (.step 29 (.step 66 (.step 19 (.step 20 (.close 33))))) (.split 34 0 (.step 33 (.step 13 (.step 20 (.step 24 (.close 29))))) (.split 35 0 (.split 43 0 (.step 66 (.step 13 (.close 15))) (.step 13 (.step 15 (.step 29 (.step 33 (.close 39)))))) (.step 33 (.close 37))))) (.split 34 0 (.split 35 0 (.step 13 (.step 24 (.step 33 (.step 24 (.step 20 (.close 39)))))) (.step 33 (.step 13 (.step 24 (.close 29))))) (.step 45 (.step 17 (.step 15 (.step 13 (.step 17 (.close 33)))))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 13 (.step 20 (.close 11))) (.step 29 (.step 24 (.step 13 (.step 19 (.close 33)))))) (.step 39 (.step 17 (.close 33)))) (.step 33 (.step 13 (.step 39 (.step 11 (.close 15)))))) (.split 35 0 (.step 13 (.split 64 0 (.split 42 0 (.step 20 (.step 11 (.close 17))) (.step 25 (.close 20))) (.step 17 (.step 20 (.step 11 (.close 24)))))) (.step 17 (.step 19 (.step 13 (.step 33 (.step 20 (.step 11 (.close 24))))))))))) (.reuse 0))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984016593719477346791051369067420115632057551396274176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 24 (.step 11 (.close 13))) (.step 29 (.split 30 0 (.step 39 (.step 13 (.step 15 (.close 37)))) (.step 33 (.step 13 (.step 15 (.close 19))))))) (.split 35 0 (.step 37 (.close 11)) (.step 29 (.step 37 (.close 17))))) (.split 34 0 (.split 35 0 (.step 13 (.step 24 (.step 25 (.close 11)))) (.step 75 (.step 13 (.step 19 (.step 11 (.close 20)))))) (.step 43 (.step 17 (.step 33 (.close 37)))))) (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 11 (.step 13 (.close 20))) (.step 29 (.step 37 (.step 19 (.close 20))))) (.step 37 (.close 11))) (.split 34 0 (.split 35 0 (.step 13 (.step 20 (.close 11))) (.step 19 (.step 13 (.step 20 (.step 11 (.close 24)))))) (.step 43 (.close 17)))) (.split 30 0 (.split 34 0 (.step 11 (.step 74 (.step 13 (.step 20 (.close 19))))) (.step 17 (.close 20))) (.split 34 0 (.split 35 0 (.step 13 (.step 20 (.step 11 (.close 24)))) (.step 11 (.step 19 (.step 13 (.step 20 (.close 24)))))) (.step 13 (.step 17 (.close 20))))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨1393796574908163946345982392040523667865600, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055221114677693969572752252831915077207328817152⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.reuse 0) (.run (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.step 11 (.step 13 (.step 19 (.close 20)))) (.step 29 (.step 19 (.step 13 (.step 15 (.step 19 (.close 33))))))) (.step 37 (.close 11))) (.step 38 (.step 11 (.close 13)))) (.split 30 0 (.split 34 0 (.step 11 (.step 67 (.step 13 (.step 19 (.step 20 (.close 24)))))) (.step 17 (.close 20))) (.split 35 0 (.step 13 (.step 25 (.step 11 (.step 17 (.close 19))))) (.step 11 (.step 17 (.close 19)))))) (.split 22 0 (.split 30 0 (.split 34 0 (.step 11 (.step 67 (.step 13 (.step 19 (.close 20))))) (.step 17 (.close 20))) (.split 35 0 (.step 13 (.step 20 (.step 11 (.step 17 (.close 19))))) (.step 11 (.step 17 (.close 19))))) (.split 30 0 (.split 35 0 (.step 20 (.step 11 (.step 13 (.step 17 (.close 19))))) (.step 11 (.step 17 (.close 19)))) (.step 19 (.step 13 (.step 20 (.close 25)))))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨1073741824, 5783586108473071698929506992293283173689605865403748829234258798600698237984932249075538293338561526017866652360432011304045101065982144014671948722836353201192589165964984018055221114677693970840402853060144478704032022528⟩
def references : Fin 3 → Box := ![Part0.root, Part2.root, Part4.root]
def proof : Chunks.Proof 3 := (.split 14 0 (.split 10 0 (.split 16 0 (.run (.split 17 0 (.split 22 0 (.step 29 (.split 30 0 (.step 39 (.close 15)) (.step 38 (.step 39 (.close 15))))) (.split 34 0 (.split 35 0 (.step 24 (.step 11 (.step 20 (.step 24 (.close 25))))) (.step 29 (.step 33 (.step 20 (.close 24))))) (.step 45 (.step 29 (.step 43 (.step 19 (.close 33))))))) (.split 22 0 (.split 30 0 (.step 29 (.step 39 (.step 15 (.step 19 (.close 33))))) (.split 34 0 (.step 33 (.step 20 (.close 11))) (.step 39 (.step 24 (.step 19 (.step 25 (.close 33))))))) (.split 30 0 (.step 45 (.split 34 0 (.step 11 (.step 20 (.close 19))) (.step 24 (.step 19 (.step 33 (.step 37 (.close 45))))))) (.step 33 (.step 25 (.step 20 (.close 11)))))))) (.reuse 0)) (.reuse 1)) (.split 10 0 (.reuse 2) (.run (.split 16 0 (.split 17 0 (.split 34 0 (.split 36 0 (.split 43 0 (.step 13 (.step 15 (.step 17 (.close 19)))) (.split 22 0 (.step 15 (.close 11)) (.step 13 (.close 11)))) (.step 13 (.step 11 (.step 15 (.step 19 (.close 33)))))) (.split 22 0 (.split 30 0 (.step 37 (.close 11)) (.split 64 0 (.step 13 (.close 17)) (.step 15 (.close 17)))) (.step 17 (.close 13)))) (.split 22 0 (.split 34 0 (.step 13 (.step 11 (.step 15 (.step 17 (.close 19))))) (.step 17 (.close 13))) (.step 13 (.step 11 (.step 15 (.close 17)))))) (.split 17 0 (.split 22 0 (.split 34 0 (.step 13 (.step 11 (.step 15 (.step 17 (.close 19))))) (.step 17 (.close 13))) (.step 13 (.step 11 (.step 15 (.close 17))))) (.step 17 (.close 13)))))))
theorem accepted : Fast.check 10 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 10 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part2.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 10 families root :=
  Fast.check_sound 10 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 10 families root := Part5.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case68

namespace FiveColour.Packed.EnumerationChunks.Projected.Case68
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 312 0 10 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 312 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 312 0).upper i := by decide +kernel
lemma budget_model : (⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 312), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 312) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 312 0 10).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 10)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 10 families = caseProblem 312 0 10 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 312) (Archive.root 312) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 312 0 10 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 312 0 10).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case68

namespace FiveColour.Packed.EnumerationChunks.Case68
def root : Box := Archive.root 312
def families : Fin 78 → List Cut := Enumeration.families 312
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case68.original_covered points
end FiveColour.Packed.EnumerationChunks.Case68
