module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case20
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709306090557319735235325418166055684768607570398085481702974350607668232618770432⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨18740915245514405755619, 5789228615351851010618494880448709935079879776571393911013839255768432661963521880064360904848620755638098170412487433395995188289264892881255633757817586178196485084283839045905928401896080274871501735988781987986060346368, 0⟩]
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
def root : Box := ⟨1073741824, 5783580587434429433756673792145735206580520665929650998089006169603204882733306204983209466308492360280898516913063084129317040523543693734538709306090557319735235325418166055684768607570398085481702974350607668232618770432⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.split 30 0 (.step 43 (.close 7)) (.step 7 (.step 33 (.close 5)))) (.step 7 (.close 5))) (.step 7 (.step 5 (.close 7)))) (.step 7 (.step 24 (.step 5 (.close 33))))) (.step 7 (.step 54 (.close 24)))) (.step 7 (.split 38 0 (.step 53 (.step 20 (.step 5 (.close 11)))) (.step 33 (.step 5 (.step 11 (.close 17))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 24 0 (.split 25 0 (.step 52 (.step 7 (.step 5 (.close 11)))) (.step 7 (.close 5))) (.step 7 (.close 5))) (.step 7 (.step 24 (.step 11 (.close 5))))) (.step 7 (.split 22 0 (.step 24 (.step 11 (.close 5))) (.step 20 (.step 11 (.step 5 (.close 17))))))) (.step 7 (.split 17 0 (.step 42 (.step 53 (.step 5 (.step 11 (.close 17))))) (.step 19 (.step 20 (.close 11))))))) (.step 7 (.split 14 0 (.split 16 0 (.split 17 0 (.step 52 (.step 43 (.close 11))) (.step 13 (.split 38 0 (.step 24 (.step 25 (.step 24 (.close 15)))) (.step 33 (.close 5))))) (.step 13 (.split 38 0 (.split 39 0 (.split 50 0 (.step 20 (.step 5 (.close 11))) (.step 24 (.step 25 (.close 15)))) (.step 17 (.step 19 (.close 5)))) (.step 33 (.step 5 (.step 14 (.step 5 (.close 11)))))))) (.step 13 (.close 5))))) (.step 7 (.split 16 0 (.step 7 (.split 24 0 (.step 7 (.close 5)) (.step 9 (.step 11 (.close 5))))) (.step 7 (.step 8 (.close 11)))))))
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
end FiveColour.Packed.EnumerationChunks.Projected.Case20

namespace FiveColour.Packed.EnumerationChunks.Projected.Case20
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 264 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 264 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 264 0).upper i := by decide +kernel
lemma budget_model : (⟨18740915245514405755619, 5789228615351851010618494880448709935079879776571393911013839255768432661963521880064360904848620755638098170412487433395995188289264892881255633757817586178196485084283839045905928401896080274871501735988781987986060346368, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 264), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨18740915245514405755619, 5789228615351851010618494880448709935079879776571393911013839255768432661963521880064360904848620755638098170412487433395995188289264892881255633757817586178196485084283839045905928401896080274871501735988781987986060346368, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 264) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 264 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 264 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 264) (Archive.root 264) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 264 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 264 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case20

namespace FiveColour.Packed.EnumerationChunks.Case20
def root : Box := Archive.root 264
def families : Fin 78 → List Cut := Enumeration.families 264
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case20.original_covered points
end FiveColour.Packed.EnumerationChunks.Case20
