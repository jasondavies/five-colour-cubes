module
public import FiveColour.RootProjection
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.Projection
open Physical

/-- One encoded header, independent of the number of roots and original total. -/
def root (header : Archive.Header) : Box := ⟨header.lower, header.upper⟩
def budgetCut (header : Archive.Header) : Cut :=
  ⟨header.badMask, header.badWeight, header.budget⟩
def families (G : Nat) (header : Archive.Header) (t : Fin 78) : List Cut :=
  if t.val = 0 then [⟨0, 0, 0⟩]
  else if t.val = 1 then [⟨2^75-1, allWeight, G⟩]
  else if t.val = 2 then [budgetCut header]
  else (cuts[t.val-3]!).toList

def HeaderValid (N : Nat) (r : Fin 357) (s G : Nat) (header : Archive.Header) : Prop :=
  ProjectionValidAt N r s G ∧
  (root header).lower = encode (Archive.rootLower r) ∧
  (root header).upper = encode (projectedUpper r s) ∧
  (budgetCut header).mask = (rootCapacity r).badMask ∧
  (budgetCut header).rhs = s

instance (N : Nat) (r : Fin 357) (s G : Nat) (header : Archive.Header) :
    Decidable (HeaderValid N r s G header) := by unfold HeaderValid; infer_instance

lemma upper_le (r : Fin 357) (s : Nat) (j : Fin 75) : projectedUpper r s j ≤ 7 := by
  unfold projectedUpper
  split
  · exact (min_le_left _ _).trans (Archive.rootUpper_le _ _)
  · exact Archive.rootUpper_le _ _

variable {N : Nat} {r : Fin 357} {s G : Nat} {header : Archive.Header}

theorem root_valid (hv : HeaderValid N r s G header) : (root header).Valid := by
  constructor
  · rw [hv.2.1]
    exact valid_encode _ (Archive.rootLower_le _)
  · rw [hv.2.2.1]
    exact valid_encode _ (upper_le r s)

theorem root_model (hv : HeaderValid N r s G header) :
    (root header).model = projectedBox r s := by
  have hl : vectorModel (root header).lower = (projectedBox r s).lower := by
    funext j
    change (values (root header).lower j : Int) = _
    rw [hv.2.1, encode_eq_pack, values_pack _ (Archive.rootLower_le _)]
    simp only [Archive.rootLower, projectedBox, Physical.rootBox]
    split_ifs <;> rfl
  have hu : vectorModel (root header).upper = (projectedBox r s).upper := by
    funext j
    change (values (root header).upper j : Int) = (projectedUpper r s j : Int)
    rw [hv.2.2.1, encode_eq_pack, values_pack _ (upper_le r s)]
  unfold Box.model
  rw [hl, hu]

lemma budgetCut_model (hv : HeaderValid N r s G header) : (budgetCut header).model =
    (⟨rootBad (rootCapacity r), s⟩ : Certificate.Cut 75) := by
  unfold Cut.model Cut.member
  rw [hv.2.2.2.1, hv.2.2.2.2]
  rfl

theorem families_models (hv : HeaderValid N r s G header) (t : Fin 78) :
    (families G header t).map Cut.model = (projectedProblem r s G).alternatives t := by
  dsimp only [families, projectedProblem, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model G)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (budgetCut_model hv)
  · exact hallCuts_models ⟨t.val-3, by omega⟩

theorem problem_model (hv : HeaderValid N r s G header) :
    Verified.problem G (families G header) = projectedProblem r s G := by
  have he := funext (families_models hv)
  unfold Verified.problem
  rw [he]
  rfl

/-- A checked projected exclusion excludes the original root at total N. -/
theorem original_exclusion (hv : HeaderValid N r s G header)
    (h : Chunks.Excludes G (families G header) (root header)) :
    ∀ x, (rootBox (rootCapacity r)).Contains x →
      ¬ (caseProblem r (rootCapacity r).budget N).Admissible x := by
  intro x hx hp
  obtain ⟨y, hy, hyp⟩ := root_projection_at N r s G hv.1 hx hp
  have he : ∀ y, (projectedBox r s).Contains y →
      ¬ (projectedProblem r s G).Admissible y := by
    simpa only [Chunks.Excludes, root_model hv, problem_model hv] using h
  exact he y hy hyp
end FiveColour.Packed.Projection
