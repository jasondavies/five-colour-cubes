module
public import FiveColour.ExtremalVarieties
public import FiveColour.StabiliserData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical


def tripleAnchor : Fin 2 → Fin 75 := ![0,3]

inductive TripleReduction where
  | solve (target : Fin 75)
  | orbit (representative : Fin 5) (symmetry : Fin 16) (swap : Bool)
  deriving Inhabited, DecidableEq

def TripleReduction.Valid (a b c : Fin 75) : TripleReduction → Prop
  | .solve t => TripleCriterion a b c t
  | .orbit j g swap => a = 0 ∧
      b = stabiliserAction g (if swap then extremalC j else extremalB j) ∧
      c = stabiliserAction g (if swap then extremalB j else extremalC j)
instance instDecidableTripleReductionValid (a b c : Fin 75) (w : TripleReduction) : Decidable (w.Valid a b c) := by
  cases w <;> unfold TripleReduction.Valid <;> infer_instance

/-- The own-target and disjoint-pair arguments leave this finite remainder. -/
def TripleResidual (kind : Fin 2) (b c : Fin 75) : Prop :=
  tripleAnchor kind ≠ b ∧ tripleAnchor kind ≠ c ∧ b < c ∧
  ¬ TripleCriterion (tripleAnchor kind) b c (tripleAnchor kind) ∧
  ¬ TripleCriterion (tripleAnchor kind) b c b ∧
  ¬ TripleCriterion (tripleAnchor kind) b c c ∧
  Replay.fits (tripleAnchor kind) b ≠ 0 ∧
  Replay.fits (tripleAnchor kind) c ≠ 0 ∧ Replay.fits b c ≠ 0
instance (kind : Fin 2) (b c : Fin 75) : Decidable (TripleResidual kind b c) := by
  unfold TripleResidual; infer_instance

structure TripleResidualRecord where
  kind : Fin 2
  b : Fin 75
  c : Fin 75
  reduction : TripleReduction
  deriving DecidableEq

def tripleResiduals : List TripleResidualRecord := [
⟨0,16,49,.orbit 0 0 false⟩,
⟨0,16,59,.orbit 1 9 true⟩,
⟨0,16,61,.orbit 0 3 false⟩,
⟨0,16,69,.orbit 1 12 true⟩,
⟨0,17,49,.orbit 2 9 true⟩,
⟨0,17,50,.orbit 3 0 false⟩,
⟨0,17,59,.orbit 0 9 true⟩,
⟨0,17,61,.orbit 3 12 true⟩,
⟨0,17,62,.orbit 4 12 true⟩,
⟨0,18,46,.orbit 0 1 false⟩,
⟨0,18,57,.orbit 1 8 true⟩,
⟨0,18,63,.orbit 0 2 false⟩,
⟨0,18,71,.orbit 1 13 true⟩,
⟨0,19,46,.orbit 2 8 true⟩,
⟨0,19,47,.orbit 3 1 false⟩,
⟨0,19,57,.orbit 0 8 true⟩,
⟨0,19,63,.orbit 3 13 true⟩,
⟨0,19,64,.orbit 4 13 true⟩,
⟨0,20,55,.solve 1⟩,
⟨0,21,68,.solve 1⟩,
⟨0,22,49,.orbit 3 9 true⟩,
⟨0,22,50,.orbit 4 9 true⟩,
⟨0,22,61,.orbit 2 12 true⟩,
⟨0,22,62,.orbit 3 3 false⟩,
⟨0,22,69,.orbit 0 12 true⟩,
⟨0,23,46,.orbit 3 8 true⟩,
⟨0,23,47,.orbit 4 8 true⟩,
⟨0,23,63,.orbit 2 13 true⟩,
⟨0,23,64,.orbit 3 2 false⟩,
⟨0,23,71,.orbit 0 13 true⟩,
⟨0,31,47,.orbit 0 4 false⟩,
⟨0,31,57,.orbit 1 11 true⟩,
⟨0,31,64,.orbit 0 7 false⟩,
⟨0,31,71,.orbit 1 14 true⟩,
⟨0,33,46,.orbit 3 4 false⟩,
⟨0,33,47,.orbit 2 11 true⟩,
⟨0,33,57,.orbit 0 11 true⟩,
⟨0,33,63,.orbit 4 14 true⟩,
⟨0,33,64,.orbit 3 14 true⟩,
⟨0,34,50,.orbit 0 5 false⟩,
⟨0,34,59,.orbit 1 10 true⟩,
⟨0,34,62,.orbit 0 6 false⟩,
⟨0,34,69,.orbit 1 15 true⟩,
⟨0,36,49,.orbit 3 5 false⟩,
⟨0,36,50,.orbit 2 10 true⟩,
⟨0,36,59,.orbit 0 10 true⟩,
⟨0,36,61,.orbit 4 15 true⟩,
⟨0,36,62,.orbit 3 15 true⟩,
⟨0,37,45,.solve 1⟩,
⟨0,40,60,.solve 1⟩,
⟨0,41,46,.orbit 4 11 true⟩,
⟨0,41,47,.orbit 3 11 true⟩,
⟨0,41,63,.orbit 3 7 false⟩,
⟨0,41,64,.orbit 2 14 true⟩,
⟨0,41,71,.orbit 0 14 true⟩,
⟨0,42,49,.orbit 4 10 true⟩,
⟨0,42,50,.orbit 3 10 true⟩,
⟨0,42,61,.orbit 3 6 false⟩,
⟨0,42,62,.orbit 2 15 true⟩,
⟨0,42,69,.orbit 0 15 true⟩]

lemma triple_residuals_valid : ∀ w ∈ tripleResiduals,
    w.reduction.Valid (tripleAnchor w.kind) w.b w.c := by decide +kernel

end FiveColour.Physical
