module
public import FiveColour.TwoVarieties
public import FiveColour.HallCuts
@[expose] public section
namespace FiveColour.Physical

/-- The adjacent-repeat and opposite-repeat canonical anchors, respectively. -/
def canonicalAnchor (kind : Fin 2) : Fin 75 := if kind = 0 then 3 else 0

/-- A compact, decidable version of the physical two-variety criterion. -/
def PairMaskCriterion (i j t : Fin 75) (a : Nat) : Prop :=
  (Replay.fits t i).lor (Replay.fits t j) = 255 ∧
    a ≤ (cornerSet (Replay.fits t i)).card ∧
    8-a ≤ (cornerSet (Replay.fits t j)).card

instance (i j t : Fin 75) (a : Nat) : Decidable (PairMaskCriterion i j t a) := by
  unfold PairMaskCriterion
  infer_instance

lemma cornerSet_fits (t i : Fin 75) :
    cornerSet (Replay.fits t i) = usableSlots (catalogue i) (catalogue t) := by
  ext k
  simp only [cornerSet, usableSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  exact incidence_fits t i k

lemma pairMaskCriterion_sound (i j t : Fin 75) (a : Nat)
    (h : PairMaskCriterion i j t a) : PairCriterion i j t a := by
  obtain ⟨hu, hi, hj⟩ := h
  refine ⟨?_, by simpa only [cornerSet_fits] using hi,
    by simpa only [cornerSet_fits] using hj⟩
  intro k
  have hfull : ∀ k : Fin 8, (255 : Nat).testBit k.val = true := by decide +kernel
  have hk := congrArg (fun mask => mask.testBit k.val) hu
  simp only [Nat.lor_eq, Nat.testBit_lor, hfull k, Bool.or_eq_true] at hk
  exact hk.imp (incidence_fits t i k).mp (incidence_fits t j k).mp

end FiveColour.Physical
