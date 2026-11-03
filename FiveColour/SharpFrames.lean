module
public import FiveColour.BoxThresholds
public import FiveColour.CubeBoxBridge
@[expose] public section
namespace FiveColour.Physical

def RarePair {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) (p : Fin 10) : Prop :=
  (pairCopies cubes p).card ≤ 4*q+5
instance {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) (p : Fin 10) : Decidable (RarePair q cubes p) :=
  inferInstanceAs (Decidable (_ ≤ _))

lemma rare_disjoint {m q : ℕ} (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hq : 1 ≤ q) (hm : 12*q+8 ≤ m) (p r : Fin 10) (hpr : p ≠ r)
    (hp : RarePair q cubes p) (hr : RarePair q cubes r) : PairDisjoint p r := by
  exact rareAt_disjoint (4*q+6) cubes hc (by omega) p r hpr
    (by unfold RareAt RarePair at *; omega) (by unfold RareAt RarePair at *; omega)

lemma at_most_two_rare {m q : ℕ} (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hq : 1 ≤ q) (hm : 12*q+8 ≤ m) (p r : Fin 10) (hpr : p ≠ r)
    (hp : RarePair q cubes p) (hr : RarePair q cubes r) :
    ∀ s, RarePair q cubes s → s = p ∨ s = r := by
  intro s hs
  by_contra hn
  have hsp : s ≠ p := fun he => hn (Or.inl he)
  have hsr : s ≠ r := fun he => hn (Or.inr he)
  exact no_three_disjoint p r s
    (rare_disjoint cubes hc hq hm p r hpr hp hr)
    (rare_disjoint cubes hc hq hm p s hsp.symm hp hs)
    (rare_disjoint cubes hc hq hm r s hsr.symm hr hs)

/-- The sharp cube-frame bound is the equal-side cuboid theorem. -/
theorem sharp_frame_of_threshold (h : Threshold15) {m : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hm : 12*q+8 ≤ m) : FrameSolvable q cubes := by
  have hf := box_frame_upper h (q+2) (q+2) (q+2) (by omega) (by omega) (by omega)
    cubes hc (by unfold boxFrameNumber; omega)
  simpa using (frame_iff_box (q+2) cubes).mpr hf
end FiveColour.Physical
