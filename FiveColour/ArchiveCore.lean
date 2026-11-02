module
public import FiveColour.CaseProblem
public import FiveColour.PackedHall
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.Archive
open Physical

/-- Natural-valued lower coordinates, before base-1024 encoding. -/
def rootLower (r : Fin 357) (i : Fin 75) : Nat :=
  if i = canonicalAnchor (rootCapacity r).kind then (rootCapacity r).copies.val else 0

lemma rootLower_le (r : Fin 357) (i : Fin 75) : rootLower r i ≤ 7 := by
  unfold rootLower
  split
  · have := (rootCapacity r).copies.isLt
    omega
  · omega

lemma rootUpper_le (r : Fin 357) (i : Fin 75) : rootUpper (rootCapacity r) i ≤ 7 := by
  rw [root_caps_match]
  unfold combinedCap
  split
  · have := (rootCapacity r).copies.isLt
    omega
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (Nat.sub_le 7 _))

/-- Literal packed bounds and anchor-cut fields derived from an archived header. -/
structure Header where
  lower : Nat
  upper : Nat
  badMask : Nat
  badWeight : Nat
  budget : Nat
  deriving Inhabited

end FiveColour.Packed.Archive
