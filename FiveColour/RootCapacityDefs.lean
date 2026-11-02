module
public import FiveColour.PairCapacities
public import FiveColour.AnchorKinds
@[expose] public section
namespace FiveColour.Physical

/-- Class bounds after selecting the anchor: adjacent priority for repeated
collections; opposite priority for distinct collections. -/
def classCap (kind : Fin 2) (m : Fin 8) (i : Fin 75) : Nat :=
  if m = 1 then
    if kind = 0 ∧ OppositeRepeat (catalogue i) then 0 else 1
  else if kind = 1 ∧ ¬ OppositeRepeat (catalogue i) then m.val - 1 else m.val

structure RootCapacity where
  kind : Fin 2
  copies : Fin 8
  cover : Nat
  budget : Nat
  rawUpper : Array Nat
  badMask : Nat
  deriving Inhabited

def rootBad (r : RootCapacity) : Finset (Fin 75) :=
  Finset.univ.filter fun i => r.badMask.testBit i.val

/-- Match the checker's interpretation of the anchor sentinel. -/
def rootUpper (r : RootCapacity) (i : Fin 75) : Nat :=
  if i = canonicalAnchor r.kind then r.copies.val else r.rawUpper[i.val]!

def combinedCap (r : RootCapacity) (i : Fin 75) : Nat :=
  if i = canonicalAnchor r.kind then r.copies.val else
    min (classCap r.kind r.copies i)
      (min (if i ∈ rootBad r then r.budget else 7) (pairCap r.kind r.copies i))

end FiveColour.Physical
