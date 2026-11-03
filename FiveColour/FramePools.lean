module
public import FiveColour.FrameGeometry
@[expose] public section
namespace FiveColour.Physical

def pairFirst : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
def pairSecond : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]

def pairIndex (a b : Fin 5) : Fin 10 :=
  let lo := min a.val b.val
  let hi := max a.val b.val
  Fin.ofNat 10 (if lo = 0 then hi-1 else if lo = 1 then hi+2 else if lo = 2 then hi+4 else 9)

def SamePair (a b c d : Fin 5) : Prop := (a=c ∧ b=d) ∨ (a=d ∧ b=c)
instance (a b c d : Fin 5) : Decidable (SamePair a b c d) := by unfold SamePair; infer_instance

lemma pairIndex_correct : ∀ a b : Fin 5, a ≠ b →
    SamePair (pairFirst (pairIndex a b)) (pairSecond (pairIndex a b)) a b := by
  decide +kernel

lemma hasEdge_samePair {c : Cube} {a b d e : Fin 5}
    (h : SamePair a b d e) (he : HasEdge c a b) : HasEdge c d e := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact he
  · exact hasEdge_symm he

lemma samePair_symm {a b c d : Fin 5} (h : SamePair a b c d) : SamePair c d a b := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [SamePair]

end FiveColour.Physical
