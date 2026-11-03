module
public import FiveColour.FrameGeometry
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

abbrev EdgePool := Fin 5 ⊕ Fin 10
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

def pairQuota (full : Fin 5 → Bool) (q : ℕ) (p : Fin 10) : ℕ :=
  if full (pairFirst p) && full (pairSecond p) then q else 2*q

def poolUnits (full : Fin 5 → Bool) : EdgePool → ℕ
  | .inl _ => 1
  | .inr p => pairQuota full 1 p

def monoFull (t : Fin 75) (full : Fin 5 → Bool) : Prop :=
  ∀ e : Fin 12, catalogue t (edgeFaces e 0) = catalogue t (edgeFaces e 1) →
    full (catalogue t (edgeFaces e 0)) = true

instance (t : Fin 75) (full : Fin 5 → Bool) : Decidable (monoFull t full) := by
  unfold monoFull
  infer_instance

/-- A doubled bichromatic edge uses the other colour's monochromatic pool
when both endpoint pools are full. All other edges use their own pair pool. -/
def edgePool (t : Fin 75) (full : Fin 5 → Bool) (e : Fin 12) : EdgePool :=
  let a := catalogue t (edgeFaces e 0)
  let b := catalogue t (edgeFaces e 1)
  if a = b then .inl a
  else if full a && full b && decide (∃ f : Fin 12, f < e ∧
      SamePair a b (catalogue t (edgeFaces f 0)) (catalogue t (edgeFaces f 1))) then
    if (Finset.univ.filter fun f : Fin 6 => catalogue t f = a).card = 2
    then .inl b else .inl a
  else .inr (pairIndex a b)

def PoolSupplies (t : Fin 75) (full : Fin 5 → Bool) (e : Fin 12) : Prop :=
  match edgePool t full e with
  | .inl a => full a = true ∧
      (a = catalogue t (edgeFaces e 0) ∨ a = catalogue t (edgeFaces e 1))
  | .inr p => SamePair (pairFirst p) (pairSecond p)
      (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))

instance (t : Fin 75) (full : Fin 5 → Bool) (e : Fin 12) : Decidable (PoolSupplies t full e) := by
  unfold PoolSupplies
  split <;> infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Finite target geometry: every pool is suitable and has enough capacity
for its assigned geometric edges. Multiplication by q is handled separately. -/
theorem edge_pool_checks (t : Fin 75) : ∀ full : Fin 5 → Bool, monoFull t full →
    (∀ e, PoolSupplies t full e) ∧
    ∀ p : EdgePool, (Finset.univ.filter fun e => edgePool t full e = p).card ≤ poolUnits full p := by
  fin_cases t <;> decide +kernel

def fullPattern (m : Fin 32) (a : Fin 5) : Bool := m.val.testBit a.val

set_option maxRecDepth 100000 in
lemma fullPattern_complete : ∀ full : Fin 5 → Bool, ∃ m, fullPattern m = full := by
  decide +kernel

/-- The worst reservation size is 25q-4, uniformly over the full colours. -/
lemma reserve_budget (full : Fin 5 → Bool) (q : ℕ) (hq : 1 ≤ q) :
    (∑ a : Fin 5, if full a then q else q-1) +
      (∑ p : Fin 10, pairQuota full q p) ≤ 25*q-4 := by
  obtain ⟨m,rfl⟩ := fullPattern_complete full
  fin_cases m <;> simp [pairQuota,pairFirst,pairSecond,fullPattern,Fin.sum_univ_succ,Nat.testBit_eq_decide_div_mod_eq] <;> omega

end FiveColour.Physical
