module
public import FiveColour.BoxMatching
public import FiveColour.ConcentrationHall
@[expose] public section
namespace FiveColour.Physical

def rectCornerEquiv (l : Fin 3 → ℕ) : {p : RectSlot l // RectCorner p} ≃ Fin 8 where
  toFun p := match p with | ⟨.inl k,_⟩ => k
  invFun k := ⟨.inl k,trivial⟩
  left_inv p := by rcases p with ⟨p,hp⟩; cases p with
    | inl k => rfl
    | inr p => exact hp.elim
  right_inv _ := rfl

lemma rect_small_hall {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube) (t : Fin 75) (d : ℕ)
    (corners : Fin 8 ↪ Fin n) (hf : ∀ k, Fits (cubes (corners k)) (catalogue t) k)
    (hedges : ∀ e, 0 < l (edgeAxis e) →
      d ≤ (Finset.univ.filter fun i => HasEdge (cubes i) (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card) :
    ∀ D : Finset (RectSlot l), D.card ≤ d → D.card ≤ (FrameHall.neighbours (fun i p => RectFits (cubes i) (catalogue t) p) D).card := by
  classical
  apply FrameHall.small_hall_of_partial _ RectCorner ((rectCornerEquiv l).toEmbedding.trans corners)
    (by rintro ⟨p,hp⟩; cases p with
        | inl k => exact hf k
        | inr p => exact hp.elim) d
  intro p hp
  cases p with
  | inl k => exact False.elim (hp trivial)
  | inr p => exact hedges p.1 (Nat.zero_lt_of_lt p.2.isLt)
end FiveColour.Physical
