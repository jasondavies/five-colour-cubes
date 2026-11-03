module
public import FiveColour.BoxModel
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

def missingAlong (c t : Cube) (axis : Fin 3) : ℕ :=
  (Finset.univ.filter fun e : Fin 12 => edgeAxis e = axis ∧
    ¬ HasEdge c (t (edgeFaces e 0)) (t (edgeFaces e 1))).card

lemma rect_missing_card (c t : Cube) (l : Fin 3 → ℕ) :
    (Finset.univ.filter fun p : RectSlot l => ¬ RectFits c t p).card =
      missingCorners c t + ∑ a, missingAlong c t a * l a := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (Equiv.subtypeSum),Fintype.card_sum]
  have hc : Fintype.card {k : Fin 8 // ¬ RectFits c t (Sum.inl k : RectSlot l)} = missingCorners c t := by
    exact Fintype.card_subtype _
  rw [hc]
  congr 1
  let bad := fun e : Fin 12 => ¬ HasEdge c (t (edgeFaces e 0)) (t (edgeFaces e 1))
  let equiv : {p : (Σ e : Fin 12, Fin (l (edgeAxis e))) // bad p.1} ≃
      (Σ e : {e : Fin 12 // bad e}, Fin (l (edgeAxis e.val))) :=
    { toFun := fun p => ⟨⟨p.val.1,p.property⟩,p.val.2⟩
      invFun := fun p => ⟨⟨p.1.val,p.2⟩,p.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Fintype.card {p : (Σ e : Fin 12, Fin (l (edgeAxis e))) // bad p.1} = _
  rw [Fintype.card_congr equiv,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_subtype (Finset.univ.filter bad) (by simp) (fun e => l (edgeAxis e))]
  have hf := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter bad)
    (t := Finset.univ) (g := edgeAxis) (f := fun e => l (edgeAxis e)) (by simp)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∑ e ∈ {e ∈ Finset.univ.filter bad | edgeAxis e = a}, l (edgeAxis e) =
      (Finset.univ.filter fun e => edgeAxis e = a ∧ bad e).card * l a := by
    have hs : {e ∈ Finset.univ.filter bad | edgeAxis e = a} =
        Finset.univ.filter fun e => edgeAxis e = a ∧ bad e := by ext e; simp [and_comm]
    rw [hs]
    exact Finset.sum_const_nat (fun e he => congrArg l (Finset.mem_filter.mp he).2.1)
  exact he
end FiveColour.Physical
