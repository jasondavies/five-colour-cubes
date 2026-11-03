module
public import FiveColour.ProjectionData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical.Projection

lemma other_other (s : Fin 2) : other (other s) = s := by fin_cases s <;> decide +kernel
lemma half_card (r : Fin 3) : Fintype.card (Half r) = 4 := by fin_cases r <;> decide +kernel
lemma slot_injective : ∀ p sign t, side sign t → Function.Injective (cornerSlot p sign t) := by decide +kernel
noncomputable def adjacentEmbedding (p : Fin 10) (sign : Fin 2) (t : Fin 9) (h : side sign t) : Fin 6 ↪ Fin 8 :=
  ⟨cornerSlot p sign t,slot_injective p sign t h⟩

/-- Every projected position is checked against the already verified physical corner incidence. -/
lemma projection_bits (p : Fin 10) : ∀ sign t j, present sign t j → ∀ w,
    (Replay.fits (Ring.variety p t) w).testBit (cornerSlot p sign t j).val =
      (bits p sign w).testBit j.val := by
  fin_cases p <;> decide +kernel
lemma fits_correct (p : Fin 10) (sign : Fin 2) (t : Fin 9) (j : Fin 6)
    (h : present sign t j) (w : Fin 75) :
    Fits p sign w j ↔ Physical.Fits (catalogue w) (catalogue (Ring.variety p t)) (cornerSlot p sign t j) := by
  rw [← incidence_fits,projection_bits p sign t j h]
  rfl
lemma family_side : ∀ p sign s, side sign s → ∀ j, Fits p sign (Ring.variety p s) j := by decide +kernel
lemma family_opposite_count : ∀ p sign s, s.val < 3 → count p sign (Ring.variety p s) = 4 := by decide +kernel
lemma family_not_side : ∀ sign s, ¬ side sign s → s.val < 3 ∨ side (other sign) s := by decide +kernel

/-- The signed projection alternatives, including the three family profiles. -/
lemma profile_bounds (p : Fin 10) : ∀ sign w (u : Fin 3), count p sign w ≤ u.val →
    ![4,2,1] u ≤ count p (other sign) w := by
  fin_cases p <;> decide +kernel

lemma present_half : ∀ sign r (j : Half r), present sign (target r) j.val := by decide +kernel

def halfSlot (p : Fin 10) (sign : Fin 2) (r : Fin 3) : Half r ⊕ Half r → Fin 8 :=
  Sum.elim (fun j => cornerSlot p sign (target r) j.val)
    (fun j => cornerSlot p (other sign) (target r) j.val)
lemma halfSlot_bijective : ∀ p sign r, Function.Bijective (halfSlot p sign r) := by decide +kernel
noncomputable def halvesEquiv (p : Fin 10) (sign : Fin 2) (r : Fin 3) :=
  Equiv.ofBijective (halfSlot p sign r) (halfSlot_bijective p sign r)

end FiveColour.Physical.Projection
