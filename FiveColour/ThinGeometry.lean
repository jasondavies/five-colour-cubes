module
public import FiveColour.BoxGeometry
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

lemma thin_missing_bound (c : Cube) (hc : UsesAllColours c) (target : Fin 75)
    (axes : Equiv.Perm (Fin 3)) (w : Fin 2) (M : ℕ) (hM : 1 ≤ M)
    (hmono : ∀ a, axes a ≠ 0 → BichromaticAxis (catalogue target) a) :
    (Finset.univ.filter fun p : RectSlot (fun a => ![0,w.val,M] (axes a)) =>
      ¬ RectFits c (catalogue target) p).card ≤ 2*M+6+w.val := by
  classical
  have he : ∀ p : RectSlot (fun a => ![0,w.val,M] (axes a)),
      RectFits c (catalogue target) p ↔ RectFits (catalogue (catalogueIndex c)) (catalogue target) p :=
    fun p => rectFits_catalogueIndex c _ hc p
  simp_rw [he]
  rw [rect_missing_card,missingCorners_bits]
  simp_rw [missingAlong_bits]
  have hr := Equiv.sum_comp axes.symm (fun a => alongBits (catalogueIndex c) target a * ![0,w.val,M] (axes a))
  simp only [Equiv.apply_symm_apply] at hr
  rw [← hr]
  have h1 := hmono (axes.symm 1) (by simp)
  have h2 := hmono (axes.symm 2) (by simp)
  obtain ⟨hthin,hboth⟩ := thin_directional_bits (catalogueIndex c) target (axes.symm 2) h2
  have hpair := hboth (axes.symm 1) (axes.symm.injective.ne (by decide)) h1
  have hk := (directional_bits (catalogueIndex c) target).2.2.1 (axes.symm 2)
  have hmul := Nat.mul_le_mul_left (M-1) hk
  have hM' : M-1+1=M := by omega
  fin_cases w <;> simp [Fin.sum_univ_succ] <;> nlinarith
end FiveColour.Physical
