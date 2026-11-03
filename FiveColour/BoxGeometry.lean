module
public import FiveColour.BoxDirectional
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators
lemma weighted_bound (h k₀ k₁ k₂ m t M : ℕ)
    (hmt : m ≤ t) (htM : t ≤ M) (hs : 2 ≤ m+t)
    (hk : k₀+k₁+k₂ ≤ 4) (hh : h+k₀+k₁+k₂ ≤ 10)
    (h₂ : k₂ ≤ 2) (h₁₂ : k₁+k₂ ≤ 3) (hh₁₂ : h+2*(k₁+k₂) ≤ 12) :
    h+k₀*m+k₁*t+k₂*M ≤ m+t+2*M+6 := by
  by_cases hm : 1 ≤ m
  · have h1 := Nat.mul_le_mul_left (m-1) hk
    have h2 := Nat.mul_le_mul_left (t-m) h₁₂
    have h3 := Nat.mul_le_mul_left (M-t) h₂
    have hm' : m-1+1=m := by omega
    have ht' : t-m+m=t := by omega
    have hM' : M-t+t=M := by omega
    nlinarith
  · have hm0 : m=0 := by omega
    subst m
    have h1 := Nat.mul_le_mul_left (t-2) h₁₂
    have h2 := Nat.mul_le_mul_left (M-t) h₂
    have ht' : t-2+2=t := by omega
    have hM' : M-t+t=M := by omega
    nlinarith

lemma rect_missing_bound (c : Cube) (hc : UsesAllColours c) (target : Fin 75)
    (axes : Equiv.Perm (Fin 3)) (m t M : ℕ) (hmt : m ≤ t) (htM : t ≤ M) (hs : 2 ≤ m+t) :
    (Finset.univ.filter fun p : RectSlot (fun a => ![m,t,M] (axes a)) =>
      ¬ RectFits c (catalogue target) p).card ≤ m+t+2*M+6 := by
  classical
  have he : ∀ p : RectSlot (fun a => ![m,t,M] (axes a)),
      RectFits c (catalogue target) p ↔ RectFits (catalogue (catalogueIndex c)) (catalogue target) p :=
    fun p => rectFits_catalogueIndex c _ hc p
  simp_rw [he]
  rw [rect_missing_card,missingCorners_bits]
  simp_rw [missingAlong_bits]
  have hr := Equiv.sum_comp axes.symm (fun a => alongBits (catalogueIndex c) target a * ![m,t,M] (axes a))
  simp only [Equiv.apply_symm_apply] at hr
  rw [← hr]
  obtain ⟨hk,hh,ha,hab⟩ := directional_bits (catalogueIndex c) target
  have hi : axes.symm (1 : Fin 3) ≠ axes.symm 2 := axes.symm.injective.ne (by decide)
  have hsum := Equiv.sum_comp axes.symm (alongBits (catalogueIndex c) target)
  rw [← hsum] at hk hh
  simp [Fin.sum_univ_succ] at hk hh ⊢
  simpa only [Nat.add_assoc] using weighted_bound (cornerMissBits (catalogueIndex c) target)
    (alongBits (catalogueIndex c) target (axes.symm 0))
    (alongBits (catalogueIndex c) target (axes.symm 1))
    (alongBits (catalogueIndex c) target (axes.symm 2))
    m t M hmt htM hs (by omega) (by omega) (ha _) (hab _ _ hi).1 (hab _ _ hi).2
end FiveColour.Physical
