module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import FiveColour.BoxCertificates
@[expose] public section
namespace FiveColour.Certificate

/-- A nonnegative integer mass can be trimmed to any smaller nonnegative mass. -/
lemma exists_submass {n : Nat} (x : Vector n) (hx : ∀ i, 0 ≤ x i)
    (S : Finset (Fin n)) (k : Int) (hk : 0 ≤ k) (hupper : k ≤ mass x S) :
    ∃ y : Vector n, (∀ i, 0 ≤ y i ∧ y i ≤ x i) ∧
      (∀ i ∉ S, y i = 0) ∧ mass y S = k := by
  induction S using Finset.induction_on generalizing k with
  | empty =>
    have he : k = 0 := by
      have h0 : k ≤ 0 := by simpa [mass] using hupper
      omega
    subst k
    exact ⟨fun _ => 0, fun i => ⟨le_rfl, hx i⟩, by simp, by simp [mass]⟩
  | @insert a S ha ih =>
    have hsum : mass x (insert a S) = x a + mass x S := by simp [mass, ha]
    let v := min k (x a)
    have hv : 0 ≤ v ∧ v ≤ x a ∧ v ≤ k := ⟨le_min hk (hx a), min_le_right _ _, min_le_left _ _⟩
    have hrest : k - v ≤ mass x S := by
      have hnonneg : 0 ≤ mass x S := Finset.sum_nonneg (fun i _ => hx i)
      dsimp [v]
      rw [hsum] at hupper
      omega
    obtain ⟨z, hz, hsupport, hmass⟩ := ih (k-v) (by omega) hrest
    refine ⟨Function.update z a v, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = a
      · subst i; simpa using (show 0 ≤ v ∧ v ≤ x a from ⟨hv.1, hv.2.1⟩)
      · simpa [Function.update_of_ne hi] using hz i
    · intro i hi
      have hia : i ≠ a := by intro he; subst i; exact hi (Finset.mem_insert_self _ _)
      have his : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
      simpa [Function.update_of_ne hia] using hsupport i his
    · simp only [mass, Finset.sum_insert ha, Function.update_self,
        Finset.sum_update_of_notMem ha]
      change v + mass z S = k
      omega

/-- Reduce the total while preserving one fixed coordinate. -/
lemma exists_trim_preserving {n : Nat} (x : Vector n) (hx : ∀ i, 0 ≤ x i)
    (a : Fin n) (G : Int) (ha : x a ≤ G) (hG : G ≤ mass x Finset.univ) :
    ∃ y : Vector n, (∀ i, 0 ≤ y i ∧ y i ≤ x i) ∧ y a = x a ∧
      mass y Finset.univ = G := by
  have hsplit : mass x (Finset.univ.erase a) + x a = mass x Finset.univ :=
    Finset.sum_erase_add _ _ (Finset.mem_univ a)
  obtain ⟨z, hz, _, hmass⟩ := exists_submass x hx (Finset.univ.erase a) (G-x a)
    (by omega) (by omega)
  refine ⟨Function.update z a (x a), ?_, by simp, ?_⟩
  · intro i
    by_cases hi : i = a
    · subst i; simpa using (show 0 ≤ x a ∧ x a ≤ x a from ⟨hx a, le_rfl⟩)
    · simpa [Function.update_of_ne hi] using hz i
  · unfold mass
    rw [Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase]
    change x a + mass z (Finset.univ.erase a) = G
    rw [hmass]
    omega

/-- Delete Hall-budget copies first, then trim the remainder. The fixed anchor
is outside the budget set, and all coordinates only decrease. -/
theorem exists_budget_projection {n : Nat} (x : Vector n) (hx : ∀ i, 0 ≤ x i)
    (a : Fin n) (S : Finset (Fin n)) (ha : a ∉ S)
    (N b s : Int) (ht : mass x Finset.univ = N)
    (hb : mass x S ≤ b) (hs : 0 ≤ s) (hsb : s ≤ b)
    (hanchor : x a ≤ N-b+s) :
    ∃ y : Vector n, (∀ i, 0 ≤ y i ∧ y i ≤ x i) ∧ y a = x a ∧
      mass y Finset.univ = N-b+s ∧ mass y S ≤ s := by
  have hnonneg : 0 ≤ mass x S := Finset.sum_nonneg (fun i _ => hx i)
  obtain ⟨z, hz, _, hmass⟩ := exists_submass x hx S (min (mass x S) s)
    (le_min hnonneg hs) (min_le_left _ _)
  let w : Vector n := fun i => if i ∈ S then z i else x i
  have hw (i) : 0 ≤ w i ∧ w i ≤ x i := by
    dsimp [w]
    split
    · exact hz i
    · exact ⟨hx i, le_rfl⟩
  have hwa : w a = x a := by simp only [w, ite_eq_right ha]
  have hws : mass w S = min (mass x S) s := by
    rw [← hmass]
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_left hi
  have hwc : mass w Sᶜ = mass x Sᶜ := by
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_right (Finset.mem_compl.mp hi)
  have hwtotal : N-b+s ≤ mass w Finset.univ := by
    have h1 := mass_complement x S
    have h2 := mass_complement w S
    rw [hws, hwc] at h2
    omega
  obtain ⟨y, hy, hya, hyt⟩ := exists_trim_preserving w (fun i => (hw i).1) a
    (N-b+s) (by simpa only [hwa] using hanchor) hwtotal
  refine ⟨y, fun i => ⟨(hy i).1, (hy i).2.trans (hw i).2⟩, hya.trans hwa, hyt, ?_⟩
  have hle := mass_mono S (fun i _ => (hy i).2)
  rw [hws] at hle
  exact hle.trans (min_le_right _ _)

/-- Hall failure is preserved when copies are deleted; only the total changes. -/
lemma hall_families_mono {n k : Nat} (families : Fin k → List (Cut n))
    {x y : Vector n} (hxy : ∀ i, y i ≤ x i)
    (h : ∀ t, ∃ c ∈ families t, c.Holds x) :
    ∀ t, ∃ c ∈ families t, c.Holds y := by
  intro t
  obtain ⟨c, hc, hcx⟩ := h t
  exact ⟨c, hc, (mass_mono c.neighbours (fun i _ => hxy i)).trans hcx⟩

end FiveColour.Certificate
