module
public import Mathlib
@[expose] public section
namespace FiveColour.Reserve
open scoped BigOperators

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def used (R : A → Finset I) : Finset I := Finset.univ.biUnion R

omit [Fintype I] [DecidableEq A] in
@[simp] lemma mem_used (R : A → Finset I) (i : I) : i ∈ used R ↔ ∃ a, i ∈ R a := by
  simp [used]

/-- Disjoint, eligible pools, each bounded by its requested capacity. -/
def Valid (available : Finset I) (eligible : A → I → Prop)
    (cap : A → ℕ) (R : A → Finset I) : Prop :=
  (∀ a i, i ∈ R a → i ∈ available ∧ eligible a i) ∧
  (∀ a, (R a).card ≤ cap a) ∧ Pairwise (fun a b => Disjoint (R a) (R b))

/-- Reserve up to the requested capacity for each requirement. Any eligible
copy left outside every pool certifies that its pool reached capacity. -/
theorem exists_saturated (available : Finset I) (eligible : A → I → Prop) (cap : A → ℕ) :
    ∃ R : A → Finset I, Valid available eligible cap R ∧
      ∀ a i, i ∈ available → i ∉ used R → eligible a i → (R a).card = cap a := by
  classical
  let candidates := Finset.univ.filter (Valid available eligible cap)
  have hz : (fun _ : A => (∅ : Finset I)) ∈ candidates := by
    simp [candidates, Valid, Pairwise]
  obtain ⟨R, hR, hmax⟩ := candidates.exists_max_image (fun R => (used R).card) ⟨_, hz⟩
  have hv : Valid available eligible cap R := (Finset.mem_filter.mp hR).2
  refine ⟨R, hv, ?_⟩
  intro a i hi hnot he
  apply le_antisymm (hv.2.1 a)
  by_contra hsmall
  have hlt : (R a).card < cap a := by omega
  have hni (b : A) : i ∉ R b := fun h => hnot ((mem_used R i).mpr ⟨b, h⟩)
  let R' := Function.update R a (insert i (R a))
  have hv' : Valid available eligible cap R' := by
    refine ⟨?_, ?_, ?_⟩
    · intro b j hj
      by_cases hb : b = a
      · subst b
        simp only [R', Function.update_self, Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact ⟨hi, he⟩
        · exact hv.1 a j hj
      · exact hv.1 b j (by simpa [R', hb] using hj)
    · intro b
      by_cases hb : b = a
      · subst b
        simpa [R', Finset.card_insert_of_notMem (hni a)] using hlt
      · simpa [R', hb] using hv.2.1 b
    · intro b c hbc
      apply Finset.disjoint_left.mpr
      intro j hj hk
      by_cases hb : b = a <;> by_cases hc : c = a
      · exact hbc (hb.trans hc.symm)
      · subst b
        simp only [R', Function.update_self, Finset.mem_insert] at hj
        have hk' : j ∈ R c := by simpa [R', hc] using hk
        rcases hj with rfl | hj
        · exact hni c hk'
        · exact Finset.disjoint_left.mp (hv.2.2 hbc) hj hk'
      · subst c
        simp only [R', Function.update_self, Finset.mem_insert] at hk
        have hj' : j ∈ R b := by simpa [R', hb] using hj
        rcases hk with rfl | hk
        · exact hni b hj'
        · exact Finset.disjoint_left.mp (hv.2.2 hbc) hj' hk
      · exact Finset.disjoint_left.mp (hv.2.2 hbc)
          (by simpa [R', hb] using hj) (by simpa [R', hc] using hk)
  have hused : used R' = insert i (used R) := by
    ext j
    simp only [mem_used, Finset.mem_insert]
    constructor
    · rintro ⟨b, hb⟩
      by_cases hba : b = a
      · subst b
        simp only [R', Function.update_self, Finset.mem_insert] at hb
        exact hb.imp_right (fun h => ⟨a, h⟩)
      · exact Or.inr ⟨b, by simpa [R', hba] using hb⟩
    · rintro (rfl | ⟨b, hb⟩)
      · exact ⟨a, by simp [R']⟩
      · refine ⟨b, ?_⟩
        by_cases hba : b = a <;> simp_all [R']
  have hm := hmax R' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩)
  rw [hused, Finset.card_insert_of_notMem hnot] at hm
  omega

omit [Fintype I] [DecidableEq A] in
lemma used_card_le (R : A → Finset I) : (used R).card ≤ ∑ a, (R a).card :=
  Finset.card_biUnion_le

omit [Fintype A] [Fintype I] [DecidableEq I] in
/-- Allocate positions by disjoint pools; each pool need only cover its fibre. -/
theorem allocate {P : Type*} [Fintype P] (tag : P → A) (R : A → Finset I)
    (hd : Pairwise (fun a b => Disjoint (R a) (R b)))
    (hc : ∀ a, Fintype.card {p : P // tag p = a} ≤ (R a).card) :
    ∃ f : P ↪ I, ∀ p, f p ∈ R (tag p) := by
  classical
  have he (a : A) : Nonempty ({p : P // tag p = a} ↪ {i // i ∈ R a}) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hc a)
  let e := fun a => Classical.choice (he a)
  let out : (Σ a, {i // i ∈ R a}) ↪ I := ⟨fun x => x.2.val, by
    rintro ⟨a, i, hi⟩ ⟨b, j, hj⟩ h
    change i = j at h
    subst j
    have hab : a = b := by
      by_contra hne
      exact Finset.disjoint_left.mp (hd hne) hi hj
    subst b
    rfl⟩
  let f := (Equiv.sigmaFiberEquiv tag).symm.toEmbedding |>.trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl A) e) |>.trans out
  exact ⟨f, fun p => (e (tag p) ⟨p, rfl⟩).property⟩

omit [Fintype I] [DecidableEq A] in
lemma fibre_prod_card (tag : A → I) (q : ℕ) (i : I) :
    Fintype.card {p : A × Fin q // tag p.1 = i} =
      Fintype.card {a : A // tag a = i} * q := by
  classical
  let e : {p : A × Fin q // tag p.1 = i} ≃ ({a : A // tag a = i} × Fin q) :=
    { toFun := fun p => (⟨p.val.1,p.property⟩,p.val.2)
      invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_fin]

end FiveColour.Reserve
