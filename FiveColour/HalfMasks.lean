module
public import FiveColour.ProjectionData
@[expose] public section
namespace FiveColour.Physical.Projection

def maskFits (m : Fin 64) (j : Fin 6) : Prop := m.val.testBit j.val = true
instance (m : Fin 64) : DecidablePred (maskFits m) := by intro j; unfold maskFits; infer_instance
def maskCount (m : Fin 64) := (Finset.univ.filter (maskFits m)).card

def halfMask (m : Fin 64) (r : Fin 3) : Finset (Fin 6) :=
  Finset.univ.filter fun j => j.val / 2 ≠ r.val ∧ maskFits m j

/-- Four of the six corners meet every half at least twice, and some half
at least three times. This check considers single masks, not triples. -/
lemma half_counts : ∀ m, 4 ≤ maskCount m →
    (∀ r, 2 ≤ (halfMask m r).card) ∧ ∃ r, 3 ≤ (halfMask m r).card := by
  decide +kernel

lemma pair_in_half : ∀ x y : Fin 6, ∃ r : Fin 3,
    x.val / 2 ≠ r.val ∧ y.val / 2 ≠ r.val := by decide +kernel

/-- At most three projections can be placed in a suitable four-position
half. Choose the positions greedily; no triples of masks are enumerated. -/
lemma place_masks (j : Fin 3) (masks : Fin (3-j.val) → Fin 64)
    (hm : ∀ i, ![4,2,1] j ≤ maskCount (masks i)) :
    ∃ r : Fin 3, ∃ f : Fin (3-j.val) ↪ Half r, ∀ i, maskFits (masks i) (f i).val := by
  fin_cases j
  · change Fin 3 → Fin 64 at masks
    change (∀ i : Fin 3, 4 ≤ maskCount (masks i)) at hm
    change ∃ r : Fin 3, ∃ f : Fin 3 ↪ Half r, ∀ i, maskFits (masks i) (f i).val
    obtain ⟨r,ha⟩ := (half_counts (masks 0) (hm 0)).2
    have hb := (half_counts (masks 1) (hm 1)).1 r
    have hc := (half_counts (masks 2) (hm 2)).1 r
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (halfMask (masks 1) r).card)
    obtain ⟨y,hy,hyx⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {x}) (t := halfMask (masks 2) r) (by simp only [Finset.card_singleton]; omega)
    have hxy : ({x,y} : Finset (Fin 6)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    obtain ⟨z,hz,hzxy⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {x,y}) (t := halfMask (masks 0) r) (by omega)
    simp only [halfMask,Finset.mem_filter,Finset.mem_univ,true_and] at hx hy hz
    simp only [Finset.mem_singleton,Finset.mem_insert,not_or] at hyx hzxy
    let f : Fin 3 → Half r := ![⟨z,hz.1⟩,⟨x,hx.1⟩,⟨y,hy.1⟩]
    refine ⟨r,⟨f,?_⟩,?_⟩
    · intro i k he
      have he' := congrArg Subtype.val he
      fin_cases i <;> fin_cases k <;> simp_all [f]
    · intro i; fin_cases i
      · exact hz.2
      · exact hx.2
      · exact hy.2
  · change Fin 2 → Fin 64 at masks
    change (∀ i : Fin 2, 2 ≤ maskCount (masks i)) at hm
    change ∃ r : Fin 3, ∃ f : Fin 2 ↪ Half r, ∀ i, maskFits (masks i) (f i).val
    have h0 := hm 0
    have h1 := hm 1
    change 2 ≤ (Finset.univ.filter (maskFits (masks 0))).card at h0
    change 2 ≤ (Finset.univ.filter (maskFits (masks 1))).card at h1
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (maskFits (masks 0))).card)
    obtain ⟨y,hy,hyx⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {x}) (t := Finset.univ.filter (maskFits (masks 1)))
      (by simp only [Finset.card_singleton]; omega)
    obtain ⟨r,hrx,hry⟩ := pair_in_half x y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx hy
    simp only [Finset.mem_singleton] at hyx
    let f : Fin 2 → Half r := ![⟨x,hrx⟩,⟨y,hry⟩]
    refine ⟨r,⟨f,?_⟩,?_⟩
    · intro i k he
      have he' := congrArg Subtype.val he
      fin_cases i <;> fin_cases k <;> simp_all [f]
    · intro i; fin_cases i
      · exact hx
      · exact hy
  · change Fin 1 → Fin 64 at masks
    change (∀ i : Fin 1, 1 ≤ maskCount (masks i)) at hm
    change ∃ r : Fin 3, ∃ f : Fin 1 ↪ Half r, ∀ i, maskFits (masks i) (f i).val
    have hc : 0 < (Finset.univ.filter (maskFits (masks 0))).card := hm 0
    obtain ⟨x,hx⟩ := Finset.card_pos.mp hc
    obtain ⟨r,hr,_⟩ := pair_in_half x x
    refine ⟨r,⟨fun _ => ⟨x,hr⟩,fun _ _ _ => Subsingleton.elim _ _⟩,?_⟩
    intro i; fin_cases i; exact (Finset.mem_filter.mp hx).2
end FiveColour.Physical.Projection
