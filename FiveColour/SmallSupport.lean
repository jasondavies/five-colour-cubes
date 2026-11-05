module
public import FiveColour.SupportData
public import FiveColour.ComparatorBridge
@[expose] public section
namespace FiveColour.Physical

/-- Distinct proper-rotation varieties present in a physical collection. -/
def varietySupport {n : ℕ} (cubes : Fin n → Cube) : Finset (Fin 75) :=
  Finset.univ.image (fun i => catalogueIndex (cubes i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem support_pair_verified (i : Fin 75) : ∀ j,
    PairMaskCriterion i j (supportPairTarget i j) (supportPairAmount i j) ∧
    supportPairAmount i j ≤ 7 ∧ 8-supportPairAmount i j ≤ 6 := by
  fin_cases i <;> decide +kernel

/-- The existing pair certificate needs only four copies of each disjoint variety. -/
theorem disjoint_pair_suffices {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (a b : Fin 75) (hab : a ≠ b)
    (hdis : Replay.fits a b = 0)
    (ha : 4 ≤ multiplicity cubes a) (hb : 4 ≤ multiplicity cubes b) : HasSolution cubes := by
  have hcrit := (support_pair_verified a b).1
  simp only [supportPairAmount, hdis, ↓reduceIte] at hcrit
  exact (hasSolution_iff_catalogue cubes).mpr
    ⟨supportPairTarget a b, two_varieties_suffice cubes hc a b _ hab 4
      (pairMaskCriterion_sound _ _ _ _ hcrit) ha (by simpa using hb)⟩

lemma support_mem {n : ℕ} (cubes : Fin n → Cube) (i : Fin n) :
    catalogueIndex (cubes i) ∈ varietySupport cubes :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

lemma support_pair_cover {n : ℕ} (hn : 0 < n) (cubes : Fin n → Cube)
    (hs : (varietySupport cubes).card ≤ 2) :
    ∃ a b : Fin 75, ∀ i, catalogueIndex (cubes i) = a ∨ catalogueIndex (cubes i) = b := by
  classical
  let a := catalogueIndex (cubes ⟨0,hn⟩)
  have ha : a ∈ varietySupport cubes := support_mem cubes ⟨0,hn⟩
  have he : ((varietySupport cubes).erase a).card ≤ 1 := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b,hb⟩ := Finset.card_le_one_iff_subset_singleton.mp he
  refine ⟨a,b,?_⟩
  intro i
  by_cases hi : catalogueIndex (cubes i) = a
  · exact Or.inl hi
  · exact Or.inr (Finset.mem_singleton.mp (hb (Finset.mem_erase.mpr ⟨hi,support_mem cubes i⟩)))

theorem one_support_suffices {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hs : (varietySupport cubes).card ≤ 1)
    (hn : 8 ≤ n) : HasSolution cubes := by
  obtain ⟨a,ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hs
  have he (i : Fin n) : catalogueIndex (cubes i) = a :=
    Finset.mem_singleton.mp (ha (support_mem cubes i))
  have hm : multiplicity cubes a = n := by simp [multiplicity,he]
  exact (hasSolution_iff_catalogue cubes).mpr
    ⟨a,solvesTarget_of_eight_copies cubes hc a (by omega)⟩

/-- Thirteen copies in at most two varieties always have a corner solution. -/
theorem two_support_suffices {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hs : (varietySupport cubes).card ≤ 2)
    (hn : 13 ≤ n) : HasSolution cubes := by
  classical
  by_contra hno
  obtain ⟨a,b,hcover⟩ := support_pair_cover (by omega) cubes hs
  have ha := multiplicity_le_seven cubes hc hno a
  have hb := multiplicity_le_seven cubes hc hno b
  by_cases hab : a = b
  · subst b
    have he (i : Fin n) : catalogueIndex (cubes i) = a := (hcover i).elim id id
    have hm : multiplicity cubes a = n := by simp [multiplicity,he]
    omega
  · have hu : (Finset.univ : Finset (Fin n)) =
        (Finset.univ.filter fun i => catalogueIndex (cubes i) = a) ∪
        (Finset.univ.filter fun i => catalogueIndex (cubes i) = b) := by
      ext i
      simp [hcover i]
    have hsum : n ≤ multiplicity cubes a + multiplicity cubes b := by
      simpa only [← hu,Finset.card_univ,Fintype.card_fin,multiplicity] using
        (Finset.card_union_le (Finset.univ.filter fun i => catalogueIndex (cubes i) = a)
          (Finset.univ.filter fun i => catalogueIndex (cubes i) = b))
    have solve (i j : Fin 75) (hij : i ≠ j) (hi : 7 ≤ multiplicity cubes i)
        (hj : 6 ≤ multiplicity cubes j) : HasSolution cubes := by
      obtain ⟨hcrit,hi',hj'⟩ := support_pair_verified i j
      exact (hasSolution_iff_catalogue cubes).mpr
        ⟨supportPairTarget i j,two_varieties_suffice cubes hc i j _ hij _
          (pairMaskCriterion_sound _ _ _ _ hcrit) (hi'.trans hi) (hj'.trans hj)⟩
    by_cases ha7 : 7 ≤ multiplicity cubes a
    · exact hno (solve a b hab ha7 (by omega))
    · exact hno (solve b a (fun he => hab he.symm) (by omega) (by omega))

def pairLowerFamily (i : Fin 12) : Cube := catalogue (if i.val < 6 then pairP else pairQ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_lower_deficit (t : Fin 75) :
    (neighbours pairLowerFamily (catalogue t) (pairLowerCut t)).card < (pairLowerCut t).card := by
  fin_cases t <;> decide +kernel

theorem pair_lower_no_solution : ¬ HasSolution pairLowerFamily := by
  intro h
  obtain ⟨t,p,hp⟩ := (hasSolution_iff_catalogue pairLowerFamily).mp h
  exact Nat.not_le_of_gt (pair_lower_deficit t)
    (solution_card_le pairLowerFamily (catalogue t) p hp (pairLowerCut t))

theorem pair_lower_uses_all : ∀ i, UsesAllColours (pairLowerFamily i) :=
  fun _ => catalogue_uses_all_colours _

theorem pair_lower_support : (varietySupport pairLowerFamily).card = 2 := by
  unfold varietySupport pairLowerFamily
  simp only [catalogue_index_faces]
  decide +kernel

set_option maxRecDepth 100000 in
theorem pair_lower_faces : catalogue pairP = ![0,1,2,3,2,4] ∧
    catalogue pairQ = ![0,3,1,2,4,1] := by decide +kernel

lemma solution_requires_eight {n : ℕ} (cubes : Fin n → Cube) (h : HasSolution cubes) : 8 ≤ n := by
  obtain ⟨_,_,p,_⟩ := h
  simpa using Fintype.card_le_of_embedding p

set_option maxRecDepth 100000 in
theorem lower_support : (varietySupport lowerFamily).card = 3 := by decide +kernel

/-- The existing fourteen-cube example uses the fewest possible varieties. -/
theorem fourteen_requires_three (cubes : Fin 14 → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hno : ¬ HasSolution cubes) :
    3 ≤ (varietySupport cubes).card := by
  by_contra hs
  exact hno (two_support_suffices cubes hc (by omega) (by omega))

def SupportGuarantee (k v : ℕ) : Prop := ∀ n, ∀ cubes : Fin n → Cube,
  (∀ i, UsesAllColours (cubes i)) → (varietySupport cubes).card ≤ k → v ≤ n → HasSolution cubes

lemma support_least {k N : ℕ} (upper : SupportGuarantee k (N+1)) (cubes : Fin N → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hs : (varietySupport cubes).card ≤ k)
    (hno : ¬ HasSolution cubes) : IsLeast {v | SupportGuarantee k v} (N+1) := by
  refine ⟨upper,?_⟩
  intro v hv
  by_contra h
  exact hno (hv N cubes hc hs (by omega))

/-- Exact thresholds with a bound on the number of source varieties. -/
theorem support_threshold_of_threshold (h : Threshold15) (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {v | SupportGuarantee k v} (if k = 1 then 8 else if k = 2 then 13 else 15) := by
  by_cases hk1 : k = 1
  · subst k
    simp only [ite_true]
    apply support_least (N := 7) (fun _ cubes hc hs hn => one_support_suffices cubes hc hs hn)
      (fun _ => catalogue 0) (fun _ => catalogue_uses_all_colours 0)
    · apply Finset.card_le_one_iff_subset_singleton.mpr
      refine ⟨0,?_⟩
      intro a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      simp [catalogue_index_faces]
    · intro hs
      have := solution_requires_eight _ hs
      omega
  · by_cases hk2 : k = 2
    · subst k
      simp only [show ¬ (2:ℕ)=1 by decide,ite_false,ite_true]
      exact support_least (fun _ cubes hc hs hn => two_support_suffices cubes hc hs hn)
        pairLowerFamily pair_lower_uses_all pair_lower_support.le pair_lower_no_solution
    · simp only [hk1,hk2,ite_false]
      apply support_least (N := 14) (fun _ cubes hc _ hn =>
        (Puzzle.hasSolution_iff cubes).mp (Puzzle.solution_of_threshold h cubes hc hn))
        lowerFamily lower_uses_all_colours
      · rw [lower_support]; omega
      · exact lower_no_solution

end FiveColour.Physical
