module
public import FiveColour.RodBounds
public import FiveColour.RodChoice
public import FiveColour.RectSmallHall
@[expose] public section
namespace FiveColour.Physical
set_option maxHeartbeats 0

def varietyCopies {n : ℕ} (cubes : Fin n → Cube) (v : Fin 75) :=
  Finset.univ.filter fun i => catalogueIndex (cubes i)=v
lemma variety_copies_fit {n : ℕ} (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (v : Fin 75) (l : Fin 3 → ℕ) (i : Fin n) (hi : i ∈ varietyCopies cubes v) (p : RectSlot l) :
    RectFits (cubes i) (catalogue v) p := by
  apply (rectFits_catalogueIndex _ _ (hc i) p).mpr
  rw [(Finset.mem_filter.mp hi).2]
  exact rectFits_self _ p

lemma rod_universal {n : ℕ} (M : ℕ) (hM : 2 ≤ M) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 4*M+8 ≤ n)
    (v : Fin 75) (ho : OppositeRepeat (catalogue v))
    (hv : 2*M+4 ≤ (varietyCopies cubes v).card) : BoxFrameSolvable 2 2 (M+2) cubes := by
  classical
  obtain ⟨a,ha,haxial⟩ := rod_axis v
  apply box_of_rod a M cubes
  apply rect_of_match _ cubes v
  apply FrameHall.match_of_pools (fun i (p : RectSlot (RodLengths a M)) => RectFits (cubes i) (catalogue v) p) (2*M+4) Finset.univ (varietyCopies cubes v)
    (by simpa only [rodSlot_card,Finset.card_univ,Fintype.card_fin] using hn) hv
  · intro i _
    rw [rect_missing_index _ _ _ (hc i),rod_count_bits]
    exact rod_axial_bound _ v a M hM (haxial ho)
  · exact fun i hi p => variety_copies_fit cubes hc v _ i hi p

/-- One fewer than half the copies of an opposite-repeat variety suffices:
a failure for that target forces more than half of another variety. -/
theorem rod_concentrated {n : ℕ} (M : ℕ) (hM : 3 ≤ M) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 4*M+8 ≤ n)
    (v : Fin 75) (ho : OppositeRepeat (catalogue v))
    (hv : 2*M+3 ≤ (varietyCopies cubes v).card) : BoxFrameSolvable 2 2 (M+2) cubes := by
  classical
  by_contra hbox
  obtain ⟨a,ha,haxial⟩ := rod_axis v
  have htarget : RodTarget v a := ⟨ha,haxial⟩
  let l := RodLengths a M
  let fits := fun (i : Fin n) (p : RectSlot l) => RectFits (cubes i) (catalogue v) p
  have hfail : ¬ ∃ f : RectSlot l ↪ Fin n, ∀ p, fits (f p) p :=
    fun hh => hbox (box_of_rod a M cubes (rect_of_match l cubes v hh))
  have hsmall : ∀ D : Finset (RectSlot l), D.card ≤ 2*M+3 → D.card ≤ (FrameHall.neighbours fits D).card := by
    intro D hd
    by_cases hnD : D.Nonempty
    · obtain ⟨p,hp⟩ := hnD
      apply hd.trans (hv.trans (Finset.card_le_card ?_))
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,variety_copies_fit cubes hc v l i hi p⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hnD]
  obtain ⟨i,hlarge,hpool⟩ := FrameHall.failure_concentrates fits (fun i => catalogueIndex (cubes i))
    (2*M+3) 1 (by simpa only [l,rodSlot_card,Fintype.card_fin] using hn) hsmall
    (by
      intro i
      change (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue v) p).card ≤ _
      rw [rect_missing_index _ _ _ (hc i),rod_count_bits]
      exact rod_axial_bound _ v a M (by omega) (haxial ho))
    (by
      intro i j hij
      change (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue v) p ∧ ¬ RectFits (cubes j) (catalogue v) p).card ≤ _
      rw [rect_joint_missing_index _ _ _ _ (hc i) (hc j)]
      exact rod_axial_separate v a M hM htarget ho _ _ hij) hfail
  change 2*M+3 < (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue v) p).card at hlarge
  rw [rect_missing_index _ _ _ (hc i),rod_count_bits] at hlarge
  have hop := rod_axial_large_opposite _ v a M hM htarget ho hlarge
  apply hbox (rod_universal M (by omega) cubes hc hn (catalogueIndex (cubes i)) hop ?_)
  have hpool' : n+1 ≤ (varietyCopies cubes (catalogueIndex (cubes i))).card+(2*M+3)+1 := by
    simpa only [Fintype.card_fin,varietyCopies] using hpool
  omega

/-- A failed thin target forces a large opposite-repeat pool. -/
lemma rod_alternative (h : Threshold15) {n : ℕ} (M d : ℕ) (hM : 2 ≤ M)
    (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hn : 4*M+8 ≤ n) (hn15 : 15 ≤ n) (hd8 : 8 ≤ d)
    (hMd : M+7 ≤ d) (hdmax : d ≤ 2*M+6) (hdn : 2*d ≤ n+1) (hfamily : 8+d ≤ n+1) :
    BoxFrameSolvable 2 2 (M+2) cubes ∨
      ∃ v : Fin 75, OppositeRepeat (catalogue v) ∧ n+1 ≤ (varietyCopies cubes v).card+2*M+6 := by
  classical
  obtain ⟨t,corners,hf,a,ha,haxial,hedges⟩ := rod_target h d cubes hc hn15 hdn hfamily
  let l := RodLengths a M
  let fits := fun (i : Fin n) (p : RectSlot l) => RectFits (cubes i) (catalogue t) p
  have htarget : RodTarget t a := ⟨ha,haxial⟩
  by_cases hmatch : ∃ f : RectSlot l ↪ Fin n, ∀ p, fits (f p) p
  · exact Or.inl (box_of_rod a M cubes (rect_of_match l cubes t hmatch))
  have hsmall := rect_small_hall l cubes t d corners hf (by
    intro e he
    apply hedges e
    by_contra hh; simp [l,RodLengths,hh] at he)
  obtain ⟨i,hlarge,hpool⟩ := FrameHall.failure_concentrates fits (fun i => catalogueIndex (cubes i))
    d (2*M+6-d) (by simpa only [l,rodSlot_card,Fintype.card_fin] using hn) hsmall
    (by
      intro i
      change (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue t) p).card ≤ _
      rw [rect_missing_index _ _ _ (hc i),rod_count_bits]
      have hb := rod_general_bound (catalogueIndex (cubes i)) t a M (by omega) htarget
      omega)
    (by
      intro i j hij
      change (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue t) p ∧ ¬ RectFits (cubes j) (catalogue t) p).card ≤ _
      rw [rect_joint_missing_index _ _ _ _ (hc i) (hc j)]
      exact rod_separate t a M d (by omega) htarget hd8 hMd _ _ hij) hmatch
  change d < (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue t) p).card at hlarge
  rw [rect_missing_index _ _ _ (hc i),rod_count_bits] at hlarge
  have hop : OppositeRepeat (catalogue (catalogueIndex (cubes i))) := by
    by_contra hh
    have hb := rod_adjacent_bound (catalogueIndex (cubes i)) t a M (by omega) htarget hh
    omega
  right; refine ⟨catalogueIndex (cubes i),hop,?_⟩
  have hpool' : n+1 ≤ (varietyCopies cubes (catalogueIndex (cubes i))).card+d+(2*M+6-d) := by
    simpa only [Fintype.card_fin,varietyCopies] using hpool
  omega

theorem box224_of_threshold (h : Threshold15) {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 17 ≤ n) : BoxFrameSolvable 2 2 4 cubes := by
  rcases rod_alternative h 2 9 (by decide) cubes hc (by omega) (by omega)
    (by decide) (by decide) (by decide) (by omega) (by omega) with hbox | ⟨v,ho,hv⟩
  · exact hbox
  · exact rod_universal 2 (by decide) cubes hc (by omega) v ho (by omega)

theorem sharp_rod_of_threshold (h : Threshold15) {n : ℕ} (M : ℕ) (hM : 3 ≤ M)
    (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i)) (hn : 4*M+8 ≤ n) :
    BoxFrameSolvable 2 2 (M+2) cubes := by
  rcases rod_alternative h M (2*M+4) (by omega) cubes hc hn (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) with hbox | ⟨v,ho,hv⟩
  · exact hbox
  · exact rod_concentrated M hM cubes hc hn v ho (by omega)
end FiveColour.Physical
