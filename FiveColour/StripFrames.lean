module
public import FiveColour.StripBounds
public import FiveColour.ThinChoice
public import FiveColour.RodFrames
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators
set_option maxHeartbeats 0

lemma stripSlot_card (axes : Equiv.Perm (Fin 3)) (M : ℕ) :
    Fintype.card (RectSlot (Strip.Lengths axes M)) = 4*M+12 := by
  rw [rectSlot_card,Equiv.sum_comp axes (fun i => ![0,1,M] i)]
  simp [Fin.sum_univ_succ]; omega
lemma box_of_strip {n : ℕ} (axes : Equiv.Perm (Fin 3)) (M : ℕ) (cubes : Fin n → Cube)
    (h : RectSolvable (Strip.Lengths axes M) cubes) : BoxFrameSolvable 2 3 (M+2) cubes := by
  refine ⟨axes,?_⟩
  simpa only [Nat.add_sub_cancel,Nat.reduceSub] using h

/-- At length c≥4, a failed initial target forces half the collection to be
one opposite-repeat variety, which becomes the successful target. -/
theorem sharp_strip_of_threshold (h : Threshold15) {n : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i)) (hn : 4*M+12 ≤ n) :
    BoxFrameSolvable 2 3 (M+2) cubes := by
  classical
  by_contra hbox
  let d := 2*M+6
  obtain ⟨t,corners,hf,z,hz,hedges⟩ := thin_target h d cubes hc (by omega) (by dsimp [d]; omega)
  let axes := Equiv.swap (0 : Fin 3) z
  let l := Strip.Lengths axes M
  let fits := fun (i : Fin n) (p : RectSlot l) => RectFits (cubes i) (catalogue t) p
  have hmono : ∀ a, axes a ≠ 0 → BichromaticAxis (catalogue t) a := by
    intro a ha; exact hz a (fun he => ha ((swap_zero z a).mpr he))
  have ha := hmono (axes.symm 1) (by simp)
  have hb := hmono (axes.symm 2) (by simp)
  have hab : axes.symm (1 : Fin 3) ≠ axes.symm 2 := axes.symm.injective.ne (by decide)
  have hfail : ¬ ∃ f : RectSlot l ↪ Fin n, ∀ p, fits (f p) p :=
    fun hh => hbox (box_of_strip axes M cubes (rect_of_match l cubes t hh))
  have hsmall := rect_small_hall l cubes t d corners hf (by
    intro e he
    apply hedges e
    intro hez
    have hx : axes (edgeAxis e)=0 := (swap_zero z _).mpr hez
    simp [l,Strip.Lengths,hx] at he)
  obtain ⟨i,hlarge,hpool⟩ := FrameHall.failure_concentrates fits (fun i => catalogueIndex (cubes i)) d 1
    (by simpa only [l,stripSlot_card,Fintype.card_fin] using hn) hsmall
    (by
      intro i
      change (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue t) p).card ≤ _
      rw [rect_missing_index _ _ _ (hc i),Strip.count_bits]
      exact (Strip.defect_bounds _ t _ _ hab ha hb M hM).1)
    (by
      intro i j hij
      change (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue t) p ∧ ¬ RectFits (cubes j) (catalogue t) p).card ≤ _
      rw [rect_joint_missing_index _ _ _ _ (hc i) (hc j)]
      exact Strip.separation _ _ t axes M hM hmono hij) hfail
  change d < (Finset.univ.filter fun p : RectSlot l => ¬ RectFits (cubes i) (catalogue t) p).card at hlarge
  rw [rect_missing_index _ _ _ (hc i),Strip.count_bits] at hlarge
  have hop := (Strip.maximal_of_large _ t _ _ hab ha hb M hM hlarge).1
  let v := catalogueIndex (cubes i)
  have hv : d ≤ (varietyCopies cubes v).card := by
    have hpool' : n+1 ≤ (varietyCopies cubes v).card+d+1 := by
      simpa only [Fintype.card_fin,varietyCopies] using hpool
    dsimp [d] at *; omega
  obtain ⟨a,_,haxial⟩ := rod_axis v
  let axes' := Equiv.swap (0 : Fin 3) a
  apply hbox (box_of_strip axes' M cubes ?_)
  apply rect_of_match _ cubes v
  apply FrameHall.match_of_pools
    (fun i (p : RectSlot (Strip.Lengths axes' M)) => RectFits (cubes i) (catalogue v) p)
    d Finset.univ (varietyCopies cubes v)
    (by simpa only [stripSlot_card,Finset.card_univ,Fintype.card_fin] using hn) hv
  · intro j _
    rw [rect_missing_index _ _ _ (hc j)]
    exact Strip.opposite_short_bound _ v a (haxial hop) M hM
  · exact fun j hj p => variety_copies_fit cubes hc v _ j hj p
end FiveColour.Physical
