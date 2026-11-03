module
public import FiveColour.RectCounting
@[expose] public section
namespace FiveColour.Physical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma missingCorners_rotate_target (c t : Cube) (r : Fin 24) :
    missingCorners c (rotate t r) = missingCorners c t := by
  classical
  apply Finset.card_bij (fun k _ => ColourCubes.Geometry.slotEquiv r k)
  · intro k hk
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,fits_rotate_target] using hk
  · intro a _ b _ he
    exact (ColourCubes.Geometry.slotEquiv r).injective he
  · intro k hk
    refine ⟨(ColourCubes.Geometry.slotEquiv r).symm k,?_,by simp⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,fits_rotate_target,Equiv.apply_symm_apply] using hk

lemma box_supported_bits : ∀ t : Fin 75,
    (∀ k : Fin 8, (Replay.fits t 3).testBit k.val = true ∨
      (Replay.fits t 9).testBit k.val = true ∨ (Replay.fits t 56).testBit k.val = true) →
    t=3 ∨ t=9 ∨ t=56 := by decide +kernel
lemma box_supported (t : Fin 75)
    (h : ∀ k, Fits (catalogue 3) (catalogue t) k ∨
      Fits (catalogue 9) (catalogue t) k ∨ Fits (catalogue 56) (catalogue t) k) :
    t=3 ∨ t=9 ∨ t=56 := by
  apply box_supported_bits t
  simpa only [incidence_fits] using h

lemma box_private_corners :
    missingCorners (catalogue 9) (catalogue 3)=2 ∧
    missingCorners (catalogue 56) (catalogue 9)=7 ∧
    missingCorners (catalogue 3) (catalogue 56)=7 := by
  simp only [missingCorners_bits]; decide +kernel
lemma box_A_corner_subset : ∀ k,
    Fits (catalogue 56) (catalogue 3) k → Fits (catalogue 9) (catalogue 3) k := by
  simp only [← incidence_fits]; decide +kernel
lemma box_C_corner_subset : ∀ k,
    Fits (catalogue 9) (catalogue 56) k → Fits (catalogue 3) (catalogue 56) k := by
  simp only [← incidence_fits]; decide +kernel
lemma box_private_edges : ∀ r : Fin 24, ∀ a : Fin 3,
    missingAlong (catalogue 56) (rotate (catalogue 9) r) a=1 ∧
    missingAlong (catalogue 3) (rotate (catalogue 56) r) a=1 := by
  unfold missingAlong
  simp only [← edgeBits_correct]
  decide +kernel
lemma box_C_edge_subset : ∀ r : Fin 24, ∀ e : Fin 12,
    HasEdge (catalogue 9) (rotate (catalogue 56) r (edgeFaces e 0)) (rotate (catalogue 56) r (edgeFaces e 1)) →
    HasEdge (catalogue 3) (rotate (catalogue 56) r (edgeFaces e 0)) (rotate (catalogue 56) r (edgeFaces e 1)) := by
  simp only [← edgeBits_correct]; decide +kernel
end FiveColour.Physical
