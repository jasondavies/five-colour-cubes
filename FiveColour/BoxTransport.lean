module
public import FiveColour.BoxLowerBound
public import FiveColour.BoxMatching
@[expose] public section
namespace FiveColour.Physical

lemma box_frame_mono {n k a b c : ℕ} (cubes : Fin k → Cube) (pick : Fin n ↪ Fin k)
    (h : BoxFrameSolvable a b c (fun i => cubes (pick i))) : BoxFrameSolvable a b c cubes := by
  obtain ⟨axes,t,ht,f,hf⟩ := h
  exact ⟨axes,t,ht,f.trans pick,hf⟩
lemma box_frame_of_full {n a b c : ℕ} (cubes : Fin n → Cube)
    (h : BoxSolvable a b c cubes) : BoxFrameSolvable a b c cubes := by
  obtain ⟨axes,h⟩ := h
  exact ⟨axes,rect_frame_of_full _ cubes h⟩
lemma box_frame_reorder {n : ℕ} (x y : Fin 3 → ℕ) (cubes : Fin n → Cube)
    (perm : Equiv.Perm (Fin 3)) (hxy : ∀ i, y (perm i)=x i)
    (h : ∃ axes : Equiv.Perm (Fin 3), RectSolvable (fun i => x (axes i)) cubes) :
    ∃ axes : Equiv.Perm (Fin 3), RectSolvable (fun i => y (axes i)) cubes := by
  obtain ⟨axes,h⟩ := h
  refine ⟨axes.trans perm,?_⟩
  simpa only [Equiv.trans_apply,hxy] using h
lemma box_frame_swap12 {n a b c : ℕ} (cubes : Fin n → Cube)
    (h : BoxFrameSolvable a b c cubes) : BoxFrameSolvable b a c cubes := by
  exact box_frame_reorder ![a-2,b-2,c-2] ![b-2,a-2,c-2] cubes (Equiv.swap 0 1)
    (by intro i; fin_cases i <;> norm_num [Equiv.swap_apply_def]) h
lemma box_frame_swap23 {n a b c : ℕ} (cubes : Fin n → Cube)
    (h : BoxFrameSolvable a b c cubes) : BoxFrameSolvable a c b cubes := by
  exact box_frame_reorder ![a-2,b-2,c-2] ![a-2,c-2,b-2] cubes (Equiv.swap 1 2)
    (by intro i; fin_cases i <;> norm_num [Equiv.swap_apply_def]) h

lemma box222_of_threshold (h : Threshold15) {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 15 ≤ n) : BoxFrameSolvable 2 2 2 cubes := by
  obtain ⟨t,corners,hf⟩ := corners_of_threshold h cubes hc hn
  let l : Fin 3 → ℕ := fun _ => 0
  let f : RectSlot l ↪ Fin n :=
    ⟨fun p => match p with | .inl k => corners k | .inr e => Fin.elim0 e.2,
      by intro a b he; cases a with
         | inl a => cases b with
           | inl b => exact congrArg Sum.inl (corners.injective he)
           | inr b => exact Fin.elim0 b.2
         | inr a => exact Fin.elim0 a.2⟩
  have hm : RectSolvable l cubes := rect_of_match l cubes t ⟨f,by
    intro p; cases p with
    | inl k => exact hf k
    | inr e => exact Fin.elim0 e.2⟩
  refine ⟨Equiv.refl _,?_⟩
  change RectSolvable (fun i : Fin 3 => ![0,0,0] i) cubes
  have he : (fun i : Fin 3 => (![0,0,0] i : ℕ)) = l := by funext i; fin_cases i <;> rfl
  rw [he]; exact hm
end FiveColour.Physical
