module
public import FiveColour.WideFrames
public import FiveColour.RodFrames
public import FiveColour.StripFrames
public import FiveColour.ThinFrames
public import FiveColour.BoxTransport
public import FiveColour.LowerBound
@[expose] public section
namespace FiveColour.Physical

/-- The complete cuboid frame function. The third term is the uniform
three-variety obstruction; it matters exactly for side sum eight. -/
def boxFrameNumber (a b c : ℕ) := max 15 (max (4*(a+b+c)-16) (2*(a+b+c)+1))
def boxNumber (a b c : ℕ) := max (a*b*c) (max 15 (2*(a+b+c)+1))
def BoxFrameThreshold (a b c n : ℕ) : Prop :=
  ∀ cubes : Fin n → Cube, (∀ i, UsesAllColours (cubes i)) → BoxFrameSolvable a b c cubes
def BoxThreshold (a b c n : ℕ) : Prop :=
  ∀ cubes : Fin n → Cube, (∀ i, UsesAllColours (cubes i)) → BoxSolvable a b c cubes

theorem box_frame_sorted (h : Threshold15) {n : ℕ} (a b c : ℕ) (ha : 2 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : boxFrameNumber a b c ≤ n) :
    BoxFrameSolvable a b c cubes := by
  obtain ⟨h15,hL,hlinear⟩ : 15 ≤ n ∧ 4*(a+b+c)-16 ≤ n ∧ 2*(a+b+c)+1 ≤ n := by
    simpa only [boxFrameNumber,max_le_iff] using hn
  by_cases hwide : 6 ≤ a+b
  · have hh := wide_frame_of_threshold h (a-2) (b-2) (c-2) (by omega) (by omega) (by omega)
      cubes hc (by omega)
    simpa only [Nat.sub_add_cancel ha,Nat.sub_add_cancel (show 2 ≤ b by omega),Nat.sub_add_cancel (show 2 ≤ c by omega)] using hh
  have ha2 : a=2 := by omega
  subst a
  by_cases hb2 : b=2
  · subst b
    by_cases hc2 : c=2
    · subst c; exact box222_of_threshold h cubes hc h15
    by_cases hc3 : c=3
    · subst c; exact thin_frame_of_threshold h 0 1 (by decide) cubes hc (by omega)
    by_cases hc4 : c=4
    · subst c; exact box224_of_threshold h cubes hc (by omega)
    have hh := sharp_rod_of_threshold h (c-2) (by omega) cubes hc (by omega)
    simpa only [Nat.sub_add_cancel (show 2 ≤ c by omega)] using hh
  · have hb3 : b=3 := by omega
    subst b
    by_cases hc3 : c=3
    · subst c; exact thin_frame_of_threshold h 1 1 (by decide) cubes hc (by omega)
    have hh := sharp_strip_of_threshold h (c-2) (by omega) cubes hc (by omega)
    simpa only [Nat.sub_add_cancel (show 2 ≤ c by omega)] using hh

/-- No order assumption on the three side lengths is needed. -/
theorem box_frame_upper (h : Threshold15) {n : ℕ} (a b c : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (cubes : Fin n → Cube)
    (hcol : ∀ i, UsesAllColours (cubes i)) (hn : boxFrameNumber a b c ≤ n) :
    BoxFrameSolvable a b c cubes := by
  have bound (x y z : ℕ) (hs : x+y+z=a+b+c) : boxFrameNumber x y z ≤ n := by
    simpa only [boxFrameNumber,hs] using hn
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · exact box_frame_sorted h a b c ha hab hbc cubes hcol hn
    · by_cases hac : a ≤ c
      · exact box_frame_swap23 cubes (box_frame_sorted h a c b ha hac (by omega) cubes hcol (bound a c b (by omega)))
      · exact box_frame_swap23 cubes (box_frame_swap12 cubes
          (box_frame_sorted h c a b hc (by omega) hab cubes hcol (bound c a b (by omega))))
  · by_cases hac : a ≤ c
    · exact box_frame_swap12 cubes (box_frame_sorted h b a c hb (by omega) hac cubes hcol (bound b a c (by omega)))
    · by_cases hbc : b ≤ c
      · exact box_frame_swap12 cubes (box_frame_swap23 cubes
          (box_frame_sorted h b c a hb hbc (by omega) cubes hcol (bound b c a (by omega))))
      · exact box_frame_swap12 cubes (box_frame_swap23 cubes (box_frame_swap12 cubes
          (box_frame_sorted h c b a hc (by omega) (by omega) cubes hcol (bound c b a (by omega)))))

/-- All three lower bounds hold for the physical model, including arbitrary
proper rotations and all permutations of the three box axes. -/
theorem box_frame_lower (a b c n : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : BoxFrameThreshold a b c n) : boxFrameNumber a b c ≤ n := by
  have h15 : 15 ≤ n := by
    by_contra hn
    let pick : Fin n ↪ Fin 14 := Fin.castLEEmb (by omega)
    have hh := h (fun i => lowerFamily (pick i)) (fun _ => lower_uses_all_colours _)
    exact lower_no_solution (box_frame_hasSolution lowerFamily (box_frame_mono lowerFamily pick hh))
  have hL : 4*(a+b+c)-16 ≤ n := box_frame_requires_pieces ha hb hc (fun _ : Fin n => catalogue 0)
    (h _ (fun _ => catalogue_uses_all_colours 0))
  have hlinear : 2*(a+b+c)+1 ≤ n := by
    by_contra hn
    obtain ⟨bad,hbad,hno⟩ := box_obstruction a b c ha hb hc
    let pick : Fin n ↪ Fin (2*(a+b+c)) := Fin.castLEEmb (by omega)
    exact hno (box_frame_mono bad pick (h (fun i => bad (pick i)) (fun _ => hbad _)))
  exact max_le h15 (max_le hL hlinear)

theorem box_frame_threshold_iff (h : Threshold15) (a b c n : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    BoxFrameThreshold a b c n ↔ boxFrameNumber a b c ≤ n := by
  exact ⟨box_frame_lower a b c n ha hb hc,fun hn cubes hcol => box_frame_upper h a b c ha hb hc cubes hcol hn⟩

lemma box_volume_ge_frame (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    4*(a+b+c)-16 ≤ a*b*c := by
  let l := fun i : Fin 3 => ![a-2,b-2,c-2] i
  calc
    _ = Fintype.card (RectSlot l) := (box_frame_card a b c ha hb hc (Equiv.refl _)).symm
    _ ≤ Fintype.card (RectFullSlot l) := Fintype.card_le_of_embedding Function.Embedding.inl
    _ = a*b*c := (rectFullSlot_card l).trans (box_volume a b c ha hb hc (Equiv.refl _))

theorem box_threshold_iff (h : Threshold15) (a b c n : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    BoxThreshold a b c n ↔ boxNumber a b c ≤ n := by
  constructor
  · intro hn
    have hvol : a*b*c ≤ n := box_requires_pieces ha hb hc (fun _ : Fin n => catalogue 0)
      (hn _ (fun _ => catalogue_uses_all_colours 0))
    have hframe : BoxFrameThreshold a b c n := fun cubes hcol => box_frame_of_full cubes (hn cubes hcol)
    have hbnd := box_frame_lower a b c n ha hb hc hframe
    unfold boxFrameNumber at hbnd
    exact max_le hvol (max_le (le_of_max_le_left hbnd) (le_of_max_le_right (le_of_max_le_right hbnd)))
  · intro hn cubes hcol
    obtain ⟨hvol,h15,hlinear⟩ : a*b*c ≤ n ∧ 15 ≤ n ∧ 2*(a+b+c)+1 ≤ n := by
      simpa only [boxNumber,max_le_iff] using hn
    apply box_full_of_frame a b c ha hb hc cubes hcol hvol
    apply box_frame_upper h a b c ha hb hc cubes hcol
    exact max_le h15 (max_le ((box_volume_ge_frame a b c ha hb hc).trans hvol) hlinear)
end FiveColour.Physical
