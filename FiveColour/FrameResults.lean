module
public import FiveColour.RareFrames
public import FiveColour.FullCube
public import FiveColour.ComparatorBridge
@[expose] public section
namespace FiveColour.Physical

/-- The sharp piece count is a necessary lower bound for every frame. -/
lemma frame_requires_pieces {m : ℕ} (q : ℕ) (cubes : Fin m → Cube)
    (h : FrameSolvable q cubes) : 12*q+8 ≤ m := by
  obtain ⟨_,_,p,_⟩ := h
  simpa [frameSlot_card,Nat.add_comm] using Fintype.card_le_of_embedding p

/-- The side-length form of the rare-pair Hall bound. -/
theorem frame_bound_of_threshold (h : Threshold15) {m : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hm : max (12*n-16) (11*n-6) ≤ m) : FrameSolvable (n-2) cubes :=
  rare_frame_of_threshold h (n-2) (by omega) cubes hc (by omega) (by omega)

/-- From side length ten, no spare cubes are needed even for the frame. -/
theorem frame_threshold_of_threshold (h : Threshold15) (n : ℕ) (hn : 10 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → FrameSolvable (n-2) cubes} (12*n-16) := by
  refine ⟨fun m cubes hc hm => frame_bound_of_threshold h n (by omega) cubes hc (by omega),?_⟩
  intro v hv
  have hf := hv v (fun _ => catalogue 0) (fun _ => catalogue_uses_all_colours 0) le_rfl
  have := frame_requires_pieces (n-2) _ hf
  omega

lemma cube_size_ge_frame_bound (q : ℕ) (hq : 1 ≤ q) :
    max (12*q+8) (11*q+16) ≤ (q+2)^3 := by
  have hs : 1 ≤ q^2 := by nlinarith
  have hc : 1 ≤ q^3 := by nlinarith [Nat.mul_le_mul hs hq]
  apply max_le <;> nlinarith

/-- From side length three, piece count is the only obstruction to a complete cube. -/
theorem full_iff_size_of_threshold (h : Threshold15) {m : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FullSolvable (n-2) cubes ↔ n^3 ≤ m := by
  have he : n-2+2 = n := by omega
  constructor
  · intro hf
    simpa only [he] using full_requires_pieces (n-2) cubes hf
  · intro hm
    have hb := cube_size_ge_frame_bound (n-2) (by omega)
    rw [he] at hb
    exact full_of_frame (n-2) cubes hc (by simpa only [he] using hm)
      (rare_frame_of_threshold h (n-2) (by omega) cubes hc (by omega) (by omega))

/-- All n³ supplied cubes can be used, for every n ≥ 3. -/
theorem full_cube_of_threshold (h : Threshold15) (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin (n^3) → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FullSolvable (n-2) cubes :=
  (full_iff_size_of_threshold h n hn cubes hc).mpr le_rfl

lemma full_hasSolution {m : ℕ} (q : ℕ) (cubes : Fin m → Cube)
    (h : FullSolvable q cubes) : HasSolution cubes := by
  obtain ⟨t,ht,p,hp⟩ := frame_of_full q cubes h
  refine ⟨t,ht,Function.Embedding.inl.trans p,?_⟩
  intro k
  obtain ⟨r,hr,hfit⟩ := hp (.inl k)
  obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff r).mp hr
  refine ⟨r,?_⟩
  intro a
  exact hfit _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)

lemma full_zero_iff {m : ℕ} (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FullSolvable 0 cubes ↔ HasSolution cubes := by
  refine ⟨full_hasSolution 0 cubes,?_⟩
  rintro ⟨t,ht,p,hp⟩
  apply full_of_frame 0 cubes hc (by simpa using Fintype.card_le_of_embedding p)
  let f : FrameSlot 0 → Fin m := Sum.elim p (fun x => Fin.elim0 x.2)
  have hinj : Function.Injective f := by
    intro a b he
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (p.injective he)
      | inr b => exact Fin.elim0 b.2
    | inr a => exact Fin.elim0 a.2
  refine ⟨t,ht,⟨f,hinj⟩,?_⟩
  intro pos
  cases pos with
  | inl k => exact frameFits_physical _ _ (.inl k : FrameSlot 0) (hp k)
  | inr pos => exact Fin.elim0 pos.2

/-- The exact guaranteed pool size, including the exceptional corner case. -/
theorem complete_threshold_of_threshold (h : Threshold15) (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → FullSolvable (n-2) cubes}
      (max (n^3) 15) := by
  by_cases he : n = 2
  · subst n
    change IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → FullSolvable 0 cubes} 15
    refine ⟨fun m cubes hc hm => (full_zero_iff cubes hc).mpr
      ((Puzzle.hasSolution_iff cubes).mp (Puzzle.solution_of_threshold h cubes hc hm)),?_⟩
    intro v hv
    by_contra hsmall
    exact lower_no_solution ((full_zero_iff lowerFamily lower_uses_all_colours).mp
      (hv 14 lowerFamily lower_uses_all_colours (by omega)))
  · have hn3 : 3 ≤ n := by omega
    have hn15 : 15 ≤ n^3 := by nlinarith [Nat.mul_le_mul (show 9 ≤ n^2 by nlinarith) hn3]
    rw [max_eq_left hn15]
    refine ⟨fun m cubes hc hm => (full_iff_size_of_threshold h n hn3 cubes hc).mpr hm,?_⟩
    intro v hv
    exact (full_iff_size_of_threshold h n hn3 (fun _ : Fin v => catalogue 0)
      (fun _ => catalogue_uses_all_colours 0)).mp
      (hv v _ (fun _ => catalogue_uses_all_colours 0) le_rfl)

end FiveColour.Physical
