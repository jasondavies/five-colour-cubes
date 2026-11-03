module
public import FiveColour.SharpFrames
public import FiveColour.FullCube
public import FiveColour.ComparatorBridge
@[expose] public section
namespace FiveColour.Physical

/-- The sharp piece count is a necessary lower bound for every frame. -/
lemma frame_requires_pieces {m : ℕ} (q : ℕ) (cubes : Fin m → Cube)
    (h : FrameSolvable q cubes) : 12*q+8 ≤ m := by
  obtain ⟨_,_,p,_⟩ := h
  simpa [frameSlot_card,Nat.add_comm] using Fintype.card_le_of_embedding p

lemma cube_size_ge_frame (q : ℕ) (hq : 1 ≤ q) : 12*q+8 ≤ (q+2)^3 := by
  have hs : 1 ≤ q^2 := by nlinarith
  have hc : 1 ≤ q^3 := by nlinarith [Nat.mul_le_mul hs hq]
  nlinarith

/-- The extra cuboid lower bound is absorbed by the cube-frame count. -/
lemma boxFrameNumber_cube (n : ℕ) (hn : 2 ≤ n) :
    boxFrameNumber n n n = max (12*n-16) 15 := by
  unfold boxFrameNumber
  omega

lemma boxNumber_cube (n : ℕ) (hn : 2 ≤ n) :
    boxNumber n n n = max (n^3) 15 := by
  have he : n*n*n = n^3 := by ring
  unfold boxNumber
  rw [he]
  by_cases h2 : n = 2
  · subst n; decide
  have hsize := cube_size_ge_frame (n-2) (by omega)
  have he : n-2+2 = n := by omega
  rw [he] at hsize
  omega

/-- The sharp side-length form is the equal-side cuboid theorem. -/
theorem frame_bound_of_threshold (h : Threshold15) {m : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hm : 12*n-16 ≤ m) : FrameSolvable (n-2) cubes :=
  sharp_frame_of_threshold h (n-2) (by omega) cubes hc (by omega)

/-- The entire cube-frame function, specialised from the cuboid classification. -/
theorem frame_threshold_all_of_threshold (h : Threshold15) (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → FrameSolvable (n-2) cubes}
      (max (12*n-16) 15) := by
  refine ⟨?_,?_⟩
  · intro m cubes hc hm
    apply (frame_iff_box n cubes).mpr
    exact box_frame_upper h n n n hn hn hn cubes hc
      (by simpa only [boxFrameNumber_cube n hn] using hm)
  · intro v hv
    have hb : BoxFrameThreshold n n n v := fun cubes hc =>
      (frame_iff_box n cubes).mp (hv v cubes hc le_rfl)
    simpa only [boxFrameNumber_cube n hn] using box_frame_lower n n n v hn hn hn hb

/-- From side length three, no spare cubes are needed even for the frame. -/
theorem frame_threshold_of_threshold (h : Threshold15) (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → FrameSolvable (n-2) cubes} (12*n-16) := by
  simpa only [max_eq_left (by omega : 15 ≤ 12*n-16)] using
    frame_threshold_all_of_threshold h n (by omega)

/-- From side length three, piece count is the only obstruction to a complete cube. -/
theorem full_iff_size_of_threshold (h : Threshold15) {m : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FullSolvable (n-2) cubes ↔ n^3 ≤ m := by
  have he : n-2+2 = n := by omega
  have h15 : 15 ≤ n^3 := by
    have hb := cube_size_ge_frame (n-2) (by omega)
    rw [he] at hb
    omega
  constructor
  · intro hf
    simpa only [he] using full_requires_pieces (n-2) cubes hf
  · intro hm
    apply (full_iff_box n cubes).mpr
    exact ((box_threshold_iff h n n n m (by omega) (by omega) (by omega)).mpr
      (by simpa only [boxNumber_cube n (by omega),max_eq_left h15] using hm)) cubes hc

/-- All n³ supplied cubes can be used, for every n ≥ 3. -/
theorem full_cube_of_threshold (h : Threshold15) (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin (n^3) → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FullSolvable (n-2) cubes :=
  (full_iff_size_of_threshold h n hn cubes hc).mpr le_rfl

/-- The complete-cube threshold, including the exceptional corner case. -/
theorem complete_threshold_of_threshold (h : Threshold15) (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Cube,
      (∀ i, UsesAllColours (cubes i)) → v ≤ m → FullSolvable (n-2) cubes}
      (max (n^3) 15) := by
  refine ⟨?_,?_⟩
  · intro m cubes hc hm
    apply (full_iff_box n cubes).mpr
    exact ((box_threshold_iff h n n n m hn hn hn).mpr
      (by simpa only [boxNumber_cube n hn] using hm)) cubes hc
  · intro v hv
    have hb : BoxThreshold n n n v := fun cubes hc =>
      (full_iff_box n cubes).mp (hv v cubes hc le_rfl)
    simpa only [boxNumber_cube n hn] using (box_threshold_iff h n n n v hn hn hn).mp hb

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

lemma frame_zero_iff {m : ℕ} (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i)) :
    FrameSolvable 0 cubes ↔ HasSolution cubes := by
  constructor
  · intro hf
    exact (full_zero_iff cubes hc).mp (full_of_frame 0 cubes hc (by
      simpa using frame_requires_pieces 0 cubes hf) hf)
  · intro hs
    exact frame_of_full 0 cubes ((full_zero_iff cubes hc).mpr hs)

end FiveColour.Physical
