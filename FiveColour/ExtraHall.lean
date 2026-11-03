module
public import FiveColour.WeightedHall
@[expose] public section
namespace FiveColour.FrameHall
variable {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]

omit [Fintype P] [Fintype I] [DecidableEq I] in
/-- A prescribed extra copy can occupy one position, leaving an ordinary
matching problem on the other positions. -/
theorem add_extra (fits : I → P → Prop) (extra : P → Prop) (p₀ : P) (hp₀ : extra p₀)
    (f : {p : P // p ≠ p₀} ↪ I) (hf : ∀ p, fits (f p) p.val) :
    ∃ g : P ↪ Option I, ∀ p, match g p with
      | none => extra p
      | some i => fits i p := by
  classical
  let g : P → Option I := fun p => if h : p = p₀ then none else some (f ⟨p,h⟩)
  have hg : Function.Injective g := by
    intro a b he
    by_cases ha : a = p₀
    · by_cases hb : b = p₀
      · exact ha.trans hb.symm
      · simp [g,ha,hb] at he
    · by_cases hb : b = p₀
      · simp [g,ha,hb] at he
      · simpa [g,ha,hb] using he
  refine ⟨⟨g,hg⟩,?_⟩
  intro p
  change match g p with | none => extra p | some i => fits i p
  dsimp [g]
  split_ifs with h
  · simpa [h] using hp₀
  · exact hf ⟨p,h⟩

/-- The two-pool criterion after removing a position supplied by an extra cube. -/
theorem two_pools_extra (fits : I → P → Prop) [DecidableRel fits]
    (extra : P → Prop) (special : Finset P) (pool strong : Finset I)
    (p₀ : P) (hp₀ : extra p₀)
    (hstrong : (special.erase p₀).card ≤ strong.card)
    (hpool : Fintype.card P - 1 ≤ pool.card)
    (hs : ∀ i ∈ strong, ∀ p ∈ special, fits i p)
    (hp : ∀ i ∈ pool, ∀ p ∉ special, fits i p) :
    ∃ g : P ↪ Option I, ∀ p, match g p with
      | none => extra p
      | some i => fits i p := by
  classical
  let R := {p : P // p ≠ p₀}
  let S : Finset R := Finset.univ.filter fun p => p.val ∈ special
  have hScard : S.card = (special.erase p₀).card := by
    apply Finset.card_bij (fun p _ => p.val)
    · intro p hp
      exact Finset.mem_erase.mpr ⟨p.property,(Finset.mem_filter.mp hp).2⟩
    · intro a _ b _ he; exact Subtype.ext he
    · intro p hp
      exact ⟨⟨p,(Finset.mem_erase.mp hp).1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_erase.mp hp).2⟩,rfl⟩
  have hRcard : Fintype.card R = Fintype.card P - 1 := by
    simp [R,Fintype.card_subtype_compl]
  obtain ⟨f,hf⟩ := match_of_two_pools (fun i (p : R) => fits i p.val) S pool strong
    (by simpa only [hScard] using hstrong) (by simpa only [hRcard] using hpool)
    (fun i hi p hpS => hs i hi p.val (Finset.mem_filter.mp hpS).2)
    (fun i hi p hpS => hp i hi p.val (by simpa [S] using hpS))
  exact add_extra fits extra p₀ hp₀ f hf
end FiveColour.FrameHall
