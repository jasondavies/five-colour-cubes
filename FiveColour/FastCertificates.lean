module
public import FiveColour.BoxCertificates
@[expose] public section
namespace FiveColour.Certificate.Fast
open scoped BigOperators

/-- Common information about all surviving Hall cuts. -/
structure Summary (n : ℕ) where
  common : Finset (Fin n)
  united : Finset (Fin n)
  slack : ℤ
  need : ℤ

def singleton {n : ℕ} (b : Box n) (goal : ℤ) (c : Cut n) : Summary n where
  common := c.neighbours
  united := c.neighbours
  slack := c.rhs - mass b.lower c.neighbours
  need := goal - c.rhs - mass b.upper c.neighboursᶜ

def merge {n : ℕ} (s t : Summary n) : Summary n where
  common := s.common ∩ t.common
  united := s.united ∪ t.united
  slack := max s.slack t.slack
  need := min s.need t.need

/-- The summary bounds are valid for this particular surviving cut. -/
def Covers {n : ℕ} (b : Box n) (goal : ℤ) (s : Summary n) (c : Cut n) : Prop :=
  s.common ⊆ c.neighbours ∧ c.neighbours ⊆ s.united ∧
    c.rhs - mass b.lower c.neighbours ≤ s.slack ∧
    s.need ≤ goal - c.rhs - mass b.upper c.neighboursᶜ

lemma singleton_covers {n : ℕ} (b : Box n) (goal : ℤ) (c : Cut n) :
    Covers b goal (singleton b goal c) c := by
  exact ⟨Finset.Subset.refl _, Finset.Subset.refl _, le_rfl, le_rfl⟩

lemma merge_covers_left {n : ℕ} {b : Box n} {goal : ℤ} {s t : Summary n} {c : Cut n}
    (h : Covers b goal s c) : Covers b goal (merge s t) c := by
  exact ⟨Finset.inter_subset_left.trans h.1, h.2.1.trans Finset.subset_union_left,
    h.2.2.1.trans (le_max_left _ _), (min_le_left _ _).trans h.2.2.2⟩

lemma merge_covers_right {n : ℕ} {b : Box n} {goal : ℤ} {s t : Summary n} {c : Cut n}
    (h : Covers b goal t c) : Covers b goal (merge s t) c := by
  exact ⟨Finset.inter_subset_right.trans h.1, h.2.1.trans Finset.subset_union_right,
    h.2.2.1.trans (le_max_right _ _), (min_le_right _ _).trans h.2.2.2⟩

def summarize {n : ℕ} (b : Box n) (goal : ℤ) : List (Cut n) → Option (Summary n)
  | [] => none
  | c :: cs =>
    let rest := summarize b goal cs
    if c.Possible b goal then
      some (match rest with | none => singleton b goal c | some t => merge (singleton b goal c) t)
    else rest

lemma summarize_covers {n : ℕ} (b : Box n) (goal : ℤ) (cs : List (Cut n))
    {c : Cut n} (hc : c ∈ cs) (hp : c.Possible b goal) :
    ∃ s, summarize b goal cs = some s ∧ Covers b goal s c := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    simp only [List.mem_cons] at hc
    by_cases hd : d.Possible b goal
    · rcases hc with rfl | hc
      · cases hr : summarize b goal ds with
        | none => exact ⟨_, by simp [summarize, hd, hr], singleton_covers _ _ _⟩
        | some s => exact ⟨merge (singleton b goal c) s, by simp [summarize, hd, hr],
            merge_covers_left (singleton_covers _ _ _)⟩
      · obtain ⟨s, hs, hsc⟩ := ih hc
        exact ⟨merge (singleton b goal d) s, by simp [summarize, hd, hs], merge_covers_right hsc⟩
    · have hc' : c ∈ ds := hc.resolve_left (fun h => hd (h ▸ hp))
      obtain ⟨s, hs, hsc⟩ := ih hc'
      exact ⟨s, by simp [summarize, hd, hs], hsc⟩

def applySummary {n : ℕ} (b : Box n) (s : Summary n) : Box n where
  lower i := if i ∈ s.united then b.lower i else max (b.lower i) (b.upper i + s.need)
  upper i := if i ∈ s.common then min (b.upper i) (b.lower i + s.slack) else b.upper i

lemma applySummary_contains {n : ℕ} {b : Box n} {x : Vector n} {goal : ℤ}
    {s : Summary n} {c : Cut n} (hx : b.Contains x) (ht : mass x Finset.univ = goal)
    (hc : c.Holds x) (hs : Covers b goal s c) : (applySummary b s).Contains x := by
  intro i
  have hxi := hx i
  have hsum := mass_complement x c.neighbours
  unfold Cut.Holds at hc
  constructor
  · by_cases hi : i ∈ s.united
    · simpa only [applySummary, ite_eq_left hi] using hxi.1
    · have hic : i ∈ c.neighboursᶜ := Finset.mem_compl.mpr (fun h => hi (hs.2.1 h))
      have hb := (coordinate_bound hx hic).2
      have hn := hs.2.2.2
      simp only [applySummary, ite_eq_right hi, max_le_iff]
      exact ⟨hxi.1, by omega⟩
  · by_cases hi : i ∈ s.common
    · have hb := (coordinate_bound hx (hs.1 hi)).1
      have hh := hs.2.2.1
      simp only [applySummary, ite_eq_left hi, le_min_iff]
      exact ⟨hxi.2, by omega⟩
    · simpa only [applySummary, ite_eq_right hi] using hxi.2

/-- One summary replaces a hull of up to 255 separate boxes. -/
def refine {n : ℕ} (b : Box n) (goal : ℤ) (cs : List (Cut n)) : Option (Box n) :=
  (summarize b goal cs).map (applySummary b)

theorem refine_sound {n : ℕ} {b : Box n} {x : Vector n} {goal : ℤ}
    (hx : b.Contains x) (ht : mass x Finset.univ = goal) (cs : List (Cut n))
    (hc : ∃ c ∈ cs, c.Holds x) :
    ∃ b', refine b goal cs = some b' ∧ b'.Contains x := by
  obtain ⟨c, hc, hcx⟩ := hc
  obtain ⟨s, hs, hsc⟩ := summarize_covers b goal cs hc (possible_of_holds hx hcx ht)
  exact ⟨applySummary b s, by simp [refine, hs], applySummary_contains hx ht hcx hsc⟩

def check {n k : ℕ} (p : Problem n k) (b : Box n) : Proof n k → Bool
  | .mass => decide (p.goal < mass b.lower Finset.univ ∨ mass b.upper Finset.univ < p.goal)
  | .close r => match summarize b p.goal (p.alternatives r) with
      | none => true
      | some _ => false
  | .step r rest => match refine b p.goal (p.alternatives r) with
      | none => true
      | some b' => check p b' rest
  | .split i v left right => check p (leftBox b i v) left && check p (rightBox b i v) right

theorem check_sound {n k : ℕ} (p : Problem n k) (proof : Proof n k)
    (b : Box n) (hcheck : check p b proof = true) :
    ∀ x, b.Contains x → ¬ p.Admissible x := by
  induction proof generalizing b with
  | mass =>
    intro x hx hp
    have hl := mass_mono Finset.univ (fun i _ => (hx i).1)
    have hu := mass_mono Finset.univ (fun i _ => (hx i).2)
    have ht := hp.1
    simp only [check, decide_eq_true_eq] at hcheck
    omega
  | close r =>
    intro x hx hp
    obtain ⟨c, hc, hcx⟩ := hp.2 r
    obtain ⟨s, hs, _⟩ := summarize_covers b p.goal (p.alternatives r) hc
      (possible_of_holds hx hcx hp.1)
    simp [check, hs] at hcheck
  | step r rest ih =>
    intro x hx hp
    obtain ⟨b', hb', hx'⟩ := refine_sound hx hp.1 (p.alternatives r) (hp.2 r)
    exact ih b' (by simpa [check, hb'] using hcheck) x hx' hp
  | split i v left right ihl ihr =>
    intro x hx hp
    simp only [check, Bool.and_eq_true] at hcheck
    by_cases hv : x i ≤ v
    · exact ihl _ hcheck.1 x (contains_left hx i v hv) hp
    · exact ihr _ hcheck.2 x (contains_right hx i v (by omega)) hp
end FiveColour.Certificate.Fast
