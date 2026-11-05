module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A generic, kernel-checked basis for Hall interval certificates.
This file does not yet assert the five-colour threshold. -/
@[expose] public section

namespace FiveColour.Certificate
open scoped BigOperators

abbrev Vector (n : ℕ) := Fin n → ℤ

def mass {n : ℕ} (x : Vector n) (s : Finset (Fin n)) : ℤ := ∑ i ∈ s, x i

structure Box (n : ℕ) where
  lower : Vector n
  upper : Vector n

def Box.Contains {n : ℕ} (b : Box n) (x : Vector n) : Prop :=
  ∀ i, b.lower i ≤ x i ∧ x i ≤ b.upper i

structure Cut (n : ℕ) where
  neighbours : Finset (Fin n)
  rhs : ℤ

def Cut.Holds {n : ℕ} (c : Cut n) (x : Vector n) : Prop := mass x c.neighbours ≤ c.rhs

lemma mass_mono {n : ℕ} {x y : Vector n} (s : Finset (Fin n))
    (h : ∀ i ∈ s, x i ≤ y i) : mass x s ≤ mass y s :=
  Finset.sum_le_sum h

lemma mass_complement {n : ℕ} (x : Vector n) (s : Finset (Fin n)) :
    mass x s + mass x sᶜ = mass x Finset.univ := by
  exact Finset.sum_add_sum_compl s x

lemma coordinate_bound {n : ℕ} {b : Box n} {x : Vector n}
    (hx : b.Contains x) {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    mass b.lower s - b.lower i + x i ≤ mass x s ∧
    mass x s ≤ mass b.upper s - b.upper i + x i := by
  have hlo := mass_mono (s.erase i) (fun j _ => (hx j).1)
  have hhi := mass_mono (s.erase i) (fun j _ => (hx j).2)
  have erase (v : Vector n) : mass v (s.erase i) + v i = mass v s := by
    exact Finset.sum_erase_add _ _ hi
  have := erase b.lower
  have := erase b.upper
  have := erase x
  omega

/-- A Hall cut is feasible in a box only if both these necessary bounds hold. -/
def Cut.Possible {n : ℕ} (c : Cut n) (b : Box n) (goal : ℤ) : Prop :=
  mass b.lower c.neighbours ≤ c.rhs ∧
    goal ≤ c.rhs + mass b.upper c.neighboursᶜ

instance {n : ℕ} (c : Cut n) (b : Box n) (goal : ℤ) :
    Decidable (c.Possible b goal) := inferInstanceAs (Decidable (_ ∧ _))

lemma possible_of_holds {n : ℕ} {b : Box n} {x : Vector n} {c : Cut n}
    (hx : b.Contains x) (hc : c.Holds x) {goal : ℤ}
    (ht : mass x Finset.univ = goal) : c.Possible b goal := by
  have hl := mass_mono c.neighbours (fun i _ => (hx i).1)
  have hu := mass_mono c.neighboursᶜ (fun i _ => (hx i).2)
  have hsum := mass_complement x c.neighbours
  unfold Cut.Holds at hc
  constructor <;> omega

/-- Tighten one box assuming a particular Hall deficiency. -/
def cutBox {n : ℕ} (b : Box n) (goal : ℤ) (c : Cut n) : Box n where
  lower i := if i ∈ c.neighbours then b.lower i else
    max (b.lower i) (goal - c.rhs - mass b.upper c.neighboursᶜ + b.upper i)
  upper i := if i ∈ c.neighbours then
    min (b.upper i) (c.rhs - mass b.lower c.neighbours + b.lower i) else b.upper i

lemma cutBox_contains {n : ℕ} {b : Box n} {x : Vector n} {c : Cut n}
    (hx : b.Contains x) (hc : c.Holds x) {goal : ℤ}
    (ht : mass x Finset.univ = goal) : (cutBox b goal c).Contains x := by
  intro i
  have hxi := hx i
  have hsum := mass_complement x c.neighbours
  unfold Cut.Holds at hc
  by_cases hi : i ∈ c.neighbours
  · have hcoord := (coordinate_bound hx hi).1
    simpa only [cutBox, ite_eq_left hi, le_min_iff] using
      (show b.lower i ≤ x i ∧ x i ≤ b.upper i ∧
        x i ≤ c.rhs - mass b.lower c.neighbours + b.lower i from ⟨hxi.1, hxi.2, by omega⟩)
  · have hic : i ∈ c.neighboursᶜ := Finset.mem_compl.mpr hi
    have hcoord := (coordinate_bound hx hic).2
    simp only [cutBox, ite_eq_right hi, max_le_iff]
    exact ⟨⟨hxi.1, by omega⟩, hxi.2⟩

/-- The smallest coordinate box containing two boxes. -/
def hull {n : ℕ} (a b : Box n) : Box n where
  lower i := min (a.lower i) (b.lower i)
  upper i := max (a.upper i) (b.upper i)

lemma hull_contains_left {n : ℕ} {a b : Box n} {x : Vector n}
    (hx : a.Contains x) : (hull a b).Contains x := by
  intro i
  exact ⟨(min_le_left _ _).trans (hx i).1, (hx i).2.trans (le_max_left _ _)⟩

lemma hull_contains_right {n : ℕ} {a b : Box n} {x : Vector n}
    (hx : b.Contains x) : (hull a b).Contains x := by
  intro i
  exact ⟨(min_le_right _ _).trans (hx i).1, (hx i).2.trans (le_max_right _ _)⟩

/-- Discard infeasible cuts and take the hull of the remaining cut boxes.
`none` means that every Hall deficiency has been excluded. -/
def refine {n : ℕ} (b : Box n) (goal : ℤ) : List (Cut n) → Option (Box n)
  | [] => none
  | c :: cs =>
    let rest := refine b goal cs
    if c.Possible b goal then
      some (match rest with | none => cutBox b goal c | some d => hull (cutBox b goal c) d)
    else rest

/-- Refinement preserves every assignment satisfying one of the listed cuts. -/
theorem refine_sound {n : ℕ} {b : Box n} {x : Vector n} {goal : ℤ}
    (hx : b.Contains x) (ht : mass x Finset.univ = goal) (cs : List (Cut n))
    (hc : ∃ c ∈ cs, c.Holds x) :
    ∃ b', refine b goal cs = some b' ∧ b'.Contains x := by
  induction cs with
  | nil => simp at hc
  | cons c cs ih =>
    simp only [List.mem_cons] at hc
    by_cases hp : c.Possible b goal
    · obtain ⟨d, hd, hdx⟩ := hc
      rcases hd with rfl | hd
      · have hcb := cutBox_contains hx hdx ht
        cases hr : refine b goal cs with
        | none => exact ⟨_, by simp [refine, hp, hr], hcb⟩
        | some b' => exact ⟨hull (cutBox b goal d) b', by simp [refine, hp, hr], hull_contains_left hcb⟩
      · obtain ⟨b', hb', hbx⟩ := ih ⟨d, hd, hdx⟩
        exact ⟨hull (cutBox b goal c) b', by simp [refine, hp, hb'], hull_contains_right hbx⟩
    · have hrest : ∃ d ∈ cs, d.Holds x := by
        obtain ⟨d, hd, hdx⟩ := hc
        rcases hd with rfl | hd
        · exact False.elim (hp (possible_of_holds hx hdx ht))
        · exact ⟨d, hd, hdx⟩
      obtain ⟨b', hb', hbx⟩ := ih hrest
      exact ⟨b', by simp [refine, hp, hb'], hbx⟩

/-- A counterexample must have the prescribed total and satisfy a Hall
 deficiency in each family (one family per target, plus any root constraints). -/
structure Problem (n k : ℕ) where
  goal : ℤ
  alternatives : Fin k → List (Cut n)

def Problem.Admissible {n k : ℕ} (p : Problem n k) (x : Vector n) : Prop :=
  mass x Finset.univ = p.goal ∧
    ∀ r, ∃ c ∈ p.alternatives r, c.Holds x

/-- Only branch choices and refinement families are supplied by the search. -/
inductive Proof (n k : ℕ) where
  | mass
  | close (reason : Fin k)
  | step (reason : Fin k) (rest : Proof n k)
  | split (i : Fin n) (value : ℤ) (left right : Proof n k)

def leftBox {n : ℕ} (b : Box n) (i : Fin n) (v : ℤ) : Box n :=
  { b with upper := Function.update b.upper i v }

def rightBox {n : ℕ} (b : Box n) (i : Fin n) (v : ℤ) : Box n :=
  { b with lower := Function.update b.lower i (v+1) }

lemma contains_left {n : ℕ} {b : Box n} {x : Vector n} (hx : b.Contains x)
    (i : Fin n) (v : ℤ) (hv : x i ≤ v) : (leftBox b i v).Contains x := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa [leftBox] using And.intro (hx i).1 hv
  · simpa [leftBox, Function.update_of_ne hj] using hx j

lemma contains_right {n : ℕ} {b : Box n} {x : Vector n} (hx : b.Contains x)
    (i : Fin n) (v : ℤ) (hv : v < x i) : (rightBox b i v).Contains x := by
  intro j
  by_cases hj : j = i
  · subst j
    have h : v+1 ≤ x i := by omega
    simpa [rightBox] using And.intro h (hx i).2
  · simpa [rightBox, Function.update_of_ne hj] using hx j

/-- A small executable reference checker; no external solver is trusted. -/
def check {n k : ℕ} (p : Problem n k) (b : Box n) : Proof n k → Bool
  | .mass => decide (p.goal < mass b.lower Finset.univ ∨ mass b.upper Finset.univ < p.goal)
  | .close r => match refine b p.goal (p.alternatives r) with
      | none => true
      | some _ => false
  | .step r rest => match refine b p.goal (p.alternatives r) with
      | none => true
      | some b' => check p b' rest
  | .split i v left right => check p (leftBox b i v) left && check p (rightBox b i v) right

/-- Every certificate accepted by `check` excludes every admissible assignment
in its root box, independently of how the certificate was found. -/
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
    obtain ⟨b', hb', _⟩ := refine_sound hx hp.1 (p.alternatives r) (hp.2 r)
    simp [check, hb'] at hcheck
  | step r rest ih =>
    intro x hx hp
    obtain ⟨b', hb', hx'⟩ := refine_sound hx hp.1 (p.alternatives r) (hp.2 r)
    have hc : check p b' rest = true := by simpa [check, hb'] using hcheck
    exact ih b' hc x hx' hp
  | split i v left right ihl ihr =>
    intro x hx hp
    simp only [check, Bool.and_eq_true] at hcheck
    by_cases hv : x i ≤ v
    · exact ihl _ hcheck.1 x (contains_left hx i v hv) hp
    · exact ihr _ hcheck.2 x (contains_right hx i v (by omega)) hp

end FiveColour.Certificate
