module
public import FiveColour.PackedSemantics
@[expose] public section
set_option maxRecDepth 2000
namespace FiveColour.Packed
open scoped BigOperators

lemma summary_ext (s t : Certificate.Fast.Summary 75)
    (h1 : s.common = t.common) (h2 : s.united = t.united)
    (h3 : s.slack = t.slack) (h4 : s.need = t.need) : s = t := by
  cases s; cases t; simp_all

lemma box_ext (s t : Certificate.Box 75)
    (h1 : s.lower = t.lower) (h2 : s.upper = t.upper) : s = t := by
  cases s; cases t; simp_all

/-- The meaning of the bit masks and the two safe relaxation amounts. -/
def Summary.model (s : Summary) : Certificate.Fast.Summary 75 where
  common := Finset.univ.filter (fun i => s.common.testBit i.val = true)
  united := Finset.univ.filter (fun i => s.united.testBit i.val = true)
  slack := s.slack
  need := -(s.gap : Int)

def singleton (b : Box) (goal : Nat) (c : Cut) : Summary :=
  ⟨c.mask, c.mask, c.rhs - mass b.lower c, c.rhs + (total b.upper - mass b.upper c) - goal⟩

def merge (s t : Summary) : Summary :=
  ⟨s.common &&& t.common, s.united ||| t.united, max s.slack t.slack, max s.gap t.gap⟩

def accumulate (b : Box) (goal : Nat) (state : Option Summary) (c : Cut) : Option Summary :=
  if mass b.lower c ≤ c.rhs && goal ≤ c.rhs + (total b.upper - mass b.upper c) then
    some (match state with | none => singleton b goal c | some t => merge t (singleton b goal c))
  else state

lemma summarize_eq (b : Box) (goal : Nat) (cs : List Cut) :
    summarize b goal cs = cs.foldl (accumulate b goal) none := rfl

lemma merge_model (s t : Summary) :
    (merge s t).model = Certificate.Fast.merge s.model t.model := by
  apply summary_ext
  · ext i
    simp [Summary.model, merge, Certificate.Fast.merge]
  · ext i
    simp [Summary.model, merge, Certificate.Fast.merge]
  · change ((max s.slack t.slack : Nat) : Int) = max (s.slack : Int) (t.slack : Int)
    omega
  · change -((max s.gap t.gap : Nat) : Int) = min (-(s.gap : Int)) (-(t.gap : Int))
    omega

lemma singleton_covers (b : Box) (hb : b.Valid) (goal : Nat) (c : Cut)
    (hc : c.Valid) (hp : possible b goal c) :
    Certificate.Fast.Covers b.model goal (singleton b goal c).model c.model := by
  have hl := mass_eq b.lower hb.1 c hc
  have ho := outside_eq b.upper hb.2 c hc
  have h1 := hp.1
  have h2 := hp.2
  refine ⟨Finset.Subset.refl _, Finset.Subset.refl _, ?_, ?_⟩
  · change (c.rhs : Int) - Certificate.mass (vectorModel b.lower) c.model.neighbours ≤
      (c.rhs - mass b.lower c : Nat)
    rw [← hl, Int.natCast_sub h1]
  · change -((c.rhs + (total b.upper - mass b.upper c) - goal : Nat) : Int) ≤
      (goal : Int) - c.rhs - Certificate.mass (vectorModel b.upper) c.model.neighboursᶜ
    rw [← ho, Int.natCast_sub h2, Nat.cast_add]
    omega

lemma accumulate_keeps {b : Box} {goal : Nat} {s : Summary} {c d : Cut}
    (hs : Certificate.Fast.Covers b.model goal s.model c.model) :
    ∃ t, accumulate b goal (some s) d = some t ∧
      Certificate.Fast.Covers b.model goal t.model c.model := by
  unfold accumulate
  split
  · exact ⟨_, rfl, by rw [merge_model]; exact Certificate.Fast.merge_covers_left hs⟩
  · exact ⟨s, rfl, hs⟩

lemma fold_keeps {b : Box} {goal : Nat} {s : Summary} {c : Cut}
    (cs : List Cut) (hs : Certificate.Fast.Covers b.model goal s.model c.model) :
    ∃ t, cs.foldl (accumulate b goal) (some s) = some t ∧
      Certificate.Fast.Covers b.model goal t.model c.model := by
  induction cs generalizing s with
  | nil => exact ⟨s, rfl, hs⟩
  | cons d ds ih =>
    obtain ⟨t, ht, htc⟩ := accumulate_keeps (d := d) hs
    obtain ⟨u, hu, huc⟩ := ih htc
    exact ⟨u, by simpa only [List.foldl_cons, ht] using hu, huc⟩

/-- Every feasible cut is covered by the packed summary. -/
theorem summarize_covers (b : Box) (hb : b.Valid) (goal : Nat) (cs : List Cut)
    {c : Cut} (hc : c ∈ cs) (hv : c.Valid) (hp : possible b goal c) :
    ∃ s, summarize b goal cs = some s ∧
      Certificate.Fast.Covers b.model goal s.model c.model := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hc
  have hs := singleton_covers b hb goal c hv hp
  have ha (state : Option Summary) : ∃ s, accumulate b goal state c = some s ∧
      Certificate.Fast.Covers b.model goal s.model c.model := by
    cases state with
    | none => exact ⟨_, by simp [accumulate, hp.1, hp.2], hs⟩
    | some t => exact ⟨merge t (singleton b goal c), by simp [accumulate, hp.1, hp.2],
        by rw [merge_model]; exact Certificate.Fast.merge_covers_right hs⟩
  obtain ⟨s, he, hsc⟩ := ha (before.foldl (accumulate b goal) none)
  obtain ⟨t, ht, htc⟩ := fold_keeps after hsc
  exact ⟨t, by simpa only [summarize_eq, List.foldl_append, List.foldl_cons, he] using ht, htc⟩

lemma applySummary_valid (b : Box) (hb : b.Valid) (s : Summary) :
    (applySummary b s).Valid := by
  dsimp only [Box.Valid, applySummary]
  constructor
  · apply valid_encode
    intro i
    have hl := hb.1.2 i
    have hu := hb.2.2 i
    change digit b.lower i.val ≤ 7 at hl
    change digit b.upper i.val ≤ 7 at hu
    split <;> omega
  · apply valid_encode
    intro i
    have hu := hb.2.2 i
    change digit b.upper i.val ≤ 7 at hu
    split <;> omega

lemma applySummary_model (b : Box) (hb : b.Valid) (s : Summary) :
    (applySummary b s).model = Certificate.Fast.applySummary b.model s.model := by
  have hvalid := applySummary_valid b hb s
  have decodelow (i : Fin 75) := pack_digit
    (fun j : Fin 75 => if s.united.testBit j.val then digit b.lower j.val
      else max (digit b.lower j.val) (digit b.upper j.val - s.gap))
    (by intro j; have hl := hb.1.2 j; have hu := hb.2.2 j
        change digit b.lower j.val ≤ 7 at hl
        change digit b.upper j.val ≤ 7 at hu
        split <;> omega) i
  have decodehigh (i : Fin 75) := pack_digit
    (fun j : Fin 75 => if s.common.testBit j.val then
      min (digit b.upper j.val) (digit b.lower j.val + s.slack) else digit b.upper j.val)
    (by intro j; have hu := hb.2.2 j
        change digit b.upper j.val ≤ 7 at hu
        split <;> omega) i
  apply box_ext
  · funext i
    change (digit (applySummary b s).lower i.val : Int) = _
    dsimp only [applySummary]
    rw [encode_eq_pack, decodelow]
    simp only [Certificate.Fast.applySummary, Summary.model, Finset.mem_filter,
      Finset.mem_univ, true_and, Box.model, vectorModel, values]
    split <;> omega
  · funext i
    change (digit (applySummary b s).upper i.val : Int) = _
    dsimp only [applySummary]
    rw [encode_eq_pack, decodehigh]
    simp only [Certificate.Fast.applySummary, Summary.model, Finset.mem_filter,
      Finset.mem_univ, true_and, Box.model, vectorModel, values]
    split <;> omega
namespace Verified

/-- Only bounded split values are accepted, so packed digits never overflow. -/
def check (goal : Nat) (families : Fin 78 → List Cut) (b : Box) : Certificate.Proof 75 78 → Bool
  | .mass => goal < total b.lower || total b.upper < goal
  | .close r => (summarize b goal (families r)).isNone
  | .step r rest => match summarize b goal (families r) with
      | none => true
      | some s => check goal families (applySummary b s) rest
  | .split i v left right =>
    if 0 ≤ v && v < 7 then
      check goal families { b with upper := replaceDigit b.upper i.val v.toNat } left &&
      check goal families { b with lower := replaceDigit b.lower i.val (v+1).toNat } right
    else false

def problem (goal : Nat) (families : Fin 78 → List Cut) : Certificate.Problem 75 78 where
  goal := goal
  alternatives r := (families r).map Cut.model

/-- Accepted packed certificates exclude every admissible integer collection
in their initial box. This theorem uses only the reference interval lemmas
and the proved base-1024 arithmetic bridge. -/
theorem check_sound (goal : Nat) (families : Fin 78 → List Cut)
    (hf : ∀ r, ∀ c ∈ families r, c.Valid) (proof : Certificate.Proof 75 78)
    (b : Box) (hb : b.Valid) (hcheck : check goal families b proof = true) :
    ∀ x, b.model.Contains x → ¬ (problem goal families).Admissible x := by
  induction proof generalizing b with
  | mass =>
    intro x hx hp
    have hl := Certificate.mass_mono Finset.univ (fun i _ => (hx i).1)
    have hu := Certificate.mass_mono Finset.univ (fun i _ => (hx i).2)
    have ht := hp.1
    have hlo := total_eq b.lower hb.1
    have hup := total_eq b.upper hb.2
    change Certificate.mass x Finset.univ = (goal : Int) at ht
    change Certificate.mass (vectorModel b.lower) Finset.univ ≤ _ at hl
    change _ ≤ Certificate.mass (vectorModel b.upper) Finset.univ at hu
    simp only [check, Bool.or_eq_true, decide_eq_true_eq] at hcheck
    omega
  | close r =>
    intro x hx hp
    obtain ⟨d, hd, hdx⟩ := hp.2 r
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    have hpossible := Certificate.possible_of_holds hx hdx hp.1
    have hp' : possible b goal c := (possible_iff b hb goal c (hf r c hc)).mpr hpossible
    obtain ⟨s, hs, _⟩ := summarize_covers b hb goal (families r) hc (hf r c hc) hp'
    simp only [check, hs, Option.isNone_some, Bool.false_eq_true] at hcheck
  | step r rest ih =>
    intro x hx hp
    obtain ⟨d, hd, hdx⟩ := hp.2 r
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    have hpossible := Certificate.possible_of_holds hx hdx hp.1
    have hp' : possible b goal c := (possible_iff b hb goal c (hf r c hc)).mpr hpossible
    obtain ⟨s, hs, hsc⟩ := summarize_covers b hb goal (families r) hc (hf r c hc) hp'
    have hx' := Certificate.Fast.applySummary_contains hx hp.1 hdx hsc
    rw [← applySummary_model b hb s] at hx'
    exact ih _ (applySummary_valid b hb s) (by simpa only [check, hs] using hcheck) x hx' hp
  | split i v left right ihl ihr =>
    intro x hx hp
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    split at hcheck
    next hv =>
      simp only [Bool.and_eq_true] at hcheck
      obtain ⟨hl, hr⟩ := hcheck
      have hv0 : 0 ≤ v := hv.1
      have hva : v.toNat ≤ 7 := by omega
      have hvb : (v+1).toNat ≤ 7 := by omega
      have hva' : (v.toNat : Int) = v := Int.toNat_of_nonneg hv0
      have hvb' : ((v+1).toNat : Int) = v+1 := Int.toNat_of_nonneg (by omega)
      by_cases hxi : x i ≤ v
      · apply ihl { b with upper := replaceDigit b.upper i.val v.toNat } ⟨hb.1, replaceDigit_valid b.upper hb.2 i v.toNat hva⟩ hl x ?_ hp
        intro j
        change vectorModel b.lower j ≤ x j ∧ x j ≤ vectorModel (replaceDigit b.upper i.val v.toNat) j
        rw [replaceDigit_model b.upper hb.2 i v.toNat hva]
        by_cases hji : j = i
        · subst j; simpa only [Function.update_self, hva'] using ⟨(hx i).1, hxi⟩
        · simpa only [Function.update_of_ne hji, Box.model] using hx j
      · apply ihr { b with lower := replaceDigit b.lower i.val (v+1).toNat } ⟨replaceDigit_valid b.lower hb.1 i (v+1).toNat hvb, hb.2⟩ hr x ?_ hp
        intro j
        change vectorModel (replaceDigit b.lower i.val (v+1).toNat) j ≤ x j ∧ x j ≤ vectorModel b.upper j
        rw [replaceDigit_model b.lower hb.1 i (v+1).toNat hvb]
        by_cases hji : j = i
        · subst j; simpa only [Function.update_self, hvb'] using ⟨show v+1 ≤ x i by omega, (hx i).2⟩
        · simpa only [Function.update_of_ne hji, Box.model] using hx j
    next => contradiction
end Verified
end FiveColour.Packed
