module
public import FiveColour.PackedPruning
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace FiveColour.Packed.Enumeration

/-- A bounded piece of a certificate. `reuse` names a previously proved box;
`run` uses the existing exclusion checker for a complete subtree. -/
inductive Proof (n : Nat) where
  | run (proof : Certificate.Proof 75 78)
  | point
  | reuse (index : Fin n)
  | step (reason : Fin 78) (rest : Proof n)
  | split (index : Fin 75) (value : Int) (left right : Proof n)

/-- A reference is accepted only when both packed bounds agree exactly.
The soundness theorem requires a coverage proof for each reference. -/
def check {n : Nat} (points : List Nat) (goal : Nat) (families : Fin 78 → List Cut)
    (references : Fin n → Box) (b : Box) : Proof n → Bool
  | .run proof => Verified.check goal families b proof
  | .point => b.lower == b.upper && points.contains b.lower
  | .reuse i => b.lower == (references i).lower && b.upper == (references i).upper
  | .step r rest => match summarize b goal (families r) with
      | none => true
      | some s => check points goal families references (applySummary b s) rest
  | .split i v left right =>
    if 0 ≤ v && v < 7 then
      check points goal families references { b with upper := replaceDigit b.upper i.val v.toNat } left &&
      check points goal families references { b with lower := replaceDigit b.lower i.val (v+1).toNat } right
    else false

def Covers (points : List Nat) (goal : Nat) (families : Fin 78 → List Cut) (b : Box) : Prop :=
  ∀ x, b.model.Contains x → (Verified.problem goal families).Admissible x →
    ∃ p ∈ points, x = vectorModel p

/-- Every admissible vector is in the explicit allowed list. Point leaves
require exact singleton bounds; every other step reuses the verified interval rules. -/
theorem check_sound {n : Nat} (points : List Nat) (goal : Nat) (families : Fin 78 → List Cut)
    (hf : ∀ r, ∀ c ∈ families r, c.Valid) (references : Fin n → Box)
    (hrefs : ∀ i, Covers points goal families (references i)) (proof : Proof n)
    (b : Box) (hb : b.Valid) (hcheck : check points goal families references b proof = true) :
    Covers points goal families b := by
  induction proof generalizing b with
  | run proof =>
    intro x hx hp
    exact False.elim (Verified.check_sound goal families hf proof b hb hcheck x hx hp)
  | point =>
    intro x hx _
    have he : b.lower = b.upper ∧ b.lower ∈ points := by simpa [check] using hcheck
    refine ⟨b.lower, he.2, ?_⟩
    funext i
    have hl : vectorModel b.lower i ≤ x i := (hx i).1
    have hu : x i ≤ vectorModel b.upper i := (hx i).2
    rw [← he.1] at hu
    exact le_antisymm hu hl
  | reuse i =>
    have he : b = references i := by
      simp only [check, Bool.and_eq_true, beq_iff_eq] at hcheck
      have ext (a d : Box) (hl : a.lower = d.lower) (hu : a.upper = d.upper) : a = d := by
        cases a; cases d; simp_all
      exact ext b (references i) hcheck.1 hcheck.2
    rw [he]
    exact hrefs i
  | step r rest ih =>
    intro x hx hp
    obtain ⟨d, hd, hdx⟩ := hp.2 r
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    have hpossible := Certificate.possible_of_holds hx hdx hp.1
    have hp' := (possible_iff b hb goal c (hf r c hc)).mpr hpossible
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
      have hva : v.toNat ≤ 7 := by omega
      have hvb : (v+1).toNat ≤ 7 := by omega
      have hva' : (v.toNat : Int) = v := Int.toNat_of_nonneg hv.1
      have hvb' : ((v+1).toNat : Int) = v+1 := Int.toNat_of_nonneg (by omega)
      by_cases hxi : x i ≤ v
      · apply ihl { b with upper := replaceDigit b.upper i.val v.toNat }
          ⟨hb.1, replaceDigit_valid b.upper hb.2 i v.toNat hva⟩ hl x ?_ hp
        intro j
        change vectorModel b.lower j ≤ x j ∧ x j ≤ vectorModel (replaceDigit b.upper i.val v.toNat) j
        rw [replaceDigit_model b.upper hb.2 i v.toNat hva]
        by_cases hji : j = i
        · subst j; simpa only [Function.update_self, hva'] using ⟨(hx i).1, hxi⟩
        · simpa only [Function.update_of_ne hji, Box.model] using hx j
      · apply ihr { b with lower := replaceDigit b.lower i.val (v+1).toNat }
          ⟨replaceDigit_valid b.lower hb.1 i (v+1).toNat hvb, hb.2⟩ hr x ?_ hp
        intro j
        change vectorModel (replaceDigit b.lower i.val (v+1).toNat) j ≤ x j ∧ x j ≤ vectorModel b.upper j
        rw [replaceDigit_model b.lower hb.1 i (v+1).toNat hvb]
        by_cases hji : j = i
        · subst j; simpa only [Function.update_self, hvb'] using ⟨show v+1 ≤ x i by omega, (hx i).2⟩
        · simpa only [Function.update_of_ne hji, Box.model] using hx j
    next => contradiction
theorem covers_of_weakened (points : List Nat) (root : Box) (hr : root.Valid) (goal : Nat)
    (families reduced : Fin 78 → List Cut)
    (hf : ∀ r, ∀ c ∈ families r, c.Valid)
    (hd : ∀ r, ∀ c ∈ reduced r, c.Valid)
    (cover : ∀ r, ∀ c ∈ families r, possible root goal c →
      ∃ d ∈ reduced r, relaxes root c d = true)
    (excluded : Covers points goal reduced root) :
    Covers points goal families root := by
  intro x hx hp
  apply excluded x hx
  refine ⟨hp.1, ?_⟩
  intro r
  obtain ⟨e, he, hex⟩ := hp.2 r
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  have hp' := (possible_iff root hr goal c (hf r c hc)).mpr
    (Certificate.possible_of_holds hx hex hp.1)
  obtain ⟨d, hd', hrel⟩ := cover r c hc hp'
  exact ⟨d.model, List.mem_map.mpr ⟨d, hd', rfl⟩,
    relaxes_holds root hr c d (hf r c hc) (hd r d hd') hrel x hx hex⟩

end FiveColour.Packed.Enumeration
