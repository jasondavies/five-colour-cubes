module
public import FiveColour.PackedVerified
@[expose] public section
namespace FiveColour.Packed.Chunks

/-- A bounded piece of a certificate. `reuse` names a previously proved box;
`run` uses the existing checker for a complete subtree. -/
inductive Proof (n : Nat) where
  | run (proof : Certificate.Proof 75 78)
  | reuse (index : Fin n)
  | step (reason : Fin 78) (rest : Proof n)
  | split (index : Fin 75) (value : Int) (left right : Proof n)

/-- A reference is accepted only when both packed bounds agree exactly.
The soundness theorem separately requires a proof excluding each reference. -/
def check {n : Nat} (goal : Nat) (families : Fin 78 → List Cut)
    (references : Fin n → Box) (b : Box) : Proof n → Bool
  | .run proof => Verified.check goal families b proof
  | .reuse i => b.lower == (references i).lower && b.upper == (references i).upper
  | .step r rest => match summarize b goal (families r) with
      | none => true
      | some s => check goal families references (applySummary b s) rest
  | .split i v left right =>
    if 0 ≤ v && v < 7 then
      check goal families references { b with upper := replaceDigit b.upper i.val v.toNat } left &&
      check goal families references { b with lower := replaceDigit b.lower i.val (v+1).toNat } right
    else false

def Excludes (goal : Nat) (families : Fin 78 → List Cut) (b : Box) : Prop :=
  ∀ x, b.model.Contains x → ¬ (Verified.problem goal families).Admissible x

/-- Chunk composition has no oracle: every referenced exclusion is supplied
as a Lean proof. Exact boundary checks prevent mismatched checkpoints. -/
theorem check_sound {n : Nat} (goal : Nat) (families : Fin 78 → List Cut)
    (hf : ∀ r, ∀ c ∈ families r, c.Valid) (references : Fin n → Box)
    (hrefs : ∀ i, Excludes goal families (references i)) (proof : Proof n)
    (b : Box) (hb : b.Valid) (hcheck : check goal families references b proof = true) :
    Excludes goal families b := by
  induction proof generalizing b with
  | run proof => exact Verified.check_sound goal families hf proof b hb hcheck
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
end FiveColour.Packed.Chunks
