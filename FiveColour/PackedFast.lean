module
public import FiveColour.PackedChunks
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FiveColour.Packed.Fast

/- Compute digit places directly. The equalities below transfer the unchanged
   checker soundness theorem; no arithmetic result is assumed or trusted. -/

theorem place_eq : ∀ i : Fin 75, (1024 : Nat)^i.val = Packed.place i.val := by
  decide +kernel

def digit (v : Nat) (i : Fin 75) : Nat := v / (1024^i.val) % 1024
lemma digit_eq (v : Nat) (i : Fin 75) : digit v i = Packed.digit v i.val := by
  simp only [digit, place_eq, Packed.digit, base]

def encode (f : Fin 75 → Nat) : Nat :=
  (List.finRange 75).foldl (fun acc i => acc + f i * (1024^i.val)) 0
lemma encode_eq (f : Fin 75 → Nat) : encode f = Packed.encode f := by
  simp only [encode, Packed.encode, place_eq]

def applySummary (b : Box) (s : Summary) : Box where
  lower := encode fun i =>
    let l := digit b.lower i
    if s.united.testBit i.val then l else max l (digit b.upper i - s.gap)
  upper := encode fun i =>
    let h := digit b.upper i
    if s.common.testBit i.val then min h (digit b.lower i + s.slack) else h
lemma applySummary_eq (b : Box) (s : Summary) : applySummary b s = Packed.applySummary b s := by
  simp only [applySummary, encode_eq, digit_eq, Packed.applySummary]

def replaceDigit (v : Nat) (i : Fin 75) (value : Nat) : Nat :=
  v - digit v i * (1024^i.val) + value * (1024^i.val)
lemma replaceDigit_eq (v : Nat) (i : Fin 75) (a : Nat) :
    replaceDigit v i a = Packed.replaceDigit v i.val a := by
  simp only [replaceDigit, digit_eq, place_eq, Packed.replaceDigit]

def run (goal : Nat) (families : Fin 78 → List Cut) (b : Box) : Certificate.Proof 75 78 → Bool
  | .mass => goal < total b.lower || total b.upper < goal
  | .close r => (summarize b goal (families r)).isNone
  | .step r rest => match summarize b goal (families r) with
      | none => true
      | some s => run goal families (applySummary b s) rest
  | .split i v left right =>
    if 0 ≤ v && v < 7 then
      run goal families { b with upper := replaceDigit b.upper i v.toNat } left &&
      run goal families { b with lower := replaceDigit b.lower i (v+1).toNat } right
    else false

theorem run_eq (goal : Nat) (families : Fin 78 → List Cut) (b : Box)
    (proof : Certificate.Proof 75 78) : run goal families b proof = Verified.check goal families b proof := by
  induction proof generalizing b with
  | mass => rfl
  | close r => rfl
  | step r rest ih =>
    simp only [run, Verified.check]
    split <;> simp_all only [applySummary_eq]
  | split i v left right ihl ihr =>
    simp only [run, Verified.check, replaceDigit_eq]
    split <;> simp_all

def check {n : Nat} (goal : Nat) (families : Fin 78 → List Cut)
    (references : Fin n → Box) (b : Box) : Chunks.Proof n → Bool
  | .run proof => run goal families b proof
  | .reuse i => b.lower == (references i).lower && b.upper == (references i).upper
  | .step r rest => match summarize b goal (families r) with
      | none => true
      | some s => check goal families references (applySummary b s) rest
  | .split i v left right =>
    if 0 ≤ v && v < 7 then
      check goal families references { b with upper := replaceDigit b.upper i v.toNat } left &&
      check goal families references { b with lower := replaceDigit b.lower i (v+1).toNat } right
    else false

theorem check_eq {n : Nat} (goal : Nat) (families : Fin 78 → List Cut)
    (references : Fin n → Box) (b : Box) (proof : Chunks.Proof n) :
    check goal families references b proof = Chunks.check goal families references b proof := by
  induction proof generalizing b with
  | run proof => exact run_eq _ _ _ _
  | reuse i => rfl
  | step r rest ih =>
    simp only [check, Chunks.check]
    split <;> simp_all only [applySummary_eq]
  | split i v left right ihl ihr =>
    simp only [check, Chunks.check, replaceDigit_eq]
    split <;> simp_all

theorem check_sound {n : Nat} (goal : Nat) (families : Fin 78 → List Cut)
    (hf : ∀ r, ∀ c ∈ families r, c.Valid) (references : Fin n → Box)
    (hrefs : ∀ i, Chunks.Excludes goal families (references i)) (proof : Chunks.Proof n)
    (b : Box) (hb : b.Valid) (hcheck : check goal families references b proof = true) :
    Chunks.Excludes goal families b := by
  apply Chunks.check_sound goal families hf references hrefs proof b hb
  rwa [← check_eq]
end FiveColour.Packed.Fast
