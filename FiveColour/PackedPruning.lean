module
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed

/-- Test a Hall alternative once against the initial root. -/
def viable (root : Box) (goal : Nat) (c : Cut) : Bool :=
  decide (mass root.lower c ≤ c.rhs ∧
    goal ≤ c.rhs + (total root.upper - mass root.upper c))

lemma viable_iff (root : Box) (goal : Nat) (c : Cut) :
    viable root goal c = true ↔ possible root goal c := by
  simp [viable, possible]

/-- A cut may drop coordinates if their lower-bound contribution pays for
its smaller right-hand side. This implication is needed only at the root. -/
def relaxes (root : Box) (c d : Cut) : Bool :=
  (d.mask &&& c.mask == d.mask) &&
    decide (c.rhs + mass root.lower d ≤ d.rhs + mass root.lower c)

lemma relaxes_holds (root : Box) (hr : root.Valid) (c d : Cut)
    (hc : c.Valid) (hd : d.Valid) (h : relaxes root c d = true)
    (x : Certificate.Vector 75) (hx : root.model.Contains x)
    (hcx : c.model.Holds x) : d.model.Holds x := by
  simp only [relaxes, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hm : d.mask &&& c.mask = d.mask := h.1
  have hs : d.model.neighbours ⊆ c.model.neighbours := by
    intro i hi
    have hi' : d.mask.testBit i.val = true := (Finset.mem_filter.mp hi).2
    have he := congrArg (fun m : Nat => m.testBit i.val) hm
    rw [Nat.testBit_and, hi'] at he
    have hc' : c.mask.testBit i.val = true := by simpa using he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc'⟩
  have hmass := Certificate.mass_mono (c.model.neighbours \ d.model.neighbours)
    (fun i _ => (hx i).1)
  have sums (v : Certificate.Vector 75) :
      Certificate.mass v (c.model.neighbours \ d.model.neighbours) +
        Certificate.mass v d.model.neighbours = Certificate.mass v c.model.neighbours := by
    exact Finset.sum_sdiff hs
  change Certificate.mass (vectorModel root.lower) _ ≤ Certificate.mass x _ at hmass
  have hlow := sums (vectorModel root.lower)
  have hxs := sums x
  have hlc := mass_eq root.lower hr.1 c hc
  have hld := mass_eq root.lower hr.1 d hd
  have hn := h.2
  have hn' : (c.rhs : Int) + mass root.lower d ≤ d.rhs + mass root.lower c := by
    exact_mod_cast hn
  change Certificate.mass x d.model.neighbours ≤ (d.rhs : Int)
  change Certificate.mass x c.model.neighbours ≤ (c.rhs : Int) at hcx
  omega

/-- An untrusted index for each original alternative either points to a
weaker replacement or accompanies a cut impossible at the initial root. -/
def covers (root : Box) (goal : Nat) (ds : Array Cut) : List Cut → List Nat → Bool
  | [], [] => true
  | c :: cs, k :: ks =>
    ((!viable root goal c) ||
      (match ds[k]? with | some d => relaxes root c d | none => false)) &&
      covers root goal ds cs ks
  | _, _ => false

lemma covers_sound (root : Box) (goal : Nat) (ds : Array Cut)
    (cs : List Cut) (ks : List Nat) (h : covers root goal ds cs ks = true) :
    ∀ c ∈ cs, possible root goal c →
      ∃ d ∈ ds.toList, relaxes root c d = true := by
  induction cs generalizing ks with
  | nil => simp
  | cons c cs ih =>
    cases ks with
    | nil => simp [covers] at h
    | cons k ks =>
      simp only [covers, Bool.and_eq_true] at h
      intro e he hp
      rcases List.mem_cons.mp he with rfl | he
      · have hv := (viable_iff root goal e).mpr hp
        have hh' : (match ds[k]? with | some d => relaxes root e d | none => false) = true := by
          simpa [hv] using h.1
        cases hk : ds[k]? with
        | none => simp [hk] at hh'
        | some d =>
          exact ⟨d, (by simpa using Array.mem_of_getElem? hk), by simpa [hk] using hh'⟩
      · exact ih ks h.2 e he hp

/-- Excluding any root-wise weakening of the families excludes the original
problem. Intermediate split boxes need not lie inside the original root. -/
theorem excludes_of_covered (root : Box) (hr : root.Valid) (goal : Nat)
    (families reduced : Fin 78 → List Cut)
    (hf : ∀ r, ∀ c ∈ families r, c.Valid)
    (hd : ∀ r, ∀ c ∈ reduced r, c.Valid)
    (cover : ∀ r, ∀ c ∈ families r, possible root goal c →
      ∃ d ∈ reduced r, relaxes root c d = true)
    (excluded : Chunks.Excludes goal reduced root) :
    Chunks.Excludes goal families root := by
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

end FiveColour.Packed
