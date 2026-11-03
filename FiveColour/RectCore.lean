module
public import FiveColour.BoxGeometry
public import FiveColour.BoxMatching
@[expose] public section
namespace FiveColour.Physical

def RectCorePosition (t : Cube) {l : Fin 3 → ℕ} : RectSlot l → Prop
  | .inl _ => True
  | .inr p => t (edgeFaces p.1 0) = t (edgeFaces p.1 1)
instance (t : Cube) (l : Fin 3 → ℕ) : DecidablePred (@RectCorePosition t l) := by
  intro p; cases p <;> unfold RectCorePosition <;> infer_instance

lemma rect_core_of_uniform {n q : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube) (t : Fin 75)
    (hl : ∀ e, catalogue t (edgeFaces e 0) = catalogue t (edgeFaces e 1) → l (edgeAxis e) = q)
    (f : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ Fin n)
    (hf : ∀ p, FrameFits (cubes (f p)) (catalogue t) p.val) :
    ∃ g : {p : RectSlot l // RectCorePosition (catalogue t) p} ↪ Fin n,
      ∀ p, RectFits (cubes (g p)) (catalogue t) p.val := by
  let lift : {p : RectSlot l // RectCorePosition (catalogue t) p} →
      {p : FrameSlot q // CorePosition (catalogue t) p} := fun p => match p with
    | ⟨.inl k,h⟩ => ⟨.inl k,h⟩
    | ⟨.inr ⟨e,j⟩,h⟩ => ⟨.inr (e,Fin.cast (hl e h) j),h⟩
  have hinj : Function.Injective lift := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Sum.inl.inj he')
      | inr b => cases he'
    | inr a => cases b with
      | inl b => cases he'
      | inr b =>
        have hp := Sum.inr.inj he'
        have heq := congrArg Prod.fst hp
        rcases a with ⟨a,j⟩; rcases b with ⟨b,k⟩
        change a=b at heq
        subst b
        have hj := congrArg (fun p : Fin 12 × Fin q => p.2.val) hp
        have hj' : j=k := Fin.ext hj
        subst k; rfl
  refine ⟨(⟨lift,hinj⟩ : _ ↪ _).trans f,?_⟩
  rintro ⟨p,hp⟩
  cases p with
  | inl k => exact hf (lift ⟨.inl k,hp⟩)
  | inr p => exact hf (lift ⟨.inr p,hp⟩)

lemma shortest_mono_length (t : Fin 75) (z : Fin 3)
    (hz : ∀ a, a ≠ z → BichromaticAxis (catalogue t) a) (m u v : ℕ) :
    ∀ e, catalogue t (edgeFaces e 0) = catalogue t (edgeFaces e 1) →
      ![m,u,v] (Equiv.swap (0 : Fin 3) z (edgeAxis e)) = m := by
  intro e he
  have haxis : edgeAxis e=z := by by_contra hn; exact hz _ hn e rfl he
  rw [(swap_zero z _).mpr haxis]
  rfl

lemma rect_from_core {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube) (t : Fin 75) (d : ℕ)
    (hn : Fintype.card (RectSlot l) ≤ n)
    (hmiss : ∀ i, (Finset.univ.filter fun pos : RectSlot l => ¬ RectFits (cubes i) (catalogue t) pos).card ≤ d)
    (core : {p : RectSlot l // RectCorePosition (catalogue t) p} ↪ Fin n)
    (hcore : ∀ p, RectFits (cubes (core p)) (catalogue t) p.val)
    (hedges : ∀ e, catalogue t (edgeFaces e 0) ≠ catalogue t (edgeFaces e 1) →
      d ≤ (Finset.univ.filter fun i => HasEdge (cubes i) (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card) :
    RectSolvable l cubes := by
  classical
  apply rect_of_match l cubes t
  apply FrameHall.match_of_partial _ d (RectCorePosition (catalogue t)) (by simpa using hn) hmiss core hcore
  intro p hp
  cases p with
  | inl k => exact False.elim (hp trivial)
  | inr e => exact hedges e.1 hp
end FiveColour.Physical
