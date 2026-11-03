module
public import FiveColour.BoxAxes
public import FiveColour.SharpFrames
@[expose] public section
namespace FiveColour.Physical

def RectCorner {l : Fin 3 → ℕ} : RectSlot l → Prop
  | .inl _ => True
  | .inr _ => False
instance (l : Fin 3 → ℕ) : DecidablePred (@RectCorner l) := by
  intro p; cases p <;> unfold RectCorner <;> infer_instance

theorem rect_from_corners {n : ℕ} (l : Fin 3 → ℕ) (cubes : Fin n → Cube)
    (t : Fin 75) (d : ℕ) (hn : Fintype.card (RectSlot l) ≤ n)
    (hmiss : ∀ i, (Finset.univ.filter fun pos : RectSlot l => ¬ RectFits (cubes i) (catalogue t) pos).card ≤ d)
    (corners : Fin 8 ↪ Fin n) (hf : ∀ k, Fits (cubes (corners k)) (catalogue t) k)
    (hedges : ∀ e, 0 < l (edgeAxis e) →
      d ≤ (Finset.univ.filter fun i => HasEdge (cubes i) (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card) :
    RectSolvable l cubes := by
  classical
  let corner : {p : RectSlot l // RectCorner p} → Fin 8 := fun p => match p with
    | ⟨.inl k,_⟩ => k
  have hinj : Function.Injective corner := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ he
    cases a with
    | inr a => exact ha.elim
    | inl a => cases b with
      | inr b => exact hb.elim
      | inl b => exact Subtype.ext (congrArg Sum.inl he)
  obtain ⟨f,hfit⟩ := FrameHall.match_of_partial (fun i pos => RectFits (cubes i) (catalogue t) pos)
    d RectCorner (by simpa using hn) hmiss ((⟨corner,hinj⟩ : {p : RectSlot l // RectCorner p} ↪ Fin 8).trans corners)
    (by rintro ⟨pos,hp⟩; cases pos with
        | inl k => exact hf k
        | inr p => exact hp.elim)
    (by intro pos hp; cases pos with
        | inl k => exact False.elim (hp trivial)
        | inr p => exact hedges p.1 (Nat.zero_lt_of_lt p.2.isLt))
  exact rect_of_match l cubes t ⟨f,hfit⟩

def RareAt {n : ℕ} (d : ℕ) (cubes : Fin n → Cube) (p : Fin 10) : Prop :=
  (pairCopies cubes p).card < d
instance {n : ℕ} (d : ℕ) (cubes : Fin n → Cube) (p : Fin 10) : Decidable (RareAt d cubes p) := by
  unfold RareAt; infer_instance
lemma rareAt_disjoint {n : ℕ} (d : ℕ) (cubes : Fin n → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hn : 2*d ≤ n+1) (p r : Fin 10) (hpr : p ≠ r)
    (hp : RareAt d cubes p) (hr : RareAt d cubes r) : PairDisjoint p r := by
  classical
  let common := Finset.univ \ (pairCopies cubes p ∪ pairCopies cubes r)
  have hu := Finset.card_union_le (pairCopies cubes p) (pairCopies cubes r)
  have he : common.card = n-(pairCopies cubes p ∪ pairCopies cubes r).card := by
    simp [common,Finset.card_sdiff]
  have hcard : 0 < common.card := by unfold RareAt at hp hr; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hcard
  have hnone : ¬ HasPair (cubes i) p ∧ ¬ HasPair (cubes i) r := by
    simpa [common,pairCopies] using hi
  apply missing_disjoint p r (catalogueIndex (cubes i)) hpr
  · simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using hnone.1
  · simpa only [HasPair,hasEdge_catalogueIndex _ (hc i)] using hnone.2

lemma corners_of_threshold (h : Threshold15) {n : ℕ} (cubes : Fin n → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hn : 15 ≤ n) :
    ∃ t : Fin 75, ∃ corners : Fin 8 ↪ Fin n, ∀ k, Fits (cubes (corners k)) (catalogue t) k := by
  let pick : Fin 15 ↪ Fin n := Fin.castLEEmb hn
  obtain ⟨t,f,hf⟩ := (hasSolution_iff_catalogue (fun i => cubes (pick i))).mp
    (h _ (fun i => hc _))
  exact ⟨t,f.trans pick,hf⟩
end FiveColour.Physical
