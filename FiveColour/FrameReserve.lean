module
public import FiveColour.Reserve
public import FiveColour.FramePools
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

/-- Reserve at most 25q-4 copies. Every catalogue corner placement in the
complement extends to a frame using only copies from the reserve for its edges. -/
theorem exists_frame_reserve {m : ℕ} (q : ℕ) (hq : 1 ≤ q) (cubes : Fin m → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) :
    ∃ reserved : Finset (Fin m), reserved.card ≤ 25*q-4 ∧
      ∀ (t : Fin 75) (corners : Fin 8 ↪ Fin m),
        (∀ k, corners k ∉ reserved) →
        (∀ k, Fits (cubes (corners k)) (catalogue t) k) → FrameSolvable q cubes := by
  classical
  obtain ⟨R,hR,satR⟩ := Reserve.exists_saturated (Finset.univ : Finset (Fin m))
    (fun a : Fin 5 => fun i => HasEdge (cubes i) a a) (fun _ => q)
  let full : Fin 5 → Bool := fun a => decide ((R a).card = q)
  let available := Finset.univ \ Reserve.used R
  obtain ⟨E,hE,satE⟩ := Reserve.exists_saturated available
    (fun p : Fin 10 => fun i => HasEdge (cubes i) (pairFirst p) (pairSecond p))
    (pairQuota full q)
  let reserved := Reserve.used R ∪ Reserve.used E
  have hsize : reserved.card ≤ 25*q-4 := by
    have hm : (Reserve.used R).card ≤ ∑ a : Fin 5, if full a then q else q-1 := by
      apply (Reserve.used_card_le R).trans
      apply Finset.sum_le_sum
      intro a _
      have ha : (R a).card ≤ q := hR.2.1 a
      by_cases he : (R a).card = q
      · simp [full,he]
      · simp only [full,he,decide_false,Bool.false_eq_true,ite_false]
        omega
    have hb : (Reserve.used E).card ≤ ∑ p : Fin 10, pairQuota full q p :=
      (Reserve.used_card_le E).trans (Finset.sum_le_sum fun p _ => hE.2.1 p)
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add hm hb).trans (reserve_budget full q hq))
  refine ⟨reserved,hsize,?_⟩
  intro t corners hout hcorner
  have houtR (k : Fin 8) : corners k ∉ Reserve.used R :=
    fun h => hout k (Finset.mem_union_left _ h)
  have houtE (k : Fin 8) : corners k ∉ Reserve.used E :=
    fun h => hout k (Finset.mem_union_right _ h)
  have havail (k : Fin 8) : corners k ∈ available :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,houtR k⟩
  have hfull : monoFull t full := by
    intro e he
    have hcE := edge_of_corner _ _ e (hcorner (cornerOfEdge e))
    rw [← he] at hcE
    have hr := satR _ (corners (cornerOfEdge e)) (Finset.mem_univ _) (houtR _) hcE
    simpa only [full,decide_eq_true_eq] using hr
  obtain ⟨hsupply,hcount⟩ := edge_pool_checks t full hfull
  let pools : EdgePool → Finset (Fin m) := Sum.elim R E
  have hdisjoint : Pairwise (fun a b => Disjoint (pools a) (pools b)) := by
    intro a b hab
    cases a with
    | inl a => cases b with
      | inl b => exact hR.2.2 (fun he => hab (congrArg Sum.inl he))
      | inr b =>
        apply Finset.disjoint_left.mpr
        intro i hi hj
        exact (Finset.mem_sdiff.mp (hE.1 b i hj).1).2 ((Reserve.mem_used R i).mpr ⟨a,hi⟩)
    | inr a => cases b with
      | inl b =>
        apply Finset.disjoint_left.mpr
        intro i hi hj
        exact (Finset.mem_sdiff.mp (hE.1 a i hi).1).2 ((Reserve.mem_used R i).mpr ⟨b,hj⟩)
      | inr b => exact hE.2.2 (fun he => hab (congrArg Sum.inr he))
  have hcapacity (p : EdgePool) (e : Fin 12) (he : edgePool t full e = p) :
      poolUnits full p * q ≤ (pools p).card := by
    have hs := hsupply e
    unfold PoolSupplies at hs
    rw [he] at hs
    cases p with
    | inl a =>
      have hr : (R a).card = q := of_decide_eq_true hs.1
      simp [pools,poolUnits,hr]
    | inr p =>
      have hp := hasEdge_samePair (samePair_symm hs)
        (edge_of_corner _ _ e (hcorner (cornerOfEdge e)))
      have hcard := satE p _ (havail (cornerOfEdge e)) (houtE (cornerOfEdge e)) hp
      change poolUnits full (.inr p) * q ≤ (E p).card
      rw [hcard]
      simp only [poolUnits,pairQuota]
      split <;> simp
  have hcard (p : EdgePool) :
      Fintype.card {x : Fin 12 × Fin q // edgePool t full x.1 = p} ≤ (pools p).card := by
    rw [Reserve.fibre_prod_card,Fintype.card_subtype]
    by_cases hex : ∃ e, edgePool t full e = p
    · obtain ⟨e,he⟩ := hex
      exact (Nat.mul_le_mul_right q (hcount p)).trans (hcapacity p e he)
    · have hz : (Finset.univ.filter fun e => edgePool t full e = p) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        exact fun e _ he => hex ⟨e,he⟩
      simp [hz]
  obtain ⟨edges,hedges⟩ := Reserve.allocate (fun x : Fin 12 × Fin q => edgePool t full x.1)
    pools hdisjoint hcard
  apply frame_of_placements q cubes (catalogue t) (catalogue_uses_all_colours t) corners edges hcorner
  · intro x
    have hs := hsupply x.1
    have hi := hedges x
    unfold PoolSupplies at hs
    cases he : edgePool t full x.1 with
    | inl a =>
      rw [he] at hs hi
      have ha := (hR.1 a _ hi).2
      rcases hs.2 with h | h
      · rw [← h]
        exact monochromatic_supplies _ (hc _) a _ ha
      · rw [← h]
        exact hasEdge_symm (monochromatic_supplies _ (hc _) a _ ha)
    | inr p =>
      rw [he] at hs hi
      exact hasEdge_samePair hs (hE.1 p _ hi).2
  · intro k x he
    apply hout k
    have hi := hedges x
    cases hp : edgePool t full x.1 with
    | inl a =>
      rw [hp] at hi
      exact Finset.mem_union_left _ ((Reserve.mem_used R _).mpr ⟨a,he ▸ hi⟩)
    | inr p =>
      rw [hp] at hi
      exact Finset.mem_union_right _ ((Reserve.mem_used E _).mpr ⟨p,he ▸ hi⟩)

/-- The fifteen-cube theorem supplies corners outside the small reserve. -/
theorem frame_of_threshold (h : Threshold15) {m : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hm : 25*q+11 ≤ m) : FrameSolvable q cubes := by
  classical
  obtain ⟨reserved,hsize,extend⟩ := exists_frame_reserve q hq cubes hc
  have hrest : 15 ≤ Fintype.card {i : Fin m // i ∉ reserved} := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin,Fintype.card_coe]
    omega
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 15) hrest
  let selected : Fin 15 → Cube := fun i => cubes (pick i).val
  obtain ⟨t,corners,hcorners⟩ := (hasSolution_iff_catalogue selected).mp
    (h selected (fun i => hc (pick i).val))
  let placement := (corners.trans pick).trans (Function.Embedding.subtype (fun i => i ∉ reserved))
  exact extend t placement (fun k => (pick (corners k)).property) hcorners

end FiveColour.Physical
