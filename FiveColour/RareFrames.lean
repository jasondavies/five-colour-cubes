module
public import Mathlib.Algebra.BigOperators.Fin
public import FiveColour.RareGeometry
public import FiveColour.FiniteHall
@[expose] public section
namespace FiveColour.Physical
open scoped BigOperators

def CorePosition (t : Cube) {q : ℕ} : FrameSlot q → Prop
  | .inl _ => True
  | .inr p => t (edgeFaces p.1 0) = t (edgeFaces p.1 1)
instance (t : Cube) (q : ℕ) : DecidablePred (@CorePosition t q) := by
  intro p; cases p <;> unfold CorePosition <;> infer_instance

/-- Combine the selected corners with the reserved monochromatic edges. -/
lemma core_placement {m : ℕ} (q : ℕ) (cubes : Fin m → Cube) (t : Fin 75)
    (corners : Fin 8 ↪ Fin m) (R : Fin 5 → Finset (Fin m))
    (hcorner : ∀ k, Fits (cubes (corners k)) (catalogue t) k)
    (hout : ∀ k, corners k ∉ Reserve.used R)
    (hR : Pairwise (fun a b => Disjoint (R a) (R b)))
    (helig : ∀ a i, i ∈ R a → HasEdge (cubes i) a a)
    (hfull : ∀ e : Fin 12, catalogue t (edgeFaces e 0) = catalogue t (edgeFaces e 1) →
      (R (catalogue t (edgeFaces e 0))).card = q) :
    ∃ f : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ Fin m,
      ∀ p, FrameFits (cubes (f p)) (catalogue t) p.val := by
  classical
  let M := {e : Fin 12 // catalogue t (edgeFaces e 0) = catalogue t (edgeFaces e 1)}
  let tag : M → Fin 5 := fun e => catalogue t (edgeFaces e.val 0)
  have hcount (a : Fin 5) : Fintype.card {p : M × Fin q // tag p.1 = a} ≤ (R a).card := by
    rw [Reserve.fibre_prod_card]
    have hc : Fintype.card {e : M // tag e = a} ≤ 1 := by
      let f : {e : M // tag e = a} ↪ {e : Fin 12 //
          catalogue t (edgeFaces e 0) = a ∧ catalogue t (edgeFaces e 1) = a} :=
        ⟨fun e => ⟨e.val.val,e.property,e.val.property.symm.trans e.property⟩,
          fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : {e : Fin 12 // catalogue t (edgeFaces e 0) = a ∧ catalogue t (edgeFaces e 1) = a} => z.val) he))⟩
      exact (Fintype.card_le_of_embedding f).trans (by simpa only [Fintype.card_subtype] using mono_edge_unique t a)
    by_cases hex : ∃ e : M, tag e = a
    · obtain ⟨e,he⟩ := hex
      have hr := hfull e.val e.property
      change (R (tag e)).card = q at hr
      rw [he] at hr
      rw [hr]
      simpa using Nat.mul_le_mul_right q hc
    · have hz : Fintype.card {e : M // tag e = a} = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        exact ⟨fun e => hex ⟨e.val,e.property⟩⟩
      simp [hz]
  obtain ⟨edges,hedges⟩ := Reserve.allocate (fun p : M × Fin q => tag p.1) R hR hcount
  have hdisjoint : ∀ k p, corners k ≠ edges p := by
    intro k p he
    exact hout k ((Reserve.mem_used R _).mpr ⟨_,he ▸ hedges p⟩)
  let placement : (Fin 8 ⊕ (M × Fin q)) ↪ Fin m :=
    ⟨Sum.elim corners edges,corners.injective.sumElim edges.injective hdisjoint⟩
  let lift : {p : FrameSlot q // CorePosition (catalogue t) p} → (Fin 8 ⊕ (M × Fin q)) :=
    fun p => match p with
    | ⟨.inl k,_⟩ => .inl k
    | ⟨.inr (e,j),h⟩ => .inr (⟨e,h⟩,j)
  let forget : (Fin 8 ⊕ (M × Fin q)) → FrameSlot q := Sum.map id (fun p => (p.1.val,p.2))
  have hforget (p) : forget (lift p) = p.val := by
    rcases p with ⟨p,hp⟩; cases p <;> rfl
  let embed : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ (Fin 8 ⊕ (M × Fin q)) :=
    ⟨lift,fun a b he => Subtype.ext ((hforget a).symm.trans ((congrArg forget he).trans (hforget b)))⟩
  refine ⟨embed.trans placement,?_⟩
  rintro ⟨p,hp⟩
  cases p with
  | inl k => exact hcorner k
  | inr p =>
    have h := helig _ _ (hedges (⟨p.1,hp⟩,p.2))
    change HasEdge (cubes (edges (⟨p.1,hp⟩,p.2)))
      (catalogue t (edgeFaces p.1 0)) (catalogue t (edgeFaces p.1 1))
    change HasEdge (cubes (edges (⟨p.1,hp⟩,p.2)))
      (catalogue t (edgeFaces p.1 0)) (catalogue t (edgeFaces p.1 0)) at h
    exact hp ▸ h

/-- Choose corners after reserving only monochromatic edge cubes. -/
lemma reserve_core (h : Threshold15) {m : ℕ} (q : ℕ) (cubes : Fin m → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (available : Finset (Fin m)) (cap : Fin 5 → ℕ)
    (hcap : ∀ i ∈ available, ∀ a, HasEdge (cubes i) a a → cap a = q)
    (hsize : 15 + ∑ a, cap a ≤ available.card) :
    ∃ t : Fin 75, (∃ corners : Fin 8 ↪ Fin m,
      (∀ k, corners k ∈ available) ∧ (∀ k, Fits (cubes (corners k)) (catalogue t) k)) ∧
      ∃ f : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ Fin m,
        ∀ p, FrameFits (cubes (f p)) (catalogue t) p.val := by
  classical
  obtain ⟨R,hR,hsat⟩ := Reserve.exists_saturated available
    (fun a : Fin 5 => fun i => HasEdge (cubes i) a a) cap
  have hused : (Reserve.used R).card ≤ ∑ a, cap a :=
    (Reserve.used_card_le R).trans (Finset.sum_le_sum fun a _ => hR.2.1 a)
  let rest := available \ Reserve.used R
  have hrest : 15 ≤ rest.card := by
    have hsub : available ⊆ rest ∪ Reserve.used R := by
      intro i hi
      by_cases hr : i ∈ Reserve.used R
      · exact Finset.mem_union_right _ hr
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,hr⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 15)
    (show 15 ≤ Fintype.card rest by simpa using hrest)
  let selected := fun i : Fin 15 => cubes (pick i).val
  obtain ⟨t,p,hp⟩ := (hasSolution_iff_catalogue selected).mp (h selected (fun i => hc _))
  let corners : Fin 8 ↪ Fin m := (p.trans pick).trans (Function.Embedding.subtype (· ∈ rest))
  have havail (k) : corners k ∈ available := (Finset.mem_sdiff.mp (pick (p k)).property).1
  have hout (k) : corners k ∉ Reserve.used R := (Finset.mem_sdiff.mp (pick (p k)).property).2
  have hfit (k) : Fits (cubes (corners k)) (catalogue t) k := hp k
  refine ⟨t,⟨corners,havail,hfit⟩,?_⟩
  apply core_placement q cubes t corners R hfit hout hR.2.2 (fun a i hi => (hR.1 a i hi).2)
  intro e he
  have hedge := edge_of_corner _ _ e (hfit (cornerOfEdge e))
  rw [← he] at hedge
  exact (hsat _ _ (havail _) (hout _) hedge).trans (hcap _ (havail _) _ hedge)


def pairCopies {m : ℕ} (cubes : Fin m → Cube) (p : Fin 10) : Finset (Fin m) :=
  Finset.univ.filter fun i => HasPair (cubes i) p

def avoidingQuota (p : Fin 10) (q : ℕ) (a : Fin 5) :=
  if a = pairFirst p ∨ a = pairSecond p then 0 else q

lemma avoidingQuota_sum (p : Fin 10) (q : ℕ) : ∑ a, avoidingQuota p q a = 3*q := by
  fin_cases p <;> simp [avoidingQuota,pairFirst,pairSecond,Fin.sum_univ_succ] <;> omega

lemma avoidingQuota_full (c : Cube) (hc : UsesAllColours c) (p : Fin 10)
    (hp : ¬ HasPair c p) (q : ℕ) (a : Fin 5) (ha : HasEdge c a a) :
    avoidingQuota p q a = q := by
  have hfirst : a ≠ pairFirst p := by
    intro he; subst a
    exact hp (monochromatic_supplies c hc _ _ ha)
  have hsecond : a ≠ pairSecond p := by
    intro he; subst a
    exact hp (hasEdge_symm (monochromatic_supplies c hc _ _ ha))
  simp [avoidingQuota,hfirst,hsecond]

lemma frame_of_match {m q : ℕ} (cubes : Fin m → Cube) (t : Fin 75)
    (h : ∃ f : FrameSlot q ↪ Fin m, ∀ p, FrameFits (cubes (f p)) (catalogue t) p) :
    FrameSolvable q cubes := by
  obtain ⟨f,hf⟩ := h
  exact ⟨catalogue t,catalogue_uses_all_colours t,f,fun p => frameFits_physical _ _ _ (hf p)⟩

lemma frame_from_core {m : ℕ} (q : ℕ) (hq : 1 ≤ q) (cubes : Fin m → Cube)
    (hc : ∀ i, UsesAllColours (cubes i)) (hm : 12*q+8 ≤ m) (t : Fin 75)
    (core : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ Fin m)
    (hcore : ∀ p, FrameFits (cubes (core p)) (catalogue t) p.val)
    (hpairs : ∀ e : Fin 12, catalogue t (edgeFaces e 0) ≠ catalogue t (edgeFaces e 1) →
      4*q+6 ≤ (Finset.univ.filter fun i =>
        HasEdge (cubes i) (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))).card) :
    FrameSolvable q cubes := by
  apply frame_of_match cubes t
  apply FrameHall.match_of_partial (fun i p => FrameFits (cubes i) (catalogue t) p)
    (4*q+6) (CorePosition (catalogue t)) (by simpa [frameSlot_card,Nat.add_comm] using hm)
    (fun i => (frame_missing_bound _ (hc i) t q hq).1) core hcore
  intro p hp
  cases p with
  | inl k => exact False.elim (hp trivial)
  | inr p => exact hpairs p.1 hp

/-- Rare bichromatic pairs either concentrate one opposite-repeat variety,
or can be avoided while selecting the preliminary corner solution. -/
theorem rare_frame_of_threshold (h : Threshold15) {m : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (cubes : Fin m → Cube) (hc : ∀ i, UsesAllColours (cubes i))
    (hslots : 12*q+8 ≤ m) (hm : 11*q+16 ≤ m) : FrameSolvable q cubes := by
  classical
  let rare := fun p => (pairCopies cubes p).card ≤ 4*q+5
  by_cases htwo : ∃ p r : Fin 10, p ≠ r ∧ rare p ∧ rare r
  · obtain ⟨p,r,hpr,hp,hr⟩ := htwo
    let common := Finset.univ \ (pairCopies cubes p ∪ pairCopies cubes r)
    have hcommon : 3*q+6 ≤ common.card := by
      have hu := Finset.card_union_le (pairCopies cubes p) (pairCopies cubes r)
      have he : common.card = m-(pairCopies cubes p ∪ pairCopies cubes r).card := by
        simp [common,Finset.card_sdiff]
      change (pairCopies cubes p).card ≤ 4*q+5 at hp
      change (pairCopies cubes r).card ≤ 4*q+5 at hr
      omega
    have hnone (i : Fin m) (hi : i ∈ common) :
        ¬ HasPair (catalogue (catalogueIndex (cubes i))) p ∧
        ¬ HasPair (catalogue (catalogueIndex (cubes i))) r := by
      have hn := (Finset.mem_sdiff.mp hi).2
      constructor
      · intro hf
        apply hn
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hasEdge_catalogueIndex _ (hc i) _ _).mpr hf⟩)
      · intro hf
        apply hn
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hasEdge_catalogueIndex _ (hc i) _ _).mpr hf⟩)
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < common.card)
    let t := catalogueIndex (cubes i)
    obtain ⟨hop,unique⟩ := two_missing_pairs t p r hpr (hnone i hi).1 (hnone i hi).2
    apply frame_of_match cubes t
    apply FrameHall.match_of_universal_copies
      (fun (i : Fin m) (p : FrameSlot q) => FrameFits (cubes i) (catalogue t) p) (3*q+6)
      (by simpa [frameSlot_card,Nat.add_comm] using hslots)
      (fun j => (frame_missing_bound _ (hc j) t q hq).2 hop) common hcommon
    intro j hj pos
    apply (frameFits_catalogueIndex _ _ (hc j) pos).mpr
    rw [unique _ (hnone j hj).1 (hnone j hj).2]
    exact frameFits_self _ _
  · have hfinish (t : Fin 75)
        (core : {p : FrameSlot q // CorePosition (catalogue t) p} ↪ Fin m)
        (hcore : ∀ p, FrameFits (cubes (core p)) (catalogue t) p.val)
        (havoids : ∀ e : Fin 12, catalogue t (edgeFaces e 0) ≠ catalogue t (edgeFaces e 1) →
          ¬ rare (pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)))) :
        FrameSolvable q cubes := by
      apply frame_from_core q hq cubes hc hslots t core hcore
      intro e he
      have hn := havoids e he
      let p := pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1))
      have hncard : 4*q+6 ≤ (pairCopies cubes p).card := by
        change ¬ (pairCopies cubes p).card ≤ 4*q+5 at hn
        omega
      apply hncard.trans (Finset.card_le_card ?_)
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hasEdge_samePair (pairIndex_correct _ _ he) (Finset.mem_filter.mp hi).2⟩
    by_cases hex : ∃ p : Fin 10, rare p
    · obtain ⟨p,hp⟩ := hex
      let available := Finset.univ \ pairCopies cubes p
      have havail : available.card = m-(pairCopies cubes p).card := by
        simp [available,Finset.card_sdiff]
      have hnot (i : Fin m) (hi : i ∈ available) : ¬ HasPair (cubes i) p := by
        intro hf
        exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩)
      obtain ⟨t,⟨corners,hcorners,hfit⟩,core,hcore⟩ := reserve_core h q cubes hc available
        (avoidingQuota p q) (fun i hi a ha => avoidingQuota_full _ (hc i) p (hnot i hi) q a ha)
        (by rw [avoidingQuota_sum,havail]; change (pairCopies cubes p).card ≤ 4*q+5 at hp; omega)
      apply hfinish t core hcore
      intro e he hr
      have heq : pairIndex (catalogue t (edgeFaces e 0)) (catalogue t (edgeFaces e 1)) = p := by
        by_contra hne
        exact htwo ⟨_,p,hne,hr,hp⟩
      have hedge := edge_of_corner _ _ e (hfit (cornerOfEdge e))
      have hpair := hasEdge_samePair (samePair_symm (pairIndex_correct _ _ he)) hedge
      rw [heq] at hpair
      exact hnot _ (hcorners _) hpair
    · obtain ⟨t,_,core,hcore⟩ := reserve_core h q cubes hc Finset.univ (fun _ => q)
        (fun _ _ _ _ => rfl) (by simp; omega)
      exact hfinish t core hcore (fun e _ hr => hex ⟨_,hr⟩)

end FiveColour.Physical
