module
public import FiveColour.ExtremalMatching
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

def disjointGroup : Fin 75 → Option (Fin 4) :=
![none,none,none,none,none,none,none,none,none,none,some 0,none,none,none,none,none,some 3,some 3,none,none,none,none,some 3,none,none,none,none,none,none,none,some 0,none,none,none,some 2,none,some 2,none,none,none,none,none,some 2,some 1,none,none,none,none,none,none,none,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 1,none,none,none,none,none,none,none]

def singletonVariety : Fin 8 → Fin 3 → Option (Fin 75) :=
![![none,none,none],![none,none,none],![some 35,some 72,none],![some 38,some 56,none],![some 14,some 74,none],![some 11,some 53,none],![some 49,some 50,some 59],![some 61,some 62,some 69]]

def disjointMasks : Fin 75 → Fin 4 → ℕ :=
![![240,240,48,192],![36,36,160,12],![66,66,10,192],![0,0,0,0],![252,60,240,204],![68,4,64,204],![16,80,20,0],![32,160,40,0],![136,8,128,204],![0,0,0,0],![207,15,195,204],![68,4,64,204],![1,65,5,0],![2,130,10,0],![136,8,128,204],![51,3,48,51],![102,6,96,238],![51,3,48,187],![0,64,4,0],![0,64,4,0],![34,66,36,170],![17,129,24,85],![51,3,48,119],![0,128,8,0],![32,160,0,40],![136,8,204,128],![68,4,204,64],![16,80,0,20],![204,12,204,192],![0,0,0,0],![63,15,51,60],![0,128,0,8],![4,132,0,12],![0,128,0,8],![153,9,221,144],![17,1,85,16],![51,3,119,48],![17,129,85,24],![34,2,170,32],![8,72,0,12],![34,66,170,36],![0,64,0,4],![51,3,187,48],![60,252,20,40],![0,0,64,128],![24,136,24,48],![64,0,192,96],![16,0,144,48],![0,0,128,32],![5,85,1,4],![5,85,1,4],![15,95,3,12],![5,85,129,36],![20,4,16,60],![1,17,5,0],![24,136,80,24],![18,2,90,16],![16,0,80,48],![8,136,0,12],![9,153,1,8],![66,34,66,192],![10,170,2,8],![10,170,2,8],![128,0,192,144],![32,0,96,48],![10,170,66,24],![0,0,64,16],![15,175,3,12],![36,68,160,36],![6,102,2,4],![4,68,0,12],![32,0,160,48],![33,1,165,32],![2,34,10,0],![40,8,32,60]]

/-- The anchor and four disjoint pools are shared by all eight corner cases. -/
def sixGroup (k : Fin 8) (i : Fin 75) : Option (Fin 8) :=
  if i = 3 then some 0 else
  match disjointGroup i with
  | some g => some ⟨g.val+1, by omega⟩
  | none => if singletonVariety k 0 = some i then some 5 else
      if singletonVariety k 1 = some i then some 6 else
      if singletonVariety k 2 = some i then some 7 else none

def sixMasks (k : Fin 8) (t : Fin 75) : Fin 8 → ℕ :=
  ![Replay.fits t 3, disjointMasks t 0, disjointMasks t 1,
    disjointMasks t 2, disjointMasks t 3,
    (singletonVariety k 0).elim 255 (Replay.fits t),
    (singletonVariety k 1).elim 255 (Replay.fits t),
    (singletonVariety k 2).elim 255 (Replay.fits t)]

def singletonCount : Fin 8 → ℕ := ![0,0,2,2,2,2,3,3]

def populatedCounts (k : Fin 8) (v : Fin 7 → ℕ) : Prop :=
  ∀ g, 4 + singletonCount k ≤ g.val → v g = 0
instance (k : Fin 8) (v : Fin 7 → ℕ) : Decidable (populatedCounts k v) := by
  unfold populatedCounts; infer_instance

def disjointCount (v : Fin 7 → ℕ) : ℕ := v 0 + v 1 + v 2 + v 3

def sixCompositionDomain (k : Fin 8) : List (Fin 7 → ℕ) :=
  (sourceCompositions 7 8).filter fun v => populatedCounts k v ∧ disjointCount v ≤ 3

def disjointCompositionDomain : List (Fin 7 → ℕ) :=
  (sourceCompositions 7 4).filter fun v => populatedCounts 0 v

structure LocalInventory where
  counts : Fin 7 → ℕ
  placement : CornerAllocation

def LocalInventory.Valid (k : Fin 8) (anchor : ℕ) (w : LocalInventory) : Prop :=
  w.placement.Valid (sixMasks k) (Fin.cons anchor w.counts)
instance instDecidableLocalInventoryValid (k : Fin 8) (a : ℕ) (w : LocalInventory) : Decidable (w.Valid k a) := by
  unfold LocalInventory.Valid
  infer_instance

end FiveColour.Physical
