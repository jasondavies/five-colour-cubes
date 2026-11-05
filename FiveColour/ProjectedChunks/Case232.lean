module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case232
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584875467977175614502853182733307993850916913393916352603581152291217965611745280⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584875467977175614502853182733307993850916913393916352603581152291217965611745280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 6 0 (.split 10 0 (.split 16 0 (.split 12 0 (.split 49 0 (.step 7 (.split 35 0 (.step 54 (.close 4)) (.step 33 (.step 9 (.step 4 (.close 19)))))) (.step 37 (.step 7 (.step 43 (.step 9 (.close 18)))))) (.step 37 (.step 7 (.step 18 (.step 9 (.step 19 (.step 20 (.close 33)))))))) (.step 7 (.split 17 0 (.step 38 (.close 43)) (.step 39 (.step 24 (.step 38 (.step 4 (.close 9)))))))) (.step 7 (.split 12 0 (.split 16 0 (.split 17 0 (.step 52 (.step 58 (.step 9 (.close 33)))) (.step 13 (.step 39 (.step 4 (.step 9 (.close 5)))))) (.step 13 (.split 35 0 (.split 38 0 (.step 43 (.step 14 (.step 17 (.close 20)))) (.step 23 (.step 5 (.step 4 (.close 15))))) (.step 33 (.step 24 (.step 4 (.step 9 (.close 15)))))))) (.step 13 (.close 15))))) (.split 25 0 (.step 7 (.close 9)) (.split 34 0 (.step 7 (.close 9)) (.step 29 (.close 7))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case232
