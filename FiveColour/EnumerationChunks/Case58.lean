module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584873658725781281437299689436667233102356706050405951969768034613546337362247680⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨32908284911715939576823, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857309521993999462306427087381105369261884265993783467999530422928012791073057088273642977565022587162213165827073, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply FastWeight.cut_valid_of_fast_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply FastWeight.cut_valid_of_fast_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply FastWeight.cut_valid_of_fast_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584873658725781281437299689436667233102356704721176688534251933480337780378697728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 0 (.split 22 0 (.split 59 0 (.split 49 0 (.split 35 0 (.step 54 (.step 4 (.step 9 (.close 18)))) (.step 33 (.step 29 (.step 4 (.step 18 (.close 38)))))) (.step 37 (.step 43 (.step 58 (.step 9 (.close 33)))))) (.step 45 (.step 43 (.step 58 (.step 9 (.close 33)))))) (.split 34 0 (.split 17 0 (.step 45 (.close 43)) (.split 35 0 (.step 54 (.step 23 (.close 9))) (.step 24 (.step 33 (.step 43 (.close 4)))))) (.split 35 0 (.split 36 0 (.step 43 (.step 55 (.step 24 (.step 9 (.close 33))))) (.step 45 (.step 39 (.step 4 (.close 5))))) (.step 33 (.step 43 (.step 4 (.close 20))))))) (.split 17 0 (.split 22 0 (.split 59 0 (.split 49 0 (.split 35 0 (.step 43 (.step 5 (.step 28 (.step 33 (.close 38))))) (.step 33 (.step 4 (.step 9 (.close 38))))) (.step 37 (.step 38 (.close 4)))) (.step 38 (.close 43))) (.split 35 0 (.split 38 0 (.step 70 (.step 23 (.close 24))) (.step 33 (.step 23 (.close 4)))) (.step 33 (.step 38 (.close 20))))) (.split 22 0 (.split 35 0 (.split 38 0 (.step 54 (.step 23 (.step 9 (.close 17)))) (.step 33 (.step 23 (.close 4)))) (.step 33 (.step 38 (.close 20)))) (.split 34 0 (.step 24 (.split 35 0 (.step 24 (.step 54 (.step 19 (.close 20)))) (.step 24 (.close 4)))) (.split 35 0 (.split 38 0 (.step 23 (.step 24 (.close 20))) (.step 23 (.close 5))) (.step 17 (.step 24 (.step 4 (.close 5))))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584873658725781281437299689436667233102356706050404684319167806384144840659042304⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 12 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 35 0 (.split 22 0 (.split 36 0 (.split 34 0 (.step 9 (.step 13 (.close 18))) (.step 15 (.step 13 (.close 18)))) (.split 49 0 (.step 58 (.step 9 (.step 15 (.close 33)))) (.step 29 (.close 37)))) (.step 43 (.split 36 0 (.step 13 (.step 18 (.step 9 (.step 15 (.close 33))))) (.step 18 (.step 13 (.step 29 (.step 15 (.step 33 (.close 39))))))))) (.split 36 0 (.split 22 0 (.step 29 (.step 15 (.step 37 (.step 18 (.close 33))))) (.step 18 (.step 9 (.step 13 (.step 15 (.step 33 (.close 38))))))) (.step 29 (.step 37 (.step 38 (.step 4 (.step 18 (.close 39)))))))) (.split 22 0 (.split 30 0 (.split 35 0 (.step 43 (.step 4 (.close 9))) (.step 29 (.step 37 (.step 18 (.step 38 (.close 39)))))) (.step 13 (.step 43 (.close 4)))) (.step 13 (.step 24 (.step 43 (.close 4)))))) (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.step 43 (.step 4 (.close 9))) (.step 29 (.step 21 (.step 13 (.step 15 (.close 38)))))) (.step 13 (.close 38))) (.step 13 (.step 24 (.step 38 (.step 24 (.close 4)))))) (.split 22 0 (.step 13 (.step 24 (.step 38 (.step 24 (.close 4))))) (.step 23 (.step 24 (.close 17))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨1267650600228229401497776947200, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584873658725781281437299689436665771600719373818259752500019445426719621149360128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 17 0 (.split 22 0 (.split 59 0 (.split 49 0 (.split 35 0 (.split 38 0 (.step 52 (.step 9 (.close 18))) (.step 33 (.step 15 (.step 16 (.close 18))))) (.step 33 (.step 15 (.step 9 (.close 18))))) (.step 37 (.step 13 (.step 9 (.close 18))))) (.step 45 (.step 15 (.step 52 (.step 9 (.close 18)))))) (.split 35 0 (.split 30 0 (.step 43 (.step 5 (.step 16 (.close 39)))) (.step 13 (.step 33 (.step 43 (.step 39 (.close 45)))))) (.step 33 (.step 43 (.step 4 (.step 15 (.close 39))))))) (.split 22 0 (.split 35 0 (.split 30 0 (.step 43 (.step 5 (.step 16 (.close 39)))) (.step 13 (.step 33 (.step 39 (.close 4))))) (.step 33 (.step 43 (.step 4 (.step 15 (.close 39)))))) (.step 13 (.split 35 0 (.split 38 0 (.step 24 (.step 14 (.close 20))) (.step 23 (.step 14 (.step 19 (.close 23))))) (.step 24 (.step 4 (.close 5))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772026226185839051871728573250994782043851970130976612154633064894568522833954916133517435385584873658725781281437299689436667233102356706050405951969768034613546337362247680⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 10 0 (.reuse 0) (.split 12 0 (.split 16 0 (.reuse 1) (.run (.split 17 0 (.split 22 0 (.split 35 0 (.split 30 0 (.step 43 (.step 5 (.step 16 (.close 39)))) (.step 13 (.step 33 (.step 38 (.close 39))))) (.step 33 (.step 38 (.close 39)))) (.step 13 (.split 35 0 (.split 38 0 (.step 24 (.step 14 (.close 20))) (.step 23 (.step 14 (.step 19 (.close 23))))) (.step 24 (.step 4 (.close 5)))))) (.split 22 0 (.step 13 (.split 35 0 (.split 38 0 (.step 24 (.step 14 (.close 20))) (.step 23 (.step 14 (.step 19 (.close 23))))) (.step 24 (.step 4 (.close 5))))) (.split 30 0 (.split 34 0 (.step 24 (.step 13 (.step 19 (.step 20 (.step 4 (.close 9)))))) (.step 13 (.step 17 (.step 14 (.close 20))))) (.step 13 (.step 19 (.step 20 (.step 17 (.close 24)))))))))) (.run (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 15 (.close 13)) (.step 13 (.close 15))) (.step 13 (.close 4))) (.step 13 (.close 4))) (.step 13 (.step 37 (.step 4 (.step 13 (.close 15)))))))))
theorem accepted : Fast.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 11 families root :=
  Fast.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part3

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part3.excludes
end FiveColour.Packed.EnumerationChunks.Case58
