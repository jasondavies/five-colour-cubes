module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case254
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772022452223414230330376331696413793774961053209756195714202226062881002554841756544659090282996878516253835722645522157254002104907008205594559998894586294689952273717526528⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨32908392998381874375671, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857311870536582236139654976861702158598911641676332376320971938148371859361899508584915508177230179531154389992449, 0⟩]
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
def root : Box := ⟨1073741824, 5515652263101992197612038864773350743462566772022452223414230330376331696413793774961053209756195714202226062881002554841756544659090282996878516253835722645522157254002104907008205594559998894586294689952273717526528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 10 0 (.split 16 0 (.split 22 0 (.split 59 0 (.split 35 0 (.step 39 (.close 9)) (.step 29 (.step 33 (.step 37 (.close 38))))) (.step 45 (.step 9 (.step 33 (.close 37))))) (.step 70 (.close 43))) (.split 17 0 (.step 53 (.step 24 (.step 9 (.close 37)))) (.split 34 0 (.step 53 (.step 20 (.close 9))) (.split 22 0 (.step 24 (.step 17 (.close 38))) (.step 24 (.close 20)))))) (.split 16 0 (.split 17 0 (.step 52 (.split 35 0 (.step 43 (.step 9 (.close 33))) (.step 33 (.step 9 (.step 38 (.close 39)))))) (.step 13 (.split 35 0 (.step 54 (.step 9 (.close 15))) (.step 24 (.step 33 (.step 15 (.step 9 (.step 38 (.close 39))))))))) (.split 34 0 (.split 17 0 (.step 13 (.step 24 (.step 38 (.close 9)))) (.step 24 (.step 13 (.step 20 (.step 19 (.close 24)))))) (.step 13 (.split 35 0 (.split 50 0 (.split 17 0 (.step 43 (.step 17 (.step 20 (.close 38)))) (.step 17 (.close 20))) (.step 24 (.step 15 (.close 33)))) (.step 17 (.step 15 (.close 33)))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 15 (.step 9 (.step 13 (.step 33 (.close 38))))) (.step 13 (.step 29 (.step 15 (.close 43))))) (.step 13 (.step 43 (.step 39 (.close 9))))) (.split 17 0 (.step 13 (.step 38 (.step 43 (.close 9)))) (.split 34 0 (.split 36 0 (.step 53 (.step 13 (.step 24 (.close 9)))) (.step 13 (.step 24 (.close 38)))) (.step 13 (.step 24 (.close 15))))))))
theorem accepted : Chunks.check 11 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 11 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 11 families root :=
  Chunks.check_sound 11 families families_valid references references_excluded proof root root_valid accepted
end Part0

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 11 families root := Part0.excludes
end FiveColour.Packed.ProjectedChunks.Case254
