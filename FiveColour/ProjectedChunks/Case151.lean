module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case151
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 14696649931972027310843567413265583015629262651307423938320615792288773154838020595935173605717644463105175303345326977828138302626100091496850794625007529270445119409878094273833412394513569251137159168⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37630511536740893520887, 5789234131009374248507346766749886964179117598075761631441503938856419104125729984377942245333425284026394393415169773689373755704242316349912225571028696891635007459092358541327061333498215709696615525420286517587399934977, 0⟩]
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
def root : Box := ⟨4294967296, 4898883310657342436947858505931967927905576914101160200674625819563888027090529966211421724624494258475940798263012264084459138448496184836936931283890147215434065744354061044044622661182693108684423168⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 11 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 47 1 (.split 51 0 (.split 53 0 (.step 55 (.step 60 (.close 3))) (.step 3 (.step 18 (.step 3 (.close 48))))) (.step 3 (.close 48))) (.step 32 (.step 50 (.close 3)))) (.step 3 (.step 18 (.step 3 (.close 48))))) (.step 3 (.step 18 (.step 31 (.close 48))))) (.step 31 (.step 3 (.step 18 (.close 48))))) (.step 31 (.step 3 (.step 18 (.close 48))))) (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 12 (.step 18 (.step 3 (.close 48)))) (.step 3 (.close 8))) (.step 3 (.step 12 (.step 3 (.close 18))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 4)))))) (.step 3 (.step 12 (.step 3 (.step 18 (.step 4 (.step 21 (.close 31))))))))) (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 48 (.step 55 (.step 3 (.step 31 (.close 21))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 12 (.step 18 (.close 48)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 9797766621314684873895708907333611306390237033044132342317282078457201946251179331749005424467194422093577773498065647936913700191995733818037935819713233218242944572240006568733728588605963420374663168⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.step 3 (.split 53 1 (.split 56 1 (.reuse 0) (.run (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 28 (.split 45 0 (.split 47 1 (.split 49 0 (.split 50 0 (.split 51 0 (.split 52 0 (.step 3 (.step 51 (.step 3 (.close 16)))) (.step 3 (.step 16 (.step 22 (.step 16 (.close 21)))))) (.step 3 (.close 16))) (.step 3 (.step 22 (.step 16 (.step 21 (.step 16 (.close 31))))))) (.step 3 (.step 22 (.step 16 (.step 21 (.step 31 (.step 21 (.close 48)))))))) (.step 32 (.step 50 (.close 3)))) (.step 22 (.step 31 (.step 3 (.step 48 (.step 21 (.step 3 (.close 48))))))))) (.step 3 (.step 31 (.step 5 (.close 12))))) (.step 3 (.step 22 (.step 18 (.step 31 (.close 12)))))) (.step 3 (.step 31 (.step 5 (.step 12 (.step 18 (.close 12))))))) (.step 3 (.step 22 (.step 31 (.close 48))))))) (.run (.step 51 (.split 59 1 (.split 34 0 (.split 36 0 (.split 42 0 (.step 8 (.split 47 1 (.split 49 0 (.split 50 0 (.split 51 0 (.split 52 0 (.split 55 0 (.step 3 (.step 51 (.step 3 (.close 12)))) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 18 (.step 12 (.close 48))))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 32 (.step 50 (.close 3))))) (.step 3 (.step 18 (.step 4 (.close 12))))) (.step 3 (.step 18 (.step 4 (.step 12 (.close 31)))))) (.step 3 (.step 14 (.step 18 (.step 4 (.close 31)))))) (.step 3 (.step 18 (.close 48))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4294967296, 9797766621314684873895708907333611306390237033044135615707889977576203376928351677159002817796921222013965973601125594359510535880928721815229463473574550868477042773333882382647750251160316848682041344⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 43 1 (.split 46 1 (.reuse 0) (.run (.step 12 (.step 32 (.step 51 (.step 69 (.split 10 0 (.step 60 (.step 49 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 38 0 (.step 55 (.close 3)) (.step 31 (.step 3 (.step 21 (.close 32))))) (.step 3 (.step 18 (.step 3 (.step 26 (.close 48)))))) (.step 3 (.step 18 (.step 3 (.step 31 (.close 48)))))) (.step 3 (.step 18 (.step 3 (.step 21 (.close 48)))))) (.step 12 (.close 3))) (.step 12 (.step 28 (.step 31 (.step 3 (.close 49)))))) (.step 8 (.step 12 (.step 49 (.close 3))))))) (.step 12 (.close 3))))))))) (.run (.step 3 (.step 8 (.close 10))))) (.run (.step 3 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 48 (.step 53 (.close 3))) (.step 3 (.step 21 (.close 32)))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 48)))))) (.step 3 (.step 18 (.step 48 (.close 12))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4294967296, 9797766621314684873895708907333611306390237033044135618904560493099779421865814925715369973147141310027117237665733157751544509902378598954420696236851086480161105236521817657946855330468278652576464896⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 42 1 (.split 49 1 (.reuse 0) (.run (.step 3 (.split 50 1 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 48 (.step 52 (.close 3))) (.step 3 (.step 31 (.step 32 (.close 48))))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.close 12))) (.step 3 (.step 16 (.step 22 (.step 31 (.step 48 (.close 21))))))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 55 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 52 (.close 3)) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.close 12))) (.step 3 (.step 16 (.step 21 (.step 22 (.step 31 (.close 48))))))) (.step 3 (.step 12 (.step 18 (.close 48)))))))))) (.run (.step 3 (.step 31 (.step 3 (.close 12)))))) (.run (.step 3 (.step 31 (.step 3 (.close 12)))))) (.run (.step 3 (.step 31 (.step 3 (.close 12))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4294967296, 9797766621314684873895708907333611306390237033044135618904560493099779421865814925715372435772528584682068005105739416727407327386083004729834109702105337043638530926403106928862846236576756466658050048⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 38 1 (.reuse 0) (.run (.step 10 (.step 21 (.step 31 (.step 32 (.split 49 1 (.split 51 1 (.split 56 1 (.step 3 (.split 53 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 28 (.step 32 (.split 45 0 (.split 46 1 (.step 3 (.step 31 (.close 3))) (.step 12 (.step 31 (.step 3 (.close 48))))) (.step 31 (.step 3 (.close 48)))))) (.step 3 (.step 31 (.step 5 (.close 12))))) (.step 3 (.step 31 (.step 5 (.step 12 (.close 18)))))) (.step 3 (.step 21 (.step 18 (.step 12 (.step 3 (.close 31))))))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 24 (.step 32 (.step 43 (.step 41 (.step 12 (.step 18 (.close 31)))))))))) (.step 28 (.step 41 (.step 3 (.step 51 (.split 59 1 (.step 41 (.close 3)) (.step 3 (.step 21 (.step 22 (.step 31 (.close 41))))))))))) (.step 3 (.close 21))) (.step 3 (.step 16 (.step 21 (.step 31 (.step 41 (.close 48))))))))))))) (.run (.step 3 (.step 18 (.step 3 (.close 32)))))) (.run (.step 3 (.step 18 (.step 3 (.close 32)))))) (.run (.step 3 (.step 18 (.step 3 (.close 32))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4294967296, 9797766621314684873895708907333611306390237033044135618904560493099779421865814925715372435772528584682068005105739416727407327386083004729834109702105337043638530926404405003077479943483889090740355072⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 11 1 (.reuse 0) (.run (.step 12 (.step 18 (.step 30 (.split 34 1 (.split 36 1 (.split 42 1 (.split 50 1 (.split 51 1 (.split 53 1 (.step 3 (.split 59 1 (.split 34 0 (.split 36 0 (.split 38 1 (.split 56 1 (.split 42 0 (.step 8 (.step 12 (.split 47 1 (.step 18 (.step 3 (.close 48))) (.step 32 (.step 18 (.step 3 (.close 48))))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 4)))))) (.step 12 (.step 8 (.step 24 (.step 14 (.step 18 (.step 14 (.close 32)))))))) (.step 12 (.step 24 (.step 18 (.close 32))))) (.step 3 (.step 12 (.step 18 (.step 4 (.step 31 (.close 32))))))) (.step 3 (.step 12 (.step 18 (.step 4 (.step 14 (.step 31 (.close 32)))))))) (.step 3 (.step 12 (.step 18 (.close 48)))))) (.step 8 (.step 14 (.step 3 (.step 51 (.split 59 1 (.step 14 (.close 3)) (.step 3 (.step 12 (.close 14))))))))) (.step 3 (.close 12))) (.step 3 (.step 12 (.step 14 (.step 18 (.close 48)))))) (.step 3 (.step 4 (.step 12 (.close 31))))) (.step 3 (.step 4 (.step 12 (.close 31))))) (.step 3 (.step 4 (.step 14 (.step 12 (.close 31)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4294967296, 9797766621314684873895708907333611313761257400888506232631956499074392898519319901610667947588111924243766156463448326855779639621257425745719084661362283004983812068848253613265675028387401842108137472⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 52 1 (.split 55 1 (.reuse 0) (.run (.step 12 (.step 18 (.step 58 (.step 3 (.split 11 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.step 58 (.split 46 1 (.split 47 1 (.split 49 1 (.step 58 (.step 3 (.step 5 (.close 31)))) (.step 12 (.step 48 (.step 3 (.step 16 (.step 21 (.step 22 (.step 21 (.close 31))))))))) (.step 32 (.step 48 (.step 50 (.step 3 (.close 16)))))) (.step 12 (.step 48 (.step 49 (.step 3 (.close 21))))))) (.step 3 (.close 31))) (.step 5 (.step 21 (.step 28 (.step 31 (.step 32 (.step 41 (.step 3 (.step 31 (.close 48)))))))))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.step 5 (.step 12 (.step 18 (.step 30 (.step 48 (.step 3 (.step 14 (.step 3 (.step 32 (.step 3 (.close 48))))))))))))))))))) (.run (.step 3 (.step 48 (.step 55 (.step 18 (.step 31 (.split 11 1 (.split 38 1 (.split 46 1 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 55 (.step 32 (.step 48 (.step 3 (.close 22))))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 3 (.step 22 (.step 31 (.step 48 (.close 21)))))) (.step 3 (.step 18 (.step 48 (.close 12))))) (.step 12 (.step 48 (.step 3 (.close 49))))) (.step 3 (.step 21 (.step 31 (.step 41 (.close 48)))))) (.step 3 (.step 12 (.step 14 (.step 18 (.close 48)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨12156783893206034058141819913157698684606776071022764355456027333078084408436254335155391744962218147328704745931545280807798294166245435472324828615568252989437056064657154899968, 9797766621314684873895717011856206784450629495435115004431079570264254956823255060753284590107488251354818724276776846150129780351199827747480139913501255574317568809886764164951130743226388423710343168⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 48 (.step 55 (.step 58 (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 53 1 (.split 56 1 (.split 11 0 (.step 55 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 62 (.close 3)) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48))))) (.step 3 (.step 18 (.step 12 (.close 48))))) (.step 3 (.step 22 (.step 31 (.step 48 (.step 21 (.close 53))))))) (.step 3 (.step 18 (.close 48)))) (.step 52 (.step 55 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 34 0 (.step 62 (.close 3)) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 22 (.step 31 (.step 48 (.close 21)))))) (.step 3 (.step 12 (.step 18 (.close 48)))))))) (.step 32 (.step 48 (.step 3 (.close 52))))) (.step 12 (.step 48 (.step 3 (.close 52))))) (.step 48 (.step 3 (.close 52)))) (.step 3 (.step 31 (.close 52)))) (.step 3 (.step 21 (.step 31 (.step 48 (.step 52 (.close 58))))))) (.step 3 (.step 22 (.step 31 (.close 52))))) (.step 3 (.step 31 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 12 (.step 18 (.close 48))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨11593612569051775034086055672795962032896781989119304995971705754354557426868681273608581299745767733887390848094506531532095235983128962967228726020401242246090946739437568, 4898883310657342436947858505939700780599549947598094886268916413396427094869694701320717797500678114016411853959115466365407990890362309828950782538852771854748542715843537932146187327744717624568709120⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 45 1 (.split 46 1 (.split 47 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 49 1 (.split 50 1 (.step 60 (.split 34 0 (.step 60 (.close 3)) (.step 31 (.step 48 (.step 3 (.close 16)))))) (.step 32 (.step 48 (.close 3)))) (.step 12 (.step 48 (.close 3)))) (.step 49 (.step 50 (.step 51 (.step 3 (.step 31 (.step 58 (.step 3 (.close 5))))))))) (.step 49 (.step 50 (.step 58 (.step 50 (.step 18 (.step 31 (.close 48)))))))) (.step 12 (.step 50 (.close 60)))) (.step 28 (.step 49 (.step 50 (.step 51 (.close 60)))))) (.step 48 (.step 58 (.close 60)))) (.step 8 (.step 49 (.step 50 (.step 51 (.close 60)))))) (.step 32 (.step 49 (.step 50 (.close 3))))) (.step 12 (.step 49 (.close 3)))) (.step 48 (.step 49 (.step 50 (.close 60))))) (.step 28 (.step 31 (.step 49 (.step 3 (.step 50 (.step 3 (.close 12)))))))) (.step 21 (.step 28 (.step 31 (.step 32 (.step 41 (.step 49 (.close 60)))))))) (.step 28 (.step 31 (.step 49 (.step 3 (.step 50 (.step 3 (.close 12)))))))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 14)))))) (.step 3 (.step 8 (.step 18 (.step 49 (.step 50 (.step 3 (.step 32 (.close 41))))))))) (.step 3 (.step 8 (.step 18 (.step 49 (.step 50 (.step 3 (.step 32 (.close 41))))))))) (.step 3 (.step 8 (.step 18 (.step 49 (.step 50 (.step 3 (.close 41)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨11321887274464624056724663742964806672750763661249321285128618900736872487176446556258380175532976302624405125092291534699311753889774377897684302754298088130952480948224, 9797766621314684873895708907333618858000593341840224591939941544403615816942789444151500735412993400463878321470854617923775894595649703802075608577093171699123395659128009952073056631624621254816825344⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 45 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.step 28 (.split 67 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 59 (.step 48 (.close 49))) (.step 31 (.step 43 (.step 32 (.step 49 (.step 32 (.close 50))))))) (.step 22 (.step 31 (.step 43 (.step 49 (.step 18 (.step 32 (.step 18 (.close 50))))))))) (.step 31 (.step 41 (.step 18 (.step 43 (.step 49 (.step 18 (.close 50)))))))) (.step 12 (.step 43 (.step 50 (.step 51 (.step 59 (.close 3))))))) (.step 3 (.step 21 (.close 26))))) (.step 3 (.step 22 (.step 31 (.step 48 (.step 21 (.step 49 (.step 21 (.close 50))))))))) (.step 3 (.step 5 (.step 28 (.step 58 (.step 51 (.step 49 (.close 59)))))))) (.step 3 (.step 21 (.step 49 (.step 21 (.close 50)))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.step 50 (.close 53)))))))) (.step 3 (.step 16 (.step 22 (.step 31 (.step 48 (.step 49 (.step 21 (.step 52 (.step 21 (.close 58))))))))))) (.step 3 (.step 10 (.step 22 (.step 31 (.step 48 (.step 49 (.step 50 (.step 4 (.step 51 (.step 12 (.close 21)))))))))))) (.step 3 (.step 5 (.step 18 (.step 32 (.step 49 (.step 32 (.close 50)))))))) (.step 3 (.step 5 (.step 18 (.step 32 (.step 49 (.step 32 (.close 50)))))))) (.step 3 (.step 5 (.step 18 (.step 32 (.step 41 (.step 49 (.close 50)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨4294967296, 14696649931972027310843567413265583011943745437832428104538006721381848520663880164898552322865436273058989812946044843462056767243066961690498960836386693713142318384922408593886019660351444921603850240⟩
def references : Fin 4 → Box := ![Part6.root, Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 4 := (.split 56 2 (.split 57 2 (.step 3 (.split 59 2 (.split 45 1 (.reuse 0) (.run (.step 12 (.step 31 (.step 48 (.step 3 (.step 48 (.split 16 1 (.split 17 1 (.split 22 1 (.split 11 1 (.split 38 1 (.step 48 (.split 46 1 (.split 47 1 (.split 49 1 (.step 48 (.step 3 (.step 4 (.step 12 (.close 18))))) (.step 12 (.step 48 (.close 3)))) (.step 32 (.step 48 (.step 4 (.step 12 (.step 18 (.close 12))))))) (.step 12 (.step 48 (.close 49))))) (.step 4 (.step 10 (.step 21 (.step 31 (.step 48 (.step 4 (.step 12 (.close 41))))))))) (.step 4 (.step 12 (.step 8 (.step 14 (.step 3 (.step 18 (.close 48)))))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 18)))))))))) (.reuse 1))) (.step 12 (.step 32 (.step 47 (.step 48 (.step 51 (.step 58 (.step 69 (.split 52 1 (.split 11 1 (.reuse 2) (.run (.step 8 (.step 12 (.step 14 (.step 50 (.close 60))))))) (.run (.step 18 (.step 31 (.step 48 (.step 49 (.step 50 (.step 3 (.close 60))))))))))))))))) (.step 3 (.step 10 (.step 31 (.step 48 (.step 51 (.step 58 (.step 60 (.split 52 1 (.split 11 1 (.split 38 1 (.reuse 3) (.run (.step 21 (.step 28 (.step 32 (.step 41 (.step 59 (.split 22 1 (.step 59 (.step 3 (.step 16 (.step 21 (.step 22 (.step 31 (.close 41))))))) (.step 3 (.step 5 (.step 18 (.close 32)))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 12 (.step 18 (.step 28 (.step 41 (.step 43 (.step 50 (.step 51 (.step 24 (.step 14 (.close 59))))))))))))))) (.run (.step 3 (.step 22 (.step 31 (.step 48 (.step 41 (.step 49 (.step 21 (.step 50 (.step 21 (.close 59))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨10544329205960616522212199627389019981725852621020117108829895873308994329698799696060251608055994196445127134297314597945019373567564764896113707455157022752768, 9797766621314684873895708907333607536113329421545373827892720791796570455201817605931003947800244355826691284865660943497370272256225141810919327475725272097743646396645797669315134465336965476504305664⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 1 (.split 36 1 (.split 42 1 (.split 45 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.step 8 (.split 38 1 (.split 67 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.step 56 (.step 48 (.close 49))) (.step 18 (.step 24 (.step 12 (.step 49 (.step 12 (.close 50))))))) (.step 24 (.step 32 (.step 49 (.step 18 (.step 32 (.step 18 (.close 12)))))))) (.step 18 (.step 24 (.step 49 (.step 50 (.step 12 (.step 51 (.step 12 (.close 31))))))))) (.step 14 (.step 18 (.step 24 (.step 49 (.step 31 (.close 32))))))) (.step 3 (.step 12 (.close 44)))) (.step 3 (.step 24 (.step 32 (.step 49 (.step 51 (.step 43 (.step 31 (.close 56)))))))))) (.step 3 (.step 18 (.step 48 (.step 12 (.step 49 (.step 12 (.close 50)))))))) (.step 3 (.step 5 (.step 8 (.step 18 (.step 48 (.step 49 (.step 50 (.step 51 (.step 56 (.step 3 (.close 48)))))))))))) (.step 3 (.step 12 (.step 49 (.step 12 (.close 50)))))) (.step 3 (.step 18 (.step 48 (.step 12 (.step 49 (.step 12 (.close 50)))))))) (.step 3 (.step 12 (.step 18 (.step 48 (.close 49)))))) (.step 3 (.step 4 (.step 8 (.step 48 (.step 51 (.step 50 (.close 56)))))))) (.step 3 (.step 4 (.step 31 (.step 12 (.step 49 (.step 12 (.close 50)))))))) (.step 3 (.step 4 (.step 31 (.step 12 (.step 49 (.step 12 (.close 50)))))))) (.step 8 (.step 12 (.step 14 (.step 56 (.split 42 1 (.step 56 (.step 3 (.step 12 (.close 14)))) (.step 3 (.step 4 (.close 14))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨9820171823688425610039569090482797456649926138129194368449874104288401389214023664649810276977712471452660052382680213027651769637656179159989877735424, 14696649931972027310843567413265583011943752467385238625063570655132006806389928303998604102894267579119150985525000834929446950093248765560147909396123860362909203517980138738242375506942521680477552640⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 21 (.step 48 (.step 53 (.step 55 (.step 58 (.split 59 1 (.step 18 (.step 31 (.split 11 1 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 53 (.step 12 (.step 32 (.step 48 (.close 3))))) (.step 3 (.step 21 (.close 32)))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 21 (.step 31 (.close 48))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 12 (.step 18 (.step 12 (.close 48)))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.close 52))))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 12 (.step 18 (.close 48))))))) (.step 52 (.step 53 (.step 55 (.step 62 (.split 34 1 (.split 36 1 (.split 56 1 (.split 11 1 (.split 17 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.split 53 1 (.split 17 0 (.step 53 (.close 3)) (.step 3 (.step 48 (.step 18 (.close 53))))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 48 (.step 52 (.close 53))))) (.step 3 (.step 48 (.close 31)))) (.step 3 (.step 21 (.close 32)))) (.step 3 (.step 21 (.close 53)))) (.step 3 (.step 21 (.step 52 (.step 31 (.close 48)))))) (.step 3 (.step 18 (.close 53)))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.close 53))))))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 53)))))) (.step 3 (.step 21 (.step 31 (.close 52)))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨9590011546570728134804266689924606891259693494266791375439330179969141981654319985009580348611047335402988332404961145534816181286773612465218387968, 4898883310657342436947862558193269440898201478182005301389347109205134991144881282349766730556994174263015885242143423417258171731011133181609287287137169827879708225378011776837824617722033525980397568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 59 1 (.step 31 (.split 53 1 (.split 56 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 52 (.step 12 (.step 32 (.step 48 (.close 3))))) (.step 3 (.step 31 (.step 32 (.close 48))))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 31 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.step 18 (.close 48)))) (.step 3 (.close 12))) (.step 3 (.step 16 (.step 22 (.step 31 (.step 48 (.close 21))))))) (.step 3 (.step 12 (.step 18 (.close 48)))))) (.step 52 (.step 53 (.step 55 (.step 62 (.split 56 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.split 53 1 (.split 16 0 (.step 62 (.close 3)) (.step 3 (.step 34 (.step 48 (.step 18 (.close 52)))))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 3 (.step 48 (.close 52)))) (.step 3 (.step 48 (.close 31)))) (.step 3 (.step 32 (.step 31 (.close 48))))) (.step 3 (.step 52 (.close 21)))) (.step 3 (.close 52))) (.step 3 (.step 22 (.step 31 (.step 48 (.step 21 (.close 52)))))))))))) (.step 3 (.step 21 (.step 31 (.step 48 (.close 52)))))) (.step 3 (.step 22 (.step 31 (.close 52))))) (.step 3 (.step 16 (.step 31 (.close 52))))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨4294967296, 14696649931972027310843567413265583011943752467385238631456911686179158896259439430615008697067396575297011902484554288242208271196128755566534808470155417298234758454620902428119829698124929987759833088⟩
def references : Fin 4 → Box := ![Part10.root, Part11.root, Part12.root, Part13.root]
def proof : Chunks.Proof 4 := (.split 49 2 (.split 50 2 (.split 53 2 (.reuse 0) (.step 3 (.step 18 (.step 30 (.step 48 (.step 51 (.step 58 (.step 60 (.split 52 1 (.split 34 1 (.reuse 1) (.run (.step 3 (.step 4 (.step 14 (.step 31 (.close 49))))))) (.run (.step 3 (.step 18 (.step 48 (.step 14 (.step 49 (.step 12 (.step 50 (.step 12 (.close 56))))))))))))))))))) (.reuse 2)) (.step 3 (.step 12 (.step 48 (.step 52 (.step 55 (.step 58 (.split 50 1 (.reuse 3) (.run (.step 21 (.step 52 (.step 53 (.step 55 (.split 36 1 (.split 42 1 (.split 56 1 (.split 17 1 (.split 22 1 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 43 0 (.split 53 1 (.split 16 0 (.split 17 0 (.step 52 (.close 3)) (.step 3 (.step 34 (.step 48 (.close 52))))) (.step 3 (.step 34 (.step 48 (.step 18 (.close 52)))))) (.step 3 (.step 12 (.step 18 (.close 48))))) (.step 3 (.step 48 (.close 52)))) (.step 3 (.step 48 (.close 31)))) (.step 3 (.step 21 (.close 32)))) (.step 3 (.step 21 (.close 52)))) (.step 3 (.step 21 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 18 (.close 52)))) (.step 3 (.step 21 (.step 22 (.step 31 (.step 48 (.close 52))))))) (.step 3 (.step 21 (.step 31 (.close 52))))) (.step 3 (.step 21 (.step 22 (.step 31 (.close 52)))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨4294967296, 14696649931972027310843567413265583011943752467385238631456917783344296232181766347797098136845337490527759295006333310033145039500306137921261605943012963180990929991595748925430172369952428597692071936⟩
def references : Fin 1 → Box := ![Part14.root]
def proof : Chunks.Proof 1 := (.split 47 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 48 (.step 50 (.step 51 (.step 69 (.split 52 1 (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 45 1 (.split 46 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 11 0 (.split 49 1 (.split 50 1 (.step 60 (.step 50 (.close 3))) (.step 48 (.step 3 (.close 18)))) (.step 12 (.step 48 (.step 3 (.close 18))))) (.step 12 (.step 18 (.step 3 (.step 48 (.close 50)))))) (.step 49 (.step 50 (.close 3)))) (.step 28 (.step 49 (.close 50)))) (.step 48 (.close 50))) (.step 8 (.step 49 (.close 50)))) (.step 12 (.step 49 (.close 3)))) (.step 48 (.step 49 (.close 50)))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 50)))))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 50)))))) (.step 28 (.step 31 (.step 49 (.step 3 (.close 14)))))) (.step 3 (.step 8 (.step 18 (.step 3 (.step 49 (.step 3 (.close 50)))))))) (.step 3 (.step 8 (.step 18 (.step 3 (.step 49 (.step 3 (.close 50)))))))) (.step 3 (.step 8 (.step 18 (.step 3 (.step 49 (.step 3 (.close 50)))))))) (.step 8 (.step 12 (.step 14 (.close 50))))) (.step 18 (.step 31 (.step 48 (.step 49 (.close 50)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨4294967296, 14696649931972027310843567413265583011943752470817637461522222646789509461152074603811876421135523340650021051349614451557940777249383006476944671319818206323882488083923319923821023907754899284860862464⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.step 55 (.split 46 2 (.reuse 0) (.run (.step 12 (.step 32 (.step 47 (.step 48 (.step 49 (.step 51 (.step 69 (.split 52 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 45 1 (.split 47 1 (.split 53 1 (.split 55 1 (.split 56 1 (.split 57 1 (.split 16 0 (.split 17 0 (.split 49 1 (.split 50 1 (.step 49 (.step 60 (.step 48 (.close 3)))) (.step 32 (.step 48 (.close 3)))) (.step 48 (.close 3))) (.step 49 (.step 50 (.step 49 (.step 3 (.step 18 (.close 48))))))) (.step 49 (.step 50 (.step 58 (.step 49 (.close 3)))))) (.step 49 (.close 3))) (.step 28 (.step 49 (.close 3)))) (.step 48 (.close 49))) (.step 8 (.step 49 (.close 3)))) (.step 32 (.step 49 (.close 3)))) (.step 48 (.close 49))) (.step 28 (.step 31 (.step 3 (.close 49))))) (.step 21 (.step 28 (.step 31 (.step 32 (.step 41 (.close 49))))))) (.step 28 (.step 31 (.step 3 (.close 49))))) (.step 28 (.step 31 (.step 3 (.close 49))))) (.step 3 (.step 8 (.step 18 (.close 49))))) (.step 3 (.step 8 (.step 18 (.close 49))))) (.step 3 (.step 8 (.step 18 (.close 49))))) (.step 18 (.step 31 (.step 48 (.close 49)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨7387876161823964852302320018776927588452451113212271250240305013296072832155726989640174922790921682651247043149824, 9797766621314684873895708907333607536113322395424965410823066563096663914242291759225617381583260301538603100382941020740650738055632556216204457814345432766079192308201467905775963685008970736434413568⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 11 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 45 1 (.split 49 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 59 1 (.step 28 (.split 53 1 (.split 67 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 41 (.step 3 (.step 21 (.close 48)))) (.step 31 (.step 5 (.step 32 (.step 5 (.close 41)))))) (.step 31 (.step 18 (.step 32 (.step 18 (.close 41)))))) (.step 21 (.step 31 (.step 18 (.step 32 (.step 18 (.close 41))))))) (.step 12 (.step 32 (.step 43 (.step 41 (.close 3)))))) (.step 3 (.step 21 (.close 26)))) (.step 3 (.step 32 (.step 43 (.step 41 (.step 3 (.step 12 (.step 3 (.close 18)))))))))) (.step 3 (.step 21 (.step 31 (.step 41 (.close 48)))))) (.step 3 (.step 5 (.step 28 (.step 32 (.step 41 (.close 48))))))) (.step 3 (.step 21 (.step 31 (.step 41 (.close 48)))))) (.step 3 (.step 21 (.close 41)))) (.step 3 (.step 16 (.step 21 (.step 31 (.step 48 (.close 41))))))) (.step 3 (.step 4 (.step 10 (.step 21 (.step 31 (.step 48 (.step 4 (.step 12 (.close 41)))))))))) (.step 3 (.step 5 (.step 18 (.step 32 (.close 41)))))) (.step 3 (.step 5 (.step 18 (.step 32 (.close 41)))))) (.step 3 (.step 5 (.step 18 (.step 32 (.close 41)))))) (.step 3 (.step 4 (.step 5 (.step 12 (.step 18 (.step 28 (.step 32 (.step 43 (.step 41 (.step 24 (.step 41 (.close 14))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨3894222643901120721397876541882368, 9797766621314684873895708907333611310075750731742722909443762048322495182340846002057043686509996627621093573931947430711102553398842243951263641106062107834620149292132365360071296649760364315872854016⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 53 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 45 1 (.split 50 1 (.split 51 1 (.split 52 1 (.split 55 1 (.split 59 1 (.step 8 (.split 67 1 (.split 34 0 (.split 38 1 (.split 56 1 (.split 36 0 (.split 38 0 (.split 42 0 (.step 14 (.step 3 (.step 12 (.close 48)))) (.step 18 (.step 4 (.step 12 (.step 4 (.close 14)))))) (.step 12 (.step 14 (.step 3 (.close 4))))) (.step 18 (.step 12 (.step 14 (.step 4 (.close 31)))))) (.step 12 (.step 24 (.step 14 (.step 3 (.step 32 (.step 3 (.close 31)))))))) (.step 12 (.step 24 (.step 32 (.step 14 (.step 43 (.step 14 (.close 31)))))))) (.step 14 (.close 3))) (.step 3 (.step 12 (.close 14))))) (.step 3 (.step 12 (.step 14 (.close 48))))) (.step 3 (.step 5 (.step 8 (.step 12 (.step 18 (.step 48 (.step 14 (.step 3 (.step 48 (.step 32 (.step 3 (.close 48))))))))))))) (.step 3 (.step 12 (.step 14 (.close 48))))) (.step 3 (.step 12 (.close 14)))) (.step 3 (.step 12 (.step 18 (.step 48 (.close 14)))))) (.step 3 (.step 4 (.step 8 (.step 12 (.step 14 (.step 3 (.close 48)))))))) (.step 3 (.step 4 (.step 12 (.step 31 (.close 14)))))) (.step 3 (.step 4 (.step 31 (.step 12 (.close 14)))))) (.step 3 (.step 4 (.step 14 (.close 31))))) (.step 8 (.step 14 (.step 56 (.split 42 1 (.step 56 (.step 3 (.step 12 (.step 14 (.close 48))))) (.step 3 (.step 4 (.close 14)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨4294967296, 14696649931972027310843567413265583015629262651307423938320615792288773154838020595935173605717644463105175303345326977828138302626100091496850794625007529270445119409878094273833412394513569251137159168⟩
def references : Fin 3 → Box := ![Part16.root, Part17.root, Part18.root]
def proof : Chunks.Proof 3 := (.step 18 (.step 31 (.step 48 (.step 58 (.split 11 2 (.split 38 2 (.reuse 0) (.step 3 (.step 10 (.step 21 (.step 31 (.step 32 (.step 41 (.step 48 (.step 49 (.step 58 (.step 60 (.split 52 2 (.split 53 2 (.split 56 1 (.reuse 1) (.run (.step 28 (.step 41 (.step 59 (.split 22 1 (.step 59 (.step 3 (.step 16 (.step 21 (.step 22 (.step 31 (.step 41 (.close 48)))))))) (.step 3 (.step 5 (.step 18 (.step 32 (.close 41))))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 8 (.step 14 (.step 18 (.step 24 (.step 32 (.step 41 (.step 43 (.step 49 (.step 51 (.step 41 (.step 12 (.close 56))))))))))))))))) (.run (.step 3 (.step 21 (.step 31 (.step 41 (.step 48 (.step 41 (.close 49)))))))))))))))))))) (.step 3 (.step 12 (.step 14 (.step 18 (.step 30 (.step 48 (.step 50 (.step 58 (.step 60 (.split 38 2 (.split 52 2 (.split 56 2 (.reuse 2) (.run (.step 3 (.step 4 (.step 5 (.step 8 (.step 12 (.step 14 (.step 24 (.step 31 (.step 41 (.step 43 (.step 50 (.step 51 (.step 14 (.step 32 (.close 59))))))))))))))))) (.run (.step 3 (.step 12 (.step 14 (.step 18 (.step 48 (.step 14 (.close 50))))))))) (.run (.step 3 (.step 4 (.step 5 (.step 8 (.step 12 (.step 14 (.step 24 (.step 31 (.step 32 (.step 41 (.step 43 (.step 60 (.step 14 (.step 3 (.close 31)))))))))))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part19.excludes
end FiveColour.Packed.ProjectedChunks.Case151
