module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.Chunked.Case78
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2, 5789234136395753411692881238169227500374411343012498997361331656212907769098245984562169002127015908277226114944835056582655132436110218345276409496704667659165840661608791535934022489219257755193906216122845178590347133954⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨28332829588240734347134, 5653548961323977936207446023492293789637427680963569422727051963205498374293613300750817692265347568044813268093686906541296848761506679246043077888340581153728623135459825353848098381261863991956758680015453701907939329, 1⟩]
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
def root : Box := ⟨2, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081322323392935885564542978⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.step 2 (.step 4 (.close 5))) (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 25 0 (.step 2 (.step 4 (.close 5))) (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.step 55 (.split 31 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.step 8 (.step 12 (.close 16))))))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 5))))) (.step 2 (.close 5))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 5 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.close 5)))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.close 5))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨1361129467683753855034090050444484149250, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407713447760611192024730839220517836161026⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.split 31 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.step 10 (.step 12 (.close 16)))))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 10)))) (.step 2 (.step 4 (.close 5)))) (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.split 31 0 (.split 32 0 (.split 33 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 5 (.step 6 (.close 2)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 5))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 5 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.step 6 (.close 16))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955202⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 1 0 (.split 2 0 (.split 3 0 (.split 4 0 (.split 5 0 (.split 6 0 (.split 7 0 (.reuse 0) (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.run (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 25 0 (.step 2 (.step 4 (.close 5))) (.split 26 0 (.split 27 0 (.split 28 0 (.split 29 0 (.split 30 0 (.step 55 (.split 31 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.close 6))))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 5))))) (.step 2 (.close 5))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 5 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.step 4 (.close 6)))) (.step 2 (.close 5)))) (.reuse 1)) (.run (.step 2 (.step 4 (.close 5))))) (.run (.step 2 (.step 4 (.step 6 (.close 12)))))) (.run (.step 2 (.step 4 (.step 6 (.close 12)))))) (.run (.step 2 (.step 4 (.step 6 (.close 12)))))) (.run (.step 2 (.close 5))))) (.run (.step 2 (.step 4 (.close 5))))) (.run (.step 2 (.step 4 (.step 6 (.close 8)))))) (.run (.step 2 (.step 4 (.close 6))))) (.run (.step 2 (.step 4 (.close 6))))) (.run (.step 2 (.close 5)))) (.run (.step 2 (.step 4 (.close 5)))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343945494986754, 5789234136395753411692881238169227500374411343012498997361331656212907769098245984562169002127015908277226114944835056582655132436110218345276409496704667659165840661608791535934022489219257755193906216122845178590347133954⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 5 (.split 3 0 (.split 1 0 (.split 4 0 (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 25 0 (.step 2 (.step 4 (.close 5))) (.step 5 (.step 2 (.step 6 (.step 8 (.step 12 (.close 16))))))) (.step 2 (.close 5))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.step 4 (.close 16)))) (.step 2 (.close 5))) (.step 5 (.step 24 (.close 2)))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.step 4 (.close 12)))) (.step 2 (.close 5))) (.step 5 (.step 24 (.close 2)))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.step 6 (.step 8 (.close 16)))))) (.step 2 (.step 4 (.step 6 (.close 16))))) (.step 2 (.step 4 (.close 5)))) (.step 2 (.step 4 (.step 6 (.close 16)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2, 5789234136395753411692881238169227500374411343012498997361331656212907769098245984562169002127015908277226114944835056582655132436110218345276409496704667659165840661608791535934022489219257755193906216122845178590347133954⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 40 1 (.split 60 1 (.reuse 0) (.run (.split 3 0 (.split 1 0 (.split 4 0 (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 9 0 (.split 10 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 23 0 (.step 68 (.step 2 (.step 4 (.close 5)))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 5))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 5))) (.step 5 (.close 2))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 5))) (.step 5 (.close 2))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))) (.step 2 (.close 4))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part4.excludes
end FiveColour.Packed.Chunked.Case78
