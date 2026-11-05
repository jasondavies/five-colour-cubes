module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case102
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629412372176344319488361123675623736891375844577090015168031054793736884600176640⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593704327342246902771, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571379824473078499879106755612070367207720047320779044319709427110487620107838411633159494367146483991396891344937179677696, 0⟩]
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895658187387370014526889255649741387314133404473034243811998986415742732431484665699676918106599049457597778738607131368394655413798383809601168797577529123002027399944941240251614409858695036928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 3 (.step 15 (.close 31))) (.step 3 (.step 18 (.step 5 (.close 12))))) (.step 3 (.step 7 (.close 12)))) (.step 3 (.step 18 (.step 5 (.close 31))))) (.split 2 0 (.split 16 0 (.step 3 (.step 18 (.step 5 (.step 17 (.close 31))))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 23 (.step 31 (.close 18)))))) (.step 29 (.step 69 (.step 75 (.step 31 (.close 3)))))) (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 31 (.step 3 (.close 18))) (.step 18 (.step 3 (.close 31)))) (.step 31 (.close 74))) (.step 11 (.step 69 (.step 74 (.close 3))))) (.step 29 (.step 69 (.step 74 (.close 3)))))) (.step 3 (.step 69 (.step 3 (.close 7))))) (.step 3 (.step 74 (.step 3 (.step 63 (.step 74 (.split 72 1 (.step 18 (.step 23 (.step 3 (.close 31)))) (.step 3 (.step 26 (.close 31)))))))))) (.step 3 (.step 67 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 17 0 (.step 31 (.step 3 (.step 18 (.close 5)))) (.step 18 (.close 31))) (.step 31 (.step 32 (.step 18 (.step 3 (.close 5)))))) (.step 11 (.step 67 (.close 3)))) (.step 29 (.step 67 (.step 3 (.step 21 (.close 31)))))) (.step 63 (.step 3 (.close 67)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753016137597481846302177162523782007670505410604388137574118329283989868874856295196356880520534905127881096498217267488253593780224⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 56 1 (.split 63 1 (.reuse 0) (.run (.step 66 (.step 3 (.step 66 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 31 (.step 3 (.close 18))) (.step 18 (.step 3 (.step 12 (.close 31))))) (.step 31 (.step 12 (.step 3 (.step 18 (.close 5)))))) (.step 11 (.step 66 (.close 3)))) (.step 29 (.step 66 (.step 3 (.step 22 (.close 31)))))) (.step 63 (.step 3 (.close 66)))))))))) (.run (.step 3 (.split 63 1 (.split 64 1 (.split 65 1 (.step 18 (.step 74 (.step 75 (.split 74 1 (.split 71 1 (.split 72 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 28 (.split 30 0 (.step 59 (.close 3)) (.step 3 (.close 31)))) (.step 3 (.step 5 (.step 3 (.close 31))))) (.step 3 (.close 31))) (.step 5 (.step 3 (.close 31)))) (.step 29 (.step 31 (.step 3 (.step 22 (.close 38)))))) (.step 22 (.step 31 (.step 5 (.close 12))))) (.step 5 (.step 12 (.close 18))))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 22 (.close 31))))))) (.step 18 (.step 31 (.step 63 (.close 67))))) (.step 18 (.step 31 (.step 12 (.step 63 (.close 66))))))))) (.run (.step 3 (.step 51 (.step 3 (.split 56 1 (.step 3 (.split 67 1 (.step 51 (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 3 (.close 18)))))))) (.run (.step 3 (.step 9 (.step 10 (.step 27 (.step 47 (.step 3 (.step 7 (.step 3 (.close 10)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943950551163295313665743697413502706600834117935101590300634778589617101907698153702277849826040631580433321033728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.step 3 (.step 75 (.split 74 1 (.split 72 1 (.split 2 0 (.split 10 0 (.split 14 0 (.step 28 (.split 30 0 (.split 34 0 (.split 35 0 (.step 18 (.step 21 (.close 31))) (.step 31 (.close 3))) (.step 31 (.close 3))) (.step 3 (.close 31)))) (.step 3 (.step 5 (.step 3 (.close 31))))) (.step 3 (.close 31))) (.step 5 (.step 3 (.close 31)))) (.step 29 (.step 31 (.step 3 (.step 22 (.close 38)))))) (.step 5 (.step 12 (.close 18)))))) (.step 18 (.step 31 (.step 18 (.step 5 (.close 12)))))) (.step 3 (.step 5 (.step 10 (.step 18 (.step 21 (.step 31 (.close 22)))))))) (.step 18 (.step 21 (.step 31 (.close 67))))) (.step 18 (.step 31 (.step 12 (.step 63 (.close 66)))))) (.step 5 (.step 10 (.step 28 (.split 63 1 (.split 64 1 (.step 59 (.step 5 (.step 59 (.step 18 (.step 74 (.step 41 (.step 3 (.step 5 (.step 3 (.step 22 (.close 31))))))))))) (.step 5 (.step 18 (.step 21 (.step 31 (.step 41 (.step 5 (.close 67)))))))) (.step 5 (.step 18 (.step 31 (.step 49 (.step 63 (.step 66 (.close 5)))))))))))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 41 (.step 3 (.step 26 (.step 39 (.close 45))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252835458093312342499596338075879062750893329385276938440646737845099594135096134393364074507338090758012928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 38 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 65 1 (.split 74 1 (.split 51 1 (.step 75 (.split 67 1 (.step 29 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 38 (.step 21 (.step 32 (.close 38)))) (.step 31 (.step 38 (.step 21 (.step 31 (.step 38 (.close 66))))))) (.step 31 (.step 40 (.step 38 (.step 31 (.step 66 (.step 18 (.close 38)))))))) (.step 21 (.step 38 (.close 18)))) (.step 40 (.step 66 (.step 38 (.step 32 (.step 67 (.step 38 (.step 3 (.close 18))))))))) (.step 31 (.step 38 (.step 3 (.step 31 (.close 66)))))) (.step 31 (.step 32 (.step 3 (.close 12)))))) (.step 3 (.close 21)))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 29 (.step 38 (.step 40 (.step 66 (.step 67 (.step 69 (.step 74 (.split 2 0 (.step 38 (.step 3 (.step 18 (.close 74)))) (.step 3 (.step 5 (.close 12))))))))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 5 (.step 29 (.step 31 (.step 38 (.close 3))))))) (.step 3 (.step 29 (.step 31 (.step 38 (.step 3 (.step 22 (.step 39 (.close 45))))))))) (.step 3 (.step 5 (.step 31 (.step 28 (.step 38 (.close 3))))))) (.step 3 (.step 29 (.step 31 (.step 38 (.step 3 (.step 22 (.close 39)))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796698108017452960440199639449572676271407739716537823301521718838494715254836262324633972244480⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 75 (.split 56 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 31 (.step 7 (.step 22 (.close 38)))) (.step 29 (.step 31 (.close 74))))) (.step 3 (.step 29 (.step 31 (.close 67))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 45))))))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.step 75 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.step 31 (.step 7 (.step 22 (.close 38)))))) (.step 3 (.step 29 (.step 31 (.close 67))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 3 (.step 5 (.step 22 (.step 31 (.close 39)))))) (.step 7 (.step 31 (.close 39)))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 39))))))))))) (.reuse 2)) (.run (.step 7 (.step 31 (.step 75 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 31 (.step 7 (.step 22 (.close 37)))) (.step 29 (.step 31 (.close 17))))) (.step 3 (.step 29 (.step 31 (.step 17 (.step 66 (.step 17 (.close 67)))))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 3 (.step 5 (.step 28 (.step 31 (.close 37)))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 5 (.step 28 (.step 31 (.step 37 (.close 3))))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 29 (.step 31 (.close 37))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629412372176344319488361123675623736888588251427271151974138633550852846003421184⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 31))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 18 (.step 31 (.close 66))))) (.step 3 (.close 31)))))))) (.run (.step 7 (.step 18 (.step 77 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 74))))) (.step 3 (.step 11 (.step 18 (.close 67))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 18 (.step 38 (.step 66 (.step 38 (.close 67)))))))))))) (.run (.step 7 (.step 18 (.step 77 (.split 22 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.step 18 (.step 3 (.close 7))))) (.step 3 (.step 11 (.step 18 (.close 67))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 18 (.step 38 (.step 66 (.step 38 (.close 67))))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 17 (.close 20)))))))))))) (.run (.step 7 (.step 18 (.step 77 (.split 17 1 (.split 22 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 38))))) (.step 3 (.step 11 (.step 18 (.step 38 (.close 67)))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 18 (.step 38 (.step 66 (.close 67)))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 17 (.close 19))))))) (.step 7 (.step 18 (.step 7 (.close 19))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096783622107585009755967253457475524032131436388556091527033820695730809753877680073881462919575849152757842094807592822779168328826397490889350882111301689519347137336620498348352882498226857409497617399808⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 34 1 (.split 36 1 (.step 27 (.step 77 (.step 3 (.step 31 (.split 74 1 (.split 2 0 (.split 16 0 (.step 3 (.step 18 (.step 5 (.close 17)))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 23 (.step 17 (.close 5))))) (.step 11 (.step 17 (.close 3)))))))) (.step 3 (.step 5 (.step 17 (.close 31))))) (.step 3 (.step 5 (.step 17 (.close 31))))) (.step 3 (.step 17 (.step 31 (.step 69 (.step 29 (.step 40 (.split 2 0 (.split 16 0 (.step 75 (.close 3)) (.step 3 (.close 17))) (.step 3 (.step 5 (.close 12))))))))))) (.step 11 (.step 17 (.step 18 (.step 36 (.step 69 (.step 74 (.close 3)))))))) (.step 3 (.step 17 (.step 18 (.step 12 (.step 17 (.step 12 (.close 34)))))))) (.step 11 (.step 17 (.step 18 (.step 51 (.step 67 (.close 3))))))) (.step 11 (.step 12 (.step 17 (.step 18 (.step 34 (.close 66))))))) (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 31 (.step 5 (.step 12 (.step 17 (.close 67))))))))))) (.step 3 (.step 5 (.step 12 (.step 16 (.step 18 (.step 31 (.step 5 (.step 12 (.step 17 (.close 67))))))))))) (.step 3 (.step 5 (.step 17 (.step 31 (.step 38 (.step 66 (.step 67 (.step 74 (.step 75 (.split 2 0 (.split 16 0 (.step 29 (.step 40 (.split 17 0 (.step 38 (.step 69 (.step 38 (.step 12 (.close 17))))) (.step 3 (.close 17))))) (.step 3 (.close 17))) (.step 3 (.step 5 (.step 12 (.close 17))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925671735958620338716744947036596930700967753021552967978180943955252839937582796702182089405629412372176344319488361123675623736891375844577090015168031054793736884600176640⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 10 1 (.split 14 1 (.reuse 0) (.step 3 (.step 31 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.close 3)))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 3 (.step 17 (.close 3)))))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 17 (.step 3 (.close 19))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.split 14 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 31))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 18 (.step 31 (.close 66))))) (.step 3 (.close 31))) (.step 3 (.close 17)))))))) (.run (.step 3 (.step 18 (.step 31 (.split 14 1 (.split 35 1 (.split 38 1 (.split 56 1 (.step 67 (.step 77 (.split 63 1 (.split 65 1 (.step 75 (.split 71 1 (.step 5 (.step 3 (.step 23 (.step 5 (.step 31 (.step 5 (.step 12 (.close 18)))))))) (.step 11 (.step 23 (.step 67 (.step 74 (.step 3 (.close 5)))))))) (.step 3 (.step 5 (.step 18 (.step 23 (.close 63)))))) (.step 11 (.step 12 (.step 63 (.step 66 (.step 3 (.close 5))))))))) (.step 5 (.step 18 (.step 5 (.step 66 (.close 67)))))) (.step 5 (.step 24 (.step 18 (.step 31 (.step 5 (.step 66 (.close 67)))))))) (.step 3 (.step 5 (.step 31 (.step 32 (.step 38 (.step 5 (.step 12 (.close 66))))))))) (.step 5 (.step 12 (.close 17)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case102
