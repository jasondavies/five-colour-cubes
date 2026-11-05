module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case104
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209944035797862380742170175151605088600124308697821266628831145616211968⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨18740915245514456087539, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475066830037980738387460577625234839625950792211697196357563187971868412046230991680761629786926547894765880320, 0⟩]
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952986726464679527504806213266711142202650634907989307401347548440268546745966716184963308133324115474985545962477728312458284008548154714393595814658276721073505462022832128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 2 0 (.step 7 (.split 14 0 (.step 7 (.step 3 (.close 5))) (.step 3 (.step 18 (.step 5 (.close 17)))))) (.step 3 (.step 31 (.close 5)))) (.step 31 (.step 27 (.step 58 (.close 3))))) (.split 55 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 23 (.step 27 (.step 23 (.step 3 (.close 17))))))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 23 (.step 18 (.close 5))))) (.step 18 (.step 31 (.step 44 (.step 5 (.close 17))))))) (.step 3 (.close 7))) (.step 44 (.split 55 1 (.split 67 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 62 (.close 3)) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 3 (.close 18))))) (.step 3 (.step 7 (.step 18 (.close 3))))) (.step 18 (.step 27 (.step 31 (.close 3))))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 31 (.step 48 (.step 3 (.close 5)))))))) (.step 3 (.step 27 (.split 59 1 (.split 74 1 (.step 3 (.split 55 1 (.split 2 0 (.split 14 0 (.step 3 (.step 31 (.close 61))) (.step 18 (.step 31 (.close 3)))) (.step 61 (.close 3))) (.step 58 (.step 18 (.close 32))))) (.step 44 (.step 61 (.close 3)))) (.step 3 (.step 44 (.step 61 (.step 3 (.close 5))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994274389529170594221147122060209573959507628926718544248417047257320812732247787264554669404053630031332588495893362307401252178912709547756313445844642224916242371706880⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 3 (.step 58 (.step 61 (.split 59 1 (.split 74 1 (.split 58 1 (.step 43 (.split 2 0 (.step 3 (.step 31 (.close 5))) (.step 5 (.close 3)))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 18 (.step 17 (.close 21)))))) (.step 3 (.step 5 (.step 22 (.step 23 (.step 31 (.close 5)))))))))))) (.run (.step 3 (.step 61 (.step 62 (.split 67 1 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 3 (.step 7 (.close 54))))))))) (.run (.step 58 (.step 61 (.step 62 (.split 51 1 (.split 67 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 55 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.split 34 0 (.split 22 0 (.step 53 (.close 5)) (.step 3 (.close 7))) (.step 7 (.step 9 (.step 3 (.step 21 (.step 5 (.close 17))))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 3 (.close 18))))) (.step 3 (.step 7 (.step 18 (.close 3))))) (.step 18 (.step 27 (.step 31 (.close 3))))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 3 (.step 5 (.step 21 (.step 5 (.close 16)))))) (.step 31 (.step 48 (.step 3 (.close 5))))) (.step 27 (.step 31 (.step 44 (.step 48 (.step 23 (.step 55 (.close 53)))))))) (.step 44 (.step 53 (.step 62 (.step 3 (.close 5)))))) (.step 27 (.step 53 (.step 61 (.step 3 (.close 5)))))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 53)))))) (.step 3 (.step 53 (.close 7)))))))))
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248483211542552735967740563782378064049313262000046878557716932228550280378384097385441419050754116812963601288201788957130752⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.step 58 (.split 49 1 (.reuse 0) (.run (.step 58 (.step 61 (.step 62 (.split 50 1 (.split 51 1 (.split 67 1 (.split 58 1 (.split 59 1 (.split 74 1 (.split 55 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 36 0 (.step 52 (.close 3)) (.step 7 (.step 9 (.step 3 (.step 22 (.step 5 (.close 17))))))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 3 (.close 18))))) (.step 3 (.step 7 (.step 18 (.close 3))))) (.step 18 (.step 27 (.step 31 (.close 3))))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 3 (.step 5 (.step 22 (.step 5 (.step 21 (.close 5))))))) (.step 31 (.step 48 (.step 3 (.close 5))))) (.step 27 (.step 31 (.step 34 (.step 44 (.step 31 (.step 48 (.step 23 (.step 18 (.close 3)))))))))) (.step 44 (.step 52 (.step 62 (.step 3 (.close 5)))))) (.step 27 (.step 34 (.step 52 (.step 61 (.step 3 (.close 5))))))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 52)))))) (.step 3 (.step 52 (.close 7)))) (.step 52 (.split 56 1 (.step 52 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 21 (.step 22 (.step 23 (.step 31 (.close 5)))))))))))))))) (.run (.step 3 (.step 27 (.step 3 (.step 46 (.step 52 (.step 53 (.step 7 (.step 9 (.step 27 (.close 46)))))))))))) (.run (.step 7 (.step 31 (.step 44 (.split 49 1 (.split 50 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 18 (.step 21 (.step 31 (.close 44)))))) (.step 9 (.step 18 (.step 31 (.step 21 (.step 44 (.close 52))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690953697962524693974082903962440187474131033127947878138454092611233040910787928913540995756289572894945710178304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 21 (.step 43 (.step 3 (.step 58 (.split 39 1 (.split 42 1 (.split 49 1 (.step 43 (.split 56 1 (.step 42 (.step 58 (.split 59 1 (.split 74 1 (.step 21 (.split 58 1 (.step 43 (.split 2 0 (.step 3 (.step 31 (.close 5))) (.step 5 (.close 3)))) (.step 5 (.close 3)))) (.step 5 (.step 18 (.step 17 (.close 21))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.close 5))))))))) (.step 5 (.step 21 (.step 43 (.step 58 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.split 49 0 (.step 28 (.split 10 0 (.split 16 0 (.step 59 (.close 3)) (.step 3 (.step 18 (.step 5 (.close 31))))) (.step 3 (.step 5 (.step 3 (.close 31)))))) (.step 3 (.step 21 (.step 22 (.step 5 (.close 16)))))) (.step 18 (.step 5 (.step 16 (.close 31))))) (.step 28 (.step 43 (.step 3 (.step 5 (.step 3 (.close 31))))))) (.step 5 (.close 31))) (.step 3 (.step 5 (.step 21 (.step 22 (.step 16 (.close 31))))))) (.step 5 (.step 3 (.step 31 (.step 21 (.close 41)))))))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 23 (.step 31 (.step 42 (.step 41 (.step 52 (.close 58))))))))))) (.step 5 (.step 21 (.step 31 (.step 3 (.step 28 (.close 41))))))) (.step 5 (.step 21 (.step 31 (.step 32 (.step 41 (.step 5 (.close 42))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690953697962524693974082903962440187474131033127947878138454092611233040910787928913540995756289572894945710178304⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 38 1 (.split 39 1 (.split 40 1 (.reuse 0) (.run (.step 3 (.step 31 (.step 43 (.step 58 (.step 61 (.split 49 1 (.split 50 1 (.step 43 (.split 59 1 (.split 74 1 (.split 14 0 (.step 43 (.close 3)) (.step 5 (.step 3 (.step 18 (.step 17 (.step 23 (.close 17))))))) (.step 5 (.step 11 (.step 18 (.step 23 (.step 17 (.close 31))))))) (.step 3 (.step 5 (.step 23 (.step 31 (.close 21))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.close 53))))))) (.step 3 (.step 5 (.step 23 (.step 31 (.step 52 (.step 5 (.close 21))))))))))))))) (.run (.step 3 (.step 31 (.step 5 (.step 58 (.step 61 (.split 40 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 74 1 (.step 31 (.step 27 (.step 42 (.step 3 (.step 61 (.step 27 (.step 42 (.step 3 (.step 31 (.step 17 (.step 3 (.close 5)))))))))))) (.step 11 (.step 42 (.step 31 (.step 42 (.step 3 (.close 5))))))) (.step 3 (.step 27 (.step 42 (.step 44 (.step 42 (.step 3 (.close 5)))))))) (.step 3 (.step 21 (.step 27 (.step 32 (.step 42 (.close 3))))))) (.step 3 (.step 27 (.step 34 (.step 42 (.step 44 (.close 52))))))) (.step 3 (.step 5 (.step 21 (.step 27 (.step 31 (.close 42)))))))))))))) (.reuse 1))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209940665804528986909199763415403267014153686953807647624092307355074560⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 36 (.step 31 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.step 7 (.step 5 (.step 21 (.close 22)))) (.step 9 (.step 18 (.step 22 (.step 16 (.step 5 (.step 21 (.close 31)))))))) (.step 3 (.step 22 (.step 5 (.close 31))))) (.step 9 (.step 18 (.step 21 (.step 22 (.close 31)))))) (.step 9 (.step 18 (.step 22 (.step 31 (.step 21 (.close 52))))))) (.step 31 (.step 7 (.step 22 (.close 39))))) (.step 21 (.step 31 (.step 28 (.close 39))))))))))) (.run (.step 7 (.step 31 (.step 34 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.step 7 (.step 5 (.step 21 (.close 22)))) (.step 9 (.step 15 (.step 18 (.step 31 (.close 21)))))) (.step 3 (.close 31))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 31 (.close 34))))))) (.step 9 (.step 15 (.step 16 (.step 18 (.step 31 (.step 21 (.step 34 (.close 52))))))))) (.step 31 (.step 7 (.step 28 (.close 37))))) (.step 16 (.step 21 (.step 31 (.step 28 (.step 37 (.close 3))))))) (.step 31 (.close 37))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 3 (.step 42 (.split 49 1 (.split 50 1 (.split 58 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 18 (.close 52)))))))))))))
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
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209944035797862380742170175148817495450305445503928845385947107019456512⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 38 1 (.step 18 (.step 77 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.step 3 (.close 61))))) (.step 18 (.step 3 (.close 53)))) (.step 18 (.step 26 (.close 52)))) (.step 11 (.step 18 (.step 3 (.close 42))))))) (.step 3 (.step 5 (.step 18 (.close 41))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.split 38 1 (.step 18 (.step 61 (.step 77 (.split 39 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 3)))) (.step 18 (.step 3 (.close 53)))) (.step 18 (.step 22 (.close 52)))) (.step 11 (.step 18 (.step 3 (.close 42)))))))) (.step 3 (.step 5 (.step 18 (.close 41))))) (.step 18 (.step 7 (.step 11 (.close 20))))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 38 1 (.step 18 (.step 42 (.step 77 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 18 (.step 3 (.close 42))))) (.step 18 (.step 3 (.step 42 (.close 53))))) (.step 18 (.step 21 (.step 42 (.close 52)))))))) (.step 3 (.step 5 (.step 18 (.close 41))))) (.step 18 (.step 7 (.step 11 (.close 19))))) (.step 18 (.close 19)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350741762303288301265122493126548277304614147387551354669867297387969003237102829525206321682772957959244696919929591506901695331223146516442280304912777107256776286424589944366179462720993904700880838524508117512817213440⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 50 1 (.split 56 1 (.split 58 1 (.step 31 (.step 27 (.step 34 (.step 77 (.split 59 1 (.split 51 1 (.split 55 1 (.step 3 (.split 74 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 23 (.step 27 (.step 23 (.step 3 (.close 17))))))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 23 (.step 17 (.step 3 (.close 5)))))) (.step 11 (.step 17 (.close 3))))) (.step 12 (.step 18 (.step 17 (.step 31 (.step 34 (.step 5 (.close 17)))))))) (.step 3 (.close 17))) (.step 3 (.step 27 (.step 34 (.step 44 (.step 23 (.step 18 (.step 21 (.step 23 (.close 32)))))))))))))) (.step 11 (.step 17 (.step 18 (.step 31 (.step 34 (.step 61 (.close 3)))))))) (.step 3 (.step 5 (.step 18 (.step 31 (.step 5 (.close 17))))))) (.step 3 (.step 5 (.step 17 (.step 23 (.step 27 (.step 31 (.step 34 (.step 48 (.step 53 (.step 61 (.split 2 0 (.split 16 0 (.step 55 (.step 62 (.step 23 (.step 17 (.close 3))))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.step 17 (.step 21 (.step 5 (.close 23))))))))))))))))) (.step 3 (.step 5 (.step 17 (.step 18 (.step 23 (.step 31 (.close 17)))))))) (.step 5 (.step 11 (.step 17 (.step 18 (.step 34 (.step 36 (.step 42 (.step 3 (.close 5)))))))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 31 (.step 5 (.step 17 (.close 42))))))))) (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.close 3))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319681495209944035797862380742170175151605088600124308697821266628831145616211968⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 2 1 (.split 10 1 (.split 14 1 (.reuse 0) (.step 3 (.step 31 (.step 34 (.step 58 (.split 16 1 (.split 17 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 3 (.step 17 (.close 3)))))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 17 (.step 3 (.close 19))))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 3 (.split 14 1 (.split 39 1 (.step 3 (.step 7 (.step 18 (.close 52)))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.close 17)))))))))) (.run (.step 3 (.step 18 (.step 31 (.step 43 (.step 5 (.step 58 (.split 14 1 (.step 58 (.split 38 1 (.split 39 1 (.step 31 (.step 5 (.step 61 (.split 49 1 (.step 5 (.step 3 (.split 50 1 (.step 77 (.split 59 1 (.step 18 (.step 3 (.step 17 (.step 3 (.close 18))))) (.step 3 (.step 17 (.step 21 (.step 23 (.close 21))))))) (.step 3 (.step 21 (.step 23 (.step 44 (.step 34 (.close 53))))))))) (.step 3 (.step 23 (.step 34 (.step 52 (.step 5 (.close 21)))))))))) (.step 5 (.step 21 (.step 32 (.step 42 (.close 18)))))) (.step 5 (.close 31)))) (.step 5 (.step 17 (.step 23 (.step 17 (.close 42))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case104
