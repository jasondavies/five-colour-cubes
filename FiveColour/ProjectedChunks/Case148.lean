module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case148
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686450204371425138696287413569753975208630337497545696341547536145423928123879037069277050894686928090329889613554523733231213404360577442746977500149416645079816076246646784⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908392998381874375607, 5789234131009374243490890256636772759901851996560544808214778193549775928795277575978058672488451386148482820637016487820419584261128081612316866307095117301248629629600134054099986201414770618195247788012495054996921910273, 0⟩]
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
def root : Box := ⟨4294967296, 11031304526203979496340767072204264539074732142405299924596678035534750176926387658708231080740990161307942283317510698671587386985496506904203959387822177679251738370813312113837513632260241826553185275864745458532352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 16 0 (.split 36 0 (.step 9 (.step 3 (.step 18 (.close 12)))) (.step 22 (.step 9 (.step 3 (.step 12 (.step 15 (.close 21))))))) (.step 3 (.step 9 (.step 3 (.step 12 (.close 18)))))) (.step 26 (.split 16 0 (.step 26 (.step 3 (.step 9 (.step 3 (.close 12))))) (.step 3 (.step 9 (.step 12 (.close 18))))))) (.step 53 (.split 54 1 (.split 16 0 (.split 17 0 (.step 9 (.step 3 (.step 18 (.step 12 (.step 15 (.close 21)))))) (.step 3 (.step 9 (.step 12 (.close 18))))) (.step 3 (.step 9 (.step 12 (.close 18))))) (.step 9 (.step 21 (.step 3 (.step 18 (.step 12 (.step 15 (.close 26)))))))))) (.step 52 (.split 54 1 (.split 16 0 (.split 17 0 (.step 9 (.step 3 (.step 12 (.step 3 (.close 21))))) (.step 3 (.step 9 (.step 12 (.close 18))))) (.step 3 (.step 9 (.step 12 (.close 18))))) (.step 9 (.step 12 (.step 3 (.step 18 (.step 21 (.close 26))))))))) (.step 26 (.step 31 (.step 9 (.close 12))))) (.step 31 (.step 9 (.close 12)))) (.step 21 (.step 29 (.step 31 (.step 38 (.split 49 1 (.split 54 1 (.split 16 0 (.split 59 1 (.step 3 (.step 9 (.step 3 (.close 12)))) (.step 9 (.step 3 (.step 18 (.step 12 (.step 15 (.close 21))))))) (.step 3 (.step 9 (.step 12 (.close 18))))) (.step 9 (.step 21 (.step 3 (.step 18 (.step 12 (.step 15 (.close 26)))))))) (.step 9 (.step 12 (.step 21 (.step 3 (.step 18 (.step 26 (.close 31))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078141359762215129152622999453185061167676019190179426423400008604072021912864676971316807217700518030632923255509573581810298726382770653969941620336995630909815250138371482877689856⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 72 2 (.split 6 1 (.split 12 1 (.step 3 (.split 21 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.reuse 0) (.run (.step 31 (.step 9 (.close 12))))) (.run (.step 3 (.step 18 (.step 9 (.close 12)))))) (.run (.step 3 (.step 18 (.step 9 (.close 12)))))) (.run (.step 3 (.step 18 (.step 9 (.close 12)))))) (.run (.step 18 (.step 31 (.step 9 (.step 3 (.step 18 (.step 57 (.step 3 (.close 18))))))))))) (.run (.step 9 (.step 12 (.step 21 (.step 22 (.step 9 (.step 3 (.step 15 (.step 18 (.step 31 (.step 15 (.split 21 1 (.split 35 1 (.step 18 (.step 12 (.step 3 (.close 15)))) (.step 12 (.step 15 (.close 3)))) (.step 3 (.step 12 (.close 15)))))))))))))))) (.run (.step 9 (.step 3 (.step 18 (.step 9 (.close 3))))))) (.run (.step 9 (.step 26 (.step 29 (.step 31 (.step 38 (.split 12 1 (.split 21 1 (.split 49 1 (.split 50 1 (.split 16 1 (.split 51 1 (.step 75 (.step 3 (.step 9 (.close 18)))) (.step 3 (.close 9))) (.step 3 (.step 18 (.close 9)))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 26 (.step 3 (.step 32 (.step 40 (.step 57 (.close 3))))))))))) (.step 3 (.step 9 (.step 12 (.step 18 (.step 26 (.step 40 (.step 52 (.step 3 (.step 21 (.close 31))))))))))) (.step 3 (.step 9 (.step 18 (.step 15 (.step 26 (.step 15 (.close 31)))))))) (.step 9 (.step 12 (.step 15 (.step 3 (.close 18)))))))))))))
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
def root : Box := ⟨9820171823688425610039569090482797456649926138129194368449874104288401389214023664649810276977712471452660052382680213027651769637656179159989877735424, 22062609052407958992681534144408529078149464284810599849193356071069493960511744270264372286555483209881573866190262853298150857341065702834416838882854875285362554156635229025685296938291203035707535465499570506563584⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 18 (.step 21 (.step 53 (.step 57 (.step 62 (.split 72 2 (.split 12 1 (.split 21 1 (.split 34 1 (.step 53 (.split 36 1 (.split 16 1 (.split 42 1 (.split 54 1 (.split 72 1 (.split 12 0 (.step 18 (.close 53)) (.step 9 (.step 18 (.step 21 (.step 3 (.step 15 (.step 18 (.close 12)))))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 3 (.close 12))))))) (.step 9 (.step 21 (.step 22 (.step 26 (.step 32 (.step 53 (.step 3 (.close 15))))))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 15 (.step 31 (.close 12)))))))) (.step 3 (.step 18 (.step 9 (.close 12))))) (.step 3 (.step 9 (.step 21 (.step 31 (.close 12))))))) (.step 3 (.step 9 (.step 15 (.step 21 (.step 31 (.close 52))))))) (.step 3 (.step 9 (.step 18 (.step 12 (.close 52)))))) (.step 9 (.step 12 (.step 15 (.step 3 (.close 18)))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 31 (.step 32 (.step 40 (.step 52 (.step 53 (.step 15 (.step 31 (.close 57))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284810599849193356071069493960511744270264372286555483209881573866190262853298150857341065702834416838882854875285362554156635229025685296938291203035707535465499570506563584⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 50 2 (.split 54 2 (.step 18 (.split 59 2 (.reuse 0) (.run (.step 3 (.step 9 (.step 26 (.step 62 (.split 12 1 (.split 21 1 (.split 34 1 (.split 35 1 (.split 16 1 (.split 36 1 (.split 42 1 (.split 54 1 (.split 12 0 (.step 18 (.step 62 (.close 3))) (.step 9 (.step 18 (.step 26 (.step 3 (.step 15 (.step 18 (.close 12)))))))) (.step 9 (.step 22 (.step 26 (.step 57 (.close 3)))))) (.step 3 (.step 9 (.step 26 (.step 31 (.close 12)))))) (.step 3 (.step 9 (.step 26 (.step 31 (.close 12)))))) (.step 3 (.step 18 (.step 9 (.close 12))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 31 (.step 32 (.step 40 (.step 31 (.close 12)))))))))) (.step 3 (.step 9 (.step 15 (.step 26 (.close 31)))))) (.step 3 (.step 9 (.step 18 (.close 12))))) (.step 9 (.step 12 (.step 15 (.step 3 (.close 18))))))))))))) (.run (.step 9 (.step 12 (.step 18 (.step 9 (.step 21 (.step 15 (.step 22 (.step 26 (.step 32 (.step 57 (.close 3))))))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284810599849193356071069500353852775317416462156066609826286168039319259031159067816894519015595737941762844881672261628188192164351240233579054892913161726647907877788844032⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 49 2 (.reuse 0) (.run (.step 3 (.step 9 (.step 12 (.step 18 (.step 52 (.step 57 (.step 62 (.split 72 2 (.split 21 1 (.split 34 1 (.step 53 (.split 35 1 (.split 36 1 (.split 16 1 (.split 42 1 (.split 54 1 (.split 72 1 (.split 12 0 (.step 18 (.step 52 (.close 3))) (.step 9 (.step 12 (.step 3 (.close 17))))) (.step 9 (.step 12 (.step 18 (.step 26 (.step 3 (.step 18 (.close 21)))))))) (.step 9 (.step 12 (.step 18 (.step 52 (.close 3)))))) (.step 3 (.step 9 (.step 26 (.step 31 (.close 12)))))) (.step 3 (.step 18 (.step 9 (.close 12))))) (.step 3 (.step 9 (.step 31 (.close 12))))) (.step 9 (.step 12 (.step 18 (.step 21 (.step 31 (.step 32 (.step 40 (.step 52 (.close 26))))))))))) (.step 3 (.step 9 (.step 15 (.step 31 (.close 52)))))) (.step 3 (.step 9 (.step 12 (.step 18 (.close 52)))))) (.step 9 (.step 12 (.step 18 (.step 26 (.step 31 (.step 38 (.step 40 (.step 52 (.close 57)))))))))))))))))))
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
def root : Box := ⟨4294967296, 22062609052407958992681534144408529078149464284810599849193356071069500353852775317416462156066609826286168039323846028391047959917740657386342115644438014941607305078079426339952447104388864064605240828901976419860480⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 12 2 (.split 21 2 (.split 35 2 (.reuse 0) (.run (.step 9 (.step 18 (.step 21 (.step 29 (.step 31 (.step 38 (.step 57 (.step 62 (.split 49 2 (.split 59 1 (.split 12 1 (.split 21 1 (.split 49 1 (.split 16 1 (.split 51 1 (.split 54 1 (.step 3 (.step 18 (.step 38 (.close 3)))) (.step 9 (.step 3 (.step 18 (.step 21 (.step 32 (.step 38 (.close 3)))))))) (.step 3 (.close 9))) (.step 3 (.step 18 (.close 9)))) (.step 3 (.step 9 (.step 12 (.step 18 (.step 21 (.step 32 (.step 38 (.close 3))))))))) (.step 3 (.step 9 (.step 18 (.step 15 (.close 31)))))) (.step 9 (.step 12 (.step 15 (.step 3 (.close 18)))))) (.step 3 (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 32 (.step 38 (.step 18 (.step 12 (.step 18 (.step 38 (.step 40 (.close 52))))))))))))))) (.step 3 (.step 9 (.step 12 (.step 18 (.step 21 (.step 32 (.step 40 (.step 52 (.step 57 (.step 38 (.close 3)))))))))))))))))))))) (.run (.step 3 (.step 18 (.step 9 (.step 31 (.step 57 (.step 18 (.step 9 (.step 15 (.step 38 (.step 52 (.step 57 (.step 62 (.step 75 (.split 50 2 (.split 35 1 (.split 49 1 (.step 24 (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 12 (.step 18 (.step 24 (.close 52)))))) (.step 18 (.step 24 (.step 26 (.step 24 (.step 31 (.close 38))))))) (.step 3 (.step 18 (.step 52 (.step 12 (.close 53))))))))))))))))))))) (.run (.step 9 (.step 12 (.step 15 (.step 18 (.step 9 (.step 21 (.step 15 (.step 3 (.step 15 (.step 3 (.step 15 (.close 18))))))))))))))
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
def root : Box := ⟨4294967296, 22062609052407963891564844801750966025999865686450204371425138696287413569753975208630337497545696341547536145423928123879037069277050894686928090329889613554523733231213404360577442746977500149416645079816076246646784⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 31 (.split 6 2 (.reuse 0) (.run (.step 9 (.step 3 (.step 11 (.step 9 (.close 3)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part6.excludes
end FiveColour.Packed.ProjectedChunks.Case148
