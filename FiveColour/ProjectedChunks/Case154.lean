module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case154
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832574280906229382831699716614570754634512794335709871693923201840820290038169768138116761893186649951661890240541121577767218619186441681085405025896775779204607767771873280⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11593776385211162737655, 5789234131009374248507346766749891419687529095235210954717691618139302379008043081853517209139218549379967658257974399757620346092362447857049156240917920953324949553008476071530732724464983909928675585042487584861087335424, 0⟩]
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
def root : Box := ⟨4294967296, 11567172216946143397859013989258505539824339634696057382705615913892062467392389867064169725005978115572170783644655083513655678709637670585148021916260989356687643223936392247567260785296893862267327160421609294572367642624⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 72 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 10 1 (.split 14 0 (.step 31 (.split 63 1 (.step 3 (.split 22 0 (.step 31 (.step 3 (.close 18))) (.step 18 (.close 31)))) (.step 66 (.step 3 (.step 12 (.step 21 (.step 18 (.close 31)))))))) (.step 18 (.split 63 1 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.step 67 (.step 3 (.step 12 (.step 3 (.close 18))))) (.step 3 (.close 11))) (.step 3 (.step 12 (.step 3 (.close 18))))) (.step 3 (.step 12 (.step 3 (.step 18 (.close 31)))))) (.step 3 (.step 18 (.step 12 (.close 31))))) (.step 12 (.close 3))))) (.step 3 (.close 12))) (.step 18 (.split 63 1 (.split 64 1 (.split 34 0 (.step 11 (.step 69 (.step 3 (.step 18 (.step 3 (.close 12)))))) (.step 3 (.step 17 (.step 3 (.step 18 (.close 31)))))) (.step 11 (.step 32 (.step 67 (.close 3))))) (.step 11 (.step 12 (.step 66 (.close 3))))))) (.step 3 (.step 12 (.step 3 (.step 21 (.step 3 (.close 66))))))) (.step 3 (.step 12 (.step 3 (.step 21 (.step 3 (.close 36))))))) (.step 3 (.step 11 (.close 9)))) (.step 9 (.step 31 (.step 69 (.split 51 1 (.split 63 1 (.split 64 1 (.step 3 (.split 16 0 (.step 29 (.step 69 (.step 3 (.step 31 (.step 3 (.close 12)))))) (.step 3 (.step 18 (.step 31 (.close 12)))))) (.step 29 (.step 32 (.step 3 (.step 67 (.close 3)))))) (.step 12 (.step 29 (.step 66 (.close 3))))) (.step 3 (.step 21 (.close 22)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4294967296, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065243617963173671762075352351418418901535493098898126606681977907623262608661938176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 65 1 (.reuse 0) (.run (.step 3 (.step 66 (.step 67 (.step 74 (.step 18 (.step 3 (.step 15 (.close 21)))))))))) (.run (.step 3 (.step 31 (.step 12 (.close 66)))))) (.run (.step 3 (.step 31 (.step 12 (.close 66)))))) (.run (.step 3 (.step 31 (.step 12 (.close 66)))))) (.run (.step 9 (.step 31 (.step 32 (.split 51 1 (.split 65 1 (.split 67 1 (.split 72 1 (.split 16 0 (.step 29 (.split 74 1 (.split 17 0 (.split 22 0 (.split 14 0 (.split 51 0 (.step 31 (.step 12 (.step 32 (.step 31 (.close 3))))) (.step 21 (.step 3 (.step 15 (.close 26))))) (.step 12 (.step 32 (.step 3 (.step 12 (.close 31)))))) (.step 31 (.step 12 (.close 32)))) (.step 31 (.step 12 (.step 18 (.step 12 (.step 18 (.close 32))))))) (.step 23 (.step 32 (.step 66 (.step 31 (.step 69 (.step 3 (.step 12 (.step 17 (.close 31))))))))))) (.step 21 (.step 31 (.step 32 (.step 18 (.step 12 (.close 38))))))) (.step 29 (.close 38))) (.step 3 (.step 21 (.close 38)))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 21 (.close 22))))))))) (.run (.step 3 (.step 18 (.step 32 (.step 38 (.step 32 (.close 66)))))))) (.run (.step 3 (.step 18 (.step 32 (.step 38 (.step 32 (.close 66)))))))) (.run (.step 3 (.step 18 (.step 32 (.step 38 (.close 66)))))))
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
def root : Box := ⟨4294967296, 23134333391815002265362563811600600460556613161528678648045928539396322387974384291591722443731300662071902249365944710170059852841261627357543605068405704923702616143064623648767037855825586684327138468315321539509306261504⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 74 2 (.split 14 1 (.reuse 0) (.run (.step 12 (.step 18 (.split 34 1 (.step 27 (.split 36 1 (.split 42 1 (.split 51 1 (.split 65 1 (.split 67 1 (.split 74 1 (.split 34 0 (.step 11 (.split 35 1 (.split 72 1 (.split 36 0 (.split 42 0 (.split 35 0 (.split 30 0 (.step 12 (.step 3 (.step 17 (.close 3)))) (.step 17 (.close 3))) (.step 12 (.step 23 (.close 17)))) (.step 18 (.step 12 (.close 32)))) (.step 18 (.step 12 (.step 31 (.close 32))))) (.step 12 (.step 23 (.step 67 (.step 17 (.step 69 (.step 3 (.close 17)))))))) (.step 12 (.step 23 (.step 32 (.step 17 (.step 18 (.step 38 (.close 17))))))))) (.step 18 (.step 12 (.step 31 (.step 17 (.close 32)))))) (.step 11 (.step 17 (.close 31)))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 12 (.step 31 (.close 17))))) (.step 3 (.step 31 (.step 12 (.close 17)))))) (.step 3 (.step 31 (.step 12 (.close 17))))))))) (.run (.step 11 (.step 18 (.step 69 (.step 77 (.split 34 1 (.step 11 (.split 35 1 (.split 36 1 (.split 42 1 (.split 51 1 (.step 77 (.step 66 (.step 67 (.step 3 (.close 31))))) (.step 3 (.step 36 (.step 12 (.close 51))))) (.step 3 (.step 31 (.step 66 (.step 12 (.step 67 (.step 12 (.close 74)))))))) (.step 3 (.step 31 (.step 66 (.step 12 (.step 67 (.step 12 (.close 74)))))))) (.step 3 (.step 23 (.step 31 (.step 32 (.step 66 (.step 69 (.step 74 (.close 77)))))))))) (.step 3 (.step 31 (.step 17 (.step 66 (.close 67))))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832574280906229382831699716614570754634512794333002186445758343577160113116716982408225667539408246221501967601158956931291032697950951882461640701747523666723883218238439424⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 63 2 (.split 64 2 (.split 65 2 (.split 71 2 (.step 3 (.split 72 2 (.reuse 0) (.run (.step 9 (.step 31 (.step 69 (.step 75 (.split 14 1 (.split 16 1 (.step 29 (.split 17 1 (.split 22 1 (.split 51 1 (.step 75 (.step 66 (.step 67 (.step 3 (.step 12 (.close 18)))))) (.step 3 (.step 22 (.step 21 (.close 51))))) (.step 3 (.step 18 (.step 66 (.step 32 (.step 67 (.step 32 (.close 74)))))))) (.step 3 (.step 18 (.step 66 (.step 32 (.step 67 (.step 32 (.close 74))))))))) (.step 3 (.step 18 (.step 38 (.step 66 (.close 67)))))) (.step 3 (.step 12 (.step 18 (.step 29 (.step 40 (.step 67 (.step 69 (.step 74 (.close 75))))))))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 69 (.step 66 (.step 67 (.step 74 (.close 3))))))))))) (.run (.step 3 (.step 18 (.step 31 (.step 74 (.split 72 2 (.split 74 2 (.step 68 (.step 74 (.split 14 1 (.step 68 (.step 66 (.step 67 (.step 3 (.step 31 (.close 21)))))) (.step 3 (.step 12 (.close 17)))))) (.step 3 (.step 17 (.step 18 (.step 66 (.step 67 (.step 68 (.step 12 (.step 74 (.step 12 (.close 77))))))))))) (.step 3 (.step 26 (.step 31 (.step 38 (.step 66 (.step 67 (.step 68 (.step 21 (.step 74 (.step 21 (.close 75)))))))))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 67 (.step 68 (.step 69 (.step 66 (.step 67 (.step 3 (.step 29 (.close 31)))))))))))))) (.run (.step 12 (.step 32 (.step 47 (.step 51 (.step 66 (.step 68 (.step 69 (.step 66 (.step 3 (.step 11 (.close 18)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4181389724724491839037947176121572077338624, 23134344433892286795713129104550232122101987226767832574280906229382831699716614570754634512794333002186445758343577164700113948962551248889181198850395383560731137293493538507875632513321363633999256355668614184514799796224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 11 (.step 12 (.step 17 (.step 18 (.step 67 (.step 74 (.step 77 (.step 68 (.split 35 2 (.split 72 2 (.split 65 1 (.split 34 1 (.step 11 (.split 35 1 (.split 36 1 (.split 42 1 (.split 51 1 (.split 67 1 (.step 17 (.step 12 (.step 67 (.step 3 (.step 17 (.step 23 (.step 31 (.close 32)))))))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 31 (.step 12 (.close 17))))) (.step 3 (.step 31 (.step 12 (.close 17))))) (.step 3 (.step 12 (.step 23 (.step 31 (.step 32 (.step 17 (.step 69 (.step 17 (.close 38))))))))))) (.step 3 (.step 17 (.step 31 (.close 12))))) (.step 3 (.step 12 (.step 17 (.close 67))))) (.step 3 (.step 11 (.step 12 (.step 23 (.step 31 (.step 38 (.step 67 (.step 69 (.step 74 (.split 16 0 (.step 75 (.close 17)) (.step 3 (.close 17))))))))))))) (.step 3 (.step 11 (.step 12 (.step 23 (.step 31 (.step 32 (.step 38 (.step 74 (.split 16 0 (.split 17 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))))))))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832574280906229382831699716614570754634512794335709871693923201840820290038169768138116761893186649951661890240541121577767218619186441681085405025896775779204607767771873280⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.step 18 (.step 31 (.split 14 2 (.split 35 2 (.reuse 0) (.run (.step 3 (.step 9 (.step 31 (.step 32 (.step 38 (.step 66 (.step 74 (.step 75 (.step 68 (.split 74 2 (.split 65 1 (.split 14 1 (.split 16 1 (.step 29 (.split 17 1 (.split 22 1 (.split 51 1 (.split 67 1 (.step 38 (.step 32 (.step 66 (.step 3 (.step 23 (.step 12 (.step 3 (.close 18)))))))) (.step 3 (.step 21 (.close 38)))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 18 (.step 32 (.close 38))))) (.step 3 (.step 18 (.step 32 (.close 38)))))) (.step 3 (.step 18 (.step 32 (.close 38))))) (.step 3 (.step 12 (.step 18 (.step 29 (.step 32 (.step 40 (.step 38 (.step 69 (.step 38 (.close 17))))))))))) (.step 3 (.step 21 (.step 31 (.step 38 (.close 66)))))) (.step 3 (.step 11 (.step 17 (.step 18 (.step 23 (.step 32 (.step 66 (.step 69 (.step 74 (.split 16 0 (.split 17 0 (.step 38 (.close 12)) (.step 3 (.step 74 (.step 12 (.step 38 (.close 77)))))) (.step 3 (.step 18 (.close 38))))))))))))))))))))))))) (.reuse 1))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case154
