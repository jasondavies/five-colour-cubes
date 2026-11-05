module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case142
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832574280906229382831699716614570754634512794335709871693923201840820290038169768138116761893194060645373078477048230120807774645289050960104006022000136767859572724767653888⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11593776385211095628535, 5789234131009374248507341982684158355876555513350053335929015326897327162342062193097593244396629436776638632267636611235444786831573185258760290656459859266733554791122816590519108237010294841316599838966919287400980022272, 0⟩]
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
def root : Box := ⟨4294967296, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457892568212888552226425244350168549660670571216294509138335113355051381558612491624687537352966322392137728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 34 1 (.split 36 1 (.split 42 1 (.split 65 1 (.split 72 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 8 0 (.step 31 (.split 63 1 (.split 64 1 (.step 3 (.step 31 (.step 3 (.step 12 (.close 18))))) (.step 67 (.close 3))) (.step 66 (.close 3)))) (.step 18 (.split 63 1 (.split 64 1 (.split 14 0 (.step 3 (.step 18 (.step 29 (.close 31)))) (.step 11 (.step 3 (.step 12 (.close 29))))) (.step 32 (.step 47 (.step 3 (.step 18 (.step 3 (.step 11 (.step 12 (.close 31))))))))) (.step 12 (.step 47 (.close 66)))))) (.step 18 (.step 11 (.step 67 (.step 69 (.step 31 (.step 12 (.step 3 (.step 18 (.step 29 (.close 31))))))))))) (.step 3 (.step 12 (.step 3 (.step 32 (.step 3 (.close 11))))))) (.step 3 (.step 12 (.step 3 (.step 22 (.close 11)))))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 9 (.step 31 (.step 69 (.split 51 1 (.split 63 1 (.split 64 1 (.step 3 (.step 29 (.step 69 (.step 3 (.step 18 (.close 12)))))) (.step 29 (.step 3 (.step 32 (.close 67))))) (.step 12 (.step 29 (.step 66 (.close 3))))) (.step 3 (.step 21 (.close 22)))))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 18 (.step 3 (.step 15 (.close 21))))))))) (.step 3 (.step 31 (.step 11 (.close 12))))) (.step 3 (.step 31 (.step 11 (.close 12))))) (.step 3 (.step 31 (.step 11 (.close 12))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2787593149816327892691964784081049483214848, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065245470636601468821202129487178557908062539215227685019654164137179044370505007104⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 12 (.step 18 (.step 27 (.split 34 1 (.split 36 1 (.split 42 1 (.split 51 1 (.step 77 (.split 65 1 (.split 67 1 (.split 64 1 (.split 71 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 35 1 (.step 11 (.step 75 (.step 3 (.step 12 (.close 17))))) (.step 12 (.step 29 (.step 11 (.step 3 (.step 17 (.close 31))))))) (.step 3 (.step 11 (.step 12 (.close 17))))) (.step 11 (.step 3 (.step 12 (.close 17))))) (.step 3 (.step 11 (.step 3 (.close 12))))) (.step 11 (.step 12 (.close 74)))) (.step 11 (.step 12 (.step 32 (.close 67))))) (.step 3 (.close 11))) (.step 3 (.step 11 (.step 12 (.close 17)))))) (.step 3 (.step 11 (.close 12)))) (.step 3 (.step 12 (.step 29 (.step 31 (.close 11)))))) (.step 3 (.step 29 (.step 31 (.step 11 (.close 12)))))) (.step 3 (.step 17 (.step 29 (.step 31 (.close 11))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨4294967296, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065249175983457062939455683758698835921113843854736985517703426779867297590653485056⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 26 1 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.reuse 0) (.run (.step 9 (.step 31 (.step 32 (.split 51 1 (.step 75 (.split 65 1 (.split 67 1 (.step 29 (.step 66 (.split 74 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.step 3 (.step 11 (.step 12 (.close 31))))) (.step 3 (.step 12 (.step 3 (.close 31))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 31)))))) (.step 3 (.step 18 (.step 12 (.step 3 (.close 31)))))) (.step 11 (.step 23 (.step 32 (.step 3 (.step 18 (.step 12 (.step 17 (.close 31))))))))))) (.step 3 (.close 21))) (.step 3 (.step 21 (.step 15 (.step 26 (.step 15 (.step 26 (.close 29))))))))) (.step 3 (.step 21 (.close 22))))))))) (.run (.step 3 (.step 18 (.step 29 (.close 32)))))) (.run (.step 3 (.step 18 (.step 29 (.close 32)))))) (.run (.step 3 (.step 18 (.step 29 (.close 32)))))) (.reuse 1)) (.run (.step 9 (.step 29 (.step 31 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.step 47 (.step 3 (.step 12 (.close 18))))) (.step 3 (.close 21))) (.step 3 (.close 29))) (.step 29 (.step 3 (.step 11 (.step 18 (.close 12)))))) (.step 12 (.step 29 (.step 3 (.step 18 (.step 23 (.step 11 (.step 18 (.close 66))))))))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 11 (.step 18 (.close 29))))) (.step 3 (.step 11 (.step 18 (.close 29))))) (.step 3 (.step 11 (.step 18 (.close 29))))) (.step 3 (.step 12 (.step 18 (.step 27 (.step 47 (.step 29 (.close 17)))))))))))))
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
def root : Box := ⟨4294967296, 23134333391815002265362563811600600460556613161528678648045928539396322387974384291591722443731300662071902249365944710170059852841261627357543610626425988314879996474471904065786614812784850635074215989056812763227053096960⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 74 2 (.split 8 1 (.reuse 0) (.run (.step 11 (.step 18 (.step 27 (.step 47 (.split 34 1 (.split 36 1 (.split 42 1 (.split 51 1 (.split 65 1 (.split 67 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 10 0 (.split 30 0 (.split 35 1 (.step 11 (.step 3 (.step 29 (.close 31)))) (.step 9 (.step 32 (.step 11 (.step 29 (.step 11 (.close 31))))))) (.step 3 (.close 11))) (.step 3 (.close 11))) (.step 11 (.step 9 (.step 29 (.step 31 (.close 32)))))) (.step 11 (.step 9 (.step 29 (.step 31 (.close 32)))))) (.step 11 (.step 9 (.step 29 (.close 66))))) (.step 3 (.close 11))) (.step 3 (.close 11))) (.step 3 (.close 11))) (.step 3 (.step 29 (.step 31 (.close 11))))) (.step 3 (.step 29 (.step 31 (.close 11))))) (.step 3 (.step 29 (.step 31 (.close 11))))))))))) (.run (.step 11 (.step 17 (.step 18 (.step 69 (.split 26 1 (.split 34 1 (.split 36 1 (.step 77 (.step 51 (.step 66 (.step 3 (.step 31 (.step 67 (.step 69 (.step 31 (.step 23 (.step 29 (.step 3 (.close 31)))))))))))) (.step 3 (.step 29 (.step 31 (.step 12 (.step 66 (.step 12 (.close 67)))))))) (.step 3 (.step 17 (.step 29 (.step 31 (.close 66)))))) (.step 3 (.step 23 (.step 29 (.step 66 (.step 67 (.step 69 (.step 29 (.step 18 (.step 29 (.step 74 (.close 12))))))))))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129104550223211085155933417796165742613846001337767629686350911020100308946480164634803895556640752157112741393033006778527877665006669902130351936231112488387826392139161771726684515734476322328543232⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 64 2 (.split 65 2 (.split 71 2 (.step 3 (.split 72 2 (.reuse 0) (.run (.step 9 (.step 29 (.step 31 (.step 38 (.step 69 (.split 8 1 (.split 14 1 (.split 16 1 (.split 51 1 (.step 75 (.step 66 (.step 3 (.step 18 (.step 67 (.step 3 (.step 11 (.close 12)))))))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 11 (.step 18 (.step 32 (.step 38 (.step 66 (.close 67)))))))) (.step 3 (.step 12 (.step 18 (.step 40 (.step 67 (.step 69 (.step 11 (.step 17 (.step 74 (.step 3 (.close 17)))))))))))) (.step 3 (.step 9 (.step 11 (.step 66 (.step 67 (.step 69 (.step 11 (.step 31 (.step 11 (.step 74 (.close 32)))))))))))))))))))) (.run (.step 11 (.step 12 (.step 29 (.step 32 (.step 47 (.step 51 (.step 66 (.step 3 (.step 67 (.step 69 (.step 74 (.close 3)))))))))))))) (.run (.step 3 (.step 18 (.step 29 (.step 31 (.step 11 (.step 74 (.step 75 (.step 77 (.split 72 1 (.split 74 1 (.step 68 (.step 66 (.step 67 (.step 74 (.split 8 1 (.step 68 (.step 3 (.step 29 (.step 15 (.close 21))))) (.step 3 (.close 11))))))) (.step 3 (.step 11 (.step 17 (.step 18 (.step 66 (.step 12 (.step 67 (.step 12 (.close 68)))))))))) (.step 3 (.step 26 (.step 29 (.step 31 (.step 38 (.step 66 (.step 21 (.step 67 (.step 21 (.close 68))))))))))))))))))))) (.run (.step 11 (.step 12 (.step 29 (.step 32 (.step 47 (.step 51 (.step 66 (.step 67 (.step 3 (.step 18 (.close 31)))))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832574280906229382831699716614570754634512794333002186445758343577164700113948962551248889181204408415666951908517624900818924895206682687477768418441184445321327187358384128⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 35 2 (.split 63 2 (.reuse 0) (.run (.step 11 (.step 12 (.step 29 (.step 32 (.step 47 (.step 51 (.step 66 (.step 3 (.step 18 (.close 31)))))))))))) (.run (.step 3 (.step 9 (.step 29 (.step 31 (.step 32 (.step 38 (.step 66 (.step 68 (.step 74 (.step 77 (.split 8 1 (.split 65 1 (.split 74 1 (.split 14 1 (.split 16 1 (.split 51 1 (.split 67 1 (.split 8 0 (.split 17 1 (.step 38 (.step 18 (.step 3 (.step 12 (.step 3 (.close 18)))))) (.step 3 (.step 18 (.step 32 (.close 38))))) (.step 9 (.step 18 (.step 32 (.step 38 (.close 11)))))) (.step 3 (.step 21 (.close 38)))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 11 (.step 18 (.step 32 (.close 38)))))) (.step 3 (.step 12 (.step 18 (.step 32 (.step 38 (.step 3 (.close 11)))))))) (.step 3 (.step 18 (.step 32 (.step 40 (.step 66 (.step 69 (.step 11 (.step 17 (.step 38 (.close 12))))))))))) (.step 3 (.step 21 (.step 31 (.close 38))))) (.step 3 (.step 9 (.step 11 (.step 32 (.step 66 (.step 74 (.split 16 0 (.split 17 0 (.step 38 (.close 11)) (.step 3 (.close 11))) (.step 3 (.close 11))))))))))))))))))))))
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
def root : Box := ⟨4294967296, 23134344433892286795713129104550232122101987226767832574280906229382831699716614570754634512794335709871693923201840820290038169768138116761893194060645373078477048230120807774645289050960104006022000136767859572724767653888⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.step 18 (.step 29 (.step 31 (.step 11 (.split 14 2 (.reuse 0) (.run (.step 3 (.step 11 (.step 12 (.step 17 (.step 18 (.step 67 (.step 68 (.step 74 (.step 75 (.split 35 2 (.split 26 1 (.split 65 1 (.split 72 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 35 1 (.split 51 1 (.step 17 (.step 3 (.step 12 (.step 3 (.step 17 (.step 23 (.step 29 (.close 31)))))))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 12 (.step 17 (.step 23 (.step 17 (.step 29 (.step 31 (.close 32))))))))) (.step 3 (.step 12 (.step 29 (.step 17 (.close 31)))))) (.step 3 (.step 29 (.step 31 (.step 12 (.close 17)))))) (.step 3 (.step 17 (.step 29 (.close 31))))) (.step 3 (.step 12 (.step 23 (.step 31 (.step 67 (.step 69 (.step 29 (.step 17 (.step 32 (.close 38))))))))))) (.step 3 (.step 12 (.close 17)))) (.step 3 (.step 12 (.step 23 (.step 29 (.step 67 (.step 74 (.split 16 0 (.step 29 (.close 17)) (.step 3 (.close 17)))))))))) (.step 3 (.step 12 (.step 23 (.step 29 (.step 31 (.step 32 (.step 38 (.step 74 (.step 17 (.step 3 (.close 31)))))))))))))))))))))))))))
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
end FiveColour.Packed.ProjectedChunks.Case142
