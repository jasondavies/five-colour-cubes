module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case42
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342785607606468608⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
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
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863332063217099735612567131388118500908379528921477156545793822902762132187825316200486535693424031915339246868117064239898638130610176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 65 1 (.split 72 1 (.split 8 0 (.split 16 0 (.split 17 0 (.step 3 (.step 7 (.split 10 0 (.step 75 (.step 3 (.step 7 (.close 17)))) (.step 3 (.close 7))))) (.step 7 (.step 3 (.close 19)))) (.step 7 (.step 3 (.step 11 (.step 67 (.step 7 (.close 19))))))) (.step 11 (.step 3 (.split 16 0 (.split 17 0 (.split 10 0 (.split 22 0 (.step 3 (.step 11 (.close 29))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 7 (.step 3 (.close 11)))) (.step 11 (.step 3 (.close 7))))))) (.step 29 (.split 74 1 (.step 3 (.step 75 (.close 3))) (.step 11 (.step 3 (.close 69)))))) (.step 3 (.split 34 0 (.split 16 0 (.step 3 (.step 74 (.close 3))) (.step 3 (.step 11 (.close 19)))) (.step 3 (.step 15 (.close 29)))))) (.step 74 (.step 3 (.step 23 (.step 11 (.step 3 (.step 17 (.step 3 (.close 29))))))))) (.step 3 (.step 7 (.close 3)))) (.step 67 (.step 3 (.step 67 (.split 65 1 (.split 72 1 (.step 3 (.step 11 (.step 3 (.close 17)))) (.step 29 (.step 3 (.step 11 (.step 3 (.close 17)))))) (.step 3 (.close 29))))))) (.step 66 (.step 3 (.step 66 (.split 65 1 (.split 72 1 (.step 3 (.step 11 (.step 3 (.close 19)))) (.step 29 (.step 3 (.step 11 (.step 3 (.close 19)))))) (.step 3 (.close 11))))))) (.step 3 (.step 55 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 51))) (.step 3 (.close 51)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284971109347745694313144495698113784064867572264212253099242730040848167805142015991150995061630097966142719000576⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 3 (.step 55 (.split 51 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 7 (.close 3)))))))) (.run (.step 7 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.split 72 1 (.step 45 (.step 3 (.close 7))) (.step 29 (.step 45 (.close 3)))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 37 (.step 11 (.close 39)))))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.close 39)))))))) (.step 29 (.step 69 (.step 3 (.step 37 (.close 11)))))) (.step 3 (.step 29 (.step 15 (.step 39 (.step 15 (.step 45 (.close 69)))))))) (.step 29 (.step 67 (.step 3 (.close 45))))) (.step 29 (.step 66 (.close 3)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973457890328468146372385178710573401894947946761161419113437331819700014167130599594458760628482734845750935552⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.reuse 0) (.run (.step 7 (.split 42 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.split 14 0 (.step 7 (.step 29 (.step 7 (.step 15 (.close 37))))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 37 (.step 11 (.close 39)))))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 17 (.step 37 (.close 39)))))))) (.step 29 (.step 51 (.close 74)))) (.step 3 (.step 29 (.step 15 (.close 39))))) (.step 29 (.step 51 (.step 67 (.close 3))))) (.step 29 (.step 51 (.step 66 (.close 3))))) (.step 39 (.split 63 1 (.split 64 1 (.step 39 (.step 3 (.step 7 (.step 29 (.step 45 (.step 11 (.close 37))))))) (.step 29 (.step 67 (.step 74 (.step 45 (.close 3)))))) (.step 29 (.step 37 (.step 51 (.step 66 (.close 3)))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878621701000088910984550333021447796084629210604308528502053798559259427776027913338243044605952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.step 66 (.split 64 1 (.split 65 1 (.split 71 1 (.split 74 1 (.split 8 0 (.split 72 1 (.split 14 0 (.step 7 (.step 15 (.close 29))) (.step 3 (.step 7 (.step 29 (.close 37))))) (.step 29 (.step 37 (.close 3)))) (.step 3 (.step 7 (.step 29 (.step 11 (.close 37)))))) (.step 3 (.step 7 (.step 29 (.step 11 (.step 17 (.close 37))))))) (.step 29 (.step 66 (.step 74 (.close 3))))) (.step 3 (.step 15 (.step 29 (.close 37))))) (.step 29 (.step 66 (.step 67 (.step 3 (.close 37))))))) (.step 37 (.split 63 1 (.split 64 1 (.step 45 (.step 29 (.step 39 (.step 66 (.step 3 (.step 37 (.step 3 (.step 37 (.close 11))))))))) (.step 29 (.step 66 (.step 45 (.step 39 (.close 67)))))) (.step 15 (.step 29 (.step 37 (.step 11 (.close 66)))))))) (.step 37 (.split 63 1 (.split 64 1 (.step 39 (.step 3 (.step 7 (.step 29 (.step 37 (.close 11)))))) (.step 29 (.step 66 (.step 39 (.step 3 (.step 37 (.step 39 (.step 11 (.close 17))))))))) (.step 15 (.step 29 (.step 37 (.step 11 (.close 66)))))))) (.step 29 (.step 37 (.step 38 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029264195332239926022211708720090624189349957806788649020801559302242304⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 75 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.split 71 1 (.split 74 1 (.step 3 (.split 8 0 (.step 7 (.step 19 (.close 37))) (.step 3 (.step 11 (.step 3 (.close 37)))))) (.step 11 (.step 3 (.step 38 (.step 3 (.close 19)))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.step 15 (.step 29 (.step 15 (.close 38)))))) (.step 29 (.step 3 (.step 67 (.close 3))))) (.step 29 (.step 66 (.close 3))))) (.step 3 (.step 40 (.step 9 (.step 29 (.step 38 (.close 3))))))) (.step 3 (.step 9 (.close 7)))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))) (.step 7 (.step 29 (.step 38 (.step 3 (.close 7)))))))) (.reuse 1)) (.run (.step 3 (.step 7 (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 67))) (.step 3 (.close 66))) (.step 3 (.step 38 (.step 3 (.close 7))))))))) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 29 (.step 74 (.step 3 (.step 11 (.close 19))))) (.step 3 (.close 7))) (.step 3 (.step 15 (.close 29)))) (.step 29 (.step 3 (.step 11 (.step 23 (.step 19 (.close 67))))))) (.step 29 (.step 3 (.step 23 (.step 11 (.close 66)))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 9 (.close 7)))) (.step 3 (.step 7 (.step 29 (.step 3 (.close 7)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2993155353253689176481146537402947624255351995498496, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938695453085160407504507633397016531618709303201890304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.step 19 (.close 20))) (.split 26 0 (.step 7 (.step 11 (.step 19 (.step 3 (.close 7))))) (.step 3 (.step 7 (.step 19 (.close 20)))))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 19 (.close 20)))))))) (.step 11 (.step 51 (.close 74)))) (.step 3 (.step 11 (.step 19 (.close 20))))) (.step 11 (.step 51 (.step 67 (.close 3))))) (.step 11 (.step 51 (.step 66 (.close 3))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 7 (.step 11 (.step 19 (.step 25 (.close 29)))))))))) (.step 3 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 20 (.step 67 (.step 20 (.close 74))))))))))))) (.step 25 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 20 (.step 3 (.step 7 (.step 11 (.step 25 (.step 19 (.close 29))))))) (.step 11 (.step 19 (.step 20 (.step 3 (.step 25 (.step 29 (.close 67)))))))) (.step 11 (.step 66 (.step 74 (.step 25 (.close 3)))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 20 (.step 25 (.step 38 (.close 66)))))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 20 (.step 19 (.step 66 (.step 20 (.close 67))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2923003274661805836407369665432566039314012569600, 11567172216946143397854115110619787389832519688183215467338191998800103240901699334777371649459497115392589330916867360103971340889514378725827946737335343814281715990194784066358889545898176597895378936600373931690300538880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.step 67 (.split 26 1 (.split 35 1 (.split 63 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 8 0 (.split 17 0 (.step 7 (.close 19)) (.step 19 (.step 7 (.close 19)))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.step 25 (.close 29)))))))) (.step 11 (.step 67 (.step 74 (.close 3))))) (.step 3 (.step 11 (.close 19)))) (.step 11 (.step 66 (.step 3 (.close 19))))) (.step 3 (.step 38 (.step 11 (.step 23 (.step 29 (.step 38 (.step 19 (.close 66))))))))) (.step 3 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 19 (.step 66 (.step 19 (.step 20 (.step 67 (.close 69))))))))))))))) (.step 19 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 25 (.step 11 (.step 20 (.step 67 (.step 3 (.step 19 (.step 3 (.step 19 (.step 25 (.close 29)))))))))) (.step 11 (.step 19 (.step 29 (.close 67))))) (.step 11 (.step 66 (.step 19 (.close 3))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 19 (.step 20 (.step 66 (.step 19 (.close 67)))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914586797738407425837081849247901728959134433280⟩
def references : Fin 3 → Box := ![Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 3 := (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 8 0 (.split 16 0 (.step 7 (.step 19 (.close 20))) (.step 25 (.step 3 (.step 7 (.close 19))))) (.step 11 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.step 19 (.close 20)))))))) (.step 11 (.step 69 (.step 3 (.step 19 (.close 29)))))) (.step 3 (.step 11 (.step 19 (.step 20 (.step 19 (.step 25 (.close 69)))))))) (.step 11 (.step 67 (.close 3)))) (.step 11 (.step 66 (.step 3 (.close 25))))) (.step 3 (.step 66 (.step 67 (.step 69 (.step 40 (.step 29 (.step 11 (.step 38 (.step 3 (.step 19 (.close 20)))))))))))) (.step 3 (.step 29 (.step 3 (.step 11 (.step 23 (.step 29 (.step 3 (.step 66 (.step 67 (.step 20 (.step 19 (.close 69)))))))))))))))) (.reuse 1)) (.step 7 (.split 17 1 (.reuse 2) (.run (.step 19 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 20 (.step 3 (.step 7 (.step 11 (.step 19 (.step 20 (.close 29))))))) (.step 11 (.step 19 (.step 29 (.close 67))))) (.step 11 (.step 66 (.step 19 (.close 3))))) (.step 3 (.step 7 (.step 11 (.step 19 (.step 29 (.close 38))))))) (.step 3 (.step 7 (.step 11 (.step 29 (.step 19 (.step 20 (.step 66 (.close 67))))))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2787593149816327892691964784081047335731200, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029264195332239926022211708721484420764258121753134631412842081896366080⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.step 77 (.split 42 1 (.split 65 1 (.split 67 1 (.step 11 (.split 71 1 (.split 72 1 (.step 3 (.split 10 0 (.split 16 0 (.split 34 0 (.step 3 (.step 17 (.close 29))) (.step 17 (.step 3 (.close 29)))) (.step 17 (.close 3))) (.step 3 (.close 7)))) (.step 23 (.step 29 (.step 3 (.step 17 (.step 3 (.close 37))))))) (.step 74 (.close 3)))) (.step 3 (.close 7))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 7 (.step 29 (.step 23 (.step 11 (.step 7 (.step 37 (.step 39 (.close 69))))))))))) (.step 3 (.step 7 (.step 74 (.step 7 (.step 29 (.step 17 (.step 37 (.step 11 (.step 17 (.close 39))))))))))) (.step 11 (.step 17 (.step 3 (.close 67))))) (.step 11 (.step 17 (.step 66 (.close 3))))) (.step 3 (.step 7 (.step 23 (.step 11 (.step 17 (.close 3))))))) (.step 3 (.step 7 (.step 11 (.close 7))))) (.step 3 (.step 66 (.step 67 (.step 74 (.step 75 (.step 77 (.step 29 (.step 38 (.step 11 (.step 3 (.step 17 (.step 3 (.close 37)))))))))))))) (.step 3 (.step 7 (.step 17 (.step 29 (.step 38 (.step 40 (.step 66 (.step 67 (.step 7 (.step 37 (.step 11 (.step 17 (.close 37)))))))))))))) (.step 3 (.step 7 (.step 67 (.split 63 1 (.step 7 (.step 3 (.close 11))) (.step 3 (.step 11 (.close 17)))))))) (.step 3 (.step 29 (.step 11 (.step 17 (.step 23 (.step 29 (.step 17 (.close 66))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2417851639229260496896000, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342785607606468608⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 11 (.split 10 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 36 1 (.split 65 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 10 0 (.step 11 (.step 3 (.step 29 (.close 37)))) (.step 3 (.step 7 (.step 11 (.close 3))))) (.step 9 (.step 29 (.step 11 (.step 3 (.step 37 (.close 39))))))) (.step 11 (.step 9 (.step 29 (.step 37 (.step 66 (.close 69))))))) (.step 3 (.close 7))) (.step 3 (.close 11))) (.step 3 (.step 7 (.step 29 (.step 40 (.step 74 (.step 7 (.step 11 (.step 45 (.step 11 (.close 37))))))))))) (.step 11 (.step 3 (.step 9 (.step 29 (.close 67)))))) (.step 11 (.step 3 (.step 9 (.step 29 (.close 66)))))) (.step 3 (.step 7 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 7 (.step 11 (.close 7))))) (.step 3 (.step 9 (.step 29 (.step 38 (.step 11 (.step 38 (.close 66)))))))) (.step 3 (.step 7 (.step 29 (.step 38 (.step 40 (.step 66 (.step 67 (.step 7 (.step 37 (.step 11 (.step 37 (.step 39 (.close 69)))))))))))))) (.step 3 (.step 7 (.step 11 (.step 3 (.close 7)))))) (.step 3 (.step 9 (.step 29 (.close 11))))) (.step 3 (.step 7 (.step 11 (.step 3 (.close 7))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11567172216946143397859013993930444732269467538584617106942714230582728458814915235977262863334838594479104592284973460186066828878623738036065247323310029265880328906622938696914588191534982335268680004384342785607606468608⟩
def references : Fin 3 → Box := ![Part7.root, Part8.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 8 1 (.split 10 1 (.split 14 1 (.reuse 0) (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 1) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17)))))))) (.run (.step 7 (.step 11 (.step 17 (.step 3 (.step 7 (.close 17))))))))) (.run (.step 3 (.step 7 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 3 (.step 7 (.close 3))) (.step 3 (.close 66))) (.step 3 (.close 66))) (.step 3 (.step 66 (.split 64 1 (.step 7 (.step 3 (.close 29))) (.step 3 (.step 29 (.close 38))))))) (.step 3 (.step 29 (.step 3 (.close 7))))) (.step 3 (.step 17 (.step 3 (.close 7))))))))) (.reuse 2))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case42
