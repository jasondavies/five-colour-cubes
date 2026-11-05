module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case103
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934408045371882287302473502903020006576514178411409702912⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002252476348160558710932874512254569726618848087032101076331750052553453812932182870694041564504618667054178653859115548130406301696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 67 1 (.step 74 (.split 72 1 (.split 74 1 (.split 71 1 (.step 3 (.split 8 0 (.step 7 (.step 3 (.step 18 (.close 29)))) (.step 3 (.step 11 (.step 3 (.close 29)))))) (.step 74 (.close 3))) (.step 11 (.step 69 (.split 71 1 (.split 16 0 (.step 3 (.step 18 (.step 17 (.close 29)))) (.step 18 (.close 3))) (.step 69 (.close 74)))))) (.step 69 (.step 29 (.step 69 (.split 71 1 (.split 8 0 (.step 3 (.step 21 (.step 18 (.close 31)))) (.step 3 (.step 18 (.close 31)))) (.step 69 (.close 74)))))))) (.step 3 (.step 69 (.step 3 (.close 7))))) (.step 3 (.step 74 (.split 72 1 (.step 18 (.split 74 1 (.step 3 (.step 15 (.close 21))) (.step 3 (.close 11)))) (.step 3 (.step 26 (.step 29 (.step 15 (.close 21))))))))) (.step 3 (.step 67 (.step 69 (.step 67 (.split 65 1 (.step 75 (.step 77 (.split 17 0 (.step 75 (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 11 (.close 18)))))) (.step 3 (.close 67)))))))) (.step 66 (.step 3 (.step 69 (.step 66 (.split 65 1 (.step 75 (.step 77 (.split 16 0 (.step 3 (.step 23 (.step 11 (.step 3 (.step 18 (.close 29)))))) (.step 3 (.step 11 (.close 18)))))) (.step 3 (.close 66)))))))) (.step 3 (.step 51 (.step 3 (.split 67 1 (.step 51 (.step 3 (.close 7))) (.step 3 (.close 7))))))) (.step 3 (.step 9 (.step 27 (.step 47 (.step 3 (.split 51 1 (.split 67 1 (.step 47 (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.close 7))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190274620753833575924561030313746308762853712136721477652790359784706412522208524193659101900297139071746048⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 38 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 42 1 (.split 65 1 (.split 74 1 (.split 51 1 (.step 75 (.split 67 1 (.step 29 (.split 8 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 36 0 (.step 66 (.step 67 (.step 3 (.split 51 0 (.step 38 (.close 3)) (.step 3 (.step 15 (.close 3))))))) (.step 31 (.step 38 (.step 3 (.close 66))))) (.step 31 (.step 40 (.step 31 (.step 66 (.step 18 (.step 67 (.step 18 (.close 38))))))))) (.step 21 (.step 38 (.step 18 (.close 66))))) (.step 31 (.step 38 (.step 3 (.close 66))))) (.step 9 (.step 66 (.step 67 (.step 38 (.step 74 (.close 38)))))))) (.step 3 (.step 21 (.close 29))))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 66 (.step 67 (.step 69 (.step 11 (.step 23 (.step 29 (.step 38 (.step 74 (.step 31 (.step 17 (.close 38))))))))))))) (.step 3 (.step 21 (.step 29 (.step 31 (.close 38)))))) (.step 3 (.step 29 (.step 31 (.step 3 (.step 26 (.close 38))))))) (.step 3 (.step 29 (.step 31 (.step 3 (.step 38 (.close 3))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317931532982145198307445651409955427715946951860159762908340105950884515549863655283682285977600⟩
def references : Fin 2 → Box := ![Part0.root, Part1.root]
def proof : Chunks.Proof 2 := (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 75 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 31 (.step 3 (.close 7))) (.step 29 (.step 31 (.step 11 (.close 74)))))) (.step 3 (.step 29 (.step 31 (.step 11 (.close 67)))))) (.step 3 (.step 29 (.step 31 (.close 66)))))))))) (.run (.step 7 (.step 31 (.step 75 (.split 42 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 74 1 (.step 31 (.step 3 (.close 7))) (.step 3 (.step 29 (.step 31 (.close 11))))))) (.step 3 (.step 29 (.step 31 (.step 11 (.close 67)))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 7 (.step 31 (.step 7 (.step 29 (.step 3 (.step 26 (.step 38 (.close 39)))))))))))))) (.reuse 1)) (.run (.step 7 (.step 31 (.step 75 (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 31 (.step 3 (.close 7))) (.step 29 (.step 31 (.step 11 (.close 17)))))) (.step 3 (.step 29 (.step 31 (.step 11 (.step 66 (.step 11 (.step 17 (.close 67))))))))) (.step 3 (.step 29 (.step 31 (.close 66))))) (.step 7 (.step 31 (.step 7 (.step 29 (.step 3 (.step 26 (.close 37)))))))) (.step 7 (.step 31 (.close 37)))) (.step 3 (.step 29 (.step 31 (.close 37))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934405049293522971358341366485916627923441770452752531456⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.split 30 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.step 29 (.close 31)))))) (.step 3 (.step 18 (.step 29 (.close 31))))) (.step 3 (.step 18 (.step 31 (.close 66))))) (.step 3 (.step 29 (.close 31))))))))) (.run (.step 3 (.step 9 (.step 29 (.step 66 (.step 67 (.step 74 (.split 65 1 (.split 74 1 (.split 30 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.step 3 (.step 11 (.close 18)))) (.step 3 (.close 21))) (.step 29 (.step 11 (.step 3 (.close 18))))) (.step 29 (.step 18 (.step 23 (.step 11 (.step 18 (.close 66))))))) (.step 3 (.step 21 (.close 22)))) (.step 3 (.close 29))) (.step 3 (.step 27 (.step 47 (.step 29 (.step 66 (.step 18 (.step 29 (.step 67 (.step 18 (.step 69 (.close 74)))))))))))) (.step 3 (.step 29 (.close 66)))))))))))) (.run (.step 7 (.step 18 (.step 77 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.step 29 (.close 74)))))) (.step 3 (.step 11 (.step 18 (.step 29 (.close 67)))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 11 (.step 18 (.step 29 (.step 38 (.step 66 (.step 38 (.close 67))))))))) (.step 3 (.step 18 (.step 29 (.step 66 (.close 67)))))))))))
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
def root : Box := ⟨2787593149816327892691964784081048409473024, 11567177732598406499846312727330591355628391050586285916292165444542790666436328029106176130320925639815257254992343318420341491185652728743603320572156652862959889510396621833839583833547889460778629865340754452471565254656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 35 1 (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 51 1 (.step 77 (.split 67 1 (.step 11 (.split 10 0 (.step 67 (.split 16 0 (.step 74 (.split 30 0 (.step 66 (.split 17 0 (.split 26 0 (.step 3 (.close 17)) (.step 23 (.step 17 (.step 3 (.close 29))))) (.step 3 (.close 17)))) (.step 3 (.close 17)))) (.step 17 (.step 18 (.close 29))))) (.step 17 (.step 3 (.step 29 (.close 66)))))) (.step 3 (.step 11 (.close 17))))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 11 (.step 17 (.step 29 (.step 31 (.step 17 (.close 66)))))))) (.step 3 (.step 29 (.step 11 (.step 17 (.step 31 (.step 17 (.close 66)))))))) (.step 3 (.step 17 (.step 29 (.step 31 (.step 11 (.close 17))))))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 31 (.step 66 (.step 67 (.step 69 (.step 11 (.step 23 (.step 29 (.step 17 (.step 74 (.close 17)))))))))))) (.step 3 (.step 11 (.step 17 (.step 18 (.close 34)))))) (.step 3 (.step 31 (.step 38 (.step 66 (.step 67 (.step 74 (.step 75 (.step 77 (.split 16 0 (.step 29 (.step 11 (.step 23 (.split 10 0 (.split 34 0 (.split 30 0 (.split 17 0 (.step 38 (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.close 17))) (.step 3 (.step 17 (.close 31)))) (.step 3 (.close 17)))))) (.step 3 (.step 11 (.step 17 (.close 29)))))))))))))) (.step 3 (.step 27 (.step 29 (.step 47 (.step 66 (.step 67 (.step 74 (.step 77 (.step 29 (.step 3 (.close 17)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934408045371882287302473500367716388268416146159653879808⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 77 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 72 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 11 (.step 18 (.close 29))))))) (.step 3 (.step 11 (.step 18 (.step 29 (.close 67)))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 11 (.step 18 (.step 29 (.step 38 (.step 66 (.step 38 (.close 67))))))))) (.step 3 (.step 18 (.step 29 (.step 66 (.close 67)))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 3 (.step 17 (.close 20))))))))))))) (.run (.step 7 (.step 18 (.step 77 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.step 29 (.close 38)))))) (.step 3 (.step 11 (.step 18 (.step 29 (.close 67)))))) (.step 3 (.step 11 (.step 18 (.close 66))))) (.step 3 (.step 11 (.step 18 (.step 29 (.step 38 (.step 66 (.close 67)))))))) (.step 3 (.step 18 (.step 29 (.step 66 (.close 67)))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 3 (.step 17 (.close 19)))))))) (.step 7 (.step 18 (.close 19))))))))) (.step 3 (.step 31 (.step 27 (.step 17 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 1) (.run (.step 3 (.step 11 (.step 17 (.step 3 (.step 17 (.close 18)))))))) (.run (.step 3 (.step 11 (.step 17 (.step 3 (.close 18))))))) (.run (.step 3 (.step 11 (.step 17 (.step 18 (.step 3 (.close 19))))))))))))))))
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

namespace Part6
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201307876925660414071345874092688222372853965894295002257891718656888427460190279100243317935607054097870984965043898820493359934408045371882287302473502903020006576514178411409702912⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 8 1 (.split 10 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.split 14 1 (.split 26 1 (.split 35 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.step 29 (.close 31)))))) (.step 3 (.step 18 (.step 29 (.close 31))))) (.step 3 (.step 18 (.step 31 (.close 66))))) (.step 3 (.step 29 (.close 31)))) (.step 3 (.close 29))) (.step 3 (.step 11 (.close 17))))))))) (.run (.step 3 (.step 11 (.step 31 (.step 11 (.step 27 (.step 47 (.step 66 (.step 67 (.step 74 (.split 35 1 (.split 65 1 (.split 72 1 (.split 10 1 (.split 26 1 (.split 30 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 67 1 (.step 11 (.step 3 (.step 29 (.close 31)))) (.step 3 (.close 11))) (.step 3 (.step 11 (.step 29 (.close 31))))) (.step 3 (.step 29 (.step 11 (.close 31))))) (.step 3 (.step 29 (.step 31 (.close 11))))) (.step 11 (.step 9 (.step 29 (.close 31))))) (.step 11 (.step 9 (.step 29 (.step 31 (.close 66)))))) (.step 3 (.close 11))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 29 (.step 11 (.close 29)))))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 29 (.step 31 (.step 47 (.step 11 (.step 66 (.step 31 (.step 11 (.step 67 (.step 31 (.step 66 (.step 69 (.close 74))))))))))))))) (.step 3 (.step 11 (.close 66)))) (.step 3 (.step 9 (.step 29 (.step 31 (.step 38 (.step 47 (.step 66 (.step 67 (.step 74 (.step 75 (.step 11 (.step 3 (.close 31)))))))))))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part6.excludes
end FiveColour.Packed.ProjectedChunks.Case103
