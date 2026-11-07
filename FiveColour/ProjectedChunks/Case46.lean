module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case46
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475476381120379074882537373524376559072823736861674438656⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908284911715939576823, 5789234131009374248507346766749891415336450807595823763245543538954566673098295099809170727596598837657640512857309521993999462306427087381105369261884265993783467999530422928012791073057088273642977565022587162213165827073, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply FastWeight.cut_valid_of_fast_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply FastWeight.cut_valid_of_fast_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply FastWeight.cut_valid_of_fast_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723026823511497443414970556934235212658789647265345092460553316133232956827146447906668353866233697537666408993898760707858752960933002955527436833994571776⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.split 12 0 (.split 16 0 (.step 7 (.step 9 (.step 7 (.close 38)))) (.step 7 (.close 4))) (.step 18 (.step 9 (.step 15 (.step 43 (.step 7 (.close 38)))))))) (.step 29 (.step 75 (.step 7 (.close 75))))) (.step 7 (.step 3 (.close 70)))) (.split 67 1 (.split 72 1 (.step 7 (.split 16 0 (.step 9 (.step 62 (.close 3))) (.step 7 (.close 18)))) (.step 18 (.close 26))) (.step 62 (.close 7)))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 7 (.step 5 (.close 58))) (.split 30 0 (.step 22 (.step 3 (.close 58))) (.step 3 (.close 15)))) (.step 7 (.close 15))) (.step 75 (.step 59 (.close 3)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 26 (.close 58))))) (.step 58 (.step 18 (.step 48 (.step 58 (.close 3)))))) (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 34 0 (.step 18 (.close 57)) (.step 15 (.step 7 (.close 57)))) (.step 26 (.step 57 (.close 3)))) (.step 3 (.step 57 (.step 70 (.close 7))))) (.step 9 (.step 26 (.step 57 (.close 3))))) (.step 48 (.close 57))) (.step 9 (.step 57 (.close 58))))) (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.split 72 1 (.split 12 0 (.step 7 (.close 54)) (.step 3 (.step 54 (.close 7)))) (.step 7 (.step 21 (.close 26)))) (.step 54 (.close 3))) (.step 7 (.close 54))) (.step 7 (.close 54))) (.step 3 (.step 54 (.close 57))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617831357297686959020572369817757356961340814854993140088303142812754140780784464961388220071840389722120519486897915266145137459200⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.split 16 0 (.step 9 (.split 12 0 (.step 55 (.close 53)) (.step 18 (.step 15 (.step 21 (.close 53)))))) (.step 7 (.close 18)))) (.step 9 (.step 18 (.step 21 (.close 75))))) (.step 53 (.close 7))) (.step 53 (.close 62))) (.step 53 (.close 7))) (.step 5 (.step 21 (.step 57 (.close 53))))) (.step 53 (.step 58 (.close 3)))) (.step 53 (.step 57 (.close 7)))))) (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.split 16 0 (.step 9 (.split 12 0 (.step 55 (.close 52)) (.step 18 (.step 15 (.step 16 (.close 7)))))) (.step 7 (.close 18)))) (.step 9 (.step 18 (.step 26 (.step 7 (.close 58)))))) (.step 52 (.close 7))) (.step 52 (.close 62))) (.step 52 (.close 7))) (.step 5 (.step 57 (.step 52 (.close 26))))) (.step 48 (.step 52 (.close 58)))) (.step 52 (.step 57 (.close 7)))) (.step 52 (.split 16 0 (.step 52 (.close 58)) (.step 5 (.close 53))))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 67 1 (.split 72 1 (.split 12 0 (.step 7 (.close 9)) (.step 3 (.step 7 (.step 9 (.close 7))))) (.step 7 (.close 9))) (.step 70 (.close 3))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 54 (.step 7 (.close 9)))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 46 (.close 52))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341459064137514009958959958259550424601661037138310001493673706658018330765422014009318896150809597312235001085952⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 49 0 (.step 45 (.close 7)) (.step 7 (.close 45))) (.step 7 (.close 26))) (.step 7 (.step 26 (.close 45)))) (.step 45 (.close 3))) (.step 7 (.step 45 (.close 16)))) (.step 26 (.step 29 (.step 57 (.step 59 (.split 55 1 (.split 10 0 (.step 26 (.step 39 (.close 57))) (.step 7 (.close 15))) (.step 3 (.close 57)))))))) (.step 29 (.step 38 (.step 57 (.step 7 (.step 45 (.close 37))))))) (.step 26 (.step 57 (.step 58 (.step 55 (.close 52))))))))) (.run (.split 42 1 (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.step 28 (.step 41 (.step 7 (.step 5 (.close 58))))) (.step 7 (.close 22))) (.step 7 (.close 21))) (.step 48 (.step 59 (.split 30 0 (.step 21 (.step 28 (.step 37 (.step 3 (.close 22))))) (.step 3 (.close 15)))))) (.step 7 (.close 41))) (.step 38 (.step 75 (.step 41 (.close 3))))) (.step 3 (.step 7 (.close 58)))) (.step 58 (.close 3))) (.step 48 (.step 57 (.close 3)))) (.step 7 (.close 54))) (.step 21 (.step 7 (.step 21 (.close 26))))) (.step 58 (.close 52))) (.step 7 (.step 9 (.close 10))))) (.step 38 (.step 28 (.step 76 (.step 41 (.step 58 (.step 45 (.close 58))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414973595399782259359350968109240775353617423898981825537686578702361370004706247167919826535191063719575552⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 49 0 (.step 39 (.close 7)) (.step 7 (.close 39))) (.step 7 (.close 39))) (.step 7 (.step 26 (.close 39)))) (.step 22 (.step 28 (.step 39 (.close 3))))) (.step 7 (.step 39 (.close 58)))) (.step 29 (.step 39 (.close 57)))) (.step 29 (.step 38 (.step 57 (.step 7 (.close 53)))))) (.step 57 (.step 7 (.step 52 (.close 26))))) (.split 49 1 (.step 39 (.step 7 (.step 45 (.close 57)))) (.step 7 (.step 57 (.step 45 (.close 52)))))) (.step 38 (.step 28 (.split 49 1 (.step 39 (.step 7 (.close 58))) (.step 7 (.step 16 (.close 58)))))))))) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 75 (.split 54 1 (.split 55 1 (.split 59 1 (.split 67 1 (.step 29 (.step 38 (.step 7 (.close 38)))) (.step 7 (.close 70))) (.step 18 (.step 26 (.step 7 (.close 38))))) (.step 18 (.close 58))) (.step 57 (.close 7)))) (.step 7 (.step 9 (.step 21 (.close 75))))) (.step 21 (.step 18 (.close 53)))) (.step 9 (.step 53 (.step 57 (.step 58 (.step 62 (.step 75 (.step 18 (.step 21 (.split 51 1 (.step 38 (.step 7 (.close 26))) (.step 7 (.close 52)))))))))))) (.step 7 (.close 9))) (.step 7 (.step 29 (.step 38 (.close 7))))) (.step 3 (.step 29 (.close 38)))) (.step 7 (.step 29 (.step 38 (.close 7)))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342918950523918153677039045841523159634979004772915961801110485729280⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 21 0 (.split 72 1 (.split 50 0 (.split 17 0 (.step 37 (.close 7)) (.step 7 (.close 15))) (.step 7 (.close 37))) (.step 37 (.close 7))) (.step 7 (.close 37))) (.step 7 (.close 37))) (.step 28 (.step 37 (.close 7)))) (.step 7 (.step 37 (.close 58)))) (.step 15 (.step 29 (.step 57 (.step 39 (.step 37 (.step 57 (.close 3)))))))) (.step 15 (.step 7 (.step 21 (.step 37 (.step 26 (.step 52 (.close 57)))))))) (.step 15 (.step 16 (.step 52 (.step 7 (.step 16 (.step 26 (.close 21)))))))) (.split 49 1 (.step 45 (.step 7 (.step 15 (.step 45 (.close 52))))) (.step 7 (.step 37 (.step 38 (.close 52)))))) (.step 16 (.step 28 (.step 38 (.step 37 (.step 7 (.close 41))))))) (.split 49 1 (.step 39 (.step 7 (.step 15 (.step 39 (.close 52))))) (.step 7 (.step 37 (.step 38 (.close 52)))))) (.step 29 (.step 37 (.step 38 (.close 7)))))))) (.run (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.close 52)))))) (.run (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 26 (.step 18 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475476381120379074882537372256725958844594335364971233280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 57 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 34 0 (.step 7 (.step 9 (.step 15 (.step 7 (.step 15 (.close 3)))))) (.step 15 (.close 3))) (.step 7 (.step 9 (.step 15 (.close 3))))) (.step 15 (.close 7))) (.step 3 (.step 15 (.step 70 (.close 7))))) (.step 3 (.step 15 (.step 54 (.step 57 (.step 7 (.close 9))))))) (.step 9 (.close 7))) (.step 15 (.close 62))) (.step 22 (.step 15 (.close 3)))) (.step 3 (.step 9 (.step 48 (.step 15 (.close 58)))))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 26 (.step 45 (.step 7 (.close 15))))))))) (.step 3 (.step 16 (.step 21 (.step 15 (.step 28 (.step 48 (.step 41 (.step 15 (.step 3 (.close 26))))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 39 (.step 22 (.step 7 (.close 58))))))))) (.step 15 (.close 38))) (.step 15 (.close 37))) (.step 18 (.close 15)))) (.step 18 (.close 15))) (.step 4 (.step 15 (.close 7)))) (.step 18 (.close 15))) (.step 18 (.close 15))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886007430066342920596028475476381120379074882537373524376559072823736861674438656⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 18 (.split 34 1 (.split 35 1 (.split 36 1 (.split 43 1 (.split 49 1 (.split 38 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 42 1 (.split 51 1 (.split 56 1 (.split 67 1 (.step 4 (.close 7)) (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 4))) (.step 7 (.close 54))) (.step 7 (.close 45))) (.step 4 (.step 9 (.step 18 (.close 26))))) (.step 9 (.close 57))) (.step 4 (.step 18 (.close 53)))) (.step 3 (.close 4))) (.step 4 (.step 18 (.close 52)))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 39))) (.step 4 (.step 18 (.close 38)))) (.step 7 (.close 37)))))) (.run (.split 22 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 22 (.step 18 (.close 7)))) (.step 7 (.step 18 (.close 52)))))) (.run (.step 18 (.split 17 1 (.split 22 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 21 (.step 18 (.close 7)))) (.step 7 (.step 18 (.close 52)))) (.step 7 (.step 18 (.close 53))))))) (.reuse 1)) (.run (.split 12 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.close 52)))) (.step 15 (.close 7)))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part6.excludes
end FiveColour.Packed.ProjectedChunks.Case46
