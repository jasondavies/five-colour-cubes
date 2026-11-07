module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case15
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725704980689733589940654927499936733694823693447950867335537345167360⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908284911715838913447, 5789234131004114107589341883129531770018971867894994468411955019690277647889009051559687699629171582451667236722394843212749036780556536815853887133914354043305755671668584339630966863574716854696998678016360900365014533121, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723026823511497443414970556934235212658789647265345092460553316133232956827148302389347545258426028166723188761172973234956913610591447394549236171829936128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.step 18 (.step 9 (.step 7 (.close 58))))) (.split 16 0 (.split 26 0 (.step 7 (.close 9)) (.step 9 (.close 7))) (.step 7 (.step 9 (.close 3))))) (.step 29 (.step 7 (.close 75)))) (.step 7 (.step 3 (.close 70)))) (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.step 26 (.step 7 (.close 58))))) (.step 18 (.close 26))) (.step 7 (.close 26)))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 4 0 (.split 10 0 (.step 28 (.step 7 (.close 37))) (.step 7 (.close 15))) (.step 7 (.close 15))) (.step 48 (.step 28 (.step 3 (.close 9))))) (.step 28 (.step 75 (.step 3 (.close 37))))) (.step 3 (.close 7))) (.step 5 (.step 9 (.close 58))))) (.step 58 (.step 18 (.step 9 (.close 58))))) (.split 55 1 (.split 59 1 (.split 56 1 (.split 72 1 (.split 4 0 (.step 57 (.step 18 (.close 16))) (.step 7 (.close 28))) (.step 9 (.step 26 (.step 29 (.step 7 (.close 15)))))) (.step 22 (.step 9 (.step 28 (.close 57))))) (.step 9 (.step 26 (.close 57)))) (.step 9 (.step 48 (.close 58))))) (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.step 7 (.step 3 (.step 7 (.close 75)))) (.step 54 (.step 7 (.close 54)))) (.step 3 (.step 7 (.close 26)))) (.step 7 (.close 54))) (.step 9 (.close 57)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617831357297686959020572369817757356961340814854993141942785822004146333111413521741155494284367487882770177931336937065482972823552⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 4 0 (.split 10 0 (.step 62 (.split 67 1 (.step 9 (.step 7 (.step 18 (.step 21 (.step 7 (.close 58)))))) (.step 7 (.close 53)))) (.step 7 (.step 52 (.step 7 (.close 9))))) (.step 7 (.step 62 (.step 7 (.close 9))))) (.step 53 (.close 7))) (.step 5 (.step 9 (.step 21 (.step 7 (.step 22 (.step 53 (.close 15)))))))) (.step 53 (.close 58))) (.step 9 (.step 21 (.step 53 (.step 18 (.close 57)))))))) (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 4 0 (.split 10 0 (.step 62 (.split 67 1 (.step 9 (.step 7 (.step 18 (.split 25 0 (.step 7 (.step 16 (.step 26 (.close 16)))) (.step 3 (.close 29)))))) (.step 7 (.close 52)))) (.step 7 (.step 52 (.close 7)))) (.step 7 (.step 62 (.step 7 (.close 9))))) (.step 52 (.close 7))) (.step 5 (.step 9 (.step 16 (.close 58))))) (.step 52 (.close 58))) (.step 57 (.close 7))) (.step 52 (.step 7 (.close 21)))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.step 9 (.split 6 0 (.step 7 (.close 9)) (.step 9 (.close 7)))) (.step 46 (.step 9 (.step 7 (.close 9))))) (.step 9 (.close 46))) (.step 9 (.step 27 (.close 46))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341459064137514009958959958259550426456143716329702193824302763437785604977949112169968554595248619111572836450304⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 72 1 (.step 45 (.step 29 (.step 7 (.close 9)))) (.step 26 (.step 29 (.step 45 (.close 3))))) (.step 7 (.close 45))) (.step 7 (.step 26 (.close 45)))) (.step 28 (.step 45 (.close 3)))) (.step 7 (.step 28 (.step 26 (.close 58))))) (.step 7 (.step 9 (.step 21 (.step 29 (.close 45)))))) (.step 29 (.step 40 (.step 9 (.step 7 (.step 26 (.step 37 (.close 52))))))))))) (.run (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 4 0 (.split 10 0 (.step 28 (.step 7 (.close 37))) (.step 7 (.close 15))) (.step 7 (.close 15))) (.step 48 (.step 28 (.step 3 (.close 9))))) (.step 28 (.step 38 (.step 3 (.close 26))))) (.step 3 (.close 7))) (.step 5 (.step 9 (.close 58)))) (.step 28 (.step 41 (.step 7 (.close 58))))) (.step 48 (.step 57 (.close 3)))) (.step 7 (.close 54))) (.step 21 (.close 58))) (.step 5 (.step 9 (.step 58 (.close 3))))) (.step 7 (.close 9))) (.step 28 (.step 38 (.step 45 (.close 58))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414973595399782259359350968111095258032808816091312454594466345976573897102866896826364265556990401554939904⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 54 1 (.step 39 (.step 7 (.close 39))) (.step 22 (.close 57))) (.step 7 (.close 39))) (.step 7 (.step 26 (.close 39)))) (.step 28 (.step 39 (.close 3)))) (.step 7 (.step 28 (.step 22 (.step 9 (.close 39)))))) (.step 7 (.step 9 (.step 21 (.step 29 (.close 39)))))) (.step 29 (.step 40 (.step 9 (.step 7 (.step 22 (.step 37 (.close 52)))))))) (.step 39 (.step 9 (.step 37 (.close 39))))) (.step 28 (.step 38 (.step 39 (.close 58)))))))) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 4 0 (.step 29 (.step 18 (.step 38 (.close 7)))) (.step 7 (.close 28))) (.step 9 (.step 18 (.step 26 (.close 38))))) (.step 29 (.step 38 (.step 3 (.close 37))))) (.step 18 (.close 58))) (.step 21 (.step 29 (.step 57 (.close 3))))) (.step 21 (.step 7 (.close 21)))) (.step 9 (.step 53 (.step 29 (.step 18 (.step 52 (.close 57)))))))) (.step 7 (.close 9))) (.step 29 (.step 38 (.close 7)))) (.step 29 (.close 38))) (.step 29 (.step 38 (.close 7))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889714586173329685272964986055608646157263431285528775366322267541946989419692032⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 54 1 (.split 6 0 (.split 25 0 (.split 26 0 (.step 7 (.close 37)) (.step 28 (.step 7 (.close 15)))) (.step 28 (.step 7 (.close 15)))) (.step 29 (.step 37 (.close 7)))) (.step 29 (.step 37 (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 37)))) (.step 28 (.step 37 (.close 3)))) (.step 7 (.step 28 (.step 37 (.close 9))))) (.step 7 (.step 9 (.step 21 (.step 29 (.close 37)))))) (.step 15 (.step 7 (.step 9 (.step 16 (.close 52)))))) (.step 37 (.close 62))) (.step 28 (.step 37 (.close 58)))) (.step 37 (.step 7 (.close 9)))) (.step 38 (.close 7)))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 29 (.split 30 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 51 1 (.step 29 (.close 7)) (.step 7 (.close 29))) (.step 9 (.step 18 (.close 29)))) (.step 29 (.close 57))) (.step 9 (.step 27 (.step 29 (.close 26))))) (.step 9 (.step 57 (.step 62 (.step 18 (.step 29 (.close 26))))))) (.step 7 (.close 18))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725704980689733589940654927499935404465560257931848581204376243142656⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 25 1 (.reuse 0) (.run (.step 7 (.split 34 1 (.split 36 1 (.split 38 1 (.split 43 1 (.split 49 1 (.split 50 1 (.step 28 (.split 51 1 (.step 29 (.split 54 1 (.split 67 1 (.step 58 (.step 7 (.close 28))) (.step 3 (.step 7 (.close 9)))) (.step 3 (.close 28)))) (.step 3 (.step 7 (.close 26))))) (.step 5 (.step 9 (.step 29 (.step 21 (.close 53)))))) (.step 9 (.step 58 (.close 3)))) (.step 7 (.close 9))) (.step 28 (.close 21))) (.step 28 (.close 29))) (.step 7 (.step 16 (.step 28 (.close 9)))))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.split 25 1 (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 43 1 (.split 36 1 (.split 38 1 (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 4 (.step 7 (.close 9))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 9)))) (.step 4 (.step 7 (.close 53)))) (.step 4 (.step 9 (.step 18 (.close 26))))) (.step 7 (.close 45)))) (.step 3 (.close 4))) (.step 7 (.close 39))) (.step 3 (.step 7 (.close 9)))) (.step 18 (.close 38))) (.step 7 (.close 37))) (.step 18 (.close 29)))) (.step 4 (.step 5 (.step 3 (.close 22)))))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.step 7 (.close 18)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725704980689733589940654927499936733694823693447949714414032738320384⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.split 10 1 (.split 12 1 (.reuse 0) (.run (.split 16 1 (.split 17 1 (.step 57 (.step 18 (.split 21 1 (.split 25 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 67 1 (.split 56 1 (.split 72 1 (.split 4 0 (.step 15 (.step 9 (.step 7 (.step 15 (.close 3))))) (.step 7 (.close 15))) (.step 15 (.close 7))) (.step 22 (.step 15 (.close 3)))) (.step 7 (.close 15))) (.step 15 (.close 7))) (.step 9 (.step 48 (.close 58)))) (.step 9 (.step 7 (.close 15)))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 9 (.close 7))) (.step 15 (.step 26 (.step 29 (.step 37 (.step 7 (.close 15))))))) (.step 3 (.step 16 (.step 21 (.step 28 (.step 48 (.step 15 (.close 41)))))))) (.step 15 (.step 22 (.step 29 (.step 37 (.step 39 (.step 7 (.close 15)))))))) (.step 15 (.close 38))) (.step 15 (.close 37))) (.step 15 (.close 29))) (.step 9 (.step 16 (.step 28 (.step 15 (.step 28 (.close 29))))))) (.step 4 (.step 15 (.close 7)))))) (.step 4 (.step 15 (.close 18)))) (.step 4 (.step 7 (.step 15 (.close 18))))))) (.run (.step 7 (.split 12 1 (.step 18 (.step 7 (.close 18))) (.step 15 (.close 3)))))) (.run (.step 7 (.split 12 1 (.step 18 (.step 7 (.close 18))) (.step 9 (.close 18))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889716395424725704980689733589940654927499936733694823693447950867335537345167360⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.reuse 0) (.run (.split 16 1 (.split 17 1 (.step 9 (.step 18 (.split 25 1 (.step 9 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.split 67 1 (.split 25 0 (.split 51 0 (.step 9 (.close 3)) (.step 7 (.close 9))) (.step 9 (.close 3))) (.step 7 (.close 9))) (.step 10 (.close 3))) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 10 (.step 26 (.step 29 (.step 7 (.close 9)))))) (.step 10 (.close 3))) (.step 7 (.step 29 (.step 39 (.step 7 (.close 9)))))) (.step 7 (.step 10 (.step 29 (.step 37 (.close 7))))))) (.step 9 (.close 10))))) (.step 4 (.step 7 (.step 9 (.close 11))))) (.step 4 (.step 7 (.step 9 (.close 11)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case15
