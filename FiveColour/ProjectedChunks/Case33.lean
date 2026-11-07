module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case33
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379522046674022425821715511990081822916608⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908284911715872467959, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691003773395856797335276228224145743890145446228163347693427359436041631246125966867020082117046907873927859536897, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030096902105339556840570123932040257941863907391135525342799424601052960944705254651034195452800577583698887108540587684412427214180162264616772596400128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.split 12 0 (.step 7 (.step 18 (.close 38))) (.step 18 (.step 9 (.step 7 (.close 58)))))) (.step 29 (.step 7 (.close 75)))) (.step 7 (.step 3 (.close 70)))) (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.step 26 (.split 12 0 (.step 7 (.step 18 (.close 38))) (.step 18 (.step 15 (.close 62))))))) (.step 18 (.close 26))) (.step 7 (.close 26)))) (.split 59 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 3 (.step 7 (.close 58))) (.step 22 (.step 3 (.close 58)))) (.step 7 (.close 15))) (.step 75 (.step 3 (.close 37)))) (.step 7 (.step 9 (.close 58))))) (.step 58 (.step 18 (.step 9 (.step 48 (.close 58)))))) (.step 57 (.split 56 1 (.step 18 (.close 57)) (.step 48 (.close 57))))) (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.step 7 (.step 3 (.step 9 (.close 75)))) (.step 54 (.close 3))) (.step 3 (.step 7 (.close 26)))) (.step 3 (.close 54))) (.step 54 (.close 57)))) (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.step 62 (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.split 12 0 (.step 7 (.step 18 (.close 53))) (.step 18 (.step 15 (.step 21 (.close 53))))))) (.step 9 (.step 18 (.close 75)))) (.step 7 (.close 53)))) (.step 18 (.step 52 (.step 7 (.close 15))))) (.step 53 (.close 7))) (.step 5 (.step 21 (.step 7 (.step 22 (.step 53 (.close 15))))))) (.step 53 (.close 58))) (.step 21 (.step 53 (.step 18 (.close 57)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935123878833676862859059191519952000574563636850760531278711524041129031667245699166105446176279851823713888430825930752⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.step 62 (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.split 12 0 (.step 7 (.step 18 (.close 52))) (.step 18 (.step 15 (.step 16 (.close 7))))))) (.step 9 (.step 18 (.close 75)))) (.step 7 (.close 52)))) (.step 7 (.step 18 (.close 52)))) (.step 52 (.close 7))) (.step 5 (.step 16 (.step 7 (.step 22 (.step 52 (.close 26))))))) (.step 52 (.close 58))) (.step 52 (.step 57 (.close 7)))) (.step 52 (.close 58))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 67 1 (.step 7 (.close 9)) (.step 46 (.step 7 (.close 9)))) (.step 9 (.close 7))) (.step 54 (.step 7 (.close 9)))) (.step 9 (.close 53))) (.step 9 (.step 27 (.close 46)))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.split 72 1 (.step 45 (.step 7 (.close 38))) (.step 26 (.step 29 (.step 45 (.close 3))))) (.step 7 (.close 45))) (.step 7 (.step 26 (.close 45)))) (.step 45 (.close 3))) (.step 7 (.step 28 (.step 45 (.close 16))))) (.step 7 (.step 21 (.step 29 (.step 45 (.close 37)))))) (.step 57 (.step 7 (.step 26 (.step 37 (.step 45 (.close 21))))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461412680096783792187847740147215791361840617918036590680174087996388626766883268011384481129326207548107259904⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 58 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 3 (.step 7 (.close 41))) (.step 21 (.step 28 (.step 3 (.close 37))))) (.step 7 (.close 15))) (.step 28 (.step 38 (.step 3 (.close 26))))) (.step 3 (.close 7))) (.step 7 (.step 9 (.close 58)))) (.step 28 (.step 58 (.step 41 (.close 58))))) (.step 48 (.step 57 (.close 3)))) (.step 7 (.close 54))) (.step 5 (.step 21 (.close 53)))) (.step 58 (.close 52))) (.step 7 (.close 9))) (.step 28 (.step 38 (.step 45 (.close 58)))))))) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 16 0 (.step 57 (.step 39 (.step 7 (.close 38)))) (.step 7 (.close 39))) (.step 7 (.step 26 (.close 39)))) (.step 28 (.step 39 (.close 3)))) (.step 7 (.step 28 (.step 39 (.close 16))))) (.step 7 (.step 21 (.step 29 (.step 39 (.close 37)))))) (.step 29 (.step 57 (.step 7 (.close 52))))) (.step 39 (.step 37 (.step 45 (.close 52))))) (.step 28 (.step 38 (.step 39 (.close 58))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501887860103494138293080634356998828878883050904187368125707877828520147651584327680⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.split 54 1 (.step 58 (.split 56 1 (.step 7 (.step 18 (.step 38 (.close 7)))) (.step 38 (.step 3 (.close 37))))) (.step 21 (.step 57 (.close 3))))) (.step 7 (.step 9 (.step 21 (.close 75))))) (.step 9 (.step 21 (.step 7 (.close 21))))) (.step 53 (.step 57 (.step 58 (.step 62 (.step 18 (.step 29 (.step 38 (.close 52)))))))))) (.step 7 (.close 9))) (.step 7 (.step 38 (.close 7)))) (.step 3 (.close 38))) (.step 7 (.step 38 (.close 7)))))) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 54 1 (.split 21 0 (.split 26 0 (.split 17 0 (.step 37 (.close 7)) (.step 7 (.close 15))) (.step 28 (.step 7 (.close 26)))) (.step 7 (.close 37))) (.step 29 (.step 37 (.step 7 (.close 21))))) (.step 7 (.step 26 (.close 37)))) (.step 28 (.step 37 (.close 3)))) (.step 7 (.step 28 (.step 37 (.close 57))))) (.step 7 (.step 21 (.step 29 (.step 37 (.close 53)))))) (.step 15 (.step 7 (.step 16 (.step 29 (.close 52)))))) (.step 37 (.step 7 (.step 37 (.close 52))))) (.step 28 (.step 37 (.step 7 (.close 58))))) (.step 37 (.step 7 (.step 37 (.close 52))))) (.step 38 (.close 7)))))) (.run (.step 18 (.step 7 (.close 18)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379520717444758990305614378781524839366656⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.step 18 (.close 26))) (.step 7 (.step 29 (.close 26)))) (.step 57 (.step 62 (.step 18 (.step 29 (.close 26)))))) (.step 57 (.step 62 (.split 50 1 (.step 18 (.step 29 (.close 26))) (.step 21 (.close 52)))))) (.step 7 (.close 9))) (.step 7 (.close 18)))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 43 1 (.split 38 1 (.step 57 (.split 42 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.step 4 (.step 9 (.close 18))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 26)))) (.step 4 (.step 9 (.step 18 (.close 26))))) (.step 4 (.step 18 (.close 52)))) (.step 7 (.close 45)))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 9)))) (.step 7 (.close 39))) (.step 18 (.close 38))) (.step 7 (.close 37))) (.step 18 (.close 29)))))) (.run (.step 18 (.step 7 (.close 18))))) (.run (.step 18 (.step 7 (.step 18 (.close 19))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501889712776921937038849582746996659133430379522046674022425821715511990081822916608⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.split 16 1 (.split 17 1 (.step 57 (.step 18 (.split 21 1 (.split 26 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 56 1 (.step 15 (.step 18 (.close 15))) (.step 22 (.step 15 (.close 3)))) (.step 9 (.step 15 (.close 58)))) (.step 3 (.step 15 (.step 54 (.step 9 (.step 7 (.close 15))))))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 9 (.close 7))) (.step 15 (.step 26 (.step 29 (.step 37 (.step 7 (.close 15))))))) (.step 3 (.step 16 (.step 21 (.step 28 (.step 48 (.step 15 (.close 41)))))))) (.step 15 (.step 22 (.step 29 (.step 37 (.step 22 (.step 39 (.step 7 (.close 15))))))))) (.step 15 (.close 38))) (.step 15 (.close 37))) (.step 15 (.close 29))) (.step 4 (.step 15 (.close 7)))))) (.step 7 (.step 15 (.close 18)))) (.step 4 (.step 7 (.step 15 (.close 18))))))) (.run (.step 7 (.split 12 1 (.step 18 (.step 7 (.close 18))) (.step 15 (.close 3))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case33
