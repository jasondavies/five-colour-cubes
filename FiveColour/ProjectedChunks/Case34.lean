module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case34
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185308179080118173433856⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908284911715906022327, 5789234131009374243490890256636772759901851996560544808214778193549775928792080905462535096443516630585174618339927574779747879969420415405063696309516301623696527858621603055273255135104029925077778448709311481902056604673, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464719674871529011794140077050684683751126919805810196994116122425772302515819628062971719279624757525174040541790100699402488824890863829430718500049992548352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.split 12 0 (.step 7 (.step 9 (.step 7 (.close 38)))) (.step 18 (.step 9 (.step 15 (.step 43 (.close 58))))))) (.split 16 0 (.split 34 0 (.step 7 (.close 9)) (.step 15 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 3))))) (.step 29 (.step 75 (.step 7 (.close 37))))) (.step 7 (.step 3 (.close 70)))) (.split 67 1 (.split 6 0 (.step 7 (.step 9 (.step 26 (.split 12 0 (.step 7 (.close 62)) (.step 18 (.step 15 (.close 62))))))) (.step 9 (.close 7))) (.step 62 (.close 7)))) (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 12 0 (.step 7 (.step 5 (.close 58))) (.step 48 (.step 28 (.step 3 (.close 58))))) (.split 10 0 (.split 30 0 (.step 22 (.step 9 (.close 3))) (.step 3 (.close 9))) (.step 3 (.close 9)))) (.step 75 (.step 59 (.close 3)))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 9 (.close 58))))) (.step 58 (.step 18 (.step 9 (.close 58))))) (.split 55 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.split 34 0 (.step 57 (.step 7 (.close 57))) (.step 29 (.step 39 (.step 7 (.close 57))))) (.step 15 (.close 57))) (.step 26 (.step 57 (.close 3)))) (.step 3 (.step 9 (.step 7 (.close 21))))) (.step 9 (.step 26 (.close 57)))) (.step 3 (.step 9 (.step 48 (.close 58)))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030096902105339556840570123932040257941863907391135525342799424601052960942854390474631469391576935120200641331448475273272578823361958598161790771658752⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 50 1 (.split 51 1 (.reuse 0) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 67 1 (.split 72 1 (.split 6 0 (.step 7 (.step 9 (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 9 (.close 7))))) (.step 7 (.step 9 (.close 21)))) (.step 54 (.step 7 (.close 54)))) (.step 7 (.close 54))) (.step 3 (.step 7 (.close 54)))) (.step 54 (.close 57))))) (.run (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.split 16 0 (.step 62 (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 21 (.close 53))))) (.step 9 (.step 18 (.step 15 (.step 21 (.close 53)))))) (.step 9 (.step 18 (.step 21 (.close 75)))))) (.step 21 (.step 18 (.step 7 (.close 53))))) (.step 7 (.step 52 (.step 7 (.close 9))))) (.step 53 (.close 7))) (.step 5 (.step 9 (.step 21 (.step 57 (.close 53)))))) (.step 48 (.step 53 (.step 9 (.close 58))))) (.step 9 (.step 21 (.step 53 (.step 57 (.close 3))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935123878833676862859059191519952000574561785986584128552650300398665533421468607053694306327889033620047433449001189376⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 51 1 (.split 10 0 (.split 16 0 (.step 62 (.split 72 1 (.split 12 0 (.step 7 (.step 9 (.step 43 (.close 52)))) (.step 9 (.step 18 (.step 16 (.close 7))))) (.step 9 (.step 26 (.step 7 (.close 58)))))) (.split 59 1 (.step 18 (.step 7 (.close 9))) (.step 27 (.close 62)))) (.step 7 (.step 52 (.close 7)))) (.step 52 (.close 7))) (.step 16 (.step 57 (.close 58)))) (.step 48 (.step 52 (.close 58)))) (.step 52 (.step 57 (.close 7)))) (.step 52 (.split 72 1 (.split 16 0 (.step 52 (.close 58)) (.step 18 (.step 7 (.close 53)))) (.step 21 (.close 52))))))) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.split 67 1 (.step 9 (.split 6 0 (.step 7 (.close 9)) (.step 3 (.step 7 (.close 9))))) (.step 70 (.close 7))) (.step 7 (.close 9))) (.step 54 (.step 7 (.close 9)))) (.step 9 (.close 53))) (.step 9 (.step 27 (.close 46)))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.step 45 (.split 25 0 (.step 7 (.close 45)) (.step 28 (.close 29)))) (.step 29 (.step 75 (.split 16 0 (.step 26 (.step 9 (.close 3))) (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 26 (.close 45))))) (.step 28 (.step 45 (.close 58)))) (.step 7 (.step 45 (.close 58)))) (.step 29 (.step 38 (.step 40 (.step 9 (.step 7 (.step 45 (.close 37)))))))) (.step 26 (.step 29 (.step 40 (.step 57 (.step 58 (.close 52))))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341459064137514009958959958259550424603470288532643067047167003298779079325629357519719529963927274983863250583552⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.reuse 0) (.run (.split 42 1 (.step 58 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 56 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 12 0 (.step 7 (.step 5 (.close 58))) (.step 48 (.step 28 (.step 3 (.close 41))))) (.split 10 0 (.split 30 0 (.step 10 (.step 21 (.step 9 (.close 3)))) (.step 3 (.close 9))) (.step 3 (.close 9)))) (.step 29 (.step 38 (.step 48 (.step 75 (.close 3)))))) (.step 3 (.step 7 (.close 9)))) (.step 5 (.step 9 (.close 58)))) (.step 28 (.step 58 (.step 41 (.close 59))))) (.step 48 (.step 57 (.close 3)))) (.step 3 (.step 7 (.close 54)))) (.step 21 (.step 7 (.step 9 (.close 21))))) (.step 58 (.close 52))) (.step 3 (.step 7 (.close 9))))) (.step 28 (.step 38 (.step 41 (.step 58 (.step 45 (.close 58)))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414973595399782259359350968109242584605011756964535318834327339450921577348216647801732944212862691969073152⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.split 21 0 (.step 39 (.step 7 (.close 39))) (.step 7 (.close 39))) (.step 29 (.step 57 (.step 39 (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 26 (.close 39))))) (.step 22 (.step 28 (.step 39 (.close 3))))) (.step 7 (.step 39 (.close 58)))) (.step 38 (.step 40 (.step 9 (.step 7 (.step 22 (.step 39 (.close 37)))))))) (.step 22 (.step 29 (.step 40 (.step 9 (.step 57 (.step 7 (.close 52)))))))) (.split 49 1 (.step 39 (.step 7 (.step 9 (.step 21 (.step 22 (.close 62)))))) (.step 7 (.step 9 (.step 29 (.step 37 (.step 22 (.step 26 (.close 52))))))))) (.step 28 (.step 38 (.step 41 (.step 58 (.step 39 (.close 3)))))))))) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 75 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.step 7 (.close 38)) (.step 9 (.close 7))) (.step 9 (.step 18 (.close 62)))) (.step 38 (.step 3 (.close 38)))) (.step 18 (.close 58))) (.step 21 (.step 57 (.close 3))))) (.step 7 (.step 9 (.close 75)))) (.step 9 (.step 21 (.step 7 (.close 21))))) (.step 9 (.step 53 (.step 57 (.step 18 (.step 21 (.step 29 (.step 52 (.step 3 (.close 58))))))))))) (.step 7 (.close 9))) (.step 7 (.step 38 (.close 7)))) (.step 3 (.close 38))) (.step 7 (.step 38 (.close 7))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886009239317735567019410714535330633105958791776228277317059624853692669759586304⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 55 1 (.split 56 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 25 0 (.split 54 1 (.split 17 0 (.step 37 (.close 7)) (.step 7 (.close 15))) (.step 29 (.step 37 (.close 7)))) (.step 29 (.close 7))) (.step 7 (.close 37))) (.step 29 (.split 16 0 (.step 37 (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 37)))) (.step 37 (.close 58))) (.step 7 (.step 37 (.close 58)))) (.step 15 (.step 7 (.step 9 (.step 21 (.step 37 (.close 53))))))) (.step 15 (.step 29 (.step 40 (.step 9 (.step 16 (.close 52))))))) (.split 49 1 (.step 45 (.step 7 (.step 9 (.close 37)))) (.step 37 (.close 52)))) (.step 38 (.step 37 (.step 7 (.close 58))))) (.split 49 1 (.step 39 (.step 7 (.step 9 (.close 37)))) (.step 37 (.close 52)))) (.step 37 (.step 38 (.close 7))))))) (.run (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.close 52))))))
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

namespace Part6
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462068164602697931120404007552905735244027204222429691904⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 22 1 (.split 10 1 (.split 25 1 (.reuse 0) (.run (.split 30 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 29 (.split 59 1 (.step 28 (.split 54 1 (.split 6 0 (.step 7 (.close 28)) (.step 3 (.close 9))) (.step 9 (.step 3 (.close 28))))) (.step 9 (.step 26 (.close 58))))) (.step 3 (.step 7 (.close 54)))) (.step 9 (.step 58 (.close 3)))) (.step 58 (.close 52))) (.step 3 (.step 7 (.close 9)))) (.step 28 (.close 29))) (.step 28 (.close 58))) (.step 28 (.close 29))) (.step 28 (.close 29))) (.step 3 (.close 7))))) (.run (.split 25 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.close 52)))) (.step 3 (.close 7))))) (.run (.step 7 (.step 26 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 7))))))) (.run (.step 18 (.split 25 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.step 18 (.split 43 1 (.split 42 1 (.step 57 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.split 59 1 (.split 67 1 (.step 4 (.close 7)) (.step 3 (.step 7 (.close 9)))) (.step 4 (.step 9 (.close 7)))) (.step 3 (.close 4))) (.step 3 (.step 7 (.close 54)))) (.step 4 (.step 9 (.step 18 (.close 26))))) (.step 4 (.step 18 (.close 52))))) (.step 7 (.step 4 (.close 26)))) (.step 3 (.step 7 (.close 9))))) (.step 4 (.step 3 (.close 5)))) (.step 7 (.close 39))) (.step 4 (.step 18 (.close 38)))) (.step 7 (.step 37 (.close 4)))) (.step 3 (.step 4 (.step 28 (.close 3))))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185307026158613566586880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.step 57 (.split 25 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 55 1 (.split 59 1 (.split 72 1 (.split 21 0 (.split 25 0 (.split 35 0 (.split 34 0 (.split 36 0 (.step 15 (.step 3 (.close 7))) (.step 7 (.close 15))) (.step 15 (.close 3))) (.step 15 (.close 3))) (.step 9 (.step 29 (.close 3)))) (.step 7 (.step 9 (.step 15 (.close 3))))) (.step 15 (.close 75))) (.step 15 (.close 7))) (.step 3 (.step 9 (.step 48 (.close 58))))) (.step 3 (.step 15 (.step 54 (.step 9 (.step 7 (.close 15))))))) (.step 15 (.close 53))) (.step 15 (.close 52))) (.step 9 (.close 7))) (.step 15 (.step 26 (.step 29 (.step 37 (.step 45 (.step 7 (.close 15)))))))) (.step 3 (.step 16 (.step 21 (.step 15 (.step 28 (.step 48 (.step 15 (.close 41))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 22 (.step 39 (.step 7 (.close 15))))))))) (.step 15 (.close 38))) (.step 15 (.close 37))) (.step 3 (.step 7 (.step 15 (.close 18))))) (.step 29 (.step 3 (.close 15))))) (.step 7 (.close 26))) (.step 4 (.step 15 (.close 7)))) (.step 4 (.step 15 (.step 18 (.close 9))))) (.step 4 (.step 7 (.step 15 (.step 18 (.close 9)))))) (.step 7 (.step 15 (.close 3)))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544052459742698464723030100098775855080416617834064982935126341461414975835144524439200597501886011048569131586727135462069662641876195297224394325644185308179080118173433856⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 6 1 (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.split 22 1 (.step 22 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 7)))) (.step 7 (.close 18)))))) (.run (.step 7 (.split 17 1 (.split 22 1 (.step 21 (.split 49 1 (.step 7 (.close 18)) (.step 18 (.close 7)))) (.step 7 (.close 18))) (.step 7 (.step 18 (.close 19))))))) (.reuse 1)) (.run (.split 16 1 (.split 17 1 (.split 22 1 (.step 9 (.split 25 1 (.step 7 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 56 1 (.split 16 0 (.split 51 0 (.step 9 (.close 3)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 10 (.close 3))) (.step 9 (.close 7))) (.step 3 (.step 54 (.step 9 (.close 7))))) (.step 9 (.close 7))) (.step 7 (.step 26 (.step 29 (.split 21 0 (.step 45 (.step 7 (.close 9))) (.step 7 (.close 9))))))) (.step 10 (.close 3))) (.step 7 (.step 9 (.step 10 (.step 29 (.step 39 (.step 22 (.step 9 (.close 3))))))))) (.step 7 (.step 10 (.step 29 (.split 21 0 (.step 37 (.step 7 (.close 9))) (.step 7 (.close 9)))))))) (.step 10 (.close 3)))) (.step 7 (.close 26))) (.step 4 (.step 7 (.step 9 (.close 18))))) (.step 4 (.step 7 (.step 11 (.close 9)))))))
theorem accepted : Fast.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Fast.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part8.excludes
end FiveColour.Packed.ProjectedChunks.Case34
