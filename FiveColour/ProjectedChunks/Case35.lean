module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case35
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906965641162702517698560⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752660196157072026346058709379448751222437197125439454832555514724895000915272340796766813855572299595499418464139057114073302233195718468417203422101504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 6 0 (.split 16 0 (.step 7 (.step 9 (.step 18 (.step 26 (.close 7))))) (.step 18 (.step 7 (.step 17 (.close 18))))) (.step 9 (.step 18 (.step 7 (.step 9 (.close 7)))))) (.split 72 1 (.split 6 0 (.step 7 (.step 9 (.close 21))) (.step 9 (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 21 (.close 26)))))) (.split 54 1 (.split 67 1 (.split 72 1 (.step 18 (.split 16 0 (.step 62 (.close 7)) (.step 18 (.close 7)))) (.step 9 (.step 18 (.close 26)))) (.step 26 (.step 62 (.close 7)))) (.step 9 (.step 26 (.step 7 (.step 15 (.step 7 (.close 17)))))))) (.split 67 1 (.split 72 1 (.split 6 0 (.split 21 0 (.split 26 0 (.step 7 (.step 9 (.step 7 (.close 21)))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 7 (.close 9))) (.step 9 (.step 46 (.step 7 (.close 9))))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 54 (.step 7 (.close 9))))) (.step 53 (.split 51 1 (.split 54 1 (.split 72 1 (.split 67 1 (.step 18 (.split 16 0 (.split 17 0 (.step 9 (.step 7 (.close 15))) (.step 7 (.close 9))) (.step 18 (.close 7)))) (.step 53 (.close 7))) (.step 9 (.step 18 (.step 21 (.step 7 (.step 15 (.step 7 (.close 26)))))))) (.step 9 (.step 21 (.step 7 (.step 18 (.step 26 (.step 7 (.close 29)))))))) (.step 53 (.close 7))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452123411166788548947610075842614534203936906263897114295763140832198601297635535107051298867379917688861651632128⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 54 1 (.split 72 1 (.split 67 1 (.step 18 (.split 16 0 (.split 17 0 (.step 9 (.step 7 (.close 15))) (.step 7 (.close 9))) (.step 18 (.close 7)))) (.step 52 (.close 7))) (.step 9 (.step 18 (.step 26 (.step 7 (.close 21)))))) (.step 9 (.step 52 (.step 57 (.close 7))))) (.step 52 (.close 7)))))) (.run (.split 49 1 (.split 51 1 (.split 67 1 (.step 9 (.split 6 0 (.split 21 0 (.split 26 0 (.step 7 (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7)))) (.step 46 (.close 7))) (.step 46 (.close 7))) (.step 9 (.step 7 (.step 27 (.close 46))))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.close 21))) (.step 29 (.close 7))) (.step 7 (.close 15))) (.step 29 (.step 75 (.step 7 (.close 9))))) (.step 7 (.step 9 (.step 26 (.step 15 (.close 21)))))) (.step 18 (.step 26 (.step 29 (.step 38 (.step 9 (.step 7 (.step 15 (.close 26))))))))) (.step 18 (.step 26 (.step 29 (.step 40 (.step 9 (.step 45 (.step 38 (.close 52))))))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762002869938770909476934032218843051222743011011783914971860758972893583525803979570636396855567690370121728⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.close 21))) (.step 29 (.close 7))) (.step 7 (.close 15))) (.step 29 (.step 57 (.step 7 (.close 9))))) (.step 7 (.step 9 (.step 26 (.step 15 (.close 21)))))) (.step 18 (.step 29 (.step 38 (.step 9 (.step 7 (.step 15 (.close 26)))))))) (.step 18 (.step 29 (.step 40 (.step 9 (.step 52 (.step 7 (.step 26 (.close 15))))))))) (.step 45 (.split 49 1 (.step 39 (.step 7 (.step 9 (.step 21 (.step 26 (.step 15 (.step 29 (.step 15 (.close 37))))))))) (.step 7 (.step 9 (.step 29 (.step 37 (.step 21 (.step 26 (.step 21 (.close 52)))))))))))))) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 51 1 (.step 75 (.step 18 (.split 67 1 (.step 29 (.step 7 (.close 9))) (.step 7 (.step 9 (.close 21)))))) (.step 7 (.step 9 (.step 21 (.step 26 (.close 29)))))) (.step 9 (.step 26 (.step 29 (.step 18 (.step 21 (.step 7 (.step 15 (.step 7 (.close 26)))))))))) (.step 9 (.step 21 (.step 29 (.step 18 (.step 38 (.step 7 (.close 26)))))))) (.step 9 (.step 21 (.step 18 (.close 21))))) (.step 9 (.step 52 (.step 29 (.step 38 (.step 18 (.step 21 (.step 7 (.close 15))))))))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 38 (.close 7))))) (.step 7 (.step 29 (.step 38 (.close 7)))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565995609705935466821066659310672864052627930797953815609085963077496397668160634880⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 30 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 18 (.close 7)))))) (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 26 0 (.step 7 (.step 15 (.close 21))) (.step 29 (.close 7))) (.step 7 (.close 15))) (.step 15 (.step 9 (.step 7 (.close 9))))) (.step 7 (.step 9 (.step 15 (.step 21 (.close 26)))))) (.step 15 (.step 7 (.step 9 (.step 21 (.step 26 (.close 29))))))) (.step 15 (.step 9 (.step 7 (.step 29 (.step 26 (.step 21 (.step 26 (.close 52))))))))) (.step 37 (.split 49 1 (.step 45 (.step 7 (.step 9 (.step 15 (.step 21 (.step 26 (.step 29 (.close 37)))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.close 52))))))))) (.step 37 (.split 49 1 (.step 39 (.step 7 (.step 9 (.step 15 (.step 21 (.step 26 (.step 29 (.close 37)))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.close 52))))))))) (.step 29 (.step 37 (.step 38 (.close 7))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565995609705935466821066659310672864052627930799283044872521479178629607324655812608⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 15 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.step 18 (.split 50 1 (.split 59 1 (.split 72 1 (.split 4 0 (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 7 (.step 54 (.close 7))) (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 7 (.step 9 (.close 7)))) (.step 9 (.step 7 (.close 15)))) (.step 9 (.step 7 (.close 15)))) (.step 9 (.close 7))) (.step 9 (.step 15 (.close 7)))) (.step 9 (.step 15 (.close 7)))) (.step 9 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26)))))))) (.step 9 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26))))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 15 (.close 7)))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 7 (.step 9 (.step 7 (.close 15))))))))) (.step 9 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26))))))) (.step 7 (.step 15 (.close 7))))))) (.run (.step 7 (.split 12 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.step 15 (.close 18))))) (.step 18 (.step 7 (.step 9 (.step 7 (.close 15)))))) (.step 18 (.close 7))) (.step 15 (.close 7)))))) (.run (.step 7 (.split 12 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 18 (.close 7))) (.step 9 (.step 15 (.step 7 (.close 15))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265565190103143347990225842026057764612223867636908759514003705692160⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 4 1 (.split 10 1 (.split 12 1 (.split 30 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.step 18 (.split 67 1 (.step 29 (.close 7)) (.step 7 (.step 9 (.close 21))))) (.step 9 (.step 18 (.step 26 (.step 7 (.close 15)))))) (.step 9 (.step 29 (.step 7 (.close 26))))) (.step 7 (.step 9 (.step 26 (.step 29 (.close 26)))))) (.step 9 (.step 27 (.step 53 (.close 29))))) (.step 9 (.step 27 (.step 52 (.close 29))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 18)))) (.step 9 (.step 15 (.close 7)))) (.step 7 (.step 15 (.step 7 (.step 9 (.step 15 (.close 18))))))) (.step 7 (.step 18 (.close 7))))))) (.run (.step 7 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.close 7))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 15 (.step 18 (.close 9)))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906964488241197910851584⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 12 1 (.split 26 1 (.split 35 1 (.split 43 1 (.step 57 (.split 49 1 (.split 50 1 (.split 59 1 (.split 72 1 (.split 34 1 (.split 36 1 (.step 9 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.step 15 (.close 26))))) (.step 7 (.step 9 (.step 7 (.step 15 (.close 26)))))) (.step 7 (.step 9 (.step 7 (.step 17 (.close 26)))))) (.step 7 (.step 9 (.step 7 (.step 18 (.close 26)))))) (.step 7 (.step 9 (.step 7 (.step 18 (.step 26 (.close 52)))))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 7 (.step 18 (.step 29 (.step 26 (.step 15 (.step 26 (.close 37)))))))))) (.step 7 (.step 9 (.step 18 (.close 29))))) (.step 9 (.step 15 (.close 7)))))))) (.run (.step 7 (.step 18 (.split 12 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.close 7))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 7 (.step 11 (.close 18)))) (.step 15 (.step 18 (.close 9)))))))) (.run (.step 7 (.step 18 (.split 12 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.close 7))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 11 (.step 18 (.close 19))))) (.step 18 (.step 9 (.close 15))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906965641162702517698560⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.reuse 0) (.run (.split 4 1 (.split 10 1 (.split 12 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 4 0 (.split 16 1 (.step 9 (.step 18 (.close 9))) (.step 11 (.close 9))) (.step 9 (.step 7 (.close 9)))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 9 (.step 57 (.step 46 (.step 7 (.close 9))))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 9 (.step 29 (.step 7 (.close 9)))))) (.step 7 (.step 9 (.step 29 (.step 39 (.step 7 (.close 9))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.step 7 (.close 9)))))))) (.step 7 (.step 9 (.step 7 (.close 9))))) (.step 9 (.close 7))) (.step 9 (.close 7))) (.step 7 (.step 9 (.step 7 (.close 9))))) (.step 7 (.step 9 (.close 7))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case35
