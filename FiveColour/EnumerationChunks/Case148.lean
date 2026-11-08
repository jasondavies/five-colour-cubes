module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
public import FiveColour.ClassificationProjection
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Projected.Case148
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906965641162702517698560⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904443229329621762877716815095803433753783035401925558845793450693587522711797889167563345248373158302283501583810009023851134823371485230174522456378444063331558883328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 67 1 (.split 6 0 (.split 16 0 (.step 7 (.step 18 (.split 17 0 (.split 12 0 (.step 7 (.step 9 (.step 7 (.close 21)))) (.step 9 (.step 18 (.step 15 (.step 7 (.close 21)))))) (.step 7 (.step 9 (.step 15 (.step 17 (.close 18)))))))) (.split 17 0 (.step 7 (.step 18 (.close 7))) (.step 7 (.step 17 (.close 18))))) (.split 16 0 (.split 72 1 (.step 18 (.split 17 0 (.step 9 (.close 7)) (.step 7 (.close 9)))) (.step 9 (.close 7))) (.step 18 (.split 72 1 (.step 18 (.close 7)) (.step 9 (.close 7)))))) (.split 72 1 (.split 6 0 (.step 7 (.step 9 (.close 21))) (.split 21 0 (.split 26 0 (.step 70 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 21 (.close 26)))))) (.split 67 1 (.split 72 1 (.split 4 0 (.split 12 0 (.step 18 (.split 16 0 (.step 62 (.close 7)) (.step 18 (.close 7)))) (.step 9 (.step 18 (.step 15 (.step 7 (.close 21)))))) (.step 18 (.split 26 0 (.step 7 (.close 9)) (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 9 (.step 26 (.close 7)))) (.step 26 (.step 62 (.close 7))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660749386805549175884476045519682621152070220555079396390043072223356798867118867666241883543763246395438348531780011497043064084976649833075363874894512128⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 4 0 (.step 57 (.step 7 (.close 18))) (.step 9 (.step 7 (.step 15 (.close 18))))) (.step 9 (.step 26 (.step 18 (.step 15 (.step 18 (.close 21))))))) (.step 57 (.split 4 0 (.split 12 0 (.split 21 0 (.split 6 0 (.step 7 (.step 9 (.close 21))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 9 (.step 7 (.step 21 (.close 26))))) (.step 7 (.close 9))))) (.step 9 (.step 26 (.step 18 (.step 15 (.close 21)))))))) (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 21 0 (.split 26 0 (.step 7 (.split 4 0 (.step 54 (.close 7)) (.step 7 (.close 9)))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 7 (.close 9))) (.step 57 (.split 21 0 (.split 26 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 18 (.step 40 (.step 9 (.step 7 (.step 21 (.step 26 (.step 21 (.close 29))))))))) (.step 54 (.step 7 (.step 9 (.step 26 (.step 21 (.step 54 (.close 29)))))))) (.step 54 (.step 57 (.step 62 (.close 7)))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922103644135012059424734283689937543763013994501621657295932892236761817049021836611277886126916525434455147171922814059621357063241728⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 4 0 (.split 6 0 (.step 18 (.split 10 0 (.step 53 (.close 7)) (.step 7 (.step 9 (.close 15))))) (.step 9 (.close 7))) (.step 18 (.split 26 0 (.step 7 (.close 9)) (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 9 (.step 29 (.step 18 (.step 21 (.step 7 (.close 15))))))) (.step 53 (.close 7))) (.step 53 (.close 7))) (.step 9 (.step 21 (.step 53 (.step 57 (.close 7)))))) (.step 53 (.close 7))))) (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 4 0 (.split 12 0 (.step 18 (.split 16 0 (.split 17 0 (.step 9 (.step 7 (.close 21))) (.step 7 (.close 9))) (.step 18 (.close 7)))) (.step 9 (.step 18 (.step 15 (.step 7 (.close 21)))))) (.step 18 (.split 26 0 (.step 7 (.close 9)) (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 9 (.step 29 (.step 18 (.step 26 (.close 7)))))) (.step 52 (.close 7))) (.step 52 (.close 7))) (.step 9 (.step 52 (.step 57 (.close 7))))) (.step 52 (.close 7))) (.step 52 (.close 7)))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452123411166788548947610075842614534203936906263897114295763140832198601297635535107051298867379917688861651632128⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.reuse 0) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 6 0 (.split 21 0 (.split 26 0 (.step 7 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.split 21 0 (.split 26 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 9 (.close 7))) (.step 70 (.step 9 (.step 46 (.close 7))))) (.step 9 (.close 7))) (.step 46 (.step 54 (.step 7 (.close 9))))) (.step 9 (.step 7 (.step 27 (.close 46))))) (.step 9 (.step 27 (.close 46)))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 26 0 (.split 34 0 (.step 7 (.step 21 (.close 26))) (.split 49 0 (.step 7 (.step 15 (.step 7 (.close 21)))) (.step 7 (.step 15 (.step 21 (.close 26)))))) (.step 29 (.close 7))) (.step 7 (.step 15 (.close 26)))) (.step 29 (.step 75 (.split 21 0 (.split 34 0 (.step 7 (.close 9)) (.step 45 (.step 7 (.close 9)))) (.step 7 (.close 9)))))) (.step 18 (.step 26 (.step 29 (.step 40 (.step 9 (.step 7 (.step 15 (.step 26 (.step 15 (.close 21))))))))))) (.step 18 (.step 26 (.step 29 (.step 38 (.step 40 (.step 9 (.step 53 (.step 7 (.step 15 (.close 26))))))))))) (.step 26 (.step 55 (.step 9 (.step 52 (.step 7 (.step 26 (.step 15 (.step 29 (.step 15 (.close 21))))))))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125759709371322780837965323211323540964281946446022615633848123170133506660649715494762566378302457564683567104⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.reuse 0) (.run (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 26 0 (.split 34 0 (.step 7 (.step 21 (.close 26))) (.step 39 (.close 7))) (.step 29 (.close 7))) (.step 7 (.step 15 (.close 26)))) (.step 29 (.step 57 (.step 75 (.step 7 (.close 9)))))) (.step 18 (.step 29 (.step 40 (.step 9 (.step 7 (.step 26 (.step 15 (.close 21))))))))) (.step 18 (.step 29 (.step 38 (.step 40 (.step 9 (.step 53 (.step 7 (.step 15 (.step 26 (.close 15))))))))))) (.step 57 (.step 75 (.step 55 (.step 9 (.step 7 (.step 29 (.step 15 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52))))))))))))) (.step 45 (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 9 (.step 26 (.step 29 (.step 15 (.step 37 (.close 21)))))))) (.step 7 (.step 9 (.step 29 (.step 38 (.step 37 (.step 26 (.step 37 (.step 39 (.close 53)))))))))) (.step 7 (.step 9 (.step 29 (.step 52 (.step 26 (.step 37 (.close 21)))))))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565995609705935466821066659310672864052627930797953815609085963077496397668160634880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 6 0 (.split 21 0 (.split 26 0 (.split 36 0 (.step 7 (.step 15 (.close 21))) (.step 37 (.step 7 (.step 15 (.close 21))))) (.step 29 (.close 7))) (.step 7 (.step 15 (.close 26)))) (.step 29 (.step 75 (.split 21 0 (.split 36 0 (.step 7 (.close 9)) (.step 37 (.step 7 (.close 9)))) (.step 7 (.close 9)))))) (.step 15 (.step 7 (.step 9 (.step 26 (.step 21 (.close 29))))))) (.step 15 (.step 18 (.step 29 (.step 38 (.step 9 (.step 7 (.step 26 (.close 52))))))))) (.step 15 (.step 52 (.step 7 (.step 9 (.step 26 (.step 29 (.step 21 (.step 26 (.close 21)))))))))) (.step 37 (.split 49 1 (.split 50 1 (.step 45 (.step 29 (.step 37 (.step 7 (.step 9 (.step 15 (.step 26 (.step 21 (.close 37))))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.close 52)))))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.step 38 (.close 52)))))))))) (.step 37 (.split 49 1 (.split 50 1 (.step 39 (.step 7 (.step 9 (.step 15 (.step 26 (.step 21 (.step 29 (.step 21 (.close 37))))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.close 52)))))))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 37 (.step 38 (.close 52)))))))))) (.step 29 (.step 37 (.step 38 (.close 7)))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565995609705935466821066659310672864052627930797953815609085963077496397668160634880⟩
def references : Fin 2 → Box := ![Part4.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 34 1 (.split 30 1 (.split 35 1 (.reuse 0) (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 51 1 (.split 59 1 (.split 72 1 (.split 67 1 (.split 4 0 (.step 29 (.step 18 (.step 38 (.close 7)))) (.step 18 (.split 6 0 (.step 7 (.step 9 (.step 15 (.close 18)))) (.step 9 (.close 7))))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 29 (.step 38 (.close 7)))) (.step 9 (.step 26 (.step 29 (.step 38 (.step 18 (.step 21 (.step 7 (.close 15))))))))) (.step 57 (.step 7 (.step 9 (.step 21 (.step 26 (.close 29))))))) (.step 9 (.step 21 (.step 29 (.step 38 (.step 18 (.close 57))))))) (.step 9 (.step 21 (.step 38 (.step 18 (.step 21 (.close 26))))))) (.step 9 (.step 53 (.step 57 (.step 62 (.step 75 (.step 52 (.step 29 (.step 18 (.step 21 (.step 7 (.close 15)))))))))))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 38 (.close 7))))) (.step 7 (.step 29 (.step 38 (.close 7))))))) (.run (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 18 (.step 53 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18)))))))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18)))))))))) (.reuse 1))
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

namespace Part7
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265565190103143347990225842026056435382960432120807626304347210514432⟩
def references : Fin 1 → Box := ![Part6.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 4 0 (.step 29 (.step 7 (.step 9 (.close 17)))) (.step 18 (.split 43 0 (.split 49 0 (.step 7 (.close 9)) (.step 9 (.step 7 (.step 15 (.close 18))))) (.step 7 (.close 9))))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 9 (.step 26 (.step 27 (.step 29 (.close 7)))))) (.step 9 (.step 29 (.step 7 (.step 18 (.close 26)))))) (.step 18 (.step 55 (.step 9 (.step 7 (.step 57 (.step 21 (.close 26)))))))) (.step 9 (.step 27 (.step 53 (.step 29 (.step 7 (.close 26))))))) (.step 9 (.step 27 (.step 52 (.step 29 (.step 7 (.close 26))))))) (.step 9 (.close 7))) (.step 7 (.step 18 (.close 7))))))) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 26 (.step 55 (.step 27 (.step 52 (.close 7))))))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 26 (.step 29 (.step 7 (.close 9)))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670692845673622083580974038683558147072011885483130880⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 26 1 (.split 35 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 12 0 (.split 34 1 (.split 36 1 (.split 42 1 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 26)))) (.step 7 (.step 9 (.step 26 (.close 29))))) (.step 9 (.split 34 1 (.split 36 1 (.step 7 (.step 15 (.step 7 (.close 26)))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.close 15))))) (.step 7 (.step 9 (.step 18 (.step 26 (.step 15 (.close 29))))))) (.step 7 (.step 9 (.step 18 (.close 26))))) (.step 9 (.close 57))) (.step 7 (.step 9 (.step 18 (.step 26 (.close 53)))))) (.step 7 (.step 9 (.step 18 (.close 52))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 18 (.step 29 (.step 37 (.step 26 (.close 38)))))))) (.step 7 (.step 9 (.step 18 (.close 29))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 22 (.step 55 (.step 27 (.step 52 (.close 7))))))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 22 (.step 29 (.step 7 (.close 9)))))) (.step 7 (.step 11 (.step 18 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29)))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762002869938770909476934032218843051222744697653955169209552006994569881630458359613348734273882013831266304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 18 (.split 21 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 4 0 (.step 15 (.step 7 (.step 9 (.step 7 (.close 15))))) (.step 9 (.step 7 (.close 15)))) (.step 9 (.step 15 (.close 7)))) (.step 15 (.split 4 0 (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9))) (.step 7 (.close 9))))) (.step 9 (.step 15 (.close 7)))) (.step 9 (.step 7 (.step 15 (.close 7)))))) (.step 15 (.step 7 (.step 11 (.step 15 (.step 17 (.close 18))))))) (.step 7 (.step 15 (.step 57 (.step 62 (.split 21 1 (.split 67 1 (.split 6 0 (.step 7 (.step 9 (.close 15))) (.step 9 (.close 7))) (.step 70 (.close 7))) (.step 7 (.step 9 (.close 15))))))))) (.step 15 (.step 21 (.step 9 (.step 15 (.step 7 (.step 18 (.step 21 (.step 22 (.close 26)))))))))) (.step 15 (.step 21 (.step 9 (.step 15 (.step 18 (.close 52))))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 15 (.step 26 (.step 29 (.split 21 1 (.split 6 0 (.step 7 (.close 15)) (.step 9 (.close 7))) (.step 7 (.step 9 (.close 15))))))))) (.step 7 (.step 15 (.step 29 (.step 57 (.step 37 (.step 7 (.step 9 (.step 7 (.close 15)))))))))) (.step 9 (.step 15 (.step 21 (.step 9 (.step 15 (.step 7 (.step 18 (.step 21 (.step 22 (.close 26))))))))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2305843011361177600, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906965641161603006070784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 10 1 (.split 12 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 18 (.step 9 (.split 67 1 (.split 4 0 (.split 51 0 (.step 9 (.close 7)) (.step 9 (.close 7))) (.step 9 (.close 7))) (.split 21 0 (.split 26 0 (.split 35 0 (.step 70 (.close 7)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9)))))) (.step 9 (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.step 57 (.split 67 1 (.split 21 0 (.split 26 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 46 (.step 54 (.close 7)))))))) (.step 9 (.step 7 (.step 9 (.close 11))))) (.step 9 (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 9 (.step 29 (.split 21 0 (.split 34 0 (.step 7 (.close 9)) (.step 15 (.step 7 (.close 9)))) (.step 7 (.close 9))))))) (.step 7 (.step 9 (.step 29 (.step 57 (.step 45 (.step 7 (.close 9)))))))) (.step 9 (.step 7 (.step 9 (.close 11))))) (.step 7 (.step 9 (.step 15 (.step 29 (.step 39 (.step 45 (.step 7 (.close 9))))))))) (.step 7 (.step 9 (.step 7 (.close 9))))) (.step 9 (.step 18 (.close 9)))) (.step 9 (.step 18 (.close 9)))) (.step 7 (.step 9 (.step 7 (.close 9))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906965641161603006070784⟩
def references : Fin 3 → Box := ![Part8.root, Part9.root, Part10.root]
def proof : Chunks.Proof 3 := (.split 6 1 (.split 10 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 21 (.step 42 (.step 53 (.step 7 (.step 18 (.close 7)))))))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 21 (.step 29 (.step 7 (.close 9)))))) (.step 7 (.step 11 (.step 18 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29))))))) (.step 7 (.step 11 (.step 18 (.step 19 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29)))))))))))) (.split 26 1 (.split 30 1 (.split 34 1 (.reuse 1) (.run (.step 7 (.step 15 (.close 7))))) (.run (.step 7 (.step 15 (.step 18 (.step 9 (.close 15))))))) (.run (.step 9 (.step 15 (.step 21 (.step 9 (.step 15 (.step 18 (.close 29)))))))))) (.run (.step 7 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.step 15 (.close 18))))) (.step 18 (.step 7 (.step 9 (.step 7 (.close 15)))))) (.step 18 (.step 52 (.close 7)))) (.step 18 (.step 7 (.step 9 (.step 7 (.close 15)))))) (.step 18 (.step 29 (.close 7)))) (.step 15 (.close 7)))))) (.reuse 2))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906965641162702517698560⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.reuse 0) (.run (.step 7 (.split 6 1 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 9 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 18 (.split 54 1 (.step 7 (.step 52 (.close 7))) (.step 9 (.step 7 (.step 18 (.close 52))))))) (.step 18 (.step 7 (.step 9 (.step 7 (.step 15 (.close 18))))))) (.step 18 (.step 29 (.close 7)))) (.step 9 (.step 15 (.step 18 (.close 15))))) (.step 9 (.close 7))))))
theorem accepted : Fast.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Fast.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part12.excludes
end FiveColour.Packed.EnumerationChunks.Projected.Case148

namespace FiveColour.Packed.EnumerationChunks.Projected.Case148
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 35 0 13 := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox 35 0).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox 35 0).upper i := by decide +kernel
lemma budget_model : (⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩ : Cut).model =
    (⟨rootBad (rootCapacity 35), 0⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => (⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩ : Cut).member i = true) = rootBad (rootCapacity 35) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem 35 0 13).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model 13)
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem 13 families = caseProblem 35 0 13 := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families 35) (Archive.root 35) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 35 0 13 projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem 35 0 13).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end FiveColour.Packed.EnumerationChunks.Projected.Case148

namespace FiveColour.Packed.EnumerationChunks.Case148
def root : Box := Archive.root 35
def families : Fin 78 → List Cut := Enumeration.families 35
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case148.original_covered points
end FiveColour.Packed.EnumerationChunks.Case148
