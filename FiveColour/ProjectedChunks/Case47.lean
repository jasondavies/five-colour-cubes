module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case47
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906963335317494280749056⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 13⟩]
  else if r.val = 2 then [⟨32908392998381807266807, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699534968387178292612729254500242869083702273, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752660196157072026346058709379448751222437197125439454832555514724895000915272340796766813855572299595499418464139057114073302233195717315494599303626752⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 16 0 (.step 7 (.step 18 (.split 17 0 (.step 29 (.step 7 (.close 15))) (.step 7 (.step 9 (.step 15 (.step 17 (.close 18)))))))) (.split 17 0 (.step 7 (.step 18 (.close 7))) (.step 7 (.step 17 (.close 18))))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.split 67 1 (.split 72 1 (.step 18 (.split 10 0 (.step 62 (.close 7)) (.step 7 (.step 9 (.close 15))))) (.step 9 (.step 26 (.close 7)))) (.step 26 (.step 62 (.close 7))))) (.split 59 1 (.split 67 1 (.step 57 (.step 9 (.step 18 (.close 21)))) (.step 57 (.split 12 0 (.step 7 (.step 9 (.close 21))) (.step 9 (.step 7 (.step 21 (.close 26))))))) (.step 9 (.step 26 (.step 18 (.step 15 (.close 21))))))) (.split 67 1 (.split 72 1 (.split 54 1 (.split 21 0 (.split 26 0 (.step 7 (.step 54 (.close 7))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 7 (.close 9))) (.step 57 (.close 7))) (.step 7 (.step 9 (.step 26 (.step 21 (.close 29)))))) (.step 54 (.step 7 (.step 9 (.step 21 (.step 26 (.close 29)))))))) (.step 53 (.split 51 1 (.split 54 1 (.split 67 1 (.split 72 1 (.step 18 (.split 10 0 (.step 53 (.close 7)) (.step 7 (.step 9 (.close 15))))) (.step 9 (.step 29 (.step 18 (.step 21 (.step 7 (.close 15))))))) (.step 53 (.close 7))) (.step 9 (.step 21 (.step 53 (.step 57 (.close 7)))))) (.step 53 (.close 7))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452123411166788548947610075842614534203936906263897114295763140832198601297635535107051298867378764766257533157376⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.run (.step 52 (.split 51 1 (.split 54 1 (.split 67 1 (.split 72 1 (.step 18 (.split 10 0 (.split 12 0 (.step 7 (.step 9 (.step 7 (.step 18 (.close 21))))) (.step 9 (.step 18 (.step 15 (.step 7 (.close 21)))))) (.step 7 (.step 9 (.close 15))))) (.step 9 (.step 29 (.step 18 (.step 26 (.close 7)))))) (.step 52 (.close 7))) (.step 9 (.step 52 (.step 57 (.close 7))))) (.step 52 (.close 7)))))) (.run (.split 49 1 (.split 51 1 (.split 67 1 (.split 50 1 (.split 72 1 (.split 54 1 (.split 21 0 (.split 26 0 (.step 7 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9)))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 46 (.step 70 (.step 7 (.close 9))))) (.step 46 (.step 54 (.step 7 (.close 9))))) (.step 9 (.step 27 (.close 46)))))) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 34 0 (.step 7 (.step 21 (.close 26))) (.step 45 (.step 7 (.step 15 (.step 21 (.close 26)))))) (.step 29 (.close 7))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.step 26 (.step 15 (.step 29 (.step 15 (.close 21))))))) (.step 18 (.step 26 (.step 29 (.step 38 (.step 40 (.step 45 (.step 18 (.step 15 (.step 26 (.step 15 (.step 52 (.close 53))))))))))))) (.step 26 (.step 55 (.step 9 (.step 52 (.step 7 (.step 26 (.step 29 (.step 15 (.close 21)))))))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125759709371322780840002359187658027050550392134431993794899591563799442911285855944116947676912871666748489728⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 34 0 (.step 7 (.step 21 (.close 26))) (.step 39 (.close 7))) (.step 29 (.close 7))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.step 26 (.step 15 (.step 29 (.step 15 (.close 21))))))) (.step 18 (.step 29 (.step 38 (.step 40 (.step 53 (.step 7 (.step 26 (.close 15))))))))) (.step 57 (.step 7 (.step 29 (.step 26 (.step 37 (.step 26 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52)))))))))))) (.step 45 (.split 49 1 (.step 39 (.step 7 (.step 29 (.step 38 (.step 37 (.step 26 (.step 37 (.step 39 (.close 53))))))))) (.step 7 (.step 29 (.step 52 (.step 26 (.step 37 (.close 21)))))))))))) (.run (.step 7 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.step 9 (.step 18 (.close 52)))))))))
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
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565995609705935466821066659310672864052627930797953815609085963076343475064042160128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 36 0 (.step 7 (.step 15 (.close 21))) (.step 37 (.step 7 (.step 15 (.close 21))))) (.step 29 (.close 7))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.step 15 (.step 26 (.step 21 (.close 29)))))) (.step 15 (.step 7 (.step 21 (.step 26 (.step 29 (.step 26 (.close 52)))))))) (.step 15 (.step 52 (.step 7 (.step 26 (.step 29 (.step 21 (.step 26 (.close 21))))))))) (.step 37 (.split 49 1 (.step 45 (.step 7 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.close 52))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 38 (.close 52))))))))) (.step 37 (.split 49 1 (.step 39 (.step 7 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.close 52))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 38 (.close 52))))))))) (.step 29 (.step 37 (.step 38 (.close 7)))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363263880193436446433003059153583117708465858110594397687601674116399104⟩
def references : Fin 2 → Box := ![Part2.root, Part3.root]
def proof : Chunks.Proof 2 := (.split 26 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.split 30 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.step 75 (.split 54 1 (.split 59 1 (.step 18 (.split 67 1 (.step 29 (.step 7 (.step 15 (.step 7 (.close 17))))) (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 9 (.step 26 (.step 29 (.step 18 (.step 21 (.step 7 (.close 15)))))))) (.step 9 (.step 21 (.step 29 (.step 7 (.step 18 (.step 26 (.step 7 (.close 15)))))))))) (.step 57 (.step 7 (.step 9 (.step 21 (.step 26 (.close 29))))))) (.step 9 (.step 21 (.step 38 (.step 18 (.step 21 (.close 26))))))) (.step 9 (.step 53 (.step 57 (.step 62 (.step 75 (.step 52 (.step 29 (.step 18 (.step 21 (.step 7 (.close 15)))))))))))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 38 (.close 7))))) (.step 7 (.step 29 (.step 38 (.close 7))))) (.step 7 (.step 18 (.close 7)))))) (.reuse 1)) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.step 18 (.split 67 1 (.step 29 (.close 7)) (.step 7 (.step 9 (.step 21 (.close 26)))))) (.step 9 (.step 26 (.step 27 (.step 26 (.step 18 (.step 15 (.close 21)))))))) (.step 9 (.step 29 (.step 7 (.step 18 (.close 26)))))) (.step 7 (.step 9 (.step 57 (.step 21 (.close 26)))))) (.step 9 (.step 27 (.step 53 (.step 29 (.close 26)))))) (.step 9 (.step 27 (.step 52 (.step 29 (.close 26)))))) (.step 7 (.close 9))) (.step 7 (.close 18))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670692845673622083580974038683558145919089281364656128⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.close 7))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7))))))))) (.run (.step 7 (.step 18 (.split 26 1 (.split 35 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 34 1 (.split 36 1 (.split 42 1 (.step 7 (.step 9 (.close 26))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.step 15 (.step 26 (.close 29))))) (.step 7 (.step 18 (.step 26 (.step 15 (.close 29)))))) (.step 7 (.step 9 (.step 18 (.close 26))))) (.step 9 (.close 57))) (.step 7 (.step 9 (.step 18 (.step 26 (.close 53)))))) (.step 7 (.step 9 (.step 18 (.close 52))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 18 (.step 29 (.step 37 (.step 26 (.close 38)))))))) (.step 7 (.step 9 (.step 18 (.close 29))))))))) (.run (.step 7 (.step 18 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.close 7))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 7 (.step 18 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29))))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813120238153306735105915997577543680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 30 1 (.split 21 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.step 18 (.step 15 (.split 51 1 (.split 59 1 (.split 67 1 (.step 15 (.step 9 (.step 18 (.close 15)))) (.step 15 (.split 21 0 (.split 26 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9))))) (.step 9 (.step 15 (.close 7)))) (.step 15 (.step 57 (.step 62 (.step 70 (.step 7 (.step 9 (.close 15)))))))))) (.step 15 (.step 18 (.step 9 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26))))))))) (.step 15 (.step 21 (.step 9 (.step 15 (.step 18 (.close 52))))))) (.step 7 (.step 9 (.close 7)))) (.step 7 (.step 15 (.close 7)))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 7 (.step 15 (.close 7)))))))) (.step 9 (.step 15 (.step 18 (.step 9 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26)))))))))) (.step 7 (.step 15 (.close 7)))) (.step 9 (.step 15 (.step 7 (.step 18 (.step 9 (.step 15 (.close 7)))))))) (.step 7 (.step 15 (.step 18 (.close 15))))) (.step 9 (.step 15 (.step 21 (.step 9 (.step 15 (.step 18 (.close 29)))))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906963335317494280749056⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.close 7))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 7 (.step 18 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29)))))) (.step 7 (.step 18 (.step 19 (.split 26 1 (.step 18 (.close 52)) (.step 18 (.close 29))))))))))) (.reuse 1)) (.run (.step 7 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 7 (.step 15 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18))))))) (.step 18 (.close 7))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18))))))) (.step 15 (.close 7))))))
theorem accepted : Chunks.check 13 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 13 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 13 families root :=
  Chunks.check_sound 13 families families_valid references references_excluded proof root root_valid accepted
end Part7

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 13 families root := Part7.excludes
end FiveColour.Packed.ProjectedChunks.Case47
