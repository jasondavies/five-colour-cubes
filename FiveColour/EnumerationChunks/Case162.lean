module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case162
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906963335317494280749056⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 12⟩]
  else if r.val = 2 then [⟨32908392998381807266807, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691006121938439571168504117704742533227172821910712256014868874656400699534968387178292612729254500242869083702273, 0⟩]
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904443229329621762877716815095803433753783035401925558845793450693587522711797889167563345248373158302283501583810009023851134823371485230174522456377291140727440408576⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 59 1 (.split 67 1 (.split 16 0 (.split 17 0 (.split 72 1 (.split 21 0 (.split 26 0 (.step 7 (.step 9 (.step 7 (.close 15)))) (.split 34 0 (.step 9 (.step 7 (.step 15 (.step 18 (.close 21))))) (.step 15 (.step 7 (.close 21))))) (.step 7 (.step 9 (.step 15 (.step 17 (.close 18)))))) (.step 29 (.step 18 (.close 75)))) (.split 21 0 (.step 7 (.split 10 0 (.split 12 0 (.step 7 (.step 9 (.close 18))) (.step 9 (.step 18 (.step 15 (.step 18 (.close 21)))))) (.step 7 (.step 15 (.close 18))))) (.step 7 (.step 17 (.close 18))))) (.split 17 0 (.split 21 0 (.step 7 (.split 10 0 (.split 12 0 (.step 7 (.step 9 (.close 18))) (.step 9 (.step 18 (.step 15 (.step 18 (.close 21)))))) (.step 7 (.step 15 (.close 18))))) (.step 7 (.step 17 (.close 18)))) (.step 7 (.close 18)))) (.split 72 1 (.split 21 0 (.split 26 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.step 9 (.close 21)))) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 26 (.step 21 (.close 29))))))) (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 18 (.split 16 0 (.step 62 (.close 7)) (.step 18 (.close 7)))) (.step 9 (.split 21 0 (.step 62 (.close 7)) (.step 15 (.step 18 (.close 21)))))) (.step 18 (.split 12 0 (.step 7 (.step 9 (.step 15 (.close 18)))) (.step 9 (.step 15 (.close 7)))))) (.step 9 (.step 26 (.step 7 (.step 18 (.close 21)))))) (.step 26 (.step 62 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660749386805549175884476045519682621152070220555079396390043072223356798867118867666241883543763246395438348531780011497043064084976649831922441270776037376⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 54 1 (.reuse 0) (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 12 0 (.step 18 (.step 9 (.step 29 (.step 7 (.close 21))))) (.step 9 (.step 15 (.close 57)))) (.step 9 (.step 26 (.step 29 (.step 18 (.step 15 (.step 18 (.close 21)))))))) (.step 57 (.split 10 0 (.split 12 0 (.split 21 0 (.split 26 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.step 21 (.close 26))))) (.step 7 (.close 9))) (.step 9 (.step 15 (.step 26 (.step 7 (.step 21 (.step 29 (.close 54)))))))) (.step 7 (.step 9 (.close 15)))))) (.step 9 (.step 26 (.step 57 (.close 7))))))) (.run (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 54 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.step 9 (.close 21)))) (.step 57 (.close 7))) (.step 7 (.step 9 (.step 21 (.close 57))))) (.step 7 (.step 9 (.close 26)))) (.step 18 (.step 57 (.step 7 (.step 9 (.step 21 (.close 26))))))) (.step 54 (.step 7 (.step 9 (.step 26 (.step 57 (.step 21 (.close 29)))))))) (.step 57 (.step 62 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408309429764096, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922103644135012059424734283689937543763013994501621657295932892236761817049021836611277886126916525434455147171922812906698752944766976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 18 (.split 16 0 (.split 22 0 (.step 9 (.step 40 (.step 29 (.step 7 (.close 21))))) (.step 7 (.step 9 (.close 18)))) (.step 18 (.close 7)))) (.step 9 (.split 21 0 (.split 26 0 (.step 18 (.step 15 (.step 7 (.close 21)))) (.step 15 (.step 27 (.step 29 (.step 7 (.step 21 (.close 26))))))) (.step 15 (.step 18 (.close 21)))))) (.step 18 (.split 12 0 (.step 7 (.step 9 (.step 15 (.close 18)))) (.step 9 (.step 15 (.close 7)))))) (.step 9 (.step 29 (.step 40 (.step 26 (.step 7 (.step 15 (.step 18 (.close 21))))))))) (.step 52 (.step 7 (.close 9)))) (.step 52 (.step 7 (.close 26)))) (.step 9 (.step 52 (.step 57 (.close 7))))) (.step 52 (.step 7 (.step 9 (.close 29))))) (.step 52 (.step 7 (.close 21)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106416804706180239593862104121686846717430938697033112508062716342431670329642236900926101322629574033244563133774310270581918924800⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 12 0 (.step 18 (.split 16 0 (.split 26 0 (.step 7 (.step 9 (.step 7 (.close 21)))) (.step 9 (.step 18 (.step 21 (.step 7 (.close 26)))))) (.step 18 (.close 7)))) (.step 9 (.split 21 0 (.split 17 0 (.step 53 (.step 7 (.close 15))) (.step 18 (.close 21))) (.step 15 (.step 18 (.close 21)))))) (.step 18 (.split 12 0 (.step 7 (.step 9 (.step 15 (.close 18)))) (.step 9 (.step 15 (.close 7)))))) (.step 9 (.step 29 (.step 38 (.step 18 (.step 26 (.close 7))))))) (.step 53 (.close 7))) (.step 53 (.step 7 (.close 26)))) (.step 9 (.step 21 (.step 53 (.step 57 (.close 7)))))) (.step 53 (.step 7 (.close 9)))))) (.reuse 1)) (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 21 0 (.split 26 0 (.split 54 1 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.close 9))) (.step 9 (.close 7))) (.step 7 (.close 9))) (.step 7 (.close 9))) (.step 9 (.close 7))) (.split 54 1 (.step 70 (.step 7 (.close 9))) (.step 9 (.close 7)))) (.step 9 (.step 7 (.step 27 (.close 46))))) (.step 46 (.step 54 (.step 7 (.close 9))))) (.step 9 (.step 27 (.close 46)))) (.step 9 (.step 27 (.close 46))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537408211353600, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125759709371322780837965323211323540964281946446022615633848123170133506660649715494762566377149534960565092352⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 34 0 (.split 42 0 (.step 7 (.step 21 (.close 26))) (.split 49 0 (.step 7 (.step 29 (.close 39))) (.step 7 (.step 21 (.close 26))))) (.split 54 1 (.split 49 0 (.step 7 (.step 29 (.step 37 (.step 7 (.close 21))))) (.step 7 (.step 15 (.step 21 (.close 26))))) (.step 15 (.step 29 (.step 39 (.close 7)))))) (.step 29 (.close 7))) (.step 7 (.step 15 (.step 26 (.step 15 (.close 29)))))) (.step 18 (.step 29 (.step 40 (.step 57 (.step 7 (.step 15 (.close 26)))))))) (.step 57 (.step 7 (.step 29 (.step 37 (.step 26 (.step 37 (.step 38 (.step 15 (.step 26 (.close 52))))))))))) (.step 57 (.split 72 1 (.split 26 0 (.step 55 (.step 9 (.close 52))) (.step 7 (.close 29))) (.step 7 (.step 26 (.step 15 (.step 21 (.step 15 (.close 29))))))))) (.split 49 1 (.step 45 (.split 50 1 (.step 39 (.step 7 (.step 29 (.step 45 (.step 37 (.close 57)))))) (.step 7 (.step 29 (.step 38 (.step 57 (.step 15 (.step 37 (.step 45 (.step 52 (.close 53))))))))))) (.step 7 (.step 26 (.step 29 (.step 57 (.step 45 (.step 38 (.step 37 (.close 52))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220253520592896, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762002869938770909476934032218843051222743011011783914971860758972893583525803979570636395702645086251646976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 36 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 67 1 (.split 10 0 (.step 29 (.step 18 (.step 38 (.close 7)))) (.step 18 (.split 12 0 (.step 7 (.step 9 (.step 15 (.close 18)))) (.step 9 (.step 15 (.close 7)))))) (.step 7 (.step 9 (.step 21 (.step 26 (.close 29)))))) (.step 29 (.step 38 (.close 7)))) (.step 9 (.step 26 (.step 29 (.step 38 (.step 40 (.step 26 (.step 18 (.step 15 (.close 21)))))))))) (.step 9 (.step 21 (.step 29 (.step 38 (.step 57 (.close 7))))))) (.step 57 (.step 7 (.step 9 (.step 38 (.step 26 (.close 29))))))) (.step 9 (.step 21 (.step 38 (.step 53 (.step 18 (.close 21))))))) (.step 9 (.step 53 (.step 57 (.step 62 (.step 75 (.split 51 1 (.split 67 1 (.step 29 (.step 40 (.step 38 (.step 7 (.step 21 (.close 26)))))) (.step 7 (.step 21 (.step 26 (.step 29 (.close 52)))))) (.step 7 (.close 52))))))))) (.step 9 (.close 7))) (.step 7 (.step 29 (.step 38 (.step 7 (.close 37)))))) (.step 7 (.step 29 (.step 38 (.step 7 (.step 37 (.close 38))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986545361715200, 11031304526203979496340767072204264539074732142405299924596678035534750176926387658708231080740990161307942280966676857026506265388615646663698086943418244554037956949458658256994849188084742740360869406684291667066880⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 36 0 (.split 42 0 (.step 7 (.step 15 (.close 21))) (.split 49 0 (.step 7 (.step 15 (.step 7 (.close 21)))) (.step 7 (.step 15 (.step 21 (.close 26)))))) (.split 54 1 (.split 49 0 (.step 7 (.step 29 (.close 37))) (.step 7 (.step 15 (.step 21 (.close 26))))) (.step 15 (.step 29 (.step 37 (.step 7 (.step 21 (.close 26)))))))) (.step 29 (.close 7))) (.step 7 (.step 15 (.step 26 (.close 29))))) (.step 15 (.step 7 (.step 26 (.step 21 (.step 29 (.step 21 (.step 37 (.close 52))))))))) (.step 15 (.step 57 (.step 7 (.step 29 (.step 37 (.step 26 (.step 37 (.step 38 (.step 26 (.close 52))))))))))) (.step 15 (.step 52 (.step 7 (.step 29 (.step 26 (.step 52 (.step 26 (.close 37))))))))) (.split 49 1 (.step 45 (.split 50 1 (.split 54 1 (.step 37 (.step 7 (.step 15 (.step 29 (.close 37))))) (.step 15 (.step 29 (.step 37 (.step 7 (.step 26 (.step 37 (.step 21 (.step 39 (.close 52)))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 38 (.step 52 (.step 45 (.close 53)))))))))) (.step 7 (.step 15 (.step 26 (.step 29 (.step 52 (.step 37 (.close 52))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513087281144589661123619667021132657281149621395658961994547317675159731581776580138357858762752⟩
def references : Fin 4 → Box := ![Part3.root, Part4.root, Part5.root, Part6.root]
def proof : Chunks.Proof 4 := (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.split 49 1 (.split 50 1 (.split 59 1 (.split 21 0 (.split 26 0 (.split 34 0 (.split 36 0 (.step 7 (.step 21 (.close 26))) (.split 49 0 (.step 7 (.step 29 (.close 39))) (.step 7 (.step 21 (.close 26))))) (.split 54 1 (.split 49 0 (.step 7 (.step 29 (.step 37 (.step 7 (.close 21))))) (.step 7 (.step 15 (.step 21 (.close 26))))) (.step 15 (.step 26 (.step 7 (.step 21 (.close 26))))))) (.step 29 (.close 7))) (.step 7 (.step 15 (.close 26)))) (.step 18 (.step 26 (.step 29 (.step 40 (.step 45 (.step 18 (.step 26 (.step 37 (.step 21 (.step 15 (.step 52 (.close 57))))))))))))) (.step 26 (.step 57 (.step 62 (.step 7 (.step 21 (.step 26 (.step 15 (.close 29))))))))) (.step 26 (.step 57 (.step 62 (.split 10 0 (.split 12 0 (.step 7 (.step 29 (.step 26 (.step 38 (.step 26 (.close 52)))))) (.step 9 (.step 15 (.step 18 (.step 26 (.step 29 (.step 21 (.close 52)))))))) (.step 7 (.close 15)))))))))) (.reuse 1)) (.reuse 2)) (.step 7 (.split 35 1 (.split 36 1 (.reuse 3) (.run (.split 49 1 (.step 45 (.split 50 1 (.step 37 (.step 39 (.step 7 (.step 15 (.step 29 (.step 37 (.step 21 (.step 26 (.step 39 (.close 52)))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 26 (.step 38 (.step 52 (.step 39 (.step 45 (.step 26 (.close 53))))))))))))) (.step 7 (.step 15 (.step 29 (.step 37 (.step 52 (.step 37 (.close 52)))))))))) (.run (.step 29 (.step 38 (.step 7 (.close 37))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363263880193436446433003059153583117708465858110594397687601674116399104⟩
def references : Fin 1 → Box := ![Part7.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 30 1 (.reuse 0) (.run (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 7 (.step 9 (.step 18 (.close 53)))))) (.step 18 (.step 53 (.step 7 (.step 9 (.step 18 (.close 52))))))) (.step 18 (.step 7 (.step 9 (.step 18 (.close 29))))))))) (.run (.step 29 (.split 30 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 10 0 (.step 29 (.step 7 (.step 17 (.close 18)))) (.step 18 (.split 12 0 (.step 7 (.step 9 (.step 15 (.close 18)))) (.step 9 (.step 15 (.close 7)))))) (.step 7 (.step 9 (.step 26 (.step 21 (.close 29)))))) (.step 9 (.step 26 (.step 29 (.step 18 (.close 26)))))) (.step 9 (.step 29 (.step 27 (.step 26 (.step 54 (.step 26 (.close 57)))))))) (.step 57 (.step 7 (.step 9 (.step 29 (.close 26)))))) (.step 9 (.step 57 (.step 62 (.split 51 1 (.split 67 1 (.step 29 (.step 18 (.close 26))) (.step 7 (.step 21 (.step 26 (.step 29 (.close 53)))))) (.step 7 (.step 21 (.close 53)))))))) (.step 9 (.step 57 (.step 62 (.split 50 1 (.split 51 1 (.split 67 1 (.step 29 (.step 18 (.close 26))) (.step 7 (.step 26 (.step 29 (.close 52))))) (.step 7 (.close 52))) (.step 21 (.step 27 (.close 52)))))))) (.step 9 (.close 7))) (.step 7 (.step 18 (.close 7)))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700669196267996995238992733465414856672106961606440648704⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 26 (.step 55 (.step 27 (.close 52)))))) (.step 18 (.step 26 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 26 (.step 29 (.step 7 (.close 18))))))))) (.run (.step 7 (.step 18 (.split 26 1 (.split 35 1 (.split 43 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 72 1 (.split 12 0 (.split 34 1 (.split 36 1 (.split 42 1 (.step 7 (.step 9 (.close 26))) (.step 7 (.close 26))) (.step 7 (.step 26 (.close 29)))) (.step 7 (.step 26 (.step 29 (.step 26 (.close 37)))))) (.step 9 (.split 34 1 (.split 26 0 (.split 36 1 (.split 42 1 (.step 7 (.step 26 (.close 54))) (.step 7 (.close 15))) (.step 7 (.step 15 (.close 26)))) (.step 7 (.step 15 (.step 18 (.step 26 (.close 29)))))) (.step 7 (.close 15))))) (.step 7 (.step 18 (.step 26 (.step 15 (.step 29 (.step 15 (.close 37)))))))) (.step 7 (.step 9 (.step 18 (.step 26 (.close 54)))))) (.step 9 (.step 57 (.close 7)))) (.step 7 (.step 9 (.step 18 (.close 53))))) (.step 7 (.step 9 (.step 18 (.close 52))))) (.step 7 (.close 9))) (.step 7 (.step 9 (.step 18 (.step 29 (.step 38 (.close 37))))))) (.step 7 (.step 9 (.step 18 (.close 29)))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259414483892242368390862202108937297199104⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 22 (.step 55 (.step 27 (.close 52)))))) (.step 18 (.step 22 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 22 (.step 29 (.step 7 (.close 18)))))) (.step 7 (.step 18 (.split 26 1 (.split 35 1 (.step 18 (.step 52 (.close 53))) (.step 18 (.close 29))) (.step 18 (.close 29)))))))))) (.run (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.close 18))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 21 (.step 42 (.step 53 (.step 7 (.step 18 (.close 7)))))))) (.step 18 (.step 21 (.step 7 (.step 18 (.close 7)))))) (.step 18 (.step 21 (.step 29 (.step 7 (.close 18)))))) (.step 7 (.step 18 (.split 26 1 (.split 35 1 (.step 18 (.step 52 (.close 53))) (.step 18 (.close 29))) (.step 18 (.close 29)))))) (.step 7 (.step 18 (.split 26 1 (.split 35 1 (.split 49 1 (.step 18 (.step 19 (.step 18 (.close 53)))) (.step 18 (.step 19 (.step 25 (.step 52 (.close 53)))))) (.step 18 (.step 19 (.close 29)))) (.step 18 (.step 19 (.step 25 (.close 29))))))))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨2658455991569831745807614122708172800, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106416804706180239593862104121686846717430938697033112508062716344118312500896474592174122998927678687624605846111728584905380069376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 43 1 (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.step 18 (.split 21 1 (.split 59 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 21 0 (.split 26 0 (.split 35 0 (.step 7 (.step 9 (.step 7 (.close 15)))) (.step 9 (.step 15 (.close 7)))) (.step 9 (.step 15 (.close 7)))) (.step 9 (.step 15 (.close 7)))) (.step 15 (.close 7))) (.step 9 (.step 15 (.close 7)))) (.step 15 (.split 10 0 (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 70 (.close 7)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))))) (.step 9 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26))))))) (.step 9 (.step 15 (.close 7))))) (.step 15 (.step 7 (.step 17 (.close 18))))) (.step 7 (.step 15 (.step 57 (.step 62 (.split 21 1 (.split 67 1 (.split 21 0 (.split 26 0 (.split 35 0 (.step 7 (.close 9)) (.step 7 (.step 9 (.close 15)))) (.step 7 (.step 9 (.close 15)))) (.step 7 (.close 9))) (.step 70 (.close 7))) (.step 7 (.step 9 (.close 15))))))))) (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 22 (.step 26 (.close 53)))))))))))) (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 26 (.close 52)))))))) (.step 7 (.step 9 (.close 7)))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486925133544044904446828460660752663392827587549922106419512391428404452125762005109683513089318180565997462379363265566835607700670694307175259415813121505803906963335317494280749056⟩
def references : Fin 2 → Box := ![Part10.root, Part11.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.reuse 0) (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 42 1 (.reuse 1) (.run (.step 7 (.step 15 (.step 26 (.step 29 (.split 21 1 (.split 10 0 (.split 16 0 (.step 15 (.close 7)) (.step 7 (.close 15))) (.step 7 (.close 15))) (.step 7 (.close 15))))))))) (.run (.step 7 (.step 15 (.step 29 (.step 57 (.step 37 (.step 7 (.step 15 (.step 7 (.step 21 (.step 22 (.close 26))))))))))))) (.run (.step 9 (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 18 (.step 21 (.step 26 (.step 22 (.step 26 (.close 29)))))))))))))) (.run (.step 7 (.step 15 (.close 7))))) (.run (.step 7 (.step 15 (.step 18 (.step 15 (.close 52))))))) (.run (.step 9 (.step 15 (.step 21 (.step 22 (.step 9 (.step 15 (.step 26 (.close 29))))))))))) (.run (.step 7 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.step 18 (.step 7 (.step 15 (.close 18)))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18))))))) (.step 18 (.step 52 (.close 7)))) (.step 18 (.step 7 (.step 9 (.step 15 (.step 7 (.close 18))))))) (.step 18 (.step 29 (.close 7)))) (.step 15 (.close 7))))))
theorem accepted : Fast.check 12 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 12 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 12 families root :=
  Fast.check_sound 12 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 12 families root := Part12.excludes
end FiveColour.Packed.EnumerationChunks.Case162
