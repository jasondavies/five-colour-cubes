module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case172
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260034324632158138612676846049625343512027709798489669117743896486821272943871589502533568036864,18741817655939057892339,5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475069125776341470636776399003572424092354108296175801265491834031787454638626179529899799972324883525318738944,0⟩
theorem header_valid : Projection.HeaderValid 14 59 0 11 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 59).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260034324632158138612676846049625343512027709798489669117743896486821272943871589502533568036864⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨18741817655939057892339, 5789228615357111146520048038021683988773733487122101869605338720869906162809155657637697080479216605571382346201475069125776341470636776399003572424092354108296175801265491834031787454638626179529899799972324883525318738944, 0⟩]
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
def points : List Nat := [7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458198299206622473898444925461015651961326023273168764928,7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458196804090447484384759603091431783203796915254177300480,7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943892802580221761283313501435668290620926562378958268823262860125667328,11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797498561161601720831629746784392225796814106738090890859931077209253557225549206701564962646976646339454285381632,11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797496212621258691740579661514352878740355175333663628037295019453182014117487883964301659893359139064022860562432,11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396464775278045821939237254118739763343628413849368246381508361094747092391044822812881046351507037498938387858753069337050278264832]
namespace Part0
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260032287596181804126590577603936934133866658328634500150365782518736636783644921704152153718784⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.step 7 (.split 42 1 (.split 43 1 (.split 51 1 (.step 7 (.run (.close 5))) (.step 7 (.run (.close 3)))) (.step 7 (.step 3 (.step 54 (.run (.close 27)))))) (.step 7 (.step 5 (.step 37 (.run (.close 45))))))) (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 16 0 (.split 17 0 (.split 74 1 (.step 7 (.step 5 (.step 37 (.run (.close 41))))) (.step 5 (.run (.close 41)))) (.step 5 (.step 7 (.run (.close 5))))) (.step 5 (.step 7 (.run (.close 5))))) (.step 3 (.run (.close 7)))) (.step 3 (.step 7 (.run (.close 10))))) (.step 3 (.step 7 (.run (.close 10))))) (.step 7 (.step 28 (.step 45 (.step 3 (.run (.close 5)))))))) (.step 7 (.split 74 1 (.step 45 (.split 2 0 (.step 7 (.step 28 (.split 17 0 (.split 38 1 (.step 7 (.run (.close 37))) (.step 39 (.run (.close 3)))) (.step 7 (.run (.close 39)))))) (.step 7 (.step 5 (.step 39 (.run (.close 5))))))) (.step 5 (.step 7 (.step 5 (.run (.close 39)))))))) (.step 7 (.split 74 1 (.step 45 (.split 2 0 (.split 14 0 (.step 7 (.step 28 (.step 37 (.run (.close 3))))) (.step 7 (.run (.close 37)))) (.step 7 (.run (.close 37))))) (.step 7 (.step 37 (.run (.close 5))))))) (.step 7 (.step 5 (.step 19 (.run (.close 20)))))) (.step 7 (.split 38 1 (.split 56 1 (.step 20 (.step 7 (.step 5 (.step 19 (.run (.close 20)))))) (.step 5 (.step 7 (.step 5 (.run (.close 20)))))) (.step 5 (.step 7 (.step 5 (.step 20 (.step 5 .point))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part0
namespace Part1
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260032287596181804126590577603936934133866658330096003181493260345104267962343596764330680385536⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Enumeration.Proof 1 := (.split 14 1 (.split 16 1 (.reuse 0) (.step 7 (.split 38 1 (.split 56 1 (.step 20 (.split 2 0 (.step 7 (.step 11 (.step 19 (.run (.close 3))))) (.step 7 (.step 5 (.run (.close 19)))))) (.step 7 (.run (.close 19)))) (.step 7 (.step 19 (.step 5 (.split 17 1 (.step 2 .point) (.step 0 (.step 1 .point))))))))) (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 56 1 (.step 7 (.split 67 1 (.step 7 (.step 17 (.step 3 (.run (.close 5))))) (.step 3 (.run (.close 7))))) (.step 3 (.step 5 (.run (.close 17))))) (.step 3 (.step 7 (.run (.close 11))))) (.step 3 (.step 7 (.step 11 (.run (.close 27)))))) (.step 5 (.step 7 (.step 5 (.run (.close 37)))))) (.step 3 (.step 5 (.step 49 (.step 67 (.step 5 (.run (.close 41)))))))) (.step 5 (.step 7 (.step 39 (.step 5 .point))))) (.step 7 (.step 37 (.step 5 (.split 36 1 (.step 2 .point) (.step 0 (.step 1 .point))))))) (.step 7 (.split 38 1 (.step 11 (.split 56 1 (.step 17 (.step 7 (.step 5 (.run (.close 17))))) (.step 3 (.step 5 (.run (.close 17)))))) (.step 3 (.step 5 (.run (.close 17))))))) (.step 7 (.step 20 (.step 74 (.step 11 (.split 38 1 (.step 17 (.step 7 (.step 5 (.run (.close 17))))) (.step 3 (.step 5 (.run (.close 17)))))))))) (.step 7 (.step 19 (.step 67 (.step 11 (.split 56 1 (.step 17 (.step 7 (.step 5 (.run (.close 17))))) (.step 3 (.step 5 (.run (.close 17)))))))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part1
namespace Part2
def root : Box := ⟨2147483648, 11567161174868858867513347584291470413161041323746864827860183622021927069469010019990779789980987466598709041494846825188742226260034324632158138612676846049625343512027709798489669117743896486821272943871589502533568036864⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Enumeration.Proof 1 := (.step 7 (.split 2 1 (.reuse 0) (.step 3 (.split 14 1 (.split 16 1 (.split 17 1 (.split 22 1 (.step 5 (.split 34 1 (.step 5 (.step 3 (.step 5 (.step 39 (.step 41 (.step 39 (.run (.close 45)))))))) (.step 7 (.step 37 (.step 5 (.run (.close 41))))))) (.step 3 (.step 5 (.run (.close 25))))) (.step 3 (.step 5 (.run (.close 20))))) (.step 3 (.step 5 (.step 7 (.run (.close 19)))))) (.step 5 (.run (.close 17)))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.covered
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part2
theorem covered : Enumeration.Covers points 11 families root := Part2.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families 11 header := rfl
end Core
namespace Lift0
def root : Box := ⟨7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458198299206622473898444925461015651961326023273168764928, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 14 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 59) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 59) root :=
  Fast.check_sound 14 (Enumeration.families 59) (Enumeration.families_valid 59)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458196804090447484384759603091431783203796915254177300480, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 14 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 59) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 59) root :=
  Fast.check_sound 14 (Enumeration.families 59) (Enumeration.families_valid 59)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943892802580221761283313501435668290620926562378958268823262860125667328, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 14 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 59) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 59) root :=
  Fast.check_sound 14 (Enumeration.families 59) (Enumeration.families_valid 59)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
namespace Lift3
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797498561161601720831629746784392225796814106738090890859931077209253557225549206701564962646976646339454285381632, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 11 (.step 15 (.step 17 (.step 23 (.run (.close 31))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 59) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 59) root :=
  Fast.check_sound 14 (Enumeration.families 59) (Enumeration.families_valid 59)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift3
namespace Lift4
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396467482963293986797496212621258691740579661514352878740355175333663628037295019453182014117487883964301659893359139064022860562432, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 11 (.step 15 (.step 17 (.step 23 (.run (.close 31))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 59) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 59) root :=
  Fast.check_sound 14 (Enumeration.families 59) (Enumeration.families_valid 59)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift4
namespace Lift5
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214308813593929159469055614459580396464775278045821939237254118739763343628413849368246381508361094747092391044822812881046351507037498938387858753069337050278264832, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 11 (.step 15 (.step 17 (.step 23 (.run (.close 31))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 59) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 59) root :=
  Fast.check_sound 14 (Enumeration.families 59) (Enumeration.families_valid 59)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift5
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 59) (CoreExtension.extension 59 p) := by
  exact List.forall_mem_cons.mpr ⟨(by simpa only [Lift0.root, upper_eq, CoreExtension.extension] using Lift0.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift1.root, upper_eq, CoreExtension.extension] using Lift1.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift2.root, upper_eq, CoreExtension.extension] using Lift2.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift3.root, upper_eq, CoreExtension.extension] using Lift3.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift4.root, upper_eq, CoreExtension.extension] using Lift4.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift5.root, upper_eq, CoreExtension.extension] using Lift5.excludes),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 59) (Archive.root 59) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 59)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case172
