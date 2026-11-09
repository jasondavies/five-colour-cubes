module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case174
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,11031304526203984395224077729546701486917029021456981675107747125572707315812807960466904529286623087051983662682463608067571667840869786206932631198292948009303173984398161690121910418372529641418445790869559084843008,32908917104513633811447,5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910783464123183971966183505480246655101777156571565223628287311696793642513456346367764851812016709392942153860097,0⟩
theorem header_valid : Projection.HeaderValid 14 61 0 11 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 61).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021456981675107747125572707315812807960466904529286623087051983662682463608067571667840869786206932631198292948009303173984398161690121910418372529641418445790869559084843008⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨32908917104513633811447, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910783464123183971966183505480246655101777156571565223628287311696793642513456346367764851812016709392942153860097, 0⟩]
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
def points : List Nat := [7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458198299206622473898444925461015651961326023273168764928,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024,7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458196804090447484384759603091431783203796915254177300480,7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943892802580221761283313501435668290620926562378958268823262860125667328,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424]
namespace Part0
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021456981675107747125572707315812807960466904529286623087051983662682463608067571665803833809872446544929847259599925012931431728845921484291072035682902727702984025341689856⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 7 (.split 34 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.step 7 (.split 17 0 (.split 22 0 (.step 28 (.split 51 0 (.split 67 0 (.split 16 0 (.step 38 (.step 3 (.step 59 (.run (.close 75))))) (.step 3 (.step 38 (.run (.close 41))))) (.step 3 (.step 22 (.run (.close 26))))) (.step 3 (.step 22 (.run (.close 26)))))) (.step 3 (.step 38 (.run (.close 45))))) (.step 3 (.step 38 (.run (.close 39)))))) (.step 7 (.step 9 (.step 3 (.run (.close 10)))))) (.step 7 (.step 45 (.run (.close 7))))) (.split 42 1 (.split 43 1 (.split 51 1 (.step 7 (.split 56 1 (.step 7 (.step 28 (.split 17 0 (.step 38 (.step 3 (.step 22 (.run (.close 41))))) (.step 3 (.step 38 (.run (.close 39))))))) (.step 28 (.step 41 (.run (.close 7)))))) (.step 3 (.step 7 (.run (.close 10))))) (.step 3 (.step 7 (.run (.close 10))))) (.step 7 (.step 28 (.step 41 (.step 7 (.step 26 (.step 39 (.run (.close 45)))))))))) (.step 7 (.step 39 (.run (.close 7))))) (.split 36 1 (.split 38 1 (.split 42 1 (.split 43 1 (.split 51 1 (.step 7 (.split 56 1 (.step 7 (.step 29 (.step 38 (.step 3 (.run (.close 7)))))) (.step 28 (.step 38 (.run (.close 3)))))) (.step 3 (.step 7 (.run (.close 9))))) (.step 3 (.step 7 (.run (.close 9))))) (.step 7 (.step 29 (.step 38 (.step 7 (.step 22 (.step 39 (.run (.close 45))))))))) (.step 3 (.step 28 (.step 38 (.run (.close 3)))))) (.step 7 (.step 29 (.step 38 (.step 7 (.run (.close 39)))))))) (.step 7 (.step 37 (.split 35 1 (.step 37 (.split 38 1 (.step 7 (.step 28 (.step 37 (.run (.close 7))))) (.step 28 (.step 37 (.run (.close 7)))))) (.step 29 (.step 37 (.run (.close 7)))))))))
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
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021456981675107747125572707315812807960466904529286623087051983662682463608067571667840869786206932631198292948009303173984398161690121910418372529641418445790869559084843008⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Enumeration.Proof 1 := (.step 7 (.split 16 1 (.split 17 1 (.reuse 0) (.step 7 (.split 35 1 (.step 4 (.step 5 .point)) (.step 3 (.step 4 .point))))) (.step 7 (.split 35 1 (.split 38 1 (.step 7 (.run (.close 19))) (.step 3 (.step 7 (.step 19 (.split 17 1 (.step 2 .point) (.step 0 (.step 1 .point))))))) (.step 3 (.step 7 (.step 19 (.split 17 1 (.step 2 .point) (.step 0 (.step 1 .point))))))))))
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
theorem covered : Enumeration.Covers points 11 families root := Part1.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families 11 header := rfl
end Core
namespace Lift0
def root : Box := ⟨7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458198299206622473898444925461015651961326023273168764928, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 14 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 61) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 61) root :=
  Fast.check_sound 14 (Enumeration.families 61) (Enumeration.families_valid 61)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 61) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 61) root :=
  Fast.check_sound 14 (Enumeration.families 61) (Enumeration.families_valid 61)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943894487576888458196804090447484384759603091431783203796915254177300480, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 14 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 61) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 61) root :=
  Fast.check_sound 14 (Enumeration.families 61) (Enumeration.families_valid 61)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
namespace Lift3
def root : Box := ⟨7547924849643082704483109161976537781833842440832880861677663375040558226319177716690205175990284943892802580221761283313501435668290620926562378958268823262860125667328, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 5 (.step 7 (.step 8 (.step 14 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 61) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 61) root :=
  Fast.check_sound 14 (Enumeration.families 61) (Enumeration.families_valid 61)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift3
namespace Lift4
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 61) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 61) root :=
  Fast.check_sound 14 (Enumeration.families 61) (Enumeration.families_valid 61)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift4
namespace Lift5
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 61) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 61) root :=
  Fast.check_sound 14 (Enumeration.families 61) (Enumeration.families_valid 61)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift5
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 61) (CoreExtension.extension 61 p) := by
  exact List.forall_mem_cons.mpr ⟨(by simpa only [Lift0.root, upper_eq, CoreExtension.extension] using Lift0.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift1.root, upper_eq, CoreExtension.extension] using Lift1.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift2.root, upper_eq, CoreExtension.extension] using Lift2.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift3.root, upper_eq, CoreExtension.extension] using Lift3.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift4.root, upper_eq, CoreExtension.extension] using Lift4.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift5.root, upper_eq, CoreExtension.extension] using Lift5.excludes),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 61) (Archive.root 61) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 61)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case174
