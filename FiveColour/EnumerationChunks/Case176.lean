module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case176
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581030942346254401830425748109619067905299424909506680623491054965943681431795400704,32908989162382549646327,5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910785812665766745799411394960843444438804532254114131948159551483306040611339819323235465820198712900767369397249,0⟩
theorem header_valid : Projection.HeaderValid 14 63 0 11 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 63).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581030942346254401830425748109619067905299424909506680623491054965943681431795400704⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨32908989162382549646327, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910785812665766745799411394960843444438804532254114131948159551483306040611339819323235465820198712900767369397249, 0⟩]
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
def points : List Nat := [11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424]
namespace Part0
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581030942346254401830425748109619067905299424909506680623491054965943681431795400704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 7 (.split 16 1 (.split 17 1 (.step 7 (.split 34 1 (.step 7 (.split 36 1 (.split 42 1 (.step 7 (.run (.close 9))) (.step 7 (.step 29 (.run (.close 38))))) (.step 7 (.step 29 (.step 38 (.step 7 (.run (.close 39)))))))) (.step 7 (.step 37 (.step 7 (.step 29 (.run (.close 37)))))))) (.step 7 .point)) (.step 7 (.step 19 (.split 17 1 (.step 2 .point) (.step 0 (.step 1 .point)))))))
theorem accepted : Enumeration.check points 11 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 11 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 11 families root :=
  Enumeration.check_sound points 11 families families_valid references references_covered proof root root_valid accepted
end Part0
theorem covered : Enumeration.Covers points 11 families root := Part0.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families 11 header := rfl
end Core
namespace Lift0
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 63) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 63) root :=
  Fast.check_sound 14 (Enumeration.families 63) (Enumeration.families_valid 63)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 63) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 63) root :=
  Fast.check_sound 14 (Enumeration.families 63) (Enumeration.families_valid 63)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 63) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 63) root :=
  Fast.check_sound 14 (Enumeration.families 63) (Enumeration.families_valid 63)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 63) (CoreExtension.extension 63 p) := by
  exact List.forall_mem_cons.mpr ⟨(by simpa only [Lift0.root, upper_eq, CoreExtension.extension] using Lift0.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift1.root, upper_eq, CoreExtension.extension] using Lift1.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift2.root, upper_eq, CoreExtension.extension] using Lift2.excludes),
    List.forall_mem_nil _⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 63) (Archive.root 63) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 63)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case176
