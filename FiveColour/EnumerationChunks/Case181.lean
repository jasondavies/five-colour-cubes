module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case181
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581030942346254401830425748109619067905299424909506680623491054965943681431795400704,32908989162382549646327,5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037297348910785812665766745799411394960843444438804532254114131948159551483306040611339819323235465820198712900767369397249,0⟩
theorem header_valid : Projection.HeaderValid 14 68 0 10 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 68).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581030942346254401830425748109619067905299424909506680623491054965943681431795400704⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 10⟩]
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
def points : List Nat := [11031304526203984395224077729546701486917029021449433750258104042868224206650831422685065136091031468230870315167874915232234443514283405422192892738581582375476329910400338242755981783982375427792821955691267902930944,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684893571339766347188006096692416177010695840678389846643929292058345581346029963947055043817577370728467005440,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311301910079910742730344574367897971958391919712665600,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312797026254900256415666943951766729487499938704130048,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397811321068094648591668045315073036984739525661032448,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285534468309942702068210746972189060898917150664442496662828529427217409468950118400,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374110187285382547566585792604696621307833544165301997836059013982177787495944552448,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253309806793904921229045022204784029214429283900721201152,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556396316204893105134906345675731204279455631506669568000,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285534468309942702068210746972187565782742161150757174293244660669688301449958653952,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374110187285382547566585792604695126191658554651616675466475145224648679476953088000,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883495263206581859482825615881289040767669146678379344481979112617934848,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285534468309942700383214080275274075193730345056618497764191835734714649055907020800,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374110187285382545881589125907781635602646738557477998937422320289675027082901454848]
namespace Part0
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581030942346254401830425748109619067905299424909506680623491054965943681431795400704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 7 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.step 7 (.split 51 1 (.step 7 (.step 29 (.step 7 (.run (.close 38))))) (.step 7 (.step 9 .point)))) (.step 7 (.step 9 (.step 70 .point)))) (.step 7 (.step 29 (.step 38 (.step 7 (.step 39 (.run (.close 45)))))))) (.step 7 (.step 39 (.step 7 (.step 29 (.step 38 (.step 7 (.run (.close 39))))))))) (.step 7 (.step 39 (.step 45 (.step 7 (.step 29 (.step 38 (.step 7 (.run (.close 37)))))))))) (.step 7 .point)) (.step 7 (.split 16 0 (.step 2 .point) (.split 22 1 (.step 2 .point) (.split 35 1 (.step 2 .point) (.step 0 (.step 1 .point))))))) (.step 7 (.step 19 (.step 25 (.split 17 1 (.step 2 (.split 17 0 (.step 2 .point) (.split 22 1 (.step 2 .point) (.split 35 1 (.step 2 .point) (.step 0 (.step 1 .point)))))) (.step 19 (.split 22 0 (.step 2 .point) (.split 35 1 (.step 2 .point) (.step 0 (.step 1 .point)))))))))))
theorem accepted : Enumeration.check points 10 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 10 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 10 families root :=
  Enumeration.check_sound points 10 families families_valid references references_covered proof root root_valid accepted
end Part0
theorem covered : Enumeration.Covers points 10 families root := Part0.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families 10 header := rfl
end Core
namespace Lift0
def root : Box := ⟨11031304526203984395224077729546701486917029021449433750258104042868224206650831422685065136091031468230870315167874915232234443514283405422192892738581582375476329910400338242755981783982375427792821955691267902930944, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 9 (.step 15 (.step 21 (.step 22 (.step 26 (.step 29 (.step 38 (.run (.close 52)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684893571339766347188006096692416177010695840678389846643929292058345581346029963947055043817577370728467005440, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 9 (.run (.close 10)))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311301910079910742730344574367897971958391919712665600, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.step 29 (.run (.close 38)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
namespace Lift3
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312797026254900256415666943951766729487499938704130048, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.step 25 (.step 29 (.run (.close 38))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift3
namespace Lift4
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397811321068094648591668045315073036984739525661032448, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.step 29 (.run (.close 38)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift4
namespace Lift5
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285534468309942702068210746972189060898917150664442496662828529427217409468950118400, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift5
namespace Lift6
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374110187285382547566585792604696621307833544165301997836059013982177787495944552448, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift6
namespace Lift7
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253309806793904921229045022204784029214429283900721201152, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.step 29 (.run (.close 38)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift7
namespace Lift8
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556396316204893105134906345675731204279455631506669568000, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.step 29 (.run (.close 38)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift8
namespace Lift9
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285534468309942702068210746972187565782742161150757174293244660669688301449958653952, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift9
namespace Lift10
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374110187285382547566585792604695126191658554651616675466475145224648679476953088000, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift10
namespace Lift11
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883495263206581859482825615881289040767669146678379344481979112617934848, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.step 29 (.run (.close 38)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift11
namespace Lift12
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285534468309942700383214080275274075193730345056618497764191835734714649055907020800, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift12
namespace Lift13
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374110187285382545881589125907781635602646738557477998937422320289675027082901454848, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 68) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 68) root :=
  Fast.check_sound 14 (Enumeration.families 68) (Enumeration.families_valid 68)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift13
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 68) (CoreExtension.extension 68 p) := by
  exact List.forall_mem_cons.mpr ⟨(by simpa only [Lift0.root, upper_eq, CoreExtension.extension] using Lift0.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift1.root, upper_eq, CoreExtension.extension] using Lift1.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift2.root, upper_eq, CoreExtension.extension] using Lift2.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift3.root, upper_eq, CoreExtension.extension] using Lift3.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift4.root, upper_eq, CoreExtension.extension] using Lift4.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift5.root, upper_eq, CoreExtension.extension] using Lift5.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift6.root, upper_eq, CoreExtension.extension] using Lift6.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift7.root, upper_eq, CoreExtension.extension] using Lift7.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift8.root, upper_eq, CoreExtension.extension] using Lift8.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift9.root, upper_eq, CoreExtension.extension] using Lift9.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift10.root, upper_eq, CoreExtension.extension] using Lift10.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift11.root, upper_eq, CoreExtension.extension] using Lift11.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift12.root, upper_eq, CoreExtension.extension] using Lift12.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift13.root, upper_eq, CoreExtension.extension] using Lift13.excludes),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 68) (Archive.root 68) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 68)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case181
