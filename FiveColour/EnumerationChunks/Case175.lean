module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case175
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581034647693109995948679302381139345918350729549015981121540317608631934651943878656,32908989162382482537463,5789234131009374248507346766749891419687533244750779835710650130547166070169190972551199135583887163440067555744480064067624080828260535803883819067065712488494011642056487991334880784408697916612570372223033612482063107073,0⟩
theorem header_valid : Projection.HeaderValid 14 62 0 11 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 62).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581034647693109995948679302381139345918350729549015981121540317608631934651943878656⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 11⟩]
  else if r.val = 2 then [⟨32908989162382482537463, 5789234131009374248507346766749891419687533244750779835710650130547166070169190972551199135583887163440067555744480064067624080828260535803883819067065712488494011642056487991334880784408697916612570372223033612482063107073, 0⟩]
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
def points : List Nat := [11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253312798487756537587318585147636599445770519594636673024,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285536320983370499127337524107949199905442802984197146911853160748561536079024357376,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374112039958810344625712569740456760314359196485056648085083645303521914106018791424,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787102671861633294128382337464642871569857499621475132962585601323129068381075708676069722051352552563412041728,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893553629429432637135702779553218590545297345119850178595093161732045461881935209849300206606312930590406475776,4586997231980143023221641794309520737190618225224227600722140961855382794711022530691161273308617400909824,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285536320983370499127337524107947704789267813470511824542269291991032428060032892928,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374112039958810344625712569740455265198184206971371325715499776545992806087027326976,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787102671861633294128382337464642871569857499621475132962584106206954078867390386306485853293823444544420577280,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893553629429432637135702779553218590545297345119850178595091666615870472368249887479716337848783822571415011328,4586997231980143023221641794309520737190618225224227599227024786865869109388652946822403744200598409445376,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285536320983370497442340857411034214200255997376373148013216467056058775665981259776,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787102671861633294128382337464642871569857497936478466265670615617942262773251709777433028358849792150368944128,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893553629429432637135702779553218590545297343434853511898178176026858656274111210950663512913810170177363378176,11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424,5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374112039958810342940715903043541774609172390877232649186446951611019153692975693824,4586997231980143023221641794309520737188933228557530685736435775049774970712123893997468770548204357812224]
namespace Part0
def root : Box := ⟨2147483648, 11031304526203984395224077729546701486917029021449433750258104042868224206650831422685070686845790206190305999307423049841252490124179581034647693109995948679302381139345918350729549015981121540317608631934651943878656⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.step 7 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.step 7 (.split 51 1 (.step 7 (.run (.close 29))) (.step 7 (.step 9 (.run (.close 29)))))) (.step 7 (.run (.close 9)))) (.step 7 (.step 29 (.step 7 (.run (.close 38)))))) (.step 7 (.step 39 (.step 7 (.step 29 (.step 7 (.run (.close 38)))))))) (.step 7 (.step 37 (.step 7 (.step 29 (.step 7 (.run (.close 37))))))))) (.step 29 (.step 7 (.run (.close 9))))) (.step 7 (.step 29 (.run (.close 7))))) (.step 7 (.split 22 1 (.step 7 (.step 29 (.run (.close 7)))) (.step 7 (.step 29 (.split 26 1 (.step 2 (.split 26 0 (.step 2 .point) (.split 35 1 (.step 2 .point) (.step 0 (.step 1 .point))))) (.split 35 1 (.step 2 (.split 35 0 (.step 2 .point) (.step 0 (.step 1 .point)))) (.step 0 (.step 1 .point))))))))) (.step 7 (.split 17 1 (.split 22 1 (.step 7 (.step 29 (.run (.close 7)))) (.step 7 (.step 29 (.split 26 1 (.step 2 (.split 26 0 (.step 2 .point) (.split 35 1 (.step 2 .point) (.step 0 (.step 1 .point))))) (.split 35 1 (.step 2 (.split 35 0 (.step 2 .point) (.step 0 (.step 1 .point)))) (.step 0 (.step 1 .point))))))) (.step 7 (.step 29 (.split 35 1 (.step 19 (.step 25 (.split 26 1 (.step 2 .point) (.split 35 0 (.step 2 .point) (.step 0 (.step 1 .point)))))) (.step 19 (.split 26 1 (.step 2 (.split 26 0 (.step 2 .point) (.step 0 (.step 1 .point)))) (.step 0 (.step 1 .point))))))))))
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
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285536320983370499127337524107949199905442802984197146911853160748561536079024357376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374112039958810344625712569740456760314359196485056648085083645303521914106018791424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
namespace Lift3
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787102671861633294128382337464642871569857499621475132962585601323129068381075708676069722051352552563412041728, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.run (.close 20))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift3
namespace Lift4
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893553629429432637135702779553218590545297345119850178595093161732045461881935209849300206606312930590406475776, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift4
namespace Lift5
def root : Box := ⟨4586997231980143023221641794309520737190618225224227600722140961855382794711022530691161273308617400909824, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift5
namespace Lift6
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883498633199915253311303371581548073633262778052730688241411575645208576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift6
namespace Lift7
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285536320983370499127337524107947704789267813470511824542269291991032428060032892928, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift7
namespace Lift8
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374112039958810344625712569740455265198184206971371325715499776545992806087027326976, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift8
namespace Lift9
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787102671861633294128382337464642871569857499621475132962584106206954078867390386306485853293823444544420577280, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.run (.close 20))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift9
namespace Lift10
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893553629429432637135702779553218590545297345119850178595091666615870472368249887479716337848783822571415011328, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift10
namespace Lift11
def root : Box := ⟨4586997231980143023221641794309520737190618225224227599227024786865869109388652946822403744200598409445376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift11
namespace Lift12
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787104965360249284199893948285536320983370497442340857411034214200255997376373148013216467056058775665981259776, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift12
namespace Lift13
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787102671861633294128382337464642871569857497936478466265670615617942262773251709777433028358849792150368944128, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.step 19 (.run (.close 20))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift13
namespace Lift14
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893553629429432637135702779553218590545297343434853511898178176026858656274111210950663512913810170177363378176, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift14
namespace Lift15
def root : Box := ⟨11031304526203974597457456414861827591216226218170224705794538792432397774848431640257320003887617175667569787107258858865274271405559106429770396883496948203248556397812782569731979494586248999905753267759181593575424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift15
namespace Lift16
def root : Box := ⟨5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893555922928048627207214390374112039958810342940715903043541774609172390877232649186446951611019153692975693824, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift16
namespace Lift17
def root : Box := ⟨4586997231980143023221641794309520737188933228557530685736435775049774970712123893997468770548204357812224, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 4 (.step 7 (.step 9 (.step 11 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 62) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 62) root :=
  Fast.check_sound 14 (Enumeration.families 62) (Enumeration.families_valid 62)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift17
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 62) (CoreExtension.extension 62 p) := by
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
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift14.root, upper_eq, CoreExtension.extension] using Lift14.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift15.root, upper_eq, CoreExtension.extension] using Lift15.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift16.root, upper_eq, CoreExtension.extension] using Lift16.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift17.root, upper_eq, CoreExtension.extension] using Lift17.excludes),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 62) (Archive.root 62) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 62)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case175
