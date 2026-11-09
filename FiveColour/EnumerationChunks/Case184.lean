module
public import FiveColour.CoreExtension
public import FiveColour.EnumerationRoot
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case184
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def header : Archive.Header := ⟨2147483648,9797766621314684873895700802803279209044463565250435826431802399782427750682958173030522736212200164190975978218718620474601171949370906567219166250139238367774664219721329030719744001651996983038050304,37631355645286554598391,5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969542117842042700880638937423209499416432818949836275778454799724524958750082049,0⟩
theorem header_valid : Projection.HeaderValid 14 71 0 9 header := by decide +kernel
def originalUpper : Nat := 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402
theorem upper_eq : originalUpper = (Archive.root 71).upper := by decide +kernel
namespace Core
def root : Box := ⟨2147483648, 9797766621314684873895700802803279209044463565250435826431802399782427750682958173030522736212200164190975978218718620474601171949370906567219166250139238367774664219721329030719744001651996983038050304⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 9⟩]
  else if r.val = 2 then [⟨37631355645286554598391, 5789234131009374248507346766749891419687533244750779835710650130547166070169194094299749451576118545037299870639182381912436331657977804152126969542117842042700880638937423209499416432818949836275778454799724524958750082049, 0⟩]
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
def points : List Nat := [9797766621314684873895700802803279209044463565250435826431802399782427750680250487782357877946196029444236597224120020632047268711004169013855476202585748153166782506238860784174637384925646152708128768,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019687237526925308200272872355647414909864189930097319829952389107852199016525392395420902602778855919180125831168,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888986582279109222787085608067853405258525670057007316331351780655908464069658157599849161348643748701011968,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367047019911026960058923082693236820888242733285274332743750913927426793285080234487183277293568,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814249233408176778596804047355250439004704079760430189256930546069536768,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814247548411510081683313458343434344866027550707605254283278152017903616,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814247548411510081681818342168444831180705181123736496754170133026439168,9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814247548411510081681816880666807500277788245089504008700551973797101568,4898883310657342436947850401401639604522231782621865961233415550616320366321965616110741525336193389532194200894785594613284451443746838857038287830814291723854946123020983781346010253778910298901577728,3351951982485649274893506254966832028199557982459278192872501530592114478825013684220232846537292309444022252589191502448545331423742609920123714905571328,2778085064617144576105725363991525314606098748847123202110499344886616874258147137328016976093874684958111966928837087131628208128,5415370496329716527311179848441611171698709447641113026288209960404944613572982681708506240371247310075137267196852008837447680,5415370496329716527311179848441611169661673471306626940019765956992233149436501454731012928462023963042282376219295371629690880,5415370496329716527311179848441611169661673471306626940019764271995566452523010865719196834323347433989457441245642977578057728,5415370496329716527311179848441611169661673471306626940019764271995566452521515749544207320638025064405588683716534958586593280,5415370496329716527311179848441611169661673471306626940019764271995566452521514288042569989735108128371356195662916799357255680,4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727077955036054772125747847545790361722028679175375484107249798059393024,3351951982485649274893506249551461531869841455148098344430890360930441007518386744200471944535059250755478376280035741149590229253107840248463214063386624,2772669694120814859578414184143083703436437075375816575170479583984614641199458593451707820332575729855941332159165426630786023424,2707685248164858261307045101702230179137145581421695874189924835437299514736901684233389234397225565285854802216350477426098176,2348542582773833227889480596789337027375685918901653264540261383265623253550760202013820196146623504843800576,2239744742177804210557442280568444281491638830628482505311722515192228022938711066578639348073418981376,2037035976334486086268449058402711554884438805399350479072292207904502497525191507995262976,3369993333393832970411733414228436153026200721425991256298515070976]
namespace Part0
def root : Box := ⟨2147483648, 9797766621314684873895700802803279209044463565250435826431802399782427750682958173030522736212200164190975978218718620474601171949370906567219166250139238367774664219721329030719744001651996983038050304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 7 (.split 16 1 (.step 7 (.split 34 1 (.step 7 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 2 .point) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point)))) (.step 7 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 43 0 (.split 51 0 (.step 2 .point) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point)))))) (.step 7 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.step 2 .point) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))) (.step 0 (.step 1 .point))))))
theorem accepted : Enumeration.check points 9 families references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 9 families (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 9 families root :=
  Enumeration.check_sound points 9 families families_valid references references_covered proof root root_valid accepted
end Part0
theorem covered : Enumeration.Covers points 9 families root := Part0.covered
theorem root_eq : root = Projection.root header := rfl
theorem families_eq : families = Projection.families 9 header := rfl
end Core
namespace Lift0
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750680250487782357877946196029444236597224120020632047268711004169013855476202585748153166782506238860784174637384925646152708128768, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 9 (.step 10 (.run (.close 46))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift0
namespace Lift1
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019687237526925308200272872355647414909864189930097319829952389107852199016525392395420902602778855919180125831168, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 9 (.step 10 (.run (.close 46))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift1
namespace Lift2
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888986582279109222787085608067853405258525670057007316331351780655908464069658157599849161348643748701011968, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 9 (.step 10 (.run (.close 46))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift2
namespace Lift3
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367047019911026960058923082693236820888242733285274332743750913927426793285080234487183277293568, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.run (.close 46))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift3
namespace Lift4
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814249233408176778596804047355250439004704079760430189256930546069536768, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 26 (.step 27 (.step 30 (.run (.close 46)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift4
namespace Lift5
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814247548411510081683313458343434344866027550707605254283278152017903616, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 22 (.step 27 (.step 30 (.run (.close 46)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift5
namespace Lift6
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814247548411510081681818342168444831180705181123736496754170133026439168, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 27 (.step 30 (.run (.close 46))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift6
namespace Lift7
def root : Box := ⟨9797766621314684873895700802803279209044463565250435826431802399782427750677542802534193019684888984342534367044982875050625572836814247548411510081681816880666807500277788245089504008700551973797101568, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.run (.close 46))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift7
namespace Lift8
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320366321965616110741525336193389532194200894785594613284451443746838857038287830814291723854946123020983781346010253778910298901577728, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 15 (.step 16 (.step 22 (.step 26 (.step 28 (.step 29 (.step 31 (.run (.close 37)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift8
namespace Lift9
def root : Box := ⟨3351951982485649274893506254966832028199557982459278192872501530592114478825013684220232846537292309444022252589191502448545331423742609920123714905571328, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 15 (.step 16 (.step 22 (.step 26 (.step 28 (.step 29 (.step 31 (.run (.close 37)))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift9
namespace Lift10
def root : Box := ⟨2778085064617144576105725363991525314606098748847123202110499344886616874258147137328016976093874684958111966928837087131628208128, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 15 (.step 16 (.step 22 (.step 26 (.step 28 (.step 9 (.step 29 (.step 21 (.step 22 (.step 26 (.run (.close 31))))))))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift10
namespace Lift11
def root : Box := ⟨5415370496329716527311179848441611171698709447641113026288209960404944613572982681708506240371247310075137267196852008837447680, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 28 (.step 29 (.step 31 (.run (.close 37)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift11
namespace Lift12
def root : Box := ⟨5415370496329716527311179848441611169661673471306626940019765956992233149436501454731012928462023963042282376219295371629690880, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 26 (.step 28 (.step 29 (.step 31 (.run (.close 37))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift12
namespace Lift13
def root : Box := ⟨5415370496329716527311179848441611169661673471306626940019764271995566452523010865719196834323347433989457441245642977578057728, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 22 (.step 28 (.step 29 (.step 31 (.run (.close 37))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift13
namespace Lift14
def root : Box := ⟨5415370496329716527311179848441611169661673471306626940019764271995566452521515749544207320638025064405588683716534958586593280, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 28 (.step 29 (.step 31 (.run (.close 37)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift14
namespace Lift15
def root : Box := ⟨5415370496329716527311179848441611169661673471306626940019764271995566452521514288042569989735108128371356195662916799357255680, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 15 (.step 16 (.step 28 (.step 29 (.step 31 (.run (.close 37)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift15
namespace Lift16
def root : Box := ⟨4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727077955036054772125747847545790361722028679175375484107249798059393024, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.step 18 (.run (.close 19)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift16
namespace Lift17
def root : Box := ⟨3351951982485649274893506249551461531869841455148098344430890360930441007518386744200471944535059250755478376280035741149590229253107840248463214063386624, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.step 18 (.run (.close 19)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift17
namespace Lift18
def root : Box := ⟨2772669694120814859578414184143083703436437075375816575170479583984614641199458593451707820332575729855941332159165426630786023424, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.run (.close 18))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift18
namespace Lift19
def root : Box := ⟨2707685248164858261307045101702230179137145581421695874189924835437299514736901684233389234397225565285854802216350477426098176, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.step 18 (.run (.close 19)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift19
namespace Lift20
def root : Box := ⟨2348542582773833227889480596789337027375685918901653264540261383265623253550760202013820196146623504843800576, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.step 18 (.run (.close 19)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift20
namespace Lift21
def root : Box := ⟨2239744742177804210557442280568444281491638830628482505311722515192228022938711066578639348073418981376, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.step 14 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift21
namespace Lift22
def root : Box := ⟨2037035976334486086268449058402711554884438805399350479072292207904502497525191507995262976, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.step 18 (.run (.close 19)))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift22
namespace Lift23
def root : Box := ⟨3369993333393832970411733414228436153026200721425991256298515070976, originalUpper⟩
def proof : Chunks.Proof 0 := (.step 3 (.step 7 (.step 8 (.step 11 (.step 14 (.step 17 (.step 18 (.run (.close 19)))))))))
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem accepted : Fast.check 14 (Enumeration.families 71) Fin.elim0 root proof = true := by decide +kernel
theorem excludes : Chunks.Excludes 14 (Enumeration.families 71) root :=
  Fast.check_sound 14 (Enumeration.families 71) (Enumeration.families_valid 71)
    Fin.elim0 (fun i => Fin.elim0 i) proof root root_valid accepted
end Lift23
theorem lifts : ∀ p ∈ Core.points,
    Chunks.Excludes 14 (Enumeration.families 71) (CoreExtension.extension 71 p) := by
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
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift18.root, upper_eq, CoreExtension.extension] using Lift18.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift19.root, upper_eq, CoreExtension.extension] using Lift19.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift20.root, upper_eq, CoreExtension.extension] using Lift20.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift21.root, upper_eq, CoreExtension.extension] using Lift21.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift22.root, upper_eq, CoreExtension.extension] using Lift22.excludes),
    List.forall_mem_cons.mpr ⟨(by simpa only [Lift23.root, upper_eq, CoreExtension.extension] using Lift23.excludes),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem covered : Enumeration.Covers [] 14 (Enumeration.families 71) (Archive.root 71) := by
  intro x hx hp
  have he := CoreExtension.original_exclusion header_valid (Enumeration.problem_model 71)
    (by simpa only [Core.root_eq, Core.families_eq] using Core.covered) lifts
  exact False.elim (he x (by simpa only [Archive.root_model] using hx)
    (by simpa only [Enumeration.problem_model] using hp))
end FiveColour.Packed.EnumerationChunks.Case184
