module
public import FiveColour.EnumerationChunks.Case171.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case171
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part714
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11578468272786241545616291232212652993601693502181331052907722459900959428036032868933181181691576894787334192322611497974422571679741628113057987724808474041815519811602924600688708150912867859397480117638639398937538069505⟩
def references : Fin 2 → Box := ![Part712.root, Part713.root]
def proof : Chunks.Proof 2 := (.split 48 1 (.split 51 1 (.split 57 1 (.split 63 1 (.reuse 0) (.step 68 (.step 47 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 47 (.run (.close 2))) (.step 27 (.step 9 (.step 2 (.run (.close 55)))))) (.step 27 (.step 9 (.step 2 (.run (.close 55)))))) (.step 9 (.run (.close 18)))) (.step 9 (.run (.close 18)))) (.step 27 (.step 9 (.run (.close 18))))) (.step 27 (.run (.close 47)))) (.step 27 (.run (.close 47)))) (.step 27 (.run (.close 47)))) (.step 27 (.step 9 (.run (.close 18))))) (.step 9 (.step 68 (.run (.close 2)))))))) (.step 10 (.step 68 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 49 0 (.split 50 0 (.step 47 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 30 (.step 10 (.run (.close 18))))) (.step 30 (.run (.close 47)))) (.step 30 (.run (.close 47)))) (.step 30 (.run (.close 47)))) (.step 30 (.step 10 (.run (.close 18))))) (.step 2 (.run (.close 7))))))) (.reuse 1)) (.step 3 (.step 47 (.split 4 0 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 49 0 (.split 50 0 (.step 47 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 55 (.run (.close 18)))) (.step 3 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part712.covered
  · exact Part713.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part714
namespace Part715
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466630849329683567905859567268172708289337583702612939375551806477580297244069910287453651857166542874001578267568429382847431681⟩
def references : Fin 1 → Box := ![Part714.root]
def proof : Chunks.Proof 1 := (.split 44 1 (.split 46 1 (.split 47 1 (.reuse 0) (.step 10 (.step 68 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 49 0 (.split 50 0 (.step 47 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 30 (.step 10 (.run (.close 18))))) (.step 30 (.run (.close 47)))) (.step 30 (.run (.close 47)))) (.step 30 (.run (.close 47)))) (.step 30 (.step 10 (.step 48 (.run (.close 2)))))) (.step 2 (.run (.close 7))))))) (.step 10 (.step 48 (.step 68 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 49 0 (.split 50 0 (.step 47 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 30 (.step 10 (.step 2 (.run (.close 7)))))) (.step 30 (.run (.close 47)))) (.step 30 (.run (.close 47)))) (.step 30 (.run (.close 47)))) (.step 30 (.step 10 (.step 48 (.run (.close 2)))))) (.step 2 (.run (.close 7)))))))) (.step 3 (.step 47 (.split 4 0 (.split 10 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 49 0 (.split 50 0 (.step 47 (.run (.close 2))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 55 (.run (.close 2)))) (.step 30 (.step 27 (.run (.close 68))))) (.step 30 (.step 27 (.run (.close 68))))) (.step 2 (.run (.close 7)))) (.step 55 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part714.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part715
namespace Part716
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633493553558731305162979691997315457108040357998414760245496520234111902394022818244764937777300841168118901643194558005117953⟩
def references : Fin 1 → Box := ![Part715.root]
def proof : Chunks.Proof 1 := (.split 33 1 (.split 37 1 (.split 41 1 (.reuse 0) (.step 27 (.step 3 (.split 35 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 9))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 43))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 4))))))) (.step 9 (.step 55 (.step 31 (.run (.close 2)))))) (.step 27 (.step 3 (.split 35 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 9))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 43))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 4)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part715.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part716
namespace Part717
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633493553558731305162979691997317543034869417457806245702502980429936102458059756766674980054882835962142497288031823306163201⟩
def references : Fin 1 → Box := ![Part716.root]
def proof : Chunks.Proof 1 := (.split 29 1 (.split 31 1 (.reuse 0) (.step 2 (.step 27 (.step 3 (.split 35 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 9))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 43))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 27 (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 9)))))))) (.step 3 (.step 47 (.split 14 1 (.split 35 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 27 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part716.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part717
namespace Part718
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633493553558731305162979691997317543034869417457806245704228417016635312680352292402435195365351415121789119515683570370741249⟩
def references : Fin 1 → Box := ![Part717.root]
def proof : Chunks.Proof 1 := (.split 19 1 (.split 23 1 (.reuse 0) (.step 9 (.step 3 (.split 14 1 (.split 74 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 27))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2))))))) (.step 9 (.step 3 (.split 14 1 (.split 74 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 27))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part717.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part718
namespace Part719
def root : Box := ⟨5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143660095799296, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489546046743747163599074927741249321496412181675892264487865926402228630605643956554803549570049⟩
def references : Fin 1 → Box := ![Part718.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 40 1 (.split 9 1 (.split 18 1 (.reuse 0) (.step 9 (.step 3 (.split 14 1 (.split 74 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 27))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2))))))) (.step 3 (.step 47 (.split 14 1 (.split 35 1 (.split 72 1 (.split 74 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 27 (.run (.close 2))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part718.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part719
namespace Part720
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5386384305058361004742352767262323884014450870428316095473833504535891239340061910983382991412603112397224795841748301111916164446258220153078748364196322161922488082324998122415890048873022919260442526463424462849⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 10 0 (.split 16 0 (.split 46 0 (.split 49 0 (.split 50 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 18 0 (.split 19 0 (.step 18 (.run (.close 2))) (.step 32 (.run (.close 2)))) (.step 32 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.split 18 0 (.split 19 0 (.step 18 (.run (.close 43))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.step 18 (.run (.close 7))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 18 (.split 17 0 (.step 2 (.run (.close 27))) (.step 18 (.run (.close 27)))))) (.step 18 (.split 17 0 (.step 2 (.run (.close 27))) (.step 18 (.run (.close 7)))))) (.step 18 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 2)))))) (.split 18 0 (.split 19 0 (.split 29 0 (.split 31 0 (.split 17 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 18 (.run (.close 43)))) (.step 18 (.run (.close 43)))) (.step 18 (.step 20 (.step 3 (.run (.close 2)))))) (.step 18 (.split 17 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2))))))) (.split 18 0 (.split 19 0 (.split 29 0 (.split 31 0 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 18 (.run (.close 43)))) (.step 18 (.run (.close 43)))) (.step 18 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))) (.step 18 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part720
namespace Part721
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789228620738230173804034131261839887132599403310184796029290053742355856776348164147103449023604485202943736668706988826901059686966865888892653984476987882379454149462056129498893871025932280707963446231338695087591784449⟩
def references : Fin 1 → Box := ![Part720.root]
def proof : Chunks.Proof 1 := (.split 73 0 (.split 74 0 (.split 4 0 (.split 9 0 (.reuse 0) (.split 10 0 (.split 16 0 (.split 22 0 (.split 34 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.run (.close 2))) (.step 32 (.run (.close 2)))) (.step 32 (.run (.close 2)))) (.step 32 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))))) (.step 18 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 29 0 (.split 31 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 18 (.run (.close 7)))) (.step 18 (.run (.close 7)))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 43))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 43))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 43))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 7))))))) (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 7)))))) (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part720.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part721
namespace Part722
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789234136395753411692881233497288307929283439123939273127918849699299165322453703940061308507015484572303887281284959046007735936664030834948753505610033779735077471947072871780061722223870482215386987168686729455863857153⟩
def references : Fin 1 → Box := ![Part721.root]
def proof : Chunks.Proof 1 := (.split 45 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 60 0 (.split 70 0 (.split 72 0 (.reuse 0) (.step 18 (.split 4 0 (.split 10 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))) (.step 3 (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))) (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 42)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 18 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 30)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 9))) (.step 24 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 30)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))) (.step 18 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part721.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part722
namespace Part723
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789234136395753411692881233497288307929283439123939273127918849699299165322453703940061308507015484577470911233290550249663539483452673827824990078829604012900724275787137953986572044365918773127028087356227333620184907777⟩
def references : Fin 1 → Box := ![Part722.root]
def proof : Chunks.Proof 1 := (.split 27 0 (.split 32 0 (.split 35 0 (.split 37 0 (.split 38 0 (.split 39 0 (.split 40 0 (.reuse 0) (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 42)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 18 (.split 40 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 43 (.run (.close 2))))))) (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.run (.close 2))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.run (.close 2))) (.step 43 (.run (.close 3)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 18 (.split 37 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 30)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 43 (.run (.close 31)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part722.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part723
namespace Part724
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789234136395753411692881233497288307929283439123939273127918849699299165322453703940061308507015484577470911233290550249663539483452673827824991933314050051360985999860420443338900508931663494531227822319375446531558604801⟩
def references : Fin 1 → Box := ![Part723.root]
def proof : Chunks.Proof 1 := (.split 13 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 26 0 (.reuse 0) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 3 (.run (.close 2))) (.step 29 (.run (.close 2)))) (.step 43 (.run (.close 3)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 18 (.split 40 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 43 (.run (.close 2))))))) (.step 3 (.step 18 (.split 40 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 27)))) (.step 3 (.run (.close 27)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 43 (.run (.close 31))))))) (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2))))))) (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 27)))) (.step 3 (.run (.close 27)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 42)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part723.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part724
namespace Part725
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789234136395753411692881233497288307929283439123939273127918849699299165322453703940061308507015484577470911233290550249663539483452673827824991933314050051360985999860420443338900508932994020601228583186189242279918567425⟩
def references : Fin 1 → Box := ![Part724.root]
def proof : Chunks.Proof 1 := (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.reuse 0) (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 31 (.split 21 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 42)))) (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 11 (.run (.close 2))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 11 (.run (.close 9)))) (.step 42 (.run (.close 3))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 10)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part724.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part725
namespace Part726
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789234136395753411692881238169227500374411343012498997365017166393397555575044377710645397235413952407791272665416921743349084586375170422884493045520563506380161787559793790430188266721597561145998213978493476690512053249⟩
def references : Fin 1 → Box := ![Part725.root]
def proof : Chunks.Proof 1 := (.split 1 0 (.split 52 0 (.split 65 0 (.split 5 0 (.split 6 0 (.reuse 0) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.run (.close 2))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 21 0 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2))))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.step 3 (.run (.close 7))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 68))))))) (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.step 2 (.run (.close 7)))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 43))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part725.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part726
namespace Part727
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789239652048016513680179966897434931288206951125608086251332488484335124015486382914734416812337116632819537289142162893057630383099731547540297778534904996629683633157476509333671647886700733144483682521907039588609688577⟩
def references : Fin 1 → Box := ![Part726.root]
def proof : Chunks.Proof 1 := (.split 26 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 72 1 (.reuse 0) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 29 (.step 38 (.step 75 (.run (.close 43))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 28 (.step 41 (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 2 (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 28 (.run (.close 41))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 2 (.run (.close 43)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 3 (.step 18 (.step 38 (.split 4 0 (.split 9 0 (.split 10 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 29 (.run (.close 38))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2)))))))) (.step 29 (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part726.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part727
namespace Part728
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 5789239652048016513680179966897434931288206955177869383986680773662644066235079471292798035330203449933430644362205390184087551513399328548032779187687283025770181834753217618246677503843556235236481638577246094209791820801⟩
def references : Fin 1 → Box := ![Part727.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 25 1 (.reuse 0) (.step 2 (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 31 0 (.split 33 0 (.split 41 0 (.step 28 (.run (.close 2))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 27))) (.step 27 (.step 2 (.run (.close 7))))) (.step 27 (.step 42 (.run (.close 2))))) (.step 7 (.run (.close 2))))))) (.step 2 (.step 31 (.split 35 1 (.step 3 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.step 2 (.step 57 (.run (.close 2))))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 18 (.run (.close 2))))))) (.step 2 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 27))) (.step 27 (.step 2 (.run (.close 7))))) (.step 27 (.step 42 (.run (.close 2))))) (.step 7 (.run (.close 2)))))))) (.step 2 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 27))) (.step 27 (.step 2 (.run (.close 7))))) (.step 27 (.step 42 (.run (.close 2))))) (.step 7 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part727.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part728
namespace Part729
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11572820244868825110617489347147286435501031520173448112629217960195680675557195725100238587372829016878080046959121575284810558432850171832960175068751430976887978220463969272414956650653451656252229519258095542698851173377⟩
def references : Fin 1 → Box := ![Part728.root]
def proof : Chunks.Proof 1 := (.split 14 1 (.split 71 1 (.split 74 1 (.reuse 0) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 11 (.step 77 (.split 16 0 (.split 17 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 42 (.run (.close 67)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 42 (.step 67 (.run (.close 2))))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 29 (.step 31 (.split 35 1 (.step 18 (.split 74 1 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 72 1 (.split 18 0 (.split 22 0 (.split 23 0 (.split 29 0 (.split 31 0 (.step 74 (.step 3 (.run (.close 2)))) (.step 68 (.run (.close 74)))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 74)))) (.step 3 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 74 (.run (.close 75)))) (.step 67 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 32)))) (.step 3 (.run (.close 2)))) (.step 67 (.step 3 (.run (.close 2)))))) (.step 74 (.run (.close 38))))))) (.step 3 (.split 71 1 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 11 (.step 77 (.split 16 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 17))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 42 (.run (.close 67)))))) (.step 3 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 42 (.step 67 (.run (.close 18))))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 18)))) (.step 7 (.run (.close 3))))) (.step 74 (.step 3 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part728.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part729
namespace Part730
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11572820244868825110617489347147286435501031520177405399052787632740648715893510080140800688958451114001955742443268155720869130229548670067401799924799869112305337426663074061401272675523138590024373086074431754252430869505⟩
def references : Fin 1 → Box := ![Part729.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 39 1 (.split 42 1 (.split 58 1 (.split 8 1 (.reuse 0) (.step 11 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 11 (.run (.close 2))) (.step 2 (.run (.close 11)))) (.step 2 (.run (.close 11)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 2 (.step 18 (.split 14 1 (.step 3 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 27 (.step 42 (.step 31 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 61 (.step 18 (.run (.close 7)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 43 (.step 42 (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 27 (.step 42 (.run (.close 2)))) (.step 43 (.run (.close 42)))) (.step 43 (.run (.close 42)))) (.step 43 (.run (.close 42)))) (.step 3 (.run (.close 42)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part729.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part730
namespace Part731
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11578468272786241545611387564831695691227734228001108554102154436602374103554232477140612436800441573995897538174264723716265121565458231059854495311547054131389619567107188811249016666261961428036132225731269450185894265857⟩
def references : Fin 1 → Box := ![Part730.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 73 1 (.split 24 1 (.split 34 1 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 2 (.step 43 (.step 18 (.split 14 1 (.step 3 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 27 (.run (.close 7))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 27 (.run (.close 2)))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 24 (.step 2 (.run (.close 30))))) (.step 24 (.step 2 (.run (.close 30))))) (.step 3 (.run (.close 7))))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part730.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part731
namespace Part732
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11578468272786241545616291232208086097475655660287667812495352959626971186181443659698602405917115855247611182807105645849981768444821758422325713348770023126945936744268077577725293704281273662625476547845059012648902853633⟩
def references : Fin 1 → Box := ![Part731.root]
def proof : Chunks.Proof 1 := (.split 66 1 (.split 67 1 (.split 6 1 (.split 12 1 (.split 13 1 (.reuse 0) (.step 2 (.step 3 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 24 (.step 2 (.run (.close 30))))) (.step 24 (.step 2 (.run (.close 30))))) (.step 3 (.run (.close 7))))))))) (.step 2 (.step 18 (.step 31 (.split 35 1 (.step 3 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.step 2 (.step 15 (.step 2 (.run (.close 7)))))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 18 (.run (.close 2)))))))) (.step 2 (.step 18 (.step 31 (.split 35 1 (.step 3 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 9 (.run (.close 2))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 9 (.run (.close 2)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 18 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part731.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part732
namespace Part733
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11578468272786241545616291232212652993601693502181331052907722459900956076084047261538333103605038097860723994652873269860921231525532533256046332641947063639721548152644677772738247002681974615047059459822130899128792646657⟩
def references : Fin 1 → Box := ![Part732.root]
def proof : Chunks.Proof 1 := (.split 57 1 (.split 63 1 (.split 64 1 (.reuse 0) (.step 67 (.step 3 (.step 18 (.step 31 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 8 0 (.split 14 0 (.split 26 0 (.split 35 0 (.split 44 0 (.split 48 0 (.step 3 (.run (.close 2))) (.step 67 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 68 (.run (.close 67)))) (.step 68 (.run (.close 67)))) (.step 67 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2))))))))) (.step 67 (.step 29 (.step 11 (.step 3 (.step 32 (.split 14 1 (.split 35 1 (.split 72 1 (.step 18 (.split 74 1 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 71 1 (.split 64 0 (.split 14 0 (.split 29 0 (.split 31 0 (.step 3 (.run (.close 2))) (.step 66 (.run (.close 7)))) (.step 18 (.run (.close 2)))) (.step 11 (.step 66 (.run (.close 43))))) (.step 67 (.run (.close 2)))) (.step 74 (.run (.close 27)))) (.step 68 (.run (.close 66)))) (.step 3 (.run (.close 2)))) (.step 68 (.step 66 (.run (.close 31))))) (.step 67 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 66 (.step 18 (.run (.close 2))))) (.step 3 (.run (.close 2))))) (.step 66 (.step 3 (.run (.close 2)))))) (.step 66 (.step 3 (.run (.close 2))))) (.step 66 (.step 3 (.run (.close 2))))) (.step 66 (.step 3 (.run (.close 2))))))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 8 (.step 2 (.run (.close 60))))) (.step 50 (.run (.close 2)))) (.step 3 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part732.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part733
namespace Part734
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569345729236737373938739666191448619833675595181730521106834481094394206192076443691579719769923261563905⟩
def references : Fin 1 → Box := ![Part733.root]
def proof : Chunks.Proof 1 := (.split 41 1 (.split 43 1 (.split 44 1 (.split 47 1 (.split 48 1 (.split 51 1 (.reuse 0) (.step 68 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 18 (.step 31 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 50 (.step 3 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 50 (.run (.close 2)))) (.step 50 (.run (.close 2)))) (.step 3 (.run (.close 2))))))))) (.step 29 (.step 11 (.step 3 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))) (.step 68 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 43 (.step 18 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part733.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part734
namespace Part735
def root : Box := ⟨4074071952668972172536891376818756322102936787331872501272280898708762599526673414514278400, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489548083779723498085161196186937730874573233144285930424116562542676747046904434511234833843201⟩
def references : Fin 1 → Box := ![Part734.root]
def proof : Chunks.Proof 1 := (.split 18 1 (.split 19 1 (.split 23 1 (.split 29 1 (.split 31 1 (.split 33 1 (.reuse 0) (.step 43 (.step 18 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 43 (.step 18 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 18 (.step 31 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 31 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 31 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 31 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part734.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part735
namespace Part736
def root : Box := ⟨2147483648, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489548083779723498085161196186937730874573233144285930424116562542677984986943719891509732967425⟩
def references : Fin 5 → Box := ![Part698.root, Part699.root, Part700.root, Part719.root, Part735.root]
def proof : Chunks.Proof 5 := (.split 30 1 (.split 43 1 (.split 21 1 (.split 55 1 (.reuse 0) (.step 2 (.split 34 1 (.split 36 1 (.split 42 1 (.split 14 1 (.split 51 1 (.split 67 1 (.split 74 1 (.reuse 1) (.step 74 (.step 40 (.step 66 (.step 67 (.step 18 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 60))) (.step 60 (.step 2 (.run (.close 74))))) (.step 5 (.run (.close 2)))))))))) (.step 55 (.step 3 (.step 2 (.run (.close 9)))))) (.step 55 (.step 3 (.step 2 (.step 7 (.run (.close 2))))))) (.step 74 (.step 49 (.step 48 (.step 40 (.step 67 (.step 18 (.split 34 0 (.split 36 0 (.step 2 (.step 34 (.step 2 (.run (.close 60))))) (.step 74 (.step 2 (.step 60 (.step 2 (.run (.close 5))))))) (.step 49 (.run (.close 2))))))))))) (.step 18 (.step 31 (.run (.close 2))))) (.step 18 (.step 31 (.step 2 (.run (.close 75)))))) (.step 18 (.step 31 (.step 2 (.run (.close 37)))))))) (.step 2 (.step 18 (.split 14 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 34 1 (.split 36 1 (.reuse 2) (.step 18 (.step 31 (.step 2 (.run (.close 26)))))) (.step 18 (.step 31 (.step 2 (.run (.close 26)))))) (.step 23 (.run (.close 2)))) (.step 68 (.step 3 (.step 2 (.run (.close 7)))))) (.step 68 (.step 3 (.step 2 (.step 7 (.run (.close 2))))))) (.step 23 (.run (.close 2))))))) (.reuse 3)) (.split 9 1 (.reuse 4) (.step 18 (.step 31 (.step 32 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 32 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part698.covered
  · exact Part699.covered
  · exact Part700.covered
  · exact Part719.covered
  · exact Part735.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part736
namespace Part737
def root : Box := ⟨2535301200456458802995553894400, 5391644440959909378249593757145204012680001210231139269336764184272221946867373518249972110120823620795609996013390641517699695160887278157468327548612485391637055771765863837250326949294000509908058102804878721025⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 16 0 (.split 17 0 (.split 46 0 (.split 49 0 (.split 50 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 18 0 (.split 19 0 (.step 18 (.run (.close 2))) (.step 12 (.run (.close 2)))) (.step 12 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.split 18 0 (.split 19 0 (.step 18 (.run (.close 7))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.split 18 0 (.split 19 0 (.step 18 (.run (.close 7))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 18 (.split 22 0 (.step 2 (.run (.close 9))) (.step 18 (.run (.close 27)))))) (.step 18 (.split 22 0 (.step 2 (.run (.close 9))) (.step 18 (.run (.close 7)))))) (.step 18 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 2)))))) (.split 18 0 (.split 19 0 (.split 29 0 (.split 31 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 18 (.run (.close 43)))) (.step 18 (.run (.close 43)))) (.step 18 (.split 22 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))))) (.step 18 (.split 22 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2))))))) (.split 18 0 (.split 19 0 (.split 29 0 (.split 31 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 18 (.run (.close 43)))) (.step 18 (.run (.close 43)))) (.step 18 (.split 17 0 (.split 22 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))))) (.step 18 (.split 17 0 (.split 22 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part737
namespace Part738
def root : Box := ⟨2535301200456458802995553894400, 5789228620743490309705582504769080877015479531975735135832113227605286536512678871674415056290193603911164245067092188998543400092750396603521711988866567066795617379176623818939759585860369181128941036878954271429046042625⟩
def references : Fin 1 → Box := ![Part737.root]
def proof : Chunks.Proof 1 := (.split 73 0 (.split 74 0 (.split 4 0 (.split 9 0 (.reuse 0) (.split 16 0 (.split 17 0 (.split 30 0 (.split 34 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 18 (.run (.close 2))) (.step 12 (.run (.close 2)))) (.step 12 (.run (.close 2)))) (.step 12 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.split 22 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))))) (.step 18 (.split 17 0 (.split 22 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 29 0 (.split 31 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 18 (.run (.close 7)))) (.step 18 (.run (.close 7)))) (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))) (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))) (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 7))))))) (.step 31 (.split 4 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 7)))))) (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part737.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part738
namespace Part739
def root : Box := ⟨2535301200456458802995553894400, 5789234136395753411692881233497288307929283439123939273127918849702731564155715679313075834951490936749411306984616993428105736468740565865987039291794932175041907533892980581583481381719406425438755917970837356491077320705⟩
def references : Fin 1 → Box := ![Part738.root]
def proof : Chunks.Proof 1 := (.split 40 0 (.split 45 0 (.split 53 0 (.split 54 0 (.split 56 0 (.split 58 0 (.split 60 0 (.split 72 0 (.reuse 0) (.step 18 (.split 4 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 43)))))) (.step 31 (.split 4 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7)))))) (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))) (.step 3 (.step 18 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 30)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))) (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))) (.step 3 (.step 31 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 30)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))) (.step 18 (.step 31 (.split 4 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7))))))) (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part738.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part739
namespace Part740
def root : Box := ⟨2535301200456458802995553894400, 5789234136395753411692881233497288307929283439123939273127918849702731564155715679313075834951490936749413831180448767452449701671523185110203864279356055382546235624651750419756309314602164009790121355286571616709903384577⟩
def references : Fin 1 → Box := ![Part739.root]
def proof : Chunks.Proof 1 := (.split 27 0 (.split 32 0 (.split 35 0 (.split 37 0 (.split 38 0 (.split 39 0 (.reuse 0) (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))) (.step 3 (.step 18 (.split 40 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 43 (.run (.close 2))))))) (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 3 (.run (.close 2))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))) (.step 18 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 43)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 3 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.step 3 (.run (.close 7))) (.step 30 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part739.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part740
namespace Part741
def root : Box := ⟨2535301200456458802995553894400, 5789234136395753411692881233497288307929283439123939273127918849702731564155715679313075834951490936749413831180448767452449701671523185110203866133840501421006497348725032909108637777806779263510567236396221299894204235777⟩
def references : Fin 1 → Box := ![Part740.root]
def proof : Chunks.Proof 1 := (.split 14 0 (.split 21 0 (.split 24 0 (.split 25 0 (.split 26 0 (.reuse 0) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 3 (.run (.close 2))) (.step 29 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 18 (.split 40 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 43 (.run (.close 2))))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.step 3 (.run (.close 7))) (.step 27 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 27)))) (.step 15 (.step 66 (.run (.close 31))))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part740.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part741
namespace Part742
def root : Box := ⟨2535301200456458802995553894400, 5789234136395753411692881233497288307929283439123939273127918849702731564155715679313075834951490936749413831180448767452449701671523185110203866133840501421006497348725032909108637779169239257264321848755350283934814437377⟩
def references : Fin 1 → Box := ![Part741.root]
def proof : Chunks.Proof 1 := (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.reuse 0) (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))) (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 31 (.split 21 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 29 0 (.step 11 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 11 (.run (.close 9)))) (.step 9 (.run (.close 11)))) (.step 9 (.run (.close 11)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part741.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part742
namespace Part743
def root : Box := ⟨2535301200456458802995553894400, 5789234136395753411692881233497288307929283439123939273127918849702731564155715679313075834951490936749413831180448767452449701671523185110203866133840501421006497348725032909108637779169239257264321849937095952056739430401⟩
def references : Fin 1 → Box := ![Part742.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.split 6 0 (.split 7 0 (.reuse 0) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 21 0 (.split 4 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 8)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 30))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10))))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part742.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part743
namespace Part744
def root : Box := ⟨2535301200456458802995553894400, 5789239652048016513680179966897434931288206951125608086251332488484335124018683053430257992857271872196127739586228725097647944851505959627399446798239707952320351759116556942812303449861754237073885926025475451079598539777⟩
def references : Fin 1 → Box := ![Part743.root]
def proof : Chunks.Proof 1 := (.split 38 1 (.split 56 1 (.split 72 1 (.split 1 0 (.split 65 0 (.reuse 0) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.step 3 (.run (.close 7))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 68))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 43)))))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.step 31 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 66 (.step 7 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 66 (.step 7 (.run (.close 2))))) (.step 66 (.step 7 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 10))))) (.step 43 (.run (.close 2)))) (.step 49 (.step 43 (.run (.close 2)))))))) (.step 2 (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 10))))) (.step 43 (.run (.close 2)))) (.step 49 (.step 43 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part743.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part744
namespace Part745
def root : Box := ⟨2535301200456458802995553894400, 5789239652048016513680179966897434931288206955177869383986680773662644062961688863396656165317013753105831492145563344141022762030105923415922648296926459696811680130688008998966327440032849086837521310439727484954372736001⟩
def references : Fin 1 → Box := ![Part744.root]
def proof : Chunks.Proof 1 := (.split 54 1 (.split 59 1 (.split 25 1 (.split 26 1 (.split 35 1 (.reuse 0) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.split 30 0 (.step 31 (.run (.close 38))) (.step 7 (.run (.close 3)))))) (.step 3 (.run (.close 31)))) (.step 43 (.step 66 (.step 29 (.run (.close 38)))))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 31)))) (.step 7 (.run (.close 3))))))) (.step 29 (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 29)))) (.step 43 (.run (.close 29)))) (.step 43 (.run (.close 29)))) (.step 43 (.step 29 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 2 (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 10))))) (.step 43 (.run (.close 2)))) (.step 49 (.step 43 (.run (.close 2))))))))) (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 9))) (.step 27 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 27)))))))) (.step 2 (.step 31 (.split 35 1 (.step 3 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 9 (.step 15 (.step 57 (.run (.close 2))))) (.step 2 (.run (.close 57)))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 18 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part744.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part745
namespace Part746
def root : Box := ⟨2535301200456458802995553894400, 11572820244868825110617489347147286435501031520173448112629217960195680675557195725100238587372829016878080046959121575284810558432848134796983840582665162531199568842302917804021290714402815517070525737005969986771959677953⟩
def references : Fin 1 → Box := ![Part745.root]
def proof : Chunks.Proof 1 := (.split 14 1 (.split 71 1 (.split 74 1 (.split 50 1 (.reuse 0) (.step 2 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 9))) (.step 27 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 27))))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 11 (.step 17 (.step 77 (.run (.close 43))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 29 (.step 31 (.split 35 1 (.step 18 (.split 74 1 (.split 4 0 (.split 9 0 (.split 16 0 (.split 72 1 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 66 (.step 74 (.step 3 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 68 (.step 74 (.run (.close 31))))) (.step 68 (.run (.close 74)))) (.step 68 (.step 66 (.step 67 (.run (.close 74)))))) (.step 74 (.step 66 (.run (.close 75))))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 12)))) (.step 3 (.run (.close 2)))) (.step 66 (.step 3 (.run (.close 2)))))) (.step 74 (.step 3 (.run (.close 2)))))))) (.step 3 (.split 71 1 (.step 31 (.step 17 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 11 (.run (.close 17))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2)))))) (.step 74 (.run (.close 17))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part745.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part746
namespace Part747
def root : Box := ⟨2535301200456458802995553894400, 11572820244868825110617489347147286435501031520177405399052787632740648715893510080140800688958451114001955742443268155720869130229546633031425465438713600666616928048502022593007606739272502450842669303822306198325539374081⟩
def references : Fin 1 → Box := ![Part746.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 39 1 (.split 42 1 (.split 58 1 (.split 8 1 (.reuse 0) (.step 11 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 11 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 2 (.step 18 (.split 14 1 (.step 3 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 27 (.step 31 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 61 (.run (.close 17))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 2 (.step 43 (.step 18 (.split 14 1 (.step 3 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 27 (.step 31 (.run (.close 2)))) (.step 3 (.run (.close 42)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 43 (.run (.close 42)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 42 (.run (.close 17)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part746.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part747
namespace Part748
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545611387564831695691227734228001108554102154436602374103554232477140612436800441573995897538174264723716265121565456194023878160825460785685701210188946137342855350730011325288854428443479143894259002770433⟩
def references : Fin 1 → Box := ![Part747.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 73 1 (.split 24 1 (.split 34 1 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 2 (.step 43 (.step 18 (.split 14 1 (.step 3 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 16 0 (.step 27 (.run (.close 43))) (.step 11 (.step 42 (.run (.close 31))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 27 (.run (.close 2)))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 24 (.step 10 (.run (.close 18))))) (.step 24 (.step 10 (.run (.close 18))))) (.step 24 (.step 10 (.run (.close 18)))))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part747.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part748
namespace Part749
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616286448142353033664682078402510193706676668384995969515465892691228757166758124241511949983073605925948874155181317945020138649964512760286252910324430120291163107507069861454592468673636068264621638657⟩
def references : Fin 1 → Box := ![Part748.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 6 1 (.split 7 1 (.split 12 1 (.split 13 1 (.reuse 0) (.step 16 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 24 (.step 10 (.run (.close 16))))) (.step 24 (.step 10 (.run (.close 16))))) (.step 24 (.step 10 (.run (.close 16)))))))))) (.step 15 (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 9 (.run (.close 15))) (.step 2 (.run (.close 7)))) (.step 24 (.run (.close 15)))) (.step 24 (.run (.close 15)))) (.step 24 (.run (.close 15)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 2 (.run (.close 7))))))))) (.step 2 (.step 18 (.step 31 (.split 35 1 (.step 3 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 9 (.run (.close 2)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part748.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part749
namespace Part750
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616291232212652993601693502181331052907722459900956076084047261538333103605038097860723994652873269860921231525530496220069998155860795194033138774483626304344581066431338475865355678750596963919312454657⟩
def references : Fin 1 → Box := ![Part749.root]
def proof : Chunks.Proof 1 := (.split 57 1 (.split 63 1 (.split 64 1 (.split 66 1 (.reuse 0) (.step 18 (.step 31 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 29 (.step 11 (.step 3 (.step 12 (.split 14 1 (.split 35 1 (.split 72 1 (.step 18 (.split 74 1 (.step 31 (.split 4 0 (.split 9 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 66 (.step 74 (.step 3 (.run (.close 67))))) (.step 67 (.step 18 (.run (.close 2))))) (.step 68 (.step 66 (.run (.close 67))))) (.step 68 (.step 66 (.step 67 (.run (.close 2)))))) (.step 68 (.run (.close 67)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 12)))) (.step 3 (.run (.close 2))))) (.step 67 (.step 3 (.run (.close 2)))))) (.step 67 (.step 3 (.run (.close 2))))) (.step 67 (.step 3 (.run (.close 2))))) (.step 67 (.step 3 (.run (.close 2)))))))))) (.step 66 (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 66 (.run (.close 27))) (.step 18 (.run (.close 2)))) (.step 68 (.run (.close 66)))) (.step 68 (.run (.close 66)))) (.step 68 (.run (.close 66)))) (.step 66 (.run (.close 3)))) (.step 18 (.run (.close 2)))) (.step 3 (.run (.close 2))))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 30))))) (.step 49 (.step 8 (.step 2 (.run (.close 60)))))) (.step 3 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part749.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part750
namespace Part751
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569345729236735336902763331705362351387987185803569469638440815158143570052894739910508185834713781371905⟩
def references : Fin 1 → Box := ![Part750.root]
def proof : Chunks.Proof 1 := (.split 41 1 (.split 43 1 (.split 44 1 (.split 47 1 (.split 48 1 (.split 51 1 (.reuse 0) (.step 68 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 18 (.step 31 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 30))))) (.step 49 (.step 8 (.step 2 (.run (.close 7)))))) (.step 3 (.run (.close 2))))))))) (.step 29 (.step 11 (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))) (.step 68 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 43 (.step 18 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part750.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part751
namespace Part752
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489548083779723498085161196186937730874571700648745064535258204196917247337949045173609353446401⟩
def references : Fin 1 → Box := ![Part751.root]
def proof : Chunks.Proof 1 := (.split 19 1 (.split 23 1 (.split 29 1 (.split 30 1 (.split 31 1 (.split 33 1 (.reuse 0) (.step 43 (.step 18 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 43 (.step 18 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 3 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 18 (.step 31 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 31 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 31 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 2 (.run (.close 7))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part751.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part752
namespace Part753
def root : Box := ⟨2201170739200, 5789234136395753411692881233497288307929279289608370392131274827114378086514569603202843621361258141395628530631882014002365884193657022752970845265081463770168656069959876136650216726027242616856760734798989897725956326401⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 39 0 (.split 53 0 (.split 54 0 (.split 58 0 (.split 72 0 (.split 73 0 (.split 74 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 9))) (.split 18 0 (.split 19 0 (.step 18 (.run (.close 7))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 18 0 (.split 19 0 (.step 18 (.run (.close 7))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 27)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 27)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 43)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part753
namespace Part754
def root : Box := ⟨2201170739200, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690118620302562339272198042129954515787237396512733837201863022767011442876037972433414373382720739361756817057109593101884275557377⟩
def references : Fin 1 → Box := ![Part753.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 65 0 (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 24 0 (.split 26 0 (.split 35 0 (.reuse 0) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 3 (.run (.close 2))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.step 18 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 31 0 (.split 33 0 (.step 3 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 43 (.run (.close 3)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 43 (.step 68 (.run (.close 2))))) (.step 43 (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 68)))) (.step 2 (.run (.close 7))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part753.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part754
namespace Part755
def root : Box := ⟨2201170739200, 5789234141782132574878415709584001140443658947020478074459303175931283722679476698116147521534513153450812913328630950783503529300774988828076283975301725054514519350194394783727288668372127605333263224573540581036186928129⟩
def references : Fin 1 → Box := ![Part754.root]
def proof : Chunks.Proof 1 := (.split 71 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 3 (.step 18 (.step 31 (.split 9 0 (.split 10 0 (.split 18 0 (.split 23 0 (.split 29 0 (.split 30 0 (.split 31 0 (.step 74 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part754.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part755
namespace Part756
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480632814827470848, 5789234141782132574883314592899225379006644639315539089938671890729545783191422783519150240661422239874541479747956005484984455410786351389172299170404530178259141977772110391097393299918458691766797923756209165531509425153⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 3 (.split 0 0 (.split 10 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 28 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 61 0 (.split 62 0 (.split 65 0 (.split 24 0 (.split 27 0 (.split 32 0 (.split 38 0 (.split 39 0 (.split 56 0 (.split 58 0 (.split 70 0 (.split 7 0 (.split 9 0 (.split 13 0 (.split 18 0 (.split 31 0 (.step 74 (.step 2 (.step 31 (.step 66 (.run (.close 2)))))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 66)))) (.step 66 (.step 68 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 74 (.step 2 (.run (.close 66)))))) (.step 68 (.step 74 (.step 2 (.run (.close 66)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part756
namespace Part757
def root : Box := ⟨2201170739200, 5789234141782132574883314592899225379006644639315539089938671890729549135143405269168425134170444461030194164448989567767471970004583718905555634132319210227448305011434658522101914327535311708334892121360099345772735104001⟩
def references : Fin 2 → Box := ![Part755.root, Part756.root]
def proof : Chunks.Proof 2 := (.split 43 1 (.split 51 1 (.split 63 1 (.split 64 1 (.split 67 1 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 3 (.step 18 (.step 31 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 74 (.split 31 0 (.split 34 0 (.split 36 0 (.step 67 (.step 3 (.run (.close 2)))) (.step 29 (.run (.close 3)))) (.step 66 (.run (.close 3)))) (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 67)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 3)))))))) (.reuse 1)) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part755.covered
  · exact Part756.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part757
namespace Part758
def root : Box := ⟨2201170739200, 5789239657434395676870613321627432809920440247428648175051024787998945351342292693384245262830446404838781998233883121396901402641721458721085183503603920420768317680525449905264342644130840524580632158142008524703297176577⟩
def references : Fin 1 → Box := ![Part757.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 35 1 (.split 72 1 (.reuse 0) (.step 7 (.step 3 (.split 63 1 (.split 64 1 (.step 18 (.split 71 1 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.step 31 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 66 (.step 3 (.run (.close 2)))))))) (.step 7 (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.step 18 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.split 30 0 (.step 31 (.run (.close 38))) (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 67 (.step 3 (.run (.close 2))))) (.step 66 (.step 3 (.run (.close 2)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part757.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part758
namespace Part759
def root : Box := ⟨2201170739200, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489548083779723498085161196186937730874573233144285930424116562543945635587171949294105947800577⟩
def references : Fin 1 → Box := ![Part758.root]
def proof : Chunks.Proof 1 := (.step 2 (.split 10 1 (.split 14 1 (.split 74 1 (.reuse 0) (.step 7 (.step 3 (.split 63 1 (.split 64 1 (.step 31 (.split 71 1 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 11 (.step 77 (.split 16 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 66 (.step 3 (.run (.close 2)))))))) (.step 7 (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.step 31 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 11 (.step 77 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 18 (.run (.close 17))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 67 (.step 3 (.run (.close 2))))) (.step 66 (.step 3 (.run (.close 2)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part758.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part759
namespace Part760
def root : Box := ⟨9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345723192016896, 5794882169699549009867419832699992206115557285681947642271816261350181799576917208063336230275286724234142555945993887374820224271451719544979123681192862114294141354486265717907085524825011715786681234299229195321178326017⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 2 (.step 74 (.step 2 (.run (.close 55))))) (.step 3 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))) (.step 3 (.split 63 1 (.step 2 (.step 74 (.run (.close 2)))) (.step 74 (.step 2 (.run (.close 66))))))) (.step 3 (.split 23 1 (.split 63 1 (.step 21 (.step 32 (.split 64 1 (.step 2 (.step 22 (.step 71 (.step 31 (.run (.close 2)))))) (.step 67 (.run (.close 2)))))) (.step 66 (.run (.close 2)))) (.step 21 (.step 2 (.step 57 (.step 2 (.run (.close 74))))))))) (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.split 35 0 (.step 2 (.run (.close 57))) (.step 43 (.step 63 (.step 31 (.run (.close 2)))))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 66 (.run (.close 2)))))) (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.split 34 0 (.step 2 (.run (.close 57))) (.step 43 (.step 63 (.step 31 (.run (.close 2)))))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 66 (.run (.close 2)))))) (.step 3 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))) (.step 3 (.step 69 (.step 2 (.step 74 (.step 2 (.run (.close 66)))))))) (.step 3 (.split 63 1 (.split 64 1 (.step 2 (.step 18 (.step 34 (.step 51 (.step 68 (.step 63 (.step 18 (.run (.close 2))))))))) (.step 74 (.step 2 (.run (.close 67))))) (.step 74 (.step 2 (.run (.close 66))))))) (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.step 2 (.run (.close 61))) (.step 24 (.step 71 (.step 18 (.run (.close 2)))))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 66 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part760
namespace Part761
def root : Box := ⟨9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345723192016896, 11578468272786241545611392353573934843609873555668489137540298544809000198268755061286277363008858473240398836509612079735087021931997304650056691667430554845945378864752372350635973551114866764607359030013268093366321546241⟩
def references : Fin 1 → Box := ![Part760.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 72 1 (.split 39 1 (.split 74 1 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.reuse 0) (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 74 (.step 66 (.step 67 (.step 3 (.step 44 (.step 69 (.split 9 1 (.split 29 1 (.split 31 1 (.step 63 (.step 18 (.run (.close 2)))) (.step 66 (.step 2 (.run (.close 61))))) (.step 2 (.step 63 (.step 42 (.step 2 (.run (.close 61))))))) (.step 66 (.step 2 (.run (.close 61)))))))))))) (.step 2 (.step 67 (.step 3 (.split 63 1 (.split 71 1 (.split 74 1 (.split 16 0 (.step 2 (.run (.close 61))) (.step 27 (.step 58 (.step 43 (.run (.close 42)))))) (.step 42 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 66 (.run (.close 2)))))))) (.step 74 (.step 66 (.step 67 (.step 3 (.step 26 (.step 69 (.split 9 1 (.split 18 1 (.split 19 1 (.step 71 (.step 31 (.run (.close 2)))) (.step 74 (.step 2 (.run (.close 15))))) (.step 67 (.step 2 (.run (.close 57))))) (.step 66 (.run (.close 2))))))))))) (.step 74 (.step 66 (.step 67 (.step 21 (.split 9 1 (.split 19 1 (.split 23 1 (.step 71 (.split 72 1 (.step 3 (.split 34 0 (.step 31 (.run (.close 2))) (.step 66 (.run (.close 31))))) (.step 29 (.step 3 (.step 69 (.step 31 (.step 2 (.run (.close 21))))))))) (.step 55 (.step 31 (.run (.close 26))))) (.step 74 (.step 55 (.step 31 (.run (.close 2)))))) (.step 66 (.step 3 (.step 31 (.run (.close 2)))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part760.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part761
namespace Part762
def root : Box := ⟨9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345723192016896, 11578468272786241545611392353573934843609873555668489137540298544809000198268755061286277363008858473240398836509612079735087021931997304650056693520105749490069284026217715787143243515748353034912990542148029673760562873345⟩
def references : Fin 1 → Box := ![Part761.root]
def proof : Chunks.Proof 1 := (.split 12 1 (.split 14 1 (.split 24 1 (.split 26 1 (.reuse 0) (.step 2 (.step 66 (.step 67 (.step 71 (.split 4 0 (.split 10 0 (.step 47 (.step 71 (.step 3 (.step 40 (.step 29 (.run (.close 2))))))) (.step 27 (.step 29 (.run (.close 2))))) (.step 2 (.run (.close 3))))))))) (.step 27 (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.step 2 (.run (.close 27))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2))))))) (.step 74 (.step 66 (.step 67 (.step 34 (.step 51 (.step 69 (.split 9 1 (.split 18 1 (.split 23 1 (.split 29 1 (.split 33 1 (.step 63 (.step 23 (.split 39 1 (.split 43 0 (.split 51 0 (.split 67 0 (.step 18 (.split 58 1 (.split 74 1 (.step 3 (.split 16 0 (.step 18 (.run (.close 2))) (.step 24 (.step 11 (.run (.close 18)))))) (.step 11 (.step 3 (.step 69 (.step 18 (.step 2 (.run (.close 34)))))))) (.step 27 (.run (.close 61))))) (.step 55 (.run (.close 7)))) (.step 55 (.run (.close 7)))) (.step 27 (.run (.close 2)))) (.step 42 (.run (.close 2)))))) (.step 74 (.step 55 (.step 18 (.run (.close 2)))))) (.step 67 (.step 3 (.step 18 (.run (.close 2)))))) (.step 40 (.step 24 (.step 2 (.run (.close 23)))))) (.step 40 (.step 67 (.step 24 (.run (.close 2)))))) (.step 66 (.step 3 (.step 18 (.run (.close 2))))))))))))) (.step 2 (.step 66 (.split 64 1 (.split 71 1 (.split 35 1 (.step 3 (.split 72 1 (.split 34 0 (.step 2 (.run (.close 57))) (.step 66 (.run (.close 2)))) (.step 66 (.step 2 (.run (.close 57)))))) (.step 63 (.step 29 (.step 55 (.run (.close 15)))))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part761.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part762
namespace Part763
def root : Box := ⟨9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345723192016896, 11578468272786241545611392353573934843609873555668489137540298544809000198268755061286277363008861180925647001367873386780188724162176441795638115215979939411534727992338619718415743490754314108719727484679456705569958659073⟩
def references : Fin 1 → Box := ![Part762.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 6 1 (.split 8 1 (.reuse 0) (.step 2 (.step 63 (.step 66 (.step 67 (.split 4 0 (.split 10 0 (.step 47 (.step 63 (.step 3 (.step 23 (.step 11 (.run (.close 2))))))) (.step 9 (.step 11 (.run (.close 2))))) (.step 2 (.run (.close 3))))))))) (.step 9 (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.split 35 0 (.step 2 (.run (.close 9))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2))))))) (.step 43 (.step 3 (.step 31 (.step 51 (.step 69 (.split 9 1 (.split 18 1 (.split 19 1 (.split 29 1 (.split 35 1 (.split 38 1 (.split 56 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 7 0 (.split 9 0 (.split 13 0 (.split 18 0 (.split 25 0 (.split 26 0 (.step 68 (.step 31 (.run (.close 57)))) (.step 48 (.run (.close 29)))) (.step 48 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 9 (.step 48 (.run (.close 67))))) (.step 9 (.step 48 (.run (.close 66))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 74 (.step 48 (.step 66 (.step 67 (.step 29 (.run (.close 31)))))))) (.step 31 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 31 (.run (.close 2))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part762.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part763
namespace Part764
def root : Box := ⟨9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345723192016896, 11578468272786241545611392353573934843609873555668489137540298544809000198268755061286277363008861180925647001367875735325011242737582135486792346833575759372205281809443976544287264800743220588343352129058718967544597709825⟩
def references : Fin 1 → Box := ![Part763.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.reuse 0) (.step 43 (.step 3 (.step 31 (.step 51 (.step 69 (.split 9 1 (.split 18 1 (.split 23 1 (.split 29 1 (.split 35 1 (.split 38 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 72 1 (.split 7 0 (.split 9 0 (.split 13 0 (.split 18 0 (.split 25 0 (.split 26 0 (.step 68 (.step 31 (.run (.close 57)))) (.step 48 (.run (.close 29)))) (.step 48 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 57 (.step 48 (.step 29 (.run (.close 31)))))) (.step 9 (.step 48 (.run (.close 67))))) (.step 9 (.step 48 (.run (.close 66))))) (.step 31 (.run (.close 39)))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 38)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))))))))) (.step 43 (.step 66 (.step 3 (.step 31 (.step 51 (.step 69 (.split 29 1 (.split 35 1 (.split 36 1 (.split 38 1 (.split 42 1 (.split 56 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 7 0 (.split 9 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 68 (.step 31 (.run (.close 57)))) (.step 48 (.run (.close 31)))) (.step 48 (.run (.close 29)))) (.step 48 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 66 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 48 (.step 66 (.step 29 (.run (.close 31)))))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 37)))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 37)))) (.step 48 (.step 31 (.run (.close 38))))) (.step 31 (.run (.close 2)))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part763.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part764
namespace Part765
def root : Box := ⟨9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345723192016896, 11578468272786241545611392353573934843609873555668489137540298544809000201545342339697942809066985633316554355881604345866164962679353280309582523898801754252163564251582065957385976775554927137081137629922301132770666087425⟩
def references : Fin 1 → Box := ![Part764.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 49 1 (.split 50 1 (.reuse 0) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 24 (.step 3 (.step 18 (.step 47 (.step 51 (.step 69 (.split 9 1 (.split 14 1 (.split 29 1 (.split 31 1 (.split 33 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.split 27 0 (.step 18 (.run (.close 61))) (.step 27 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 58 (.step 11 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 27 (.step 58 (.run (.close 67))))) (.step 27 (.step 58 (.run (.close 66))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 74 (.step 58 (.step 66 (.step 67 (.step 11 (.run (.close 18)))))))) (.step 18 (.run (.close 2))))))))))) (.step 74 (.step 24 (.step 3 (.step 18 (.step 51 (.step 69 (.split 9 1 (.split 14 1 (.split 22 1 (.step 47 (.split 29 1 (.split 31 1 (.split 41 1 (.split 63 1 (.split 64 1 (.split 74 1 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.split 27 0 (.step 18 (.run (.close 60))) (.step 27 (.run (.close 2))))) (.step 18 (.run (.close 2)))) (.step 58 (.step 11 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 61 (.step 58 (.step 11 (.run (.close 18)))))) (.step 27 (.step 58 (.run (.close 67))))) (.step 27 (.step 58 (.run (.close 66))))) (.step 68 (.run (.close 44)))) (.step 68 (.step 2 (.run (.close 18))))) (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 20)))) (.step 18 (.run (.close 17)))) (.step 18 (.run (.close 2)))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part764.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part765
namespace Part766
def root : Box := ⟨6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028293262540800, 5789239657434395676860815550334178932601416642737285171604882007746461322923400826928860647150449079737948714223951510738343565825350617525684390585040605583664371731476410873546649072268723273582145465972607454454718923777⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 1 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 28 0 (.split 5 0 (.split 11 0 (.split 13 0 (.split 25 0 (.split 32 0 (.split 34 0 (.split 35 1 (.split 72 1 (.split 36 0 (.split 42 0 (.step 2 (.step 74 (.step 2 (.run (.close 15))))) (.step 55 (.step 2 (.run (.close 74))))) (.step 3 (.step 51 (.step 55 (.step 2 (.run (.close 74))))))) (.step 74 (.step 40 (.step 66 (.step 2 (.run (.close 57))))))) (.step 74 (.step 40 (.step 66 (.step 67 (.step 2 (.run (.close 57)))))))) (.step 3 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 14 0 (.step 2 (.run (.close 57))) (.step 48 (.run (.close 55)))) (.step 40 (.step 2 (.run (.close 57))))) (.step 74 (.run (.close 2)))) (.step 74 (.step 40 (.step 66 (.step 2 (.run (.close 57))))))) (.step 9 (.step 48 (.step 40 (.run (.close 66)))))) (.step 74 (.step 40 (.step 66 (.step 67 (.step 2 (.run (.close 57)))))))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 9)))) (.step 2 (.step 74 (.step 40 (.step 66 (.run (.close 31))))))) (.step 40 (.step 3 (.step 69 (.step 2 (.step 74 (.step 2 (.run (.close 15))))))))) (.step 40 (.step 3 (.split 63 1 (.split 64 1 (.step 2 (.step 48 (.step 27 (.step 61 (.run (.close 2)))))) (.step 74 (.step 2 (.run (.close 15))))) (.step 74 (.step 2 (.run (.close 66)))))))) (.step 40 (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.split 17 0 (.step 2 (.run (.close 15))) (.step 23 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 42 (.run (.close 2)))) (.step 74 (.step 40 (.step 2 (.run (.close 66))))))))) (.step 2 (.run (.close 23))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part766
namespace Part767
def root : Box := ⟨6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028293262540800, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580374782999197367709641956906662272606491377218181905166084490405217963099481112027595777⟩
def references : Fin 1 → Box := ![Part766.root]
def proof : Chunks.Proof 1 := (.step 2 (.step 3 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 14 1 (.split 74 1 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 65 0 (.split 67 0 (.reuse 0) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 74 (.step 66 (.step 67 (.step 23 (.split 43 0 (.step 44 (.split 4 0 (.split 10 0 (.split 30 0 (.step 69 (.split 51 0 (.step 2 (.run (.close 61))) (.step 61 (.step 2 (.run (.close 7)))))) (.step 67 (.step 68 (.run (.close 2))))) (.step 66 (.step 68 (.step 2 (.run (.close 61)))))) (.step 2 (.run (.close 68))))) (.step 27 (.run (.close 2))))))))) (.step 74 (.step 66 (.step 67 (.step 23 (.split 43 0 (.split 4 0 (.step 34 (.split 51 0 (.split 74 1 (.split 10 0 (.split 30 0 (.split 65 0 (.step 2 (.run (.close 61))) (.step 68 (.step 2 (.run (.close 61))))) (.step 67 (.step 2 (.run (.close 61))))) (.step 55 (.run (.close 2)))) (.step 77 (.run (.close 2)))) (.step 61 (.step 68 (.step 2 (.run (.close 42))))))) (.step 2 (.run (.close 7)))) (.step 27 (.run (.close 2))))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 2 (.run (.close 26)))))) (.step 3 (.step 31 (.step 2 (.run (.close 26)))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.step 2 (.run (.close 44)))))) (.step 3 (.step 18 (.step 2 (.run (.close 44))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part766.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part767
namespace Part768
def root : Box := ⟨2147483648, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580374782999197367709641956906662272606491377218181905166084490405217963099481112027595777⟩
def references : Fin 5 → Box := ![Part736.root, Part752.root, Part759.root, Part765.root, Part767.root]
def proof : Chunks.Proof 5 := (.split 52 1 (.split 65 1 (.split 4 1 (.split 10 1 (.reuse 0) (.split 9 1 (.split 18 1 (.reuse 1) (.step 24 (.step 31 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 2 (.run (.close 7)))))))) (.step 18 (.step 31 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))) (.reuse 2)) (.step 3 (.split 16 1 (.reuse 3) (.step 67 (.step 24 (.step 3 (.step 18 (.step 51 (.step 69 (.split 14 1 (.split 17 1 (.split 22 1 (.step 47 (.split 29 1 (.split 33 1 (.split 41 1 (.split 63 1 (.split 71 1 (.split 74 1 (.split 5 0 (.split 8 0 (.split 9 0 (.split 11 0 (.step 68 (.split 27 0 (.split 31 0 (.split 32 0 (.step 18 (.run (.close 60))) (.step 58 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 27 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 58 (.step 11 (.run (.close 2))))) (.step 58 (.run (.close 2)))) (.step 58 (.step 42 (.step 11 (.run (.close 18)))))) (.step 74 (.run (.close 2)))) (.step 66 (.run (.close 2)))) (.step 68 (.run (.close 44)))) (.step 68 (.step 2 (.run (.close 18))))) (.step 67 (.run (.close 2))))) (.step 18 (.run (.close 19)))) (.step 18 (.run (.close 19)))) (.step 11 (.step 18 (.run (.close 17)))))))))))))) (.reuse 4))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part736.covered
  · exact Part752.covered
  · exact Part759.covered
  · exact Part765.covered
  · exact Part767.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part768
namespace Part769
def root : Box := ⟨3885337784451458141838923813647037813284813678104279042503624819477808570412564480000, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493334015740077731621369092677372993996795341293976517649877787916742837108650761892886850255193283530298954112610594085183683560448⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 15 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.split 2 0 (.step 31 (.split 16 0 (.split 17 0 (.step 2 (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 74))))) (.step 32 (.split 74 1 (.split 2 0 (.step 31 (.split 16 0 (.step 2 (.split 17 0 (.step 2 (.run (.close 74))) (.step 74 (.run (.close 2))))) (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 67 (.run (.close 2)))))) (.step 12 (.split 7 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 73 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 27 0 (.step 74 (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 66 (.run (.close 31)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 66 (.run (.close 31)))) (.step 66 (.step 3 (.run (.close 2))))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 3 (.run (.close 31)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 31 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))) (.step 31 (.step 2 (.run (.close 74))))) (.step 31 (.step 2 (.run (.close 66))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 2 (.step 7 (.step 66 (.run (.close 31))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part769
namespace Part770
def root : Box := ⟨3213876088517980551083924184682325205044405987565587818086400, 5789239657434395676860815555006118125046544546625844895841980324433694915515860890984462835079766154350999640355934576822634645333100535014493484356067872761532455841418277778974939460566988237538353911059317410271748686848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 34 0 (.split 36 0 (.split 42 0 (.split 45 0 (.split 46 0 (.split 47 0 (.split 35 1 (.split 72 1 (.split 61 0 (.split 62 0 (.split 65 0 (.step 2 (.step 74 (.step 2 (.run (.close 15))))) (.step 23 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 74 (.step 40 (.step 66 (.step 2 (.run (.close 15))))))) (.step 74 (.step 40 (.step 66 (.step 67 (.step 2 (.run (.close 15)))))))) (.step 2 (.step 74 (.step 4 (.step 66 (.run (.close 67))))))) (.step 2 (.step 74 (.step 4 (.step 66 (.run (.close 67))))))) (.step 2 (.run (.close 23)))) (.step 18 (.step 26 (.split 35 1 (.split 63 1 (.step 2 (.step 74 (.step 2 (.run (.close 15))))) (.step 74 (.step 2 (.run (.close 66))))) (.step 74 (.step 66 (.step 67 (.step 2 (.run (.close 15)))))))))) (.step 18 (.step 22 (.split 35 1 (.split 63 1 (.split 72 1 (.step 23 (.step 2 (.run (.close 57)))) (.step 57 (.step 67 (.step 2 (.run (.close 15)))))) (.step 63 (.step 40 (.run (.close 66))))) (.step 57 (.step 48 (.step 66 (.step 67 (.step 29 (.step 23 (.run (.close 2)))))))))))) (.step 18 (.split 35 1 (.split 72 1 (.split 36 0 (.split 38 0 (.split 42 0 (.split 63 1 (.step 2 (.step 74 (.step 2 (.run (.close 15))))) (.step 63 (.run (.close 66)))) (.step 66 (.step 23 (.step 2 (.run (.close 74)))))) (.step 2 (.run (.close 5)))) (.step 66 (.step 31 (.step 51 (.split 64 1 (.split 7 0 (.step 31 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 57 (.step 66 (.step 2 (.run (.close 67)))))))))) (.step 74 (.step 48 (.step 66 (.step 67 (.step 23 (.run (.close 2)))))))) (.step 74 (.step 48 (.step 66 (.step 67 (.step 29 (.step 23 (.step 2 (.run (.close 57))))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part770
namespace Part771
def root : Box := ⟨3213876088517980551083924184682325205044405987565587818086400, 11572820244868825110622388230462510674064013058900678945602631942405742315922027221191475053028674730949932661916105090798973693817455572545088710915355176164602591899593836022043348779359697046522726320784560108954689995777⟩
def references : Fin 1 → Box := ![Part770.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 67 1 (.split 14 1 (.split 74 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 0 0 (.split 28 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 25 0 (.split 32 0 (.reuse 0) (.step 2 (.run (.close 23)))) (.step 2 (.step 67 (.run (.close 29))))) (.step 40 (.step 18 (.split 65 0 (.split 35 0 (.step 2 (.step 74 (.step 2 (.run (.close 15))))) (.step 42 (.step 2 (.run (.close 23))))) (.step 40 (.run (.close 2))))))) (.step 18 (.step 22 (.split 65 0 (.split 61 0 (.step 23 (.run (.close 2))) (.step 2 (.run (.close 5)))) (.step 40 (.run (.close 2))))))) (.step 40 (.step 18 (.split 65 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 51 0 (.split 61 0 (.split 62 0 (.step 23 (.run (.close 2))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 27 (.step 2 (.run (.close 9))))) (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 27 (.run (.close 2))))))) (.step 2 (.step 40 (.step 66 (.step 67 (.step 23 (.run (.close 31)))))))) (.step 2 (.run (.close 23)))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 23 (.run (.close 2)))) (.step 23 (.run (.close 2)))) (.step 55 (.step 18 (.run (.close 2))))) (.step 55 (.step 23 (.step 18 (.run (.close 2)))))) (.step 27 (.step 55 (.step 18 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part770.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
def root : Box := ⟨3213876088517980551083924184682325205044405987565587818086400, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580376725668089593438712876370176034169657009900562919397946904820149904997549110071395329⟩
def references : Fin 1 → Box := ![Part771.root]
def proof : Chunks.Proof 1 := (.step 2 (.split 65 1 (.split 34 1 (.split 36 1 (.split 42 1 (.reuse 0) (.step 40 (.step 23 (.step 18 (.step 31 (.step 26 (.split 35 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.step 2 (.run (.close 57))) (.step 48 (.run (.close 23)))) (.step 74 (.run (.close 2)))) (.step 9 (.step 48 (.run (.close 67))))) (.step 9 (.step 48 (.run (.close 66))))) (.step 48 (.run (.close 31)))))))))) (.step 40 (.step 23 (.step 18 (.step 31 (.step 22 (.split 35 1 (.split 42 1 (.split 64 1 (.split 72 1 (.split 7 0 (.split 13 0 (.split 14 0 (.split 25 0 (.step 31 (.run (.close 2))) (.step 2 (.run (.close 5)))) (.step 48 (.step 29 (.run (.close 23))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 9)))) (.step 48 (.run (.close 31)))) (.step 9 (.step 48 (.run (.close 67))))) (.step 31 (.run (.close 2)))) (.step 48 (.step 29 (.run (.close 31))))))))))) (.step 40 (.step 66 (.step 23 (.step 18 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 7 0 (.split 8 0 (.split 9 0 (.split 13 0 (.split 14 0 (.split 25 0 (.split 26 0 (.step 31 (.run (.close 2))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 76)))) (.step 49 (.run (.close 23)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 48 (.run (.close 31)))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 37)))) (.step 48 (.step 31 (.run (.close 26))))))))))) (.step 55 (.step 24 (.step 23 (.step 2 (.step 74 (.step 2 (.run (.close 23))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part771.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part772
namespace Part773
def root : Box := ⟨2854495385411919762116571938898990274912976896, 5789239657434395676865714438316775467483492397027246535446502556216320133429076792184354048955104925752266736865777021314805914652612099410847882917629234967484708097400378788042704295538194661169377037920536871819354833920⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 22 0 (.split 28 0 (.split 30 0 (.split 35 1 (.split 43 0 (.split 51 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 14 0 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.split 1 0 (.split 8 0 (.split 14 0 (.step 18 (.step 2 (.step 3 (.run (.close 2))))) (.step 74 (.run (.close 18)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74))))) (.step 32 (.step 18 (.split 7 0 (.split 8 0 (.split 9 0 (.split 13 0 (.step 74 (.step 18 (.step 2 (.run (.close 74))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 67)))) (.step 2 (.run (.close 67)))) (.step 2 (.run (.close 7))))))) (.step 12 (.split 27 0 (.split 32 0 (.split 61 0 (.split 62 0 (.split 67 0 (.split 69 0 (.split 70 0 (.split 1 0 (.split 7 0 (.split 8 0 (.split 31 0 (.step 74 (.step 67 (.step 18 (.step 2 (.step 3 (.run (.close 2))))))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 66)))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 31 (.step 32 (.step 2 (.step 74 (.step 2 (.run (.close 66)))))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 2 (.run (.close 3)))) (.step 18 (.split 35 1 (.step 2 (.step 74 (.step 2 (.run (.close 66))))) (.step 74 (.step 66 (.step 2 (.run (.close 67))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part773
namespace Part774
def root : Box := ⟨2147483648, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580376725668089593438712876370176034169657011327810612103906785878435874447044246454141953⟩
def references : Fin 4 → Box := ![Part768.root, Part769.root, Part772.root, Part773.root]
def proof : Chunks.Proof 4 := (.split 15 1 (.split 20 1 (.split 28 1 (.reuse 0) (.step 2 (.step 3 (.step 18 (.step 31 (.split 35 1 (.split 65 1 (.split 72 1 (.split 0 0 (.split 4 0 (.split 10 0 (.split 14 1 (.reuse 1) (.step 18 (.step 12 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.step 74 (.step 2 (.run (.close 67))))) (.step 74 (.run (.close 31)))) (.step 67 (.run (.close 31)))) (.step 67 (.run (.close 31))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 2 (.step 7 (.step 74 (.step 66 (.run (.close 31))))))) (.step 2 (.step 7 (.step 74 (.step 66 (.run (.close 31))))))) (.step 31 (.step 29 (.step 31 (.step 74 (.step 67 (.run (.close 75)))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 31 (.step 29 (.step 75 (.step 66 (.step 31 (.step 74 (.step 67 (.run (.close 77))))))))))))))) (.reuse 2)) (.step 2 (.step 3 (.step 18 (.step 31 (.split 14 1 (.split 65 1 (.split 74 1 (.split 0 0 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.reuse 3) (.step 18 (.split 35 1 (.step 2 (.run (.close 74))) (.step 74 (.step 2 (.run (.close 32))))))) (.step 18 (.split 35 1 (.step 2 (.run (.close 67))) (.step 66 (.step 2 (.run (.close 67))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 2 (.step 7 (.step 74 (.step 66 (.run (.close 18))))))) (.step 2 (.step 7 (.step 74 (.step 66 (.run (.close 18))))))) (.step 18 (.step 11 (.step 18 (.step 74 (.step 66 (.run (.close 77)))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 11 (.step 77 (.step 67 (.step 18 (.step 74 (.step 66 (.run (.close 75)))))))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part768.covered
  · exact Part769.covered
  · exact Part772.covered
  · exact Part773.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part774
namespace Part775
def root : Box := ⟨2149580800, 11572814729216562008625291735112988558276321749984766581281234581571095663896707994575872496617995244338810635111526648182961982071093008607974759204578938998239114571390701074510456368973152012092853270283205436385318141952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 36 0 (.split 42 0 (.split 65 0 (.split 14 1 (.split 74 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.step 63 (.split 27 0 (.split 32 0 (.split 70 0 (.split 33 0 (.step 66 (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))))) (.step 3 (.step 2 (.run (.close 74))))) (.step 3 (.step 2 (.step 74 (.run (.close 2)))))) (.step 3 (.split 63 1 (.step 2 (.step 58 (.step 63 (.run (.close 67))))) (.step 74 (.step 2 (.step 49 (.step 2 (.run (.close 60))))))))) (.step 5 (.step 63 (.step 11 (.step 5 (.step 77 (.run (.close 2)))))))) (.step 5 (.step 63 (.step 11 (.step 5 (.step 17 (.run (.close 2)))))))) (.step 63 (.step 3 (.step 2 (.run (.close 60)))))) (.step 5 (.step 3 (.split 12 0 (.split 7 0 (.split 13 0 (.split 18 0 (.split 63 1 (.step 2 (.step 58 (.step 74 (.step 2 (.run (.close 5)))))) (.step 74 (.step 2 (.step 50 (.step 2 (.run (.close 5))))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 23))))))) (.step 5 (.step 3 (.split 6 0 (.split 12 0 (.split 42 0 (.split 7 0 (.split 13 0 (.split 18 0 (.split 63 1 (.step 2 (.step 58 (.run (.close 74)))) (.step 74 (.step 2 (.step 74 (.step 2 (.run (.close 5))))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 43 (.split 63 1 (.split 64 1 (.step 2 (.step 57 (.step 60 (.run (.close 2))))) (.step 60 (.step 2 (.run (.close 74))))) (.step 60 (.step 2 (.run (.close 74))))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 11)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part775
namespace Part776
def root : Box := ⟨2149580800, 11572820244868825110617489347151853331627065208499277305998109710623117098008811319991583839153335959548665565406262644013303810643859532460766168340763559796889989324475859163424367803359735505790316234545903975195977188353⟩
def references : Fin 1 → Box := ![Part775.root]
def proof : Chunks.Proof 1 := (.split 72 1 (.split 0 0 (.split 1 0 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 34 0 (.reuse 0) (.step 5 (.step 3 (.split 12 0 (.split 36 0 (.split 42 0 (.split 7 0 (.split 13 0 (.split 18 0 (.split 63 1 (.step 2 (.step 58 (.step 74 (.step 2 (.run (.close 5)))))) (.step 74 (.step 2 (.step 50 (.step 2 (.run (.close 5))))))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 43 (.split 63 1 (.split 64 1 (.step 2 (.step 48 (.step 60 (.run (.close 2))))) (.step 60 (.step 2 (.run (.close 74))))) (.step 60 (.step 74 (.step 2 (.run (.close 50)))))))) (.step 43 (.step 28 (.split 63 1 (.split 64 1 (.split 7 0 (.split 9 0 (.split 13 0 (.step 31 (.run (.close 5))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 49)))) (.step 2 (.run (.close 5)))) (.step 74 (.step 50 (.step 2 (.run (.close 60)))))) (.step 74 (.step 49 (.step 2 (.run (.close 66))))))))) (.step 2 (.run (.close 23))))))) (.step 63 (.step 3 (.run (.close 2))))) (.step 63 (.step 3 (.run (.close 2))))) (.step 63 (.step 3 (.run (.close 2))))) (.step 5 (.step 3 (.step 2 (.run (.close 74)))))) (.step 5 (.step 3 (.step 2 (.run (.close 74)))))) (.step 2 (.run (.close 5)))) (.step 2 (.step 5 (.run (.close 3))))) (.step 4 (.step 5 (.split 63 1 (.split 64 1 (.split 71 1 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 5))) (.step 5 (.run (.close 2)))) (.step 5 (.step 2 (.run (.close 60))))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 66 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part775.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part776
namespace Part777
def root : Box := ⟨2149580800, 11572820244868825110617489347151853331627065208499277305998109710623117098008811319991583839153338667233913730264526301894486902697338070697765274675752066197469330778748594123257239374313687276525323737167296349700309910529⟩
def references : Fin 1 → Box := ![Part776.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 35 1 (.reuse 0) (.step 4 (.step 5 (.split 72 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 5))) (.step 5 (.run (.close 2)))) (.step 5 (.run (.close 38)))) (.step 74 (.run (.close 2)))) (.step 74 (.step 50 (.step 2 (.run (.close 5)))))) (.step 66 (.run (.close 2)))) (.step 75 (.run (.close 2))))))) (.step 5 (.step 43 (.step 28 (.step 3 (.split 35 1 (.split 63 1 (.split 71 1 (.split 7 0 (.split 9 0 (.split 13 0 (.step 31 (.step 60 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 5)))) (.step 74 (.run (.close 2)))) (.step 60 (.step 74 (.step 49 (.step 2 (.run (.close 66))))))) (.step 5 (.run (.close 38))))))))) (.step 5 (.step 43 (.step 28 (.step 31 (.split 35 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 7 0 (.split 9 0 (.split 13 0 (.step 31 (.run (.close 5))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 5)))) (.step 5 (.run (.close 75)))) (.step 57 (.run (.close 74)))) (.step 74 (.step 50 (.step 5 (.run (.close 31)))))) (.step 48 (.step 5 (.run (.close 66))))) (.step 31 (.run (.close 39)))) (.step 5 (.run (.close 38)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part776.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part777
namespace Part778
def root : Box := ⟨2147483648, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580376725668089593438712876370176034169657011327810612103906785878435874447044246455190530⟩
def references : Fin 2 → Box := ![Part774.root, Part777.root]
def proof : Chunks.Proof 2 := (.split 0 1 (.split 2 1 (.reuse 0) (.step 2 (.step 3 (.split 65 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.reuse 1) (.step 5 (.step 43 (.step 28 (.step 3 (.split 35 1 (.split 36 1 (.split 42 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 7 0 (.split 9 0 (.split 13 0 (.step 31 (.run (.close 5))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 49)))) (.step 2 (.run (.close 5)))) (.step 5 (.run (.close 75)))) (.step 74 (.run (.close 2)))) (.step 74 (.step 50 (.step 5 (.step 2 (.step 60 (.run (.close 31)))))))) (.step 48 (.run (.close 66)))) (.step 31 (.run (.close 37)))) (.step 31 (.run (.close 37)))) (.step 5 (.run (.close 38))))))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.step 2 (.run (.close 77)))))) (.step 3 (.step 18 (.step 2 (.run (.close 19)))))) (.step 63 (.run (.close 2))))))) (.step 2 (.step 18 (.step 31 (.split 14 1 (.split 74 1 (.split 35 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.step 12 (.step 2 (.run (.close 74))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.step 31 (.step 2 (.run (.close 74)))))) (.step 3 (.step 31 (.step 2 (.run (.close 38)))))) (.step 3 (.step 18 (.step 2 (.run (.close 74)))))) (.step 3 (.step 18 (.step 2 (.run (.close 17))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part774.covered
  · exact Part777.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part778
namespace Part779
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548544347594002730665403589693622580067872086838310766244227039375174681190433106257994791007996408636435408337168598994737691722326109792929617614207947544551332695789279532172468735935617482365224036074497⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 28 0 (.split 30 0 (.split 8 0 (.split 14 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 39 0 (.split 58 0 (.split 65 0 (.step 2 (.run (.close 30))) (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2))))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 73)))) (.split 74 0 (.split 65 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 63 (.run (.close 2))))) (.split 37 0 (.split 2 0 (.split 74 0 (.split 56 0 (.split 9 0 (.step 68 (.split 27 0 (.step 22 (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57))))) (.split 74 0 (.split 65 0 (.split 51 0 (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.step 2 (.run (.close 9))))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))) (.split 35 0 (.split 72 0 (.split 43 0 (.split 51 0 (.split 67 0 (.step 2 (.run (.close 57))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 71 (.run (.close 3)))))) (.step 2 (.run (.close 74)))) (.split 14 0 (.split 34 0 (.split 39 0 (.split 58 0 (.split 65 0 (.split 74 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 74)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 68 (.step 2 (.run (.close 9))))) (.step 63 (.run (.close 2))))) (.step 2 (.run (.close 31))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part779
namespace Part780
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548544347594002730665403589693622580067872086838310766244227039375174681190433106257994791007996408636435408337168598994737691722326109792931302610874644461035077060859062847330144326163500080272967935722497⟩
def references : Fin 1 → Box := ![Part779.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.reuse 0) (.split 30 0 (.split 35 0 (.split 1 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 54 0 (.split 72 0 (.split 33 0 (.split 53 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30)))))) (.split 20 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 35 0 (.split 1 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 33 0 (.split 53 0 (.step 68 (.split 7 0 (.step 36 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 9))))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 61)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 74)))) (.step 18 (.step 31 (.step 30 (.step 24 (.run (.close 2))))))) (.step 2 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part779.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part780
namespace Part781
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548544347594002730665403589693622580067872086838310766244227039375174681190433106257994791007996408636435408337168598994737691722326109792931302610874644461036539989744086456209496719882414042190356465845249⟩
def references : Fin 1 → Box := ![Part780.root]
def proof : Chunks.Proof 1 := (.split 15 0 (.split 4 0 (.split 10 0 (.split 16 0 (.reuse 0) (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 1 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 54 0 (.split 72 0 (.split 33 0 (.split 53 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 18 (.step 31 (.step 30 (.step 24 (.run (.close 2))))))) (.step 18 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 7)))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 58 0 (.split 65 0 (.split 74 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 74)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 68 (.step 2 (.run (.close 9))))) (.step 18 (.step 31 (.step 2 (.run (.close 10)))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 18))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part780.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part781
namespace Part782
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789239657434400813722079682132875167394750651442857850791836799195330157102779979706807938393269592597043626039112521370534888237136172095068945346312214965949822125435667051721091966373110117860289938430970969588442858497⟩
def references : Fin 1 → Box := ![Part781.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 65 1 (.split 67 1 (.reuse 0) (.split 63 0 (.split 64 0 (.split 65 0 (.split 71 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 2 (.run (.close 30))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 76 (.run (.close 2))))) (.step 10 (.step 76 (.step 2 (.run (.close 57)))))) (.step 68 (.run (.close 2)))) (.step 73 (.step 68 (.run (.close 2))))) (.step 30 (.step 73 (.step 68 (.run (.close 2)))))) (.step 30 (.step 73 (.step 68 (.step 2 (.run (.close 61))))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 76 (.step 71 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 53 0 (.step 22 (.step 26 (.split 27 0 (.split 31 0 (.split 32 0 (.split 33 0 (.step 9 (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 74)))) (.step 57 (.run (.close 4)))) (.step 73 (.run (.close 74)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9))))))) (.step 74 (.step 63 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 74 (.run (.close 2)))) (.step 74 (.run (.close 2))))))))) (.step 74 (.step 63 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 74 (.run (.close 2)))) (.step 74 (.run (.close 2))))))))) (.step 74 (.step 63 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 74 (.run (.close 2)))) (.step 74 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part781.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part782
namespace Part783
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789239657434400813722079682132875167394750651442857850791836799195333509054762465356082831902291813752696310740146083653022402830933539611452280308226895015138985159098215182725612993989963134428384136034861149829668537345⟩
def references : Fin 1 → Box := ![Part782.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.reuse 0) (.step 57 (.split 48 0 (.split 63 0 (.split 64 0 (.split 65 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 2 (.run (.close 30))) (.step 10 (.step 2 (.run (.close 57))))) (.step 57 (.run (.close 2)))) (.step 10 (.step 57 (.run (.close 2))))) (.step 30 (.step 61 (.step 2 (.run (.close 7)))))) (.step 61 (.step 68 (.run (.close 2))))) (.step 30 (.step 61 (.step 68 (.run (.close 2)))))) (.step 57 (.step 61 (.run (.close 2))))) (.step 57 (.step 61 (.run (.close 2))))) (.step 72 (.run (.close 70)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))))) (.step 68 (.split 72 1 (.split 48 0 (.split 51 1 (.split 63 0 (.split 64 0 (.split 65 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.step 10 (.step 30 (.run (.close 2)))) (.step 30 (.run (.close 2)))) (.step 30 (.run (.close 9)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 10 (.run (.close 2))))) (.step 30 (.step 10 (.step 2 (.run (.close 7)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 10 (.step 72 (.step 46 (.run (.close 2))))))) (.step 2 (.run (.close 55)))) (.step 9 (.run (.close 10))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part782.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part783
namespace Part784
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 11572820244868830247473854590967953031538323462914888621343443953602130473634496993163312622100522847549095139280631710938517530802323995883012356335535101437674244722735941535247202865377896047691447278266067378144380191745⟩
def references : Fin 1 → Box := ![Part783.root]
def proof : Chunks.Proof 1 := (.split 74 1 (.split 35 1 (.reuse 0) (.step 57 (.step 74 (.step 71 (.split 43 1 (.split 67 1 (.split 72 1 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 53 0 (.step 21 (.step 22 (.split 27 0 (.split 31 0 (.split 32 0 (.split 33 0 (.step 9 (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 74)))) (.step 74 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 57 (.step 74 (.run (.close 2))))) (.step 10 (.step 57 (.step 76 (.step 4 (.step 2 (.run (.close 74)))))))) (.step 9 (.run (.close 2)))))))) (.step 61 (.step 73 (.step 74 (.step 63 (.split 43 1 (.split 7 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 13 0 (.split 25 0 (.step 44 (.step 71 (.step 36 (.split 14 0 (.step 2 (.run (.close 30))) (.step 27 (.step 2 (.run (.close 61)))))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 73 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 30 (.run (.close 27)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part783.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part784
namespace Part785
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 11572820244868830247473854590967953031538323462914888621343443953602130473634496993163312622100525555234343304138893017983619233032503133028593778031409291360824685355553760453686392677119158946764450884261699694411564188673⟩
def references : Fin 1 → Box := ![Part784.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 42 1 (.split 14 1 (.reuse 0) (.step 61 (.step 74 (.step 63 (.split 43 1 (.split 67 1 (.split 74 1 (.split 7 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 25 0 (.split 38 0 (.step 34 (.step 36 (.split 16 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 60))))))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 27)))) (.step 74 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 61 (.step 74 (.run (.close 2))))) (.step 30 (.step 61 (.step 73 (.step 4 (.step 2 (.run (.close 74)))))))) (.step 30 (.run (.close 27)))))))) (.step 68 (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 76 (.step 2 (.run (.close 57)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 10 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 57 (.step 74 (.step 2 (.run (.close 76))))))))))) (.step 73 (.step 7 (.step 18 (.split 14 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.step 73 (.step 68 (.step 2 (.run (.close 61))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 27 (.step 61 (.step 73 (.step 74 (.run (.close 2)))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part784.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part785
namespace Part786
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 11572820244868830247473854590967953031538323462914888621343443953602130473634496993163312622100525555234343304138895366528441751607910863755724344135091379767183648550820168747951579923358701566837429909940725293092386636801⟩
def references : Fin 1 → Box := ![Part785.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 57 (.step 68 (.step 7 (.step 31 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.split 26 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 57)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 57 (.step 10 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2))))))))) (.step 68 (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.split 26 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 57)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 16))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 57 (.step 74 (.step 2 (.run (.close 76))))))) (.step 76 (.step 7 (.run (.close 2))))) (.step 57 (.step 7 (.run (.close 2))))) (.step 57 (.step 74 (.step 58 (.run (.close 2)))))))))) (.step 68 (.step 7 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 30 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 7 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part785.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part786
namespace Part787
def root : Box := ⟨2147483648, 11578468272786246682467757592718095351076003906195540728648534471100779984578567948814069404084855446703933003623990344413588985204011315747264974909714398798632982140761562191409444146983781828332516994783350629493771338754⟩
def references : Fin 2 → Box := ![Part778.root, Part786.root]
def proof : Chunks.Proof 2 := (.split 69 1 (.reuse 0) (.step 2 (.split 10 1 (.split 16 1 (.split 17 1 (.reuse 1) (.step 61 (.step 68 (.step 7 (.step 18 (.split 22 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.split 10 0 (.split 11 0 (.step 68 (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 61)))) (.step 61 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2))))))))) (.step 7 (.step 18 (.split 14 1 (.split 17 1 (.split 22 1 (.split 74 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.step 35 (.step 68 (.step 2 (.run (.close 61))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 61 (.step 73 (.step 74 (.run (.close 2)))))) (.step 73 (.step 7 (.run (.close 2))))) (.step 61 (.step 7 (.run (.close 2))))) (.step 61 (.step 74 (.step 48 (.run (.close 2))))))))) (.step 68 (.step 7 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 64 (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 7)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part778.covered
  · exact Part786.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part787
namespace Part788
def root : Box := ⟨10032913020226237310869197622070557910061530690809581488606035047662224110216294903018315384440590765432325303757053790498770584583633048750167493382743608188543746320969475933440520778435368952317083648000, 5789239657434395681882170948429894122918091208062525490477267901621110877732094316015466104060479707567303614226493989846825482827700520546938355255963282243660965529285071897070414583984584511107699612759914880130610103297⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 51 0 (.split 67 0 (.split 14 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 35 1 (.split 72 1 (.step 2 (.step 74 (.step 2 (.run (.close 4))))) (.step 4 (.step 2 (.step 74 (.step 2 (.run (.close 66))))))) (.step 40 (.step 71 (.step 2 (.step 74 (.step 2 (.run (.close 66)))))))) (.step 18 (.split 35 1 (.split 72 1 (.step 2 (.step 74 (.step 2 (.run (.close 48))))) (.step 4 (.step 48 (.step 2 (.run (.close 69)))))) (.step 4 (.step 50 (.step 29 (.step 48 (.step 2 (.run (.close 69)))))))))) (.step 2 (.run (.close 71)))) (.step 18 (.split 35 1 (.split 72 1 (.split 63 1 (.step 2 (.step 74 (.run (.close 2)))) (.step 74 (.step 2 (.run (.close 60))))) (.step 74 (.step 71 (.step 2 (.step 60 (.step 2 (.run (.close 74)))))))) (.step 74 (.step 50 (.step 71 (.step 2 (.run (.close 38))))))))) (.step 18 (.split 35 1 (.split 72 1 (.split 63 1 (.split 64 1 (.step 2 (.step 63 (.step 2 (.run (.close 60))))) (.step 74 (.step 50 (.step 2 (.run (.close 57)))))) (.step 63 (.run (.close 66)))) (.step 66 (.step 71 (.step 31 (.step 2 (.run (.close 74))))))) (.step 50 (.step 66 (.step 71 (.step 31 (.step 2 (.run (.close 74)))))))))) (.step 2 (.run (.close 71)))) (.step 4 (.step 18 (.split 63 1 (.step 2 (.step 74 (.step 2 (.run (.close 73))))) (.step 74 (.step 2 (.run (.close 66)))))))) (.step 71 (.step 18 (.step 2 (.run (.close 73)))))) (.step 71 (.step 18 (.split 14 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part788
namespace Part789
def root : Box := ⟨10032913020226237310869197622070557910061530690809581488606035047662224110216294903018315384440590765432325303757053790498770584583633048750167493382743608188543746320969475933440520778435368952317083648000, 11572820244868825115638844745247568521943739773824517624870495604501199051647570113935680246465682661366024162776716499349226361299491329943416097989191124095840229460359224979992993701658346292432031230288568470855459275777⟩
def references : Fin 1 → Box := ![Part788.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 14 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 65 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 28 0 (.split 43 0 (.reuse 0) (.step 71 (.step 18 (.split 7 0 (.split 13 0 (.split 14 0 (.split 51 0 (.step 2 (.run (.close 30))) (.step 68 (.run (.close 2)))) (.step 27 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9))))))) (.step 2 (.step 58 (.step 74 (.step 48 (.step 50 (.step 60 (.step 74 (.run (.close 50)))))))))) (.step 71 (.step 18 (.run (.close 2))))) (.step 71 (.step 18 (.run (.close 2))))) (.step 71 (.step 18 (.run (.close 2))))) (.step 71 (.step 18 (.run (.close 2))))) (.step 71 (.step 18 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 9))))) (.step 74 (.step 4 (.step 63 (.step 66 (.step 67 (.step 18 (.split 43 0 (.split 51 0 (.split 67 0 (.step 2 (.run (.close 73))) (.step 73 (.run (.close 2)))) (.step 61 (.step 73 (.run (.close 2))))) (.step 27 (.run (.close 2))))))))))) (.step 68 (.step 18 (.run (.close 2))))) (.step 68 (.step 71 (.step 18 (.run (.close 2)))))) (.step 9 (.step 68 (.step 18 (.run (.close 2)))))) (.step 74 (.step 4 (.step 63 (.step 66 (.step 67 (.step 18 (.split 43 0 (.split 51 0 (.split 67 0 (.step 2 (.step 34 (.step 2 (.run (.close 73))))) (.step 4 (.run (.close 71)))) (.step 4 (.run (.close 71)))) (.step 27 (.run (.close 2))))))))))) (.step 40 (.step 18 (.step 31 (.step 75 (.step 38 (.split 63 1 (.split 64 1 (.step 2 (.step 60 (.step 2 (.run (.close 74))))) (.step 60 (.step 2 (.run (.close 67))))) (.step 60 (.step 74 (.step 2 (.run (.close 66))))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part788.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part789
namespace Part790
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411692881238169227504725489630651886188833479731882867073021121792535782274539962292755020136794038307604072032113814530530717468171233900715891770799110078253785128430405807657477667052061806188714836100097⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 8 0 (.split 14 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 39 0 (.split 58 0 (.split 65 0 (.step 2 (.run (.close 30))) (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2))))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 73)))) (.split 74 0 (.split 65 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 63 (.run (.close 2))))) (.split 39 0 (.split 58 0 (.split 74 0 (.split 40 0 (.split 65 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 4))))) (.split 37 0 (.split 5 0 (.split 74 0 (.split 65 0 (.split 11 0 (.split 53 0 (.split 60 0 (.split 27 0 (.split 32 0 (.split 36 0 (.step 21 (.step 2 (.run (.close 9)))) (.step 18 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 4))))) (.split 35 0 (.split 72 0 (.split 43 0 (.split 51 0 (.split 67 0 (.step 2 (.run (.close 57))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 71 (.run (.close 3)))))) (.step 2 (.run (.close 55))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part790
namespace Part791
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411692881238169227504725489630651886188833479731882867073021121792535782274539962292755020136794038307604072032113816567566693802657320169163265176843968046205923159436439758955602611661244167433164919145473⟩
def references : Fin 1 → Box := ![Part790.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.split 30 0 (.reuse 0) (.split 14 0 (.split 34 0 (.split 39 0 (.split 58 0 (.split 65 0 (.split 74 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 2 (.run (.close 9))))) (.step 63 (.run (.close 2))))) (.split 30 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 65 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 61))))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30)))))) (.split 22 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 65 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 61))))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 18 (.step 31 (.step 30 (.step 24 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part790.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part791
namespace Part792
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411692881238169227504725489630651886188833479731882867073021121792535782274539962292755020136794038307604072032113816567566693802657320169163265176843968046207384661073770661875073947094188679855417066521601⟩
def references : Fin 1 → Box := ![Part791.root]
def proof : Chunks.Proof 1 := (.split 4 0 (.split 10 0 (.split 16 0 (.reuse 0) (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 65 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 61))))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 18 (.step 31 (.step 30 (.step 24 (.run (.close 2))))))) (.step 18 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 58 0 (.split 65 0 (.split 74 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 2 (.run (.close 9))))) (.step 18 (.step 31 (.step 2 (.run (.close 10)))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 2)))))) (.step 2 (.run (.close 7))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part791.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part792
namespace Part793
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789239657434395676870613326299372006716650588472163971753229692767430985896862397067909022500125627357272754836742192539198583182353744924071025677522591197912388094759252222565763296057315783437517150205608634649043534849⟩
def references : Fin 1 → Box := ![Part792.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 65 1 (.split 67 1 (.reuse 0) (.split 63 0 (.split 64 0 (.split 65 0 (.split 71 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 2 (.run (.close 30))) (.step 10 (.step 2 (.run (.close 60))))) (.step 10 (.step 76 (.run (.close 2))))) (.step 10 (.step 76 (.step 2 (.run (.close 7)))))) (.step 68 (.run (.close 2)))) (.step 73 (.step 68 (.run (.close 2))))) (.step 30 (.step 73 (.step 68 (.run (.close 2)))))) (.step 30 (.step 73 (.step 68 (.step 2 (.run (.close 7))))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 76 (.step 71 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 53 0 (.step 21 (.step 26 (.split 34 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 76 (.run (.close 2)))) (.step 73 (.run (.close 4)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9))))))) (.step 63 (.step 67 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))))))) (.step 63 (.step 67 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))))))) (.step 63 (.step 67 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part792.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part793
namespace Part794
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789239657434395676870613326299372006716650588472163971753229692767434337848844882717183916009147848512925439537775757115184713766222624051275255941524212043666540296702924091159123710597044888490419417828051925015955768321⟩
def references : Fin 1 → Box := ![Part793.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 43 1 (.split 51 1 (.reuse 0) (.step 68 (.split 72 1 (.split 48 0 (.split 63 0 (.split 64 0 (.split 65 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 2 (.run (.close 30))) (.step 10 (.step 2 (.run (.close 60))))) (.step 10 (.step 68 (.step 2 (.run (.close 76)))))) (.step 7 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 68 (.run (.close 2))))) (.step 30 (.step 68 (.step 2 (.run (.close 73)))))) (.step 7 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 65 (.run (.close 70)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 10 (.step 57 (.step 73 (.step 76 (.step 58 (.run (.close 2)))))))))) (.step 68 (.split 72 1 (.split 51 1 (.split 63 0 (.split 64 0 (.split 65 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.step 10 (.step 30 (.run (.close 2)))) (.step 30 (.run (.close 2)))) (.step 30 (.run (.close 9)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 10 (.run (.close 2))))) (.step 30 (.step 10 (.step 2 (.run (.close 50)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 10 (.step 65 (.step 70 (.step 2 (.run (.close 7)))))))) (.step 9 (.run (.close 10)))))) (.step 67 (.step 71 (.step 21 (.step 4 (.step 10 (.step 63 (.run (.close 71)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part793.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part794
namespace Part795
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 11572820244868825110622388235134449870860223399944194742304836847174231302428579410524413706207378882309324268078261382107181225747541568712014436666745477669636810692059526706091875588858676621432620836023097083727574991873⟩
def references : Fin 1 → Box := ![Part794.root]
def proof : Chunks.Proof 1 := (.split 14 1 (.split 74 1 (.reuse 0) (.step 73 (.step 63 (.step 67 (.split 43 1 (.split 51 1 (.split 7 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 13 0 (.split 25 0 (.step 44 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 61))))) (.step 27 (.step 42 (.step 2 (.run (.close 61))))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 73 (.run (.close 2)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 30 (.step 61 (.step 73 (.step 76 (.step 2 (.run (.close 7)))))))) (.step 30 (.run (.close 27)))))))) (.step 63 (.step 67 (.split 43 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 7 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 25 0 (.split 38 0 (.step 34 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 27)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 5 (.step 42 (.step 63 (.step 2 (.run (.close 60))))))) (.step 30 (.step 73 (.step 4 (.step 48 (.run (.close 2))))))) (.step 30 (.step 61 (.step 4 (.step 48 (.step 2 (.run (.close 73)))))))) (.step 30 (.run (.close 27)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part794.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part795
namespace Part796
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 11572820244868825110622388235134449870860223399944194742304836847174231302428579410524413706207381589994572432936525037694865701810948595338192647699647043275336159644748052915502596215828479220785141795034722128175196800001⟩
def references : Fin 1 → Box := ![Part795.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 22 1 (.split 42 1 (.reuse 0) (.step 76 (.step 68 (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 76 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 10 (.step 2 (.run (.close 50))))))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 2))))))))) (.step 73 (.step 68 (.step 7 (.step 18 (.split 14 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.step 73 (.step 68 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2))))))))) (.step 68 (.step 7 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.split 26 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 10 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 76 (.step 48 (.step 2 (.run (.close 58))))))) (.step 76 (.step 7 (.run (.close 2))))) (.step 58 (.run (.close 41))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part795.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part796
namespace Part797
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 11572820244868825110622388235134449870860223399944194742304836847174231302428579410524413706207381589994572432936525037697105446553128436584726424466301755999146214520143755415373927879887495472987925823189175085827911320577⟩
def references : Fin 1 → Box := ![Part796.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 68 (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.split 26 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 16))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 76 (.step 48 (.step 2 (.run (.close 7))))))) (.step 76 (.step 7 (.run (.close 2))))) (.step 7 (.step 2 (.run (.close 76))))) (.step 58 (.run (.close 41)))))))) (.step 50 (.step 7 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 30 (.step 2 (.run (.close 7))))) (.step 50 (.run (.close 2)))) (.step 50 (.run (.close 2)))) (.step 7 (.run (.close 2))))))))) (.step 68 (.step 7 (.step 18 (.split 14 1 (.split 22 1 (.split 74 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.split 10 0 (.split 11 0 (.step 68 (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 7)))) (.step 48 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2)))) (.step 73 (.step 7 (.run (.close 2))))) (.step 48 (.step 2 (.run (.close 73)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part796.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part797
namespace Part798
def root : Box := ⟨2147483648, 11578468272786246687484214102831214010861685154385775756144406404583393723965612293065026974042849278350796658224387299648970855639296519196191654352862259491435906766184343990924104973524403382176643154684576355959156245506⟩
def references : Fin 3 → Box := ![Part787.root, Part789.root, Part797.root]
def proof : Chunks.Proof 3 := (.split 62 1 (.split 68 1 (.reuse 0) (.step 2 (.split 34 1 (.split 36 1 (.reuse 1) (.step 74 (.step 40 (.step 18 (.step 31 (.step 75 (.step 38 (.split 42 1 (.split 63 1 (.step 2 (.step 74 (.step 2 (.run (.close 60))))) (.step 74 (.step 2 (.run (.close 66))))) (.step 31 (.run (.close 2))))))))))) (.step 40 (.step 66 (.step 29 (.step 18 (.step 31 (.step 75 (.step 38 (.split 36 1 (.split 42 1 (.split 64 1 (.step 2 (.step 49 (.step 48 (.run (.close 31))))) (.step 74 (.step 50 (.step 2 (.run (.close 60)))))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))))))))))))) (.step 2 (.split 10 1 (.split 16 1 (.reuse 2) (.step 42 (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.step 35 (.step 68 (.step 2 (.run (.close 73))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 42 (.step 35 (.step 8 (.step 68 (.run (.close 2))))))) (.step 42 (.step 7 (.run (.close 2))))))))) (.step 68 (.step 7 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 64 (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 7)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 65)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part787.covered
  · exact Part789.covered
  · exact Part797.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part798
namespace Part799
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411692881238169227500378656297439464253157889849457463826955731717057753015075711465722917402892823553026766113575178056616527195655792536406295365499760322206456189676487350809288293645575498590122301981697⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 0 0 (.split 14 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 39 0 (.split 58 0 (.split 65 0 (.step 2 (.run (.close 30))) (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2))))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 73)))) (.split 74 0 (.split 65 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 63 (.run (.close 2))))) (.split 39 0 (.split 58 0 (.split 74 0 (.split 40 0 (.split 65 0 (.split 42 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 4))))) (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 74 0 (.split 65 0 (.split 9 0 (.split 60 0 (.split 27 0 (.split 32 0 (.split 36 0 (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2)))) (.step 43 (.step 10 (.step 18 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.split 35 0 (.split 72 0 (.split 43 0 (.split 51 0 (.split 67 0 (.step 2 (.run (.close 57))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 71 (.run (.close 3)))))) (.step 2 (.run (.close 55))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part799
namespace Part800
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411692881238169227500378656297439464253157889849457463826955731717057753015075711465722917402892823553026766113575180093652503530141878804853668771544618290158594220682521302107413238254757859834572385027073⟩
def references : Fin 1 → Box := ![Part799.root]
def proof : Chunks.Proof 1 := (.split 17 0 (.split 22 0 (.split 30 0 (.reuse 0) (.split 14 0 (.split 34 0 (.split 39 0 (.split 58 0 (.split 65 0 (.split 74 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 2 (.run (.close 9))))) (.step 63 (.run (.close 2))))) (.split 24 0 (.split 30 0 (.split 35 0 (.split 1 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 54 0 (.split 72 0 (.split 11 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 7))))) (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 1 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 54 0 (.split 72 0 (.split 11 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 61)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 7)))) (.step 18 (.step 31 (.step 30 (.step 24 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part799.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part800
namespace Part801
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411692881238169227500378656297439464253157889849457463826955731717057753015075711465722917402892823553026766113575180093652503530141878804853668771544618290160057149567544910986765631973671821750861403522049⟩
def references : Fin 1 → Box := ![Part800.root]
def proof : Chunks.Proof 1 := (.split 15 0 (.split 10 0 (.split 16 0 (.reuse 0) (.split 17 0 (.split 22 0 (.split 24 0 (.split 30 0 (.split 35 0 (.split 1 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 54 0 (.split 72 0 (.split 11 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 7)))) (.step 18 (.step 31 (.step 30 (.step 24 (.run (.close 2))))))) (.step 18 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 14 0 (.split 30 0 (.split 34 0 (.split 39 0 (.split 58 0 (.split 65 0 (.split 74 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 68 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 68 (.step 2 (.run (.close 9))))) (.step 18 (.step 31 (.step 2 (.run (.close 10)))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 68 (.run (.close 2)))))) (.step 2 (.run (.close 18))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part800.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part801
namespace Part802
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789239657434395676870613326299372002369817255259742036077639810342027739831472321589879763035874800325170020935527437961892664643717271009880753162081226888315982795409496175238251789831564895129202029688750530093380535297⟩
def references : Fin 1 → Box := ![Part801.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.split 64 1 (.split 71 1 (.split 72 1 (.split 65 1 (.split 67 1 (.reuse 0) (.split 63 0 (.split 64 0 (.split 65 0 (.split 71 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 2 (.run (.close 30))) (.step 10 (.step 2 (.run (.close 60))))) (.step 10 (.step 76 (.run (.close 2))))) (.step 10 (.step 76 (.step 2 (.run (.close 7)))))) (.step 68 (.run (.close 2)))) (.step 73 (.step 68 (.run (.close 2))))) (.step 30 (.step 73 (.step 68 (.run (.close 2)))))) (.step 30 (.step 73 (.step 68 (.step 2 (.run (.close 7))))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 76 (.step 71 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 53 0 (.step 26 (.split 34 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57))))) (.step 9 (.step 76 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 76 (.run (.close 2)))) (.step 73 (.run (.close 4)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9))))))) (.step 63 (.step 66 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))))))) (.step 63 (.step 66 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2))))))))) (.step 63 (.step 66 (.step 68 (.step 71 (.split 14 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part801.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part802
namespace Part803
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789239657434395676870613326299372002369817255259742036077639810342031091783454807239154656544897021480822705636561000244380179237514638526264088123995906937505145829072044306242772817448417911697296227292640710334606214145⟩
def references : Fin 1 → Box := ![Part802.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.reuse 0) (.step 68 (.split 72 1 (.split 48 0 (.split 63 0 (.split 64 0 (.split 65 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 2 (.run (.close 30))) (.step 10 (.step 2 (.run (.close 60))))) (.step 10 (.step 68 (.step 2 (.run (.close 76)))))) (.step 7 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 68 (.run (.close 2))))) (.step 30 (.step 68 (.step 2 (.run (.close 73)))))) (.step 7 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 64 (.run (.close 70)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 10 (.step 57 (.step 73 (.step 76 (.step 58 (.run (.close 2)))))))))) (.step 68 (.split 72 1 (.split 51 1 (.split 63 0 (.split 64 0 (.split 65 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.step 10 (.step 30 (.run (.close 2)))) (.step 30 (.run (.close 2)))) (.step 30 (.run (.close 9)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 10 (.run (.close 2))))) (.step 30 (.step 10 (.step 2 (.run (.close 7)))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 30 (.step 10 (.step 64 (.step 70 (.step 2 (.run (.close 7)))))))) (.step 9 (.run (.close 10))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part802.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part803
namespace Part804
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 11572820244868825110622388235134449866513390066731772806629246964748828056363189335046384446743128055277221534177046627529875307208905094797824164151304113360040405392709770658764364082632925733124305715506238979171911992321⟩
def references : Fin 1 → Box := ![Part803.root]
def proof : Chunks.Proof 1 := (.split 14 1 (.split 74 1 (.split 35 1 (.reuse 0) (.step 66 (.step 71 (.split 43 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 53 0 (.step 21 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57))))) (.step 9 (.step 48 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 9 (.step 66 (.step 2 (.run (.close 76)))))) (.step 10 (.step 76 (.step 4 (.step 58 (.run (.close 2))))))) (.step 10 (.step 57 (.step 4 (.step 58 (.step 2 (.run (.close 76)))))))) (.step 9 (.run (.close 2))))))) (.step 73 (.step 63 (.step 66 (.split 43 1 (.split 51 1 (.split 7 0 (.split 26 0 (.split 35 0 (.split 72 0 (.split 13 0 (.split 25 0 (.step 44 (.step 71 (.step 34 (.split 16 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 61)))))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 73 (.run (.close 2)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 5)))) (.step 30 (.step 61 (.step 73 (.step 76 (.step 2 (.run (.close 7)))))))) (.step 30 (.run (.close 27)))))))) (.step 63 (.step 66 (.step 34 (.step 5 (.step 30 (.step 63 (.run (.close 60)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part803.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part804
namespace Part805
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 11572820244868825110622388235134449866513390066731772806629246964748828056363189335046384446743130762962469699035310283117559783272312121424002375184205678965739754345398296868175084709602728332476826674517864023619533800449⟩
def references : Fin 1 → Box := ![Part804.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 22 1 (.split 42 1 (.reuse 0) (.step 76 (.step 68 (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 76 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 49 (.step 58 (.step 2 (.run (.close 10))))))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 2))))))))) (.step 73 (.step 68 (.step 7 (.step 18 (.split 14 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.step 73 (.step 68 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2))))))))) (.step 68 (.step 7 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.split 26 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 49 (.step 58 (.step 2 (.run (.close 10))))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 76 (.step 48 (.step 2 (.run (.close 58))))))) (.step 76 (.step 7 (.run (.close 2))))) (.step 58 (.step 2 (.run (.close 76)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part804.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part805
namespace Part806
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 11572820244868825110622388235134449866513390066731772806629246964748828056363189335046384446743130762962469699035310283119799528014491962670536151950860391689549809220793999368046416373661744584679610702672316981272248321025⟩
def references : Fin 1 → Box := ![Part805.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 68 (.step 7 (.step 15 (.step 31 (.split 36 1 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.split 26 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 49 (.run (.close 16))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.step 2 (.run (.close 60)))))))))) (.step 68 (.step 7 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 30 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 7 (.run (.close 2))))))))) (.step 68 (.step 7 (.step 18 (.split 14 1 (.split 22 1 (.split 74 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.split 10 0 (.split 11 0 (.step 68 (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 7)))) (.step 49 (.step 48 (.run (.close 2))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2)))) (.step 73 (.step 7 (.run (.close 2))))) (.step 48 (.run (.close 14))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part805.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part806
namespace Part807
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234141782132574873516826277910694132748938512735810729627430679075101303845640839375915549437537784362680244411044258347987359544284364296018936855104637465206097715583694401964757640724005310297375388773707716854023168⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 42 0 (.split 65 0 (.split 14 0 (.split 63 1 (.split 64 1 (.step 2 (.split 16 0 (.step 2 (.run (.close 60))) (.step 18 (.step 50 (.run (.close 56)))))) (.step 74 (.step 51 (.step 2 (.run (.close 60)))))) (.step 74 (.step 51 (.step 2 (.step 74 (.step 2 (.run (.close 60)))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 35 0 (.step 2 (.run (.close 60))) (.step 4 (.step 2 (.run (.close 60))))) (.step 74 (.run (.close 2)))) (.step 74 (.step 2 (.run (.close 60))))) (.step 74 (.step 2 (.run (.close 49)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 57))) (.step 24 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 60))))) (.step 74 (.run (.close 2)))) (.step 74 (.step 50 (.step 2 (.run (.close 60)))))) (.step 74 (.step 49 (.step 2 (.run (.close 71))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 60 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 4 (.step 48 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 74 (.run (.close 2)))) (.step 60 (.step 74 (.step 2 (.run (.close 57)))))) (.step 60 (.step 74 (.step 2 (.step 50 (.step 2 (.run (.close 5)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part807
namespace Part808
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234141782132574873516826277910694132748938512735810729627430679075101303845640839375915549437537784362680244413392803170505934949978055450250554450924598135759914820940520273486067629630484933922019768035969691493073920⟩
def references : Fin 1 → Box := ![Part807.root]
def proof : Chunks.Proof 1 := (.split 34 0 (.split 36 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 37 0 (.split 14 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 48 0 (.split 56 0 (.split 59 0 (.split 58 0 (.split 25 0 (.step 24 (.step 51 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 31 (.run (.close 2)))) (.step 4 (.step 8 (.step 71 (.step 49 (.step 2 (.run (.close 60)))))))) (.step 2 (.run (.close 74)))) (.step 74 (.run (.close 2)))) (.step 74 (.run (.close 2)))) (.step 74 (.run (.close 2))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 24 (.step 4 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 74 (.run (.close 2)))) (.step 74 (.step 50 (.step 49 (.step 48 (.step 2 (.run (.close 60)))))))) (.step 48 (.step 71 (.step 66 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part807.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part808
namespace Part809
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234141782132574878415709588568036569696788914137450334149662461700319217061542039267129424776309185629776754255837295341773118472469492975563340869331721909965669861781428713819471379769378422641471658271544928966280192⟩
def references : Fin 1 → Box := ![Part808.root]
def proof : Chunks.Proof 1 := (.split 43 0 (.split 51 0 (.split 67 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 35 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 57))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 36)))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 35 0 (.split 37 0 (.split 34 0 (.split 19 0 (.split 33 0 (.split 71 0 (.split 36 0 (.split 42 0 (.split 65 0 (.step 2 (.run (.close 57))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 57)))) (.step 48 (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2)))) (.step 4 (.step 30 (.step 4 (.step 48 (.step 2 (.run (.close 60)))))))) (.step 48 (.run (.close 36)))) (.step 48 (.run (.close 51)))) (.step 48 (.run (.close 51))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 35 0 (.split 51 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 30))) (.step 4 (.step 2 (.run (.close 30))))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 3 (.step 30 (.step 2 (.run (.close 9)))))) (.step 48 (.run (.close 2)))) (.step 4 (.step 30 (.step 2 (.run (.close 60)))))) (.step 48 (.run (.close 36)))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part808.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part809
namespace Part810
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205998256835176131859587340483017873674912474333270064566263551852159197645375568306810149404672, 5789234141782132574878415709588563581061281142239119246065003470770953353173597432117459923182083048174724299530245577614861970997966910198571454863667210823160170579821662728492915366405612304033446673011794566328321311744⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 64 1 (.split 71 1 (.split 52 0 (.split 1 0 (.split 6 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 15 0 (.split 20 0 (.split 24 0 (.split 25 0 (.split 37 0 (.split 60 0 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 45 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 55 0 (.split 68 0 (.split 21 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 73 0 (.split 9 0 (.step 8 (.split 29 0 (.step 56 (.split 61 0 (.step 56 (.step 50 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 73))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 4 (.step 24 (.step 2 (.run (.close 74)))))) (.step 4 (.step 24 (.step 50 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 48 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 74 (.run (.close 2)))) (.step 50 (.run (.close 2))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part810
namespace Part811
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915712977493864304034371600669212672, 5789234136395753411692881238169227500374407193496930116368373147316388081093901841329179018420248543250630330437237451990120872930463597673110817274452359972960541873980612872241925454650535628553332223897849789709780254720⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 6 0 (.split 12 0 (.split 14 0 (.split 15 0 (.split 20 0 (.split 24 0 (.split 25 0 (.split 37 0 (.split 60 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 45 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 55 0 (.split 68 0 (.split 21 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 73 0 (.split 9 0 (.step 8 (.split 29 0 (.step 56 (.step 14 (.step 56 (.step 49 (.run (.close 18)))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 4 (.step 24 (.step 2 (.run (.close 74)))))) (.step 24 (.step 49 (.run (.close 2))))) (.step 3 (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.step 14 (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 50)))) (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part811
namespace Part812
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072040699457630145252839209775515890369545914486316893376530241917288448, 5789234141782132574878415709588568036569696788914137450334149662461700319217061542039267129424776309185629776754255837295341773118474506530894566719181329240202833621543266790916580689621271958493780389333954349505549698049⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 73 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 37 0 (.split 40 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 52 0 (.split 59 0 (.split 65 0 (.split 67 0 (.split 63 1 (.split 64 1 (.split 0 0 (.split 9 0 (.step 56 (.run (.close 25))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 60 (.step 74 (.step 2 (.run (.close 50)))))) (.step 60 (.step 74 (.step 2 (.step 50 (.step 2 (.run (.close 49)))))))) (.step 73 (.step 58 (.step 7 (.step 2 (.run (.close 61))))))) (.step 60 (.step 58 (.step 7 (.step 2 (.run (.close 61))))))) (.step 2 (.run (.close 25)))) (.step 2 (.run (.close 58)))) (.step 73 (.step 58 (.run (.close 56))))) (.step 2 (.run (.close 25)))) (.step 2 (.run (.close 25)))) (.step 7 (.step 18 (.run (.close 25))))) (.step 2 (.step 58 (.run (.close 7))))) (.step 2 (.step 58 (.run (.close 7))))) (.step 74 (.step 7 (.run (.close 56)))))) (.step 60 (.step 74 (.step 50 (.step 7 (.step 2 (.step 74 (.run (.close 2))))))))) (.step 60 (.step 8 (.step 7 (.step 18 (.step 74 (.run (.close 25)))))))) (.step 2 (.step 30 (.step 60 (.step 74 (.run (.close 4))))))) (.step 2 (.run (.close 56)))) (.step 2 (.run (.close 56)))) (.step 2 (.step 24 (.run (.close 18))))) (.step 2 (.step 24 (.run (.close 74))))) (.step 2 (.step 24 (.run (.close 18))))) (.step 2 (.step 4 (.step 48 (.run (.close 18))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part812
namespace Part813
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234141782132574878415709588568036569696788914137450334149662461700319217061542039267129424776309185629776754255837295341773118474506530894566719181329240202833621543268287494257316465860199067049090807766477180473705473⟩
def references : Fin 4 → Box := ![Part809.root, Part810.root, Part811.root, Part812.root]
def proof : Chunks.Proof 4 := (.split 17 1 (.split 22 1 (.split 0 0 (.split 2 0 (.split 4 0 (.split 10 0 (.split 28 0 (.split 30 0 (.reuse 0) (.split 63 1 (.reuse 1) (.step 74 (.step 50 (.step 4 (.step 49 (.step 2 (.run (.close 30))))))))) (.step 2 (.step 7 (.step 74 (.run (.close 31)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 28 0 (.split 52 0 (.split 1 0 (.reuse 2) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 74 (.step 2 (.run (.close 30))))) (.step 74 (.step 49 (.step 4 (.step 48 (.run (.close 2))))))) (.step 49 (.run (.close 2))))) (.step 2 (.step 7 (.run (.close 74))))) (.step 2 (.step 58 (.step 4 (.run (.close 74)))))) (.step 2 (.step 7 (.run (.close 74))))) (.reuse 3)) (.step 74 (.split 12 0 (.split 18 0 (.split 19 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 37 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 59 0 (.split 67 0 (.split 0 0 (.split 9 0 (.step 56 (.step 51 (.run (.close 2)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 61 (.run (.close 2)))) (.step 2 (.run (.close 61)))) (.step 61 (.run (.close 56)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 61)))) (.step 74 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 36)))) (.step 74 (.run (.close 56))))) (.step 61 (.step 74 (.run (.close 2))))) (.step 74 (.step 7 (.run (.close 2))))) (.step 2 (.step 30 (.run (.close 74))))) (.step 2 (.run (.close 56)))) (.step 2 (.step 24 (.run (.close 74))))) (.step 56 (.run (.close 25)))) (.step 2 (.run (.close 20)))) (.step 2 (.step 24 (.run (.close 20))))) (.step 2 (.step 61 (.run (.close 20)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part809.covered
  · exact Part810.covered
  · exact Part811.covered
  · exact Part812.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part813
namespace Part814
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234141782132574878415709588568036569696788914137450334149662461700319217061542039267129424776309185629776754255837295341773118474506530894566719181329240202833621543268288955758953796763117270733923524049496836406248449⟩
def references : Fin 1 → Box := ![Part813.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.reuse 0) (.split 12 0 (.split 13 0 (.split 17 1 (.split 18 0 (.split 19 0 (.split 20 0 (.split 21 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 73 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 37 0 (.split 40 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 59 0 (.split 65 0 (.split 67 0 (.split 63 1 (.split 64 1 (.split 71 1 (.split 9 0 (.step 56 (.run (.close 19))) (.step 2 (.run (.close 18)))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 74 (.step 50 (.step 49 (.step 2 (.run (.close 60))))))) (.step 30 (.step 7 (.step 18 (.run (.close 19)))))) (.step 50 (.step 7 (.step 58 (.run (.close 2)))))) (.step 2 (.run (.close 19)))) (.step 35 (.step 7 (.run (.close 56))))) (.step 2 (.run (.close 19)))) (.step 2 (.run (.close 19)))) (.step 50 (.step 67 (.step 7 (.step 18 (.step 58 (.step 60 (.run (.close 56))))))))) (.step 2 (.step 58 (.run (.close 43))))) (.step 2 (.step 58 (.run (.close 43))))) (.step 7 (.step 18 (.run (.close 56)))))) (.step 50 (.step 35 (.run (.close 2))))) (.step 74 (.step 50 (.step 67 (.step 8 (.step 7 (.step 18 (.step 66 (.step 51 (.step 2 (.run (.close 60)))))))))))) (.step 2 (.step 30 (.step 74 (.run (.close 19)))))) (.step 2 (.run (.close 56)))) (.step 2 (.run (.close 56)))) (.step 2 (.step 24 (.run (.close 18))))) (.step 56 (.run (.close 25)))) (.step 2 (.step 24 (.run (.close 19))))) (.step 2 (.run (.close 19)))) (.step 2 (.step 24 (.run (.close 19))))) (.step 2 (.run (.close 19)))) (.step 8 (.step 56 (.step 20 (.run (.close 2)))))) (.step 2 (.run (.close 56)))) (.step 2 (.step 4 (.run (.close 19))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part813.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part814
namespace Part815
def root : Box := ⟨11567161174868858867503549817670155728287145622944061541103214315843146733133213403755925998655808722076699404427715989203923606168634109120678158823943603289270005087464628094741899598943029361266353408501111206482016206848, 11572820244868825110617489347151853331627065208499277305998109714137893499995683494062317048283009286790616439079635015916767717736929153971186962329601036613804707307829610818657271818606712617845374651218848457249810023425⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 74 (.step 4 (.split 4 0 (.split 10 0 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 63 1 (.split 64 1 (.split 67 0 (.split 65 0 (.split 22 0 (.split 35 0 (.step 2 (.run (.close 74))) (.step 74 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 61 (.step 73 (.step 2 (.run (.close 74)))))) (.step 61 (.step 73 (.step 2 (.run (.close 74)))))) (.step 60 (.step 74 (.step 50 (.step 58 (.run (.close 2))))))) (.step 60 (.step 74 (.step 49 (.step 58 (.step 2 (.run (.close 4)))))))) (.step 61 (.step 73 (.step 4 (.step 2 (.run (.close 58))))))) (.step 61 (.step 73 (.step 4 (.step 27 (.step 2 (.run (.close 11)))))))) (.step 60 (.step 2 (.run (.close 30))))) (.step 60 (.step 74 (.run (.close 2))))) (.step 60 (.step 74 (.step 4 (.step 2 (.run (.close 66))))))) (.step 4 (.step 48 (.step 8 (.step 18 (.step 77 (.run (.close 2)))))))) (.step 60 (.step 73 (.run (.close 2))))) (.step 61 (.step 74 (.step 2 (.run (.close 77)))))) (.step 77 (.step 56 (.run (.close 19))))) (.step 8 (.step 7 (.step 25 (.step 20 (.step 19 (.step 18 (.step 77 (.run (.close 2)))))))))) (.step 2 (.step 7 (.run (.close 77)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part815
namespace Part816
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876401417606065528037735956040589051149154254848, 11572820244868825110617489347151853331627065208499277305998109714137893499995683494062317048283009286790616439079635015916767717736929153971186962329601036613804707307829610818657273212403287526009320997201240497772404147201⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 74 (.step 4 (.step 49 (.split 64 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 0 (.split 36 0 (.split 74 1 (.split 8 0 (.split 37 0 (.split 52 0 (.split 65 0 (.split 24 0 (.split 39 0 (.split 4 0 (.split 49 0 (.split 42 0 (.split 43 0 (.split 50 0 (.split 51 0 (.split 10 0 (.split 30 0 (.split 67 0 (.step 18 (.split 26 0 (.split 35 0 (.step 14 (.step 2 (.run (.close 60)))) (.step 74 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 17))))) (.step 61 (.step 4 (.step 2 (.run (.close 60)))))) (.step 4 (.step 48 (.step 8 (.step 18 (.run (.close 56))))))) (.step 8 (.step 7 (.step 18 (.run (.close 56)))))) (.step 61 (.step 48 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 17)))) (.step 61 (.step 48 (.step 2 (.run (.close 60)))))) (.step 74 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 17)))) (.step 2 (.step 48 (.run (.close 17))))) (.step 2 (.run (.close 17)))) (.step 2 (.run (.close 17)))) (.step 74 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 8)))) (.step 77 (.run (.close 2)))) (.step 74 (.step 4 (.run (.close 2))))) (.step 74 (.step 4 (.step 2 (.step 60 (.step 2 (.run (.close 5)))))))) (.step 56 (.step 17 (.run (.close 25))))) (.step 61 (.step 74 (.step 14 (.step 2 (.run (.close 17))))))) (.step 56 (.step 17 (.run (.close 19))))) (.step 74 (.step 58 (.step 67 (.step 2 (.run (.close 60))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part816
namespace Part817
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 11572820244868825110617489351823792524072193112387837030235208030828559491418208862975410186611867058012302082861689734705756031110258878974547635415746270248493155818040336010052820541173330072554232306086103670632926413825⟩
def references : Fin 3 → Box := ![Part814.root, Part815.root, Part816.root]
def proof : Chunks.Proof 3 := (.split 65 1 (.split 14 1 (.split 74 1 (.split 35 1 (.split 72 1 (.reuse 0) (.step 60 (.step 74 (.step 4 (.split 16 1 (.split 63 1 (.split 64 1 (.split 5 0 (.step 71 (.split 61 0 (.split 62 0 (.step 69 (.step 51 (.split 16 0 (.step 2 (.run (.close 60))) (.step 60 (.step 2 (.run (.close 74))))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 57 (.step 60 (.step 74 (.run (.close 2)))))) (.step 57 (.step 60 (.step 74 (.run (.close 66)))))) (.step 60 (.step 73 (.step 74 (.step 2 (.run (.close 4))))))))))) (.step 74 (.step 4 (.step 50 (.split 22 1 (.split 72 1 (.split 63 1 (.split 5 0 (.step 71 (.split 61 0 (.split 62 0 (.split 69 0 (.step 51 (.split 16 0 (.split 22 0 (.step 2 (.run (.close 60))) (.step 74 (.run (.close 2)))) (.step 74 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 74 (.step 4 (.run (.close 2))))) (.step 57 (.step 74 (.step 60 (.step 2 (.run (.close 4))))))) (.step 4 (.run (.close 2)))))))) (.reuse 1)) (.reuse 2)) (.step 63 (.step 24 (.split 43 0 (.step 36 (.split 49 0 (.split 50 0 (.split 16 1 (.split 22 1 (.split 4 0 (.step 51 (.split 10 0 (.split 30 0 (.step 2 (.run (.close 60))) (.step 50 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 58 (.step 2 (.run (.close 50))))) (.step 50 (.step 58 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 30 (.run (.close 27)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part814.covered
  · exact Part815.covered
  · exact Part816.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part817
namespace Part818
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 11572820244868825110622388235134449866509140962789238669839730262611184709331424764175301400484435867404696529370217420603708435395929764173432784940464207673788738048501812052597200823814196941375920924998652431691678745601⟩
def references : Fin 1 → Box := ![Part817.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 67 1 (.split 34 1 (.split 36 1 (.split 42 1 (.reuse 0) (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 24 0 (.split 18 0 (.step 60 (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 2 (.run (.close 50)))))) (.step 2 (.run (.close 7)))) (.step 57 (.step 60 (.step 74 (.step 2 (.run (.close 4)))))))))) (.step 74 (.step 7 (.step 31 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 30 0 (.step 2 (.run (.close 60))) (.step 74 (.run (.close 2)))) (.step 74 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))))))) (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 16 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 49))))) (.step 2 (.run (.close 7)))) (.step 57 (.step 60 (.step 74 (.run (.close 2)))))) (.step 7 (.run (.close 2)))) (.step 74 (.step 7 (.run (.close 2))))) (.step 74 (.step 4 (.run (.close 2)))))))) (.step 48 (.step 7 (.step 3 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 2 (.run (.close 61))) (.step 30 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 7)))))))) (.step 7 (.step 3 (.split 67 1 (.split 9 0 (.step 68 (.split 10 0 (.split 19 0 (.split 33 0 (.split 18 0 (.step 48 (.run (.close 2))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 57)))) (.step 61 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 68 (.step 30 (.step 2 (.run (.close 35))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part817.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part818
namespace Part819
def root : Box := ⟨2147483648, 11578468272786246687484214102831214010865934258328309892933923113750589874971121212077576438558118158698350760376646487200849446760416463381142667675502767518223411549261277081277580448360993936847115436889161986762319332354⟩
def references : Fin 3 → Box := ![Part798.root, Part806.root, Part818.root]
def proof : Chunks.Proof 3 := (.split 53 1 (.split 61 1 (.reuse 0) (.step 2 (.split 10 1 (.split 16 1 (.reuse 1) (.step 68 (.step 7 (.step 18 (.split 14 1 (.split 17 1 (.split 22 1 (.split 74 1 (.split 7 0 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 24 (.step 30 (.step 35 (.step 68 (.step 2 (.run (.close 73))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2)))) (.step 73 (.step 7 (.run (.close 2))))) (.step 7 (.step 2 (.run (.close 73))))) (.step 48 (.run (.close 14)))))))) (.step 7 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 64 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 49 (.run (.close 2)))) (.step 49 (.run (.close 2)))) (.step 49 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))) (.step 2 (.split 10 1 (.split 30 1 (.split 43 1 (.reuse 2) (.step 48 (.step 68 (.step 3 (.step 30 (.step 68 (.run (.close 2)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.split 16 0 (.step 2 (.run (.close 7))) (.step 50 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 50)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 8 (.step 14 (.step 56 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part798.covered
  · exact Part806.covered
  · exact Part818.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part819
namespace Part820
def root : Box := ⟨2596148429267413814265250312093696, 5789234141782132574873516826277910694132748938512735810729627427164298699316973466768642706419764210542411806571038674648382696256546174464696120250104568618800473949339872261963765442634267447529590377057778355290028114944⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 42 0 (.split 65 0 (.split 14 0 (.split 63 1 (.split 64 1 (.step 2 (.split 16 0 (.step 2 (.run (.close 60))) (.step 18 (.step 50 (.step 2 (.run (.close 60))))))) (.split 16 0 (.step 2 (.step 50 (.step 2 (.run (.close 60))))) (.step 74 (.step 50 (.step 2 (.run (.close 60))))))) (.step 66 (.split 16 0 (.step 2 (.run (.close 60))) (.step 50 (.step 2 (.run (.close 60))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 35 0 (.step 2 (.run (.close 60))) (.step 4 (.step 2 (.run (.close 60))))) (.step 18 (.run (.close 74)))) (.step 74 (.step 50 (.step 49 (.step 2 (.run (.close 60))))))) (.step 49 (.run (.close 2))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 60))) (.step 24 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 60))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 48 (.step 58 (.run (.close 2)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.step 48 (.step 66 (.step 2 (.run (.close 74))))))) (.step 60 (.step 74 (.step 50 (.step 48 (.step 2 (.run (.close 74)))))))) (.step 60 (.step 74 (.step 49 (.step 48 (.step 2 (.run (.close 66)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part820
namespace Part821
def root : Box := ⟨2596148429267413814265250312093696, 5789234141782132574873516826277910694132748938512735810729627427164298699316973466768642706419764210542411806571041023193205214831951868155850351867700388579471027766445229087835286752623173927153215021437040617264667165696⟩
def references : Fin 1 → Box := ![Part820.root]
def proof : Chunks.Proof 1 := (.split 34 0 (.split 36 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 31 (.run (.close 2)))) (.step 4 (.step 8 (.step 71 (.step 49 (.step 2 (.run (.close 60)))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 48 (.step 71 (.step 74 (.run (.close 2)))))) (.step 48 (.step 71 (.step 67 (.run (.close 2)))))) (.step 66 (.run (.close 2))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 24 (.step 4 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 66 (.run (.close 2)))) (.step 50 (.step 49 (.step 48 (.run (.close 66)))))) (.step 66 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part820.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part821
namespace Part822
def root : Box := ⟨2596148429267413814265250312093696, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015474359593375664654118795703245233521486069996275620156373312820641934473327276192502140371968⟩
def references : Fin 1 → Box := ![Part821.root]
def proof : Chunks.Proof 1 := (.split 43 0 (.split 51 0 (.split 67 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 35 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 61))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 60))))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 57))) (.step 4 (.step 2 (.run (.close 60))))) (.step 48 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 7))))) (.step 48 (.run (.close 2)))) (.step 4 (.step 30 (.step 4 (.step 48 (.step 2 (.run (.close 60)))))))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 35 0 (.split 51 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 30))) (.step 4 (.step 2 (.run (.close 30))))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 3 (.step 30 (.step 2 (.run (.close 9)))))) (.step 48 (.run (.close 2)))) (.step 4 (.step 30 (.step 2 (.run (.close 60)))))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2))))) (.step 48 (.step 58 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part821.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part822
namespace Part823
def root : Box := ⟨2597416079867642043666747015299072, 5789234136395753411692881238169227500374407193496930116368373143801611679107029667258445809290575216008679456763865082380155581827465487773510918587701823954295809725604901439803726139644079070772625225566854437282954347520⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 1 0 (.split 6 0 (.split 12 0 (.split 14 0 (.split 20 0 (.split 24 0 (.split 25 0 (.split 37 0 (.split 60 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 45 0 (.split 26 0 (.split 35 0 (.split 38 0 (.split 39 0 (.split 55 0 (.split 68 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 73 0 (.split 9 0 (.step 8 (.split 29 0 (.split 51 0 (.split 56 0 (.split 62 0 (.split 65 0 (.step 14 (.run (.close 2))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 4 (.step 24 (.step 2 (.run (.close 74)))))) (.step 24 (.step 49 (.run (.close 2))))) (.step 3 (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.run (.close 14))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 50)))) (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part823
namespace Part824
def root : Box := ⟨2596148429267413814265250312093696, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015476396631294668032430793219853104806470640371311692931676088483610751864594173217009747100673⟩
def references : Fin 2 → Box := ![Part822.root, Part823.root]
def proof : Chunks.Proof 2 := (.split 0 0 (.split 4 0 (.split 10 0 (.split 28 0 (.split 30 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 24 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 58 0 (.split 59 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 9 0 (.split 51 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 60))) (.step 48 (.run (.close 2)))) (.step 50 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 24 (.run (.close 2))))) (.step 4 (.step 24 (.step 2 (.run (.close 74)))))) (.step 4 (.step 24 (.step 50 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 4 (.step 48 (.step 2 (.run (.close 60)))))) (.step 50 (.step 48 (.step 58 (.step 74 (.run (.close 2))))))) (.step 50 (.run (.close 2)))) (.step 74 (.step 50 (.step 49 (.step 4 (.step 48 (.run (.close 2))))))))) (.step 2 (.step 7 (.step 74 (.step 48 (.step 4 (.run (.close 66)))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 28 0 (.split 52 0 (.reuse 1) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 11 (.step 18 (.run (.close 74)))))) (.step 74 (.step 50 (.step 49 (.step 4 (.step 48 (.step 2 (.run (.close 60))))))))) (.step 49 (.run (.close 2))))) (.step 2 (.step 7 (.run (.close 14))))) (.step 2 (.step 7 (.run (.close 18)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part822.covered
  · exact Part823.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part824
namespace Part825
def root : Box := ⟨2596148429267413814265250312093696, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015476396631294668032430793221538101473167555358478381374614815400713073391002958997078722741249⟩
def references : Fin 1 → Box := ![Part824.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 1 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 50 0 (.split 51 0 (.split 59 0 (.split 65 0 (.split 67 0 (.split 71 1 (.split 10 0 (.split 14 0 (.step 18 (.step 14 (.run (.close 25)))) (.step 14 (.run (.close 2)))) (.step 7 (.run (.close 14)))) (.step 60 (.step 18 (.run (.close 74))))) (.step 73 (.step 58 (.step 7 (.step 2 (.run (.close 61))))))) (.step 60 (.step 58 (.step 7 (.step 2 (.run (.close 61))))))) (.step 2 (.run (.close 25)))) (.step 73 (.step 58 (.step 7 (.step 2 (.run (.close 61))))))) (.step 2 (.run (.close 25)))) (.step 7 (.step 18 (.run (.close 25))))) (.step 60 (.step 66 (.step 7 (.step 18 (.run (.close 25)))))))) (.step 60 (.step 50 (.step 66 (.step 7 (.step 2 (.step 50 (.run (.close 2))))))))) (.step 66 (.step 7 (.run (.close 14))))) (.step 2 (.step 30 (.step 60 (.step 4 (.run (.close 14))))))) (.step 2 (.run (.close 14)))) (.step 2 (.step 4 (.step 48 (.run (.close 18)))))) (.step 2 (.step 24 (.run (.close 18))))) (.step 2 (.step 24 (.run (.close 18))))) (.step 2 (.step 24 (.run (.close 18))))) (.step 2 (.run (.close 14)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part824.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part825
namespace Part826
def root : Box := ⟨2923003274661808432555798932846380304562177179648, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015476396631294668032430793221538101473167556856517559638790306559490026925193054144409579291649⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 12 0 (.split 17 1 (.split 18 0 (.split 19 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 1 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 50 0 (.split 51 0 (.split 59 0 (.split 67 0 (.split 71 1 (.split 10 0 (.split 14 0 (.step 18 (.step 14 (.run (.close 19)))) (.step 14 (.run (.close 2)))) (.step 7 (.run (.close 14)))) (.step 67 (.step 18 (.run (.close 74))))) (.step 35 (.step 7 (.step 18 (.step 58 (.run (.close 2))))))) (.step 2 (.run (.close 19)))) (.step 35 (.step 7 (.step 18 (.step 58 (.run (.close 2))))))) (.step 2 (.run (.close 19)))) (.step 50 (.step 67 (.step 7 (.step 18 (.step 58 (.run (.close 14)))))))) (.step 50 (.step 7 (.step 18 (.step 74 (.step 58 (.run (.close 14))))))))) (.step 50 (.step 35 (.run (.close 2))))) (.step 50 (.step 8 (.step 7 (.run (.close 14)))))) (.step 2 (.step 30 (.step 74 (.step 4 (.run (.close 14))))))) (.step 2 (.run (.close 14)))) (.step 2 (.step 4 (.run (.close 19))))) (.step 2 (.step 24 (.run (.close 18))))) (.step 14 (.run (.close 25)))) (.step 2 (.step 24 (.run (.close 19))))) (.step 2 (.run (.close 19)))) (.step 8 (.step 14 (.step 20 (.run (.close 2)))))) (.step 2 (.run (.close 14))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part826
namespace Part827
def root : Box := ⟨2596148429267413814265250312093696, 5789239657434395676865714438316775467483492397027246535446502556216320133429076792184354048955104925752266736865777019021307298662540587800026987615542294172604715595816173033697482632212323146801604510656646876508271412225⟩
def references : Fin 2 → Box := ![Part825.root, Part826.root]
def proof : Chunks.Proof 2 := (.split 72 1 (.split 16 1 (.split 17 1 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 1 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 50 0 (.split 51 0 (.split 59 0 (.split 67 0 (.split 64 1 (.split 10 0 (.split 14 0 (.step 18 (.step 14 (.run (.close 20)))) (.step 14 (.run (.close 2)))) (.step 7 (.run (.close 14)))) (.step 74 (.step 66 (.step 18 (.run (.close 7)))))) (.step 30 (.step 7 (.step 18 (.step 58 (.run (.close 2))))))) (.step 2 (.run (.close 20)))) (.step 30 (.step 7 (.step 18 (.run (.close 20)))))) (.step 2 (.run (.close 20)))) (.step 74 (.step 7 (.step 18 (.step 51 (.step 58 (.run (.close 14)))))))) (.step 7 (.step 51 (.run (.close 2)))))) (.step 66 (.step 7 (.step 18 (.run (.close 20)))))) (.step 8 (.step 7 (.step 18 (.run (.close 14)))))) (.step 2 (.step 30 (.step 74 (.step 4 (.run (.close 66))))))) (.step 2 (.run (.close 14)))) (.step 2 (.step 4 (.run (.close 20))))) (.step 2 (.step 24 (.run (.close 18))))) (.step 14 (.run (.close 25)))) (.step 2 (.run (.close 20)))) (.step 2 (.step 24 (.run (.close 20))))) (.step 2 (.run (.close 14))))) (.reuse 1)) (.step 60 (.step 4 (.step 66 (.split 16 1 (.split 17 1 (.split 64 1 (.split 71 1 (.split 5 0 (.step 71 (.split 61 0 (.split 62 0 (.step 69 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 60 (.step 2 (.run (.close 74))))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4))))) (.step 2 (.run (.close 4)))) (.step 74 (.run (.close 2)))) (.step 4 (.run (.close 67)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part825.covered
  · exact Part826.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part827
namespace Part828
def root : Box := ⟨2787593152412476321959378598346295500341248, 11572814729216562008630190618419083460095647405167527049280056522028827653302675335845184517975434740572869054234863179866055622597016698982460254350341370142786996430525906810130589302863686297757868078438016428928951911425⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 71 1 (.split 7 0 (.split 9 0 (.split 16 1 (.split 17 1 (.split 22 1 (.split 18 0 (.split 19 0 (.split 23 0 (.split 73 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 17 (.split 8 0 (.split 29 0 (.split 37 0 (.split 52 0 (.split 65 0 (.split 24 0 (.split 39 0 (.split 46 0 (.split 4 0 (.split 47 0 (.split 49 0 (.split 42 0 (.split 43 0 (.split 50 0 (.split 51 0 (.split 56 0 (.split 57 0 (.split 10 0 (.split 30 0 (.split 67 0 (.step 18 (.split 26 0 (.step 14 (.run (.close 2))) (.step 2 (.run (.close 14))))) (.step 58 (.run (.close 2)))) (.step 4 (.step 48 (.step 8 (.step 18 (.run (.close 14))))))) (.step 8 (.step 7 (.step 18 (.run (.close 14)))))) (.step 2 (.run (.close 14)))) (.step 2 (.run (.close 14)))) (.step 48 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 17)))) (.step 27 (.step 4 (.run (.close 8))))) (.step 4 (.step 49 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 17)))) (.step 2 (.run (.close 14)))) (.step 2 (.run (.close 17)))) (.step 2 (.run (.close 14)))) (.step 2 (.run (.close 17)))) (.step 2 (.run (.close 17)))) (.step 49 (.step 48 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 58)))) (.step 2 (.run (.close 17)))) (.step 2 (.run (.close 8))))) (.step 2 (.run (.close 14)))) (.step 4 (.step 49 (.step 48 (.step 2 (.run (.close 17))))))) (.step 4 (.step 49 (.run (.close 2))))) (.step 2 (.run (.close 14)))) (.step 2 (.run (.close 14)))) (.step 2 (.run (.close 17)))) (.step 2 (.run (.close 17)))) (.step 2 (.run (.close 17)))) (.step 14 (.run (.close 2)))) (.step 14 (.run (.close 2)))) (.step 14 (.run (.close 2)))) (.step 18 (.run (.close 14)))) (.step 2 (.run (.close 11)))) (.step 74 (.step 11 (.step 18 (.run (.close 14))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part828
namespace Part829
def root : Box := ⟨2596148429267413814265250312093696, 11572820244868825110617489347151853331627065208499277305998109710623117098008811319991583839153335959548665565406262646306802426633931044071587063642850500595139975159453899386219073897396830968228613998870245145345577190401⟩
def references : Fin 2 → Box := ![Part827.root, Part828.root]
def proof : Chunks.Proof 2 := (.split 14 1 (.split 74 1 (.split 35 1 (.reuse 0) (.step 4 (.step 50 (.step 66 (.split 22 1 (.split 72 1 (.split 71 1 (.split 5 0 (.step 71 (.split 34 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 66))))) (.step 2 (.run (.close 4)))) (.step 74 (.run (.close 2)))) (.step 74 (.step 4 (.step 66 (.run (.close 2)))))) (.step 4 (.run (.close 2)))))))) (.step 4 (.step 66 (.split 4 0 (.split 10 0 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 64 1 (.split 67 0 (.split 71 1 (.split 65 0 (.split 22 0 (.split 35 0 (.step 2 (.run (.close 74))) (.step 4 (.step 2 (.run (.close 74))))) (.step 60 (.run (.close 2)))) (.step 73 (.step 48 (.step 2 (.run (.close 61)))))) (.step 74 (.run (.close 2)))) (.step 73 (.step 4 (.step 2 (.run (.close 58)))))) (.step 60 (.step 74 (.step 50 (.step 58 (.step 66 (.step 2 (.run (.close 74))))))))) (.step 58 (.run (.close 2)))) (.step 48 (.step 58 (.run (.close 2))))) (.step 60 (.step 2 (.run (.close 30))))) (.step 60 (.step 74 (.step 4 (.step 48 (.step 2 (.step 74 (.step 2 (.run (.close 49)))))))))) (.step 60 (.step 74 (.step 4 (.step 48 (.step 2 (.run (.close 66)))))))) (.step 4 (.step 48 (.step 8 (.step 18 (.step 77 (.run (.close 2)))))))) (.step 60 (.step 73 (.run (.close 2))))) (.step 77 (.step 14 (.run (.close 20))))) (.step 77 (.step 14 (.run (.close 19))))) (.step 8 (.step 7 (.step 14 (.step 18 (.run (.close 17))))))) (.step 2 (.step 7 (.run (.close 77)))))))) (.step 4 (.split 64 1 (.reuse 1) (.step 58 (.step 67 (.run (.close 17)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part827.covered
  · exact Part828.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part829
namespace Part830
def root : Box := ⟨2596148429267413814265250312093696, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482196438455599374046581020685714960812845599911683390042465744111964421452890885334758642511161741068203885685738825075856352740353⟩
def references : Fin 1 → Box := ![Part829.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 42 1 (.split 65 1 (.reuse 0) (.step 63 (.step 24 (.split 43 0 (.split 51 0 (.step 34 (.split 67 0 (.split 16 1 (.split 17 1 (.split 22 1 (.split 14 0 (.split 64 0 (.step 2 (.run (.close 60))) (.step 50 (.step 2 (.run (.close 60))))) (.step 48 (.step 2 (.run (.close 60))))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 7))))) (.step 50 (.step 58 (.step 2 (.run (.close 7)))))) (.step 68 (.run (.close 7))))) (.step 68 (.run (.close 7)))) (.step 30 (.run (.close 27))))))) (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 24 0 (.split 18 0 (.step 60 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 2 (.run (.close 50)))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2))))))) (.step 7 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 30 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 60)))))))) (.step 66 (.step 7 (.step 31 (.split 36 1 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 16 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 49))))) (.step 2 (.run (.close 7)))) (.step 49 (.step 43 (.step 66 (.step 2 (.run (.close 50))))))) (.step 7 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part829.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part830
namespace Part831
def root : Box := ⟨2147483648, 11578468272786246687484214102831214010865934258328309892933923113750589874971121212077576438558118158698350760376646487200849446760416463381142667675502767518223411549261277081277580448360995234921330070596069119386401637378⟩
def references : Fin 2 → Box := ![Part819.root, Part830.root]
def proof : Chunks.Proof 2 := (.split 11 1 (.reuse 0) (.step 2 (.split 10 1 (.split 30 1 (.split 43 1 (.split 51 1 (.split 67 1 (.reuse 1) (.step 48 (.step 7 (.step 3 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 2 (.run (.close 61))) (.step 30 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 7)))))))) (.step 48 (.step 7 (.step 3 (.split 67 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 2 (.run (.close 61))) (.step 30 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 68 (.step 30 (.step 2 (.run (.close 7))))))))))) (.step 48 (.step 68 (.step 3 (.step 30 (.step 68 (.run (.close 2)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.split 16 0 (.step 2 (.run (.close 7))) (.step 50 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 50)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 8 (.run (.close 14))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part819.covered
  · exact Part830.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part831
namespace Part832
def root : Box := ⟨2251801961168896, 5789234141782132574873516826277910694132748938512735810729627427164298699316973466768642706419761502857163641712777367603280994026367037319114698554230378697335029983218968330691265467628305075648640009746417852890238419968⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 65 0 (.split 14 0 (.split 63 1 (.split 64 1 (.step 2 (.split 16 0 (.step 2 (.run (.close 60))) (.step 18 (.run (.close 8))))) (.split 16 0 (.step 2 (.step 50 (.step 2 (.run (.close 60))))) (.step 74 (.step 50 (.step 2 (.run (.close 60))))))) (.split 16 0 (.split 17 0 (.step 2 (.step 74 (.step 2 (.run (.close 60))))) (.step 74 (.step 2 (.run (.close 11))))) (.step 74 (.step 50 (.step 2 (.run (.close 11))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 35 0 (.step 2 (.run (.close 60))) (.step 4 (.step 2 (.run (.close 60))))) (.step 11 (.run (.close 2)))) (.step 74 (.step 50 (.step 49 (.step 2 (.run (.close 60))))))) (.step 49 (.run (.close 2))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 9))) (.step 24 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 60))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 48 (.step 58 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part832
namespace Part833
def root : Box := ⟨2251801961168896, 5789234141782132574873516826277910694132748938512735810729627427164298699316973466768642706419764210542411806571041023190965470089774063945292909587131944301349382269210579552935297651659380757898839442349257117268884587520⟩
def references : Fin 1 → Box := ![Part832.root]
def proof : Chunks.Proof 1 := (.split 36 0 (.split 42 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.run (.close 2)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 4 (.step 48 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 11 (.run (.close 2)))) (.step 60 (.step 74 (.step 50 (.step 48 (.step 2 (.run (.close 74)))))))) (.step 60 (.step 74 (.step 49 (.step 48 (.step 2 (.step 50 (.run (.close 66)))))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 31 (.run (.close 2)))) (.step 4 (.step 8 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 48 (.step 11 (.run (.close 2))))) (.step 50 (.step 48 (.step 11 (.run (.close 2)))))) (.step 48 (.step 66 (.step 11 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part832.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part833
namespace Part834
def root : Box := ⟨2251801961168896, 5789234141782132574878415709588568036569696788914137450334149658946920565278206882319259026786080760788026218379849905402888967421676992076992329692204115654056070487823521865271099128756458505999625642016480005536739230720⟩
def references : Fin 1 → Box := ![Part833.root]
def proof : Chunks.Proof 1 := (.split 67 0 (.split 34 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 6 0 (.split 12 0 (.split 14 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 54 0 (.split 24 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 25 0 (.split 9 0 (.step 24 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 24 (.step 4 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 48 (.step 11 (.step 2 (.run (.close 60)))))) (.step 50 (.step 48 (.step 66 (.step 11 (.run (.close 2))))))) (.step 48 (.step 66 (.step 11 (.step 2 (.run (.close 60)))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 9))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 11)))) (.step 48 (.run (.close 11)))) (.step 48 (.run (.close 11)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part833.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part834
namespace Part835
def root : Box := ⟨2037035976334486086268445688409378161051468393665936250636140449354381299765588508144566272, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015476396629351999140205064148933642899647121464669286092623947663017074220920133522484148306944⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 63 1 (.split 64 1 (.split 71 1 (.split 52 0 (.split 6 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 26 0 (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 63 0 (.step 8 (.run (.close 2))) (.step 50 (.step 4 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 4 (.step 24 (.step 2 (.run (.close 74)))))) (.step 4 (.step 24 (.step 50 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 4 (.step 48 (.step 2 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 11)))) (.step 50 (.run (.close 2)))) (.step 74 (.step 50 (.step 49 (.step 4 (.run (.close 11)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part835
namespace Part836
def root : Box := ⟨1267650600228231653298664374272, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015476396631294668032430793219853104806470640371311692931676087185536537230887267209186060010496⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 63 1 (.split 64 1 (.split 71 1 (.split 52 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 37 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 26 0 (.split 35 0 (.split 39 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 58 0 (.split 59 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 54 0 (.split 63 0 (.step 8 (.run (.close 2))) (.step 49 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 4 (.step 24 (.step 2 (.run (.close 74)))))) (.step 24 (.step 49 (.run (.close 2))))) (.step 3 (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.run (.close 2))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 4 (.step 48 (.step 8 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 48 (.run (.close 11)))) (.step 74 (.step 50 (.step 49 (.step 4 (.run (.close 11))))))) (.step 49 (.run (.close 2))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part836
namespace Part837
def root : Box := ⟨2251801961168896, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015476396631294668032430793219853104806470640371311692931676087185536537230887267210285571638273⟩
def references : Fin 3 → Box := ![Part834.root, Part835.root, Part836.root]
def proof : Chunks.Proof 3 := (.split 0 0 (.split 4 0 (.split 10 0 (.split 28 0 (.split 30 0 (.split 43 0 (.split 51 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 9))) (.step 4 (.step 2 (.run (.close 60))))) (.step 48 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 7))))) (.step 48 (.run (.close 2)))) (.step 4 (.step 30 (.step 4 (.step 48 (.step 2 (.run (.close 60)))))))) (.step 48 (.run (.close 11)))) (.step 48 (.run (.close 11)))) (.step 48 (.run (.close 11))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 14 0 (.split 35 0 (.split 51 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 64 0 (.step 2 (.run (.close 30))) (.step 4 (.step 2 (.run (.close 30))))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 3 (.step 30 (.step 2 (.run (.close 9)))))) (.step 48 (.run (.close 2)))) (.step 4 (.step 30 (.step 2 (.run (.close 60)))))) (.step 48 (.run (.close 11)))) (.step 48 (.run (.close 11)))) (.step 48 (.run (.close 11))))) (.reuse 1)) (.step 2 (.step 11 (.step 7 (.step 74 (.run (.close 31))))))) (.reuse 2)) (.step 2 (.step 11 (.run (.close 7))))) (.step 2 (.step 11 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part834.covered
  · exact Part835.covered
  · exact Part836.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part837
namespace Part838
def root : Box := ⟨2251801961168896, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920295102981943678903080883467685376482015476396631294668032430793221538101473167556856517559638790305261415812291486148137685403829249⟩
def references : Fin 1 → Box := ![Part837.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.step 11 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 73 0 (.split 25 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 38 0 (.step 11 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))))) (.step 11 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 73 0 (.split 25 0 (.split 10 0 (.split 16 0 (.split 22 0 (.split 30 0 (.split 38 0 (.step 11 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))))) (.step 11 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 73 0 (.split 25 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.step 11 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7)))) (.step 50 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part837.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part838
namespace Part839
def root : Box := ⟨2251801961168896, 5789239657434395676865714438316775467483492397027246535446502556216320133429076792184354048955104925752266736865777021314805914652612099410847882917629234969169704764097296771286322019135197937212197946968293979909782504449⟩
def references : Fin 1 → Box := ![Part838.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 72 1 (.reuse 0) (.step 4 (.step 11 (.split 63 1 (.split 64 1 (.split 71 1 (.split 61 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 16 0 (.split 62 0 (.step 69 (.step 48 (.split 17 0 (.step 2 (.run (.close 60))) (.step 60 (.step 2 (.run (.close 74))))))) (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 74 (.run (.close 2)))) (.step 4 (.run (.close 67)))) (.step 4 (.run (.close 66))))))) (.step 4 (.step 50 (.step 11 (.split 72 1 (.split 63 1 (.split 71 1 (.split 6 0 (.split 61 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 16 0 (.split 62 0 (.split 65 0 (.split 69 0 (.step 47 (.split 12 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.step 2 (.run (.close 60))) (.step 60 (.step 2 (.run (.close 74))))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 9))))) (.step 2 (.run (.close 9)))) (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 74 (.run (.close 2)))) (.step 4 (.run (.close 66)))) (.step 9 (.step 4 (.run (.close 75)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part838.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part839
namespace Part840
def root : Box := ⟨2251801961168896, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482196438455599374046578672140892442237439906220529158424869924151293867635785528508887121201172833290506046407652656807157538227201⟩
def references : Fin 1 → Box := ![Part839.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 65 1 (.split 14 1 (.split 74 1 (.reuse 0) (.step 11 (.split 4 0 (.split 8 0 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 67 0 (.step 18 (.step 11 (.run (.close 2)))) (.step 4 (.run (.close 11)))) (.step 48 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 60 (.step 2 (.run (.close 30))))) (.step 4 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))))) (.step 11 (.split 4 0 (.split 8 0 (.split 10 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 51 0 (.split 67 0 (.step 18 (.step 11 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 48 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 4 (.run (.close 11)))) (.step 2 (.run (.close 8)))) (.step 2 (.run (.close 8)))))) (.step 63 (.step 8 (.step 24 (.split 43 0 (.split 51 0 (.split 10 0 (.split 30 0 (.split 67 0 (.split 16 0 (.step 2 (.run (.close 60))) (.step 58 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 7))))) (.step 30 (.run (.close 27)))))))) (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 24 0 (.split 18 0 (.step 60 (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 2 (.run (.close 50)))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part839.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part840
namespace Part841
def root : Box := ⟨2251801961168896, 11572820244868825110622388235134449866509140962789238669839730259096408307344552590104568191357535209856866470556423465177886227996368091349208702828884151235738627207931726243198975914911878663618390503922154644369650484225⟩
def references : Fin 1 → Box := ![Part840.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 67 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 7 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 30 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 60)))))))) (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 16 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 49))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.step 2 (.run (.close 60))))) (.step 4 (.step 2 (.run (.close 60)))))))) (.step 48 (.step 7 (.step 3 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 2 (.run (.close 61))) (.step 30 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 7)))))))) (.step 48 (.step 7 (.step 3 (.split 67 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 2 (.run (.close 61))) (.step 30 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 68 (.step 30 (.step 2 (.run (.close 7))))))))))) (.step 48 (.step 68 (.step 3 (.step 30 (.step 68 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part840.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part841
namespace Part842
def root : Box := ⟨2147485696, 5789239657434395676860815555006118125046544546625844895841980324433694915515860890984462835079766154350999640355934576822634647469087570937346235645124559398022092964198487907784954334689301907923513620234900593513750071296⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 17 0 (.split 22 0 (.split 65 0 (.split 7 0 (.split 13 0 (.split 14 0 (.split 34 0 (.split 35 1 (.split 72 1 (.split 36 0 (.step 2 (.step 71 (.split 73 0 (.split 19 0 (.step 66 (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 4)))))) (.step 3 (.step 2 (.step 74 (.run (.close 2)))))) (.step 4 (.step 75 (.run (.close 2))))) (.step 4 (.step 38 (.run (.close 2))))) (.step 3 (.split 63 1 (.split 64 1 (.split 71 1 (.step 2 (.step 4 (.step 31 (.run (.close 2))))) (.step 48 (.step 40 (.step 74 (.run (.close 2)))))) (.step 74 (.step 50 (.step 2 (.step 60 (.step 2 (.run (.close 74)))))))) (.step 48 (.step 40 (.run (.close 66))))))) (.step 4 (.step 3 (.step 2 (.step 74 (.step 2 (.run (.close 4)))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 71 (.step 3 (.step 2 (.run (.close 57)))))) (.step 4 (.step 3 (.split 63 1 (.step 2 (.step 48 (.step 40 (.step 74 (.step 2 (.run (.close 4))))))) (.step 74 (.step 2 (.step 50 (.step 2 (.run (.close 4)))))))))) (.step 4 (.step 3 (.split 22 0 (.split 63 1 (.step 2 (.step 48 (.step 40 (.run (.close 74))))) (.step 74 (.step 2 (.step 74 (.step 2 (.run (.close 4))))))) (.step 24 (.split 63 1 (.split 64 1 (.step 2 (.step 61 (.step 60 (.run (.close 2))))) (.step 60 (.step 2 (.run (.close 74))))) (.step 60 (.step 2 (.run (.close 74))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part842
namespace Part843
def root : Box := ⟨2147485696, 11572820244868825110617489347151853331627065208499277305998109710623117098008811319991583839153338667233913730264523953351904128864110181217168485338724690514920422458877886832285707165288572668081860038168911580997276928001⟩
def references : Fin 1 → Box := ![Part842.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 14 1 (.split 74 1 (.split 0 0 (.split 2 0 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.reuse 0) (.step 4 (.step 3 (.split 17 0 (.split 22 0 (.split 63 1 (.step 2 (.step 48 (.step 40 (.run (.close 67))))) (.step 74 (.step 2 (.step 50 (.step 2 (.run (.close 4))))))) (.split 63 1 (.split 64 1 (.step 2 (.step 4 (.run (.close 2)))) (.step 60 (.step 2 (.run (.close 74))))) (.step 60 (.step 74 (.step 2 (.run (.close 4))))))) (.step 24 (.step 8 (.step 18 (.split 63 1 (.split 64 1 (.split 71 1 (.split 9 0 (.split 31 0 (.step 4 (.run (.close 2))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 4)))) (.step 61 (.run (.close 74)))) (.step 74 (.step 4 (.run (.close 2))))) (.step 74 (.step 4 (.run (.close 18)))))))))))) (.step 71 (.step 3 (.run (.close 2))))) (.step 71 (.step 3 (.run (.close 2))))) (.step 71 (.step 3 (.run (.close 2))))) (.step 4 (.step 3 (.step 2 (.run (.close 74)))))) (.step 4 (.step 3 (.step 2 (.run (.close 74)))))) (.step 2 (.run (.close 4)))) (.step 2 (.step 4 (.run (.close 3))))) (.step 4 (.step 5 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 60))))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 66 (.run (.close 2))))))) (.step 4 (.step 5 (.split 74 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 4))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 17)))) (.step 74 (.run (.close 2)))) (.step 67 (.run (.close 2)))) (.step 74 (.step 49 (.step 2 (.run (.close 66)))))) (.step 77 (.run (.close 2))))))) (.step 3 (.step 31 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part842.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part843
namespace Part844
def root : Box := ⟨2147485696, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482196438455599374046581020685714960812845599911683390042465744111964421452890885334758642511161739770129671052031917943232270436353⟩
def references : Fin 1 → Box := ![Part843.root]
def proof : Chunks.Proof 1 := (.split 65 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 3 (.step 31 (.step 2 (.run (.close 75)))))) (.step 3 (.step 31 (.step 2 (.run (.close 37)))))) (.step 4 (.step 24 (.step 8 (.step 3 (.split 14 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 9 0 (.split 26 0 (.split 27 0 (.split 31 0 (.step 18 (.run (.close 25))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 18)))) (.step 74 (.run (.close 2)))) (.step 60 (.step 74 (.step 4 (.run (.close 18)))))) (.step 60 (.step 74 (.step 4 (.step 49 (.run (.close 18))))))) (.step 4 (.run (.close 17))))))))) (.step 4 (.step 24 (.step 8 (.split 14 1 (.split 22 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 9 0 (.split 27 0 (.split 31 0 (.step 18 (.run (.close 4))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 18)))) (.step 4 (.run (.close 77)))) (.step 61 (.run (.close 74)))) (.step 74 (.step 4 (.step 2 (.step 60 (.run (.close 18))))))) (.step 74 (.step 4 (.step 49 (.step 2 (.run (.close 66))))))) (.step 18 (.run (.close 20)))) (.step 4 (.run (.close 17)))))))) (.step 4 (.step 24 (.step 8 (.step 3 (.split 14 1 (.split 17 1 (.split 22 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 74 1 (.split 9 0 (.split 27 0 (.split 31 0 (.step 18 (.run (.close 4))) (.step 2 (.run (.close 40)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 18)))) (.step 4 (.run (.close 77)))) (.step 74 (.run (.close 2)))) (.step 58 (.run (.close 67)))) (.step 4 (.step 50 (.step 49 (.step 58 (.run (.close 66))))))) (.step 18 (.run (.close 19)))) (.step 18 (.run (.close 19)))) (.step 4 (.run (.close 17))))))))) (.step 71 (.run (.close 2))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part843.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part844
namespace Part845
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 5789234141787392710779964083095809026452576917579687790136972832806422198133258100122831001114441271100587511814268380880165355724166111113514378569341434055265266311304138839762752909872496054797852573392520023650566407169⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 51 0 (.split 67 0 (.split 65 0 (.split 14 0 (.split 63 1 (.split 64 1 (.step 2 (.split 16 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 74))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 74))))) (.step 58 (.run (.close 12))))) (.step 71 (.split 16 0 (.split 14 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 8 0 (.split 14 0 (.split 25 0 (.split 26 0 (.step 44 (.split 35 0 (.step 2 (.run (.close 61))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 4 (.step 30 (.step 4 (.step 73 (.run (.close 2))))))) (.step 2 (.run (.close 73)))) (.step 27 (.step 61 (.step 4 (.step 58 (.run (.close 2))))))) (.step 58 (.step 42 (.step 2 (.run (.close 71)))))) (.step 58 (.step 40 (.step 2 (.run (.close 71))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 8 0 (.split 14 0 (.split 25 0 (.split 26 0 (.step 36 (.split 35 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 4 (.step 30 (.step 4 (.step 73 (.run (.close 2))))))) (.step 2 (.run (.close 11)))) (.step 61 (.run (.close 2)))) (.step 27 (.step 58 (.step 42 (.step 63 (.step 2 (.run (.close 71)))))))) (.step 58 (.step 40 (.step 68 (.step 2 (.run (.close 61))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part845
namespace Part846
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11572814729221822144531738991930886890596149729051718560688579987213219162712992627930060791315444974591107155214332420056304951408921492849629375869733179261850158014466367077735479194238267365837445202548968754191159788545⟩
def references : Fin 1 → Box := ![Part845.root]
def proof : Chunks.Proof 1 := (.split 14 1 (.split 74 1 (.split 43 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 12 0 (.split 14 0 (.split 35 0 (.split 51 0 (.split 22 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.run (.close 2)))) (.step 30 (.step 2 (.run (.close 27))))) (.step 30 (.run (.close 2)))) (.step 4 (.step 3 (.run (.close 2))))) (.step 4 (.step 30 (.run (.close 2))))) (.step 2 (.run (.close 27)))) (.step 27 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 9))))) (.step 27 (.step 2 (.run (.close 71)))))) (.step 44 (.step 69 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 73))) (.step 61 (.step 2 (.run (.close 73))))) (.step 73 (.run (.close 18)))) (.step 73 (.run (.close 2)))) (.step 73 (.run (.close 2)))) (.step 27 (.run (.close 2))))))) (.step 34 (.split 64 1 (.split 71 1 (.split 16 0 (.split 17 0 (.split 43 0 (.split 51 0 (.split 74 1 (.split 22 0 (.step 2 (.run (.close 73))) (.step 58 (.run (.close 2)))) (.step 69 (.run (.close 2)))) (.step 61 (.step 4 (.step 2 (.run (.close 73)))))) (.step 27 (.run (.close 2)))) (.step 27 (.step 58 (.run (.close 2))))) (.step 27 (.step 58 (.step 2 (.run (.close 73)))))) (.step 71 (.step 2 (.run (.close 74))))) (.step 74 (.step 42 (.step 71 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part845.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part846
namespace Part847
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11572814729221822144531738991930886890596149729051718560688579987213219162712992627930060791315447682276355320072596075643989427472328519475807586902634744865864510300457978299979511378269343048087644635151808018569805956097⟩
def references : Fin 1 → Box := ![Part846.root]
def proof : Chunks.Proof 1 := (.split 36 0 (.split 42 0 (.reuse 0) (.step 44 (.split 14 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 57))))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 60))))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 69)))) (.step 58 (.run (.close 69)))) (.step 58 (.run (.close 2)))))) (.split 14 1 (.split 74 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 42 0 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 57))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 36)))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 60))))) (.step 71 (.run (.close 2)))) (.split 16 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 17 0 (.split 22 0 (.step 26 (.split 35 0 (.step 2 (.run (.close 30))) (.step 60 (.run (.close 2))))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 2 (.run (.close 60)))) (.step 60 (.run (.close 2))))) (.step 60 (.step 58 (.run (.close 2))))) (.step 60 (.step 58 (.step 2 (.run (.close 57)))))) (.step 60 (.step 58 (.step 2 (.step 74 (.run (.close 2))))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part846.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part847
namespace Part848
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11572814729221822144531738991930886890596149729051718560688579987213219162712992627930060791315447682276355320072596075646229172214506323686365029183203189143986155797692627834879500479233134919267805580532685511841413071873⟩
def references : Fin 1 → Box := ![Part847.root]
def proof : Chunks.Proof 1 := (.split 34 0 (.reuse 0) (.split 74 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 36 0 (.split 42 0 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 57))))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.run (.close 34)))) (.step 71 (.run (.close 2)))) (.split 16 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 17 0 (.split 22 0 (.step 26 (.split 35 0 (.step 2 (.run (.close 30))) (.step 60 (.run (.close 2))))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 2 (.run (.close 60)))) (.step 60 (.run (.close 2))))) (.split 16 0 (.split 74 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 34 (.step 36 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 60 (.run (.close 2)))) (.step 76 (.run (.close 4)))) (.step 60 (.step 4 (.run (.close 2)))))) (.step 60 (.step 58 (.step 2 (.run (.close 57)))))) (.step 60 (.step 58 (.step 2 (.step 50 (.step 2 (.run (.close 57)))))))) (.step 58 (.step 40 (.run (.close 2))))) (.step 58 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part847.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part848
namespace Part849
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383328783419245662771988002322251776, 11572814729221822144531738991930886890596149729051718560688579987213219162712992627930060791315447682276355320072596075646229172214508360724284032561515186660594027082677198209915573254535910582236622971799582535249508172801⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 71 (.split 14 1 (.split 74 1 (.split 12 0 (.split 14 0 (.split 30 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 17 0 (.split 22 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 60))) (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 8 (.step 3 (.split 17 0 (.step 2 (.run (.close 60))) (.step 18 (.run (.close 73)))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.run (.close 2))))))) (.step 71 (.run (.close 2)))) (.step 3 (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 4 (.step 71 (.step 30 (.step 2 (.run (.close 73))))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 58 (.run (.close 2))))) (.step 58 (.step 3 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part849
namespace Part850
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11572820244874085246519037725331033513955073241053387370038031201173281370334405421058974058304307397306628797639544345771148302234902276896377025230771921246349089715536539578491043576727969716093111866148038441308234187777⟩
def references : Fin 2 → Box := ![Part848.root, Part849.root]
def proof : Chunks.Proof 2 := (.split 72 1 (.split 65 1 (.split 4 0 (.split 10 0 (.split 28 0 (.split 30 0 (.reuse 0) (.step 71 (.split 14 1 (.split 74 1 (.split 12 0 (.split 14 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 17 0 (.split 22 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 60))) (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 8 (.step 3 (.split 9 0 (.step 35 (.run (.close 2))) (.step 2 (.run (.close 60)))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.run (.close 2))))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 4)))) (.step 73 (.step 4 (.run (.close 18))))) (.step 27 (.step 58 (.step 2 (.step 73 (.run (.close 2))))))))) (.step 2 (.step 3 (.step 58 (.run (.close 40)))))) (.reuse 1)) (.step 2 (.step 71 (.step 7 (.run (.close 58)))))) (.step 71 (.split 4 0 (.split 10 0 (.split 30 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 69 (.split 34 0 (.split 36 0 (.split 31 0 (.split 59 0 (.split 1 0 (.split 6 0 (.split 12 0 (.step 30 (.split 14 0 (.split 15 0 (.step 68 (.run (.close 2))) (.step 2 (.run (.close 73)))) (.step 73 (.step 2 (.run (.close 61)))))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 5)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 58)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2))))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 30 (.run (.close 55)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 7)))))) (.step 4 (.step 40 (.step 71 (.step 2 (.run (.close 60)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part848.covered
  · exact Part849.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part850
namespace Part851
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11572820244874085246519037725331033513955073241053387370038031201173281370334405421058974058304307397306628797639544348064646918224973788507197920532858862044599075550514579799824248033434160962253510164049189459177820390401⟩
def references : Fin 1 → Box := ![Part850.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 35 1 (.reuse 0) (.step 4 (.step 40 (.step 71 (.step 2 (.run (.close 60))))))) (.step 73 (.step 18 (.split 14 1 (.split 4 0 (.step 44 (.split 9 0 (.step 8 (.split 10 0 (.split 14 0 (.step 2 (.run (.close 60))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 60 (.step 73 (.run (.close 2)))))))) (.step 18 (.split 14 1 (.split 22 1 (.split 65 1 (.split 74 1 (.split 4 0 (.step 36 (.step 8 (.split 10 0 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 60))) (.step 35 (.step 2 (.run (.close 60))))) (.step 58 (.run (.close 2)))) (.step 3 (.step 18 (.run (.close 73))))))) (.step 2 (.run (.close 7)))) (.step 73 (.run (.close 77)))) (.step 30 (.step 73 (.step 58 (.step 43 (.run (.close 2))))))) (.step 60 (.step 73 (.run (.close 2))))) (.step 61 (.step 58 (.step 8 (.step 18 (.step 73 (.run (.close 7))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part850.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part851
namespace Part852
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11572820244874085246519037725331033513955073241053387370038031201173281370334405421058974058304310104991876962497808003652331394288380815133376131565760427648613427836506191023529781854796139562707394429368311743212399100929⟩
def references : Fin 1 → Box := ![Part851.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 16 1 (.reuse 0) (.step 18 (.split 14 1 (.split 17 1 (.split 22 1 (.split 65 1 (.split 74 1 (.split 4 0 (.split 9 0 (.step 8 (.split 10 0 (.split 12 0 (.split 14 0 (.split 17 0 (.split 19 0 (.split 22 0 (.split 23 0 (.step 35 (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 60)))) (.step 60 (.run (.close 2)))) (.step 2 (.run (.close 73)))) (.step 35 (.step 18 (.run (.close 73))))) (.step 58 (.step 2 (.run (.close 73))))) (.step 2 (.run (.close 4)))) (.step 35 (.step 18 (.step 73 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 73 (.run (.close 77)))) (.step 73 (.step 50 (.step 58 (.run (.close 68)))))) (.step 60 (.step 73 (.run (.close 2))))) (.step 8 (.step 18 (.run (.close 19))))) (.step 58 (.step 35 (.step 8 (.step 18 (.step 73 (.run (.close 19)))))))))) (.step 43 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 44 (.run (.close 40))) (.step 60 (.step 76 (.run (.close 2))))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 60 (.run (.close 2)))) (.step 60 (.step 76 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 43 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 36 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 60 (.step 4 (.run (.close 36))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part851.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part852
namespace Part853
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11572820244874085246523936608641690856392021091454789009642553432955906588247621322258865272179648876393144059007650448146742406214081110781458886632747279050509279088781681466870104359510070327376274826639424811721479422977⟩
def references : Fin 1 → Box := ![Part852.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 51 1 (.split 67 1 (.split 34 1 (.reuse 0) (.step 43 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 34 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 60 (.step 4 (.run (.close 34))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7)))))) (.step 76 (.step 68 (.step 3 (.split 4 0 (.step 44 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 29 0 (.split 44 0 (.step 73 (.run (.close 55))) (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 76)))) (.step 73 (.run (.close 2)))) (.step 73 (.run (.close 2)))) (.step 73 (.step 76 (.run (.close 3))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))))))) (.step 68 (.step 3 (.step 31 (.split 67 1 (.split 4 0 (.step 36 (.split 10 0 (.split 16 0 (.split 22 0 (.step 2 (.run (.close 9))) (.step 30 (.step 2 (.run (.close 60))))) (.step 30 (.step 73 (.run (.close 2))))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 76 (.step 3 (.run (.close 2)))))))))) (.step 10 (.step 68 (.step 3 (.step 30 (.split 9 0 (.step 10 (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 30)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part852.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part853
namespace Part854
def root : Box := ⟨2147483648, 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705624978129482813392851479365895332994063430111232304948708892959186898679214393313341538538044262402⟩
def references : Fin 4 → Box := ![Part831.root, Part841.root, Part844.root, Part853.root]
def proof : Chunks.Proof 4 := (.split 70 1 (.split 1 1 (.split 5 1 (.reuse 0) (.step 2 (.split 10 1 (.split 30 1 (.reuse 1) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.run (.close 2))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 8 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))) (.step 2 (.step 3 (.reuse 2)))) (.step 2 (.split 10 1 (.split 30 1 (.reuse 3) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 30 (.step 73 (.step 2 (.run (.close 60))))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part831.covered
  · exact Part841.covered
  · exact Part844.covered
  · exact Part853.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part854
namespace Part855
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920292327604564309923363041397911309179642440127602174277160500012410046729033158705972744394412315912213259694031315798753360917562369⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 51 0 (.split 67 0 (.split 65 0 (.split 14 0 (.split 63 1 (.split 64 1 (.step 2 (.split 16 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 74))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 50 (.step 2 (.run (.close 74))))) (.step 58 (.run (.close 12))))) (.step 71 (.split 16 0 (.split 14 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 8 0 (.split 14 0 (.split 25 0 (.split 26 0 (.step 44 (.split 35 0 (.step 2 (.run (.close 61))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 4 (.step 30 (.step 4 (.step 73 (.step 2 (.run (.close 61)))))))) (.step 2 (.run (.close 11)))) (.step 27 (.step 61 (.step 4 (.step 58 (.run (.close 2))))))) (.step 42 (.run (.close 2)))) (.step 58 (.step 40 (.step 2 (.run (.close 71))))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 8 0 (.split 14 0 (.split 25 0 (.split 26 0 (.step 36 (.split 35 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 4 (.step 30 (.step 4 (.step 42 (.step 35 (.step 2 (.run (.close 60))))))))) (.step 2 (.run (.close 11)))) (.step 61 (.run (.close 2)))) (.step 42 (.run (.close 2)))) (.step 58 (.step 40 (.step 68 (.step 2 (.run (.close 61))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part855
namespace Part856
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493331308054829566763105437087448775327195509338289274460891757616631620736320934210717120696681683524299286660472247483901510943745⟩
def references : Fin 1 → Box := ![Part855.root]
def proof : Chunks.Proof 1 := (.split 14 1 (.split 74 1 (.split 43 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 12 0 (.split 14 0 (.split 35 0 (.split 51 0 (.split 22 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.run (.close 2)))) (.step 30 (.step 2 (.run (.close 27))))) (.step 30 (.run (.close 2)))) (.step 4 (.step 3 (.run (.close 2))))) (.step 4 (.step 30 (.run (.close 2))))) (.step 2 (.run (.close 27)))) (.step 27 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 9))))) (.step 27 (.step 2 (.run (.close 71)))))) (.step 42 (.step 44 (.split 43 0 (.split 51 0 (.split 67 0 (.split 35 0 (.split 65 0 (.split 72 0 (.step 2 (.step 61 (.step 2 (.run (.close 74))))) (.step 73 (.step 2 (.run (.close 74))))) (.step 5 (.run (.close 71)))) (.step 27 (.step 4 (.step 5 (.step 74 (.step 58 (.run (.close 2)))))))) (.step 73 (.step 2 (.run (.close 71))))) (.step 61 (.step 73 (.step 4 (.step 2 (.run (.close 71))))))) (.step 27 (.run (.close 2))))))) (.step 42 (.step 34 (.split 71 1 (.split 16 0 (.split 17 0 (.split 43 0 (.split 51 0 (.split 74 1 (.split 22 0 (.step 2 (.run (.close 73))) (.step 58 (.run (.close 2)))) (.step 42 (.step 44 (.step 2 (.run (.close 73)))))) (.step 61 (.step 4 (.step 2 (.run (.close 73)))))) (.step 27 (.run (.close 2)))) (.step 27 (.step 58 (.run (.close 2))))) (.step 27 (.step 58 (.step 2 (.run (.close 73)))))) (.step 27 (.step 61 (.step 58 (.step 42 (.step 2 (.step 74 (.run (.close 2))))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part855.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part856
namespace Part857
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493334015740077731621369092675133251390602535964467485493793323220645973022312545432961152880712759206549486093075086748280157111297⟩
def references : Fin 1 → Box := ![Part856.root]
def proof : Chunks.Proof 1 := (.split 36 0 (.split 42 0 (.reuse 0) (.step 44 (.split 14 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 57))))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 60))))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 50 (.run (.close 2)))) (.step 50 (.step 58 (.run (.close 2))))) (.step 58 (.run (.close 2)))))) (.split 14 1 (.split 74 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 42 0 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 57))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 36)))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 60))))) (.step 71 (.run (.close 2)))) (.split 16 0 (.split 14 0 (.split 17 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 44 (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30)))))) (.step 50 (.step 58 (.run (.close 2))))) (.step 50 (.run (.close 2)))) (.step 50 (.step 58 (.step 2 (.run (.close 57)))))) (.step 58 (.run (.close 2)))) (.step 58 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part856.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part857
namespace Part858
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493334015740077731621369092677372996132780340175024927774361767498767618519547194967861141981676551077729647038455964241551764227073⟩
def references : Fin 1 → Box := ![Part857.root]
def proof : Chunks.Proof 1 := (.split 34 0 (.reuse 0) (.split 74 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 36 0 (.split 42 0 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 57))))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.run (.close 34)))) (.step 71 (.run (.close 2)))) (.split 16 0 (.split 74 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 34 (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30)))))) (.split 16 0 (.split 74 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 34 (.step 36 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 50 (.run (.close 2)))))) (.step 50 (.step 58 (.step 2 (.run (.close 57)))))) (.step 50 (.run (.close 2)))) (.step 50 (.step 58 (.step 2 (.step 63 (.step 2 (.run (.close 60)))))))) (.step 58 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part857.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part858
namespace Part859
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215645707102161509329447423024562176, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493334015740077731621369092677372996132782377212943931152673765015375489804531765342897214756979326740698464429722861264959859328001⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 71 (.split 14 1 (.split 74 1 (.split 12 0 (.split 14 0 (.split 30 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 17 0 (.split 22 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 60))) (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 8 (.step 3 (.split 17 0 (.step 2 (.run (.close 60))) (.step 50 (.run (.close 2)))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.run (.close 2))))))) (.step 71 (.run (.close 2)))) (.step 3 (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 4 (.step 71 (.step 30 (.step 2 (.run (.close 73))))))) (.step 2 (.run (.close 7)))) (.step 27 (.step 73 (.step 58 (.run (.close 2)))))) (.step 27 (.step 58 (.step 42 (.step 2 (.step 73 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part859
namespace Part860
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 11572814729216562008630190623095585093158397504274727945122855130044386873232449264688856848822191786961763375403423811466361309506112102216304604238818998650063938314742490534292762085749369287243375738607724438919893222401⟩
def references : Fin 2 → Box := ![Part858.root, Part859.root]
def proof : Chunks.Proof 2 := (.split 65 1 (.split 4 0 (.split 10 0 (.split 28 0 (.split 30 0 (.reuse 0) (.step 71 (.split 14 1 (.split 74 1 (.split 12 0 (.split 14 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 17 0 (.split 22 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 60))) (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 8 (.step 3 (.split 9 0 (.step 35 (.run (.close 2))) (.step 2 (.run (.close 7)))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.run (.close 2))))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 4)))) (.step 73 (.step 58 (.run (.close 2))))) (.step 58 (.run (.close 42)))))) (.step 2 (.step 3 (.step 74 (.step 50 (.step 4 (.run (.close 49)))))))) (.reuse 1)) (.step 2 (.step 50 (.step 58 (.step 7 (.run (.close 58))))))) (.step 71 (.split 4 0 (.split 10 0 (.split 30 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 59 0 (.split 67 0 (.split 6 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 31 0 (.split 63 0 (.step 30 (.split 8 0 (.split 14 0 (.step 32 (.step 2 (.run (.close 60)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 8))))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 63)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 55)))) (.step 2 (.run (.close 55)))) (.step 30 (.run (.close 55)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 2 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part858.covered
  · exact Part859.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part860
namespace Part861
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482193730770351209188317365095790742143247804995857819124017440399380538272369146932805889535877577120715351621972468188888171545601⟩
def references : Fin 1 → Box := ![Part860.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 35 1 (.split 72 1 (.reuse 0) (.step 4 (.step 40 (.step 71 (.step 2 (.run (.close 60))))))) (.step 4 (.step 40 (.step 71 (.step 2 (.run (.close 60))))))) (.step 18 (.split 14 1 (.split 65 1 (.split 4 0 (.step 44 (.split 9 0 (.step 8 (.split 10 0 (.split 14 0 (.step 2 (.run (.close 7))) (.step 58 (.run (.close 2)))) (.step 73 (.step 3 (.step 18 (.run (.close 35))))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 30 (.step 50 (.step 58 (.step 43 (.step 2 (.run (.close 7)))))))) (.step 27 (.step 73 (.step 58 (.step 42 (.step 2 (.run (.close 7)))))))))) (.step 18 (.split 14 1 (.split 22 1 (.split 65 1 (.split 74 1 (.split 4 0 (.step 36 (.step 8 (.split 10 0 (.split 14 0 (.split 16 0 (.step 2 (.run (.close 60))) (.step 50 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 18 (.step 35 (.run (.close 60))))))) (.step 2 (.run (.close 7)))) (.step 27 (.step 73 (.step 58 (.step 2 (.run (.close 7))))))) (.step 30 (.step 50 (.step 58 (.step 43 (.step 2 (.run (.close 7)))))))) (.step 8 (.step 18 (.run (.close 25))))) (.step 58 (.step 42 (.step 8 (.step 36 (.step 77 (.step 2 (.step 73 (.step 2 (.run (.close 48)))))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part860.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part861
namespace Part862
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482196438455599374046581020683475218206654831622036030156919006003394890558360758156511423357239555721169235887291590472922750256129⟩
def references : Fin 1 → Box := ![Part861.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 16 1 (.reuse 0) (.step 50 (.step 18 (.split 14 1 (.split 17 1 (.split 22 1 (.split 74 1 (.split 9 0 (.step 8 (.split 10 0 (.split 12 0 (.split 14 0 (.split 19 0 (.split 23 0 (.step 35 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 50 (.step 2 (.run (.close 73))))) (.step 2 (.run (.close 4)))) (.step 50 (.step 35 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 27 (.step 73 (.step 50 (.step 2 (.run (.close 7))))))) (.step 73 (.step 50 (.step 35 (.run (.close 2)))))) (.step 50 (.step 35 (.step 2 (.run (.close 73)))))) (.step 50 (.step 35 (.step 18 (.run (.close 17))))))))) (.step 43 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 44 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 50 (.run (.close 44))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7)))))) (.step 43 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 36 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 50 (.run (.close 36))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part861.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part862
namespace Part863
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 11572820244868825110622388235134449866509140962789238669839730259096408307344552590104568191357535209856866470556423465177886230132357164306095119709992125850979151188797300068245411798204122626287470665862466878138013975553⟩
def references : Fin 1 → Box := ![Part862.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 34 1 (.reuse 0) (.step 43 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 34 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 40)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 50 (.run (.close 34))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7)))))) (.step 68 (.step 3 (.step 31 (.split 4 0 (.step 44 (.split 10 0 (.split 16 0 (.split 17 0 (.split 30 0 (.step 2 (.run (.close 9))) (.step 42 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 2)))) (.step 3 (.step 35 (.run (.close 70)))))) (.step 2 (.run (.close 7)))))))) (.step 68 (.step 3 (.step 31 (.split 67 1 (.split 4 0 (.step 36 (.split 10 0 (.split 16 0 (.split 22 0 (.step 2 (.run (.close 9))) (.step 30 (.step 2 (.run (.close 4))))) (.step 68 (.run (.close 2)))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 3 (.step 70 (.run (.close 2))))))))) (.step 10 (.step 68 (.step 3 (.step 30 (.split 9 0 (.step 10 (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 30))))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 35)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part862.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part863
namespace Part864
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789234141782132574878415709588568036569696788914137450334149658946923917230189367968533920292327604564309923363041397911309177506453091683208760795294099499959896124296084865416299279755205767293003133470538664320059835393⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 51 0 (.split 67 0 (.split 65 0 (.split 7 0 (.split 13 0 (.split 14 0 (.split 63 1 (.split 64 1 (.step 2 (.split 16 0 (.step 2 (.run (.close 27))) (.step 27 (.step 2 (.run (.close 27)))))) (.step 71 (.run (.close 2)))) (.step 71 (.step 2 (.run (.close 74))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.step 2 (.run (.close 27))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 12))))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 11)))) (.step 71 (.split 16 0 (.split 14 0 (.step 2 (.run (.close 27))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 7 0 (.split 13 0 (.split 14 0 (.split 25 0 (.split 26 0 (.step 44 (.split 35 0 (.step 2 (.run (.close 27))) (.step 27 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 27 (.run (.close 2)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 74)))))) (.split 63 1 (.split 64 1 (.split 71 1 (.split 7 0 (.split 13 0 (.split 14 0 (.split 25 0 (.split 26 0 (.step 36 (.split 35 0 (.step 2 (.run (.close 27))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 27 (.run (.close 2)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 74))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part864
namespace Part865
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493334015740077731621366744132550475421387610564905179791560034628010231793579217034661525539126938152139331496231441890536267449345⟩
def references : Fin 1 → Box := ![Part864.root]
def proof : Chunks.Proof 1 := (.split 42 0 (.split 14 1 (.split 74 1 (.split 43 0 (.reuse 0) (.split 63 1 (.split 64 1 (.split 71 1 (.split 7 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 35 0 (.split 51 0 (.split 22 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.run (.close 2)))) (.step 30 (.step 2 (.run (.close 27))))) (.step 30 (.run (.close 2)))) (.step 4 (.step 27 (.step 4 (.run (.close 2)))))) (.step 27 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 30)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 47))))) (.step 44 (.split 7 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 27)))))) (.step 34 (.split 38 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 27)))))) (.step 44 (.split 14 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 27))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 27))))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 27))))) (.step 71 (.run (.close 2)))) (.step 58 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 74))))) (.step 58 (.step 2 (.step 74 (.step 2 (.run (.close 4))))))) (.step 4 (.step 27 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part864.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part865
namespace Part866
def root : Box := ⟨2239744742177804210561236555748572655213285071271414220264525051821315581182605891493648790705796022272, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493334015740077731621369092677372993996793304256059411409155854588680785610684573860533046849115844631762956140610704152510906500097⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 74 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 36 0 (.split 42 0 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 27))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 27))))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.run (.close 34)))) (.step 71 (.run (.close 2)))) (.split 16 0 (.split 74 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 34 (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30)))))) (.split 16 0 (.split 74 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 34 (.step 36 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 4 (.run (.close 2)))) (.step 43 (.run (.close 2))))) (.step 58 (.step 40 (.run (.close 2))))) (.step 58 (.step 40 (.run (.close 2))))) (.step 58 (.step 40 (.run (.close 2))))) (.step 4 (.step 27 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part866
namespace Part867
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 11572814729216562008630190618423645900713269600386168220885756813353720881809923895775763710493334015740077731621369092677372993996795341292035745895242123034369194988845625328926712785366480772212310521910467489217089897473⟩
def references : Fin 2 → Box := ![Part865.root, Part866.root]
def proof : Chunks.Proof 2 := (.split 30 0 (.split 34 0 (.split 36 0 (.reuse 0) (.split 14 1 (.split 74 1 (.split 63 1 (.split 64 1 (.split 71 1 (.split 42 0 (.split 16 0 (.split 14 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.step 2 (.run (.close 27))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 36)))) (.step 4 (.step 8 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 27))))) (.step 71 (.run (.close 2)))) (.split 16 0 (.split 14 0 (.split 17 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 44 (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30)))))) (.step 58 (.step 2 (.run (.close 57))))) (.step 58 (.step 2 (.step 50 (.step 2 (.run (.close 57))))))) (.step 58 (.step 40 (.run (.close 2))))) (.step 4 (.step 27 (.run (.close 2))))) (.step 4 (.step 27 (.run (.close 2)))))) (.reuse 1)) (.step 71 (.split 74 1 (.split 12 0 (.split 14 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 17 0 (.split 22 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 8 (.step 3 (.step 30 (.step 3 (.run (.close 2)))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.run (.close 2))))))) (.step 4 (.step 27 (.step 4 (.run (.close 2)))))) (.step 4 (.step 27 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 27 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part865.covered
  · exact Part866.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part867
namespace Part868
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482193730770351209188317362802292124017189257464128738564498857620124257621704966697502183107558539907336450016487152796772519117825⟩
def references : Fin 1 → Box := ![Part867.root]
def proof : Chunks.Proof 1 := (.split 72 1 (.split 65 1 (.split 4 0 (.split 10 0 (.reuse 0) (.step 71 (.split 74 1 (.split 12 0 (.split 14 0 (.split 30 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 17 0 (.split 22 0 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 18 (.step 8 (.step 3 (.step 30 (.step 3 (.run (.close 2)))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.run (.close 2))))))) (.step 4 (.step 27 (.step 4 (.run (.close 2)))))) (.step 3 (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.run (.close 7))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30))))))) (.step 4 (.step 27 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 3)))) (.step 27 (.run (.close 2)))))) (.step 2 (.step 27 (.step 68 (.step 58 (.run (.close 7))))))) (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 2 (.step 30 (.run (.close 27)))) (.step 27 (.step 2 (.run (.close 57))))) (.step 43 (.run (.close 2)))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 27 (.run (.close 2)))) (.step 30 (.run (.close 27)))) (.step 27 (.step 2 (.run (.close 7))))) (.step 27 (.step 30 (.run (.close 68))))) (.step 30 (.run (.close 27)))) (.step 27 (.step 30 (.run (.close 68))))) (.step 27 (.step 43 (.step 30 (.run (.close 2)))))))) (.step 4 (.step 40 (.step 71 (.step 2 (.run (.close 60)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part867.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part868
namespace Part869
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482193730770351209188317365095790740007260769074949633866585798418374243456683006920296889201595634071700533147104586834298037863425⟩
def references : Fin 1 → Box := ![Part868.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.reuse 0) (.step 4 (.step 40 (.step 71 (.step 2 (.run (.close 60))))))) (.step 27 (.step 18 (.split 65 1 (.split 4 0 (.step 44 (.split 9 0 (.step 8 (.split 10 0 (.split 14 0 (.step 2 (.run (.close 7))) (.step 27 (.run (.close 30)))) (.step 18 (.step 30 (.run (.close 4)))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 30 (.run (.close 7))))))) (.step 27 (.step 18 (.split 22 1 (.split 65 1 (.split 4 0 (.step 36 (.step 8 (.split 10 0 (.split 12 0 (.split 14 0 (.step 30 (.run (.close 18))) (.step 27 (.run (.close 30)))) (.step 2 (.run (.close 27)))) (.step 18 (.step 7 (.run (.close 2))))))) (.step 2 (.run (.close 7)))) (.step 30 (.run (.close 7)))) (.step 8 (.step 18 (.run (.close 25)))))))) (.step 27 (.step 18 (.split 17 1 (.split 22 1 (.split 65 1 (.split 9 0 (.step 8 (.split 10 0 (.split 11 0 (.split 12 0 (.split 14 0 (.split 17 0 (.split 19 0 (.split 22 0 (.step 30 (.run (.close 7))) (.step 73 (.step 30 (.run (.close 7))))) (.step 2 (.run (.close 30)))) (.step 35 (.step 18 (.step 30 (.run (.close 60)))))) (.step 27 (.step 48 (.step 2 (.run (.close 4)))))) (.step 2 (.run (.close 4)))) (.step 30 (.run (.close 4)))) (.step 18 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 30 (.run (.close 7)))) (.step 8 (.step 18 (.run (.close 19))))) (.step 8 (.step 18 (.run (.close 19))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part868.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part869
namespace Part870
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 11572820244868825110617489351823792524072193112387837030235208027313783089431336688904676977482196438455599374046581020685714960812845599911685287180055808300510241239909267677440910486590501625130893525088303591948291146753⟩
def references : Fin 1 → Box := ![Part869.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 42 1 (.reuse 0) (.step 43 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 44 (.run (.close 28))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 43 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 36 (.run (.close 28))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 43 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 34 (.run (.close 28))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part869.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part870
namespace Part871
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402⟩
def references : Fin 1 → Box := ![Part870.root]
def proof : Chunks.Proof 1 := (.step 2 (.split 10 1 (.split 30 1 (.split 43 1 (.split 51 1 (.split 67 1 (.reuse 0) (.step 68 (.step 3 (.step 31 (.split 4 0 (.step 44 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 29 0 (.split 44 0 (.split 30 0 (.step 2 (.run (.close 9))) (.step 35 (.step 7 (.run (.close 2))))) (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 3 (.step 7 (.run (.close 2))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))))))) (.step 68 (.step 3 (.step 31 (.split 67 1 (.split 4 0 (.step 36 (.split 10 0 (.split 16 0 (.split 22 0 (.step 2 (.run (.close 9))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 3 (.step 70 (.run (.close 2))))))))) (.step 10 (.step 68 (.step 3 (.step 30 (.split 9 0 (.step 10 (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 30))))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.run (.close 7))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 16 0 (.step 30 (.run (.close 49))) (.step 8 (.step 35 (.run (.close 31))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part870.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part871
namespace Part872
def root : Box := ⟨2147483648, 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402⟩
def references : Fin 3 → Box := ![Part854.root, Part863.root, Part871.root]
def proof : Chunks.Proof 3 := (.split 27 1 (.split 32 1 (.reuse 0) (.step 2 (.split 10 1 (.reuse 1) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 30 (.step 31 (.run (.close 2)))) (.step 3 (.run (.close 35)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))) (.reuse 2))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part854.covered
  · exact Part863.covered
  · exact Part871.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part872
end FiveColour.Packed.EnumerationChunks.Case171
