module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case99
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447783622995019261834600293796402646082303876835311616⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨37630511536740859966423, 5789234131009369111655880410916383799149935097950111679937790244350696937832588910803674238545500183085609357535611307840729301634221804252716538090356296810875202044827950228461282219658217406305038239415791728186442646529, 0⟩]
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
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428103608535382820839502517187328220872637725612953037113167359257830256167358084505511883429889174893601830119260538095858685210203095649894246454210629619222052864⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.split 45 1 (.split 55 1 (.split 5 0 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 3 (.close 48)) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 18 (.step 3 (.close 4))))) (.step 3 (.close 7))) (.step 3 (.step 18 (.step 47 (.step 3 (.close 8)))))) (.step 58 (.close 3))) (.step 48 (.close 3))) (.step 3 (.close 7))) (.split 67 1 (.step 48 (.step 58 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.step 31 (.close 48))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 48))) (.step 3 (.close 7)))) (.step 18 (.close 48))))) (.step 3 (.close 7)))) (.step 3 (.split 45 1 (.split 11 0 (.split 16 0 (.split 17 0 (.split 43 0 (.step 60 (.close 3)) (.step 31 (.step 3 (.close 48)))) (.step 18 (.close 60))) (.step 18 (.close 60))) (.step 60 (.close 3))) (.step 48 (.close 60))))) (.step 3 (.step 58 (.step 60 (.step 3 (.split 45 1 (.split 55 1 (.split 57 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.split 10 0 (.step 31 (.close 48)) (.step 3 (.close 12)))) (.step 3 (.close 59))) (.step 3 (.close 59))) (.step 3 (.close 59))) (.step 10 (.step 28 (.step 18 (.close 31))))) (.step 3 (.step 31 (.close 48)))) (.step 51 (.step 60 (.close 3)))) (.step 5 (.step 28 (.step 3 (.step 31 (.close 48)))))) (.step 10 (.step 31 (.step 28 (.step 48 (.close 4))))))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959688358679431672185434291799788349847875366911508185271737702070981949118002082541921790033604133561824730292831416285667672300860127627562844836658675712⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 52 1 (.split 53 1 (.reuse 0) (.run (.step 3 (.step 48 (.step 51 (.step 60 (.step 3 (.split 55 1 (.split 10 0 (.step 51 (.split 45 1 (.split 57 1 (.split 5 0 (.split 16 0 (.step 3 (.step 51 (.step 18 (.split 25 0 (.step 48 (.close 14)) (.step 3 (.close 28)))))) (.step 18 (.close 56))) (.step 8 (.close 3))) (.step 51 (.step 60 (.close 3)))) (.step 4 (.step 8 (.step 18 (.close 48)))))) (.step 3 (.step 8 (.step 14 (.step 3 (.close 49)))))) (.step 5 (.step 18 (.step 30 (.step 8 (.step 51 (.close 58)))))))))))))) (.run (.step 55 (.step 60 (.split 53 1 (.split 56 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 48 (.step 3 (.step 48 (.step 3 (.close 21))))) (.step 31 (.close 48))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 18 (.close 48))) (.step 3 (.step 28 (.step 31 (.close 48))))) (.step 3 (.step 8 (.step 18 (.close 48))))))))) (.run (.step 51 (.step 3 (.close 54)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 14696649931972027310843563361000416961428110644959694911853988495516326408048693131662584394368729267579177585613271594698356212993911546580175684444170589001525226342450454425250673589531359800996134912⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 55 (.split 50 1 (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.step 31 (.close 48))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 12))) (.step 3 (.close 7)))) (.step 18 (.close 48))))) (.step 3 (.close 7))) (.split 5 0 (.split 11 0 (.split 25 0 (.step 52 (.split 34 0 (.split 16 0 (.step 62 (.close 3)) (.step 18 (.close 52))) (.step 9 (.step 31 (.close 48))))) (.step 3 (.close 58))) (.step 3 (.close 48))) (.step 3 (.close 48)))) (.step 3 (.step 49 (.step 48 (.close 3))))) (.step 3 (.step 31 (.step 49 (.close 52))))) (.step 3 (.step 18 (.step 34 (.close 48))))) (.step 3 (.close 54))) (.step 52 (.step 55 (.split 45 1 (.split 53 1 (.split 56 1 (.split 5 0 (.split 11 0 (.split 25 0 (.step 52 (.split 34 0 (.split 36 0 (.split 10 0 (.step 53 (.close 3)) (.step 18 (.close 52))) (.step 9 (.step 31 (.close 48)))) (.step 9 (.step 31 (.close 48))))) (.step 21 (.step 3 (.close 52)))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 34 (.close 48)))) (.step 31 (.step 48 (.close 52)))) (.step 3 (.close 48))) (.step 48 (.close 3))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 14696649931972027310843563361000416961428110644959694911853994592681463743971020048844673834146670182809924978135050616489292981298088928934902481917028134884281397879425300922561016261358858410928373760⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 47 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.split 51 1 (.split 53 1 (.split 56 1 (.split 57 1 (.split 59 1 (.split 67 1 (.step 48 (.step 58 (.split 5 0 (.step 55 (.split 10 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 58 (.step 31 (.close 48))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.close 48))) (.step 3 (.close 7)))) (.step 3 (.close 48))))) (.step 3 (.close 7))) (.split 5 0 (.split 11 0 (.split 25 0 (.step 53 (.split 34 0 (.split 16 0 (.step 62 (.close 3)) (.step 18 (.close 53))) (.step 9 (.step 31 (.close 48))))) (.step 3 (.close 58))) (.step 3 (.close 48))) (.step 3 (.close 48)))) (.step 3 (.step 50 (.step 48 (.close 3))))) (.step 3 (.step 21 (.step 31 (.close 58))))) (.step 3 (.step 18 (.step 48 (.close 8))))) (.step 3 (.close 54))))) (.reuse 1)) (.run (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.step 60 (.split 45 1 (.split 55 1 (.split 17 0 (.split 22 0 (.split 43 0 (.step 50 (.close 3)) (.step 31 (.close 50))) (.step 18 (.close 50))) (.step 18 (.close 50))) (.step 32 (.step 50 (.close 3)))) (.step 48 (.close 50)))))) (.step 48 (.step 50 (.close 3)))) (.step 28 (.step 48 (.step 50 (.step 3 (.step 50 (.close 59))))))) (.step 8 (.step 50 (.step 3 (.step 50 (.close 48)))))) (.step 48 (.step 3 (.close 50)))) (.step 3 (.step 50 (.step 48 (.close 3))))) (.step 3 (.step 48 (.step 53 (.step 49 (.close 55)))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837821305112336769945558783645540743836221325928254928649657619342529412444168554988297162121008275372489330598357237760⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.step 48 (.step 58 (.split 46 1 (.reuse 0) (.run (.split 47 1 (.step 3 (.split 49 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.step 60 (.split 45 1 (.split 55 1 (.split 11 0 (.split 16 0 (.step 49 (.step 3 (.close 21))) (.step 18 (.close 49))) (.step 49 (.close 3))) (.step 49 (.close 3))) (.step 48 (.close 49)))))) (.step 48 (.step 49 (.close 3)))) (.step 28 (.step 49 (.step 3 (.step 49 (.close 48)))))) (.step 8 (.step 49 (.step 3 (.step 49 (.step 3 (.close 48))))))) (.step 48 (.step 3 (.close 49)))) (.step 3 (.step 50 (.step 48 (.close 3))))) (.step 3 (.step 48 (.step 52 (.step 49 (.close 55))))))) (.step 48 (.step 49 (.step 3 (.step 50 (.close 3)))))))))) (.run (.step 10 (.step 30 (.step 47 (.step 3 (.step 46 (.step 9 (.step 27 (.step 46 (.close 52))))))))))) (.run (.step 58 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 60 (.split 53 1 (.step 31 (.close 7)) (.step 3 (.close 31)))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 50)))) (.step 31 (.close 49))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808404421007984981332222981525634950415101928307752620619525102454410189852805791217533983713968832919896064⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.reuse 0) (.run (.step 58 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 52 1 (.split 53 1 (.step 21 (.split 56 1 (.split 57 1 (.step 3 (.step 58 (.split 45 1 (.split 55 1 (.split 59 1 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.step 28 (.split 10 0 (.step 31 (.close 48)) (.step 3 (.close 12)))) (.step 3 (.close 41))) (.step 3 (.close 41))) (.step 3 (.step 28 (.step 18 (.close 31))))) (.step 10 (.step 28 (.step 18 (.close 31))))) (.step 3 (.step 21 (.close 41)))) (.step 5 (.step 31 (.close 58)))) (.step 10 (.step 21 (.step 31 (.close 48))))))) (.step 28 (.step 3 (.step 60 (.close 41))))) (.step 28 (.step 41 (.step 3 (.step 58 (.step 41 (.close 3)))))))) (.step 5 (.step 51 (.step 24 (.step 60 (.split 5 0 (.step 43 (.close 41)) (.step 8 (.close 3)))))))) (.step 3 (.step 48 (.close 41)))) (.step 3 (.step 21 (.step 48 (.step 28 (.step 49 (.close 58))))))) (.step 21 (.step 32 (.step 41 (.close 50))))) (.step 21 (.step 48 (.step 28 (.step 41 (.step 49 (.step 3 (.step 49 (.close 41))))))))) (.step 31 (.step 3 (.close 41))))))) (.run (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 53 1 (.split 57 1 (.step 31 (.close 7)) (.step 31 (.close 3))) (.step 3 (.step 28 (.step 8 (.close 31))))))) (.step 31 (.close 53))) (.step 31 (.close 52))) (.step 31 (.close 50))) (.step 31 (.close 49))) (.step 31 (.step 7 (.close 39)))) (.step 31 (.step 28 (.close 39))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500250506526720, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343338214548610398614813211261605033395849851515813578045129035786223616⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 38 1 (.step 48 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 28 (.split 52 1 (.split 53 1 (.split 57 1 (.step 3 (.step 58 (.step 28 (.split 45 1 (.split 55 1 (.split 59 1 (.split 5 0 (.split 16 0 (.split 17 0 (.step 28 (.close 3)) (.step 3 (.close 28))) (.step 3 (.step 18 (.close 28)))) (.step 10 (.step 28 (.close 5)))) (.step 3 (.step 28 (.close 48)))) (.step 5 (.step 28 (.close 48)))) (.step 10 (.step 31 (.step 28 (.close 48)))))))) (.step 28 (.step 3 (.close 60)))) (.step 28 (.step 30 (.step 24 (.step 28 (.step 18 (.close 56))))))) (.step 3 (.step 48 (.close 28))))) (.step 3 (.step 50 (.step 28 (.close 53))))) (.step 3 (.step 31 (.step 49 (.step 58 (.close 21)))))) (.step 48 (.step 28 (.step 3 (.step 49 (.step 28 (.close 50))))))) (.step 48 (.step 28 (.step 49 (.step 3 (.close 49))))))) (.step 58 (.step 28 (.step 3 (.close 21))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447780699991744600026165202696269343240944523585519616⟩
def references : Fin 2 → Box := ![Part5.root, Part6.root]
def proof : Chunks.Proof 2 := (.split 17 1 (.split 22 1 (.split 25 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.split 36 1 (.split 38 1 (.split 42 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 31 (.step 59 (.split 53 1 (.split 57 1 (.step 31 (.close 7)) (.step 31 (.close 3))) (.step 3 (.step 28 (.step 14 (.close 31))))))) (.step 31 (.close 52))) (.step 31 (.close 52))) (.step 31 (.close 50))) (.step 31 (.close 49))) (.step 31 (.step 7 (.close 37)))) (.step 16 (.step 21 (.step 28 (.step 31 (.step 3 (.close 37))))))) (.step 7 (.step 31 (.close 37)))))) (.run (.split 38 1 (.split 46 1 (.step 3 (.step 7 (.step 18 (.step 50 (.split 53 1 (.step 3 (.step 7 (.close 31))) (.step 3 (.close 18))))))) (.step 18 (.close 31))) (.step 3 (.close 31))))) (.reuse 1)) (.run (.step 48 (.split 25 1 (.split 38 1 (.split 46 1 (.step 7 (.split 47 1 (.split 49 1 (.split 50 1 (.step 60 (.split 56 1 (.step 18 (.close 7)) (.step 3 (.close 18)))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50)))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 49 (.step 41 (.close 50)))))) (.step 3 (.step 18 (.step 28 (.close 49)))))))) (.run (.split 22 1 (.split 25 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 57 1 (.step 18 (.close 7)) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 28)))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 49 (.step 41 (.close 50)))))) (.step 3 (.step 18 (.step 28 (.close 49))))) (.step 18 (.step 7 (.close 20))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes
  · exact Part6.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨2596148429267413814265251385835520, 14696649931972027310843563361000416961428110644959694908657324083115057888911105633968524043930674806493827324308274735363626943128406028362768188960037679684260837200899992385506332129118752467962560512⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 46 1 (.split 47 1 (.split 50 1 (.split 52 1 (.split 53 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 34 1 (.split 36 1 (.split 42 1 (.step 34 (.split 55 1 (.split 59 1 (.split 5 0 (.split 16 0 (.step 3 (.split 17 0 (.split 22 0 (.split 25 0 (.split 34 0 (.step 48 (.close 14)) (.step 4 (.close 14))) (.step 3 (.close 28))) (.step 3 (.step 14 (.close 18)))) (.step 3 (.step 14 (.close 18))))) (.step 18 (.step 3 (.close 14)))) (.step 8 (.close 3))) (.step 3 (.step 18 (.close 48)))) (.step 12 (.step 18 (.step 8 (.close 58)))))) (.step 3 (.close 31))) (.step 4 (.close 31))) (.step 3 (.close 31))))) (.step 8 (.step 3 (.step 48 (.step 60 (.step 3 (.close 12))))))) (.step 5 (.step 31 (.step 51 (.step 24 (.step 60 (.split 5 0 (.step 43 (.step 14 (.close 28))) (.step 8 (.close 3))))))))) (.step 8 (.step 34 (.step 14 (.step 3 (.step 48 (.step 51 (.split 36 1 (.split 42 1 (.step 14 (.close 3)) (.step 4 (.close 14))) (.step 4 (.close 14)))))))))) (.step 3 (.step 48 (.close 14)))) (.step 3 (.step 48 (.close 14)))) (.step 12 (.step 48 (.step 8 (.step 14 (.step 50 (.step 3 (.step 50 (.close 14))))))))) (.step 12 (.step 14 (.step 18 (.step 34 (.close 49)))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447783622995019261834600293796402646080052077021626368⟩
def references : Fin 2 → Box := ![Part7.root, Part8.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 11 1 (.split 16 1 (.reuse 0) (.run (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 57 1 (.step 18 (.close 7)) (.step 18 (.close 3))) (.step 3 (.step 18 (.close 28)))) (.step 18 (.close 53))) (.step 18 (.close 52))) (.step 18 (.close 50))) (.step 18 (.close 49))) (.step 3 (.step 18 (.step 41 (.close 49))))) (.step 3 (.step 18 (.step 28 (.close 49))))) (.step 18 (.step 7 (.close 19)))) (.step 7 (.step 18 (.close 19)))))) (.step 31 (.step 34 (.step 58 (.split 16 1 (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.reuse 1) (.run (.step 4 (.step 14 (.step 31 (.step 41 (.step 49 (.step 50 (.step 60 (.split 16 0 (.split 17 0 (.step 43 (.split 22 0 (.split 56 1 (.step 24 (.step 43 (.step 28 (.step 14 (.close 31))))) (.step 41 (.close 3))) (.step 3 (.step 14 (.close 28))))) (.step 3 (.step 5 (.step 14 (.close 28))))) (.step 3 (.step 5 (.step 14 (.close 28)))))))))))))) (.run (.step 28 (.step 30 (.step 14 (.step 24 (.step 28 (.step 49 (.step 14 (.close 50)))))))))) (.run (.step 14 (.step 18 (.step 3 (.close 8)))))) (.run (.step 18 (.step 8 (.step 3 (.close 14)))))) (.run (.step 18 (.step 14 (.step 3 (.close 19)))))))))) (.run (.split 11 1 (.split 25 1 (.split 38 1 (.split 46 1 (.step 3 (.step 18 (.split 47 1 (.split 53 1 (.step 3 (.step 7 (.close 31))) (.step 3 (.close 8))) (.step 18 (.close 31))))) (.step 18 (.close 31))) (.step 3 (.close 31))) (.step 3 (.close 28))) (.step 3 (.close 14)))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part7.excludes
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨3221225472, 14696649931972027310843563361000416965113620825449481388652387744134990272634624761837826230367808408900497469341014716049079171878343341584541943792447783622995019261834600293796402646082303876835311616⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.split 5 1 (.reuse 0) (.run (.step 31 (.split 11 1 (.step 58 (.split 38 1 (.split 46 1 (.split 47 1 (.split 49 1 (.split 50 1 (.step 8 (.split 52 1 (.split 56 1 (.split 57 1 (.step 3 (.step 48 (.split 25 1 (.split 34 1 (.split 36 1 (.split 42 1 (.step 8 (.split 45 1 (.split 55 1 (.split 59 1 (.split 5 2 (.split 16 0 (.step 3 (.step 47 (.split 34 0 (.step 8 (.close 3)) (.step 4 (.close 8))))) (.step 8 (.close 3))) (.step 8 (.close 3))) (.step 3 (.step 8 (.close 48)))) (.step 18 (.step 30 (.step 8 (.close 48))))) (.step 8 (.close 48)))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 3 (.close 31))) (.step 10 (.close 47))))) (.step 3 (.step 8 (.step 47 (.step 48 (.close 60)))))) (.step 5 (.step 8 (.step 10 (.step 28 (.step 31 (.step 8 (.step 43 (.close 59))))))))) (.step 3 (.step 48 (.close 8))))) (.step 3 (.step 48 (.close 8)))) (.step 3 (.step 48 (.close 8)))) (.step 48 (.step 8 (.step 3 (.step 49 (.close 50)))))) (.step 48 (.step 8 (.step 49 (.step 3 (.close 49)))))) (.step 8 (.step 10 (.step 41 (.step 43 (.step 8 (.step 49 (.step 41 (.close 50)))))))))) (.step 48 (.step 8 (.step 3 (.close 12))))))))
theorem accepted : Fast.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Fast.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part10.excludes
end FiveColour.Packed.ProjectedChunks.Case99
