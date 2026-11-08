module
public import FiveColour.EnumerationChunks.Case173.Parts0
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case173
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Part714
def root : Box := ⟨2535301200456458802995553894400, 5789234136395753411692881238169227500374411343012498997365017166389965156744979072850177315421158449975466527160861389740594288610845113279272209495012821120338963984734353387974817055491180352856811984237369217490773607425⟩
def references : Fin 1 → Box := ![Part713.root]
def proof : Chunks.Proof 1 := (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.reuse 0) (.step 3 (.step 31 (.split 21 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2))))))) (.step 3 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 7))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 13 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 9 (.run (.close 7))) (.step 3 (.run (.close 2)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part713.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part714
namespace Part715
def root : Box := ⟨2535301200456458802995553894400, 5789239652048016513680179966897434931288206951125608086251332488484335124015486382911757285397622310809129506972032894026846499379650928125830082281844369433204680415635462620621065107856550566729682143039946133284326474753⟩
def references : Fin 1 → Box := ![Part714.root]
def proof : Chunks.Proof 1 := (.split 56 1 (.split 72 1 (.split 2 0 (.split 52 0 (.split 5 0 (.reuse 0) (.step 3 (.step 31 (.split 21 0 (.split 4 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 8)))) (.step 3 (.run (.close 7)))) (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 30))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10))))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2))))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 31 0 (.split 33 0 (.step 3 (.run (.close 7))) (.step 43 (.run (.close 12)))) (.step 43 (.run (.close 12)))) (.step 43 (.run (.close 3)))) (.step 68 (.run (.close 2)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 3)))) (.step 68 (.run (.close 2)))) (.step 43 (.step 68 (.run (.close 2))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 68))))))) (.step 18 (.step 31 (.split 4 0 (.split 16 0 (.split 17 0 (.step 3 (.run (.close 2))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 3 (.run (.close 43))))))) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.step 31 (.run (.close 7))))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 10))))) (.step 43 (.run (.close 2)))) (.step 49 (.step 43 (.run (.close 2))))))))
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
def root : Box := ⟨2535301200456458802995553894400, 5789239652048016513680179966897434931288206955177869383986677174531608428401385944447349309071877095961138617998061032465763227088186354724057028547982238065010288850478407860058990531414801021053566320642053475028016563201⟩
def references : Fin 1 → Box := ![Part715.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.split 25 1 (.split 26 1 (.split 35 1 (.reuse 0) (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.split 30 0 (.step 31 (.run (.close 38))) (.step 7 (.run (.close 2)))))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 29 (.step 3 (.step 18 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 29 (.run (.close 2))) (.step 2 (.run (.close 29)))) (.step 43 (.run (.close 29)))) (.step 43 (.run (.close 29)))) (.step 43 (.step 29 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 2 (.step 3 (.step 18 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 10))))) (.step 43 (.run (.close 2)))) (.step 49 (.step 43 (.run (.close 2))))))))) (.step 18 (.step 31 (.split 4 0 (.split 6 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 22 0 (.split 12 0 (.split 29 0 (.step 52 (.step 62 (.step 3 (.run (.close 27))))) (.step 3 (.run (.close 7)))) (.step 15 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 2)))))))
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
def root : Box := ⟨2535301200456458802995553894400, 5789239652048016513680179966897434931288206955177869383986680773662644066235079471289820903915488644109740614045096123611375036500022036737143460845757116055969294562648087606129436003056036807555512800435182424641269400577⟩
def references : Fin 1 → Box := ![Part716.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.split 54 1 (.reuse 0) (.step 29 (.step 31 (.split 35 1 (.step 3 (.split 59 1 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 29 0 (.step 9 (.step 15 (.step 57 (.run (.close 68))))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 18)))) (.step 9 (.step 15 (.step 57 (.run (.close 3)))))) (.step 9 (.step 15 (.step 57 (.run (.close 12)))))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 57 (.step 3 (.run (.close 7)))))) (.step 15 (.step 18 (.run (.close 2)))))))) (.step 18 (.split 54 1 (.step 31 (.split 4 0 (.split 6 0 (.split 9 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 52 (.step 62 (.split 30 0 (.step 3 (.run (.close 27))) (.step 7 (.run (.close 2)))))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 68 (.run (.close 53)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 3))))) (.step 15 (.step 3 (.run (.close 7))))))) (.split 25 0 (.split 38 0 (.split 47 0 (.split 5 0 (.split 11 0 (.split 56 0 (.split 57 0 (.step 52 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 52 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 3)))) (.step 66 (.run (.close 52)))) (.step 7 (.run (.close 3)))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 2))))))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 48 (.step 9 (.run (.close 31))))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))) (.step 7 (.run (.close 3)))))
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
def root : Box := ⟨2535301200456458802995553894400, 11572820244868825110617489347147286435501031520177405399052787632740648715893510080137823557543736308178263190397759971358904255524377079584632167142529016671368793143909365032119123144231374040859626705407152077160322171905⟩
def references : Fin 1 → Box := ![Part717.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 58 1 (.split 14 1 (.split 71 1 (.split 74 1 (.reuse 0) (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 11 (.step 17 (.step 77 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 2 (.step 31 (.split 35 1 (.step 18 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 66 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2))))))) (.step 2 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 11 (.run (.close 17))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 2 (.step 3 (.split 49 1 (.split 50 1 (.step 18 (.split 4 0 (.split 9 0 (.split 18 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 27 (.step 61 (.step 31 (.run (.close 2))))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 61 (.step 3 (.run (.close 7))))) (.step 61 (.run (.close 52))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))
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
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545611387564831695691227734228001108554102154436602374103554232477137635305385726768172207507857155457143552606552080939248965176969616887159903735628305142313925908458360223924475887118064505238588364948481⟩
def references : Fin 1 → Box := ![Part718.root]
def proof : Chunks.Proof 1 := (.split 73 1 (.split 24 1 (.split 34 1 (.split 36 1 (.split 39 1 (.reuse 0) (.step 2 (.step 43 (.step 3 (.split 49 1 (.split 50 1 (.step 18 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 27 (.step 31 (.run (.close 2)))) (.step 3 (.run (.close 42)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 43 (.run (.close 42)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 42 (.step 3 (.run (.close 7))))) (.step 42 (.run (.close 52)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 2 (.step 43 (.step 3 (.split 49 1 (.split 50 1 (.step 18 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 16 0 (.step 27 (.run (.close 43))) (.step 11 (.step 42 (.run (.close 31))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 24 (.step 10 (.run (.close 18))))) (.step 24 (.step 10 (.run (.close 18))))) (.step 24 (.step 10 (.run (.close 18))))))))))
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
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545611387564831695691227734228001108554102154436602374103554232477137635305385726768172207507857155457143552606552080939248965176969616887161588732295002058799131775166836900696034700949570380023492961633281⟩
def references : Fin 1 → Box := ![Part719.root]
def proof : Chunks.Proof 1 := (.split 7 1 (.split 12 1 (.split 13 1 (.split 16 1 (.split 17 1 (.split 22 1 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 7))))) (.step 7 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 7)))))) (.step 16 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 24 (.step 10 (.run (.close 16))))) (.step 24 (.step 10 (.run (.close 16))))) (.step 24 (.step 10 (.run (.close 16)))))))))) (.step 15 (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 9 (.run (.close 15))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 15)))) (.step 24 (.run (.close 15)))) (.step 24 (.run (.close 15)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 7))))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 8 (.run (.close 10)))) (.step 2 (.run (.close 7)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part719.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part720
namespace Part721
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616291232212648538093277855506308984101053250951864414688692219626204467020300324591129829876502292088586624831223108921009989414150544861866424910161200226927774417682006229618866766907850223360863634433⟩
def references : Fin 1 → Box := ![Part720.root]
def proof : Chunks.Proof 1 := (.split 64 1 (.split 66 1 (.split 67 1 (.split 6 1 (.reuse 0) (.step 2 (.step 15 (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.split 72 1 (.step 3 (.split 4 0 (.split 9 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 9 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 11 (.run (.close 9)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 7))))) (.step 9 (.run (.close 2))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 2 (.step 3 (.step 31 (.split 35 1 (.step 18 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 66 (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 3 (.run (.close 2))))))))
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
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740881771480194378076702380523137015023701083303175328932610298495904119405164205180041077221665600643660744207609284704676609921836385281⟩
def references : Fin 1 → Box := ![Part721.root]
def proof : Chunks.Proof 1 := (.split 46 1 (.split 47 1 (.split 48 1 (.split 51 1 (.split 57 1 (.split 63 1 (.reuse 0) (.step 66 (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 16 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 66 (.run (.close 2))) (.step 2 (.run (.close 66)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 66 (.run (.close 3)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 30))))) (.step 49 (.step 8 (.step 2 (.run (.close 60)))))) (.step 3 (.run (.close 2))))))))) (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.step 2 (.run (.close 30))))) (.step 49 (.step 8 (.step 2 (.run (.close 7)))))) (.step 3 (.run (.close 2))))))))) (.step 49 (.step 3 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 49 (.run (.close 2)))) (.step 49 (.run (.close 2)))) (.step 49 (.step 2 (.run (.close 30))))))))))
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
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489548081790430552446014625839972151588078117954384825585652023966482180118688829471728786736129⟩
def references : Fin 1 → Box := ![Part722.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 31 1 (.split 33 1 (.split 41 1 (.split 43 1 (.split 44 1 (.reuse 0) (.step 29 (.step 3 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7))))))
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
def root : Box := ⟨2535301200456458802995553894400, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489548083779723498085161196186937730874573233144285930424116562543945635587171949293006436172801⟩
def references : Fin 1 → Box := ![Part723.root]
def proof : Chunks.Proof 1 := (.split 9 1 (.split 18 1 (.split 19 1 (.split 23 1 (.split 29 1 (.reuse 0) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 2 (.run (.close 7))))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 2 (.run (.close 7))))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 24 (.run (.close 3)))) (.step 2 (.run (.close 7))))))) (.step 3 (.step 12 (.split 4 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.run (.close 3))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))
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
def root : Box := ⟨2201170739200, 5789234136395753411692881238169227500374407193496930116368373140286835277120157493187709692806004706336581614188777680622228755138383695925235765889249896636370676103913577514812763184473844565502163127417027276614429312000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 54 0 (.split 58 0 (.split 72 0 (.split 73 0 (.split 74 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 9))) (.split 22 0 (.step 2 (.run (.close 9))) (.step 18 (.run (.close 27))))) (.split 22 0 (.split 44 0 (.split 48 0 (.split 18 0 (.step 18 (.step 62 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 9)))) (.step 18 (.run (.close 7))))) (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 18 (.run (.close 7))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 27))) (.step 3 (.run (.close 27)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 43)))))) (.step 2 (.run (.close 7)))) (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 3 (.run (.close 7))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part725
namespace Part726
def root : Box := ⟨2201170739200, 5789234136395753411692881238169227500374407193496930116368373143801611679107029667258445809290575216008679456763865082380155581827465487773510918587701823954295809725604901439802298891951371812817352305890497811721511502848⟩
def references : Fin 1 → Box := ![Part725.root]
def proof : Chunks.Proof 1 := (.split 5 0 (.split 6 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 13 0 (.split 14 0 (.split 21 0 (.split 24 0 (.split 26 0 (.split 35 0 (.split 39 0 (.split 40 0 (.split 45 0 (.split 53 0 (.reuse 0) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 9))) (.step 3 (.run (.close 9)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 18 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 9))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 3 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 31 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 18 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))
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
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182410508453019648, 5789234136395753411692881238169227500374407197549191414103717829848884986769516507205703279022954453551595922303621829066727413487700547583707144762496067476417522436978839091238457621088039409068965242017167424087966876672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 21 0 (.split 25 0 (.split 26 0 (.split 27 0 (.split 32 0 (.split 35 0 (.split 37 0 (.split 38 0 (.split 46 0 (.split 47 0 (.split 5 0 (.split 7 0 (.split 8 0 (.split 11 0 (.split 40 0 (.split 45 0 (.split 56 0 (.split 57 0 (.split 60 0 (.split 64 0 (.split 70 0 (.split 71 0 (.split 72 0 (.split 53 0 (.split 73 0 (.split 74 0 (.split 6 0 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 44 0 (.step 53 (.split 48 0 (.split 12 0 (.split 29 0 (.step 52 (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 7 (.run (.close 31)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))) (.step 7 (.run (.close 31)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 9 (.step 7 (.run (.close 3))))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 31)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 18)))) (.step 3 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 18)))) (.step 2 (.run (.close 7)))) (.step 9 (.step 7 (.run (.close 3)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part727
namespace Part728
def root : Box := ⟨2201170739200, 5789234136395753411692881238169227500374407197549191414103717829852317385599581812063194229422495150160230639953693481771424645217293319177348641680783076367667711621291006153578032136851445884201694259631808218575116698625⟩
def references : Fin 2 → Box := ![Part726.root, Part727.root]
def proof : Chunks.Proof 2 := (.split 0 0 (.split 2 0 (.split 15 0 (.split 28 0 (.split 52 0 (.split 49 1 (.split 50 1 (.split 59 1 (.reuse 0) (.step 18 (.step 31 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 12 0 (.split 29 0 (.split 30 0 (.split 31 0 (.step 62 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 18 (.step 31 (.split 9 0 (.split 10 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 24 0 (.split 29 0 (.split 30 0 (.step 62 (.split 31 0 (.split 33 0 (.split 34 0 (.step 53 (.run (.close 2))) (.step 9 (.step 68 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 3 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.reuse 1)) (.step 2 (.step 7 (.run (.close 18))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part726.covered
  · exact Part727.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part728
namespace Part729
def root : Box := ⟨2201170739200, 5789239652048016513685078850208092273725150656063702138820596558035371102316808900260436827234300739972127527080702398214995919914218683068340089623034128302570077570327545662498705459942468832358456376212444147926827009025⟩
def references : Fin 1 → Box := ![Part728.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 35 1 (.split 54 1 (.split 72 1 (.reuse 0) (.step 3 (.step 18 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 19 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.step 31 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7))))))) (.step 3 (.split 49 1 (.split 50 1 (.step 31 (.split 59 1 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 29 0 (.step 9 (.step 57 (.step 18 (.run (.close 2))))) (.step 2 (.run (.close 57)))) (.step 24 (.run (.close 18)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 24 (.run (.close 18)))) (.step 24 (.run (.close 18)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 3)))) (.step 57 (.step 3 (.run (.close 7)))))) (.step 57 (.step 3 (.run (.close 7))))) (.step 57 (.step 3 (.run (.close 7))))))) (.step 18 (.split 54 1 (.step 3 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 29 0 (.step 29 (.step 75 (.split 30 0 (.step 31 (.run (.close 38))) (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7))))) (.step 18 (.run (.close 2)))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
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
def root : Box := ⟨2201170739200, 5789239652048016513685078850208092273725150656063702138820596558035374454268791385909711720743325668813028376639999616087407655313602918457435412384505086681268644432074321006207602151743552459908586859508600202593465009153⟩
def references : Fin 1 → Box := ![Part729.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 43 1 (.split 51 1 (.split 34 1 (.split 36 1 (.split 42 1 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))
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
def root : Box := ⟨2201170739200, 11578468272786241545616291232212652993601693502181331052907722459900959428036032871984740884613466633496135808609392071569347916489548083779723498085161196186937730874573233144285930424116562543945635587171949294105947800577⟩
def references : Fin 1 → Box := ![Part730.root]
def proof : Chunks.Proof 1 := (.step 2 (.step 18 (.split 10 1 (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))) (.step 18 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.split 72 1 (.step 3 (.split 9 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 18 0 (.split 19 0 (.split 22 0 (.split 23 0 (.split 29 0 (.step 9 (.step 57 (.step 18 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 24 (.run (.close 18)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 24 (.step 9 (.run (.close 18))))) (.step 24 (.step 9 (.run (.close 18))))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 3))))) (.step 18 (.run (.close 2))))) (.step 15 (.step 3 (.run (.close 7))))) (.step 15 (.step 3 (.run (.close 7))))) (.step 15 (.step 3 (.run (.close 7))))) (.step 18 (.run (.close 2)))))) (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 7 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))
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
def root : Box := ⟨9343878384890255807777119448474196633381331982845050737826186276657715542443371287564109437577976626746659450006721346172290467269376897020421450382791094657540085093089822617769726345723192016896, 5789239652048016513680179971569374123733330705498598925717827956896141920115614013675656175464465431090530458372452795152830351267767361485943980405755581262018860118464265562336936627632405558038632880027284194924377932801⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 42 1 (.split 21 1 (.split 12 1 (.split 35 1 (.split 54 1 (.split 72 1 (.split 10 0 (.split 30 0 (.split 43 0 (.split 49 0 (.split 50 0 (.split 51 0 (.split 59 0 (.split 67 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 57))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 71 (.step 3 (.step 31 (.step 69 (.step 55 (.run (.close 2)))))))) (.split 49 0 (.split 50 0 (.step 3 (.step 2 (.step 74 (.step 2 (.run (.close 57)))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 71 (.step 40 (.split 43 0 (.split 51 0 (.split 67 0 (.step 31 (.split 54 1 (.split 49 0 (.split 72 1 (.step 3 (.run (.close 2))) (.step 29 (.step 3 (.step 2 (.run (.close 57)))))) (.step 40 (.step 66 (.step 29 (.run (.close 55)))))) (.step 9 (.run (.close 57))))) (.step 55 (.run (.close 2)))) (.step 9 (.run (.close 3)))) (.step 9 (.run (.close 2))))))) (.split 51 0 (.split 67 0 (.split 35 1 (.split 18 0 (.split 54 1 (.step 3 (.split 72 1 (.split 21 0 (.split 49 0 (.step 3 (.run (.close 2))) (.step 66 (.run (.close 2)))) (.step 9 (.step 43 (.step 2 (.run (.close 7)))))) (.step 40 (.step 66 (.step 55 (.run (.close 2))))))) (.step 57 (.run (.close 2)))) (.step 2 (.step 57 (.step 66 (.run (.close 68)))))) (.step 57 (.step 40 (.step 66 (.step 55 (.step 2 (.run (.close 57)))))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2))))) (.step 68 (.step 2 (.run (.close 57))))) (.step 3 (.step 31 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part732
namespace Part733
def root : Box := ⟨6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028293262540800, 5789239652048016513675281083586777588851254951208637561876207408426283109609938048420162773659806877390964270872365977531266300210326742455199066377292761956731434281862071012488475443691630545976136990160391647230090544129⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 15 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 28 0 (.split 13 0 (.split 25 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 42 0 (.split 35 1 (.split 12 1 (.step 2 (.step 40 (.step 2 (.run (.close 57))))) (.step 57 (.step 2 (.step 40 (.step 2 (.run (.close 15))))))) (.step 57 (.step 40 (.step 2 (.step 66 (.step 2 (.run (.close 15)))))))) (.step 3 (.step 26 (.step 55 (.run (.close 2)))))) (.step 2 (.step 57 (.run (.close 55))))) (.step 3 (.split 35 1 (.split 12 1 (.split 54 1 (.step 2 (.step 48 (.step 57 (.step 2 (.run (.close 55)))))) (.step 57 (.run (.close 2)))) (.step 57 (.step 2 (.run (.close 15))))) (.step 57 (.step 48 (.step 29 (.step 55 (.run (.close 2))))))))) (.step 3 (.split 35 1 (.split 72 1 (.split 12 1 (.split 36 0 (.step 2 (.step 55 (.run (.close 2)))) (.step 51 (.split 9 0 (.step 55 (.run (.close 2))) (.step 2 (.run (.close 15)))))) (.step 66 (.run (.close 2)))) (.step 48 (.step 66 (.step 55 (.run (.close 2)))))) (.step 57 (.step 48 (.step 66 (.step 29 (.step 55 (.run (.close 2)))))))))) (.step 2 (.run (.close 29)))) (.step 2 (.step 48 (.run (.close 55))))) (.step 2 (.step 55 (.run (.close 31))))) (.step 40 (.step 3 (.split 21 0 (.step 2 (.step 48 (.step 9 (.step 57 (.run (.close 55)))))) (.step 40 (.run (.close 2))))))) (.step 40 (.step 3 (.step 51 (.step 2 (.step 40 (.run (.close 2)))))))) (.step 40 (.step 3 (.split 21 0 (.split 5 0 (.split 11 0 (.split 17 0 (.split 22 0 (.step 2 (.step 48 (.step 9 (.step 57 (.run (.close 55)))))) (.step 40 (.run (.close 2)))) (.step 23 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 9)))) (.step 40 (.run (.close 2))))))) (.step 2 (.run (.close 55))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part733
namespace Part734
def root : Box := ⟨6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028293262540800, 5789239652048016513685078850208092273725150656063702138820596558038806853098856690767202671142866365421663094290071268792104887043195690049134240410566366501599371709562970658481019207608030923745149398989832551871418467329⟩
def references : Fin 1 → Box := ![Part733.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.reuse 0) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 9 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 3 (.step 55 (.run (.close 2))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 40 (.step 55 (.step 3 (.step 31 (.step 69 (.split 12 1 (.split 35 1 (.split 54 1 (.split 12 0 (.step 2 (.run (.close 57))) (.step 48 (.step 9 (.step 66 (.run (.close 2)))))) (.step 57 (.run (.close 2)))) (.step 48 (.run (.close 31)))) (.step 57 (.step 66 (.step 55 (.run (.close 2)))))))))))) (.step 40 (.step 55 (.step 3 (.step 31 (.step 51 (.split 12 1 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.split 12 0 (.split 25 0 (.split 26 0 (.step 55 (.run (.close 2))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 29)))) (.step 57 (.step 48 (.step 9 (.step 66 (.run (.close 2))))))) (.step 2 (.run (.close 31)))) (.step 48 (.run (.close 31)))) (.step 31 (.run (.close 2)))) (.step 48 (.step 29 (.run (.close 31))))) (.step 48 (.step 55 (.run (.close 15))))))))))) (.step 55 (.step 3 (.split 35 1 (.split 36 1 (.split 42 1 (.split 54 1 (.split 72 1 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 57))) (.step 48 (.run (.close 31)))) (.step 66 (.run (.close 2)))) (.step 48 (.run (.close 31)))) (.step 57 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.run (.close 37)))) (.step 48 (.step 31 (.run (.close 26)))))))) (.step 55 (.step 23 (.step 3 (.run (.close 2)))))) (.step 55 (.step 23 (.step 3 (.run (.close 2))))))
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
def root : Box := ⟨2147483648, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580374782999197367709641956906662272606491377218181905166084490405217963099481112027595777⟩
def references : Fin 7 → Box := ![Part670.root, Part691.root, Part708.root, Part724.root, Part731.root, Part732.root, Part734.root]
def proof : Chunks.Proof 7 := (.split 52 1 (.split 65 1 (.split 4 1 (.split 10 1 (.split 30 1 (.split 43 1 (.reuse 0) (.split 21 1 (.split 40 1 (.split 9 1 (.reuse 1) (.step 3 (.split 12 1 (.split 35 1 (.split 54 1 (.split 72 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 2 (.run (.close 9))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))))) (.step 9 (.step 3 (.step 31 (.step 2 (.run (.close 27))))))) (.step 68 (.step 18 (.step 9 (.run (.close 2))))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.step 2 (.step 3 (.split 16 1 (.split 17 1 (.split 22 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 34 1 (.split 36 1 (.reuse 5) (.step 3 (.step 31 (.step 2 (.run (.close 69)))))) (.step 3 (.step 31 (.step 2 (.run (.close 69)))))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 55 (.run (.close 2)))) (.step 68 (.step 3 (.run (.close 2))))) (.step 68 (.step 3 (.run (.close 2))))) (.step 68 (.step 3 (.run (.close 2)))))))) (.step 2 (.split 21 1 (.split 16 1 (.reuse 6) (.step 55 (.step 23 (.step 3 (.step 2 (.run (.close 55))))))) (.step 68 (.step 55 (.step 23 (.step 2 (.run (.close 57)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part670.covered
  · exact Part691.covered
  · exact Part708.covered
  · exact Part724.covered
  · exact Part731.covered
  · exact Part732.covered
  · exact Part734.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part735
namespace Part736
def root : Box := ⟨3885337784451458141838923813647037813284813678104279042503624819477808570412564480000, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962375882734687357856369587565805557688551272893464843031876936537542517759028889042792055761001872178021377⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 4 0 (.split 10 0 (.split 12 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 35 0 (.split 43 0 (.step 2 (.run (.close 57))) (.step 3 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.split 1 0 (.split 9 0 (.split 21 0 (.step 31 (.split 24 0 (.split 26 0 (.split 27 0 (.split 29 0 (.split 31 0 (.step 9 (.step 57 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57))))) (.step 48 (.run (.close 31)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57))))) (.step 3 (.step 2 (.step 21 (.step 2 (.run (.close 57))))))) (.step 3 (.step 12 (.step 2 (.step 21 (.step 2 (.run (.close 57)))))))) (.step 31 (.step 2 (.step 9 (.run (.close 62)))))) (.step 31 (.step 2 (.step 57 (.run (.close 2)))))) (.step 31 (.step 2 (.run (.close 52))))) (.step 3 (.step 2 (.run (.close 57))))) (.step 3 (.step 2 (.run (.close 57))))) (.step 3 (.step 2 (.run (.close 57))))) (.step 3 (.step 2 (.run (.close 57))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 12 (.split 50 1 (.step 31 (.split 21 0 (.split 27 0 (.split 29 0 (.split 31 0 (.step 9 (.step 57 (.step 2 (.step 3 (.run (.close 2)))))) (.step 2 (.run (.close 15)))) (.step 2 (.run (.close 15)))) (.step 2 (.run (.close 7)))) (.step 9 (.run (.close 31))))) (.step 9 (.step 15 (.run (.close 2)))))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31)))) (.step 3 (.run (.close 31))))) (.step 3 (.step 2 (.run (.close 31))))) (.step 2 (.step 7 (.step 57 (.run (.close 3))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part736
namespace Part737
def root : Box := ⟨3213876088517980551083924184682325205044405987565587818086400, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962375882734687357856367644896913331959480353433164957557229284406245427711848799832904519850499459804824577⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 10 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 28 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 27 0 (.split 32 0 (.split 43 0 (.split 51 0 (.split 12 1 (.split 54 1 (.split 49 1 (.step 2 (.step 55 (.run (.close 2)))) (.step 55 (.step 2 (.run (.close 34))))) (.step 57 (.step 2 (.run (.close 57))))) (.step 15 (.step 2 (.run (.close 15))))) (.split 12 1 (.split 54 1 (.split 14 0 (.split 35 0 (.split 72 0 (.step 2 (.step 57 (.step 2 (.run (.close 3))))) (.step 5 (.step 9 (.run (.close 55))))) (.step 5 (.step 9 (.run (.close 55))))) (.step 2 (.run (.close 23)))) (.step 57 (.run (.close 2)))) (.step 57 (.step 40 (.step 2 (.run (.close 15))))))) (.step 18 (.step 9 (.split 12 0 (.step 2 (.run (.close 9))) (.step 27 (.run (.close 2))))))) (.step 2 (.step 4 (.run (.close 23))))) (.step 2 (.run (.close 27)))) (.step 55 (.step 18 (.step 2 (.step 57 (.step 2 (.run (.close 15)))))))) (.step 55 (.step 18 (.split 12 1 (.step 2 (.step 5 (.step 74 (.run (.close 2))))) (.step 57 (.step 2 (.run (.close 15)))))))) (.step 55 (.step 18 (.split 54 1 (.split 12 0 (.step 2 (.run (.close 57))) (.step 40 (.run (.close 2)))) (.step 57 (.run (.close 2))))))) (.step 2 (.step 57 (.step 40 (.step 15 (.run (.close 3))))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2))))) (.step 18 (.step 23 (.run (.close 2)))))
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
def root : Box := ⟨3213876088517980551083924184682325205044405987565587818086400, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580376725668089593438712876370176034169657009900562919397946904820149904997549110071395329⟩
def references : Fin 1 → Box := ![Part737.root]
def proof : Chunks.Proof 1 := (.step 2 (.step 18 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.split 67 1 (.split 35 1 (.split 72 1 (.reuse 0) (.step 57 (.step 40 (.step 15 (.split 5 0 (.split 8 0 (.split 4 0 (.step 69 (.split 10 0 (.step 26 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 57))) (.step 74 (.step 2 (.run (.close 7))))) (.step 24 (.run (.close 2))))) (.step 15 (.step 24 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))))))) (.step 57 (.step 40 (.step 15 (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 4 0 (.step 21 (.split 17 0 (.split 21 0 (.split 22 0 (.split 53 0 (.step 9 (.step 75 (.split 10 0 (.step 2 (.run (.close 57))) (.step 66 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 5)))) (.step 23 (.run (.close 2)))) (.step 23 (.run (.close 2)))) (.step 74 (.step 24 (.step 2 (.run (.close 66))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))))))) (.step 3 (.step 18 (.step 2 (.run (.close 26)))))) (.step 3 (.step 18 (.split 49 1 (.step 2 (.run (.close 26))) (.step 27 (.step 2 (.run (.close 26)))))))) (.step 9 (.step 3 (.step 18 (.step 2 (.run (.close 9))))))) (.step 18 (.step 31 (.run (.close 2))))) (.step 18 (.step 31 (.step 2 (.run (.close 26)))))) (.step 18 (.step 31 (.step 2 (.run (.close 26))))))))
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
def root : Box := ⟨2147483648, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580376725668089593438712876370176034169657011327810612103906785878435874447044246454141953⟩
def references : Fin 3 → Box := ![Part735.root, Part736.root, Part738.root]
def proof : Chunks.Proof 3 := (.split 15 1 (.split 20 1 (.split 28 1 (.reuse 0) (.step 2 (.step 3 (.step 18 (.step 31 (.split 21 1 (.split 35 1 (.split 72 1 (.reuse 1) (.step 31 (.step 29 (.step 9 (.step 15 (.step 31 (.run (.close 75)))))))) (.step 31 (.step 29 (.step 21 (.step 75 (.step 9 (.step 57 (.step 55 (.step 15 (.run (.close 38))))))))))) (.step 3 (.step 31 (.run (.close 2)))))))))) (.reuse 2)) (.step 2 (.step 3 (.step 18 (.step 31 (.split 35 1 (.split 72 1 (.split 10 0 (.split 12 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 49 1 (.split 50 1 (.split 59 1 (.split 43 0 (.step 2 (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.step 2 (.run (.close 57))))) (.step 3 (.step 18 (.run (.close 2))))) (.step 3 (.step 12 (.step 2 (.step 18 (.run (.close 2))))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 18))))) (.step 18 (.step 2 (.run (.close 18))))) (.step 18 (.step 2 (.run (.close 18))))) (.step 18 (.step 2 (.run (.close 18))))) (.step 3 (.step 12 (.split 50 1 (.step 31 (.split 59 1 (.split 16 0 (.split 17 0 (.split 35 0 (.step 2 (.run (.close 57))) (.step 18 (.run (.close 2)))) (.step 24 (.run (.close 15)))) (.step 24 (.run (.close 15)))) (.step 18 (.run (.close 2))))) (.step 18 (.run (.close 2))))))) (.step 3 (.run (.close 2)))) (.step 18 (.step 2 (.step 18 (.run (.close 2)))))) (.step 18 (.step 31 (.run (.close 2))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part735.covered
  · exact Part736.covered
  · exact Part738.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part739
namespace Part740
def root : Box := ⟨2149580800, 5789239652048016513685078850208092273725150656063702138820596558035374450992204107498046274685198508736872857268007349956329714566246942797909582005809081919174364206709972332542545518782895827577145198236246614849540326401⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 59 1 (.split 12 1 (.split 35 1 (.split 54 1 (.split 72 1 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 60))) (.step 3 (.step 2 (.run (.close 57))))) (.step 3 (.split 12 0 (.step 2 (.run (.close 57))) (.step 5 (.run (.close 2)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 4 (.split 12 0 (.split 34 0 (.step 2 (.run (.close 57))) (.step 5 (.run (.close 2)))) (.step 40 (.run (.close 2)))))) (.step 4 (.split 72 1 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 57))) (.step 57 (.run (.close 2)))) (.step 57 (.run (.close 2)))) (.step 57 (.run (.close 2)))))) (.step 4 (.split 54 1 (.split 72 1 (.split 12 0 (.split 34 0 (.step 2 (.run (.close 57))) (.step 5 (.run (.close 2)))) (.step 40 (.run (.close 2)))) (.step 40 (.step 2 (.run (.close 57))))) (.step 57 (.run (.close 2)))))) (.step 57 (.step 4 (.split 35 1 (.split 72 1 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 76))) (.step 57 (.step 2 (.run (.close 76))))) (.step 5 (.run (.close 2)))) (.step 76 (.step 40 (.run (.close 2))))) (.step 40 (.step 2 (.step 76 (.step 2 (.run (.close 57)))))))))) (.step 57 (.step 40 (.step 15 (.step 3 (.split 34 0 (.split 36 0 (.step 2 (.run (.close 76))) (.step 57 (.step 2 (.run (.close 76))))) (.step 48 (.run (.close 5)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part740
namespace Part741
def root : Box := ⟨2147483650, 5789239652048016513680179966897434931288202801610039201480729640205475928693088644762563037135604952183596649732136769318740335664258499337001885623736157705863322137575315233626734354673844587182003101672332945425381196802⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 10 0 (.split 12 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 35 1 (.split 54 1 (.split 72 1 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 49 0 (.step 2 (.run (.close 57))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.split 9 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.step 9 (.split 34 0 (.step 3 (.step 2 (.run (.close 57)))) (.step 7 (.run (.close 3))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))))) (.step 31 (.split 43 0 (.split 51 0 (.split 67 0 (.step 2 (.step 21 (.step 2 (.run (.close 57))))) (.step 57 (.run (.close 3)))) (.step 57 (.run (.close 3)))) (.step 9 (.run (.close 2)))))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.step 3 (.run (.close 2)))) (.split 11 0 (.split 15 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 27 0 (.split 28 0 (.split 30 0 (.step 12 (.split 32 0 (.split 70 0 (.split 31 0 (.split 35 1 (.split 54 1 (.step 3 (.split 29 0 (.step 9 (.step 3 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 7))))) (.step 9 (.run (.close 57)))) (.step 15 (.run (.close 2)))) (.step 2 (.run (.close 15)))) (.step 2 (.run (.close 15)))) (.step 2 (.run (.close 15))))) (.step 3 (.run (.close 15)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3)))) (.step 3 (.run (.close 15)))) (.step 3 (.run (.close 15)))) (.step 3 (.run (.close 15)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 3))))) (.step 3 (.step 2 (.run (.close 57)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part741
namespace Part742
def root : Box := ⟨2147483648, 11578468272786241545616291236884592186046821406069890777144820776595057818288623545755324973341865101326456170041518443063033461592470580376725668089593438712876370176034169657011327810612103906785878435874447044246455190530⟩
def references : Fin 3 → Box := ![Part739.root, Part740.root, Part741.root]
def proof : Chunks.Proof 3 := (.split 0 1 (.split 2 1 (.reuse 0) (.step 2 (.split 21 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.reuse 1) (.step 57 (.step 40 (.step 15 (.step 3 (.split 34 0 (.split 36 0 (.step 2 (.step 21 (.step 2 (.run (.close 76))))) (.step 57 (.step 2 (.step 76 (.step 2 (.run (.close 5))))))) (.step 48 (.run (.close 5))))))))) (.step 57 (.step 40 (.step 15 (.step 3 (.split 50 1 (.split 34 0 (.split 36 0 (.step 2 (.step 34 (.step 2 (.run (.close 76))))) (.step 57 (.step 2 (.step 76 (.step 2 (.run (.close 5))))))) (.step 48 (.run (.close 5)))) (.step 21 (.step 34 (.step 2 (.run (.close 52))))))))))) (.step 3 (.step 31 (.run (.close 2))))) (.step 3 (.step 31 (.step 2 (.run (.close 75)))))) (.step 3 (.step 31 (.step 2 (.run (.close 37)))))) (.step 23 (.step 3 (.run (.close 2))))) (.step 23 (.step 3 (.run (.close 2))))) (.step 23 (.step 3 (.run (.close 2))))) (.step 4 (.run (.close 2)))))) (.step 2 (.step 3 (.step 18 (.step 31 (.split 21 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 4 0 (.reuse 2) (.step 2 (.run (.close 3)))) (.step 3 (.step 26 (.step 62 (.run (.close 2)))))) (.step 3 (.step 21 (.step 53 (.run (.close 2)))))) (.step 3 (.step 62 (.step 53 (.step 12 (.step 2 (.step 9 (.step 57 (.run (.close 52)))))))))) (.step 7 (.step 3 (.run (.close 2))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part739.covered
  · exact Part740.covered
  · exact Part741.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part742
namespace Part743
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548544347594002730665403589693622580067872090437441801878784145623605487339218593353752485649529715117037626681896483690679511531899778234247572171857899510252072003364340711964235072317078590009353666823169⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 36 0 (.split 42 0 (.split 12 1 (.split 54 1 (.split 74 0 (.split 12 0 (.step 2 (.run (.close 9))) (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2))))) (.step 2 (.run (.close 57)))) (.step 22 (.split 25 0 (.step 36 (.split 35 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57)))))) (.step 2 (.run (.close 57)))))) (.step 57 (.step 22 (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 9))))))) (.split 12 1 (.split 54 1 (.split 37 0 (.split 2 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 49 0 (.split 19 0 (.split 56 0 (.step 68 (.step 22 (.step 2 (.run (.close 9))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 10 (.step 63 (.step 16 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 57 (.run (.close 2)))) (.step 10 (.step 57 (.step 2 (.run (.close 76))))))) (.split 12 1 (.split 54 1 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 71 (.run (.close 2))))) (.step 63 (.step 10 (.step 63 (.step 71 (.run (.close 2))))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 57 (.run (.close 2)))) (.step 57 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part743
namespace Part744
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548544347594002730665403589693622580067872090437441801878784145623605487339218593353752485649529715117039866426638663531927987977558658676042303334144676051368050221603586411755785330344271980359551783273473⟩
def references : Fin 1 → Box := ![Part743.root]
def proof : Chunks.Proof 1 := (.split 28 0 (.split 30 0 (.split 8 0 (.split 14 0 (.split 21 0 (.split 34 0 (.reuse 0) (.split 12 1 (.split 54 1 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 63 (.step 76 (.run (.close 2)))))) (.step 10 (.step 63 (.step 71 (.run (.close 2)))))) (.step 63 (.step 10 (.step 63 (.step 16 (.run (.close 2))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 57 (.run (.close 2)))) (.step 4 (.step 48 (.step 15 (.run (.close 2))))))) (.split 12 1 (.split 54 1 (.split 58 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 49 0 (.step 2 (.run (.close 57))) (.step 63 (.run (.close 2)))) (.step 10 (.step 2 (.run (.close 9))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 61)))) (.step 57 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 9)))) (.split 12 1 (.split 54 1 (.split 21 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 10 (.step 71 (.run (.close 2)))))) (.step 63 (.run (.close 2)))) (.step 57 (.run (.close 2)))) (.step 10 (.step 57 (.step 4 (.step 48 (.step 15 (.run (.close 2))))))))) (.step 2 (.step 57 (.run (.close 7)))))
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
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548544347594002730665403589693622580067872090437441801878784145623605487339218593353752485649529715117039866426638663531927987977558658676043988330811372967853256088310700629831664605404870861286951615464449⟩
def references : Fin 1 → Box := ![Part744.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.split 12 1 (.split 54 1 (.split 21 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 1 (.split 54 1 (.split 21 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 18 (.step 31 (.step 2 (.run (.close 30)))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 1 (.split 54 1 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 18 (.step 31 (.step 2 (.run (.close 30)))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 18 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10))))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
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
def root : Box := ⟨10273712730478288321014932260701054103182216471852576688064502355637218721502218613791246182490782561567120478552402531718583362569289249374320683309372211370623667857425009927596934527626390497960489274834944, 5789234136395758548549246477313388007840537544023981707476612669224423744745379039156103659584909903998100061338523999249550179228388655849129955383162403118573373532751260630691900686833915709852881259385436084544077825025⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 44 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 37 0 (.split 40 0 (.split 42 0 (.split 45 0 (.split 55 0 (.split 72 0 (.split 12 1 (.split 54 1 (.split 9 0 (.step 72 (.run (.close 70))) (.step 2 (.run (.close 70)))) (.step 57 (.run (.close 2)))) (.step 10 (.step 57 (.step 2 (.run (.close 76)))))) (.step 10 (.step 76 (.run (.close 2))))) (.step 2 (.run (.close 72)))) (.step 2 (.run (.close 72)))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 70)))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 57))))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 57))))))) (.step 2 (.step 57 (.run (.close 71))))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 10 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 2 (.run (.close 70)))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 70)))) (.step 2 (.step 48 (.step 58 (.run (.close 3)))))) (.step 2 (.step 48 (.step 58 (.run (.close 3)))))) (.step 2 (.run (.close 72)))) (.step 2 (.step 68 (.run (.close 70))))) (.step 2 (.run (.close 72)))) (.step 2 (.step 30 (.step 10 (.run (.close 48))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part746
namespace Part747
def root : Box := ⟨10273702932711667006330058365000251299903007427389011451036483853777416038648498479793678017406847854098897799909003803331623093650413730321108662307381168630084725325915768782720034683091102780387321282822144, 5789234136395758548549246477313388007840537544023981707476612669224427096697361524805378553091159455459631931179979147347894610118749586290137473769906603587147915258608183138656447308346629148323584246027922692956329346049⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.step 57 (.split 44 0 (.split 48 0 (.split 63 0 (.split 64 0 (.split 66 0 (.split 67 1 (.split 8 0 (.split 11 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 26 0 (.split 35 0 (.split 36 0 (.split 37 0 (.split 42 0 (.split 72 0 (.split 1 0 (.split 9 0 (.step 72 (.step 22 (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 57)))) (.step 57 (.run (.close 2)))) (.step 57 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 10 (.step 57 (.run (.close 2))))) (.step 57 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 30 (.step 61 (.step 2 (.run (.close 7)))))) (.step 57 (.step 68 (.run (.close 2))))) (.step 2 (.run (.close 22)))) (.step 61 (.run (.close 72)))) (.step 30 (.step 61 (.step 68 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 72)))) (.step 2 (.run (.close 54)))) (.step 72 (.run (.close 70)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part747
namespace Part748
def root : Box := ⟨10273702932711667006330058365008355822498478116761105990941351687929188672908834490261058971889217000074991947270660009300715890711859378417459210077801320314512959856320959908253472112444109177880265353068544, 5789234136395758548544347594002730665403589697674841365607431524358039548612938936707296079853432470543395672497031381445596221554776089765348614605263052501666340723672509221964434153018921154457033316227426883825510122496⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 65 0 (.split 66 0 (.split 71 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 37 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 53 0 (.step 62 (.split 12 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57)))))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 9 (.step 57 (.run (.close 2))))) (.step 9 (.step 57 (.step 76 (.step 4 (.run (.close 7))))))) (.step 2 (.step 73 (.run (.close 4))))) (.step 2 (.step 57 (.run (.close 62))))) (.step 2 (.run (.close 9)))) (.step 2 (.step 76 (.run (.close 4))))) (.step 2 (.step 76 (.run (.close 4))))) (.step 2 (.step 27 (.run (.close 57))))) (.step 2 (.step 73 (.run (.close 4))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.run (.close 26)))) (.step 2 (.run (.close 22)))) (.step 2 (.step 57 (.run (.close 62))))) (.step 2 (.step 76 (.run (.close 58))))) (.step 61 (.step 73 (.step 4 (.run (.close 2)))))) (.step 73 (.step 9 (.step 4 (.run (.close 2)))))) (.step 61 (.step 73 (.step 4 (.run (.close 2)))))) (.step 61 (.step 73 (.step 4 (.run (.close 2)))))) (.step 2 (.step 61 (.step 73 (.run (.close 4)))))) (.step 2 (.step 9 (.run (.close 7))))) (.step 2 (.run (.close 62)))) (.step 2 (.step 76 (.run (.close 48))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 2 (.step 57 (.run (.close 7))))) (.step 2 (.step 48 (.run (.close 3)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part748
namespace Part749
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548549246477313388007840537548076243005211957355271700401083261086340970576765414240611641042206007283493312721837213501277543522879474852230996342194540947860738259132454905353513001909173608047840615990273⟩
def references : Fin 4 → Box := ![Part745.root, Part746.root, Part747.root, Part748.root]
def proof : Chunks.Proof 4 := (.split 59 1 (.split 51 1 (.split 67 1 (.split 4 0 (.split 10 0 (.reuse 0) (.split 54 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 24 0 (.split 12 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 16 (.step 10 (.step 2 (.run (.close 57))))))) (.step 18 (.step 2 (.run (.close 10))))) (.step 63 (.step 10 (.step 63 (.step 16 (.step 71 (.run (.close 2)))))))) (.step 2 (.run (.close 4)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 68 (.step 2 (.run (.close 30)))))) (.step 10 (.step 57 (.run (.close 2)))))) (.step 2 (.step 7 (.run (.close 57))))) (.reuse 1)) (.reuse 2)) (.step 57 (.split 12 1 (.split 0 0 (.split 9 0 (.split 51 1 (.split 67 1 (.split 44 0 (.split 46 0 (.reuse 3) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 9 (.run (.close 48))))) (.step 73 (.step 76 (.step 62 (.run (.close 2)))))) (.step 57 (.step 61 (.step 62 (.step 2 (.run (.close 7))))))) (.step 2 (.step 62 (.run (.close 7))))) (.step 2 (.step 62 (.run (.close 7))))) (.step 57 (.step 76 (.step 4 (.step 15 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part745.covered
  · exact Part746.covered
  · exact Part747.covered
  · exact Part748.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part749
namespace Part750
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444339126670021909772601512360084410151971598227894787240626189664206933346206449591029938053408581263099370569600927863497861527790209588593277153834958848, 5789234136395758548544342805260491513021450370007460782169291015282449088452325930476913729224778973231970939908930806313400391097041343105513039894554065972389334907095759549205713646797916568286815930651547523179636327425⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 71 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 20 0 (.split 37 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 62 (.split 45 0 (.split 53 0 (.split 4 0 (.split 56 0 (.step 53 (.step 3 (.step 53 (.run (.close 2))))) (.step 2 (.run (.close 22)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53))))) (.step 2 (.run (.close 53)))) (.step 9 (.step 57 (.step 2 (.run (.close 76)))))) (.step 9 (.step 57 (.step 58 (.run (.close 2)))))) (.step 2 (.step 27 (.step 61 (.run (.close 4)))))) (.step 2 (.step 57 (.run (.close 53))))) (.step 2 (.step 9 (.run (.close 57))))) (.step 2 (.step 27 (.step 57 (.run (.close 4)))))) (.step 2 (.step 27 (.step 57 (.run (.close 4)))))) (.step 2 (.step 27 (.run (.close 53))))) (.step 2 (.step 27 (.step 57 (.run (.close 61)))))) (.step 2 (.step 27 (.step 61 (.run (.close 4)))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 9 (.step 57 (.run (.close 26)))))) (.step 2 (.step 9 (.run (.close 22))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 57 (.run (.close 58))))) (.step 61 (.step 4 (.step 30 (.step 2 (.run (.close 73))))))) (.step 61 (.step 4 (.step 30 (.step 2 (.run (.close 73))))))) (.step 61 (.step 4 (.step 30 (.step 2 (.run (.close 73))))))) (.step 61 (.step 4 (.step 30 (.step 2 (.step 73 (.run (.close 2)))))))) (.step 2 (.step 27 (.step 61 (.step 4 (.run (.close 73))))))) (.step 2 (.step 9 (.run (.close 7))))) (.step 2 (.step 48 (.run (.close 3)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part750
namespace Part751
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332586282147148536013575850201881570071759116931697288908140041024194391374961344800161519610828528816625731558227679996606783154572008989578804062060544, 5789234136395758548544347589326224576832423951892618400957967306524424305121500367999810954020071459801378375030049410735522215845159523273498660767824747888363802812415371316713841084789804612120934955847027736508078490625⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 66 0 (.split 71 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 20 0 (.split 37 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 62 (.split 45 0 (.split 53 0 (.step 53 (.split 4 0 (.split 32 0 (.split 56 0 (.step 52 (.step 3 (.step 52 (.run (.close 2))))) (.step 2 (.run (.close 22)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52))))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52))))) (.step 2 (.run (.close 52)))) (.step 9 (.step 57 (.step 2 (.run (.close 52)))))) (.step 58 (.run (.close 52)))) (.step 2 (.step 27 (.step 61 (.step 4 (.run (.close 73))))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 9 (.run (.close 72))))) (.step 2 (.step 27 (.step 57 (.run (.close 7)))))) (.step 2 (.step 27 (.step 57 (.run (.close 71)))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 57 (.run (.close 72))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 3 (.run (.close 52))))) (.step 2 (.step 57 (.run (.close 52))))) (.step 2 (.step 57 (.run (.close 52))))) (.step 2 (.step 57 (.run (.close 52))))) (.step 2 (.step 9 (.step 57 (.run (.close 58)))))) (.step 61 (.step 4 (.step 30 (.step 2 (.run (.close 62))))))) (.step 61 (.step 4 (.step 30 (.step 2 (.run (.close 52))))))) (.step 61 (.step 4 (.step 30 (.step 2 (.run (.close 52))))))) (.step 61 (.step 4 (.step 30 (.step 48 (.run (.close 2))))))) (.step 2 (.step 61 (.step 4 (.run (.close 7)))))) (.step 2 (.step 9 (.run (.close 72))))) (.step 2 (.step 63 (.run (.close 52))))) (.step 2 (.step 48 (.run (.close 52)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part751
namespace Part752
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789234136395758548549246477313388007840537548076243005211957355271700404359848364752636022823538693002548396719735894034466441778984646100333699944700847109269627969982120790092606037483296744575197182154592305322784719873⟩
def references : Fin 3 → Box := ![Part749.root, Part750.root, Part751.root]
def proof : Chunks.Proof 3 := (.split 49 1 (.split 50 1 (.reuse 0) (.split 12 1 (.split 9 0 (.split 51 1 (.split 67 1 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 65 0 (.split 66 0 (.reuse 1) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 57 (.run (.close 48))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 9 (.run (.close 48))))) (.step 72 (.step 53 (.run (.close 70))))) (.step 57 (.step 61 (.step 53 (.run (.close 2)))))) (.step 2 (.step 3 (.step 62 (.step 7 (.step 57 (.step 61 (.run (.close 53))))))))) (.step 9 (.step 57 (.step 4 (.step 15 (.step 2 (.run (.close 76))))))))) (.step 16 (.split 9 0 (.split 51 1 (.split 67 1 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 65 0 (.reuse 2) (.step 2 (.step 48 (.run (.close 52))))) (.step 2 (.step 63 (.run (.close 52))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 58 (.run (.close 52))))) (.step 2 (.step 57 (.step 48 (.run (.close 62)))))) (.step 2 (.step 58 (.run (.close 52))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 9 (.step 48 (.run (.close 62)))))) (.step 72 (.step 52 (.run (.close 70))))) (.step 57 (.step 61 (.step 52 (.run (.close 2)))))) (.step 3 (.run (.close 52))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part749.covered
  · exact Part750.covered
  · exact Part751.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part752
namespace Part753
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789239652048021650536545206041595438754333156189352090324310252541096620558735788968456151486313306505257045364207859554540342129485274344441836102982827640950863400436362590312503437009452909984165978579588609250450998273⟩
def references : Fin 1 → Box := ![Part752.root]
def proof : Chunks.Proof 1 := (.split 72 1 (.split 43 1 (.reuse 0) (.split 48 0 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 63 0 (.split 64 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.step 10 (.step 30 (.step 10 (.step 2 (.run (.close 7)))))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 72)))) (.step 72 (.run (.close 70)))) (.step 2 (.step 10 (.run (.close 7))))) (.step 2 (.step 10 (.run (.close 7))))) (.step 30 (.step 9 (.step 62 (.step 2 (.run (.close 7))))))) (.step 30 (.step 10 (.step 72 (.step 46 (.run (.close 2))))))) (.step 30 (.step 9 (.step 53 (.run (.close 46)))))) (.step 30 (.step 9 (.step 52 (.run (.close 46)))))) (.step 2 (.step 10 (.run (.close 46)))))) (.step 57 (.step 76 (.step 71 (.split 43 1 (.split 12 1 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 21 0 (.split 53 0 (.step 22 (.step 26 (.step 2 (.run (.close 9))))) (.step 2 (.run (.close 57)))) (.step 57 (.run (.close 4)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 9 (.step 57 (.step 2 (.run (.close 60)))))) (.step 9 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part752.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part753
namespace Part754
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789239652048021650536545206041595438754333156189352090324310252541096620558735788968456151486316014190505210222469168893140660349735923100844153100943958358982942039395711465215997768120847422780692518068229794915100394497⟩
def references : Fin 1 → Box := ![Part753.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 21 1 (.split 35 1 (.reuse 0) (.step 57 (.step 71 (.split 43 1 (.split 67 1 (.split 72 1 (.split 12 1 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 21 0 (.split 53 0 (.step 22 (.split 12 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57)))))) (.step 2 (.run (.close 57)))) (.step 57 (.run (.close 4)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 74)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 9 (.step 57 (.step 2 (.run (.close 60)))))) (.step 9 (.step 57 (.step 74 (.step 2 (.run (.close 76))))))) (.step 10 (.step 57 (.step 76 (.step 2 (.run (.close 74))))))) (.step 9 (.run (.close 2))))))) (.step 4 (.step 68 (.step 22 (.split 67 1 (.split 5 0 (.split 8 0 (.split 11 0 (.split 14 0 (.split 16 0 (.step 22 (.step 36 (.step 30 (.split 10 0 (.step 2 (.run (.close 73))) (.step 4 (.run (.close 2))))))) (.step 5 (.step 30 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 3)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 3)))) (.step 4 (.step 7 (.run (.close 2))))))))) (.step 76 (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 58 (.step 2 (.run (.close 10)))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 57 (.step 74 (.step 2 (.run (.close 76)))))))))))
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
def root : Box := ⟨10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170496779780096, 5789239652048021650536545206041595438754333156189352090324310252541096620558735788968456151486316014190505210222471517437963178925143653827974719204626046767026901901359036243225550084143705200529261771629853301339822490625⟩
def references : Fin 1 → Box := ![Part754.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 57 (.step 7 (.step 31 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 57 (.step 2 (.run (.close 10)))))) (.step 2 (.run (.close 7)))) (.step 57 (.step 43 (.step 10 (.step 2 (.run (.close 7))))))))))) (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 58 (.run (.close 16))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 57 (.step 74 (.step 2 (.run (.close 76))))))) (.step 7 (.run (.close 2)))) (.step 57 (.step 7 (.run (.close 2))))) (.step 57 (.step 58 (.run (.close 2)))))))) (.step 7 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 7 (.run (.close 2)))))))) (.step 7 (.step 18 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7))))))) (.step 7 (.step 18 (.split 22 1 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))))))
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
def root : Box := ⟨10032913020226237310869197622070557910061530690809581488606035047662224110216294903018315384440590765432325303757053790498770584583633048750167493382743608188543746320969475933440520778435368952317083648000, 5789239652048016518696636477010553586722801616697579454246839671657539977382005730129267115918007188844763452978460288180321099261251346609769561511207199172168901809737852003579951982631712976687961196162576443169366344705⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 59 1 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 21 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 35 1 (.split 72 1 (.split 34 0 (.split 36 0 (.step 2 (.split 42 0 (.step 2 (.run (.close 57))) (.step 4 (.step 48 (.step 57 (.step 2 (.run (.close 15)))))))) (.step 18 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 57))))) (.step 71 (.step 2 (.run (.close 75))))) (.step 71 (.step 75 (.step 2 (.run (.close 38)))))) (.step 71 (.step 18 (.step 2 (.step 9 (.step 4 (.step 57 (.step 2 (.run (.close 15)))))))))) (.step 71 (.step 18 (.split 12 1 (.step 2 (.step 63 (.step 40 (.step 57 (.run (.close 2)))))) (.step 9 (.step 4 (.step 57 (.step 2 (.run (.close 76)))))))))) (.step 71 (.step 18 (.split 12 1 (.split 54 1 (.split 51 0 (.step 2 (.run (.close 9))) (.step 68 (.step 30 (.step 9 (.run (.close 2)))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2))))))) (.step 4 (.step 18 (.run (.close 2))))) (.step 71 (.step 18 (.run (.close 2))))) (.step 4 (.step 18 (.run (.close 2))))) (.step 4 (.step 18 (.run (.close 2))))) (.step 4 (.step 18 (.run (.close 2))))) (.step 71 (.step 18 (.run (.close 2))))) (.step 58 (.step 71 (.split 12 1 (.split 54 1 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57))))) (.step 9 (.step 26 (.run (.close 2))))) (.step 57 (.run (.close 2)))) (.step 29 (.step 15 (.run (.close 2))))))))
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
def root : Box := ⟨10032913020226237310869197622070557910061530690809581488606035047662224110216294903018315384440590765432325303757053790498770584583633048750167493382743608188543746320969475933440520778435368952317083648000, 5789239652048016518701535360321210929159749467098981093851361903440161846619826424091548882342448191481285219300997780931158571792747615353701716400936921125027230306557317710370111263793390244670781723429906095647782601729⟩
def references : Fin 1 → Box := ![Part756.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 49 1 (.split 50 1 (.reuse 0) (.step 58 (.step 71 (.split 12 1 (.split 59 1 (.split 54 1 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57))))) (.step 9 (.step 21 (.step 2 (.run (.close 57)))))) (.step 57 (.run (.close 2)))) (.step 62 (.run (.close 2)))) (.step 29 (.step 15 (.step 2 (.run (.close 76))))))))) (.step 58 (.step 71 (.split 50 1 (.split 59 1 (.split 54 1 (.split 12 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57))))) (.step 4 (.step 66 (.step 52 (.run (.close 2)))))) (.step 57 (.run (.close 2)))) (.step 62 (.run (.close 2)))) (.step 53 (.run (.close 2))))))) (.step 68 (.step 71 (.step 3 (.step 18 (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 1 (.split 54 1 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 76)))) (.step 9 (.step 76 (.run (.close 2))))) (.step 2 (.run (.close 3)))) (.step 57 (.run (.close 2)))) (.step 9 (.step 57 (.step 76 (.step 2 (.run (.close 57))))))) (.step 76 (.run (.close 2)))) (.step 71 (.run (.close 53)))) (.step 71 (.run (.close 52)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part756.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part757
namespace Part758
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411692881238169227504725489630651886188833483331013902707578228040966588423325449388512714778327344788206290376841701263508513612230988610479534736220285051163924971904370119328768639929606604011114224157697⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 36 0 (.split 42 0 (.split 12 1 (.split 54 1 (.split 74 0 (.split 12 0 (.step 2 (.run (.close 9))) (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2))))) (.step 2 (.run (.close 73)))) (.step 21 (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2)))))) (.step 21 (.split 51 0 (.step 2 (.step 4 (.step 9 (.step 2 (.run (.close 57)))))) (.step 10 (.step 2 (.step 57 (.run (.close 2)))))))) (.split 12 1 (.split 54 1 (.split 39 0 (.split 58 0 (.split 74 0 (.split 49 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 63 (.step 16 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 10 (.step 76 (.step 2 (.run (.close 57)))))) (.step 10 (.step 57 (.step 76 (.step 2 (.run (.close 57)))))))) (.split 12 1 (.split 54 1 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 71 (.run (.close 2))))) (.step 63 (.step 10 (.step 16 (.step 71 (.run (.close 2))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.step 57 (.run (.close 2)))))) (.step 4 (.step 48 (.step 15 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part758
namespace Part759
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113518653435059108788748941081126765246263006878879241268362403314697085922666845837324164530176, 5789234136395753411692881238169227504725489630651886188833483331013902707578228040966588423325449388512714778327344788208530121583881104755047388997643323203346436600238073373260783304563679599067084338135270461477957403649⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 12 1 (.split 54 1 (.split 55 0 (.split 21 0 (.split 24 0 (.split 37 0 (.split 1 0 (.split 5 0 (.split 6 0 (.split 8 0 (.split 11 0 (.split 12 0 (.split 14 0 (.split 34 0 (.split 52 0 (.split 39 0 (.split 58 0 (.split 74 0 (.split 9 0 (.split 36 0 (.split 42 0 (.split 44 0 (.split 46 0 (.split 48 0 (.split 53 0 (.split 56 0 (.split 57 0 (.split 63 0 (.split 66 0 (.split 71 0 (.split 7 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 26 0 (.step 65 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 9)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 63 (.step 10 (.step 71 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 10 (.step 4 (.step 48 (.step 57 (.step 2 (.run (.close 57)))))))) (.step 10 (.step 4 (.step 48 (.step 15 (.step 16 (.step 2 (.run (.close 76)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part759
namespace Part760
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411692881238169227504725489630651886188833483331013902707578228040966588423325449388512714778327344788208530121583881104756990057889869052275950896780696551526060154128516638378583820796485954309544976843777⟩
def references : Fin 2 → Box := ![Part758.root, Part759.root]
def proof : Chunks.Proof 2 := (.split 20 0 (.split 22 0 (.split 28 0 (.split 30 0 (.split 14 0 (.split 21 0 (.split 34 0 (.reuse 0) (.split 12 1 (.split 54 1 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 63 (.step 76 (.run (.close 2)))))) (.step 10 (.step 63 (.step 71 (.run (.close 2)))))) (.step 63 (.step 10 (.step 16 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.step 57 (.run (.close 2)))))) (.step 4 (.step 48 (.step 15 (.run (.close 2))))))) (.split 12 1 (.split 54 1 (.split 58 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 35 0 (.step 2 (.run (.close 57))) (.step 63 (.run (.close 2)))) (.step 10 (.step 2 (.run (.close 9))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.reuse 1)) (.step 2 (.step 9 (.step 57 (.run (.close 31)))))) (.split 12 1 (.split 54 1 (.split 21 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 2 (.step 10 (.run (.close 4)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part758.covered
  · exact Part759.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part760
namespace Part761
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411692881238169227504725489630651886188833483331013902707578228040966588423325449388512714778327344788208530121583881104756990057889869052275950896780696553024099332392692129537360774330676049456875833394177⟩
def references : Fin 1 → Box := ![Part760.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.reuse 0) (.split 12 1 (.split 54 1 (.split 21 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 18 (.step 31 (.step 2 (.run (.close 30)))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 1 (.split 54 1 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 18 (.step 31 (.step 2 (.run (.close 30)))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 18 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10))))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
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
def root : Box := ⟨9797766621314693576060575112715424139257639720889722090520471940923670432325860766640748377820909457805942292966864241366729951670126784608441310858540965357200084378338928088982049939773290610476187648, 5789234136395753411697780121479884847162437481053287828438005562796524573539461456517204743691765938758329190136153670418213874173606228678132035714372779350535939502074845801536572016518121375430108471160073749604678501377⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 44 0 (.split 48 0 (.split 63 0 (.split 66 0 (.split 71 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 37 0 (.split 42 0 (.split 72 0 (.split 12 1 (.split 54 1 (.split 9 0 (.step 65 (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 70)))) (.step 10 (.step 76 (.step 3 (.run (.close 65)))))) (.step 10 (.step 57 (.step 76 (.step 16 (.run (.close 2))))))) (.step 10 (.step 76 (.run (.close 2))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 26))))))) (.step 2 (.run (.close 70)))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 72))))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 21))))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 64))))))) (.step 2 (.step 10 (.step 76 (.step 58 (.run (.close 57))))))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 10 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 2 (.run (.close 70)))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 2 (.run (.close 70)))) (.step 2 (.run (.close 70)))) (.step 2 (.step 48 (.step 58 (.run (.close 3)))))) (.step 2 (.run (.close 70)))) (.step 2 (.step 48 (.step 58 (.run (.close 3)))))) (.step 2 (.step 68 (.run (.close 70))))) (.step 2 (.step 30 (.step 10 (.run (.close 48))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part762
namespace Part763
def root : Box := ⟨8702164874309912144930213176155652694072018612138240816712191863198475664443113441235127298894238477281097811076151073572587439319815800426414668575137194051189137514652055717442484174848, 5789234136395753411697780121479884847162437481053287828438005562796527925491443942166479637198015490219861059977608818516558305063967159119139554101116979819110481227931768309501118638030834813900811457802560358016930022401⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 44 0 (.split 48 0 (.split 63 0 (.split 66 0 (.split 67 1 (.split 71 0 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 20 0 (.split 21 0 (.split 22 0 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 37 0 (.split 42 0 (.split 72 0 (.split 12 1 (.split 54 1 (.split 9 0 (.step 65 (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 54)))) (.step 57 (.run (.close 2)))) (.step 10 (.step 57 (.step 16 (.run (.close 2)))))) (.step 10 (.step 57 (.step 7 (.step 2 (.step 57 (.step 2 (.run (.close 76))))))))) (.step 10 (.step 57 (.step 7 (.step 2 (.step 57 (.step 2 (.run (.close 76))))))))) (.step 2 (.run (.close 54)))) (.step 10 (.step 57 (.step 7 (.step 2 (.run (.close 22))))))) (.step 7 (.step 3 (.run (.close 53))))) (.step 10 (.step 57 (.step 7 (.step 2 (.run (.close 64))))))) (.step 2 (.run (.close 54)))) (.step 30 (.step 4 (.step 7 (.step 2 (.run (.close 57))))))) (.step 10 (.step 4 (.step 7 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 54)))) (.step 30 (.step 4 (.step 7 (.step 2 (.run (.close 57))))))) (.step 4 (.step 7 (.run (.close 65))))) (.step 2 (.run (.close 54)))) (.step 2 (.run (.close 54)))) (.step 2 (.step 48 (.run (.close 54))))) (.step 65 (.run (.close 70)))) (.step 2 (.step 68 (.run (.close 54))))) (.step 2 (.step 48 (.run (.close 54))))) (.step 2 (.run (.close 54)))) (.step 2 (.step 30 (.run (.close 54)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part763
namespace Part764
def root : Box := ⟨8702164882414434740400902548250192598939852763910875077048202330579430146812259417329274660550444446373894872521799169923135209739967484854649198980328319584626566867658453210386554421248, 5789234136395753411692881238169227504725489634704147486568824417930140377407021354071374295375003311127314831611770319186972431513368917369263678792317327257741384586940172936532681047240010108533526792817822277156916429824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 65 0 (.split 66 0 (.split 71 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 28 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 37 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 30 0 (.split 32 0 (.step 62 (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 4)))) (.step 58 (.step 7 (.run (.close 62))))) (.step 2 (.run (.close 62)))) (.step 9 (.step 76 (.step 58 (.run (.close 2)))))) (.step 9 (.step 76 (.step 58 (.run (.close 2)))))) (.step 2 (.step 73 (.run (.close 4))))) (.step 2 (.step 9 (.run (.close 62))))) (.step 2 (.run (.close 9)))) (.step 2 (.step 76 (.run (.close 4))))) (.step 2 (.step 76 (.run (.close 4))))) (.step 2 (.step 73 (.run (.close 4))))) (.step 2 (.step 73 (.run (.close 4))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 7 (.run (.close 9))))) (.step 2 (.step 9 (.run (.close 62))))) (.step 2 (.step 9 (.run (.close 21))))) (.step 2 (.step 76 (.run (.close 58))))) (.step 73 (.step 4 (.run (.close 62))))) (.step 73 (.step 9 (.step 4 (.run (.close 2)))))) (.step 73 (.step 4 (.step 2 (.run (.close 30)))))) (.step 73 (.step 4 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.step 4 (.run (.close 48))))) (.step 2 (.step 9 (.run (.close 7))))) (.step 2 (.run (.close 62)))) (.step 2 (.step 76 (.run (.close 48))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 48 (.run (.close 3)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part764
namespace Part765
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411697780121479884847162437485105549126173350248843801229877343503702071660872270275371870171003636954661976416782431074106545603210685228462958908163864533031582930462139111019090229120948245712901216666625⟩
def references : Fin 4 → Box := ![Part761.root, Part762.root, Part763.root, Part764.root]
def proof : Chunks.Proof 4 := (.split 59 1 (.split 51 1 (.split 67 1 (.split 15 0 (.split 4 0 (.split 10 0 (.reuse 0) (.split 54 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 16 (.step 10 (.step 2 (.run (.close 76))))))) (.step 18 (.step 2 (.run (.close 10))))) (.step 63 (.step 10 (.step 63 (.step 16 (.step 71 (.run (.close 2)))))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 68 (.step 2 (.run (.close 30)))))) (.step 10 (.step 4 (.step 48 (.step 15 (.step 71 (.step 2 (.run (.close 57)))))))))) (.step 2 (.step 7 (.run (.close 57))))) (.step 2 (.step 7 (.run (.close 57))))) (.reuse 1)) (.reuse 2)) (.split 12 1 (.split 54 1 (.split 0 0 (.split 9 0 (.split 51 1 (.split 67 1 (.split 44 0 (.reuse 3) (.step 2 (.step 9 (.run (.close 48))))) (.step 73 (.step 76 (.step 62 (.run (.close 2)))))) (.step 62 (.step 65 (.run (.close 54))))) (.step 2 (.step 62 (.run (.close 7))))) (.step 2 (.step 62 (.run (.close 7))))) (.step 9 (.step 57 (.step 76 (.step 4 (.run (.close 2))))))) (.step 9 (.step 76 (.step 4 (.step 15 (.step 2 (.run (.close 16)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part761.covered
  · exact Part762.covered
  · exact Part763.covered
  · exact Part764.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part765
namespace Part766
def root : Box := ⟨8702164874309912144930213176155645990174446981870738181789562271402028329354376274034616298030476169852395535623765552625444742767175986967420900887048407937937608995558264908925263413248, 5789234136395753411692881238169227504725489634704147486568824417930140380683608632483039744272341530297936602333795054290643863774051627376890028832114412685386889555341983858820819802907329471324322090276064087508622771201⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 65 0 (.split 66 0 (.split 71 0 (.split 5 0 (.step 53 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 62 (.split 30 0 (.split 35 0 (.split 12 0 (.split 42 0 (.split 50 0 (.step 2 (.run (.close 9))) (.step 53 (.run (.close 2)))) (.step 9 (.step 58 (.run (.close 2))))) (.step 9 (.step 16 (.run (.close 2))))) (.step 58 (.run (.close 53)))) (.step 7 (.run (.close 53))))) (.step 2 (.run (.close 52)))) (.step 9 (.step 4 (.step 58 (.run (.close 52)))))) (.step 9 (.step 58 (.step 2 (.step 76 (.run (.close 52))))))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 4 (.step 30 (.step 2 (.step 73 (.run (.close 62))))))) (.step 4 (.step 30 (.step 2 (.run (.close 52)))))) (.step 4 (.step 30 (.step 48 (.run (.close 2)))))) (.step 4 (.step 30 (.step 48 (.run (.close 2)))))) (.step 2 (.run (.close 64))))) (.step 2 (.step 27 (.step 9 (.run (.close 48)))))) (.step 2 (.step 63 (.run (.close 52))))) (.step 2 (.step 48 (.run (.close 52))))) (.step 2 (.step 63 (.run (.close 52))))) (.step 2 (.step 58 (.run (.close 52))))) (.step 2 (.step 63 (.run (.close 52))))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 52)))) (.step 2 (.step 9 (.step 48 (.run (.close 62))))))
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
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789234136395753411697780121479884847162437485105549126173350248843801233153930782113737106930394727762777525517365565203130136724202218929335780275911223341232193939305705960937277367167502410152424393929229970383385396225⟩
def references : Fin 2 → Box := ![Part765.root, Part766.root]
def proof : Chunks.Proof 2 := (.split 49 1 (.split 50 1 (.reuse 0) (.split 9 0 (.split 44 0 (.split 46 0 (.split 48 0 (.split 57 0 (.split 65 0 (.split 66 0 (.split 5 0 (.step 53 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 31 0 (.split 33 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 38 0 (.split 10 0 (.split 41 0 (.step 53 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 7 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 4 (.step 30 (.step 2 (.run (.close 73)))))) (.step 4 (.run (.close 65)))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 2 (.run (.close 53))))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 53))))) (.step 16 (.split 54 1 (.split 9 0 (.split 51 1 (.split 67 1 (.reuse 1) (.step 64 (.step 65 (.run (.close 70))))) (.step 52 (.step 65 (.run (.close 54))))) (.step 3 (.run (.close 52)))) (.step 57 (.step 3 (.run (.close 52)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part765.covered
  · exact Part766.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part767
namespace Part768
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789239652048016513685078850208092278076233093218658211285703146113197449352818206329557235593169341265486174161837533016702653064774358784264811736280144669478418538041071498746014153616534664046201260372779384436738229249⟩
def references : Fin 1 → Box := ![Part767.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 72 1 (.split 43 1 (.reuse 0) (.split 48 0 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 63 0 (.split 64 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.step 10 (.step 30 (.step 10 (.step 2 (.run (.close 7)))))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 2 (.step 10 (.run (.close 7))))) (.step 30 (.step 10 (.step 65 (.run (.close 2)))))) (.step 2 (.run (.close 65)))) (.step 2 (.step 10 (.run (.close 7))))) (.step 30 (.step 9 (.step 62 (.step 2 (.run (.close 7))))))) (.step 30 (.step 10 (.step 65 (.run (.close 46)))))) (.step 30 (.step 9 (.run (.close 53))))) (.step 30 (.step 9 (.step 53 (.step 52 (.run (.close 2))))))) (.step 2 (.step 10 (.run (.close 46)))))) (.step 76 (.step 71 (.split 43 1 (.split 51 1 (.split 12 1 (.split 54 1 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 21 0 (.split 53 0 (.step 21 (.step 26 (.step 2 (.run (.close 9))))) (.step 2 (.run (.close 57)))) (.step 73 (.run (.close 4)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 57 (.run (.close 2)))) (.step 4 (.run (.close 15)))) (.step 10 (.step 57 (.step 73 (.step 76 (.step 2 (.run (.close 7)))))))) (.step 9 (.run (.close 2))))))) (.step 71 (.step 21 (.step 4 (.step 10 (.step 63 (.run (.close 71))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part767.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part768
namespace Part769
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 5789239652048016513685078850208092278076233093218658211285703146113197449352818206329557235593172048950734339020101188604387129128181385410443022769181710273494416328590003927032201306830167696801383428841252228678733005825⟩
def references : Fin 1 → Box := ![Part768.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 21 1 (.reuse 0) (.step 4 (.step 68 (.split 51 1 (.split 67 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 30 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 5 (.run (.close 2))))) (.step 30 (.step 4 (.run (.close 2))))) (.step 5 (.step 2 (.run (.close 30))))) (.step 5 (.step 30 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 4)))) (.step 4 (.step 7 (.run (.close 2))))) (.step 4 (.step 7 (.run (.close 2)))))))) (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 76))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 2 (.run (.close 10)))))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 2))))))) (.step 7 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 76))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 2 (.run (.close 10)))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 76 (.step 4 (.step 2 (.run (.close 7))))))) (.step 7 (.run (.close 2)))) (.step 58 (.run (.close 41)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part768.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part769
namespace Part770
def root : Box := ⟨8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500617981132800, 11578468272786246687484214102831214010861685154385775756144406404583393723965612293065026974042849278350796658224387299648970855639296519196191654352862259491435906766184343990924104973524403382176643154684576355959156245506⟩
def references : Fin 1 → Box := ![Part769.root]
def proof : Chunks.Proof 1 := (.step 2 (.split 10 1 (.split 16 1 (.split 17 1 (.split 22 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 7 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 76))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 16))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 76 (.step 4 (.step 2 (.run (.close 7))))))) (.step 7 (.run (.close 2)))) (.step 7 (.step 2 (.run (.close 76))))) (.step 58 (.run (.close 41))))))) (.step 7 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 7))))) (.step 50 (.run (.close 2)))) (.step 7 (.run (.close 2)))))))) (.step 7 (.step 18 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7))))))) (.step 7 (.step 18 (.split 22 1 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2))))))) (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 42 (.step 35 (.step 8 (.step 68 (.run (.close 2))))))) (.step 7 (.run (.close 2))))))) (.step 7 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 30 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 30))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part769.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part770
namespace Part771
def root : Box := ⟨2147483648, 11578468272786246687484214102831214010861685154385775756144406404583393723965612293065026974042849278350796658224387299648970855639296519196191654352862259491435906766184343990924104973524403382176643154684576355959156245506⟩
def references : Fin 4 → Box := ![Part742.root, Part755.root, Part757.root, Part770.root]
def proof : Chunks.Proof 4 := (.split 62 1 (.split 68 1 (.split 69 1 (.reuse 0) (.step 2 (.split 10 1 (.split 16 1 (.reuse 1) (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 7 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 30 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 68 (.step 2 (.run (.close 30))))))))))) (.step 2 (.split 21 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.reuse 2) (.step 71 (.step 3 (.step 18 (.split 49 1 (.split 50 1 (.split 59 1 (.split 67 1 (.split 12 1 (.split 54 1 (.split 9 0 (.split 12 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.run (.close 2))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 2 (.run (.close 71)))) (.step 9 (.step 4 (.step 57 (.step 2 (.run (.close 76))))))) (.step 2 (.run (.close 3)))) (.step 57 (.run (.close 2)))) (.step 29 (.step 15 (.run (.close 2))))) (.step 3 (.run (.close 54)))) (.step 71 (.run (.close 62)))) (.step 71 (.run (.close 53)))) (.step 71 (.run (.close 52)))))))) (.step 9 (.step 68 (.step 18 (.step 30 (.step 9 (.step 3 (.run (.close 46))))))))) (.step 18 (.step 31 (.run (.close 2))))) (.step 18 (.step 31 (.step 2 (.run (.close 75)))))) (.step 18 (.step 31 (.step 2 (.run (.close 37)))))) (.step 4 (.run (.close 2)))))) (.reuse 3))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part742.covered
  · exact Part755.covered
  · exact Part757.covered
  · exact Part770.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part771
namespace Part772
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411692881238169227500378656297439464253157893448588499461512837965488559163861198561480612044426130033628984458303064789594323339715547246169938332527873339375587735940106460781622927331292739689351396459521⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 36 0 (.split 42 0 (.split 12 1 (.split 54 1 (.split 74 0 (.split 12 0 (.step 2 (.run (.close 9))) (.split 43 0 (.step 2 (.run (.close 57))) (.step 10 (.run (.close 2))))) (.step 2 (.run (.close 73)))) (.split 51 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 4 (.step 9 (.step 2 (.run (.close 57)))))) (.step 10 (.step 15 (.step 2 (.run (.close 57))))))) (.step 15 (.split 51 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 4 (.step 9 (.step 2 (.run (.close 76)))))) (.step 15 (.run (.close 2)))))) (.split 12 1 (.split 54 1 (.split 39 0 (.split 58 0 (.split 74 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 63 (.step 16 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 10 (.step 76 (.step 2 (.run (.close 57)))))) (.step 10 (.step 57 (.step 76 (.step 2 (.run (.close 57)))))))) (.split 12 1 (.split 54 1 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 71 (.run (.close 2))))) (.step 63 (.step 10 (.step 16 (.step 71 (.run (.close 2))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.step 57 (.run (.close 2)))))) (.step 4 (.step 48 (.run (.close 15))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part772
namespace Part773
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411692881238169227500378656297439464253157893448588499461512837965488559163861198561480612044426130033631224203045244630842799785374427687964669494814649880491565954179352160573173184149560310424920338203649⟩
def references : Fin 1 → Box := ![Part772.root]
def proof : Chunks.Proof 1 := (.split 28 0 (.split 30 0 (.split 14 0 (.split 21 0 (.split 34 0 (.reuse 0) (.split 12 1 (.split 54 1 (.split 24 0 (.split 39 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 10 (.step 63 (.step 76 (.run (.close 2)))))) (.step 10 (.step 63 (.step 71 (.run (.close 2)))))) (.step 63 (.step 10 (.step 16 (.run (.close 2)))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 48 (.run (.close 15))))) (.step 4 (.step 48 (.run (.close 15)))))) (.split 12 1 (.split 54 1 (.split 58 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 43 0 (.split 49 0 (.step 2 (.run (.close 57))) (.step 63 (.run (.close 2)))) (.step 10 (.step 2 (.run (.close 9))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.split 12 1 (.split 54 1 (.split 21 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 63 (.step 10 (.step 71 (.run (.close 2)))))) (.step 63 (.run (.close 2)))) (.step 10 (.step 4 (.step 48 (.step 57 (.step 2 (.run (.close 57)))))))) (.step 15 (.run (.close 2))))) (.step 2 (.step 9 (.step 57 (.run (.close 31))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part772.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part773
namespace Part774
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411692881238169227500378656297439464253157893448588499461512837965488559163861198561480612044426130033631224203045244630842799785374427687966354491481346796976771820886466378649052459210159191352320170394625⟩
def references : Fin 1 → Box := ![Part773.root]
def proof : Chunks.Proof 1 := (.split 16 0 (.split 17 0 (.split 22 0 (.reuse 0) (.split 12 1 (.split 54 1 (.split 21 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 1 (.split 54 1 (.split 21 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 18 (.step 31 (.step 2 (.run (.close 30)))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 1 (.split 54 1 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 35 0 (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.step 2 (.run (.close 30))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.run (.close 2)))) (.step 63 (.run (.close 2)))) (.step 18 (.step 31 (.step 2 (.run (.close 30)))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 18 (.step 31 (.split 5 0 (.split 8 0 (.split 9 0 (.step 68 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10))))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part773.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part774
namespace Part775
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411692881238169227500378656297439464253157893448588499461512837965488559163861198561480612044426130033631224203045244630842799785374427687966354491481346796976773248134159084610201168096356870250052767974401⟩
def references : Fin 1 → Box := ![Part774.root]
def proof : Chunks.Proof 1 := (.split 15 0 (.split 4 0 (.split 10 0 (.reuse 0) (.split 54 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 63 0 (.split 64 0 (.split 71 0 (.split 35 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 71 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 71 (.run (.close 2)))) (.step 68 (.step 16 (.step 10 (.step 2 (.run (.close 76))))))) (.step 18 (.step 2 (.run (.close 10))))) (.step 63 (.step 10 (.step 63 (.step 16 (.step 71 (.run (.close 2)))))))) (.step 63 (.step 2 (.run (.close 30))))) (.step 63 (.step 30 (.step 2 (.run (.close 7)))))) (.step 63 (.step 68 (.run (.close 2))))) (.step 63 (.step 68 (.step 2 (.run (.close 30)))))) (.step 10 (.step 48 (.step 15 (.step 71 (.step 2 (.run (.close 57))))))))) (.step 2 (.step 7 (.run (.close 57))))) (.step 2 (.step 7 (.run (.close 57)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part774.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part775
namespace Part776
def root : Box := ⟨8498207885068273579033411304846201941238461182182297783690209134270196640683932080515461816965529452717266045268344953394628721116288331759645562685692274572507273618339508331158175744, 5789234136395753411697780121479884842815604147840865892762415680371124679426053866688450377733764663187758326076394063939252386525330685204949281585675615509514075928582012262173607131805083925592496337285702253461267022849⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 48 0 (.split 64 0 (.split 67 1 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 12 1 (.split 54 1 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 7 (.step 52 (.run (.close 2))))) (.step 57 (.run (.close 2)))) (.step 15 (.run (.close 2)))) (.step 10 (.step 57 (.step 7 (.step 2 (.step 57 (.step 2 (.run (.close 76))))))))) (.step 10 (.step 57 (.step 7 (.step 2 (.run (.close 64))))))) (.step 10 (.step 57 (.step 7 (.step 2 (.run (.close 22))))))) (.step 10 (.step 7 (.step 15 (.step 3 (.run (.close 54))))))) (.step 10 (.step 57 (.step 7 (.step 2 (.run (.close 64))))))) (.step 30 (.step 4 (.step 7 (.step 2 (.run (.close 57))))))) (.step 10 (.step 4 (.step 7 (.step 2 (.run (.close 57))))))) (.step 30 (.step 4 (.step 7 (.step 2 (.run (.close 57))))))) (.step 30 (.step 4 (.step 7 (.step 2 (.run (.close 57))))))) (.step 64 (.run (.close 70)))) (.step 2 (.step 48 (.run (.close 54))))) (.step 2 (.run (.close 54))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part776
namespace Part777
def root : Box := ⟨8498215989590869049722783399386106809072612954816558119700676515224679009829908174662823473171498545514327490916441303942399141267972759994175967876817808009936626624737001275228422144, 5789234136395753411692881238169227500378656301491725550893234535504737131341631278593345038749966250874926513918851689172184225293644008639909579251447053497517198480551054882138961391653187191953811696778221725470791042049⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 63 0 (.split 64 0 (.split 65 0 (.split 66 0 (.split 71 0 (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 37 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.split 53 0 (.step 62 (.step 52 (.step 2 (.run (.close 9))))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 9 (.step 76 (.step 58 (.run (.close 2)))))) (.step 9 (.step 76 (.step 58 (.run (.close 2)))))) (.step 2 (.run (.close 64)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 9)))) (.step 2 (.step 76 (.run (.close 4))))) (.step 2 (.step 76 (.run (.close 4))))) (.step 2 (.step 73 (.run (.close 4))))) (.step 2 (.step 73 (.run (.close 4))))) (.step 2 (.step 3 (.run (.close 7))))) (.step 2 (.run (.close 26)))) (.step 2 (.step 9 (.run (.close 62))))) (.step 2 (.step 9 (.run (.close 62))))) (.step 2 (.run (.close 64)))) (.step 73 (.step 4 (.run (.close 62))))) (.step 73 (.step 9 (.step 4 (.run (.close 2)))))) (.step 73 (.step 4 (.step 2 (.run (.close 30)))))) (.step 73 (.step 4 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.step 4 (.run (.close 48))))) (.step 2 (.step 9 (.run (.close 7))))) (.step 2 (.run (.close 62)))) (.step 2 (.step 76 (.run (.close 48))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 2 (.run (.close 62)))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 9 (.run (.close 48)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part777
namespace Part778
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411697780121479884842815604151893127190497760366418397983811953428224042401408019448339767437102422200084670498243794600192355330695243864153362502864514776984255418955913360130781914000431387608345553667073⟩
def references : Fin 3 → Box := ![Part775.root, Part776.root, Part777.root]
def proof : Chunks.Proof 3 := (.split 59 1 (.split 51 1 (.split 67 1 (.reuse 0) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 12 1 (.split 54 1 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 10 (.step 2 (.run (.close 57))))) (.step 7 (.step 52 (.run (.close 2))))) (.step 10 (.step 76 (.step 15 (.step 2 (.run (.close 57))))))) (.step 15 (.run (.close 2)))) (.step 10 (.step 76 (.run (.close 2))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 15))))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 15))))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 15))))))) (.step 10 (.step 76 (.step 7 (.step 2 (.run (.close 15))))))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 10 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2))))))) (.step 30 (.step 73 (.step 4 (.step 7 (.run (.close 2)))))))) (.reuse 1)) (.step 15 (.split 54 1 (.split 9 0 (.split 51 1 (.split 67 1 (.reuse 2) (.step 73 (.step 76 (.step 62 (.run (.close 2)))))) (.step 62 (.step 64 (.run (.close 54))))) (.step 2 (.run (.close 52)))) (.step 9 (.step 57 (.step 76 (.step 4 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part775.covered
  · exact Part776.covered
  · exact Part777.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part778
namespace Part779
def root : Box := ⟨8498207885068273579033411304839504584054705675916250797570499866404761391057727969956179002826404762969822081129053782785729921210757617603920574780407416065614392104152398163710312448, 5789234131009374248507341978016777148544887415519438180969860686493332221558713553002056885355861130612726078952042942298193722765611876923715143703180721341312897810496537322395229420264954262716932295655173961822738842625⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 5 0 (.split 11 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 20 0 (.split 37 0 (.split 40 0 (.split 7 0 (.split 13 0 (.split 27 0 (.split 34 0 (.split 36 0 (.split 38 0 (.step 62 (.split 53 0 (.split 10 0 (.split 14 0 (.split 49 0 (.split 6 0 (.split 8 0 (.split 12 0 (.split 24 0 (.split 26 0 (.split 35 0 (.step 65 (.step 2 (.run (.close 9)))) (.step 9 (.step 58 (.run (.close 2))))) (.step 2 (.run (.close 29)))) (.step 2 (.run (.close 4)))) (.step 15 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 53 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 53 (.run (.close 2)))) (.step 2 (.run (.close 53))))) (.step 2 (.run (.close 53)))) (.step 4 (.step 58 (.run (.close 53))))) (.step 9 (.step 58 (.step 2 (.run (.close 53)))))) (.step 2 (.step 27 (.run (.close 53))))) (.step 2 (.run (.close 52)))) (.step 2 (.step 9 (.run (.close 76))))) (.step 2 (.step 27 (.run (.close 53))))) (.step 2 (.step 27 (.run (.close 53))))) (.step 2 (.step 27 (.run (.close 53))))) (.step 2 (.step 27 (.run (.close 53))))) (.step 2 (.step 27 (.run (.close 53))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 9 (.run (.close 53))))) (.step 2 (.step 9 (.run (.close 53))))) (.step 2 (.run (.close 53)))) (.step 2 (.step 9 (.run (.close 53))))) (.step 4 (.step 30 (.step 2 (.step 73 (.run (.close 62))))))) (.step 4 (.step 30 (.step 2 (.run (.close 53)))))) (.step 4 (.step 30 (.step 48 (.run (.close 2)))))) (.step 4 (.step 30 (.step 48 (.run (.close 2)))))) (.step 2 (.step 4 (.run (.close 48))))) (.step 2 (.step 9 (.run (.close 48)))))
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
def root : Box := ⟨8498207885068273579033411304839498043666830914679662861060617337822861551946764880004460953203222024014990592882824006251932168476474872765877874596906161320978754524548699813937414144, 5789234136395753411697780121479884842815604151893127190497760366418397987088540706635707847466143900730674791616150810625824218185565745015145507760469859031635788639955949913609765860941751521844109273412371865827722396673⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 44 0 (.split 47 0 (.split 48 0 (.split 57 0 (.split 65 0 (.split 66 0 (.split 5 0 (.split 11 0 (.step 52 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 25 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 31 0 (.split 33 0 (.split 40 0 (.split 7 0 (.split 27 0 (.split 38 0 (.split 53 0 (.split 10 0 (.split 32 0 (.step 52 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 7 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 4 (.step 30 (.step 2 (.run (.close 73)))))) (.step 4 (.step 30 (.step 2 (.run (.close 73)))))) (.step 4 (.step 48 (.run (.close 2))))) (.step 4 (.step 48 (.run (.close 2)))))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52)))) (.step 2 (.run (.close 52))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part780
namespace Part781
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789234136395753411697780121479884842815604151893127190497760366418397987088540706635707847468916570424795606475729224809967301889002182090521324335640338612250409947761575536649740267045891099941500484373775437656696554497⟩
def references : Fin 3 → Box := ![Part778.root, Part779.root, Part780.root]
def proof : Chunks.Proof 3 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.step 15 (.split 54 1 (.split 9 0 (.split 51 1 (.split 67 1 (.split 44 0 (.split 46 0 (.split 47 0 (.split 48 0 (.split 52 0 (.split 57 0 (.split 63 0 (.split 65 0 (.split 66 0 (.split 71 0 (.reuse 1) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.step 48 (.run (.close 3))))) (.step 2 (.run (.close 53)))) (.step 2 (.run (.close 52)))) (.step 2 (.step 9 (.run (.close 48))))) (.step 53 (.step 64 (.run (.close 70))))) (.step 53 (.step 64 (.run (.close 54))))) (.step 2 (.run (.close 52)))) (.step 57 (.step 3 (.run (.close 53))))))) (.reuse 2)) (.split 48 0 (.split 49 1 (.split 50 1 (.split 51 1 (.split 59 1 (.split 63 0 (.split 64 0 (.split 67 1 (.split 71 0 (.split 14 0 (.split 16 0 (.step 10 (.step 30 (.step 10 (.step 2 (.run (.close 7)))))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 2 (.step 10 (.run (.close 7))))) (.step 30 (.step 10 (.step 64 (.run (.close 2)))))) (.step 2 (.step 10 (.run (.close 7))))) (.step 2 (.run (.close 64)))) (.step 30 (.step 9 (.step 62 (.step 2 (.run (.close 7))))))) (.step 30 (.step 10 (.step 64 (.run (.close 46)))))) (.step 30 (.step 9 (.step 53 (.run (.close 46)))))) (.step 30 (.step 9 (.run (.close 52))))) (.step 2 (.step 10 (.run (.close 46))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part778.covered
  · exact Part779.covered
  · exact Part780.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part781
namespace Part782
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789239652048016513685078850208092273729399760006236275610113263687794203287428130851527976128918514233383440260622778439396734526137884870074539220838780359883658743248636657460657616573341126242868875721554859744423838721⟩
def references : Fin 1 → Box := ![Part781.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 35 1 (.split 72 1 (.reuse 0) (.step 76 (.step 15 (.step 71 (.split 43 1 (.split 51 1 (.split 54 1 (.split 5 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 11 0 (.split 21 0 (.split 53 0 (.step 26 (.split 12 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57)))))) (.step 2 (.run (.close 57)))) (.step 73 (.run (.close 4)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 57 (.run (.close 2)))) (.step 10 (.step 57 (.step 73 (.step 76 (.run (.close 2))))))) (.step 9 (.run (.close 2)))))))) (.step 15 (.step 71 (.split 43 1 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 21 0 (.split 12 0 (.split 27 0 (.split 32 0 (.split 34 0 (.step 2 (.run (.close 9))) (.step 9 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 63 (.run (.close 15))))) (.step 4 (.run (.close 2)))) (.step 57 (.run (.close 2)))) (.step 9 (.step 57 (.step 4 (.step 66 (.step 76 (.step 2 (.run (.close 57))))))))) (.step 57 (.step 76 (.step 58 (.run (.close 2)))))) (.step 57 (.step 58 (.step 2 (.run (.close 76)))))) (.step 9 (.run (.close 2))))))) (.step 4 (.step 68 (.split 51 1 (.split 67 1 (.split 16 0 (.split 17 0 (.step 34 (.step 30 (.split 10 0 (.split 22 0 (.step 2 (.run (.close 57))) (.step 73 (.step 2 (.run (.close 57))))) (.step 4 (.run (.close 2)))))) (.step 5 (.step 2 (.run (.close 30))))) (.step 5 (.step 30 (.step 2 (.run (.close 7)))))) (.step 4 (.step 7 (.run (.close 2))))) (.step 4 (.step 7 (.run (.close 2))))))))
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
def root : Box := ⟨8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291506655133696, 5789239652048016513685078850208092273729399760006236275610113263687794203287428130851527976128921221918631605118886434029320955331724752742786527020395058689393062571332863870165033280757571737224905161413820734169836160001⟩
def references : Fin 1 → Box := ![Part782.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.reuse 0) (.step 7 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 76))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 2 (.run (.close 10)))))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 2))))))) (.step 7 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 76))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.step 2 (.run (.close 10)))))) (.step 2 (.run (.close 7)))) (.step 9 (.step 76 (.step 4 (.step 2 (.run (.close 7))))))) (.step 7 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 76)))))))) (.step 7 (.step 15 (.step 31 (.split 36 1 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 71 (.step 10 (.step 2 (.run (.close 76))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 58 (.run (.close 16))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))))))) (.step 7 (.step 18 (.step 31 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 7))))) (.step 68 (.run (.close 2)))) (.step 7 (.run (.close 2)))))))) (.step 7 (.step 18 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))))))
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
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234136395753411692881238169227500374407193496930116368373147319817127971984660537395075310767018703612363386275542412330590066256964714392644744738420369333158646469180335181885758853746985519903776411158170616435049472⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 67 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 21 0 (.split 16 0 (.step 2 (.run (.close 57))) (.split 12 0 (.step 2 (.run (.close 57))) (.step 18 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 2 (.run (.close 57))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2))))) (.split 12 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.step 2 (.run (.close 57))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.step 2 (.run (.close 57))))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.step 2 (.run (.close 57))))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.step 2 (.run (.close 57))))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part784
namespace Part785
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234136395753411692881238169227500374407193496930116368373147319820479923967146186669968819789239859265048087309104694818104660054332230775979706653100418522321680131728466186406786470600002087997974015048350857660728320⟩
def references : Fin 1 → Box := ![Part784.root]
def proof : Chunks.Proof 1 := (.split 43 0 (.split 51 0 (.reuse 0) (.split 52 0 (.split 6 0 (.split 8 0 (.split 12 0 (.split 14 0 (.split 24 0 (.split 25 0 (.split 35 0 (.split 38 0 (.split 34 0 (.split 19 0 (.split 71 0 (.split 27 0 (.split 39 0 (.split 40 0 (.split 54 0 (.split 32 0 (.split 36 0 (.split 42 0 (.split 56 0 (.split 58 0 (.step 18 (.split 65 0 (.split 67 0 (.step 2 (.run (.close 57))) (.step 30 (.step 73 (.run (.close 2))))) (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 4 (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 7))))) (.split 12 0 (.split 35 0 (.split 51 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 68 0 (.split 64 0 (.split 58 0 (.split 61 0 (.split 62 0 (.step 24 (.split 67 0 (.step 2 (.run (.close 30))) (.step 30 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 3 (.step 30 (.step 2 (.run (.close 9)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
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
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789234136395753411692881238169227500374407193496930116368373147319820479923967146186669968819789239859265048087309104694818104660056369266752314192739368864210731058292779934580072722721236143805002955543041090160058958849⟩
def references : Fin 1 → Box := ![Part785.root]
def proof : Chunks.Proof 1 := (.split 0 0 (.split 4 0 (.split 10 0 (.split 30 0 (.reuse 0) (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 43 0 (.split 21 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 61))))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 24 (.run (.close 2)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 43 0 (.split 21 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 61))))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 24 (.run (.close 2)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 3 (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.step 8 (.step 14 (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 4 (.step 2 (.run (.close 30)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 3))))
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
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789239652048016513680179966897434931288202801610039201480729643720252330679960818833296246265278279425547523405509138928705626767256609236601784310486693726214696457205262859273777081800257482648444080111750984447845991425⟩
def references : Fin 1 → Box := ![Part786.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 35 1 (.split 54 1 (.split 72 1 (.split 22 1 (.reuse 0) (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 54 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 2 (.run (.close 57))) (.step 73 (.run (.close 2)))) (.step 73 (.step 2 (.run (.close 61))))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))) (.step 60 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 25)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 2))))) (.step 60 (.step 4 (.split 5 0 (.step 71 (.split 61 0 (.split 62 0 (.step 69 (.step 51 (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4))))))) (.step 57 (.step 4 (.step 48 (.step 24 (.split 12 0 (.split 16 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 57 (.run (.close 2))))))))) (.step 57 (.step 4 (.split 22 1 (.split 72 1 (.split 5 0 (.step 71 (.split 61 0 (.split 62 0 (.split 69 0 (.step 51 (.split 12 0 (.step 2 (.run (.close 57))) (.step 57 (.run (.close 2))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57))))) (.step 2 (.run (.close 4)))) (.step 57 (.step 74 (.run (.close 2))))) (.step 4 (.run (.close 2))))))) (.step 24 (.run (.close 2))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part786.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part787
namespace Part788
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789239652048016513680179966897434931288202801610039201480729643720252330679960818833296246265278279425547523405509138928705626767256609236601784310486693726214696457205264357312955345975748641425397614301846131778702541825⟩
def references : Fin 1 → Box := ![Part787.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.reuse 0) (.step 74 (.step 24 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 2 (.run (.close 57))) (.step 61 (.run (.close 2)))) (.step 61 (.run (.close 2)))) (.step 61 (.run (.close 2)))) (.step 74 (.step 2 (.run (.close 7))))) (.step 7 (.run (.close 2))))) (.step 61 (.step 74 (.run (.close 2))))) (.step 7 (.run (.close 2)))) (.step 2 (.step 30 (.run (.close 74))))) (.step 61 (.step 74 (.run (.close 2))))) (.step 2 (.run (.close 23)))) (.step 56 (.run (.close 25)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 61 (.step 74 (.step 7 (.run (.close 2))))))))) (.step 50 (.split 72 1 (.split 12 0 (.split 17 1 (.split 18 0 (.split 19 0 (.split 21 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 2 (.run (.close 57))) (.step 35 (.step 2 (.run (.close 57))))) (.step 35 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))) (.step 50 (.step 35 (.run (.close 2))))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 19)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 56 (.run (.close 25)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 8 (.step 56 (.step 20 (.run (.close 18)))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 4 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part787.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part788
namespace Part789
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789239652048016513680179966897434931288202805662300499216074329767525638342447658780553715997657516968463988945265885615277458427491669046798010485280937248336409168579202008749114075113745465672795466301419551205438260225⟩
def references : Fin 1 → Box := ![Part788.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 1 (.reuse 0) (.step 57 (.step 4 (.step 48 (.step 24 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))))) (.step 57 (.step 61 (.step 73 (.step 48 (.split 16 1 (.split 5 0 (.step 58 (.split 25 0 (.split 38 0 (.step 44 (.step 36 (.split 12 0 (.step 2 (.run (.close 30))) (.step 27 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 48)))) (.step 30 (.step 60 (.step 61 (.step 73 (.run (.close 2)))))))))))) (.step 57 (.step 48 (.step 35 (.split 22 1 (.split 59 1 (.split 5 0 (.step 58 (.split 25 0 (.split 38 0 (.split 56 0 (.step 36 (.split 12 0 (.split 16 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 57))))) (.step 57 (.run (.close 2))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 48)))) (.step 27 (.step 57 (.step 61 (.run (.close 2)))))) (.step 61 (.step 73 (.step 4 (.run (.close 2)))))))))) (.step 57 (.step 61 (.step 48 (.split 16 1 (.split 22 1 (.split 50 1 (.split 59 1 (.split 5 0 (.step 58 (.split 25 0 (.split 38 0 (.step 34 (.step 36 (.split 16 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 48)))) (.step 27 (.step 57 (.step 61 (.run (.close 2)))))) (.step 27 (.step 57 (.step 61 (.step 2 (.run (.close 73))))))) (.step 30 (.step 61 (.step 73 (.step 4 (.run (.close 2))))))) (.step 48 (.run (.close 2))))))))
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
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789239652048016513685078850208092273725150656063702138820596561550147504303681074331170036363976774899326565612338423412645687080623819594118199342686229926935804175949106008428958635278107024843620153190604210580331955201⟩
def references : Fin 1 → Box := ![Part789.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 67 1 (.reuse 0) (.step 7 (.step 24 (.step 3 (.split 49 1 (.split 50 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 31 (.step 73 (.step 2 (.run (.close 57))))) (.step 30 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 3)))) (.step 27 (.step 57 (.step 61 (.step 73 (.step 2 (.run (.close 7)))))))) (.step 73 (.step 48 (.run (.close 2))))))))) (.step 7 (.step 24 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 24 0 (.split 18 0 (.step 60 (.split 16 0 (.step 2 (.run (.close 57))) (.step 4 (.step 2 (.run (.close 50)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 49 (.step 2 (.run (.close 50))))))) (.step 2 (.run (.close 7)))) (.step 57 (.step 60 (.step 74 (.step 2 (.run (.close 4))))))))))) (.step 74 (.step 7 (.step 24 (.step 31 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 21 0 (.split 30 0 (.step 2 (.run (.close 60))) (.step 74 (.run (.close 2)))) (.step 57 (.run (.close 24)))) (.step 74 (.step 49 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part789.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part790
namespace Part791
def root : Box := ⟨7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970103966007296, 5789239652048016513685078850208092273725150656063702138820596561550150856255663559980444929872998996054979250313371985697372946416601028357035311071255622699935022085007355142727134700109388053041229677475135220799348147201⟩
def references : Fin 1 → Box := ![Part790.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 43 1 (.split 51 1 (.split 34 1 (.reuse 0) (.step 7 (.step 24 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 57))) (.step 74 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 7))))) (.step 4 (.run (.close 49))))) (.step 2 (.run (.close 7)))) (.step 57 (.step 60 (.step 74 (.run (.close 2)))))) (.step 60 (.step 7 (.run (.close 2))))) (.step 74 (.step 7 (.run (.close 2))))) (.step 74 (.step 4 (.run (.close 2))))))))) (.step 61 (.step 7 (.step 24 (.step 3 (.split 67 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 19 0 (.split 33 0 (.split 18 0 (.step 48 (.step 30 (.split 16 0 (.step 2 (.run (.close 57))) (.step 61 (.run (.close 2)))))) (.step 2 (.run (.close 57)))) (.step 2 (.run (.close 61)))) (.step 2 (.run (.close 57)))) (.step 61 (.step 2 (.run (.close 30))))) (.step 61 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 7 (.run (.close 2)))))))))) (.step 43 (.step 3 (.step 30 (.step 68 (.step 30 (.run (.close 27)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.step 8 (.split 16 0 (.step 2 (.run (.close 7))) (.step 50 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))
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
def root : Box := ⟨2596148429267413814265250312093696, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759687343242923193359554358320900709729853619785255800264444732084819242968223950391410708233065360003866209899764722649426601859613696⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 51 0 (.split 67 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 21 0 (.split 16 0 (.step 2 (.run (.close 60))) (.split 12 0 (.step 2 (.run (.close 60))) (.step 18 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2))))) (.split 12 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 60))) (.step 4 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.step 2 (.run (.close 57))))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 60))) (.step 4 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.step 2 (.run (.close 60))))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 61))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 54 0 (.step 2 (.run (.close 73))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 7))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part792
namespace Part793
def root : Box := ⟨2596148429267413814265250312093696, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714779586024295957212045736633720374272⟩
def references : Fin 1 → Box := ![Part792.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 30 0 (.split 43 0 (.reuse 0) (.split 12 0 (.split 35 0 (.split 51 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 68 0 (.split 64 0 (.split 58 0 (.split 61 0 (.split 62 0 (.step 24 (.split 67 0 (.step 2 (.run (.close 30))) (.step 30 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 3 (.step 30 (.step 2 (.run (.close 9)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 43 0 (.split 21 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 73))))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 24 (.run (.close 2)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 43 0 (.split 21 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 73))))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 24 (.run (.close 2)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 3 (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.run (.close 14))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 4 (.step 2 (.run (.close 30))))))
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
def root : Box := ⟨2596148429267413814265250312093696, 5789239652048016513680179966897434931288202801610039201480729640205475928693088644762563037135604952183596649732136769318740335664258499337001885623736157707549964308829551426835577766793800924867737081780755632021019034625⟩
def references : Fin 1 → Box := ![Part793.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 35 1 (.split 54 1 (.split 72 1 (.split 22 1 (.split 0 0 (.split 4 0 (.reuse 0) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 3)))) (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 54 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 2 (.run (.close 60))) (.step 73 (.run (.close 2)))) (.step 73 (.step 2 (.run (.close 7))))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))) (.step 60 (.step 7 (.run (.close 2))))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 25)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 2))))) (.step 60 (.step 4 (.split 5 0 (.step 71 (.split 61 0 (.split 62 0 (.step 69 (.split 12 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 73))))) (.step 2 (.run (.close 4))))))) (.step 4 (.step 48 (.step 15 (.step 24 (.split 12 0 (.split 16 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))))) (.step 4 (.step 15 (.split 22 1 (.split 72 1 (.split 5 0 (.step 71 (.split 12 0 (.split 34 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 4 (.step 40 (.step 2 (.run (.close 57)))))) (.step 4 (.run (.close 2))))))) (.step 24 (.run (.close 2))))
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
def root : Box := ⟨2596148429267413814265250312093696, 5789239652048016513680179966897434931288202801610039201480729640205475928693088644762563037135604952183596649732136769318740335664258499337001885623736157707549964308829552924874756030969292083644690615970850779351875585025⟩
def references : Fin 1 → Box := ![Part794.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.reuse 0) (.split 35 1 (.split 72 1 (.split 12 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 2 (.run (.close 60))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))) (.step 7 (.step 2 (.run (.close 60))))) (.step 7 (.run (.close 2)))) (.step 2 (.step 30 (.run (.close 4))))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 8 (.step 14 (.run (.close 25))))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 24 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 24 (.split 72 1 (.split 12 0 (.split 17 1 (.split 18 0 (.split 19 0 (.split 21 0 (.split 22 1 (.split 23 0 (.split 54 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 8 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.split 51 0 (.step 2 (.run (.close 60))) (.step 35 (.step 2 (.run (.close 60))))) (.step 35 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))) (.step 50 (.step 35 (.run (.close 2))))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 19)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 8 (.step 14 (.run (.close 25))))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 8 (.step 14 (.step 20 (.run (.close 4)))))) (.step 7 (.step 24 (.run (.close 2))))) (.step 4 (.run (.close 2))))))
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
def root : Box := ⟨2596148429267413814265250312093696, 5789239652048016513680179966897434931288202805662300499216074326252749236355575484709820506867984189726513115271893516005312167324493559147198111798530401229671677020203490576310914760107288907892088467970424198778611303425⟩
def references : Fin 1 → Box := ![Part795.root]
def proof : Chunks.Proof 1 := (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 1 (.reuse 0) (.step 4 (.step 48 (.step 15 (.step 24 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))))) (.step 73 (.step 48 (.step 15 (.split 16 1 (.split 17 1 (.split 5 0 (.step 58 (.split 25 0 (.split 38 0 (.step 44 (.step 34 (.split 12 0 (.step 2 (.run (.close 30))) (.step 27 (.step 2 (.run (.close 57))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 48)))) (.step 30 (.step 60 (.step 61 (.step 73 (.step 2 (.run (.close 4)))))))) (.step 30 (.step 73 (.step 4 (.step 2 (.run (.close 7))))))))))) (.step 48 (.step 35 (.step 15 (.split 17 1 (.split 22 1 (.split 59 1 (.split 5 0 (.step 58 (.split 25 0 (.split 38 0 (.split 56 0 (.step 34 (.split 12 0 (.split 16 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 61))))) (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 48)))) (.step 27 (.step 48 (.step 58 (.step 2 (.run (.close 57))))))) (.step 30 (.step 73 (.step 4 (.step 2 (.run (.close 7))))))) (.step 48 (.run (.close 2)))))))) (.step 48 (.step 15 (.step 34 (.step 58 (.step 4 (.step 48 (.run (.close 2)))))))))
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
def root : Box := ⟨2596148429267413814265250312093696, 5789239652048016513685078850208092273725150656063702138820596558035371102316808900260436827234303447657375691938966053804920140719803513905075742936504138186392717524808044110890748421235442338243074100240486351425112114177⟩
def references : Fin 1 → Box := ![Part796.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 42 1 (.split 67 1 (.reuse 0) (.step 7 (.step 24 (.step 3 (.split 49 1 (.split 50 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 31 (.step 73 (.step 2 (.run (.close 4))))) (.step 30 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 3)))) (.step 73 (.step 48 (.run (.close 2))))) (.step 73 (.step 48 (.run (.close 2))))))))) (.step 7 (.step 24 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 24 0 (.split 18 0 (.step 60 (.split 16 0 (.step 2 (.run (.close 4))) (.step 4 (.step 2 (.run (.close 50)))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 4)))) (.step 4 (.step 49 (.step 2 (.run (.close 50))))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))))))) (.step 7 (.step 24 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 21 0 (.split 30 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 24)))) (.step 4 (.step 49 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))) (.step 60 (.step 7 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 60))))))))) (.step 66 (.step 7 (.step 24 (.step 31 (.split 36 1 (.split 42 1 (.split 9 0 (.step 43 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 7))))) (.step 4 (.run (.close 49))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 66 (.step 7 (.run (.close 2))))))))))
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
def root : Box := ⟨2596148429267413814265250312093696, 11578468272786246687484214102831214010865934258328309892933923113750589874971121212077576438558118158698350760376646487200849446760416463381142667675502767518223411549261277081277580448360995234921330070596069119386401637378⟩
def references : Fin 1 → Box := ![Part797.root]
def proof : Chunks.Proof 1 := (.step 2 (.split 10 1 (.split 30 1 (.split 43 1 (.split 51 1 (.reuse 0) (.step 7 (.step 24 (.step 3 (.split 49 1 (.split 50 1 (.split 59 1 (.split 67 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.split 16 0 (.step 2 (.run (.close 73))) (.step 48 (.run (.close 2)))) (.step 30 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 7 (.run (.close 2))))) (.step 73 (.step 48 (.run (.close 2))))) (.step 48 (.step 2 (.run (.close 73))))) (.step 27 (.run (.close 64)))))))) (.step 43 (.step 3 (.step 30 (.step 68 (.step 30 (.run (.close 27)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.step 8 (.split 16 0 (.step 2 (.run (.close 7))) (.step 50 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 8 (.run (.close 14))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part797.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part798
namespace Part799
def root : Box := ⟨2251801961168896, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759687343242923193359554358320900709729853619785255800264444732084819242968223950391410708233065360002568135685131015743419877684151296⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 51 0 (.split 67 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 21 0 (.split 16 0 (.step 2 (.run (.close 9))) (.split 12 0 (.step 2 (.run (.close 9))) (.step 18 (.run (.close 2))))) (.split 16 0 (.split 17 0 (.step 2 (.run (.close 9))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2))))) (.split 12 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 9))) (.step 4 (.step 2 (.run (.close 9))))) (.step 48 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 9))) (.step 4 (.step 2 (.run (.close 9))))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 9))) (.step 4 (.step 2 (.run (.close 9))))) (.step 48 (.run (.close 2)))) (.step 31 (.run (.close 2)))) (.step 31 (.step 2 (.run (.close 9))))) (.step 48 (.run (.close 2))))) (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 72 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 35 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 72 0 (.split 54 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 7))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))
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
def root : Box := ⟨2251801961168896, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505139729909544911872⟩
def references : Fin 1 → Box := ![Part799.root]
def proof : Chunks.Proof 1 := (.split 10 0 (.split 30 0 (.split 43 0 (.reuse 0) (.split 12 0 (.split 35 0 (.split 51 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 68 0 (.split 64 0 (.split 58 0 (.split 61 0 (.split 62 0 (.step 24 (.split 67 0 (.step 2 (.run (.close 30))) (.step 30 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 3 (.step 30 (.step 2 (.run (.close 9)))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 43 0 (.split 21 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 73))))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 24 (.run (.close 2)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 30 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 35 0 (.split 43 0 (.split 21 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 73))))) (.step 4 (.run (.close 2)))) (.step 48 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 24 (.run (.close 2)))) (.step 4 (.step 24 (.run (.close 2))))) (.step 3 (.step 31 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.run (.close 2))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10))))))) (.step 4 (.step 2 (.run (.close 30))))))
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
def root : Box := ⟨2251801961168896, 5789239652048016513680179966897434931288202801610039201480729640205475928693088644762563037135604952183596649732136769318740335664258499337001885623736157707549964308829551426835577766793799626793522448073849625296843572225⟩
def references : Fin 1 → Box := ![Part800.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 35 1 (.split 54 1 (.split 72 1 (.split 22 1 (.split 0 0 (.split 4 0 (.reuse 0) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 3)))) (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 54 0 (.split 73 0 (.split 25 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 30 0 (.split 38 0 (.step 11 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 11 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 8 (.run (.close 9)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 7)))) (.step 11 (.run (.close 2))))) (.step 60 (.step 4 (.split 61 0 (.split 49 0 (.split 50 0 (.split 59 0 (.split 16 0 (.split 62 0 (.step 69 (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 60 (.step 2 (.run (.close 9))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 9))))))) (.step 9 (.step 4 (.step 48 (.step 24 (.split 12 0 (.split 16 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 9 (.run (.close 2))))))))) (.step 9 (.step 4 (.step 11 (.split 72 1 (.split 49 0 (.split 50 0 (.split 59 0 (.split 16 0 (.split 12 0 (.step 2 (.run (.close 9))) (.step 9 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.step 4 (.run (.close 2))))))))) (.step 24 (.run (.close 2))))
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
def root : Box := ⟨2251801961168896, 5789239652048016513680179966897434931288202801610039201480729640205475928693088644762563037135604952183596649732136769318740335664258499337001885623736157707549964308829552924874756030970620013566260898136848579687980467201⟩
def references : Fin 1 → Box := ![Part801.root]
def proof : Chunks.Proof 1 := (.split 12 1 (.split 16 1 (.split 17 1 (.reuse 0) (.step 11 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 54 0 (.split 73 0 (.split 25 0 (.split 10 0 (.split 16 0 (.split 22 0 (.split 30 0 (.split 38 0 (.step 11 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 11 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 8 (.run (.close 9)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 7)))) (.step 11 (.run (.close 2)))))) (.step 11 (.split 12 0 (.split 13 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 54 0 (.split 73 0 (.split 25 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 38 0 (.step 11 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 50 (.run (.close 8)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 8 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 11 (.run (.close 2)))) (.step 2 (.run (.close 23)))) (.step 8 (.run (.close 9)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 23)))) (.step 2 (.run (.close 7)))) (.step 11 (.run (.close 2)))))) (.step 9 (.step 4 (.step 48 (.step 24 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))))))))
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
def root : Box := ⟨2251801961168896, 5789239652048016513685078850208092273725150656063702138820596558035371102316808900260436827234300739972127527080702398214995919914218683068340089623034128304256719741581783353746727136240573486738499088549863587050683368449⟩
def references : Fin 1 → Box := ![Part802.root]
def proof : Chunks.Proof 1 := (.split 67 1 (.split 49 1 (.split 50 1 (.split 59 1 (.reuse 0) (.step 9 (.step 48 (.step 11 (.split 25 0 (.split 38 0 (.split 56 0 (.split 12 0 (.split 26 0 (.split 35 0 (.split 72 0 (.step 44 (.split 16 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 9)))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 9 (.run (.close 2)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 9)))) (.step 2 (.run (.close 27)))))))) (.step 9 (.step 48 (.step 11 (.split 59 1 (.split 12 0 (.split 35 0 (.split 72 0 (.split 16 0 (.split 43 0 (.step 2 (.run (.close 9))) (.step 30 (.run (.close 2)))) (.step 30 (.step 4 (.run (.close 35))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 27 (.step 9 (.step 73 (.run (.close 2)))))))))) (.step 9 (.step 48 (.step 11 (.split 50 1 (.split 59 1 (.split 12 0 (.split 35 0 (.split 72 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 9))))) (.step 30 (.step 4 (.step 2 (.run (.close 73)))))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 9 (.run (.close 2)))) (.step 27 (.step 9 (.step 73 (.run (.close 2)))))) (.step 27 (.step 9 (.step 48 (.run (.close 2)))))))))) (.step 7 (.step 24 (.step 3 (.split 49 1 (.split 50 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.step 31 (.step 73 (.step 2 (.run (.close 9))))) (.step 30 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 3)))) (.step 73 (.step 48 (.run (.close 2))))) (.step 73 (.step 48 (.run (.close 2)))))))))
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
def root : Box := ⟨2251801961168896, 5789239652048016513685078850208092273725150656063702138820596558035371102316808900260436827234303447657375691938966053804920140719803513905075742936504138186392717524808044110890748421235441040168859466533580344700936651777⟩
def references : Fin 1 → Box := ![Part803.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 42 1 (.reuse 0) (.step 7 (.step 24 (.step 31 (.split 35 1 (.split 9 0 (.step 43 (.split 10 0 (.split 24 0 (.split 18 0 (.step 60 (.split 16 0 (.step 2 (.run (.close 9))) (.step 4 (.step 2 (.run (.close 7)))))) (.step 2 (.run (.close 7)))) (.step 9 (.run (.close 4)))) (.step 4 (.step 49 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))))))) (.step 7 (.step 24 (.step 31 (.split 35 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 21 0 (.split 30 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 9 (.run (.close 24)))) (.step 4 (.step 49 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))) (.step 60 (.step 7 (.run (.close 2))))) (.step 4 (.step 2 (.run (.close 60))))))))) (.step 7 (.step 24 (.step 31 (.split 35 1 (.split 36 1 (.split 42 1 (.split 72 1 (.split 9 0 (.step 43 (.split 10 0 (.split 16 0 (.split 17 0 (.step 2 (.run (.close 9))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 7))))) (.step 4 (.run (.close 49))))) (.step 2 (.run (.close 7)))) (.step 4 (.run (.close 2)))) (.step 60 (.step 7 (.run (.close 2))))) (.step 7 (.step 2 (.run (.close 60))))) (.step 4 (.step 2 (.run (.close 60)))))))))
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
def root : Box := ⟨2251801961168896, 11578468272786246687484214102831214010865934258328309892933923113750589874971121212077576438558118158698350760376646487200849446760416463381142667675502767518223411549261277081277580448360995234921330070596070245286308480002⟩
def references : Fin 1 → Box := ![Part804.root]
def proof : Chunks.Proof 1 := (.step 2 (.split 10 1 (.split 30 1 (.split 43 1 (.split 51 1 (.reuse 0) (.step 7 (.step 24 (.step 3 (.split 49 1 (.split 50 1 (.split 59 1 (.split 67 1 (.split 9 0 (.step 68 (.split 10 0 (.split 30 0 (.split 43 0 (.split 16 0 (.step 2 (.run (.close 9))) (.step 48 (.run (.close 2)))) (.step 30 (.run (.close 2)))) (.step 48 (.step 2 (.run (.close 30))))) (.step 48 (.step 30 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 7 (.run (.close 2))))) (.step 73 (.step 48 (.run (.close 2))))) (.step 48 (.step 2 (.run (.close 73))))) (.step 27 (.step 48 (.step 2 (.run (.close 73)))))))))) (.step 43 (.step 3 (.step 30 (.step 68 (.run (.close 46))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 8 (.run (.close 2))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 2 (.run (.close 10)))) (.step 7 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.step 8 (.run (.close 2))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))
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
def root : Box := ⟨2147483648, 11578468272786246687484214102831214010865934258328309892933923113750589874971121212077576438558118158698350760376646487200849446760416463381142667675502767518223411549261277081277580448360995234921330070596070245286308480002⟩
def references : Fin 5 → Box := ![Part771.root, Part783.root, Part791.root, Part798.root, Part805.root]
def proof : Chunks.Proof 5 := (.split 5 1 (.split 11 1 (.split 53 1 (.split 61 1 (.reuse 0) (.step 2 (.split 10 1 (.split 16 1 (.split 17 1 (.reuse 1) (.step 7 (.step 18 (.split 22 1 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2))))))) (.step 7 (.step 18 (.split 17 1 (.split 22 1 (.split 7 0 (.step 31 (.split 9 0 (.step 24 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))) (.step 7 (.run (.close 2)))) (.step 7 (.run (.close 2))))))) (.step 7 (.step 18 (.step 31 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 10))) (.step 30 (.step 2 (.run (.close 7))))) (.step 49 (.run (.close 2)))) (.step 49 (.step 2 (.run (.close 30))))))))))) (.step 2 (.split 10 1 (.reuse 2) (.step 7 (.step 3 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 21 0 (.split 23 0 (.split 29 0 (.step 8 (.step 14 (.step 56 (.run (.close 2))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))) (.reuse 3)) (.reuse 4))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part771.covered
  · exact Part783.covered
  · exact Part791.covered
  · exact Part798.covered
  · exact Part805.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part806
namespace Part807
def root : Box := ⟨2147485696, 5789239652048016513685078850208092273725150656063702138820596558035374454265594715394188144698388205564472009484649395999394504049538310894043378410483636802446102037171450689471384615525524187299384479987273248041415477249⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 50 1 (.split 59 1 (.split 21 1 (.split 10 0 (.split 30 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.step 57 (.step 2 (.run (.close 73))))) (.step 40 (.step 2 (.run (.close 57))))) (.step 40 (.step 2 (.step 57 (.step 2 (.run (.close 73))))))) (.step 3 (.step 2 (.run (.close 26))))) (.step 3 (.split 35 1 (.step 2 (.run (.close 57))) (.step 57 (.step 2 (.run (.close 38))))))) (.step 3 (.split 35 1 (.split 72 1 (.step 2 (.step 57 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 15))))) (.step 4 (.step 15 (.step 2 (.run (.close 38)))))))) (.step 4 (.step 3 (.step 2 (.run (.close 60)))))) (.step 4 (.step 3 (.split 21 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2))))))) (.step 4 (.step 3 (.split 17 0 (.split 21 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 24 (.run (.close 2))))))) (.step 4 (.step 3 (.run (.close 2))))) (.step 4 (.step 3 (.run (.close 2))))) (.step 4 (.step 3 (.run (.close 2))))) (.step 4 (.step 3 (.run (.close 2))))) (.step 4 (.step 3 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 57 (.step 4 (.step 40 (.step 15 (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 73))) (.step 73 (.run (.close 2)))) (.step 61 (.step 73 (.run (.close 2))))) (.step 4 (.run (.close 2)))))))))) (.step 57 (.step 4 (.step 40 (.step 15 (.step 3 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.step 21 (.step 2 (.run (.close 73))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))))))))
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
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 5789234136401013547594429611676468490257287326214741753906544602842851301056560122132773882985158449205646502782876725256725761641004231200526712257087368972296482827945140189959909149348657866407025702553923501752132305921⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 50 1 (.split 54 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.step 2 (.run (.close 73))) (.split 12 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 21 0 (.split 25 0 (.split 26 0 (.step 44 (.split 35 0 (.step 2 (.run (.close 30))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 18 (.run (.close 2))))) (.split 21 0 (.split 22 0 (.split 25 0 (.split 26 0 (.step 36 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.split 17 0 (.split 21 0 (.split 22 0 (.split 35 0 (.split 49 0 (.step 2 (.run (.close 30))) (.step 71 (.step 2 (.run (.close 30))))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 44 (.split 16 0 (.split 8 0 (.split 14 0 (.step 26 (.run (.close 2))) (.step 2 (.run (.close 73)))) (.step 2 (.run (.close 9)))) (.step 73 (.run (.close 2)))))) (.step 4 (.step 36 (.step 26 (.run (.close 2)))))) (.split 54 1 (.split 17 0 (.split 59 1 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.split 12 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.step 44 (.step 26 (.run (.close 2)))))) (.step 27 (.step 4 (.step 2 (.step 73 (.run (.close 2))))))) (.step 4 (.step 57 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part808
namespace Part809
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 5789234136401013547594429611676468490257287326214741753906544602842851301059756792648297459030095912454202869938224596799916394329663145072764514613512998888765120243603059899700071901824268550054485079126873008641668023297⟩
def references : Fin 1 → Box := ![Part808.root]
def proof : Chunks.Proof 1 := (.split 42 0 (.split 12 1 (.split 49 1 (.reuse 0) (.step 34 (.split 54 1 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 59 1 (.split 22 0 (.step 2 (.run (.close 73))) (.step 4 (.run (.close 2)))) (.step 26 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 73))))) (.step 4 (.step 2 (.run (.close 44))))) (.step 3 (.run (.close 73)))) (.step 27 (.run (.close 2)))) (.step 4 (.step 57 (.run (.close 2))))))) (.step 4 (.step 34 (.step 26 (.split 50 1 (.split 54 1 (.split 5 0 (.step 26 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 57 (.step 4 (.run (.close 2))))))))) (.step 44 (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.step 4 (.run (.close 26)))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 5 (.run (.close 2))))))
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
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965939952101177603843075057809888294699907662949258934559982242245990160175198695929590815420079777226162176, 5789234136401013547594429611676468490257287326214741753906544602842851301059756792648297459030095912454202869938226945344738912905068838763918746231108818849435674060708416725571593211813175029678109723506135270616307074049⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 36 0 (.split 42 0 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.split 16 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 12 0 (.split 17 0 (.split 22 0 (.step 26 (.run (.close 2))) (.step 60 (.run (.close 44)))) (.step 60 (.step 2 (.run (.close 30))))) (.step 76 (.run (.close 2)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 9)))) (.step 60 (.step 4 (.run (.close 2)))))) (.split 16 0 (.split 12 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 34 (.step 36 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 73)))) (.step 4 (.run (.close 40)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 4 (.run (.close 40)))) (.step 60 (.step 4 (.run (.close 2)))))) (.step 4 (.run (.close 3)))) (.step 76 (.step 4 (.step 57 (.run (.close 2)))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 57 (.step 5 (.run (.close 2))))))
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
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 5789234136401013547594429611676468490257287326214741753906544602842851301059756792648297459030095912454202869938226945344738912905070875799895080717195087295124083438869468193965259148063811170127464104805898607322490471425⟩
def references : Fin 2 → Box := ![Part809.root, Part810.root]
def proof : Chunks.Proof 2 := (.split 30 0 (.split 34 0 (.split 36 0 (.reuse 0) (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 42 0 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 57))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.split 16 0 (.split 8 0 (.split 14 0 (.split 74 0 (.split 17 0 (.split 22 0 (.step 26 (.run (.close 2))) (.step 60 (.run (.close 44)))) (.step 60 (.run (.close 36)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 9)))) (.step 60 (.step 4 (.run (.close 2)))))) (.step 4 (.run (.close 3)))) (.step 76 (.step 4 (.run (.close 57))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 5 (.run (.close 2)))))) (.reuse 1)) (.step 4 (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 54 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 2 (.run (.close 73))) (.step 3 (.step 2 (.run (.close 60))))) (.step 4 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.step 36 (.step 2 (.run (.close 60))))))) (.step 18 (.step 8 (.step 3 (.step 2 (.run (.close 60))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.step 27 (.run (.close 2)))))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 73 (.step 4 (.run (.close 2))))) (.step 27 (.step 4 (.step 42 (.step 2 (.step 73 (.run (.close 2)))))))) (.step 27 (.step 4 (.step 42 (.step 48 (.step 2 (.run (.close 73))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part809.covered
  · exact Part810.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part811
namespace Part812
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 5789234136401013547594429611676468490257287326214741753906544602842851301059756792648297459030095912454202869938226945344738912905070875799895080717195087295125728943426789400007414117246368521900097440899761589782053913601⟩
def references : Fin 1 → Box := ![Part811.root]
def proof : Chunks.Proof 1 := (.split 21 1 (.split 4 0 (.split 10 0 (.reuse 0) (.step 4 (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 0 (.split 30 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 54 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 2 (.run (.close 73))) (.step 3 (.step 2 (.run (.close 60))))) (.step 4 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.step 36 (.step 2 (.run (.close 60))))))) (.step 18 (.step 8 (.step 3 (.step 2 (.run (.close 60))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.step 27 (.run (.close 2)))))))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 4 (.step 2 (.run (.close 30))))) (.step 73 (.step 4 (.run (.close 2))))) (.step 27 (.step 4 (.step 35 (.step 48 (.step 2 (.run (.close 73)))))))) (.step 27 (.step 58 (.step 3 (.step 73 (.run (.close 2))))))))) (.step 2 (.step 3 (.step 7 (.run (.close 30)))))) (.step 4 (.split 4 0 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 30 0 (.step 26 (.split 12 0 (.split 35 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 30))) (.step 30 (.step 2 (.run (.close 57))))) (.step 30 (.step 73 (.run (.close 2))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.step 76 (.step 4 (.run (.close 2))))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 2 (.run (.close 4)))) (.step 10 (.step 76 (.step 4 (.step 43 (.run (.close 2))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part811.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part812
namespace Part813
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 5789239652053276649586627223715333263608030784729252478623419731894872735171860118064008801562663957969936985373384529282196529022292632941597791813641456587601913348288659587343223938175987430190132863719525215483907277825⟩
def references : Fin 1 → Box := ![Part812.root]
def proof : Chunks.Proof 1 := (.split 51 1 (.split 22 1 (.split 35 1 (.split 67 1 (.split 72 1 (.reuse 0) (.step 4 (.step 40 (.step 71 (.run (.close 2)))))) (.step 76 (.step 3 (.split 49 1 (.split 50 1 (.split 4 0 (.step 44 (.split 10 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 2 (.run (.close 9))) (.step 30 (.step 2 (.run (.close 73))))) (.step 73 (.run (.close 2)))) (.step 73 (.run (.close 2)))) (.step 73 (.step 76 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 27 (.step 73 (.step 76 (.run (.close 2)))))) (.step 27 (.step 73 (.step 76 (.step 2 (.run (.close 7)))))))))) (.step 4 (.step 40 (.step 71 (.run (.close 2)))))) (.step 24 (.step 18 (.split 4 0 (.step 44 (.split 9 0 (.step 8 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 60))) (.step 58 (.run (.close 2)))) (.step 60 (.step 2 (.run (.close 61)))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7))))))) (.step 3 (.split 21 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 67 1 (.split 4 0 (.step 36 (.split 10 0 (.split 16 0 (.split 21 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 9))) (.step 3 (.step 73 (.run (.close 2))))) (.step 30 (.step 73 (.run (.close 2))))) (.step 10 (.step 73 (.run (.close 2))))) (.step 30 (.step 73 (.run (.close 3))))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 76 (.step 2 (.run (.close 27)))))) (.step 73 (.run (.close 62)))) (.step 4 (.step 35 (.step 3 (.step 62 (.run (.close 54))))))) (.step 27 (.step 3 (.step 34 (.step 36 (.step 62 (.step 53 (.step 2 (.run (.close 54)))))))))) (.step 10 (.step 73 (.step 4 (.run (.close 24))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part812.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part813
namespace Part814
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 5789239652053276649586627223715333263608030784729252478623419731894872735171860118064008801565439335349305965091226599056263833531313900853709261702281946050352532439320545967527219629274994561717884452664645544963134718977⟩
def references : Fin 1 → Box := ![Part813.root]
def proof : Chunks.Proof 1 := (.split 34 1 (.split 36 1 (.split 42 1 (.split 43 1 (.reuse 0) (.step 3 (.step 30 (.split 9 0 (.step 10 (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 30))))))) (.step 43 (.split 4 0 (.split 10 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 44 (.run (.close 40))) (.step 76 (.run (.close 2)))) (.step 2 (.run (.close 76)))) (.step 2 (.run (.close 76)))) (.step 60 (.run (.close 44)))) (.step 60 (.run (.close 44)))) (.step 60 (.step 76 (.run (.close 2))))) (.step 2 (.run (.close 7)))))) (.step 5 (.step 43 (.step 40 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 36 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 60 (.step 4 (.run (.close 36))))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))) (.step 5 (.step 43 (.step 40 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 34 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 60 (.step 4 (.run (.close 2))))) (.step 60 (.step 4 (.run (.close 34))))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))))
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
def root : Box := ⟨10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586505619046400, 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705624978129482813392851479365895332994063430111232304948708892959186898679214393313341538538044262402⟩
def references : Fin 1 → Box := ![Part814.root]
def proof : Chunks.Proof 1 := (.step 2 (.split 10 1 (.split 16 1 (.split 17 1 (.split 30 1 (.reuse 0) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.step 2 (.run (.close 60))))) (.step 2 (.run (.close 60)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 18 (.step 31 (.split 22 1 (.split 4 0 (.step 36 (.step 8 (.split 10 0 (.step 2 (.run (.close 60))) (.step 3 (.step 2 (.run (.close 60))))))) (.step 2 (.run (.close 7)))) (.step 60 (.step 73 (.step 2 (.run (.close 61)))))))))) (.step 24 (.step 18 (.step 31 (.split 17 1 (.split 22 1 (.split 4 0 (.split 9 0 (.step 8 (.split 10 0 (.split 12 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 60))) (.step 60 (.run (.close 2)))) (.step 35 (.step 18 (.step 2 (.run (.close 60)))))) (.step 58 (.step 2 (.run (.close 61))))) (.step 35 (.step 18 (.step 73 (.run (.close 2))))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 60 (.step 73 (.step 2 (.run (.close 61)))))) (.step 8 (.step 18 (.run (.close 19))))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 30 (.step 73 (.step 2 (.run (.close 60))))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part814.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part815
namespace Part816
def root : Box := ⟨2147483648, 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705624978129482813392851479365895332994063430111232304948708892959186898679214393313341538538044262402⟩
def references : Fin 3 → Box := ![Part806.root, Part807.root, Part815.root]
def proof : Chunks.Proof 3 := (.split 70 1 (.split 1 1 (.reuse 0) (.step 2 (.split 16 1 (.split 17 1 (.split 22 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 49 1 (.reuse 1) (.step 57 (.step 4 (.step 40 (.step 15 (.step 3 (.split 50 1 (.split 16 0 (.split 17 0 (.split 22 0 (.step 2 (.step 34 (.step 2 (.run (.close 73))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 53 (.run (.close 2)))))))))) (.step 40 (.step 3 (.step 31 (.step 75 (.step 38 (.step 2 (.step 57 (.run (.close 2)))))))))) (.step 57 (.step 40 (.step 3 (.step 31 (.step 75 (.step 38 (.step 2 (.run (.close 31)))))))))) (.step 40 (.step 15 (.step 3 (.step 31 (.step 75 (.step 38 (.split 36 1 (.step 2 (.run (.close 31))) (.step 31 (.run (.close 2))))))))))) (.step 4 (.step 24 (.step 3 (.run (.close 2)))))) (.step 4 (.step 24 (.step 3 (.run (.close 2)))))) (.step 4 (.step 24 (.step 3 (.run (.close 2)))))))) (.reuse 2))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part806.covered
  · exact Part807.covered
  · exact Part815.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part816
namespace Part817
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789234136395753411692881238169227500374407197549191414103721428983353020153491389978476802163044782669368914331649742287869585559278247687243941956020218256158483642976188416299143812739934503617054750738297946257274962945⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 50 1 (.split 54 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.step 2 (.run (.close 73))) (.split 12 0 (.step 2 (.run (.close 57))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 21 0 (.split 25 0 (.split 26 0 (.step 44 (.split 35 0 (.step 2 (.run (.close 30))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 18 (.run (.close 2))))) (.split 21 0 (.split 22 0 (.split 25 0 (.split 26 0 (.step 36 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.split 17 0 (.split 21 0 (.split 22 0 (.split 35 0 (.split 49 0 (.step 2 (.run (.close 30))) (.step 71 (.step 2 (.run (.close 30))))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 44 (.split 16 0 (.split 43 0 (.split 51 0 (.split 17 0 (.split 12 0 (.step 2 (.run (.close 60))) (.step 4 (.run (.close 2)))) (.step 61 (.step 73 (.run (.close 2))))) (.step 61 (.step 73 (.step 2 (.run (.close 60)))))) (.step 27 (.run (.close 2)))) (.step 73 (.step 4 (.run (.close 2))))))) (.step 4 (.step 36 (.step 21 (.step 2 (.run (.close 57))))))) (.split 17 0 (.split 59 1 (.split 8 0 (.split 14 0 (.split 51 0 (.split 11 0 (.step 21 (.run (.close 2))) (.step 2 (.run (.close 4)))) (.step 27 (.step 4 (.run (.close 2))))) (.step 2 (.run (.close 35)))) (.step 2 (.run (.close 35)))) (.step 27 (.step 21 (.step 2 (.run (.close 73)))))) (.step 27 (.step 4 (.step 2 (.step 73 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part817
namespace Part818
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486997613831060218247937161559481744312445848172627121058634108126039306565215545187264514127311247453146810680321⟩
def references : Fin 1 → Box := ![Part817.root]
def proof : Chunks.Proof 1 := (.split 42 0 (.split 12 1 (.split 49 1 (.reuse 0) (.step 34 (.split 54 1 (.split 43 0 (.split 51 0 (.split 67 0 (.split 16 0 (.split 17 0 (.split 59 1 (.step 2 (.step 21 (.run (.close 2)))) (.step 53 (.step 2 (.run (.close 60))))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 73))))) (.step 4 (.step 2 (.run (.close 44))))) (.step 42 (.step 3 (.run (.close 35))))) (.step 27 (.run (.close 2)))) (.step 4 (.step 57 (.run (.close 2))))))) (.step 4 (.step 21 (.step 34 (.split 54 1 (.split 59 1 (.split 5 0 (.step 21 (.run (.close 2))) (.step 2 (.run (.close 9)))) (.step 4 (.run (.close 2)))) (.step 57 (.step 4 (.run (.close 2))))))))) (.step 44 (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.step 4 (.step 2 (.run (.close 57))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 5 (.run (.close 2))))))
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
def root : Box := ⟨2239749014151876052377607070611856617225874702643694248205528995047007515619612506661977539197928472576, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962375882736823342855250635975930041668133297674875739464951910827875204451666888138771690509715121449731073⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 36 0 (.split 42 0 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 60))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.split 16 0 (.split 12 0 (.split 17 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 34 (.step 44 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 40)))) (.step 4 (.step 2 (.run (.close 30)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 34 (.step 36 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 4)))) (.step 4 (.run (.close 40)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 4 (.step 50 (.run (.close 2)))))) (.step 4 (.run (.close 3)))) (.step 10 (.step 4 (.step 57 (.run (.close 2)))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 57 (.step 5 (.run (.close 2))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part819
namespace Part820
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962375882736823344892288554979308353665649905546160724035326946900650507227328589305562729177337032841626625⟩
def references : Fin 2 → Box := ![Part818.root, Part819.root]
def proof : Chunks.Proof 2 := (.split 28 0 (.split 30 0 (.split 34 0 (.split 36 0 (.reuse 0) (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 42 0 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 57))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.split 16 0 (.split 12 0 (.split 17 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 44 (.step 2 (.run (.close 30)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 40)))) (.step 4 (.step 2 (.run (.close 30)))))) (.step 4 (.run (.close 3)))) (.step 10 (.step 4 (.run (.close 57))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 5 (.run (.close 2)))))) (.reuse 1)) (.step 4 (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 54 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 2 (.run (.close 73))) (.step 3 (.step 2 (.run (.close 60))))) (.step 4 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.step 36 (.step 2 (.run (.close 60))))))) (.step 18 (.step 8 (.step 3 (.step 2 (.run (.close 7))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.step 27 (.run (.close 2)))))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 27 (.step 73 (.step 4 (.run (.close 2)))))) (.step 58 (.run (.close 42)))) (.step 58 (.run (.close 42)))))) (.step 2 (.step 3 (.step 48 (.step 57 (.run (.close 5)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part818.covered
  · exact Part819.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part820
namespace Part821
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962375882736823344892288554979308353665649905546160724035326946900650507227329856956162957406739629056459777⟩
def references : Fin 1 → Box := ![Part820.root]
def proof : Chunks.Proof 1 := (.split 4 0 (.split 10 0 (.reuse 0) (.step 4 (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 0 (.split 30 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 54 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 2 (.run (.close 73))) (.step 3 (.step 2 (.run (.close 60))))) (.step 4 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.step 36 (.step 2 (.run (.close 60))))))) (.step 18 (.step 8 (.step 3 (.step 2 (.run (.close 7))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.step 27 (.run (.close 2)))))))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))) (.step 4 (.step 2 (.run (.close 30))))) (.step 27 (.step 73 (.step 4 (.step 2 (.run (.close 7))))))) (.step 27 (.step 4 (.step 42 (.step 48 (.run (.close 2))))))) (.step 27 (.step 4 (.step 42 (.step 48 (.step 2 (.run (.close 73)))))))))) (.step 2 (.step 3 (.step 7 (.run (.close 30))))))
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
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789239652048016513685078850208092273725150656063702138820596558035371102316808900260436827234300739972127527080702398214995922050205718989250172018055834473808834344286304212360318819106690150181271335000317336782006912001⟩
def references : Fin 1 → Box := ![Part821.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 35 1 (.split 67 1 (.split 72 1 (.split 21 1 (.reuse 0) (.step 4 (.split 4 0 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 21 (.split 74 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.step 30 (.step 2 (.run (.close 57)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 4))))) (.step 10 (.step 4 (.run (.close 2))))) (.step 24 (.run (.close 2)))) (.step 24 (.run (.close 2)))) (.step 50 (.step 35 (.run (.close 2))))) (.step 2 (.run (.close 4)))) (.step 10 (.step 4 (.step 43 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 4)))) (.step 2 (.run (.close 7)))))) (.step 4 (.step 40 (.step 71 (.run (.close 2)))))) (.step 3 (.split 21 1 (.split 49 1 (.split 50 1 (.split 4 0 (.step 44 (.split 10 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 2 (.run (.close 9))) (.step 30 (.step 2 (.run (.close 4))))) (.step 30 (.step 68 (.run (.close 2))))) (.step 68 (.run (.close 35)))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 73 (.step 4 (.step 42 (.step 35 (.run (.close 2))))))) (.step 27 (.step 73 (.step 4 (.step 42 (.step 3 (.step 48 (.run (.close 35))))))))) (.step 10 (.step 4 (.step 43 (.step 35 (.run (.close 2))))))))) (.step 4 (.step 40 (.step 71 (.run (.close 2)))))) (.step 24 (.step 18 (.split 4 0 (.step 44 (.split 9 0 (.step 8 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 58 (.run (.close 2)))) (.step 73 (.step 3 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))))))
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
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789239652048016513685078850208092273725150656063702138820596558035374454268791385909711720743325668813028376639997267542585138874182223651214928675844704444463441344069756274637339821729504240556101266208662012698846823425⟩
def references : Fin 1 → Box := ![Part822.root]
def proof : Chunks.Proof 1 := (.split 42 1 (.split 43 1 (.split 51 1 (.reuse 0) (.step 3 (.step 31 (.split 21 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 67 1 (.split 4 0 (.step 36 (.split 10 0 (.split 16 0 (.split 21 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 9))) (.step 42 (.run (.close 2)))) (.step 30 (.step 73 (.step 2 (.run (.close 4)))))) (.step 10 (.step 4 (.run (.close 2))))) (.step 68 (.run (.close 35)))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 3 (.step 70 (.run (.close 2))))) (.step 27 (.step 73 (.step 4 (.step 42 (.step 2 (.run (.close 7)))))))) (.step 35 (.run (.close 53)))) (.step 27 (.step 4 (.step 42 (.step 3 (.step 36 (.step 62 (.step 35 (.run (.close 54)))))))))) (.step 10 (.step 4 (.step 43 (.step 35 (.step 2 (.run (.close 7))))))))))) (.step 3 (.step 30 (.split 9 0 (.step 10 (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 30))))))) (.step 5 (.step 43 (.step 40 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 44 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 50 (.run (.close 44))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part822.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part823
namespace Part824
def root : Box := ⟨4271974071841820164790043412339104229205409044713305539894083215644439451561281100045926321356800, 5789239652048016513685078850208092273725150656063702138820596558035374454268791385909711720743325668813028376639999616087407657449589954378345494779526792850822404539336166065480203694813635101202348993361499739054593278977⟩
def references : Fin 1 → Box := ![Part823.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.step 5 (.step 43 (.step 40 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 36 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 50 (.run (.close 36))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))) (.step 5 (.step 43 (.step 40 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 34 (.run (.close 40))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 4 (.step 50 (.run (.close 34))))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7))))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.step 35 (.run (.close 2)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 3 (.run (.close 35)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 18 (.step 31 (.split 22 1 (.split 4 0 (.step 36 (.step 8 (.split 10 0 (.step 2 (.run (.close 4))) (.step 3 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 8 (.step 18 (.run (.close 25)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part823.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part824
namespace Part825
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207979538232677116628736306785958513881770988494934806251365745341074844183650583087438711457648877667491087495861532868430338720769⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 16 0 (.split 17 0 (.split 22 0 (.split 43 0 (.split 51 0 (.step 2 (.run (.close 27))) (.split 12 0 (.step 2 (.run (.close 27))) (.step 4 (.run (.close 2))))) (.split 12 0 (.split 35 0 (.step 2 (.run (.close 30))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2))))) (.split 21 0 (.split 25 0 (.split 26 0 (.step 44 (.split 35 0 (.step 2 (.run (.close 30))) (.step 71 (.run (.close 2))))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 18 (.run (.close 2))))) (.split 21 0 (.split 22 0 (.split 25 0 (.split 26 0 (.step 36 (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.split 17 0 (.split 21 0 (.split 22 0 (.split 35 0 (.split 46 0 (.split 47 0 (.split 49 0 (.step 2 (.run (.close 30))) (.step 27 (.run (.close 2)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 71 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 18 (.run (.close 2))))) (.step 44 (.split 7 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 9)))))) (.step 27 (.step 4 (.step 36 (.split 12 0 (.step 2 (.run (.close 27))) (.step 4 (.run (.close 2)))))))) (.split 7 0 (.split 13 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27))))) (.step 34 (.split 7 0 (.step 27 (.run (.close 2))) (.step 2 (.run (.close 27)))))) (.step 27 (.step 4 (.step 34 (.split 54 1 (.split 16 0 (.step 2 (.run (.close 27))) (.step 27 (.run (.close 2)))) (.step 4 (.run (.close 2))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part825
namespace Part826
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962373642989945178015121113017284267310945089196469642194309682743641679953349741286928464372132808984888321⟩
def references : Fin 1 → Box := ![Part825.root]
def proof : Chunks.Proof 1 := (.split 36 0 (.split 42 0 (.reuse 0) (.step 44 (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.step 4 (.step 2 (.run (.close 27))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 27 (.step 4 (.step 57 (.step 2 (.run (.close 27))))))))) (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 42 0 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.split 16 0 (.split 12 0 (.split 17 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 44 (.step 2 (.run (.close 30)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 4 (.step 2 (.run (.close 30)))))) (.step 4 (.run (.close 3)))) (.step 10 (.step 4 (.run (.close 57))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 27 (.step 10 (.step 4 (.step 57 (.step 2 (.run (.close 27)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part825.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part826
namespace Part827
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962375882734687355819331670459564835755223210841966876843844582732742643745220921447873845249626080592004097⟩
def references : Fin 1 → Box := ![Part826.root]
def proof : Chunks.Proof 1 := (.split 34 0 (.reuse 0) (.split 12 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 36 0 (.split 42 0 (.split 16 0 (.split 43 0 (.split 51 0 (.split 67 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 71 (.run (.close 2)))) (.step 71 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 18 (.step 2 (.run (.close 30))))) (.split 16 0 (.split 12 0 (.split 17 0 (.split 25 0 (.split 26 0 (.split 35 0 (.step 34 (.step 44 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 29)))) (.step 4 (.step 2 (.run (.close 30)))))) (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 35 0 (.split 38 0 (.step 34 (.step 36 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 28)))) (.step 2 (.run (.close 27)))) (.step 2 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.step 2 (.run (.close 30))))) (.step 43 (.run (.close 2))))) (.step 4 (.run (.close 3)))) (.step 10 (.step 4 (.step 57 (.run (.close 2)))))) (.step 4 (.run (.close 3)))) (.step 4 (.run (.close 3)))) (.step 4 (.step 57 (.step 5 (.run (.close 2)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part826.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part827
namespace Part828
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789234136395753411692881238169227500374407197549191414103721428983353020156688060494000378207982245917925281486999962375882734687357856367646794050922023668899251345037895312976398678894381362638452855373242365382990234625⟩
def references : Fin 1 → Box := ![Part827.root]
def proof : Chunks.Proof 1 := (.split 4 0 (.split 10 0 (.split 30 0 (.reuse 0) (.step 4 (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 54 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 3 (.step 2 (.run (.close 27))))) (.step 4 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.step 36 (.step 2 (.run (.close 30))))))) (.step 18 (.step 8 (.step 3 (.step 2 (.run (.close 7))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.step 27 (.run (.close 2)))))))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))))) (.step 4 (.split 49 1 (.split 50 1 (.split 59 1 (.split 12 0 (.split 30 0 (.split 35 0 (.split 43 0 (.split 16 0 (.split 51 0 (.split 54 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 2 (.run (.close 27))) (.step 3 (.step 2 (.run (.close 27))))) (.step 4 (.run (.close 2)))) (.step 18 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.step 36 (.step 2 (.run (.close 30))))))) (.step 18 (.step 8 (.step 3 (.step 2 (.run (.close 7))))))) (.step 3 (.step 30 (.step 18 (.step 30 (.step 27 (.run (.close 2)))))))) (.step 4 (.run (.close 2)))) (.step 3 (.step 18 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.run (.close 7))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30))))))) (.step 4 (.step 2 (.run (.close 30))))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 27 (.run (.close 2)))))) (.step 2 (.step 27 (.run (.close 7)))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part827.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part828
namespace Part829
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789239652048016513685078850208092273725150656063702138820596558035371102316808900260436827234300739972127527080702398214995919914218683068341986760624192492802539528600164198389816847493844182962768027416152962535940686849⟩
def references : Fin 1 → Box := ![Part828.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 35 1 (.split 67 1 (.split 72 1 (.split 21 1 (.reuse 0) (.step 4 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 2 (.run (.close 30))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 4 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 27 (.run (.close 2)))) (.step 4 (.run (.close 2)))) (.step 27 (.step 2 (.run (.close 30))))) (.step 27 (.step 30 (.run (.close 24))))) (.step 27 (.step 30 (.run (.close 24))))) (.step 27 (.step 35 (.run (.close 24))))) (.step 27 (.step 10 (.step 43 (.step 2 (.run (.close 30))))))))) (.step 4 (.step 40 (.step 71 (.run (.close 2)))))) (.step 27 (.step 3 (.split 21 1 (.split 4 0 (.step 44 (.split 10 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 2 (.run (.close 9))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 30 (.run (.close 7))))))) (.step 4 (.step 40 (.step 71 (.run (.close 2)))))) (.step 24 (.step 18 (.split 4 0 (.step 44 (.split 9 0 (.step 8 (.split 10 0 (.split 12 0 (.step 2 (.run (.close 4))) (.step 27 (.run (.close 30)))) (.step 73 (.step 3 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7))))) (.step 2 (.run (.close 7)))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part828.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part829
namespace Part830
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789239652048016513685078850208092273725150656063702138820596558035374454268791385909711720743325668813028376639999616085167910571423077210903532755440438146006054848254323551638370059141772881781061657622882407155812533249⟩
def references : Fin 1 → Box := ![Part829.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 42 1 (.split 43 1 (.split 51 1 (.reuse 0) (.step 27 (.step 3 (.step 31 (.split 21 1 (.split 67 1 (.split 4 0 (.step 36 (.split 10 0 (.split 16 0 (.split 21 0 (.split 22 0 (.split 30 0 (.step 2 (.run (.close 9))) (.step 3 (.step 30 (.run (.close 27))))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 30 (.run (.close 27)))) (.step 3 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 3 (.step 70 (.run (.close 2))))) (.step 30 (.run (.close 7)))))))) (.step 3 (.step 30 (.split 9 0 (.step 10 (.step 30 (.run (.close 27)))) (.step 2 (.run (.close 30))))))) (.step 5 (.step 43 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 44 (.run (.close 28))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 43 (.run (.close 2)))) (.step 2 (.run (.close 7)))))))) (.step 43 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 36 (.run (.close 28))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 4 (.run (.close 36)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 7)))))))
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
def root : Box := ⟨3794275180128377091639574036764685364535950857523710002444946112771297434188906496, 5789239652048016513685078850208092273725150656063702138820596558035374454268791385909711720743325668813028376639999616087407655313602918457437309522095150869816109723650026052971203360531692052187530518493618384464459596801⟩
def references : Fin 1 → Box := ![Part830.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 30 1 (.split 34 1 (.reuse 0) (.step 43 (.step 31 (.split 4 0 (.split 10 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 25 0 (.split 26 0 (.split 30 0 (.step 34 (.run (.close 28))) (.step 4 (.step 2 (.run (.close 30))))) (.step 2 (.run (.close 28)))) (.step 2 (.run (.close 28)))) (.step 4 (.run (.close 34)))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 4 (.step 43 (.run (.close 2))))) (.step 2 (.run (.close 7))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 10 0 (.split 18 0 (.split 19 0 (.split 23 0 (.step 30 (.run (.close 7))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 2 (.run (.close 30)))) (.step 3 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))) (.step 24 (.step 18 (.step 31 (.split 22 1 (.split 4 0 (.step 36 (.step 8 (.split 10 0 (.step 2 (.run (.close 4))) (.step 3 (.step 2 (.run (.close 7))))))) (.step 2 (.run (.close 7)))) (.step 8 (.step 18 (.run (.close 25))))))))) (.step 24 (.step 18 (.step 31 (.split 17 1 (.split 22 1 (.split 9 0 (.step 8 (.split 10 0 (.split 11 0 (.split 12 0 (.split 14 0 (.split 17 0 (.split 19 0 (.split 22 0 (.step 2 (.run (.close 4))) (.step 73 (.step 30 (.run (.close 7))))) (.step 2 (.run (.close 30)))) (.step 35 (.step 18 (.step 30 (.run (.close 60)))))) (.step 2 (.run (.close 4)))) (.step 27 (.run (.close 24)))) (.step 30 (.run (.close 4)))) (.step 18 (.step 7 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 8 (.step 18 (.run (.close 19))))) (.step 8 (.step 18 (.run (.close 19)))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part830.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part831
namespace Part832
def root : Box := ⟨2147483648, 11578468272791506823385762476338455000748814386993860232736746287610088155874189944231873519380231825234628348827873470169705627114116518734304831011977665691091997819834137004283746815429556575900162647010277210216151910402⟩
def references : Fin 3 → Box := ![Part816.root, Part824.root, Part831.root]
def proof : Chunks.Proof 3 := (.split 27 1 (.split 32 1 (.reuse 0) (.step 2 (.split 10 1 (.split 16 1 (.reuse 1) (.step 50 (.step 35 (.step 24 (.step 18 (.split 17 1 (.split 22 1 (.split 9 0 (.step 8 (.split 10 0 (.split 12 0 (.split 17 0 (.split 22 0 (.step 2 (.run (.close 4))) (.step 50 (.run (.close 2)))) (.step 50 (.run (.close 2)))) (.step 58 (.step 2 (.run (.close 61))))) (.step 50 (.step 35 (.run (.close 2)))))) (.step 2 (.run (.close 7)))) (.step 50 (.step 35 (.run (.close 2))))) (.step 50 (.step 35 (.step 2 (.run (.close 61))))))))))) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 30 0 (.step 30 (.step 31 (.run (.close 2)))) (.step 3 (.run (.close 35)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))))))))) (.step 2 (.split 10 1 (.reuse 2) (.step 3 (.step 18 (.step 31 (.split 4 0 (.split 9 0 (.split 18 0 (.split 19 0 (.split 23 0 (.split 29 0 (.split 16 0 (.step 30 (.run (.close 49))) (.step 8 (.step 35 (.run (.close 31))))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7)))) (.step 2 (.run (.close 7))))))))))
theorem accepted : Fast.check 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel
theorem references_covered : ∀ i, Chunks.Excludes 14 checkedFamilies (references i) := by
  intro i
  fin_cases i
  · exact Part816.covered
  · exact Part824.covered
  · exact Part831.covered
theorem covered : Chunks.Excludes 14 checkedFamilies root :=
  Fast.check_sound 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part832
end FiveColour.Packed.EnumerationChunks.Case173
