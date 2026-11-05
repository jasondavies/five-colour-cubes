module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case87
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381984959626041258113107201226117490567900120422023168⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨18740915245514405755891, 5789228615357111146520048038021683988773733487122101869605338720869906159532568379226031634421092153180474991687746456288884260796616315754835057774399955913938411420916390258617521507017839600618566356805942290412597150720, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952986726464679527504806213266711142202650634907989307401347548440268546745966716184963308133324117286003787360321666135338222270039633437564590112167708795719861786958102528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 58 1 (.split 59 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 2 0 (.split 10 0 (.split 14 0 (.split 16 0 (.step 31 (.split 17 0 (.step 3 (.close 5)) (.step 3 (.close 7)))) (.step 7 (.step 3 (.close 5)))) (.step 3 (.step 18 (.step 5 (.close 17))))) (.step 3 (.close 7))) (.step 31 (.step 27 (.step 3 (.close 5))))) (.step 31 (.step 27 (.step 3 (.close 58))))) (.split 55 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 27 (.step 3 (.close 5))))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 23 (.step 18 (.close 5))))) (.step 18 (.step 27 (.step 5 (.close 17)))))) (.step 3 (.close 7))) (.step 44 (.split 67 1 (.split 55 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 10 0 (.step 62 (.step 3 (.close 5))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 3 (.close 18))))) (.step 3 (.step 7 (.step 3 (.close 18))))) (.step 18 (.step 27 (.step 3 (.step 5 (.close 17)))))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 31 (.step 48 (.step 3 (.close 5))))) (.step 3 (.close 7))))) (.step 3 (.step 27 (.step 61 (.step 3 (.split 59 1 (.step 18 (.step 5 (.step 23 (.close 5)))) (.step 44 (.step 3 (.step 31 (.step 32 (.step 3 (.step 18 (.close 5))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 17350741762303288301270021376437205619741561997788952994274389529170594221147122060209573959507628926718544248417047257320812732247787264554669404055441049573986339831185187339513670391432718750610955276716871272567306977280⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.step 61 (.step 62 (.split 51 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 58 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 62 (.split 10 0 (.split 22 0 (.split 24 0 (.step 31 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 18 (.close 3))))) (.step 3 (.step 18 (.close 3)))) (.step 27 (.step 18 (.step 31 (.close 3))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 17 (.close 23))))))) (.step 3 (.step 5 (.step 21 (.step 5 (.step 22 (.step 5 (.step 31 (.close 5))))))))) (.step 27 (.step 53 (.step 61 (.step 3 (.close 5)))))) (.step 48 (.step 53 (.step 58 (.step 3 (.close 27)))))) (.step 27 (.step 31 (.step 44 (.step 23 (.step 48 (.step 23 (.step 18 (.step 53 (.step 3 (.step 17 (.close 18)))))))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 7 (.step 53 (.close 7)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 17350741762303288301270021376437205619741561997788952994274389529170594221153515401240621111597498437845160653011220386316990593164746818007982165376543929563992726730259218896448995946369359514300832730908053680874589257728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 58 (.step 61 (.step 62 (.split 50 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 55 1 (.split 58 1 (.split 56 1 (.split 2 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 52 (.split 10 0 (.split 22 0 (.split 24 0 (.step 31 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 17 (.close 21))))) (.step 3 (.close 7))) (.step 3 (.close 7)))) (.step 3 (.step 7 (.step 18 (.close 3))))) (.step 3 (.step 18 (.close 3)))) (.step 27 (.step 18 (.step 31 (.close 3))))) (.step 3 (.step 5 (.step 27 (.step 5 (.step 17 (.close 21))))))) (.step 3 (.step 5 (.step 22 (.step 5 (.step 31 (.close 5))))))) (.step 27 (.step 34 (.step 52 (.step 3 (.step 31 (.step 58 (.close 61)))))))) (.step 48 (.step 52 (.step 58 (.step 3 (.close 27)))))) (.step 27 (.step 31 (.step 34 (.step 44 (.step 23 (.step 18 (.step 31 (.step 3 (.step 18 (.close 32))))))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 52)))))) (.step 3 (.step 7 (.step 52 (.close 7))))) (.step 52 (.split 56 1 (.step 52 (.step 3 (.close 5))) (.step 3 (.step 5 (.step 21 (.step 22 (.step 23 (.step 31 (.close 5))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248483211542552735967740563782378064049313262000048689575958330072488103258322358876920142221748414322395675934558113892401152⟩
def references : Fin 3 → Box := ![Part0.root, Part1.root, Part2.root]
def proof : Chunks.Proof 3 := (.split 42 1 (.split 43 1 (.step 58 (.split 49 1 (.split 50 1 (.split 51 1 (.split 56 1 (.reuse 0) (.run (.step 3 (.step 58 (.step 61 (.split 59 1 (.split 74 1 (.split 58 1 (.step 43 (.split 10 0 (.split 14 0 (.split 2 0 (.step 3 (.step 5 (.step 3 (.step 5 (.close 16))))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 3 (.close 5)))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 18 (.step 17 (.close 21)))))) (.step 3 (.step 5 (.step 22 (.step 23 (.step 31 (.close 5)))))))))))) (.run (.step 3 (.step 61 (.step 62 (.split 67 1 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53)))))))))))) (.reuse 1)) (.reuse 2))) (.run (.step 3 (.step 27 (.step 3 (.step 46 (.step 9 (.step 27 (.step 46 (.close 52)))))))))) (.run (.step 7 (.step 31 (.step 44 (.split 49 1 (.split 50 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 18 (.step 21 (.step 31 (.close 27)))))) (.step 9 (.step 18 (.step 31 (.step 21 (.step 27 (.step 21 (.step 27 (.close 44))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100831720013824, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690953697962524693974082903962440187475942051369345722076276972549494532389511099907838505188364219251270645448704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 21 (.step 43 (.step 3 (.step 58 (.split 39 1 (.split 42 1 (.split 49 1 (.step 43 (.split 56 1 (.step 42 (.step 58 (.split 59 1 (.split 74 1 (.step 21 (.split 58 1 (.step 43 (.split 10 0 (.split 14 0 (.split 2 0 (.step 3 (.step 5 (.step 3 (.step 5 (.close 16))))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 3 (.close 5)))) (.step 5 (.close 3)))) (.step 5 (.step 18 (.step 17 (.close 21))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.close 5))))))))) (.step 5 (.step 21 (.step 43 (.step 58 (.split 55 1 (.split 59 1 (.split 74 1 (.split 2 0 (.split 14 0 (.step 28 (.split 16 0 (.step 59 (.close 3)) (.step 3 (.close 5)))) (.step 18 (.step 5 (.step 16 (.close 28))))) (.step 28 (.step 5 (.close 3)))) (.step 5 (.close 28))) (.step 3 (.step 5 (.step 21 (.step 22 (.step 16 (.close 28))))))) (.step 5 (.step 3 (.step 28 (.step 22 (.step 16 (.step 21 (.step 16 (.close 31))))))))))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 31 (.step 42 (.step 28 (.step 41 (.step 52 (.close 58))))))))))) (.step 5 (.step 21 (.step 31 (.step 3 (.step 28 (.step 3 (.step 22 (.step 39 (.close 41)))))))))) (.step 5 (.step 21 (.step 31 (.step 32 (.step 41 (.step 5 (.step 27 (.close 42)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690953697962524693974082903962440187475942051369345722076276972549494532389511099907838505188364219251270645448704⟩
def references : Fin 2 → Box := ![Part3.root, Part4.root]
def proof : Chunks.Proof 2 := (.split 38 1 (.split 39 1 (.split 40 1 (.reuse 0) (.run (.step 3 (.step 31 (.step 43 (.step 58 (.step 61 (.split 49 1 (.step 43 (.split 50 1 (.split 59 1 (.split 74 1 (.split 16 0 (.split 58 1 (.step 43 (.close 3)) (.step 5 (.step 3 (.step 27 (.step 17 (.close 21)))))) (.step 3 (.step 5 (.close 18)))) (.step 5 (.step 11 (.step 18 (.step 23 (.step 17 (.step 27 (.step 17 (.close 31))))))))) (.step 3 (.step 5 (.step 23 (.step 27 (.close 31)))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 27 (.step 31 (.close 53))))))))) (.step 3 (.step 5 (.step 23 (.step 27 (.step 31 (.step 52 (.close 5))))))))))))))) (.run (.step 3 (.step 31 (.step 5 (.step 27 (.step 58 (.step 61 (.split 40 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 74 1 (.step 31 (.step 27 (.step 3 (.step 42 (.step 3 (.step 5 (.step 3 (.close 5)))))))) (.step 11 (.step 27 (.step 31 (.step 42 (.step 3 (.close 5))))))) (.step 3 (.step 27 (.step 42 (.step 3 (.close 5)))))) (.step 3 (.step 21 (.step 27 (.step 32 (.step 42 (.close 3))))))) (.step 3 (.step 27 (.step 34 (.step 42 (.step 44 (.close 52))))))) (.step 3 (.step 5 (.step 21 (.step 27 (.step 31 (.close 42))))))))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319683306228182063648466809789138024906881990185147984463239722270448632290344960⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 36 (.step 31 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.step 7 (.step 5 (.step 21 (.close 22)))) (.step 9 (.step 18 (.step 22 (.step 28 (.step 5 (.step 21 (.close 27)))))))) (.step 3 (.step 22 (.step 5 (.close 28))))) (.step 9 (.step 18 (.step 21 (.step 22 (.step 5 (.step 29 (.close 31)))))))) (.step 9 (.step 18 (.step 22 (.step 31 (.step 21 (.close 36))))))) (.step 31 (.step 7 (.step 22 (.step 28 (.step 3 (.close 39))))))) (.step 21 (.step 31 (.step 28 (.step 3 (.step 22 (.close 39))))))))))))) (.run (.step 7 (.step 31 (.step 34 (.step 31 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 56 1 (.split 59 1 (.step 7 (.step 5 (.step 21 (.close 22)))) (.step 9 (.step 15 (.step 18 (.step 31 (.close 21)))))) (.step 3 (.step 29 (.step 5 (.step 16 (.step 21 (.close 22))))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 31 (.close 27))))))) (.step 9 (.step 15 (.step 16 (.step 18 (.step 31 (.step 21 (.close 34)))))))) (.step 31 (.step 7 (.step 28 (.step 3 (.step 22 (.close 37))))))) (.step 16 (.step 21 (.step 31 (.step 28 (.step 3 (.close 37))))))) (.step 31 (.close 37))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.step 3 (.step 42 (.split 49 1 (.split 50 1 (.split 58 1 (.step 3 (.close 7)) (.step 3 (.close 18))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨3618502788666131106986593281521497120414687020801267626233049500250506526720, 17350741762303288301265122493126548277304614147387551354669867297387969003240299500040729897727710421205218809271937431366303988737593342305244419621375475768737348746315472920952367199092651465231752276320273497955268296704⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.split 39 1 (.split 42 1 (.split 49 1 (.step 43 (.split 50 1 (.split 56 1 (.step 27 (.step 58 (.split 59 1 (.split 74 1 (.split 58 1 (.step 43 (.split 10 0 (.split 14 0 (.split 2 0 (.step 3 (.step 5 (.step 3 (.step 5 (.close 16))))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 5 (.close 3))))) (.step 3 (.close 5)))) (.step 5 (.close 3))) (.step 5 (.step 3 (.step 18 (.step 17 (.close 21)))))) (.step 3 (.step 5 (.step 23 (.step 27 (.close 28)))))))) (.step 5 (.step 28 (.step 43 (.step 58 (.split 59 1 (.split 74 1 (.split 16 0 (.split 49 0 (.step 28 (.close 3)) (.step 3 (.step 22 (.step 5 (.step 16 (.close 21)))))) (.step 3 (.step 18 (.step 5 (.step 3 (.close 28)))))) (.step 5 (.close 28))) (.step 3 (.step 5 (.step 22 (.close 28)))))))))) (.step 3 (.step 5 (.step 21 (.step 23 (.step 27 (.step 29 (.step 27 (.step 28 (.close 53))))))))))) (.step 3 (.step 5 (.step 23 (.step 27 (.step 31 (.step 27 (.step 28 (.step 21 (.step 52 (.close 28))))))))))) (.step 5 (.step 28 (.step 29 (.step 3 (.step 22 (.close 28))))))) (.step 5 (.step 21 (.step 27 (.step 29 (.step 27 (.step 5 (.close 28))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264664859336342455549014547889839436527136579482103871563161282160885760⟩
def references : Fin 2 → Box := ![Part6.root, Part7.root]
def proof : Chunks.Proof 2 := (.split 24 1 (.split 25 1 (.reuse 0) (.step 3 (.step 43 (.step 58 (.split 34 1 (.split 36 1 (.split 38 1 (.reuse 1) (.run (.step 5 (.step 10 (.step 21 (.step 28 (.step 3 (.step 43 (.step 58 (.split 49 1 (.split 59 1 (.split 74 1 (.split 16 0 (.split 49 0 (.step 28 (.close 3)) (.step 3 (.step 21 (.close 28)))) (.step 3 (.step 18 (.step 5 (.step 3 (.close 28)))))) (.step 5 (.close 28))) (.step 3 (.step 5 (.step 21 (.close 28))))) (.step 3 (.step 5 (.step 16 (.step 21 (.step 22 (.close 28)))))))))))))))) (.run (.step 3 (.step 5 (.step 28 (.step 29 (.step 3 (.step 22 (.close 28))))))))) (.run (.step 3 (.step 5 (.step 16 (.step 28 (.step 29 (.step 3 (.step 22 (.close 28)))))))))))))) (.run (.step 3 (.step 27 (.step 29 (.split 25 1 (.split 38 1 (.split 40 1 (.split 56 1 (.split 30 1 (.split 34 1 (.step 27 (.step 3 (.step 31 (.step 27 (.close 3))))) (.step 3 (.step 5 (.close 27)))) (.step 3 (.close 18))) (.step 3 (.step 5 (.step 29 (.step 5 (.close 27)))))) (.step 3 (.step 5 (.close 27)))) (.step 3 (.step 5 (.step 21 (.step 28 (.step 29 (.step 5 (.close 27)))))))) (.step 3 (.step 5 (.step 27 (.step 28 (.step 29 (.step 27 (.step 5 (.close 28))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381982036619979003157451930662559636758976769960181760⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.split 17 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 27 (.split 25 1 (.split 38 1 (.step 18 (.step 77 (.split 39 1 (.step 7 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 11 (.close 18)))) (.step 11 (.step 18 (.step 3 (.close 27))))) (.step 18 (.step 3 (.step 27 (.close 53))))) (.step 18 (.step 26 (.step 27 (.close 52)))))) (.step 3 (.step 11 (.step 18 (.step 3 (.step 27 (.close 42))))))))) (.step 3 (.step 5 (.step 18 (.close 28))))) (.step 3 (.step 5 (.step 18 (.close 28)))))))))) (.run (.step 7 (.step 18 (.step 27 (.split 22 1 (.split 25 1 (.split 38 1 (.step 18 (.step 61 (.step 7 (.step 42 (.step 77 (.split 49 1 (.split 50 1 (.split 59 1 (.split 24 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 3)))) (.step 3 (.step 11 (.step 18 (.close 27))))) (.step 18 (.step 3 (.step 27 (.step 42 (.close 53)))))) (.step 18 (.step 22 (.step 27 (.step 42 (.close 52))))))))))) (.step 3 (.step 5 (.step 18 (.close 28))))) (.step 3 (.step 5 (.step 18 (.close 28))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 17 (.close 20))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part8.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350741762303288301265122493126548277304614147387551354669867297387969003237102829525206321682772957959244696919929591506901695331223146516442280310344064984385529715563646461649910980374679403696533515790325580286330404864⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 25 1 (.split 38 1 (.split 39 1 (.split 40 1 (.split 50 1 (.split 56 1 (.split 58 1 (.split 59 1 (.split 24 1 (.step 31 (.step 27 (.step 34 (.step 77 (.split 51 1 (.split 55 1 (.step 3 (.split 74 1 (.split 2 0 (.split 16 0 (.step 31 (.step 18 (.step 27 (.step 3 (.close 5))))) (.step 11 (.step 18 (.close 3)))) (.step 11 (.step 23 (.step 18 (.close 5))))) (.step 11 (.step 17 (.close 3))))) (.step 12 (.step 18 (.step 17 (.step 27 (.step 5 (.close 17))))))) (.step 3 (.close 17))))))) (.step 11 (.step 17 (.step 18 (.step 27 (.close 5)))))) (.step 3 (.step 17 (.step 23 (.step 27 (.step 34 (.step 23 (.step 44 (.step 18 (.step 5 (.close 21))))))))))) (.step 11 (.step 17 (.step 18 (.step 27 (.step 31 (.step 34 (.step 61 (.close 3))))))))) (.step 3 (.step 5 (.step 18 (.step 31 (.step 5 (.close 17))))))) (.step 3 (.step 5 (.step 17 (.step 23 (.step 27 (.step 31 (.step 34 (.step 48 (.step 53 (.step 23 (.step 55 (.step 23 (.step 17 (.step 53 (.close 61)))))))))))))))) (.step 3 (.step 5 (.step 17 (.step 18 (.step 23 (.step 27 (.step 17 (.close 31))))))))) (.step 5 (.step 11 (.step 17 (.step 18 (.step 27 (.step 34 (.step 36 (.step 42 (.step 3 (.close 5))))))))))) (.step 3 (.step 5 (.step 18 (.step 21 (.step 31 (.step 5 (.step 17 (.close 27))))))))) (.step 3 (.step 5 (.step 18 (.step 27 (.step 29 (.step 5 (.close 17)))))))) (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.close 3))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381984959626041258113107201226117490567900120419926016⟩
def references : Fin 2 → Box := ![Part9.root, Part10.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 14 1 (.split 16 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 27 (.split 17 1 (.split 22 1 (.split 25 1 (.split 38 1 (.step 18 (.step 42 (.step 7 (.step 42 (.step 77 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 11 (.close 18)))) (.step 11 (.step 18 (.step 3 (.close 27))))) (.step 18 (.step 3 (.step 27 (.step 42 (.close 53)))))) (.step 18 (.step 21 (.step 27 (.step 42 (.close 52))))))))))) (.step 3 (.step 5 (.step 18 (.close 28))))) (.step 3 (.step 5 (.step 18 (.close 28))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 17 (.close 19))))))) (.step 7 (.step 18 (.step 7 (.step 11 (.close 19))))))))))) (.step 3 (.step 27 (.step 31 (.step 34 (.step 58 (.split 16 1 (.split 17 1 (.reuse 1) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 3 (.close 17))))))))) (.run (.step 3 (.step 5 (.step 11 (.step 17 (.step 18 (.step 17 (.step 3 (.close 19)))))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 14 1 (.split 24 1 (.step 7 (.step 31 (.step 3 (.split 39 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.step 17 (.close 18))))))) (.step 3 (.step 17 (.close 18)))) (.step 3 (.close 17)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes
  · exact Part10.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨3221225472, 17350741762303288301270021376437205619741561997788952994278075039351084007630313794386117467941835248488381090690958395052169731124898365416701319686928264668229329675849381984959626041258113107201226117490567900120422023168⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 2 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 27 (.step 31 (.step 5 (.step 58 (.split 14 1 (.split 25 1 (.split 38 1 (.split 49 1 (.step 5 (.split 39 1 (.step 31 (.step 5 (.step 27 (.step 61 (.step 3 (.split 50 1 (.step 77 (.step 61 (.step 18 (.step 3 (.step 17 (.close 21)))))) (.step 3 (.step 21 (.step 23 (.step 27 (.step 23 (.step 34 (.close 44))))))))))))) (.step 5 (.step 21 (.step 27 (.step 32 (.step 42 (.close 18)))))))) (.step 3 (.step 5 (.step 23 (.step 27 (.step 34 (.step 42 (.step 52 (.step 5 (.close 21)))))))))) (.step 5 (.step 28 (.close 31)))) (.step 5 (.close 28))) (.step 5 (.step 17 (.step 23 (.step 17 (.close 27))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part12.excludes
end FiveColour.Packed.ProjectedChunks.Case87
