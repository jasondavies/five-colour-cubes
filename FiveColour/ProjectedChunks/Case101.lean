module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case101
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231548175077138580140037819542512687120384⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 14⟩]
  else if r.val = 2 then [⟨11592891989185068313591, 5789234131009374248507346766749891415336446658080254882252585026546702981937144087362938485159698842000310822204500455332697475700356713936529532818369645300856559260305089462646221349807102293740064093958240592194881717248, 0⟩]
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
def root : Box := ⟨3221225472, 5783586108473071698929506996965222366134733773348527137630275073014641211963365061407257151770905019981373183719519790822093350474905949501118222832300809514923782105583616072404305743848062463116091197244806638949392973824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 34 0 (.split 22 0 (.split 36 0 (.split 39 0 (.step 55 (.close 3)) (.step 27 (.step 32 (.step 40 (.close 3))))) (.step 3 (.step 23 (.step 26 (.close 31))))) (.step 3 (.step 21 (.close 12)))) (.step 31 (.step 3 (.step 15 (.step 17 (.close 21)))))) (.step 3 (.step 18 (.step 23 (.step 15 (.close 21)))))) (.step 18 (.step 3 (.step 23 (.close 3))))) (.step 18 (.split 17 0 (.step 3 (.step 18 (.step 23 (.close 3)))) (.step 7 (.close 18))))) (.split 16 0 (.split 17 0 (.step 23 (.split 22 0 (.split 34 0 (.split 36 0 (.step 55 (.split 39 0 (.step 55 (.step 3 (.step 12 (.step 17 (.close 21))))) (.step 27 (.step 23 (.step 34 (.step 23 (.step 3 (.close 21)))))))) (.step 3 (.step 23 (.step 12 (.close 31))))) (.step 3 (.step 23 (.step 12 (.close 17))))) (.step 3 (.step 12 (.step 17 (.close 21)))))) (.step 11 (.step 18 (.step 12 (.step 17 (.close 21)))))) (.step 11 (.step 18 (.split 17 0 (.step 3 (.step 12 (.step 17 (.step 18 (.close 21))))) (.step 17 (.close 18))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350747283341930566433056814635378094421879396292588678733489381828235141122834117021716732167367087574170840800491040806086374437543838822596584282743340766864322896296821302269806712779505341936036857771246083884426723328⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 74 1 (.split 10 0 (.split 12 0 (.reuse 0) (.run (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.split 21 0 (.split 22 0 (.split 35 0 (.split 30 0 (.step 40 (.split 34 0 (.step 55 (.step 3 (.close 12))) (.step 15 (.close 3)))) (.step 3 (.step 31 (.step 12 (.step 15 (.close 21)))))) (.step 21 (.split 49 0 (.step 38 (.step 15 (.step 3 (.close 22)))) (.step 15 (.step 12 (.close 3)))))) (.step 3 (.step 23 (.step 3 (.close 15))))) (.step 3 (.step 18 (.step 15 (.step 12 (.step 23 (.close 21)))))))) (.step 3 (.step 18 (.step 22 (.step 3 (.step 12 (.close 15))))))) (.step 3 (.step 18 (.step 21 (.close 3))))) (.step 23 (.step 40 (.step 55 (.split 16 0 (.split 17 0 (.step 15 (.step 9 (.step 23 (.close 3)))) (.step 3 (.close 12))) (.step 3 (.step 12 (.close 17)))))))))) (.run (.step 3 (.step 18 (.step 31 (.split 12 0 (.split 16 0 (.split 14 0 (.split 17 0 (.step 18 (.step 12 (.close 21))) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 3 (.step 7 (.step 3 (.close 12))))) (.step 3 (.step 12 (.close 3))))))))) (.run (.step 11 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.step 77 (.step 23 (.step 44 (.step 3 (.close 12))))) (.step 18 (.step 23 (.step 12 (.close 31))))) (.step 18 (.step 23 (.step 69 (.step 18 (.step 12 (.close 31))))))) (.step 23 (.step 69 (.close 77)))) (.step 17 (.step 3 (.step 18 (.step 23 (.step 31 (.close 32))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579558101483520, 5783586119245830025300575939794769646273237280395623053812135137267120501448128513407678675459694086277874331832380911039546340351169746749494653143986574165218834086291914150875358887149344159095022692106926985041959452672⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 3)) (.step 29 (.step 31 (.step 22 (.step 12 (.close 23)))))) (.step 29 (.step 74 (.close 3)))) (.step 29 (.step 31 (.step 22 (.step 15 (.step 17 (.close 21))))))) (.step 40 (.split 34 0 (.split 35 0 (.step 36 (.step 55 (.step 3 (.close 31)))) (.step 32 (.close 3))) (.step 3 (.step 31 (.step 23 (.close 32))))))) (.step 3 (.step 18 (.step 31 (.step 23 (.step 40 (.step 12 (.close 32)))))))) (.step 18 (.step 22 (.step 31 (.close 23))))) (.step 18 (.step 22 (.step 31 (.step 40 (.step 12 (.close 32))))))) (.step 18 (.step 31 (.step 23 (.step 40 (.step 12 (.close 32))))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 22 (.step 9 (.step 57 (.step 66 (.step 23 (.close 3)))))) (.step 23 (.step 31 (.step 22 (.step 15 (.close 21)))))) (.step 12 (.step 22 (.step 23 (.step 15 (.step 24 (.close 21))))))) (.step 22 (.step 3 (.close 18)))) (.step 23 (.step 31 (.step 23 (.close 18)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 17350758325419215096778723214921340236387974119565902765140055240619506863005372417453778513176160041487847656483139263695400997607936018408437653760652107319292603122302351735100707236720065892706284953670040127636691222528⟩
def references : Fin 2 → Box := ![Part1.root, Part2.root]
def proof : Chunks.Proof 2 := (.split 71 1 (.split 72 1 (.reuse 0) (.run (.step 69 (.split 74 1 (.step 29 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 75 (.step 40 (.step 26 (.step 3 (.close 12))))) (.step 26 (.step 31 (.close 23)))) (.step 31 (.step 40 (.step 69 (.step 31 (.step 15 (.close 18))))))) (.step 31 (.step 38 (.step 3 (.step 18 (.step 31 (.step 21 (.step 12 (.close 15))))))))) (.step 40 (.step 69 (.close 75))))) (.step 23 (.step 40 (.close 69))))))) (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 39 0 (.step 40 (.split 54 0 (.step 74 (.close 3)) (.step 12 (.step 9 (.step 22 (.step 23 (.step 3 (.close 21)))))))) (.step 11 (.step 12 (.step 23 (.step 36 (.step 34 (.step 40 (.step 3 (.close 32))))))))) (.step 11 (.step 18 (.step 12 (.step 23 (.close 32)))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 23 (.step 32 (.close 21)))))))) (.step 11 (.step 12 (.step 18 (.step 17 (.step 22 (.step 21 (.close 23)))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 22 (.step 32 (.close 21)))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 21 (.step 32 (.close 21)))))))))) (.run (.split 12 0 (.step 18 (.step 66 (.step 31 (.step 12 (.step 21 (.close 22)))))) (.step 12 (.step 3 (.close 15)))))) (.run (.step 11 (.step 69 (.step 74 (.step 55 (.close 3))))))) (.run (.step 29 (.step 69 (.step 74 (.step 55 (.close 3))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748387714433024, 5783586108473071698929506996974347247369978163785809480841675655664427668977862181268415536806703570315790538492531616444728093274463234120265411646922186924366532981580121395043748778429320772296650297035484153871572402176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 3)) (.step 29 (.step 31 (.step 22 (.step 12 (.close 23)))))) (.step 21 (.step 29 (.step 32 (.close 3))))) (.step 29 (.step 31 (.step 21 (.step 23 (.close 12)))))) (.step 21 (.step 32 (.step 40 (.step 3 (.step 11 (.close 12))))))) (.step 3 (.step 18 (.step 31 (.step 23 (.step 32 (.step 12 (.close 21)))))))) (.step 18 (.step 21 (.step 31 (.close 23))))) (.step 18 (.step 31 (.step 23 (.step 32 (.step 12 (.close 21))))))) (.step 18 (.step 21 (.step 31 (.step 32 (.step 12 (.close 21))))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 21 (.step 9 (.step 32 (.step 66 (.step 40 (.close 3)))))) (.step 23 (.step 31 (.step 21 (.close 22))))) (.step 12 (.step 21 (.step 3 (.step 18 (.step 23 (.step 15 (.close 24)))))))) (.step 23 (.step 31 (.step 23 (.close 18))))) (.step 21 (.step 3 (.close 18))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748387714433024, 17350758320032835933598087626826348819990914606881038789865048022925675541238721226865342456733880608919628849008529411418992998059086528324538605243934329478172870729323000795940436772681592070902084275370746981239991828480⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 72 1 (.split 74 1 (.split 67 1 (.split 71 1 (.split 10 0 (.split 14 0 (.reuse 0) (.run (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 39 0 (.step 40 (.split 12 0 (.step 67 (.close 3)) (.step 12 (.step 3 (.step 21 (.close 23)))))) (.step 11 (.step 12 (.step 21 (.step 32 (.step 34 (.step 40 (.close 3)))))))) (.step 11 (.step 18 (.step 12 (.step 23 (.close 32)))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 23 (.step 32 (.close 21)))))))) (.step 11 (.step 12 (.step 18 (.step 17 (.step 21 (.step 22 (.close 23)))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 23 (.step 32 (.close 21)))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 21 (.step 32 (.close 21)))))))))) (.run (.split 12 0 (.step 18 (.step 66 (.step 31 (.step 12 (.step 21 (.close 22)))))) (.step 12 (.step 3 (.close 15)))))) (.run (.step 67 (.close 3)))) (.run (.step 3 (.close 55)))) (.run (.step 11 (.step 67 (.step 3 (.step 55 (.step 3 (.close 12)))))))) (.run (.step 29 (.step 67 (.step 3 (.step 69 (.step 32 (.step 23 (.step 3 (.close 12))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 17350758325419215096788520990895658187387370018583107836034696920215869034787387106242355815602307234756865122437878291315379872333603000876590144396571406147282336461476892995402871074903226728986078609912623011734724018176⟩
def references : Fin 2 → Box := ![Part3.root, Part5.root]
def proof : Chunks.Proof 2 := (.split 64 1 (.split 65 1 (.split 67 1 (.reuse 0) (.run (.step 3 (.step 69 (.split 72 1 (.step 3 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.step 12 (.close 42))))) (.step 3 (.step 15 (.close 21)))))))) (.run (.step 3 (.split 72 1 (.split 74 1 (.split 71 1 (.step 3 (.step 68 (.step 18 (.step 3 (.close 15))))) (.split 10 0 (.split 17 0 (.split 36 0 (.split 54 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 18 (.step 68 (.close 3))) (.step 3 (.step 21 (.close 24)))) (.step 3 (.step 24 (.step 15 (.close 21))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 18 (.step 12 (.close 42))))) (.step 3 (.step 31 (.close 15)))) (.step 3 (.step 31 (.step 15 (.close 21))))) (.step 3 (.step 24 (.close 31)))) (.step 3 (.close 18))) (.step 3 (.close 12)))) (.step 3 (.step 18 (.step 12 (.step 61 (.step 12 (.close 74))))))) (.step 3 (.step 26 (.step 31 (.step 15 (.step 57 (.step 15 (.close 74))))))))))) (.step 3 (.step 67 (.split 65 1 (.reuse 1) (.run (.step 3 (.step 67 (.split 10 0 (.split 17 0 (.split 36 0 (.split 54 0 (.split 12 0 (.split 22 0 (.split 34 0 (.split 14 0 (.split 16 0 (.split 35 0 (.step 18 (.step 68 (.close 3))) (.step 3 (.close 21))) (.step 3 (.close 18))) (.step 3 (.step 18 (.step 12 (.close 42))))) (.step 3 (.step 21 (.step 24 (.close 15))))) (.step 3 (.close 18))) (.step 3 (.step 21 (.close 31)))) (.step 3 (.step 21 (.step 31 (.close 15))))) (.step 3 (.step 21 (.step 24 (.close 31))))) (.step 3 (.close 18))) (.step 3 (.close 12))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes
  · exact Part5.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part6

namespace Part7
def root : Box := ⟨8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630616877957120, 5783586113859450862119940351695224700275386865842154315469720011629889883261156982732277838984901900564257801419285665312780573643556807016782896146534886308254135191716650887624507685168779681725157054960653037085967515648⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 67 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 12 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.close 3)) (.step 29 (.step 31 (.step 12 (.step 22 (.close 23)))))) (.step 29 (.step 66 (.step 3 (.close 21))))) (.step 15 (.step 29 (.step 31 (.step 12 (.close 15)))))) (.step 40 (.split 34 0 (.step 12 (.step 67 (.step 55 (.step 3 (.close 31))))) (.step 3 (.step 12 (.step 31 (.step 15 (.step 21 (.close 32))))))))) (.step 3 (.step 18 (.step 31 (.step 12 (.step 23 (.step 32 (.close 21)))))))) (.step 18 (.step 12 (.step 31 (.step 23 (.close 21)))))) (.step 18 (.step 31 (.step 12 (.step 23 (.step 32 (.close 21))))))) (.step 18 (.step 31 (.step 12 (.step 21 (.step 32 (.close 21))))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 43 0 (.step 12 (.step 66 (.close 3))) (.step 9 (.step 3 (.close 11)))) (.step 23 (.step 31 (.close 23)))) (.step 12 (.step 23 (.close 15)))) (.step 23 (.step 31 (.step 23 (.close 18))))) (.step 23 (.step 31 (.step 23 (.close 18)))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.step 12 (.close 66)) (.step 11 (.step 12 (.step 3 (.close 12))))) (.step 11 (.step 18 (.close 12)))) (.step 11 (.step 12 (.close 3)))) (.step 11 (.step 18 (.close 12)))) (.step 11 (.step 18 (.close 12))))) (.split 12 0 (.step 18 (.step 12 (.step 3 (.close 31)))) (.step 12 (.close 3)))) (.step 66 (.close 3))) (.step 3 (.close 55))) (.step 66 (.close 3))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨8104522595470689372094546608771799123071184047348509570304018222052056272290836223436927829974812098219136497287696853871865529444163623648216552410378835326291370709771794513920, 17350758325419215096788520990895667098404201320037666840043678675691909575646114449157154275436203327082694298937955082967175700011546023512163128542284682123855599269744762776795634805569365569042012296096474352116954038272⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 26 (.step 44 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 44 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 34 0 (.step 62 (.close 23)) (.step 3 (.step 9 (.step 18 (.step 3 (.step 26 (.step 31 (.step 23 (.close 12))))))))) (.step 9 (.step 26 (.split 10 0 (.split 35 0 (.step 62 (.close 3)) (.step 15 (.step 21 (.step 40 (.close 3))))) (.step 3 (.close 12)))))) (.step 3 (.step 26 (.step 18 (.step 3 (.step 12 (.close 32))))))) (.step 3 (.close 23))) (.step 3 (.step 27 (.step 44 (.step 23 (.step 55 (.step 3 (.close 12)))))))) (.step 3 (.step 27 (.step 53 (.step 18 (.step 3 (.step 23 (.close 12)))))))) (.step 27 (.step 44 (.step 23 (.step 52 (.step 55 (.step 3 (.step 12 (.step 17 (.close 18))))))))))) (.step 9 (.step 23 (.close 26)))) (.step 26 (.step 44 (.step 55 (.close 74))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 26 (.step 44 (.step 55 (.close 67)))))) (.step 3 (.step 26 (.step 44 (.step 66 (.step 55 (.close 66)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416711979597824, 17350752798994193668425254426674242867772622854815013976297503855970189303955583666869277384364924360505623104189166185555109963423783278746430659130025694278148496199182973937983358121053769283131500278894515627688124743680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 74 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 12 0 (.split 22 0 (.split 34 0 (.split 30 0 (.split 39 0 (.split 40 0 (.split 49 0 (.step 40 (.close 3)) (.step 27 (.step 40 (.step 3 (.close 12))))) (.step 3 (.step 31 (.step 22 (.close 23))))) (.step 27 (.step 42 (.close 61)))) (.step 3 (.step 32 (.close 12)))) (.step 3 (.step 31 (.step 23 (.close 32))))) (.step 3 (.step 18 (.step 23 (.step 40 (.step 12 (.close 32))))))) (.step 34 (.step 22 (.step 9 (.step 57 (.step 23 (.step 3 (.close 21)))))))) (.step 27 (.split 12 0 (.step 18 (.step 3 (.step 22 (.step 3 (.close 23))))) (.step 3 (.step 12 (.step 18 (.step 22 (.step 15 (.step 21 (.close 23)))))))))) (.step 27 (.step 36 (.step 18 (.step 3 (.step 22 (.step 40 (.step 12 (.close 32))))))))) (.step 27 (.split 35 0 (.split 40 0 (.split 51 0 (.split 63 0 (.step 61 (.step 3 (.close 18))) (.step 18 (.step 12 (.step 21 (.step 22 (.close 32)))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 18 (.step 21 (.close 32))))))) (.step 27 (.step 34 (.step 61 (.step 12 (.step 3 (.step 18 (.close 21)))))))) (.step 27 (.split 12 0 (.step 18 (.step 61 (.close 3))) (.step 3 (.close 12))))) (.step 40 (.step 27 (.step 23 (.step 32 (.step 23 (.close 18))))))) (.step 3 (.close 12))) (.step 11 (.step 44 (.step 61 (.step 40 (.close 3)))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part9

namespace Part10
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416711979597824, 17350758325419215096788520990895667098404201320045581412890818020781845656318743159238278478607442105959944316732927794170584719760996148346122905981951807609488115728604006457893450844288327046005272877469805768825712410624⟩
def references : Fin 1 → Box := ![Part9.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 40 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.reuse 0) (.run (.step 11 (.step 36 (.step 40 (.step 55 (.step 61 (.split 34 0 (.split 40 0 (.split 42 0 (.split 65 0 (.split 10 0 (.step 61 (.step 12 (.step 15 (.close 21)))) (.step 12 (.step 18 (.step 40 (.step 32 (.close 42)))))) (.step 18 (.step 22 (.step 55 (.step 12 (.close 42)))))) (.step 18 (.step 22 (.step 40 (.step 12 (.close 42)))))) (.step 18 (.step 22 (.step 40 (.step 12 (.close 42)))))) (.step 17 (.step 18 (.step 22 (.step 34 (.close 40))))))))))))) (.run (.step 3 (.step 18 (.close 61))))) (.run (.step 11 (.step 32 (.step 40 (.step 51 (.step 55 (.step 67 (.step 68 (.step 74 (.step 77 (.split 65 1 (.split 34 0 (.split 40 0 (.split 42 0 (.step 42 (.step 61 (.step 55 (.step 3 (.close 12))))) (.step 18 (.step 23 (.step 40 (.step 12 (.close 42)))))) (.step 18 (.step 23 (.step 40 (.step 12 (.close 42)))))) (.step 17 (.step 18 (.step 23 (.step 34 (.step 31 (.close 40))))))) (.step 3 (.step 18 (.step 42 (.step 12 (.close 61))))))))))))))))) (.run (.step 11 (.step 12 (.step 34 (.step 40 (.step 51 (.step 55 (.step 66 (.step 67 (.step 68 (.step 74 (.step 77 (.split 65 1 (.split 42 0 (.step 61 (.step 66 (.step 3 (.close 18)))) (.step 18 (.step 23 (.close 40)))) (.step 3 (.step 18 (.close 42))))))))))))))))) (.run (.step 3 (.step 26 (.step 27 (.step 44 (.step 55 (.step 61 (.step 40 (.close 3))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 5783586108473071698929506996965222366134733773348527137630282271276712481077577558268869449341879211496762466786132752031009529415035023881710733297398575740295221979040629705836502877075080481991378526741999830271841533952⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 14 0 (.split 16 0 (.split 36 0 (.split 17 0 (.step 9 (.step 57 (.close 3))) (.step 3 (.step 18 (.step 22 (.step 12 (.close 21)))))) (.step 9 (.step 22 (.step 31 (.step 23 (.close 12)))))) (.step 3 (.step 18 (.step 21 (.step 3 (.close 12)))))) (.step 55 (.split 36 0 (.split 39 0 (.split 42 0 (.step 23 (.close 3)) (.step 3 (.step 12 (.close 23)))) (.step 12 (.step 21 (.step 9 (.close 23))))) (.step 3 (.step 12 (.step 22 (.close 23))))))) (.step 9 (.step 21 (.step 40 (.step 55 (.close 57)))))) (.step 9 (.step 31 (.step 3 (.step 15 (.step 23 (.close 21))))))) (.step 3 (.step 31 (.step 23 (.close 32))))) (.step 3 (.step 18 (.step 23 (.step 31 (.step 23 (.step 3 (.close 21)))))))) (.step 9 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.split 51 0 (.split 58 0 (.step 15 (.step 40 (.step 55 (.close 57)))) (.step 12 (.step 22 (.step 15 (.step 23 (.close 3)))))) (.step 3 (.step 12 (.step 15 (.step 3 (.step 22 (.close 23))))))) (.step 12 (.step 21 (.step 15 (.step 36 (.step 3 (.close 23))))))) (.step 15 (.step 22 (.step 31 (.step 3 (.step 12 (.step 21 (.close 23)))))))) (.step 15 (.step 21 (.close 57)))) (.step 15 (.close 3))) (.step 15 (.step 3 (.step 23 (.step 51 (.step 31 (.step 12 (.step 23 (.close 21))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 11567177737984785663031847198749922980806849356709675425878574732288521473360631659746122002608733842230241165155196745322615786702688006675301496311944179672098463218199011236466505347530572818166700697037913882811619606528⟩
def references : Fin 1 → Box := ![Part11.root]
def proof : Chunks.Proof 1 := (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 67 1 (.split 74 1 (.split 10 0 (.reuse 0) (.run (.step 9 (.split 14 0 (.split 21 0 (.split 34 0 (.split 36 0 (.split 39 0 (.step 31 (.step 15 (.step 3 (.step 12 (.step 21 (.close 22)))))) (.step 3 (.step 12 (.step 21 (.close 22))))) (.step 3 (.step 12 (.close 21)))) (.step 3 (.step 12 (.close 15)))) (.step 3 (.close 12))) (.step 3 (.close 12)))))) (.run (.step 23 (.step 9 (.step 23 (.step 12 (.step 15 (.close 23)))))))) (.run (.step 3 (.close 15)))) (.run (.step 9 (.step 26 (.step 57 (.step 23 (.close 3))))))) (.run (.step 22 (.step 23 (.step 29 (.step 55 (.step 57 (.split 16 0 (.split 21 0 (.split 22 0 (.split 65 0 (.split 10 0 (.step 57 (.close 12)) (.step 12 (.step 15 (.step 23 (.step 31 (.step 21 (.close 26))))))) (.step 31 (.step 36 (.step 55 (.step 15 (.close 21)))))) (.step 23 (.step 26 (.step 31 (.close 15))))) (.step 23 (.step 31 (.step 15 (.close 21))))) (.step 21 (.step 23 (.close 31))))))))))) (.run (.step 3 (.step 31 (.close 57))))) (.run (.step 21 (.step 23 (.step 29 (.step 32 (.step 51 (.step 55 (.step 67 (.step 68 (.step 74 (.step 75 (.split 10 0 (.split 21 0 (.split 12 0 (.step 67 (.step 40 (.step 3 (.step 23 (.close 3))))) (.step 12 (.step 15 (.step 40 (.step 3 (.step 26 (.close 3))))))) (.step 23 (.close 31))) (.step 3 (.step 12 (.step 3 (.close 15)))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part11.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 17350758325419215096788520990895667098404201320045581412890825219043916925432955656099890776178416297475333599799540755379500898701125222726715416447049573834859555602061020091325647977514015836884775291094095153087880626176⟩
def references : Fin 1 → Box := ![Part12.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 23 (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 0) (.run (.step 12 (.step 23 (.step 29 (.step 51 (.step 55 (.step 66 (.step 67 (.step 68 (.step 74 (.step 75 (.split 65 1 (.split 16 0 (.split 21 0 (.split 22 0 (.step 15 (.step 57 (.step 55 (.step 3 (.close 21))))) (.step 23 (.step 15 (.step 26 (.step 3 (.close 21)))))) (.step 15 (.step 23 (.step 31 (.close 21))))) (.step 21 (.step 15 (.step 3 (.step 18 (.step 23 (.close 26))))))) (.step 3 (.step 15 (.step 31 (.step 21 (.close 57)))))))))))))))))) (.run (.step 3 (.step 9 (.step 26 (.step 44 (.step 55 (.step 57 (.step 23 (.close 3)))))))))) (.run (.step 3 (.step 22 (.step 23 (.step 40 (.step 57 (.split 16 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 40 0 (.split 10 0 (.step 57 (.step 11 (.close 12))) (.step 3 (.step 12 (.step 23 (.step 21 (.close 26)))))) (.step 3 (.step 40 (.step 12 (.close 21))))) (.step 3 (.step 15 (.step 23 (.step 34 (.close 40)))))) (.step 3 (.step 23 (.step 12 (.close 21))))) (.step 3 (.step 23 (.step 12 (.close 21))))) (.step 3 (.step 21 (.close 23)))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part12.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 17350758325419215096788520981551788713513945512268461964416628585662591653038651105364538026559579251610224356351625706084342712701770369794276699857596617269171926685161729026237014818119499639170871738380128130848394313728⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 32 (.step 57 (.step 61 (.split 51 1 (.split 59 1 (.split 63 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 58 1 (.split 64 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 34 0 (.step 53 (.step 3 (.close 21))) (.step 3 (.step 9 (.step 18 (.step 3 (.step 21 (.step 31 (.step 23 (.close 12))))))))) (.step 9 (.step 21 (.split 10 0 (.split 36 0 (.step 53 (.close 3)) (.step 3 (.step 15 (.step 22 (.step 12 (.step 23 (.close 26))))))) (.step 3 (.close 12)))))) (.step 3 (.step 27 (.step 55 (.step 3 (.close 12)))))) (.step 3 (.step 21 (.step 18 (.close 23))))) (.step 3 (.step 27 (.step 55 (.close 53))))) (.step 3 (.step 21 (.step 18 (.step 3 (.step 12 (.close 32))))))) (.step 27 (.step 52 (.step 23 (.step 55 (.close 53)))))) (.step 32 (.close 3))) (.step 27 (.step 32 (.step 61 (.close 53))))) (.step 9 (.step 21 (.step 32 (.step 53 (.step 57 (.close 53))))))) (.step 27 (.step 23 (.step 32 (.step 44 (.step 55 (.step 61 (.split 54 1 (.step 23 (.step 77 (.step 32 (.close 3)))) (.step 21 (.step 23 (.close 3))))))))))) (.step 9 (.step 21 (.step 23 (.step 26 (.step 32 (.step 40 (.step 55 (.step 3 (.step 53 (.step 3 (.close 15)))))))))))) (.step 32 (.step 55 (.close 74)))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 32 (.step 55 (.step 66 (.close 12)))))) (.step 26 (.step 44 (.step 53 (.step 55 (.close 53)))))) (.step 3 (.step 53 (.close 7))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635883701843190724303217294794053595643915735143662319339448429819800998046029887084538548823705583179409028109475659584732260694356149854476569438846976⟩
def references : Fin 6 → Box := ![Part6.root, Part7.root, Part8.root, Part10.root, Part13.root, Part14.root]
def proof : Chunks.Proof 6 := (.split 50 1 (.split 51 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 0) (.step 66 (.step 3 (.split 65 1 (.split 72 1 (.split 74 1 (.reuse 1) (.run (.step 11 (.step 66 (.step 3 (.step 69 (.step 12 (.step 18 (.close 21))))))))) (.run (.step 29 (.step 66 (.step 3 (.step 55 (.step 3 (.close 31)))))))) (.run (.step 3 (.step 66 (.split 16 0 (.split 17 0 (.split 12 0 (.split 14 0 (.split 22 0 (.split 34 0 (.split 35 0 (.step 68 (.close 3)) (.step 3 (.step 21 (.close 31)))) (.step 3 (.step 15 (.close 24)))) (.step 3 (.close 18))) (.step 3 (.step 12 (.close 18)))) (.step 3 (.step 15 (.close 24)))) (.step 3 (.close 18))) (.step 3 (.close 18)))))))))) (.reuse 2)) (.reuse 3)) (.reuse 4)) (.run (.step 3 (.step 51 (.step 3 (.step 57 (.step 61 (.split 59 1 (.split 67 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 58 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.step 22 (.close 12)))) (.step 3 (.step 22 (.step 12 (.close 36))))) (.step 3 (.step 12 (.close 36)))) (.step 3 (.step 15 (.step 21 (.step 15 (.close 22)))))) (.step 3 (.step 36 (.step 12 (.step 42 (.step 12 (.close 51))))))) (.step 3 (.step 22 (.step 15 (.step 21 (.step 15 (.close 51))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 54))))))))))))) (.step 3 (.reuse 5)))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part8.excludes
  · exact Part10.excludes
  · exact Part13.excludes
  · exact Part14.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 17350758325419215096788520981542659376770285467047681535041819167551501239144507910875375632625652096140517164566375299040653554652934383737824754051107831541679350424396424823673918298680467768214600139764357095057287806976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 52 (.split 54 1 (.split 58 1 (.split 63 1 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 12 0 (.split 34 0 (.split 35 0 (.step 52 (.step 3 (.close 21))) (.step 9 (.step 53 (.step 40 (.step 52 (.close 3)))))) (.step 3 (.step 9 (.step 18 (.step 3 (.step 31 (.step 12 (.step 17 (.close 21))))))))) (.step 9 (.step 34 (.split 10 0 (.split 34 0 (.step 52 (.step 3 (.close 12))) (.step 3 (.step 12 (.close 15)))) (.step 3 (.close 12)))))) (.step 3 (.step 27 (.step 34 (.step 18 (.step 3 (.step 12 (.step 23 (.close 32))))))))) (.step 3 (.step 17 (.step 18 (.step 12 (.close 23)))))) (.step 3 (.step 27 (.step 55 (.step 34 (.step 18 (.close 3))))))) (.step 3 (.step 27 (.step 53 (.step 18 (.step 3 (.step 12 (.close 21)))))))) (.step 27 (.step 34 (.step 52 (.close 3))))) (.step 12 (.close 3))) (.step 12 (.step 27 (.step 34 (.step 61 (.close 52)))))) (.step 9 (.step 12 (.step 52 (.step 57 (.close 52))))))) (.step 12 (.step 27 (.step 34 (.step 44 (.step 23 (.step 53 (.step 23 (.step 55 (.step 3 (.step 52 (.step 3 (.close 18))))))))))))) (.step 9 (.step 12 (.step 23 (.step 26 (.step 40 (.step 55 (.step 57 (.split 50 1 (.split 58 1 (.step 40 (.step 75 (.step 12 (.close 3)))) (.step 12 (.step 22 (.step 23 (.step 34 (.step 40 (.close 3))))))) (.step 21 (.close 52))))))))))) (.step 12 (.step 55 (.close 74)))) (.step 3 (.step 7 (.close 52)))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991354449690624, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059938950007945587715116986772232620521696225283893079303532715341152510270074588383792816426799758825699472753019885897908224⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.step 44 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.split 74 1 (.step 31 (.step 3 (.close 7))) (.step 3 (.step 31 (.step 12 (.close 40))))) (.step 29 (.step 31 (.step 12 (.step 40 (.close 74))))))) (.step 3 (.step 29 (.step 31 (.step 40 (.close 67)))))) (.step 3 (.step 29 (.step 31 (.step 40 (.close 66))))))) (.step 7 (.step 9 (.step 18 (.step 23 (.step 26 (.step 31 (.step 12 (.close 21))))))))) (.step 3 (.step 9 (.step 23 (.step 26 (.step 31 (.step 12 (.step 40 (.close 57))))))))) (.step 7 (.step 9 (.step 18 (.step 23 (.step 21 (.step 26 (.step 31 (.step 40 (.step 44 (.close 53))))))))))) (.step 7 (.step 9 (.step 12 (.step 18 (.step 23 (.step 26 (.step 31 (.step 44 (.close 52)))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343948716212224, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944114507701761532296298610576626545444884695478737750558376659865591565318622066182075717506319101362344559363831392894976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 31 (.step 68 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 31 (.step 68 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.split 71 1 (.split 74 1 (.step 43 (.step 3 (.step 18 (.close 23)))) (.step 11 (.step 18 (.step 23 (.step 12 (.close 42)))))) (.step 23 (.step 31 (.step 18 (.step 12 (.step 61 (.step 12 (.close 74))))))))) (.step 18 (.step 31 (.close 67)))) (.step 12 (.step 18 (.step 31 (.close 66))))) (.step 3 (.step 23 (.step 31 (.step 12 (.close 21)))))))) (.step 3 (.step 27 (.step 43 (.step 31 (.step 61 (.step 3 (.step 18 (.step 23 (.close 43)))))))))) (.step 3 (.step 9 (.step 23 (.step 24 (.step 31 (.step 3 (.close 57)))))))) (.step 3 (.step 21 (.step 23 (.step 31 (.close 53)))))) (.step 3 (.step 12 (.step 23 (.step 31 (.step 34 (.close 52)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350752798994193668425254426674242867772622854811056689873934183425224615571251797477990176285557230213783173448189423590190758386731102298606760699437141502545721043286921989058248341171224083007933977656814271804370583552⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 74 1 (.split 51 1 (.split 58 1 (.split 42 1 (.split 67 1 (.split 72 1 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 12 0 (.split 22 0 (.split 34 0 (.step 42 (.step 3 (.close 12))) (.step 3 (.step 31 (.step 23 (.close 32))))) (.step 3 (.step 18 (.step 23 (.step 32 (.step 12 (.close 21))))))) (.step 34 (.step 21 (.step 9 (.step 32 (.step 40 (.close 3))))))) (.step 27 (.step 32 (.step 18 (.step 3 (.step 21 (.step 3 (.close 23)))))))) (.step 27 (.step 36 (.step 18 (.step 3 (.step 23 (.step 32 (.step 12 (.close 21))))))))) (.step 27 (.split 35 0 (.split 40 0 (.split 51 0 (.split 63 0 (.step 42 (.close 3)) (.step 18 (.step 12 (.step 21 (.close 32))))) (.step 3 (.close 18))) (.step 3 (.close 18))) (.step 3 (.step 18 (.step 21 (.close 32))))))) (.step 27 (.step 34 (.step 42 (.step 3 (.close 12)))))) (.step 27 (.split 12 0 (.step 18 (.step 42 (.close 3))) (.step 3 (.close 12))))) (.step 40 (.step 27 (.step 23 (.step 32 (.step 23 (.close 18))))))) (.step 3 (.close 12))) (.step 3 (.step 31 (.step 38 (.step 23 (.close 12)))))) (.step 27 (.step 42 (.step 15 (.step 26 (.close 31)))))) (.step 3 (.step 12 (.close 36)))) (.step 11 (.step 42 (.step 31 (.step 40 (.step 44 (.step 40 (.close 3)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350752809766951994796323378856802325053457861527113401750373219184862885774290450080554821501756481613902140398248598660050945487154656808424710143748026808233683728681045554352605694850479381649503736482166285847018602496⟩
def references : Fin 1 → Box := ![Part19.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.reuse 0) (.run (.step 11 (.step 32 (.step 36 (.step 40 (.step 55 (.step 61 (.step 77 (.split 34 0 (.split 40 0 (.split 42 0 (.step 42 (.step 61 (.step 55 (.step 3 (.close 12))))) (.step 18 (.step 23 (.step 40 (.step 12 (.close 42)))))) (.step 18 (.step 23 (.step 40 (.step 12 (.close 42)))))) (.step 17 (.step 18 (.step 23 (.step 34 (.step 31 (.close 40)))))))))))))))) (.run (.step 3 (.step 18 (.close 42))))) (.run (.step 11 (.step 32 (.step 40 (.step 42 (.step 67 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 42 (.step 12 (.step 15 (.close 21)))) (.step 18 (.step 21 (.step 40 (.step 12 (.close 42)))))) (.step 18 (.step 21 (.step 40 (.step 12 (.close 42)))))) (.step 18 (.step 21 (.step 36 (.step 40 (.close 12)))))) (.step 17 (.step 18 (.step 21 (.step 34 (.step 31 (.step 36 (.close 40))))))))))))))) (.run (.step 11 (.step 12 (.step 32 (.step 34 (.step 40 (.step 51 (.step 55 (.step 66 (.step 67 (.step 68 (.step 74 (.step 77 (.split 65 1 (.split 36 0 (.step 61 (.split 40 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 42 0 (.step 42 (.close 3)) (.step 18 (.step 23 (.step 40 (.close 42))))) (.step 18 (.close 42))) (.step 18 (.step 23 (.close 42)))) (.step 18 (.step 36 (.close 42)))) (.step 18 (.step 23 (.step 40 (.close 42)))))) (.step 18 (.step 23 (.step 36 (.step 31 (.step 40 (.close 42))))))) (.step 3 (.step 18 (.close 42)))))))))))))))))) (.run (.step 3 (.step 26 (.step 27 (.step 42 (.step 44 (.step 55 (.close 62)))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part19.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158554670789637782293759363827451745685364370135550157247147308771008817825033978532399726631546582612214152167424⟩
def references : Fin 5 → Box := ![Part15.root, Part16.root, Part17.root, Part18.root, Part20.root]
def proof : Chunks.Proof 5 := (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.reuse 0) (.step 3 (.step 12 (.step 53 (.step 3 (.step 57 (.step 61 (.split 51 1 (.split 59 1 (.split 64 1 (.reuse 1) (.run (.step 3 (.step 12 (.step 53 (.step 55 (.step 67 (.close 21)))))))) (.run (.step 26 (.step 44 (.step 52 (.step 55 (.close 52))))))) (.run (.step 3 (.step 52 (.close 7)))))))))))) (.run (.step 3 (.step 9 (.step 27 (.step 47 (.step 3 (.step 52 (.step 53 (.split 51 1 (.split 59 1 (.split 67 1 (.split 49 1 (.split 50 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.step 11 (.close 9)))) (.step 3 (.step 11 (.close 9)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 46)))))) (.step 3 (.close 46))) (.step 3 (.step 9 (.step 27 (.close 46))))) (.step 3 (.close 46)))))))))))) (.reuse 2)) (.reuse 3)) (.step 3 (.step 27 (.step 31 (.step 40 (.step 42 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.reuse 4) (.run (.step 3 (.step 21 (.step 23 (.step 32 (.step 36 (.step 40 (.step 61 (.step 62 (.split 21 0 (.split 22 0 (.step 9 (.step 57 (.step 23 (.step 3 (.close 26))))) (.step 3 (.step 23 (.close 12)))) (.step 3 (.step 23 (.close 12)))))))))))))) (.run (.step 3 (.step 21 (.step 27 (.step 32 (.step 42 (.close 3)))))))) (.run (.step 3 (.step 12 (.step 27 (.step 34 (.step 42 (.step 44 (.step 52 (.close 23)))))))))) (.run (.step 3 (.step 21 (.step 24 (.step 27 (.step 31 (.step 42 (.step 43 (.step 31 (.step 42 (.step 18 (.step 42 (.step 23 (.close 43)))))))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part18.excludes
  · exact Part20.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350752804380572831610788907437461788858168258001426185890341258534504035203579432443159530761314537444937287945049893109735366561837009323697366120545826282447063673128458185784840174846713329982157736651180234291541966848⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 74 1 (.step 21 (.split 39 1 (.split 51 1 (.step 75 (.split 54 1 (.split 63 1 (.split 64 1 (.split 67 1 (.step 29 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 38 (.step 3 (.close 12))) (.step 31 (.step 38 (.step 3 (.step 12 (.close 21)))))) (.step 21 (.step 3 (.step 18 (.step 31 (.close 23)))))) (.step 31 (.step 40 (.step 31 (.step 18 (.close 21)))))) (.step 21 (.step 3 (.step 18 (.step 31 (.close 32)))))) (.step 40 (.step 38 (.step 3 (.step 12 (.close 18)))))) (.step 21 (.split 14 0 (.split 17 0 (.step 38 (.split 21 0 (.step 38 (.close 3)) (.step 3 (.step 15 (.step 18 (.step 23 (.step 3 (.close 24)))))))) (.step 22 (.step 3 (.step 18 (.step 23 (.close 3)))))) (.step 15 (.step 23 (.close 26)))))) (.step 31 (.split 71 1 (.split 12 0 (.step 3 (.step 31 (.step 12 (.step 21 (.close 22))))) (.step 15 (.step 3 (.step 12 (.close 3))))) (.step 31 (.step 12 (.step 38 (.close 12)))))))) (.step 3 (.step 15 (.close 21)))) (.step 21 (.step 32 (.step 38 (.close 67))))) (.step 29 (.step 66 (.step 3 (.close 38))))) (.step 9 (.step 21 (.step 38 (.step 57 (.close 38))))))) (.step 3 (.step 21 (.step 22 (.step 15 (.close 38)))))) (.step 3 (.step 32 (.close 3))))) (.step 3 (.step 23 (.step 32 (.step 40 (.step 66 (.step 67 (.step 69 (.step 23 (.step 40 (.step 74 (.step 38 (.step 3 (.step 17 (.step 18 (.step 23 (.close 74))))))))))))))))) (.step 3 (.step 21 (.step 31 (.close 38))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372461800561940358166010287114963593003093777952223450970828129561016929959926256270169580458369871589146624⟩
def references : Fin 1 → Box := ![Part22.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 9 (.step 21 (.step 31 (.step 32 (.step 38 (.step 57 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 42 1 (.split 49 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 21 (.step 23 (.step 26 (.step 32 (.step 40 (.step 55 (.step 57 (.step 38 (.step 3 (.close 12)))))))))))))) (.run (.step 3 (.step 21 (.step 32 (.step 40 (.step 27 (.close 61)))))))) (.run (.step 3 (.step 9 (.step 12 (.step 21 (.step 23 (.step 32 (.step 52 (.step 40 (.step 57 (.step 61 (.split 58 1 (.step 75 (.step 55 (.split 71 1 (.split 10 0 (.split 12 0 (.step 38 (.step 26 (.step 38 (.step 3 (.step 12 (.step 22 (.step 32 (.close 40)))))))) (.step 12 (.step 15 (.step 38 (.step 26 (.step 31 (.step 38 (.close 52)))))))) (.step 3 (.step 12 (.step 15 (.close 26))))) (.step 12 (.step 22 (.step 23 (.step 32 (.close 38)))))))) (.step 12 (.step 22 (.step 23 (.step 32 (.step 34 (.step 40 (.close 3)))))))))))))))))))) (.run (.step 3 (.step 21 (.step 29 (.step 31 (.step 3 (.step 26 (.close 38))))))))) (.run (.step 3 (.step 21 (.step 29 (.step 31 (.step 3 (.step 38 (.close 3)))))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986546435457024, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424713774431401999524729891650021243217920269897929539218857543668616592060342213356414803378176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.step 34 (.step 31 (.step 75 (.split 35 1 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.split 74 1 (.split 39 1 (.step 31 (.step 3 (.close 7))) (.step 3 (.step 31 (.close 34)))) (.step 3 (.step 31 (.step 12 (.step 17 (.close 34)))))) (.step 29 (.step 31 (.step 17 (.close 34)))))) (.step 3 (.step 29 (.step 31 (.step 34 (.step 17 (.step 66 (.step 17 (.close 67))))))))) (.step 3 (.step 29 (.step 31 (.step 34 (.close 66)))))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 23 (.step 26 (.step 31 (.step 21 (.close 34)))))))))) (.step 3 (.step 9 (.step 15 (.step 23 (.step 31 (.step 21 (.close 34)))))))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 21 (.step 23 (.step 21 (.step 31 (.step 34 (.step 52 (.close 53)))))))))))) (.step 7 (.step 9 (.step 12 (.step 15 (.step 17 (.step 18 (.step 31 (.step 34 (.close 52)))))))))) (.step 7 (.step 31 (.step 7 (.step 26 (.close 37)))))) (.step 7 (.step 31 (.step 7 (.close 37))))) (.step 3 (.step 21 (.step 29 (.step 31 (.close 37))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428541398061974242372834716871091358815949515300822941740029827170172928⟩
def references : Fin 3 → Box := ![Part21.root, Part23.root, Part24.root]
def proof : Chunks.Proof 3 := (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 36 (.step 31 (.step 57 (.step 75 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 74 1 (.split 39 1 (.split 54 1 (.step 31 (.step 40 (.step 31 (.step 3 (.close 7))))) (.step 9 (.step 22 (.close 31)))) (.step 3 (.step 31 (.step 22 (.step 12 (.close 36)))))) (.step 3 (.step 31 (.close 36)))))) (.step 3 (.step 29 (.step 31 (.step 36 (.close 67)))))) (.step 3 (.step 29 (.step 31 (.step 36 (.step 51 (.close 66))))))) (.step 7 (.step 9 (.step 18 (.step 22 (.step 23 (.step 26 (.step 31 (.step 12 (.close 21)))))))))) (.step 7 (.step 9 (.step 18 (.step 21 (.step 22 (.step 23 (.step 21 (.step 31 (.close 53)))))))))) (.step 7 (.step 9 (.step 12 (.step 18 (.step 22 (.step 23 (.step 31 (.step 36 (.close 52)))))))))) (.step 7 (.step 31 (.step 7 (.step 26 (.step 38 (.close 39))))))))))))))) (.reuse 1)) (.reuse 2)) (.run (.step 3 (.step 7 (.step 18 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.step 18 (.step 31 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 31))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 18 (.step 31 (.close 66))))))) (.step 3 (.close 7))) (.step 3 (.close 18))) (.step 3 (.close 31))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 18 (.close 52))))) (.step 3 (.close 18))) (.step 3 (.close 31))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part21.excludes
  · exact Part23.excludes
  · exact Part24.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨3291009114642412084309938365114701009965471731267159729918443520, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750845221134557915601384484729909347490578749691818672128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 31 (.step 43 (.step 68 (.split 35 1 (.split 39 1 (.step 31 (.split 49 1 (.split 50 1 (.split 54 1 (.step 18 (.step 68 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.step 43 (.split 71 1 (.split 72 1 (.step 24 (.step 3 (.step 18 (.step 15 (.close 21))))) (.step 9 (.step 18 (.step 24 (.step 26 (.step 15 (.close 21))))))) (.step 18 (.step 31 (.step 15 (.step 57 (.step 15 (.close 74))))))))) (.step 9 (.step 18 (.step 21 (.step 67 (.close 24)))))) (.step 9 (.step 12 (.step 18 (.close 66))))) (.step 3 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 18 (.step 3 (.step 12 (.step 57 (.step 12 (.close 61)))))))))) (.step 3 (.step 9 (.step 24 (.step 18 (.step 57 (.step 3 (.step 18 (.close 24))))))))) (.step 3 (.step 18 (.step 21 (.close 53))))) (.step 3 (.step 12 (.step 18 (.step 34 (.close 52))))))) (.step 3 (.step 18 (.step 3 (.step 21 (.step 24 (.step 42 (.close 3)))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 24 (.step 31 (.step 38 (.close 66)))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2993155353253689176481146537402947624255353069240320, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848214289911169290560965876446750438203005041666686976⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.step 22 (.step 77 (.split 22 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.split 64 1 (.step 7 (.step 74 (.split 72 1 (.step 23 (.step 18 (.step 3 (.close 7)))) (.step 3 (.step 18 (.step 15 (.step 21 (.close 22)))))))) (.step 3 (.step 11 (.step 18 (.step 22 (.close 67)))))) (.step 3 (.step 11 (.step 18 (.step 22 (.step 51 (.close 66)))))))) (.step 7 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 11 (.step 18 (.step 12 (.step 22 (.close 61))))))) (.step 7 (.step 18 (.step 22 (.close 53))))) (.step 7 (.step 12 (.step 18 (.step 22 (.close 52)))))) (.step 3 (.step 11 (.step 18 (.step 22 (.close 42)))))) (.step 3 (.step 18 (.step 22 (.step 38 (.step 66 (.step 38 (.close 67)))))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 17 (.close 20))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨2923003274661805836407369665432566039315086311424, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212914443952366802283816415870769044353531772928⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.step 21 (.step 77 (.split 17 1 (.split 22 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.split 72 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 18 (.step 15 (.close 21))))) (.step 11 (.step 18 (.step 15 (.step 21 (.close 38))))))) (.step 3 (.step 11 (.step 18 (.step 21 (.step 38 (.close 67))))))) (.step 3 (.step 11 (.step 18 (.step 21 (.close 66))))))) (.step 7 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 11 (.step 18 (.step 12 (.step 21 (.close 42))))))) (.step 7 (.step 18 (.step 21 (.step 42 (.close 53)))))) (.step 7 (.step 12 (.step 18 (.step 21 (.step 42 (.close 52))))))) (.step 3 (.step 11 (.step 18 (.step 21 (.close 42)))))) (.step 3 (.step 18 (.step 21 (.step 38 (.step 66 (.close 67))))))) (.step 7 (.step 18 (.step 7 (.step 11 (.step 17 (.close 19))))))) (.step 7 (.step 18 (.step 7 (.close 19))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨2787593149816327892691964784081048409473024, 11567177732598406499846312727330591355628391054642504500451083402266067648995432143040325426469346118120386344866462939060493125699583562731703506093833150552698468721372016583063528180612848889901089900910319637854110613504⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 42 1 (.step 34 (.split 51 1 (.step 77 (.split 63 1 (.split 64 1 (.split 67 1 (.step 11 (.split 10 0 (.split 14 2 (.split 16 0 (.split 17 0 (.split 22 0 (.split 30 0 (.step 23 (.split 34 0 (.split 35 0 (.step 34 (.step 17 (.step 23 (.step 17 (.close 3))))) (.step 23 (.step 17 (.step 12 (.close 31))))) (.step 17 (.step 3 (.step 12 (.step 17 (.close 31))))))) (.step 18 (.step 12 (.step 17 (.close 21))))) (.step 17 (.step 18 (.step 12 (.close 17))))) (.step 17 (.step 18 (.step 12 (.close 17))))) (.step 17 (.step 18 (.step 12 (.close 17))))) (.step 17 (.split 71 1 (.step 23 (.step 17 (.split 36 0 (.step 3 (.close 12)) (.step 3 (.step 12 (.close 17)))))) (.step 17 (.step 23 (.close 31)))))) (.step 17 (.step 3 (.close 12))))) (.step 3 (.step 12 (.close 17)))) (.step 11 (.step 67 (.step 3 (.close 17))))) (.step 11 (.step 12 (.step 34 (.close 66)))))) (.step 3 (.close 17)))) (.step 3 (.step 17 (.step 23 (.step 31 (.step 12 (.step 17 (.step 12 (.close 66))))))))) (.step 3 (.step 23 (.step 31 (.step 17 (.step 12 (.close 66))))))) (.step 3 (.step 17 (.step 31 (.step 12 (.close 17)))))) (.step 3 (.close 17))) (.step 3 (.step 23 (.step 31 (.step 23 (.step 66 (.step 67 (.step 69 (.step 23 (.step 40 (.step 17 (.step 74 (.close 17))))))))))))) (.step 3 (.step 17 (.step 18 (.step 17 (.step 12 (.close 34))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part29

namespace Part30
def root : Box := ⟨2787593149816327892691964784081048409473024, 11567177732598406499846312727330591355628391062754941668768919317712621614100853688846529714586448052477411715426355931522435136853812170244561946819368715920774279671999156339950967288111745319198102246043926847578919927808⟩
def references : Fin 1 → Box := ![Part29.root]
def proof : Chunks.Proof 1 := (.split 39 1 (.split 40 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.reuse 0) (.run (.step 3 (.step 12 (.step 23 (.step 27 (.step 34 (.step 23 (.step 17 (.step 44 (.step 17 (.step 3 (.close 32))))))))))))) (.run (.step 11 (.step 12 (.step 17 (.step 18 (.step 34 (.step 36 (.step 40 (.step 44 (.step 61 (.close 17)))))))))))) (.run (.step 3 (.step 12 (.step 23 (.step 9 (.step 31 (.step 34 (.close 57))))))))) (.run (.step 3 (.step 12 (.step 23 (.step 27 (.step 32 (.step 34 (.step 53 (.step 23 (.step 57 (.step 61 (.split 54 1 (.step 77 (.step 55 (.split 71 1 (.split 10 0 (.split 12 0 (.step 23 (.step 17 (.step 44 (.step 17 (.step 3 (.step 17 (.step 32 (.close 53)))))))) (.step 12 (.step 17 (.step 21 (.step 17 (.close 3)))))) (.step 3 (.step 12 (.close 17)))) (.step 12 (.step 17 (.step 3 (.step 23 (.step 3 (.close 32))))))))) (.step 12 (.step 21 (.step 23 (.close 3))))))))))))))))) (.run (.step 3 (.step 12 (.step 18 (.step 23 (.step 31 (.close 17)))))))) (.run (.step 11 (.step 12 (.step 17 (.step 18 (.step 23 (.step 34 (.step 36 (.step 40 (.step 42 (.close 17))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part29.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part30

namespace Part31
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231545516618611709107835553125398720020480⟩
def references : Fin 1 → Box := ![Part30.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 18 (.step 31 (.step 27 (.step 17 (.step 34 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 35 1 (.reuse 0) (.run (.step 3 (.step 21 (.step 23 (.step 31 (.step 32 (.step 38 (.step 57 (.step 61 (.step 66 (.step 67 (.step 74 (.split 54 1 (.split 58 1 (.split 72 1 (.step 23 (.split 74 1 (.step 40 (.split 10 0 (.split 12 0 (.step 23 (.split 30 0 (.split 34 0 (.split 35 2 (.step 17 (.step 3 (.step 12 (.close 31)))) (.step 40 (.step 38 (.close 17)))) (.step 3 (.step 17 (.close 31)))) (.step 3 (.close 17)))) (.step 12 (.close 23))) (.step 3 (.step 12 (.close 17))))) (.step 17 (.close 23)))) (.step 29 (.step 38 (.close 17)))) (.step 11 (.step 12 (.step 17 (.step 23 (.step 31 (.close 32))))))) (.step 9 (.step 12 (.step 21 (.step 23 (.step 26 (.close 31)))))))))))))))))))) (.run (.step 3 (.step 11 (.step 17 (.step 3 (.close 18))))))) (.run (.step 3 (.step 11 (.step 17 (.step 18 (.close 3))))))) (.run (.step 3 (.step 11 (.step 17 (.step 18 (.step 3 (.close 19)))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part30.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part31

namespace Part32
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231545516618611709107835553125398720020480⟩
def references : Fin 5 → Box := ![Part25.root, Part26.root, Part27.root, Part28.root, Part31.root]
def proof : Chunks.Proof 5 := (.split 14 1 (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 26 (.step 77 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.split 72 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 18 (.step 15 (.close 21))))) (.step 11 (.step 18 (.step 15 (.step 23 (.close 74))))))) (.step 3 (.step 11 (.step 18 (.step 23 (.close 67)))))) (.step 3 (.step 11 (.step 18 (.step 23 (.close 66))))))) (.step 7 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 11 (.step 18 (.step 12 (.step 23 (.close 61))))))) (.step 7 (.step 18 (.step 23 (.step 26 (.close 53)))))) (.step 7 (.step 12 (.step 18 (.step 26 (.close 52)))))) (.step 3 (.step 11 (.step 18 (.step 23 (.close 42)))))) (.step 3 (.step 18 (.step 26 (.step 38 (.step 66 (.step 38 (.close 67)))))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3)) (.reuse 4))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part25.excludes
  · exact Part26.excludes
  · exact Part27.excludes
  · exact Part28.excludes
  · exact Part31.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part32

namespace Part33
def root : Box := ⟨2658455991569831745807614123781914624, 11567166695907501132686180789110957572715254435221959547786404459204063394456315490414378155841704863170166458768530753167219748166492122705564655950730461052892486959154304359570269580158430419899091499546236195675234631680⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 22 1 (.split 30 1 (.split 42 1 (.split 51 1 (.split 67 1 (.split 74 1 (.split 10 0 (.split 12 2 (.split 21 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 14 0 (.split 16 0 (.split 36 0 (.split 17 0 (.step 9 (.step 15 (.step 12 (.step 23 (.close 3))))) (.step 3 (.step 12 (.step 15 (.close 18))))) (.step 9 (.step 22 (.step 15 (.close 3))))) (.step 3 (.step 18 (.step 12 (.step 15 (.close 3)))))) (.step 55 (.split 36 0 (.split 39 0 (.step 15 (.step 3 (.close 12))) (.step 12 (.close 3))) (.step 3 (.close 12))))) (.step 9 (.step 21 (.step 15 (.step 3 (.close 22)))))) (.step 9 (.step 31 (.step 3 (.step 12 (.close 15)))))) (.step 3 (.step 15 (.step 3 (.step 12 (.close 15)))))) (.step 3 (.step 18 (.close 15)))) (.step 9 (.split 21 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 39 0 (.step 15 (.step 3 (.step 12 (.close 18)))) (.step 12 (.step 21 (.close 15)))) (.step 15 (.close 3))) (.step 15 (.close 18))) (.step 15 (.close 3))) (.step 15 (.close 18))))) (.step 9 (.split 14 0 (.split 21 0 (.split 34 0 (.split 36 0 (.split 39 0 (.step 31 (.step 12 (.close 3))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 12))))) (.step 23 (.step 9 (.step 12 (.close 15))))) (.step 3 (.close 15))) (.step 3 (.close 15))) (.step 3 (.step 9 (.step 26 (.step 15 (.step 3 (.step 15 (.step 21 (.close 23))))))))) (.step 3 (.close 15))) (.step 3 (.step 17 (.step 18 (.close 15))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part33

namespace Part34
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663031847198749922980806849356709675425878567534026453556198401648533784598544011909861631916788302587801968259458506730608428492033146892244810968898683148821742410157976552599672407267666671783361126596608⟩
def references : Fin 1 → Box := ![Part33.root]
def proof : Chunks.Proof 1 := (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 14 1 (.split 34 1 (.split 36 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 3 (.step 17 (.step 18 (.close 15)))))) (.run (.step 3 (.step 17 (.step 18 (.close 15)))))) (.run (.step 3 (.step 9 (.step 22 (.close 31)))))) (.run (.step 3 (.step 9 (.step 15 (.step 23 (.step 15 (.close 3)))))))) (.run (.step 3 (.step 12 (.step 3 (.step 15 (.step 3 (.close 17)))))))) (.run (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 3 (.step 18 (.step 26 (.step 23 (.step 22 (.step 23 (.step 21 (.step 23 (.close 3)))))))))))))))) (.run (.step 12 (.step 21 (.step 22 (.step 23 (.step 29 (.step 31 (.step 55 (.step 75 (.split 16 0 (.split 21 0 (.split 22 0 (.step 15 (.step 57 (.step 55 (.step 3 (.step 15 (.close 21)))))) (.step 23 (.step 15 (.close 21)))) (.step 23 (.close 15))) (.step 21 (.step 15 (.step 3 (.close 15))))))))))))))) (.run (.step 3 (.step 15 (.close 24))))) (.run (.step 12 (.step 21 (.step 22 (.step 23 (.step 29 (.step 31 (.step 32 (.step 51 (.step 55 (.step 67 (.step 68 (.step 74 (.step 75 (.split 65 1 (.split 17 0 (.split 21 0 (.split 22 0 (.step 15 (.step 40 (.close 3))) (.step 23 (.close 15))) (.step 23 (.close 15))) (.step 22 (.step 15 (.step 3 (.close 15))))) (.step 3 (.close 15))))))))))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part33.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part34

namespace Part35
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663031847198749931891823680658172149002734695832854501453397144755214650451236369877367079602933596090127708564053577265852793529799735496714596078303230917020407563259903415196255770157681918783624115650560⟩
def references : Fin 1 → Box := ![Part34.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.reuse 0) (.run (.step 12 (.step 15 (.step 21 (.step 22 (.step 23 (.step 29 (.step 31 (.step 66 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 15 (.close 21)) (.step 23 (.close 15))) (.step 15 (.step 18 (.close 21)))) (.step 22 (.step 15 (.step 3 (.close 18))))) (.step 21 (.step 23 (.close 15)))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 22 (.step 26 (.step 23 (.step 55 (.close 62))))))))))))) (.run (.step 3 (.step 12 (.step 21 (.step 22 (.step 23 (.step 34 (.step 40 (.step 62 (.split 16 0 (.step 9 (.step 57 (.split 22 0 (.step 15 (.step 61 (.step 15 (.step 3 (.close 15))))) (.step 3 (.step 15 (.step 18 (.close 21))))))) (.step 3 (.step 21 (.close 15)))))))))))))) (.run (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 22 (.step 15 (.step 23 (.step 15 (.step 23 (.step 21 (.step 22 (.close 57))))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 22 (.step 26 (.step 32 (.step 53 (.close 18))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 22 (.step 26 (.step 34 (.step 3 (.step 26 (.close 52)))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 23 (.step 24 (.step 31 (.step 3 (.close 15)))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part34.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part35

namespace Part36
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354668496902428544771346316750848217212917231548175077138580140037819542512687120384⟩
def references : Fin 2 → Box := ![Part32.root, Part35.root]
def proof : Chunks.Proof 2 := (.split 10 1 (.split 12 1 (.reuse 0) (.step 3 (.step 18 (.step 9 (.step 23 (.step 31 (.split 21 1 (.split 35 1 (.split 39 1 (.reuse 1) (.run (.step 3 (.step 12 (.step 15 (.step 21 (.step 22 (.step 23 (.step 32 (.step 34 (.step 36 (.step 40 (.step 42 (.step 43 (.step 57 (.step 61 (.step 62 (.split 40 1 (.split 17 0 (.step 9 (.split 36 0 (.split 51 0 (.split 21 0 (.split 22 0 (.step 15 (.close 22)) (.step 3 (.step 15 (.close 22)))) (.step 3 (.step 15 (.close 18)))) (.step 3 (.close 15))) (.step 3 (.step 15 (.step 22 (.close 23)))))) (.step 3 (.step 22 (.close 15)))) (.step 3 (.step 31 (.close 15))))))))))))))))))))) (.run (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 22 (.step 15 (.step 26 (.step 31 (.step 32 (.step 38 (.close 18)))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 18 (.step 24 (.step 18 (.step 15 (.close 24))))))))))))))))) (.run (.step 3 (.step 7 (.step 18 (.step 31 (.split 12 1 (.split 14 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.split 59 1 (.step 18 (.step 31 (.split 63 1 (.split 64 1 (.step 7 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 31))))) (.step 3 (.step 18 (.close 31)))) (.step 3 (.step 18 (.step 31 (.close 66))))))) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 3 (.close 12))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 18 (.close 52))))) (.step 3 (.step 12 (.step 17 (.close 18))))) (.step 3 (.close 31))) (.step 3 (.close 17))) (.step 3 (.step 12 (.close 15))))))))))
theorem accepted : Chunks.check 14 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 14 families (references i) := by
  intro i
  fin_cases i
  · exact Part32.excludes
  · exact Part35.excludes

theorem excludes : Chunks.Excludes 14 families root :=
  Chunks.check_sound 14 families families_valid references references_excluded proof root root_valid accepted
end Part36

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 14 families root := Part36.excludes
end FiveColour.Packed.ProjectedChunks.Case101
