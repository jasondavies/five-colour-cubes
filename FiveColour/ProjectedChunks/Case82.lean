module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case82
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439027885657660779310766230433955840⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨11592891989185001204471, 5789234131009374248507341982684158351525473076195097263463908735304727765271163198607014520417109729396981796214162666810521916439567451338240667233911583614265164498419429981634596862352413225127988347882672294734774404096, 0⟩]
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
def root : Box := ⟨3221225472, 5783586108473071698929506996965222366134733773348527137630275073014641211963365061407257151770905019981373183719519790822093350474905949501118224684974237311982908882719376211410831396169146341360900744439054572619747557376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 14 0 (.split 21 0 (.split 16 0 (.split 17 0 (.split 22 0 (.split 34 0 (.step 55 (.step 40 (.split 26 0 (.step 55 (.close 3)) (.step 27 (.step 3 (.close 12)))))) (.step 29 (.step 3 (.step 23 (.step 26 (.close 31)))))) (.step 3 (.step 23 (.close 3)))) (.step 3 (.step 18 (.step 23 (.close 3))))) (.step 3 (.step 18 (.step 23 (.close 3))))) (.step 3 (.step 18 (.step 23 (.step 15 (.close 21)))))) (.split 16 0 (.step 23 (.split 17 0 (.split 22 0 (.split 34 0 (.split 36 0 (.step 27 (.step 23 (.step 40 (.close 3)))) (.step 3 (.step 12 (.step 23 (.close 27))))) (.step 3 (.step 23 (.step 12 (.close 17))))) (.step 3 (.step 12 (.step 17 (.close 21))))) (.step 3 (.step 12 (.step 17 (.step 18 (.close 21))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.close 21))))))) (.split 14 0 (.split 16 0 (.step 9 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 34 0 (.step 40 (.step 15 (.step 3 (.close 12)))) (.step 15 (.step 3 (.step 12 (.step 15 (.step 21 (.close 22))))))) (.step 3 (.step 29 (.step 31 (.step 12 (.step 15 (.close 21))))))) (.step 3 (.step 23 (.step 3 (.close 15))))) (.step 3 (.step 15 (.step 18 (.step 12 (.step 23 (.close 21))))))) (.step 3 (.step 18 (.step 22 (.step 3 (.step 12 (.close 15)))))))) (.step 3 (.step 18 (.step 21 (.close 3))))) (.step 23 (.step 40 (.step 55 (.split 16 0 (.step 15 (.step 9 (.step 23 (.close 3)))) (.step 3 (.close 12)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 17350758314646456770407654272091792956249470612518806848958195176367027573520608965453356989487370975191346508370278143477948007731672221160061225301639770466056677918729813795636178351943293166808217868945595289321059909632⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 72 1 (.split 74 1 (.split 8 0 (.split 10 0 (.reuse 0) (.run (.step 3 (.step 18 (.step 31 (.split 12 0 (.split 14 0 (.split 16 0 (.step 18 (.step 12 (.close 21))) (.step 3 (.close 7))) (.step 3 (.close 12))) (.step 3 (.step 12 (.close 3))))))))) (.run (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.step 9 (.step 23 (.split 22 0 (.split 34 0 (.split 36 0 (.step 27 (.step 55 (.close 3))) (.step 3 (.step 9 (.close 11)))) (.step 3 (.step 9 (.close 11)))) (.step 3 (.close 9))))) (.step 3 (.step 9 (.close 11)))) (.step 11 (.step 3 (.close 9)))) (.step 11 (.step 9 (.split 34 0 (.step 11 (.close 3)) (.step 3 (.close 9)))))) (.step 23 (.step 40 (.step 55 (.split 10 0 (.split 14 0 (.step 9 (.step 3 (.close 11))) (.step 11 (.close 9))) (.step 3 (.close 9))))))))) (.run (.step 11 (.split 26 0 (.split 34 0 (.split 35 0 (.step 77 (.split 36 0 (.step 77 (.step 3 (.close 12))) (.step 3 (.step 18 (.step 22 (.close 23)))))) (.step 23 (.step 69 (.step 3 (.step 18 (.step 12 (.close 31))))))) (.step 3 (.step 17 (.step 18 (.step 23 (.close 31)))))) (.step 23 (.step 27 (.step 3 (.step 18 (.step 17 (.close 29)))))))))) (.run (.step 69 (.step 29 (.split 8 0 (.split 14 0 (.split 16 0 (.step 75 (.split 17 0 (.step 75 (.step 3 (.close 12))) (.step 3 (.step 18 (.step 23 (.close 3)))))) (.step 3 (.step 18 (.step 31 (.step 21 (.close 12)))))) (.step 40 (.step 69 (.step 3 (.step 18 (.close 12)))))) (.step 9 (.step 40 (.step 3 (.step 11 (.step 3 (.close 31)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579558101483520, 5783586119245830025300575939794769646273237280395623053812135137267120501448128513407678675459694086277874331832380911039546340351169746749494654996660001962277960863427674289881884539469098809344048532354090726281208397824⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 12 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.step 3 (.close 27))) (.step 29 (.step 3 (.step 23 (.step 12 (.step 23 (.close 31))))))) (.step 29 (.step 74 (.close 3)))) (.step 29 (.step 31 (.step 22 (.step 15 (.step 17 (.close 21))))))) (.step 3 (.step 31 (.step 23 (.step 12 (.step 21 (.close 27))))))) (.step 3 (.step 18 (.step 22 (.step 29 (.step 31 (.step 21 (.close 12)))))))) (.step 18 (.step 22 (.step 31 (.step 22 (.step 12 (.step 21 (.close 27)))))))) (.step 18 (.step 31 (.step 21 (.step 12 (.step 21 (.close 27))))))) (.step 47 (.step 74 (.close 3)))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 9 (.step 22 (.step 29 (.step 57 (.step 55 (.step 3 (.close 15))))))) (.step 23 (.step 31 (.step 22 (.step 9 (.step 15 (.close 21))))))) (.step 12 (.step 22 (.step 9 (.step 23 (.step 15 (.step 24 (.close 21)))))))) (.step 22 (.step 3 (.close 11)))) (.step 23 (.step 31 (.step 23 (.step 11 (.close 18))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748387714433024, 17350758325419215096788520990895658187387370018583107836034696920215869034787387106242355815602307234756865122437878291315379872333603000876590146249244833944341463238612653134409396727222981379235104450159786752973972963328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 67 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 12 0 (.step 67 (.step 40 (.step 23 (.step 67 (.split 8 0 (.step 3 (.step 18 (.step 17 (.close 21)))) (.step 9 (.step 3 (.step 9 (.close 3))))))))) (.split 16 0 (.split 17 0 (.step 32 (.step 21 (.step 9 (.step 29 (.step 66 (.step 3 (.step 18 (.step 23 (.close 24))))))))) (.step 23 (.step 31 (.step 23 (.close 11))))) (.step 21 (.step 3 (.step 11 (.close 18)))))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 39 0 (.step 40 (.split 8 0 (.step 67 (.close 3)) (.step 9 (.step 11 (.step 3 (.step 29 (.close 31))))))) (.step 11 (.step 12 (.step 21 (.step 32 (.step 27 (.step 17 (.step 3 (.step 21 (.close 31)))))))))) (.step 11 (.step 3 (.step 12 (.step 23 (.step 17 (.step 21 (.close 27)))))))) (.step 11 (.step 3 (.step 18 (.step 12 (.step 17 (.step 23 (.close 27)))))))) (.step 11 (.step 12 (.step 3 (.step 18 (.step 17 (.step 21 (.step 22 (.close 23))))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 23 (.close 27))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 21 (.close 27)))))))) (.split 8 0 (.step 31 (.step 66 (.step 18 (.step 12 (.step 21 (.close 22)))))) (.step 11 (.step 3 (.close 9))))) (.step 67 (.close 3))) (.step 11 (.step 67 (.step 23 (.close 3))))) (.step 29 (.step 67 (.step 55 (.step 21 (.close 3)))))) (.step 67 (.step 3 (.close 15))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 17350758325419215096788520990895658187387370018583107836034696920215869034787387106242355815602307234756865122437878291315379872333603000876590146249244833944341463238612653134409396727222981379235104450159786752973972963328⟩
def references : Fin 3 → Box := ![Part1.root, Part2.root, Part3.root]
def proof : Chunks.Proof 3 := (.split 64 1 (.split 65 1 (.split 67 1 (.split 71 1 (.reuse 0) (.split 72 1 (.split 74 1 (.split 10 0 (.split 14 0 (.reuse 1) (.run (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 30 0 (.split 8 0 (.step 40 (.split 54 0 (.step 74 (.close 3)) (.step 12 (.step 9 (.step 22 (.step 23 (.step 3 (.close 21)))))))) (.step 11 (.step 9 (.step 29 (.close 31))))) (.step 11 (.step 3 (.step 12 (.step 23 (.step 17 (.step 21 (.close 27)))))))) (.step 11 (.step 3 (.step 18 (.step 12 (.step 17 (.step 23 (.close 27)))))))) (.step 11 (.step 12 (.step 3 (.step 18 (.step 17 (.step 22 (.step 21 (.close 23))))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 22 (.close 27))))))) (.step 11 (.step 18 (.step 12 (.step 17 (.step 21 (.close 27))))))))) (.run (.split 8 0 (.step 31 (.step 66 (.step 18 (.step 12 (.step 21 (.close 22)))))) (.step 11 (.step 3 (.close 9)))))) (.run (.step 11 (.step 69 (.step 74 (.step 18 (.close 12))))))) (.run (.step 29 (.step 69 (.step 74 (.step 23 (.close 3)))))))) (.run (.step 3 (.step 69 (.split 72 1 (.step 3 (.split 74 1 (.step 3 (.close 7)) (.step 3 (.step 11 (.close 12))))) (.step 3 (.step 15 (.close 21)))))))) (.run (.step 3 (.step 74 (.split 72 1 (.split 74 1 (.split 8 0 (.step 31 (.step 68 (.step 3 (.close 12)))) (.step 3 (.close 11))) (.step 3 (.step 11 (.step 18 (.close 12))))) (.step 3 (.step 26 (.step 29 (.step 31 (.close 15)))))))))) (.reuse 2))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes
  · exact Part2.excludes
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201311933144244572989303597362966874315326085970228087693756778676076885898810676339476574618193537351032175821612633217872175014993471638536809672567808912202810052267383587629694976⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 63 1 (.reuse 0) (.run (.step 66 (.step 3 (.step 69 (.split 65 1 (.split 72 1 (.split 74 1 (.split 64 1 (.split 71 1 (.split 10 0 (.split 14 0 (.split 12 0 (.split 8 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 34 0 (.split 35 0 (.split 36 0 (.step 55 (.step 3 (.close 27))) (.step 29 (.step 3 (.step 12 (.step 23 (.close 31)))))) (.step 29 (.step 66 (.step 3 (.close 21))))) (.step 15 (.step 29 (.step 31 (.step 12 (.close 15)))))) (.step 3 (.step 31 (.step 12 (.step 23 (.close 27)))))) (.step 3 (.step 12 (.step 18 (.step 31 (.close 23)))))) (.step 18 (.step 31 (.step 12 (.step 23 (.close 27)))))) (.step 18 (.step 31 (.step 12 (.step 21 (.close 27)))))) (.step 47 (.step 66 (.step 3 (.close 9))))) (.step 66 (.close 3))) (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 12 (.close 66)) (.step 11 (.step 3 (.step 12 (.close 3))))) (.step 11 (.close 12))) (.step 11 (.step 18 (.close 12)))) (.step 11 (.step 18 (.close 12))))) (.split 8 0 (.step 31 (.step 12 (.close 3))) (.step 11 (.step 3 (.close 9))))) (.step 66 (.close 3))) (.step 66 (.close 3))) (.step 11 (.step 66 (.step 55 (.step 12 (.close 3)))))) (.step 29 (.step 66 (.step 40 (.close 3))))) (.step 66 (.step 3 (.close 18)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

namespace Part6
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320037666840043678675691909575646114449157154275436203327082694298937955082967175700011546023512163130394958109920914726046880522915802160457889120219291038136343638093356202983424⟩
def references : Fin 1 → Box := ![Part5.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.reuse 0) (.run (.step 3 (.step 26 (.step 44 (.split 63 1 (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.step 44 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.step 62 (.step 3 (.close 23))) (.step 9 (.step 26 (.step 27 (.step 29 (.close 3)))))) (.step 3 (.step 18 (.close 23)))) (.step 9 (.step 26 (.split 10 0 (.split 21 0 (.split 26 0 (.step 62 (.close 3)) (.step 15 (.step 27 (.close 29)))) (.step 3 (.step 12 (.step 15 (.step 21 (.close 22)))))) (.step 3 (.close 12)))))) (.step 3 (.step 18 (.step 3 (.step 23 (.close 12)))))) (.step 3 (.step 18 (.step 3 (.step 21 (.step 23 (.close 12))))))) (.step 27 (.step 23 (.step 44 (.step 52 (.step 23 (.step 55 (.step 3 (.close 12))))))))) (.step 9 (.step 11 (.step 3 (.close 11)))))) (.step 9 (.step 23 (.close 26)))) (.step 26 (.step 44 (.step 55 (.close 74))))) (.step 3 (.close 7))) (.step 3 (.step 26 (.step 44 (.step 55 (.step 32 (.close 67))))))) (.step 3 (.step 26 (.step 44 (.step 66 (.step 55 (.step 12 (.close 66)))))))))))))
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
def root : Box := ⟨7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416711979597824, 5783591634898093127287874668522977077187032888516646711771627379626452798319644647704623007290934808963712183412247173578886176747684062752186752019438628398977091444935534148159624965406651783050483645401636317107956219904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 71 1 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 72 1 (.split 12 0 (.split 21 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 39 0 (.step 40 (.step 3 (.step 9 (.close 12)))) (.step 27 (.step 40 (.step 32 (.step 3 (.close 12)))))) (.step 3 (.step 23 (.close 12)))) (.step 27 (.close 15))) (.step 3 (.step 23 (.step 12 (.step 21 (.close 27)))))) (.step 3 (.step 18 (.step 22 (.close 23))))) (.step 22 (.step 9 (.step 27 (.step 34 (.step 57 (.step 23 (.close 3)))))))) (.step 40 (.close 3))) (.step 18 (.step 3 (.step 22 (.step 27 (.step 22 (.step 12 (.step 21 (.close 32))))))))) (.step 18 (.step 3 (.step 23 (.step 27 (.step 21 (.step 12 (.step 21 (.close 32))))))))) (.step 27 (.step 34 (.step 40 (.step 61 (.close 3)))))) (.step 3 (.step 18 (.step 12 (.step 21 (.step 23 (.close 27))))))) (.step 27 (.split 72 1 (.split 10 0 (.split 21 0 (.split 30 0 (.split 34 0 (.step 61 (.close 11)) (.step 11 (.step 3 (.close 9)))) (.step 11 (.step 3 (.close 9)))) (.step 11 (.close 3))) (.step 11 (.step 3 (.close 9)))) (.step 9 (.step 11 (.step 3 (.close 31))))))) (.step 11 (.step 36 (.step 40 (.split 34 0 (.split 40 0 (.split 10 0 (.step 74 (.step 3 (.close 12))) (.step 12 (.step 3 (.step 18 (.step 27 (.step 21 (.step 22 (.step 32 (.close 21))))))))) (.step 18 (.step 22 (.step 27 (.step 40 (.close 12)))))) (.step 17 (.step 18 (.step 22 (.step 34 (.step 27 (.step 31 (.close 32)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part7

namespace Part8
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 11567166706680259459052350848629847510416810091867653824363749489935988735142075538076520763228899311589662443439479497240459031272617765790826346186979033813619671132241290538246833550956419334433402964401654670751699042304⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 71 1 (.split 8 0 (.split 10 0 (.split 12 0 (.step 23 (.split 21 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 14 0 (.split 35 0 (.split 16 0 (.step 9 (.step 55 (.step 40 (.step 57 (.close 3))))) (.step 3 (.step 18 (.close 21)))) (.step 9 (.step 21 (.step 40 (.step 3 (.close 12)))))) (.step 23 (.step 9 (.step 15 (.step 23 (.step 36 (.step 23 (.close 3)))))))) (.step 9 (.step 31 (.step 3 (.step 15 (.step 17 (.close 21))))))) (.step 3 (.step 31 (.step 23 (.close 12))))) (.step 9 (.split 14 0 (.step 57 (.close 23)) (.step 15 (.step 23 (.close 29)))))) (.step 3 (.step 18 (.step 23 (.step 29 (.step 31 (.close 12)))))))) (.step 9 (.split 21 0 (.split 26 0 (.step 23 (.split 35 0 (.split 39 0 (.step 15 (.close 57)) (.step 12 (.step 21 (.step 15 (.step 3 (.step 18 (.step 22 (.close 23)))))))) (.step 15 (.step 21 (.step 40 (.step 3 (.close 12))))))) (.step 15 (.step 23 (.close 57)))) (.step 15 (.step 3 (.step 18 (.step 23 (.step 31 (.step 12 (.step 23 (.close 21))))))))))) (.step 9 (.step 23 (.step 31 (.step 15 (.step 3 (.step 12 (.step 21 (.close 22))))))))) (.step 9 (.close 11))) (.step 22 (.step 23 (.step 29 (.split 16 0 (.split 21 0 (.split 10 0 (.step 74 (.step 3 (.step 9 (.close 12)))) (.step 9 (.step 12 (.step 3 (.step 15 (.step 23 (.step 3 (.close 21)))))))) (.step 9 (.step 23 (.step 31 (.close 15))))) (.step 21 (.step 3 (.step 9 (.step 18 (.step 23 (.close 15))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part8

namespace Part9
def root : Box := ⟨7198262071269114212496861612297570974191515389283066612961208916178940129074380592510465097766225371439873457013633432197133225688790879502413624289384265389441024, 17350758325419215096788520990895667098404201320045581412890825219043916925432955656099890776178416297475333599799540755379500898701125222726715418299723001631918682379196780230332173629833770487133801131341258894327129571328⟩
def references : Fin 1 → Box := ![Part8.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 23 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 72 1 (.split 67 1 (.reuse 0) (.run (.step 3 (.step 15 (.step 29 (.step 15 (.close 21))))))) (.run (.step 9 (.step 26 (.step 29 (.step 57 (.close 23))))))) (.run (.step 3 (.step 29 (.step 31 (.close 57)))))) (.run (.step 21 (.step 23 (.step 29 (.step 32 (.step 51 (.step 55 (.step 67 (.step 9 (.step 57 (.step 3 (.step 26 (.step 3 (.step 17 (.step 3 (.close 24))))))))))))))))) (.run (.step 12 (.step 23 (.step 29 (.step 51 (.step 55 (.step 66 (.step 9 (.step 68 (.step 57 (.step 40 (.step 3 (.step 26 (.step 3 (.close 18)))))))))))))))) (.run (.step 3 (.step 9 (.step 26 (.step 44 (.step 55 (.step 57 (.step 23 (.close 3)))))))))) (.run (.step 3 (.step 22 (.step 23 (.step 40 (.step 57 (.split 16 0 (.split 21 0 (.split 22 0 (.step 9 (.step 57 (.close 3))) (.step 3 (.step 23 (.close 12)))) (.step 3 (.step 9 (.step 23 (.close 12))))) (.step 3 (.step 21 (.step 9 (.step 18 (.close 23)))))))))))))))
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
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923629336920627398440563190915400398397339482451051576189760481847083608730455073211402569067765830910625246261266872859197364075207104626232111151632613376⟩
def references : Fin 3 → Box := ![Part6.root, Part7.root, Part9.root]
def proof : Chunks.Proof 3 := (.split 51 1 (.split 54 1 (.split 58 1 (.reuse 0) (.step 3 (.step 40 (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 74 1 (.split 67 1 (.reuse 1) (.run (.step 3 (.step 11 (.step 12 (.close 42)))))) (.run (.step 11 (.step 27 (.step 44 (.step 61 (.close 40))))))) (.run (.step 3 (.step 11 (.step 18 (.close 61)))))) (.run (.step 11 (.step 32 (.step 40 (.step 51 (.step 55 (.step 67 (.step 27 (.step 68 (.step 61 (.step 23 (.step 3 (.step 44 (.step 3 (.close 17)))))))))))))))) (.run (.step 11 (.step 12 (.step 34 (.step 40 (.step 51 (.step 55 (.step 66 (.step 27 (.step 61 (.step 3 (.step 23 (.step 3 (.step 44 (.step 3 (.close 18))))))))))))))))) (.run (.step 3 (.step 26 (.step 27 (.step 44 (.step 55 (.step 61 (.step 40 (.close 3))))))))))))) (.reuse 2)) (.run (.step 3 (.step 51 (.step 3 (.step 57 (.step 61 (.step 62 (.split 67 1 (.split 72 1 (.split 74 1 (.split 54 1 (.split 58 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.step 22 (.close 11)))) (.step 3 (.step 22 (.step 11 (.close 12))))) (.step 3 (.close 7))) (.step 3 (.step 11 (.step 12 (.close 36))))) (.step 3 (.step 15 (.step 21 (.step 15 (.close 22)))))) (.step 3 (.step 11 (.step 36 (.step 12 (.close 42)))))) (.step 3 (.step 22 (.step 15 (.step 21 (.step 15 (.close 29))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part6.excludes
  · exact Part7.excludes
  · exact Part9.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part10

namespace Part11
def root : Box := ⟨6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106660276404224, 17350758325419215096788520981547217361879492019643565800113717953232920809261189189284834360498433081149812223377368005363796164217001159347244991540943482236133780534092157771418766520695387649016233819855259395087486943232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 53 (.split 54 1 (.split 58 1 (.split 64 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 34 0 (.step 53 (.step 3 (.close 21))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 15 (.step 23 (.step 22 (.step 17 (.close 26)))))))))) (.step 9 (.step 21 (.step 27 (.step 29 (.close 3)))))) (.step 3 (.step 18 (.step 21 (.close 23))))) (.step 9 (.step 21 (.split 10 0 (.split 21 0 (.split 22 0 (.split 26 0 (.step 53 (.close 3)) (.step 15 (.step 27 (.close 29)))) (.step 3 (.step 12 (.step 15 (.step 22 (.close 23)))))) (.step 3 (.step 12 (.step 15 (.step 18 (.step 22 (.close 23))))))) (.step 3 (.close 12)))))) (.step 3 (.step 18 (.step 3 (.step 23 (.close 12)))))) (.step 3 (.step 18 (.step 3 (.step 21 (.close 12)))))) (.step 27 (.step 23 (.step 52 (.step 55 (.step 3 (.step 12 (.step 17 (.close 18))))))))) (.step 9 (.step 11 (.step 3 (.close 11))))) (.step 32 (.close 3))) (.step 27 (.step 32 (.step 61 (.step 40 (.close 3)))))) (.step 9 (.step 21 (.step 32 (.step 53 (.step 57 (.step 23 (.close 3))))))))) (.step 27 (.step 23 (.step 32 (.step 44 (.step 23 (.step 11 (.step 55 (.step 3 (.close 53)))))))))) (.step 9 (.step 21 (.step 23 (.step 26 (.step 29 (.step 32 (.step 40 (.step 53 (.step 55 (.step 3 (.close 15)))))))))))) (.step 32 (.step 55 (.close 74)))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part11

namespace Part12
def root : Box := ⟨6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408310503505920, 17350758325419215096788520981551784258005529861537225175988564436248561000544904592272126041335705431626943630365415260808706409170955583344377993827970885392029655013461455007401700203485002613001764173057371939565316603904⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 64 1 (.split 67 1 (.split 71 1 (.split 72 1 (.split 74 1 (.step 52 (.split 54 1 (.split 58 1 (.split 63 1 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 26 0 (.split 34 0 (.split 35 0 (.step 52 (.close 3)) (.step 9 (.step 40 (.step 53 (.step 52 (.close 3)))))) (.step 3 (.step 9 (.step 18 (.step 31 (.step 12 (.close 17))))))) (.step 9 (.step 27 (.step 29 (.close 3))))) (.step 3 (.step 18 (.step 12 (.close 23))))) (.step 9 (.step 34 (.split 26 0 (.step 52 (.close 12)) (.step 12 (.step 3 (.step 15 (.close 21)))))))) (.step 3 (.step 18 (.step 3 (.step 12 (.step 22 (.close 21))))))) (.step 3 (.step 18 (.step 3 (.step 12 (.close 21)))))) (.step 27 (.step 23 (.step 34 (.step 52 (.close 3)))))) (.step 9 (.step 11 (.step 3 (.close 11))))) (.step 12 (.close 3))) (.step 12 (.step 27 (.step 34 (.step 61 (.step 40 (.close 3))))))) (.step 9 (.step 12 (.step 52 (.step 57 (.step 23 (.close 3)))))))) (.step 12 (.step 27 (.step 34 (.step 44 (.step 23 (.step 11 (.step 52 (.step 55 (.step 3 (.close 18))))))))))) (.step 9 (.step 12 (.step 23 (.step 26 (.step 40 (.step 55 (.step 57 (.split 58 1 (.step 40 (.step 29 (.step 52 (.step 55 (.step 3 (.close 15)))))) (.step 12 (.step 22 (.step 23 (.step 27 (.step 34 (.step 40 (.close 3)))))))))))))))) (.step 12 (.step 55 (.close 74)))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 52)))))) (.step 3 (.step 12 (.step 53 (.step 55 (.step 32 (.close 67))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part12

namespace Part13
def root : Box := ⟨5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991354449690624, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059938950007945587715116986772232620521696225285745752731329774467929646030213594909445136181450007851539719916761125146853376⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.step 44 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.split 63 1 (.step 7 (.split 64 1 (.split 71 1 (.split 74 1 (.step 31 (.step 3 (.close 7))) (.step 3 (.step 29 (.step 11 (.step 31 (.close 12)))))) (.step 29 (.step 31 (.step 11 (.step 12 (.close 40)))))) (.step 29 (.step 31 (.step 11 (.step 40 (.close 67))))))) (.step 3 (.step 29 (.step 31 (.step 40 (.close 66))))))) (.step 7 (.step 9 (.step 18 (.step 23 (.step 26 (.step 29 (.step 31 (.close 12))))))))) (.step 3 (.step 9 (.step 23 (.step 26 (.step 29 (.step 31 (.step 12 (.close 40))))))))) (.step 7 (.step 9 (.step 18 (.step 23 (.step 21 (.step 26 (.step 31 (.step 12 (.step 34 (.step 40 (.close 53)))))))))))) (.step 7 (.step 9 (.step 12 (.step 18 (.step 23 (.step 26 (.step 31 (.step 44 (.close 52)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part13

namespace Part14
def root : Box := ⟨5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343948716212224, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944114507701761532296298610576626545444884697331411178355435786642727325457628591834395472156568127202591723105070641840128⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 31 (.step 68 (.step 31 (.step 61 (.step 68 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.step 61 (.step 18 (.split 74 1 (.step 43 (.step 27 (.step 23 (.step 42 (.step 22 (.step 3 (.step 9 (.close 12)))))))) (.step 11 (.step 18 (.step 23 (.step 12 (.step 61 (.step 12 (.close 42))))))))))) (.step 11 (.step 18 (.step 23 (.step 31 (.step 18 (.step 61 (.close 67)))))))) (.step 11 (.step 12 (.step 18 (.step 31 (.close 66)))))) (.step 3 (.step 9 (.step 23 (.step 31 (.step 12 (.close 21))))))) (.step 3 (.step 9 (.step 23 (.step 31 (.step 3 (.step 12 (.close 57)))))))) (.step 3 (.step 9 (.step 21 (.step 23 (.step 31 (.close 53))))))) (.step 3 (.step 9 (.step 12 (.step 23 (.step 31 (.step 34 (.close 52)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part14

namespace Part15
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350752809766951994796323378847668532801382169635272054529990881059035887901065987304597976632061838953655609125159981385620375009654349553704539036086801219276796821552430589326923188127591202493875360645312938319544320000⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 65 1 (.split 71 1 (.split 74 1 (.split 51 1 (.split 58 1 (.split 67 1 (.split 72 1 (.step 44 (.split 8 0 (.split 10 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 12 0 (.split 21 0 (.split 22 0 (.split 26 0 (.step 42 (.step 3 (.close 12))) (.step 27 (.close 15))) (.step 3 (.step 23 (.step 12 (.step 21 (.close 27)))))) (.step 3 (.step 18 (.step 21 (.close 23))))) (.step 21 (.step 9 (.step 32 (.step 27 (.step 34 (.step 3 (.step 18 (.step 22 (.close 23)))))))))) (.step 18 (.step 3 (.step 23 (.step 12 (.step 21 (.close 27))))))) (.step 18 (.step 3 (.step 21 (.step 12 (.step 21 (.close 27))))))) (.step 27 (.step 34 (.step 42 (.close 3))))) (.step 3 (.step 18 (.step 12 (.step 21 (.close 22)))))) (.step 27 (.split 10 0 (.split 21 0 (.split 30 0 (.split 34 0 (.step 42 (.step 3 (.close 9))) (.step 11 (.step 3 (.close 9)))) (.step 11 (.step 3 (.close 9)))) (.step 11 (.close 3))) (.step 11 (.step 3 (.close 9))))))) (.step 31 (.step 40 (.step 27 (.step 23 (.close 11)))))) (.step 3 (.close 11))) (.step 27 (.step 42 (.step 15 (.step 22 (.close 31)))))) (.step 3 (.step 11 (.close 12)))) (.step 11 (.step 27 (.step 42 (.step 31 (.step 40 (.close 3))))))) (.step 11 (.step 32 (.step 36 (.step 40 (.step 55 (.step 61 (.step 67 (.step 27 (.step 61 (.step 74 (.step 42 (.step 3 (.step 23 (.step 3 (.step 40 (.close 3))))))))))))))))) (.step 3 (.step 11 (.step 18 (.close 42))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part15

namespace Part16
def root : Box := ⟨5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248385980497920, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158554670789637782293759363827451747538037797932609284024283068910015343477353733182648752471793746353453401112576⟩
def references : Fin 1 → Box := ![Part15.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 27 (.step 31 (.step 40 (.step 42 (.split 40 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 63 1 (.split 64 1 (.reuse 0) (.run (.step 11 (.step 32 (.step 40 (.step 42 (.step 67 (.split 34 0 (.split 36 0 (.split 40 0 (.split 42 0 (.step 27 (.close 42)) (.step 18 (.step 21 (.step 27 (.step 12 (.close 40)))))) (.step 18 (.step 21 (.step 27 (.step 40 (.close 12)))))) (.step 18 (.step 21 (.step 27 (.step 36 (.step 31 (.close 12))))))) (.step 17 (.step 18 (.step 21 (.step 34 (.step 27 (.close 31)))))))))))))) (.run (.step 11 (.step 12 (.step 32 (.step 34 (.step 40 (.step 51 (.step 55 (.step 66 (.step 67 (.step 68 (.step 74 (.step 77 (.split 65 1 (.split 36 0 (.step 27 (.step 42 (.step 3 (.step 18 (.close 23))))) (.step 18 (.step 23 (.step 27 (.step 31 (.step 36 (.step 31 (.close 40)))))))) (.step 3 (.step 18 (.close 42)))))))))))))))))) (.run (.step 3 (.step 26 (.step 27 (.step 42 (.step 31 (.step 44 (.step 32 (.step 40 (.step 3 (.step 12 (.step 3 (.step 36 (.close 55))))))))))))))) (.run (.step 3 (.step 21 (.step 23 (.step 32 (.step 36 (.step 40 (.step 27 (.step 61 (.step 9 (.step 57 (.step 42 (.step 3 (.step 23 (.close 3)))))))))))))))) (.run (.step 3 (.step 21 (.step 27 (.step 32 (.step 42 (.close 3)))))))) (.run (.step 3 (.step 12 (.step 27 (.step 34 (.step 42 (.step 44 (.close 52))))))))) (.run (.step 3 (.step 21 (.step 24 (.step 27 (.step 31 (.step 42 (.step 31 (.step 24 (.step 42 (.step 18 (.step 15 (.close 23)))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part15.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part16

namespace Part17
def root : Box := ⟨4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537409285095424, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559367874803329960215142788645326212092549297707100664024483491958407895403962399535679869790515890859464982528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.step 36 (.step 57 (.step 74 (.step 75 (.split 42 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.step 7 (.split 64 1 (.split 74 1 (.split 39 1 (.step 31 (.step 40 (.step 31 (.step 3 (.close 7))))) (.step 3 (.step 29 (.step 31 (.step 22 (.step 11 (.close 12))))))) (.step 3 (.step 31 (.step 11 (.step 12 (.close 36)))))) (.step 29 (.step 31 (.step 11 (.step 36 (.close 67))))))) (.step 3 (.step 29 (.step 31 (.step 36 (.step 11 (.close 66))))))) (.step 7 (.step 9 (.step 18 (.step 22 (.step 23 (.step 26 (.step 29 (.step 31 (.close 12)))))))))) (.step 7 (.step 9 (.step 18 (.step 21 (.step 22 (.step 23 (.step 21 (.step 29 (.step 31 (.close 53))))))))))) (.step 7 (.step 9 (.step 12 (.step 18 (.step 22 (.step 23 (.step 31 (.step 21 (.step 36 (.close 52))))))))))) (.step 7 (.step 31 (.step 7 (.step 26 (.close 29)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part17

namespace Part18
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 5783591629511713964107239080423427675680766827280245196312930316339578123199059639002513673707136927408768343299969205547765715852539669995497660350486255558188752639129562712134770200696269237584850814703311393431696179200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 21 (.split 39 1 (.step 75 (.split 51 1 (.step 29 (.split 54 1 (.split 67 1 (.split 8 0 (.split 10 0 (.split 12 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.split 39 0 (.split 40 0 (.split 49 0 (.split 51 0 (.step 38 (.step 21 (.step 32 (.step 31 (.close 38))))) (.step 21 (.step 3 (.step 15 (.step 22 (.close 3)))))) (.step 21 (.step 38 (.close 3)))) (.step 31 (.step 23 (.step 12 (.step 21 (.close 32)))))) (.step 32 (.close 38))) (.step 31 (.step 32 (.step 23 (.step 21 (.step 32 (.close 38))))))) (.step 21 (.step 3 (.step 18 (.step 31 (.close 23)))))) (.step 31 (.step 40 (.step 31 (.step 18 (.step 21 (.step 18 (.close 38)))))))) (.step 21 (.step 31 (.step 38 (.step 18 (.close 32)))))) (.step 40 (.step 38 (.step 12 (.step 66 (.step 38 (.step 3 (.close 18)))))))) (.step 21 (.step 38 (.step 15 (.step 23 (.close 3)))))) (.step 31 (.step 66 (.split 64 1 (.split 71 1 (.step 3 (.step 31 (.step 12 (.close 21)))) (.step 31 (.step 12 (.step 21 (.close 22))))) (.step 21 (.step 3 (.step 31 (.step 12 (.step 32 (.close 38)))))))))) (.step 9 (.step 40 (.step 66 (.step 38 (.step 67 (.step 38 (.step 3 (.close 11))))))))) (.step 3 (.step 15 (.close 21)))) (.step 9 (.step 21 (.step 38 (.step 3 (.step 57 (.step 3 (.step 18 (.step 12 (.step 15 (.close 17)))))))))))) (.step 3 (.step 21 (.step 15 (.close 22)))))) (.step 3 (.step 32 (.close 3))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part18

namespace Part19
def root : Box := ⟨4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220254594334720, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372461800561940358166010287116816266430890837079000586730967136086669249714576505296009827622111110838091776⟩
def references : Fin 1 → Box := ![Part18.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 9 (.step 21 (.step 31 (.step 32 (.step 38 (.step 57 (.step 66 (.step 67 (.step 74 (.split 36 1 (.split 42 1 (.split 49 1 (.split 58 1 (.split 59 1 (.split 65 1 (.split 74 1 (.reuse 0) (.run (.step 3 (.step 23 (.step 32 (.step 40 (.step 66 (.step 67 (.step 69 (.step 23 (.step 40 (.step 29 (.step 23 (.step 11 (.step 31 (.step 38 (.step 3 (.step 18 (.close 74))))))))))))))))))) (.run (.step 3 (.step 21 (.step 29 (.step 31 (.close 38))))))) (.run (.step 3 (.step 9 (.step 21 (.step 23 (.step 26 (.step 29 (.step 32 (.step 40 (.step 38 (.close 3)))))))))))) (.run (.step 3 (.step 21 (.step 32 (.step 40 (.step 27 (.close 61)))))))) (.run (.step 3 (.step 9 (.step 12 (.step 21 (.step 23 (.step 32 (.step 40 (.step 52 (.step 57 (.step 61 (.step 75 (.step 55 (.split 58 1 (.step 40 (.step 29 (.step 38 (.step 26 (.step 38 (.close 3)))))) (.step 12 (.step 22 (.step 27 (.step 32 (.step 34 (.step 3 (.step 26 (.step 3 (.step 38 (.close 40))))))))))))))))))))))))) (.run (.step 3 (.step 21 (.step 29 (.step 31 (.close 3))))))) (.run (.step 3 (.step 21 (.step 29 (.step 31 (.step 3 (.step 26 (.close 38)))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part18.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part19

namespace Part20
def root : Box := ⟨4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986546435457024, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424713774431402001377403319447080369995056030036936064871177298318865617900589377097654052323328⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 31 (.step 34 (.step 38 (.step 66 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 59 1 (.step 31 (.split 64 1 (.step 7 (.step 66 (.split 71 1 (.split 74 1 (.split 35 1 (.split 39 1 (.step 31 (.step 3 (.close 7))) (.step 3 (.step 29 (.step 31 (.close 11))))) (.step 29 (.step 31 (.close 3)))) (.step 3 (.step 31 (.step 11 (.step 12 (.step 17 (.close 34))))))) (.step 29 (.step 31 (.step 11 (.step 12 (.step 17 (.close 34))))))))) (.step 3 (.step 29 (.step 31 (.step 34 (.step 11 (.step 66 (.step 11 (.close 17)))))))))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 23 (.step 26 (.step 31 (.close 21))))))))) (.step 3 (.step 9 (.step 15 (.step 23 (.step 29 (.step 31 (.step 21 (.close 34))))))))) (.step 7 (.step 9 (.step 15 (.step 18 (.step 21 (.step 23 (.step 21 (.step 31 (.step 34 (.close 52))))))))))) (.step 7 (.step 9 (.step 15 (.step 17 (.step 18 (.step 31 (.step 34 (.close 52))))))))) (.step 7 (.step 31 (.step 7 (.step 26 (.step 29 (.step 3 (.close 37)))))))) (.step 7 (.step 31 (.close 37)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part20

namespace Part21
def root : Box := ⟨3705346855594118253554271520278013051304639509300498049262642688253223369703424, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711932575442305649653251736448048318079900262375925831592024286567596032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 9 (.step 27 (.step 29 (.step 31 (.step 57 (.step 66 (.step 67 (.step 74 (.split 49 1 (.split 50 1 (.split 59 1 (.split 65 1 (.split 74 1 (.split 30 1 (.split 39 1 (.split 51 1 (.split 54 1 (.split 58 1 (.step 29 (.split 63 1 (.step 3 (.split 8 0 (.split 14 0 (.split 16 0 (.split 17 0 (.split 21 0 (.step 29 (.step 27 (.close 3))) (.step 3 (.step 18 (.close 23)))) (.step 3 (.step 18 (.step 22 (.step 12 (.close 15)))))) (.step 3 (.step 18 (.step 21 (.close 12))))) (.step 23 (.step 27 (.step 17 (.step 3 (.step 12 (.close 18))))))) (.step 9 (.close 11)))) (.step 29 (.step 11 (.step 18 (.step 23 (.step 27 (.close 18)))))))) (.step 3 (.step 27 (.close 29)))) (.step 9 (.step 29 (.step 3 (.close 12))))) (.step 3 (.step 22 (.step 15 (.step 21 (.step 15 (.close 29))))))) (.step 3 (.step 27 (.close 29)))) (.step 3 (.close 29))) (.step 3 (.step 23 (.step 27 (.step 29 (.step 11 (.step 18 (.step 29 (.step 66 (.step 18 (.close 67))))))))))) (.step 3 (.close 29))) (.step 3 (.step 9 (.step 23 (.step 26 (.step 27 (.close 29))))))) (.step 3 (.step 9 (.step 21 (.step 23 (.step 27 (.step 29 (.step 26 (.step 29 (.step 3 (.step 29 (.close 53)))))))))))) (.step 3 (.step 9 (.step 12 (.step 23 (.step 27 (.step 29 (.step 52 (.step 55 (.step 57 (.step 29 (.step 21 (.step 26 (.step 29 (.step 3 (.close 52))))))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part21

namespace Part22
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711932575442305649653251736448048318079900262375925831592024286567596032⟩
def references : Fin 10 → Box := ![Part10.root, Part11.root, Part12.root, Part13.root, Part14.root, Part16.root, Part17.root, Part19.root, Part20.root, Part21.root]
def proof : Chunks.Proof 10 := (.split 26 1 (.split 30 1 (.split 34 1 (.split 35 1 (.split 36 1 (.split 39 1 (.split 40 1 (.split 42 1 (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.step 3 (.step 32 (.step 53 (.step 57 (.step 61 (.split 51 1 (.split 63 1 (.reuse 1) (.run (.step 3 (.step 32 (.step 55 (.step 12 (.close 66))))))) (.run (.step 3 (.step 7 (.step 53 (.close 7)))))))))))) (.step 3 (.step 12 (.step 52 (.step 57 (.step 61 (.split 51 1 (.reuse 2) (.run (.step 3 (.step 52 (.close 7))))))))))) (.run (.step 3 (.step 9 (.step 27 (.step 47 (.step 3 (.step 52 (.step 53 (.step 62 (.split 51 1 (.split 67 1 (.split 49 1 (.split 50 1 (.split 59 1 (.split 63 1 (.split 64 1 (.step 3 (.close 7)) (.step 3 (.step 9 (.step 3 (.close 11))))) (.step 3 (.step 11 (.close 9)))) (.step 3 (.close 7))) (.step 3 (.close 7))) (.step 3 (.step 7 (.step 9 (.step 27 (.close 46)))))) (.step 3 (.close 46))) (.step 3 (.close 46))))))))))))) (.reuse 3)) (.reuse 4)) (.reuse 5)) (.reuse 6)) (.reuse 7)) (.reuse 8)) (.run (.step 3 (.step 7 (.step 18 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 18 (.step 31 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.step 29 (.close 31))))))) (.step 3 (.step 18 (.close 31)))))) (.step 3 (.step 11 (.close 18)))) (.step 3 (.step 29 (.close 31)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 11 (.close 18)))) (.step 3 (.step 29 (.close 31))))))))) (.reuse 9))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part10.excludes
  · exact Part11.excludes
  · exact Part12.excludes
  · exact Part13.excludes
  · exact Part14.excludes
  · exact Part16.excludes
  · exact Part17.excludes
  · exact Part19.excludes
  · exact Part20.excludes
  · exact Part21.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part22

namespace Part23
def root : Box := ⟨3291009114642412084309938365114701009965471731267159729918443520, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158125638154134872560648435476984450380430744151216095232⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 3 (.step 18 (.step 31 (.step 43 (.step 68 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 18 (.step 68 (.split 58 1 (.split 59 1 (.split 63 1 (.step 43 (.split 64 1 (.step 3 (.step 31 (.split 72 1 (.step 24 (.step 9 (.step 40 (.step 15 (.step 18 (.step 3 (.close 21))))))) (.step 9 (.step 18 (.step 24 (.step 29 (.step 24 (.step 31 (.step 57 (.step 15 (.close 21)))))))))))) (.step 9 (.step 18 (.step 21 (.step 31 (.close 67))))))) (.step 9 (.step 12 (.step 18 (.close 66))))) (.step 3 (.step 18 (.close 12)))) (.step 3 (.step 18 (.step 3 (.step 12 (.step 57 (.step 12 (.close 21)))))))))) (.step 3 (.step 9 (.step 24 (.step 18 (.step 57 (.step 3 (.step 18 (.close 24))))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.close 53)))))) (.step 3 (.step 9 (.step 12 (.step 18 (.step 34 (.close 52))))))) (.step 3 (.step 18 (.step 3 (.step 21 (.step 24 (.step 3 (.close 42)))))))) (.step 3 (.step 9 (.step 18 (.step 21 (.step 24 (.step 29 (.step 31 (.close 38))))))))) (.step 3 (.step 9 (.step 18 (.close 29)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part23

namespace Part24
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158125638154134872560648435476984450380430744151216095232⟩
def references : Fin 2 → Box := ![Part22.root, Part23.root]
def proof : Chunks.Proof 2 := (.split 21 1 (.split 22 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 26 (.step 77 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.split 72 1 (.step 23 (.step 18 (.step 3 (.close 7)))) (.step 3 (.step 11 (.step 18 (.step 15 (.step 21 (.step 15 (.close 23)))))))) (.step 11 (.step 18 (.step 23 (.step 29 (.close 67)))))))) (.step 3 (.step 11 (.step 18 (.step 23 (.close 66))))))) (.step 7 (.step 18 (.close 12)))) (.step 3 (.step 11 (.step 18 (.step 12 (.step 17 (.close 23))))))) (.step 7 (.step 18 (.step 23 (.step 26 (.close 53)))))) (.step 7 (.step 12 (.step 18 (.step 26 (.close 52)))))) (.step 3 (.step 11 (.step 18 (.step 23 (.close 42)))))) (.step 3 (.step 18 (.step 26 (.step 29 (.step 38 (.step 66 (.step 38 (.close 67))))))))) (.step 3 (.step 18 (.step 26 (.step 29 (.close 66)))))))))))) (.reuse 1))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part22.excludes
  · exact Part23.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part24

namespace Part25
def root : Box := ⟨2923003274661805836407369665432566039315086311424, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232491400911630753030891518760621038812929196032⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.step 7 (.step 18 (.step 21 (.step 42 (.step 67 (.step 77 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 58 1 (.split 59 1 (.step 18 (.split 63 1 (.step 7 (.step 67 (.split 71 1 (.split 72 1 (.step 18 (.step 3 (.close 7))) (.step 3 (.step 11 (.step 18 (.step 15 (.close 21)))))) (.step 11 (.step 18 (.step 15 (.step 21 (.close 29)))))))) (.step 3 (.step 11 (.step 18 (.step 21 (.step 29 (.close 66)))))))) (.step 7 (.step 18 (.step 12 (.close 21))))) (.step 3 (.step 11 (.step 18 (.step 12 (.step 21 (.close 42))))))) (.step 7 (.step 18 (.step 21 (.step 42 (.close 53)))))) (.step 7 (.step 12 (.step 18 (.step 21 (.step 42 (.close 52))))))) (.step 3 (.step 18 (.step 21 (.step 29 (.step 38 (.close 66))))))) (.step 3 (.step 18 (.step 21 (.step 29 (.close 66)))))) (.step 7 (.step 18 (.step 7 (.close 11))))) (.step 7 (.step 18 (.step 7 (.close 19))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part25

namespace Part26
def root : Box := ⟨2787593149816327892691964784081048409473024, 11567166701293880295871715260530298108910544030643124168175750646890911274088920911823060994077246077498466920358446975114206442816679471268650370327457893303291513957730179257396209783147553903886101852069223303039867158528⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 39 1 (.split 42 1 (.step 34 (.step 77 (.split 51 1 (.step 11 (.split 58 1 (.split 67 1 (.split 10 0 (.split 14 2 (.split 16 0 (.split 17 0 (.split 22 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.split 42 0 (.split 49 0 (.split 50 0 (.step 55 (.step 12 (.close 3))) (.step 12 (.step 17 (.close 3)))) (.step 12 (.close 17))) (.step 18 (.step 12 (.close 17)))) (.step 12 (.step 17 (.step 3 (.step 12 (.step 3 (.close 17))))))) (.step 18 (.step 23 (.step 12 (.step 17 (.step 12 (.close 31))))))) (.step 23 (.step 17 (.step 12 (.step 31 (.close 66)))))) (.step 17 (.step 3 (.step 17 (.step 12 (.step 23 (.close 31))))))) (.step 18 (.step 12 (.step 17 (.step 12 (.close 21)))))) (.step 23 (.step 27 (.close 29)))) (.step 17 (.step 3 (.step 12 (.step 17 (.step 12 (.close 29))))))) (.step 17 (.step 18 (.step 12 (.step 17 (.step 12 (.close 29))))))) (.step 17 (.step 18 (.step 12 (.step 17 (.step 12 (.close 29))))))) (.step 17 (.step 23 (.step 66 (.step 67 (.step 23 (.step 17 (.step 3 (.close 29))))))))) (.step 17 (.step 3 (.step 12 (.close 29))))) (.step 3 (.step 12 (.close 17)))) (.step 12 (.step 17 (.step 27 (.step 34 (.step 3 (.step 61 (.step 3 (.step 12 (.step 3 (.close 17)))))))))))) (.step 3 (.step 11 (.step 12 (.close 17))))))) (.step 3 (.step 17 (.step 23 (.step 11 (.step 29 (.step 17 (.step 31 (.step 12 (.close 17)))))))))) (.step 11 (.step 12 (.step 17 (.step 27 (.step 34 (.step 42 (.step 3 (.close 17))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part26

namespace Part27
def root : Box := ⟨2787593149816327892691964784081048409473024, 11567177732598406499846312727330591355628391062750984382345349645167653573764539333805967613000828663038784184800473006674061041120520698636298534848895271186430399528927422912215209099592888717925185161003413256272410050560⟩
def references : Fin 1 → Box := ![Part26.root]
def proof : Chunks.Proof 1 := (.split 40 1 (.split 50 1 (.split 54 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 30 1 (.split 34 1 (.split 36 1 (.reuse 0) (.run (.step 3 (.step 23 (.step 31 (.step 11 (.close 17))))))) (.run (.step 3 (.step 17 (.step 29 (.step 23 (.step 31 (.step 11 (.step 12 (.close 17)))))))))) (.run (.step 3 (.step 11 (.close 17))))) (.run (.step 3 (.step 23 (.step 31 (.step 23 (.step 66 (.step 67 (.step 69 (.step 23 (.step 11 (.step 40 (.step 74 (.split 39 1 (.step 17 (.step 3 (.step 17 (.step 12 (.close 29))))) (.step 12 (.step 17 (.step 3 (.close 27)))))))))))))))))) (.run (.step 3 (.step 11 (.step 17 (.step 12 (.step 17 (.step 18 (.close 34))))))))) (.run (.step 3 (.step 12 (.step 23 (.step 27 (.step 17 (.step 23 (.step 34 (.step 11 (.step 23 (.step 42 (.step 44 (.step 17 (.close 3))))))))))))))) (.run (.step 3 (.step 12 (.step 23 (.step 9 (.step 31 (.step 34 (.close 57))))))))) (.run (.step 3 (.step 12 (.step 23 (.step 27 (.step 32 (.step 34 (.step 23 (.step 42 (.step 53 (.step 57 (.step 61 (.step 77 (.step 55 (.split 54 1 (.step 23 (.step 11 (.step 17 (.step 44 (.step 17 (.close 3)))))) (.step 9 (.step 12 (.step 21 (.close 23)))))))))))))))))))) (.run (.step 3 (.step 12 (.step 17 (.step 18 (.step 23 (.step 27 (.step 31 (.step 11 (.close 17)))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part26.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part27

namespace Part28
def root : Box := ⟨2787593149816327892691964784081048409473024, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188504780569358784210725405119858117443584⟩
def references : Fin 1 → Box := ![Part27.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 17 (.step 18 (.step 31 (.step 27 (.step 34 (.step 42 (.step 61 (.step 66 (.step 67 (.step 74 (.split 16 1 (.split 17 1 (.split 22 1 (.split 26 1 (.split 35 1 (.reuse 0) (.run (.step 3 (.step 21 (.step 23 (.step 31 (.step 32 (.step 38 (.step 57 (.step 66 (.step 67 (.step 74 (.split 54 1 (.split 58 1 (.split 72 1 (.step 23 (.split 74 1 (.step 40 (.split 8 0 (.step 40 (.step 29 (.step 23 (.step 17 (.step 3 (.close 31)))))) (.step 9 (.close 11)))) (.step 11 (.step 17 (.close 23))))) (.step 29 (.step 23 (.step 38 (.step 11 (.close 17)))))) (.step 11 (.step 12 (.step 17 (.step 23 (.step 27 (.step 3 (.close 31)))))))) (.step 9 (.step 12 (.step 21 (.step 23 (.step 26 (.close 29))))))))))))))))))) (.run (.step 3 (.step 23 (.step 27 (.step 29 (.step 23 (.step 47 (.step 29 (.close 17)))))))))) (.run (.step 3 (.step 11 (.step 17 (.step 3 (.close 18))))))) (.run (.step 3 (.step 11 (.step 17 (.step 3 (.close 18))))))) (.run (.step 3 (.step 11 (.step 17 (.step 18 (.step 3 (.close 19)))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part27.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part28

namespace Part29
def root : Box := ⟨2658455991569831745807614123781914624, 11567166695907501132686180789110957572715254435221959547786408058335099029013421738845184304627191958927861100301839582316500356211962353587015146506222019720367014267259689778210119025575181754237471356496246164961137524736⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 26 1 (.split 34 1 (.split 36 1 (.split 42 1 (.split 16 1 (.split 30 1 (.split 51 1 (.split 54 1 (.split 17 1 (.split 67 1 (.split 74 1 (.step 26 (.split 8 0 (.split 10 0 (.split 12 2 (.split 21 0 (.split 26 0 (.split 30 0 (.split 34 0 (.split 14 0 (.split 35 0 (.split 16 0 (.step 9 (.step 15 (.step 23 (.step 3 (.step 12 (.close 15)))))) (.step 3 (.step 12 (.step 15 (.close 18))))) (.step 9 (.step 21 (.step 15 (.close 3))))) (.step 15 (.step 3 (.close 12)))) (.step 9 (.step 15 (.close 3)))) (.step 3 (.step 15 (.close 3)))) (.step 9 (.split 14 0 (.split 16 0 (.step 15 (.step 3 (.step 18 (.step 21 (.close 22))))) (.step 3 (.step 18 (.step 15 (.close 3))))) (.step 12 (.step 3 (.close 15)))))) (.step 3 (.step 18 (.close 15)))) (.step 9 (.step 15 (.step 3 (.step 12 (.close 18)))))) (.step 9 (.step 31 (.step 12 (.close 3))))) (.step 9 (.close 11)))) (.step 18 (.step 23 (.step 9 (.step 12 (.close 15)))))) (.step 3 (.close 15))) (.step 3 (.step 11 (.step 17 (.step 18 (.close 15)))))) (.step 9 (.step 15 (.close 18)))) (.step 3 (.close 15))) (.step 3 (.close 15))) (.step 3 (.step 11 (.step 17 (.step 18 (.close 15)))))) (.step 3 (.step 9 (.step 15 (.step 23 (.step 26 (.step 3 (.step 15 (.step 21 (.close 22)))))))))) (.step 3 (.step 9 (.step 15 (.step 22 (.step 15 (.step 23 (.step 29 (.step 3 (.step 24 (.step 15 (.close 23)))))))))))) (.step 3 (.step 9 (.step 15 (.step 23 (.close 3)))))) (.step 9 (.step 15 (.step 3 (.step 18 (.close 29)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part29

namespace Part30
def root : Box := ⟨2658455991569831745807614123781914624, 11567177737984785663031847198749931891823680658164234429887552888633529731614235239879389207163395097945155734821685860058222176606514290434297735116755906928188205197951045697864323759895045135666142632231175683723763908608⟩
def references : Fin 1 → Box := ![Part29.root]
def proof : Chunks.Proof 1 := (.split 59 1 (.split 63 1 (.split 64 1 (.split 65 1 (.split 71 1 (.split 72 1 (.split 14 1 (.reuse 0) (.run (.step 3 (.step 12 (.step 3 (.step 11 (.step 3 (.step 15 (.step 3 (.close 17)))))))))) (.run (.step 9 (.step 12 (.step 15 (.step 21 (.step 22 (.step 26 (.step 29 (.step 3 (.step 23 (.close 3)))))))))))) (.run (.step 12 (.step 21 (.step 22 (.step 23 (.step 29 (.step 31 (.step 55 (.step 57 (.step 66 (.step 9 (.step 57 (.step 74 (.step 15 (.step 3 (.step 15 (.step 3 (.step 18 (.close 23)))))))))))))))))))) (.run (.step 3 (.close 15)))) (.run (.step 12 (.step 21 (.step 22 (.step 23 (.step 29 (.step 31 (.step 32 (.step 51 (.step 55 (.step 67 (.step 68 (.step 74 (.step 75 (.split 21 0 (.split 65 1 (.split 8 0 (.step 57 (.step 66 (.split 17 0 (.step 15 (.step 3 (.step 15 (.close 22)))) (.step 3 (.step 18 (.step 15 (.close 3))))))) (.step 9 (.close 11))) (.step 3 (.close 15))) (.step 9 (.step 15 (.step 23 (.close 15)))))))))))))))))))) (.run (.step 12 (.step 15 (.step 21 (.step 22 (.step 23 (.step 29 (.step 31 (.step 66 (.split 16 0 (.split 17 0 (.split 21 0 (.split 22 0 (.step 9 (.close 15)) (.step 23 (.close 15))) (.step 9 (.step 15 (.close 18)))) (.step 22 (.step 9 (.close 15)))) (.step 21 (.step 3 (.step 18 (.step 9 (.close 15)))))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 18 (.step 23 (.step 26 (.step 12 (.step 23 (.step 3 (.step 22 (.step 32 (.close 55)))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part29.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part30

namespace Part31
def root : Box := ⟨2658455991569831745807614123781914624, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439025350354042471212733978678132736⟩
def references : Fin 1 → Box := ![Part30.root]
def proof : Chunks.Proof 1 := (.step 3 (.step 18 (.step 9 (.step 15 (.step 23 (.step 29 (.step 31 (.split 21 1 (.split 35 1 (.split 39 1 (.split 40 1 (.split 49 1 (.split 50 1 (.split 58 1 (.reuse 0) (.run (.step 3 (.step 12 (.step 21 (.step 22 (.step 23 (.step 34 (.step 9 (.step 40 (.step 57 (.step 27 (.step 61 (.step 15 (.step 3 (.step 15 (.step 3 (.close 18)))))))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 21 (.step 22 (.step 26 (.step 32 (.close 53))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 18 (.step 21 (.step 22 (.step 26 (.step 3 (.step 34 (.close 52))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 23 (.step 24 (.step 29 (.step 31 (.step 3 (.close 15)))))))))))) (.run (.step 3 (.step 12 (.step 21 (.step 22 (.step 23 (.step 32 (.step 34 (.step 36 (.step 40 (.step 42 (.step 43 (.step 57 (.step 27 (.step 61 (.step 9 (.step 62 (.split 40 1 (.split 17 0 (.step 15 (.step 3 (.step 15 (.step 3 (.close 22))))) (.step 3 (.step 15 (.close 18)))) (.step 3 (.step 15 (.step 22 (.close 23))))))))))))))))))))))) (.run (.step 9 (.step 12 (.step 15 (.step 21 (.step 15 (.step 22 (.step 26 (.step 29 (.step 31 (.step 32 (.close 38))))))))))))) (.run (.step 3 (.step 9 (.step 12 (.step 15 (.step 18 (.step 24 (.step 15 (.step 18 (.close 24))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part30.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part31

namespace Part32
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439025350354042471212733978678132736⟩
def references : Fin 4 → Box := ![Part24.root, Part25.root, Part28.root, Part31.root]
def proof : Chunks.Proof 4 := (.split 12 1 (.split 14 1 (.split 16 1 (.split 17 1 (.reuse 0) (.run (.step 7 (.step 18 (.step 22 (.step 61 (.step 74 (.step 77 (.split 22 1 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 18 (.split 63 1 (.step 7 (.step 67 (.split 72 1 (.step 23 (.split 64 1 (.step 18 (.step 3 (.close 7))) (.step 11 (.step 18 (.close 15))))) (.step 3 (.step 11 (.step 18 (.step 22 (.close 29)))))))) (.step 3 (.step 11 (.step 18 (.step 22 (.step 29 (.close 66)))))))) (.step 7 (.step 18 (.step 12 (.close 21))))) (.step 7 (.step 18 (.step 12 (.step 22 (.close 53)))))) (.step 7 (.step 12 (.step 18 (.step 22 (.close 52)))))) (.step 3 (.step 11 (.step 18 (.step 22 (.close 42)))))) (.step 3 (.step 18 (.step 22 (.step 29 (.step 38 (.close 66))))))) (.step 3 (.step 18 (.step 22 (.step 29 (.close 66)))))) (.step 7 (.step 18 (.step 7 (.close 11))))))))))))) (.reuse 1)) (.reuse 2)) (.reuse 3))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part24.excludes
  · exact Part25.excludes
  · exact Part28.excludes
  · exact Part31.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part32

namespace Part33
def root : Box := ⟨2417851639229261570637824, 5783597145163977066094537818495513491484818251278953611793738891629820974624501887052408097972175777916218012673420519400205670866651416309947308497588663224169023811359762597071537746515310472486534365320550381233383669760⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 50 1 (.split 59 1 (.split 65 1 (.split 72 1 (.split 10 1 (.split 12 1 (.split 26 1 (.split 30 1 (.split 34 1 (.split 36 1 (.split 39 1 (.split 42 1 (.split 51 1 (.split 54 1 (.step 11 (.split 58 1 (.split 63 1 (.step 3 (.split 26 0 (.split 34 0 (.split 35 0 (.split 36 0 (.split 40 0 (.step 11 (.step 9 (.close 3))) (.step 3 (.step 9 (.close 11)))) (.step 3 (.step 9 (.close 11)))) (.step 9 (.close 11))) (.step 3 (.step 9 (.step 11 (.close 31))))) (.step 9 (.step 11 (.close 29))))) (.step 11 (.step 9 (.step 29 (.close 31))))) (.step 11 (.close 3)))) (.step 3 (.step 9 (.close 11)))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 11 (.step 29 (.close 31)))))) (.step 11 (.step 3 (.close 9)))) (.step 3 (.step 9 (.step 11 (.step 29 (.close 31)))))) (.step 3 (.step 9 (.step 11 (.step 29 (.step 11 (.close 31))))))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 11 (.step 27 (.step 29 (.close 11))))))) (.step 3 (.step 9 (.close 11)))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 11 (.step 29 (.step 31 (.step 11 (.step 29 (.step 11 (.step 31 (.step 66 (.step 31 (.close 67))))))))))))) (.step 3 (.close 11))) (.step 3 (.step 9 (.step 11 (.step 3 (.close 42)))))) (.step 3 (.step 9 (.step 11 (.step 27 (.step 42 (.step 11 (.step 44 (.step 11 (.step 3 (.step 11 (.close 53)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part33

namespace Part34
def root : Box := ⟨3221225472, 17350758325419215096788520990895667098404201320045581412890825219043923635890095184221771455312715059944119551158559372466280051424717848503354674054922711935948726648158128634232494188507439027885657660779310766230433955840⟩
def references : Fin 2 → Box := ![Part32.root, Part33.root]
def proof : Chunks.Proof 2 := (.split 8 1 (.split 10 1 (.reuse 0) (.run (.step 3 (.step 7 (.step 18 (.split 12 1 (.split 14 1 (.split 26 1 (.split 35 1 (.split 39 1 (.split 49 1 (.split 50 1 (.split 54 1 (.split 58 1 (.step 18 (.step 31 (.split 63 1 (.step 7 (.split 64 1 (.split 71 1 (.step 3 (.close 7)) (.step 3 (.step 18 (.close 29)))) (.step 3 (.step 18 (.step 29 (.close 31)))))) (.step 3 (.step 18 (.close 31)))))) (.step 3 (.step 11 (.close 12)))) (.step 3 (.close 12))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 11 (.step 12 (.close 17))))) (.step 3 (.step 29 (.close 31)))) (.step 3 (.close 29))) (.step 3 (.step 11 (.close 17)))) (.step 3 (.step 12 (.close 15))))))))) (.step 3 (.step 9 (.step 11 (.step 18 (.step 31 (.step 11 (.step 27 (.step 42 (.step 47 (.step 61 (.step 66 (.step 67 (.step 74 (.split 35 1 (.split 40 1 (.split 49 1 (.reuse 1) (.run (.step 3 (.step 9 (.step 11 (.step 27 (.step 34 (.step 42 (.step 52 (.step 55 (.step 61 (.step 11 (.step 44 (.step 11 (.step 3 (.close 52)))))))))))))))) (.run (.step 3 (.step 9 (.step 11 (.step 18 (.step 23 (.step 11 (.step 27 (.step 31 (.close 11))))))))))) (.run (.step 3 (.step 9 (.step 11 (.step 29 (.step 31 (.step 38 (.step 40 (.step 47 (.step 11 (.close 38))))))))))))))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part32.excludes
  · exact Part33.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part34

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part34.excludes
end FiveColour.Packed.ProjectedChunks.Case82
