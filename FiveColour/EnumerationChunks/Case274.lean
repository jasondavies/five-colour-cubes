module
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case274
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root 161
def families : Fin 78 → List Cut := Enumeration.families 161
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid 161
def points : List Nat := []
def reduced28 : Array Cut := #[⟨38493912825856, 2977131417487478162034720337682076566758762840798440375682292710081385764338271553321772261169951332358936211493064760084098456775345307648, 0⟩,⟨40768098009088, 2977131414714805826272282657821562439263131830983115028979022780893545510236306684475596224475389715138461310426839325218304017024998703104, 0⟩,⟨42977858682880, 2977131417487478164616972678394372431069634916228494429897943715416019850811462259335280005197173192605852600384569302467779202124429131776, 1⟩,⟨1152923852074909696, 2977131417487478162034720340086984169279423323979462306944185906399071794769753016408028279294342477518208532727770362393628105797531598848, 0⟩,⟨1152926126260092928, 2977131414714805826272282660226470041783792314164136960240915977211231540667788147561852242599780860297733631661544927527833666047184994304, 0⟩,⟨1152928336020766720, 2977131417487478164616972680799280033590295399409516361159836911733705881242943722421536023321564337765124921619274904777308851146615422976, 1⟩,⟨1152960135958626304, 2977131417487478162034720340086984171519168066157268506794573826114084694420391100926038216018934767872870165763838880412493649202640846848, 1⟩,⟨1152962410143809536, 2977131414714805826272282660226470044023537056341943160091303896926244440318426232079862179324373150652395264697613445546699209452294242304, 1⟩,⟨1152964619904483328, 2977131417487478164616972680799280035830040141587322561010224831448718780893581806939545960046156628119786554655343422796174394551724670976, 4⟩]
def witnesses28 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid28 : ∀ c ∈ reduced28.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered28 : ∀ c ∈ families 31, possible root 14 c →
    ∃ d ∈ reduced28.toList, relaxes root c d = true :=
  covers_sound root 14 reduced28 (families 31) witnesses28 (by decide +kernel)
def reduced37 : Array Cut := #[⟨3446711255040, 2772672338344690022977717598806653052782011742588644331123617548778920619698599270470754620148542207244718696976355830275738959872, 1⟩,⟨5720896438272, 2582252343117203471311022042966686395885374401935777294676955750852423233776193002928067306178493262110561390525392355328, 1⟩,⟨7930657112064, 2772672340926942363690013463117525128212065796804295336458251635252111325712107014497976480395458596136223239360036575624822784000, 3⟩,⟨1152923852074909696, 2977131417487478162034720340086984169279423323979462306944185906399071794769753016408028279294342477518208532727770362393628105797531598848, 0⟩,⟨1152924951586537472, 2977131417487478162034720340086984171519168066157266517501628186967516072891398513642677814194331578482000403907931307774505599069138714624, 2⟩,⟨1152926126260092928, 2977131414714805826272282660226470041783792314164136960240915977211231540667788147561852242599780860297733631661544927527833666047184994304, 0⟩,⟨1152927225771720704, 2977131414714805826272282660226470044023537056341941170798358257779675818789433644796501777499769961261525502841705872908711159318792110080, 2⟩,⟨1152928336020766720, 2977131417487478164616972680799280033590295399409516361159836911733705881242943722421536023321564337765124921619274904777308851146615422976, 1⟩,⟨1152929435532394496, 2977131417487478164616972680799280035830040141587320571717279192302150159364589219656185558221553438728916792799435850158186344418222538752, 5⟩]
def witnesses37 : List Nat := [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid37 : ∀ c ∈ reduced37.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered37 : ∀ c ∈ families 40, possible root 14 c →
    ∃ d ∈ reduced37.toList, relaxes root c d = true :=
  covers_sound root 14 reduced37 (families 40) witnesses37 (by decide +kernel)
def reduced40 : Array Cut := #[⟨3446711255040, 2772672338344690022977717598806653052782011742588644331123617548778920619698599270470754620148542207244718696976355830275738959872, 1⟩,⟨5720896438272, 2582252343117203471311022042966686395885374401935777294676955750852423233776193002928067306178493262110561390525392355328, 1⟩,⟨7930657112064, 2772672340926942363690013463117525128212065796804295336458251635252111325712107014497976480395458596136223239360036575624822784000, 3⟩,⟨38493912825856, 2977131417487478162034720337682076566758762840798440375682292710081385764338271553321772261169951332358936211493064760084098456775345307648, 0⟩,⟨38631351779328, 2977131417487478162034720340086984171519168066157268506794573826114084694420391100926038216018933374076295257599892534430101608680046723072, 2⟩,⟨40768098009088, 2977131414714805826272282657821562439263131830983115028979022780893545510236306684475596224475389715138461310426839325218304017024998703104, 0⟩,⟨40905536962560, 2977131414714805826272282660226470044023537056341943160091303896926244440318426232079862179324371756855820356533667099564307168929700118528, 2⟩,⟨42977858682880, 2977131417487478164616972678394372431069634916228494429897943715416019850811462259335280005197173192605852600384569302467779202124429131776, 1⟩,⟨43115297636352, 2977131417487478164616972680799280035830040141587322561010224831448718780893581806939545960046155234323211646491397076813782354029130547200, 5⟩]
def witnesses40 : List Nat := [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid40 : ∀ c ∈ reduced40.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered40 : ∀ c ∈ families 43, possible root 14 c →
    ∃ d ∈ reduced40.toList, relaxes root c d = true :=
  covers_sound root 14 reduced40 (families 43) witnesses40 (by decide +kernel)
def checkedFamilies (r : Fin 78) : List Cut :=
  match r.val with
  | 31 => reduced28.toList
  | 40 => reduced37.toList
  | 43 => reduced40.toList
  | _ => families r
theorem checkedFamilies_valid : ∀ r, ∀ c ∈ checkedFamilies r, c.Valid := by
  intro r
  fin_cases r
  · exact families_valid 0
  · exact families_valid 1
  · exact families_valid 2
  · exact families_valid 3
  · exact families_valid 4
  · exact families_valid 5
  · exact families_valid 6
  · exact families_valid 7
  · exact families_valid 8
  · exact families_valid 9
  · exact families_valid 10
  · exact families_valid 11
  · exact families_valid 12
  · exact families_valid 13
  · exact families_valid 14
  · exact families_valid 15
  · exact families_valid 16
  · exact families_valid 17
  · exact families_valid 18
  · exact families_valid 19
  · exact families_valid 20
  · exact families_valid 21
  · exact families_valid 22
  · exact families_valid 23
  · exact families_valid 24
  · exact families_valid 25
  · exact families_valid 26
  · exact families_valid 27
  · exact families_valid 28
  · exact families_valid 29
  · exact families_valid 30
  · exact valid28
  · exact families_valid 32
  · exact families_valid 33
  · exact families_valid 34
  · exact families_valid 35
  · exact families_valid 36
  · exact families_valid 37
  · exact families_valid 38
  · exact families_valid 39
  · exact valid37
  · exact families_valid 41
  · exact families_valid 42
  · exact valid40
  · exact families_valid 44
  · exact families_valid 45
  · exact families_valid 46
  · exact families_valid 47
  · exact families_valid 48
  · exact families_valid 49
  · exact families_valid 50
  · exact families_valid 51
  · exact families_valid 52
  · exact families_valid 53
  · exact families_valid 54
  · exact families_valid 55
  · exact families_valid 56
  · exact families_valid 57
  · exact families_valid 58
  · exact families_valid 59
  · exact families_valid 60
  · exact families_valid 61
  · exact families_valid 62
  · exact families_valid 63
  · exact families_valid 64
  · exact families_valid 65
  · exact families_valid 66
  · exact families_valid 67
  · exact families_valid 68
  · exact families_valid 69
  · exact families_valid 70
  · exact families_valid 71
  · exact families_valid 72
  · exact families_valid 73
  · exact families_valid 74
  · exact families_valid 75
  · exact families_valid 76
  · exact families_valid 77
theorem checkedFamilies_cover : ∀ r, ∀ c ∈ families r, possible root 14 c →
    ∃ d ∈ checkedFamilies r, relaxes root c d = true := by
  intro r
  fin_cases r
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered28
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered37
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered40
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
namespace Part0
def root : Box := ⟨3, 12448546706642978875537223591073483453037338705449375396954921366493524120446157275696388520005154350752729634742169377100967832483078338677203627717424925841614701934763101103587331⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 31 (.step 40 (.step 31 (.run (.close 43)))))
theorem accepted : Enumeration.check points 14 checkedFamilies references root proof = true := by decide +kernel
theorem root_valid : root.Valid := by decide +kernel
theorem references_covered : ∀ i, Enumeration.Covers points 14 checkedFamilies (references i) := by
  intro i
  exact Fin.elim0 i
theorem covered : Enumeration.Covers points 14 checkedFamilies root :=
  Enumeration.check_sound points 14 checkedFamilies checkedFamilies_valid references references_covered proof root root_valid accepted
end Part0
/-- Every admissible vector in the original root is one of the explicit points. -/
theorem covered : Enumeration.Covers points 14 families root :=
  Enumeration.covers_of_weakened points root (Archive.root_valid 161) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part0.covered
end FiveColour.Packed.EnumerationChunks.Case274
