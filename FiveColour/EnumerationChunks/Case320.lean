module
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case320
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root 207
def families : Fin 78 → List Cut := Enumeration.families 207
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid 207
def points : List Nat := [16159137489556603414253445801442999651007926217484190679028505391241642297861790670568982157711840702425286693371797924011377308112101057358202432570533278613761854546310013577594635970430550990367436492260711071748,10772758326371068942843234601991370092703019430998960938227158975006509131792159101242486899730798805755362046074388800473024051797486436609670238950107128061405958168394208523234624277031364792831715076675517546500,16159137489556603414253445801442999651007926217484190679028505391241642297861790670568982155067616827264292297564136691882379073638248839253416443816869300753055393236178548997489202031708298050960245179299076767748,10772758326371068942843234601991370092703019430998960938227158975006509131792159101242486897086574930594367650266727568344025817323634218504884250196443150200699496858262743943129190338309111853424523763713883242500,13696232869697879005959923355393257356173617608673899635351990039084355456108612090521445217899789335053163554186609724337711461556784882128379581797308168497687596281996077683720579824742301700,9138247760491330462336956018839157722027355144889449626580003763878341299805411928025792087062220055782117574993458280315412101273613912331297089092155995534228816446184992679878020939324063748,13696232869697879005959923355393257356173617608673899635351990039084352811884736929527049410240744454693787252492250369439951944326956953936107848988350638347255790420056063242095992908332138500,9138247760491330462336956018839157722027355144889449626580003763878338655581536767031396279403175175422741273299098925417652584043785984139025356283198465383797010584244978238253434022913900548]
def reduced31 : Array Cut := #[⟨2147483648, 2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104139578097391210961403571828974157824, 0⟩,⟨2209760673792, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721783477467391289957729977249475185099430428672, 4⟩,⟨9223372039002259456, 2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704453056462848, 1⟩,⟨9223374246615449600, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721783477467392588031944610956382317723512733696, 5⟩]
def witnesses31 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,3,1,0,0,0,0,0]
theorem valid31 : ∀ c ∈ reduced31.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered31 : ∀ c ∈ families 34, possible root 14 c →
    ∃ d ∈ reduced31.toList, relaxes root c d = true :=
  covers_sound root 14 reduced31 (families 34) witnesses31 (by decide +kernel)
def reduced33 : Array Cut := #[⟨8589934592, 2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024, 0⟩,⟨2209760673792, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721783477467391289957729977249475185099430428672, 4⟩,⟨2361183241443412541440, 2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100094506958848, 1⟩,⟨2361183243644583280640, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721783477467391289957729977249475185100504170496, 5⟩]
def witnesses33 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,1,0,3,0,0,0]
theorem valid33 : ∀ c ∈ reduced33.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered33 : ∀ c ∈ families 36, possible root 14 c →
    ∃ d ∈ reduced33.toList, relaxes root c d = true :=
  covers_sound root 14 reduced33 (families 36) witnesses33 (by decide +kernel)
def reduced41 : Array Cut := #[⟨2199023255552, 2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824, 1⟩,⟨2209760673792, 2772672338344690020572809991806503085245379400918920934522474340575155574859683780721783477467391289957729977249475185099430428672, 5⟩]
def witnesses41 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,1,0]
theorem valid41 : ∀ c ∈ reduced41.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered41 : ∀ c ∈ families 44, possible root 14 c →
    ∃ d ∈ reduced41.toList, relaxes root c d = true :=
  covers_sound root 14 reduced41 (families 44) witnesses41 (by decide +kernel)
def reduced63 : Array Cut := #[⟨9223372036854775808, 1298074214633706907132624082305024, 0⟩,⟨9223372039002259456, 2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140876171605844668310704453056462848, 1⟩,⟨2388853357545386934272, 1299341865233935136534121859252224, 4⟩,⟨2388853357547534417920, 2772669694120814859578414184143083703436437075375816575170479580614621307805625623039974406104140877439256444896540105950833410048, 5⟩]
def witnesses63 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,3,0,2,0,0,0]
theorem valid63 : ∀ c ∈ reduced63.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered63 : ∀ c ∈ families 66, possible root 14 c →
    ∃ d ∈ reduced63.toList, relaxes root c d = true :=
  covers_sound root 14 reduced63 (families 66) witnesses63 (by decide +kernel)
def reduced64 : Array Cut := #[⟨18446744073709551616, 1267650600228229401496703205376, 1⟩,⟨2388853357545386934272, 1299341865233935136534121859252224, 5⟩]
def witnesses64 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0]
theorem valid64 : ∀ c ∈ reduced64.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered64 : ∀ c ∈ families 67, possible root 14 c →
    ∃ d ∈ reduced64.toList, relaxes root c d = true :=
  covers_sound root 14 reduced64 (families 67) witnesses64 (by decide +kernel)
def reduced71 : Array Cut := #[⟨2361183241434822606848, 1073741824, 0⟩,⟨2361183241443412541440, 2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100094506958848, 1⟩,⟨2388853357545386934272, 1299341865233935136534121859252224, 4⟩,⟨2388853357553976868864, 2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756843058203004624299984634215292469248, 5⟩]
def witnesses71 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,2,0,2,0,2,0,3,0,0,0,2,0,0,0,0,0]
theorem valid71 : ∀ c ∈ reduced71.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered71 : ∀ c ∈ families 74, possible root 14 c →
    ∃ d ∈ reduced71.toList, relaxes root c d = true :=
  covers_sound root 14 reduced71 (families 74) witnesses71 (by decide +kernel)
def checkedFamilies (r : Fin 78) : List Cut :=
  match r.val with
  | 34 => reduced31.toList
  | 36 => reduced33.toList
  | 44 => reduced41.toList
  | 66 => reduced63.toList
  | 67 => reduced64.toList
  | 74 => reduced71.toList
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
  · exact families_valid 31
  · exact families_valid 32
  · exact families_valid 33
  · exact valid31
  · exact families_valid 35
  · exact valid33
  · exact families_valid 37
  · exact families_valid 38
  · exact families_valid 39
  · exact families_valid 40
  · exact families_valid 41
  · exact families_valid 42
  · exact families_valid 43
  · exact valid41
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
  · exact valid63
  · exact valid64
  · exact families_valid 68
  · exact families_valid 69
  · exact families_valid 70
  · exact families_valid 71
  · exact families_valid 72
  · exact families_valid 73
  · exact valid71
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
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered31
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered33
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered41
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
  · exact covered63
  · exact covered64
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered71
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
namespace Part0
def root : Box := ⟨4, 16159137489556603414258021608585868786251622001897329545425639517879283187557791481814961215911765811483823385224561263526939013288355611914398530557596530201573000985896641947927905288757043373883567639036310847492⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.split 31 1 (.split 33 1 (.step 66 (.run (.close 74))) (.split 41 1 (.step 66 (.run (.close 74))) (.split 63 1 (.step 36 (.run (.close 67))) (.step 34 (.step 74 (.step 36 (.step 74 (.step 36 (.step 74 (.split 33 2 (.step 67 (.split 63 2 (.step 2 .point) (.step 1 .point))) (.step 44 (.split 63 2 (.step 2 .point) (.step 1 .point))))))))))))) (.split 33 1 (.split 41 1 (.step 66 (.run (.close 74))) (.split 63 1 (.step 34 (.step 36 (.step 66 (.split 31 2 (.step 67 (.split 64 2 (.step 2 .point) (.step 1 .point))) (.step 44 (.split 64 2 (.step 2 .point) (.step 1 .point))))))) (.step 34 (.run (.close 66))))) (.split 63 1 (.step 36 (.run (.close 67))) (.step 34 (.run (.close 66))))))
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
  Enumeration.covers_of_weakened points root (Archive.root_valid 207) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part0.covered
end FiveColour.Packed.EnumerationChunks.Case320
