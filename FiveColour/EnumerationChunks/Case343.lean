module
public import FiveColour.EnumerationRoot
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks.Case343
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := Archive.root 230
def families : Fin 78 → List Cut := Enumeration.families 230
theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := Enumeration.families_valid 230
def points : List Nat := []
def reduced7 : Array Cut := #[⟨128, 4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727074585042721378292777435812376133285876920625254286345394996247527424, 1⟩,⟨9444732965739290435712, 4898883310657342441196954343935776394038937435041614979870160492432575751912103351217640287695700151597052607846958206493092460393699082707815356079514435351088535963418575736175904453028540748501353472, 3⟩,⟨9444805023608239825024, 4898883310657342441196954343935776394038937435041614983066831007956151796846858914525842584784613192268756899554624413746262457972514760259917125488770000331149411315211913051728639730623252727358030848, 5⟩]
def witnesses7 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid7 : ∀ c ∈ reduced7.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered7 : ∀ c ∈ families 10, possible root 14 c →
    ∃ d ∈ reduced7.toList, relaxes root c d = true :=
  covers_sound root 14 reduced7 (families 10) witnesses7 (by decide +kernel)
def reduced13 : Array Cut := #[⟨8192, 4249103942534136789516705652419749018636744941816255385595553105603228478886817941913300018121834285351114635889972008122772634701221657915276159830132698815550650166683145752253825024, 1⟩,⟨9444732965739290435712, 4898883310657342441196954343935776394038937435041614979870160492432575751912103351217640287695700151597052607846958206493092460393699082707815356079514435351088535963418575736175904453028540748501353472, 3⟩,⟨9444805023608239825024, 4898883310657342441196954343935776394038937435041614983066831007956151796846858914525842584784613192268756899554624413746262457972514760259917125488770000331149411315211913051728639730623252727358030848, 5⟩]
def witnesses13 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid13 : ∀ c ∈ reduced13.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered13 : ∀ c ∈ families 16, possible root 14 c →
    ∃ d ∈ reduced13.toList, relaxes root c d = true :=
  covers_sound root 14 reduced13 (families 16) witnesses13 (by decide +kernel)
def reduced25 : Array Cut := #[⟨33554432, 3196670515523576044934755563308202297086564498088930458479776726656380660551439995003193449537015778467662777468320381844938727095591204153641140224, 1⟩,⟨72057868949389312, 3196670515523576044934755563308202297088913040671704291707666207253169997578815677552101769409255564980060875351793337315552735277594711978856677376, 3⟩,⟨9444805023608239825024, 4898883310657342441196954343935776394038937435041614983066831007956151796846858914525842584784613192268756899554624413746262457972514760259917125488770000331149411315211913051728639730623252727358030848, 5⟩]
def witnesses25 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid25 : ∀ c ∈ reduced25.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered25 : ∀ c ∈ families 28, possible root 14 c →
    ∃ d ∈ reduced25.toList, relaxes root c d = true :=
  covers_sound root 14 reduced25 (families 28) witnesses25 (by decide +kernel)
def reduced38 : Array Cut := #[⟨274877906944, 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976, 1⟩,⟨72057868949389312, 3196670515523576044934755563308202297088913040671704291707666207253169997578815677552101769409255564980060875351793337315552735277594711978856677376, 3⟩,⟨9444805023608239825024, 4898883310657342441196954343935776394038937435041614983066831007956151796846858914525842584784613192268756899554624413746262457972514760259917125488770000331149411315211913051728639730623252727358030848, 5⟩]
def witnesses38 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid38 : ∀ c ∈ reduced38.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered38 : ∀ c ∈ families 41, possible root 14 c →
    ∃ d ∈ reduced38.toList, relaxes root c d = true :=
  covers_sound root 14 reduced38 (families 41) witnesses38 (by decide +kernel)
def reduced56 : Array Cut := #[⟨72057594037927936, 1532495540865888858358347027150309183618739122183602176, 1⟩,⟨72057868949389312, 3196670515523576044934755563308202297088913040671704291707666207253169997578815677552101769409255564980060875351793337315552735277594711978856677376, 3⟩,⟨9444805023608239825024, 4898883310657342441196954343935776394038937435041614983066831007956151796846858914525842584784613192268756899554624413746262457972514760259917125488770000331149411315211913051728639730623252727358030848, 5⟩]
def witnesses56 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid56 : ∀ c ∈ reduced56.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered56 : ∀ c ∈ families 59, possible root 14 c →
    ∃ d ∈ reduced56.toList, relaxes root c d = true :=
  covers_sound root 14 reduced56 (families 59) witnesses56 (by decide +kernel)
def reduced73 : Array Cut := #[⟨9444732965739290427392, 1024, 1⟩,⟨9444732965739290435712, 4898883310657342441196954343935776394038937435041614979870160492432575751912103351217640287695700151597052607846958206493092460393699082707815356079514435351088535963418575736175904453028540748501353472, 3⟩,⟨9444805023608239825024, 4898883310657342441196954343935776394038937435041614983066831007956151796846858914525842584784613192268756899554624413746262457972514760259917125488770000331149411315211913051728639730623252727358030848, 5⟩]
def witnesses73 : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem valid73 : ∀ c ∈ reduced73.toList, c.Valid := by
  apply list_valid_of_weights
  decide +kernel

theorem covered73 : ∀ c ∈ families 76, possible root 14 c →
    ∃ d ∈ reduced73.toList, relaxes root c d = true :=
  covers_sound root 14 reduced73 (families 76) witnesses73 (by decide +kernel)
def checkedFamilies (r : Fin 78) : List Cut :=
  match r.val with
  | 10 => reduced7.toList
  | 16 => reduced13.toList
  | 28 => reduced25.toList
  | 41 => reduced38.toList
  | 59 => reduced56.toList
  | 76 => reduced73.toList
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
  · exact valid7
  · exact families_valid 11
  · exact families_valid 12
  · exact families_valid 13
  · exact families_valid 14
  · exact families_valid 15
  · exact valid13
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
  · exact valid25
  · exact families_valid 29
  · exact families_valid 30
  · exact families_valid 31
  · exact families_valid 32
  · exact families_valid 33
  · exact families_valid 34
  · exact families_valid 35
  · exact families_valid 36
  · exact families_valid 37
  · exact families_valid 38
  · exact families_valid 39
  · exact families_valid 40
  · exact valid38
  · exact families_valid 42
  · exact families_valid 43
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
  · exact valid56
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
  · exact valid73
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
  · exact covered7
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
  · exact covered13
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
  · exact covered25
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
  · exact covered38
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
  · exact covered56
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
  · exact covered73
  · intro c hc _; exact ⟨c, hc, by simp [relaxes]⟩
namespace Part0
def root : Box := ⟨5, 22592111669665739975592870737637022906810831294812635293316914733066959609107911952322555035646721641528906279313022053741439013282460507991364412514788928418875692833778952520356696855656924371641458437984254770011963397⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Enumeration.Proof 0 := (.step 59 (.step 76 (.split 7 1 (.split 13 1 (.step 28 (.step 41 (.run (.close 59)))) (.step 16 (.step 28 (.step 16 (.run (.close 41)))))) (.step 10 (.step 28 (.step 10 (.run (.close 41))))))))
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
  Enumeration.covers_of_weakened points root (Archive.root_valid 230) 14 families checkedFamilies
    families_valid checkedFamilies_valid checkedFamilies_cover Part0.covered
end FiveColour.Packed.EnumerationChunks.Case343
